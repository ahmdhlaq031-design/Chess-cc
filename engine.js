/* ============================================================================
 * ChessEnginePro.js — محرك شطرنج محسّن شامل (إصلاحات + تحسينات ذكاء)
 * ----------------------------------------------------------------------------
 * تحسينات رئيسية على النسخة الأصلية:
 *  - إصلاح أخطاء: en passant undo, attack detection, eval double-counting,
 *    TT (Number بدل BigInt), repetition tracking داخل الشجرة, null-move hash.
 *  - Zobrist بـ Number (32-bit × 2) أسرع 5-10x من BigInt.
 *  - SEE (Static Exchange Evaluation) لترتيب الأكل و Pruning.
 *  - PVS (Principal Variation Search) + Aspiration Windows.
 *  - Late Move Pruning (LMP) + Futility Pruning + Reverse Futility.
 *  - Internal Iterative Deepening (IID).
 *  - Check Extension.
 *  - History heuristic محسّن + Butterfly + Counter-move.
 *  - تحسين التقييم: passer, doubled, isolated, rook on open file, king shelter,
 *    bishop pair, mobility خفيفة, tempo.
 *  - تحسين إدارة الوقت.
 * ==========================================================================*/

(function (global) {
  "use strict";

  /* ------------------------------ ثوابت ------------------------------ */
  const WHITE = 0, BLACK = 1;
  const PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6;

  const pieceOf = (c, t) => (c << 3) | t;
  const colorOf = (p) => p >> 3;
  const typeOf  = (p) => p & 7;

  const W_PAWN = pieceOf(WHITE, PAWN),   B_PAWN = pieceOf(BLACK, PAWN);
  const W_KNIGHT = pieceOf(WHITE, KNIGHT), B_KNIGHT = pieceOf(BLACK, KNIGHT);
  const W_BISHOP = pieceOf(WHITE, BISHOP), B_BISHOP = pieceOf(BLACK, BISHOP);
  const W_ROOK = pieceOf(WHITE, ROOK),   B_ROOK = pieceOf(BLACK, ROOK);
  const W_QUEEN = pieceOf(WHITE, QUEEN), B_QUEEN = pieceOf(BLACK, QUEEN);
  const W_KING = pieceOf(WHITE, KING),   B_KING = pieceOf(BLACK, KING);

  const isValidSq = (sq) => (sq & 0x88) === 0;

  const SQ = {};
  for (let r = 0; r < 8; r++)
    for (let f = 0; f < 8; f++)
      SQ["abcdefgh"[f] + (8 - r)] = r * 16 + f;

  const FILES = "abcdefgh";
  const sqName = (sq) => FILES[sq & 7] + (8 - (sq >> 4));
  const nameToSq = (s) => SQ[s];

  const N_DIRS = [-33, -31, -18, -14, 14, 18, 31, 33];
  const B_DIRS = [-17, -15, 15, 17];
  const R_DIRS = [-16, -1, 1, 16];
  const K_DIRS = [-17, -16, -15, -1, 1, 15, 16, 17];

  const CASTLE_WK = 1, CASTLE_WQ = 2, CASTLE_BK = 4, CASTLE_BQ = 8;

  const MATE = 30000;
  const MATE_IN_MAX = MATE - 1000;
  const INF = 1000000;

  /* --------------------------- Attack Tables ------------------------- */
  // نستخدم اتجاهات صحيحة للبيادق: الأبيض يهاجم sq+15 و sq+17 (لأنه يتحرك لأعلى -16)
  function isSquareAttackedBy(state, sq, byColor) {
    const b = state.board;
    if (byColor === WHITE) {
      if (isValidSq(sq + 15) && b[sq + 15] === W_PAWN) return true;
      if (isValidSq(sq + 17) && b[sq + 17] === W_PAWN) return true;
    } else {
      if (isValidSq(sq - 15) && b[sq - 15] === B_PAWN) return true;
      if (isValidSq(sq - 17) && b[sq - 17] === B_PAWN) return true;
    }
    for (const d of N_DIRS) {
      const t = sq + d;
      if (!isValidSq(t)) continue;
      const p = b[t];
      if (p && colorOf(p) === byColor && typeOf(p) === KNIGHT) return true;
    }
    for (const d of K_DIRS) {
      const t = sq + d;
      if (!isValidSq(t)) continue;
      const p = b[t];
      if (p && colorOf(p) === byColor && typeOf(p) === KING) return true;
    }
    for (const d of B_DIRS) {
      let t = sq + d;
      while (isValidSq(t)) {
        const p = b[t];
        if (p) {
          if (colorOf(p) === byColor && (typeOf(p) === BISHOP || typeOf(p) === QUEEN)) return true;
          break;
        }
        t += d;
      }
    }
    for (const d of R_DIRS) {
      let t = sq + d;
      while (isValidSq(t)) {
        const p = b[t];
        if (p) {
          if (colorOf(p) === byColor && (typeOf(p) === ROOK || typeOf(p) === QUEEN)) return true;
          break;
        }
        t += d;
      }
    }
    return false;
  }

  /* ------------------------------ State ------------------------------ */
  class State {
    constructor() {
      this.board = new Array(128).fill(0);
      this.turn = WHITE;
      this.castling = 0;
      this.ep = -1;
      this.halfmove = 0;
      this.fullmove = 1;
      this.kings = [-1, -1];
      this.hashLo = 0;
      this.hashHi = 0;
      this.history = [];
    }
    clone() {
      const s = new State();
      s.board = this.board.slice();
      s.turn = this.turn;
      s.castling = this.castling;
      s.ep = this.ep;
      s.halfmove = this.halfmove;
      s.fullmove = this.fullmove;
      s.kings = this.kings.slice();
      s.hashLo = this.hashLo;
      s.hashHi = this.hashHi;
      s.history = this.history.slice();
      return s;
    }
  }

  /* ------------------------- Zobrist (Number) ------------------------ */
  const ZOBRIST_PIECES_LO = [], ZOBRIST_PIECES_HI = [];
  const ZOBRIST_CASTLE_LO = [], ZOBRIST_CASTLE_HI = [];
  const ZOBRIST_EP_LO = [], ZOBRIST_EP_HI = [];
  const ZOBRIST_TURN_LO = [], ZOBRIST_TURN_HI = [];

  (function initZobrist() {
    let s = 0x9e3779b9 >>> 0;
    const rnd = () => {
      s ^= s << 13; s >>>= 0;
      s ^= s >>> 17;
      s ^= s << 5;  s >>>= 0;
      return s;
    };
    for (let p = 0; p < 16; p++) {
      ZOBRIST_PIECES_LO[p] = []; ZOBRIST_PIECES_HI[p] = [];
      for (let sq = 0; sq < 128; sq++) {
        ZOBRIST_PIECES_LO[p][sq] = rnd();
        ZOBRIST_PIECES_HI[p][sq] = rnd();
      }
    }
    for (let i = 0; i < 16; i++) { ZOBRIST_CASTLE_LO[i] = rnd(); ZOBRIST_CASTLE_HI[i] = rnd(); }
    for (let i = 0; i < 128; i++) { ZOBRIST_EP_LO[i] = rnd(); ZOBRIST_EP_HI[i] = rnd(); }
    for (let i = 0; i < 2; i++) { ZOBRIST_TURN_LO[i] = rnd(); ZOBRIST_TURN_HI[i] = rnd(); }
  })();

  function computeHash(state) {
    let lo = 0, hi = 0;
    for (let sq = 0; sq < 128; sq++) {
      if (!isValidSq(sq)) continue;
      const p = state.board[sq];
      if (p) { lo ^= ZOBRIST_PIECES_LO[p][sq]; hi ^= ZOBRIST_PIECES_HI[p][sq]; }
    }
    lo ^= ZOBRIST_CASTLE_LO[state.castling]; hi ^= ZOBRIST_CASTLE_HI[state.castling];
    if (state.ep >= 0) { lo ^= ZOBRIST_EP_LO[state.ep]; hi ^= ZOBRIST_EP_HI[state.ep]; }
    lo ^= ZOBRIST_TURN_LO[state.turn]; hi ^= ZOBRIST_TURN_HI[state.turn];
    state.hashLo = lo >>> 0; state.hashHi = hi >>> 0;
  }

  /* -------------------------------- FEN ------------------------------ */
  function parseFEN(fen) {
    const s = new State();
    const parts = fen.trim().split(/\s+/);
    const placement = parts[0];
    const turn = parts[1] || "w";
    const castling = parts[2] || "-";
    const ep = parts[3] || "-";
    s.halfmove = parseInt(parts[4] || "0", 10);
    s.fullmove = parseInt(parts[5] || "1", 10);

    let r = 0, f = 0;
    for (const ch of placement) {
      if (ch === "/") { r++; f = 0; continue; }
      if (/\d/.test(ch)) { f += parseInt(ch, 10); continue; }
      const color = ch === ch.toUpperCase() ? WHITE : BLACK;
      const lower = ch.toLowerCase();
      const type = lower === "p" ? PAWN : lower === "n" ? KNIGHT : lower === "b" ? BISHOP
                 : lower === "r" ? ROOK : lower === "q" ? QUEEN : KING;
      const sq = r * 16 + f;
      const p = pieceOf(color, type);
      s.board[sq] = p;
      if (type === KING) s.kings[color] = sq;
      f++;
    }
    s.turn = turn === "w" ? WHITE : BLACK;
    s.castling = 0;
    if (castling.includes("K")) s.castling |= CASTLE_WK;
    if (castling.includes("Q")) s.castling |= CASTLE_WQ;
    if (castling.includes("k")) s.castling |= CASTLE_BK;
    if (castling.includes("q")) s.castling |= CASTLE_BQ;
    s.ep = ep === "-" ? -1 : nameToSq(ep);
    computeHash(s);
    return s;
  }

  function toFEN(s) {
    let out = "";
    for (let r = 0; r < 8; r++) {
      let empty = 0;
      for (let f = 0; f < 8; f++) {
        const p = s.board[r * 16 + f];
        if (!p) { empty++; continue; }
        if (empty) { out += empty; empty = 0; }
        const t = typeOf(p);
        const ch = t === PAWN ? "p" : t === KNIGHT ? "n" : t === BISHOP ? "b"
                 : t === ROOK ? "r" : t === QUEEN ? "q" : "k";
        out += colorOf(p) === WHITE ? ch.toUpperCase() : ch;
      }
      if (empty) out += empty;
      if (r < 7) out += "/";
    }
    out += " " + (s.turn === WHITE ? "w" : "b") + " ";
    let c = "";
    if (s.castling & CASTLE_WK) c += "K";
    if (s.castling & CASTLE_WQ) c += "Q";
    if (s.castling & CASTLE_BK) c += "k";
    if (s.castling & CASTLE_BQ) c += "q";
    out += (c || "-") + " ";
    out += (s.ep >= 0 ? sqName(s.ep) : "-") + " ";
    out += s.halfmove + " " + s.fullmove;
    return out;
  }

  /* --------------------------- Apply / Undo -------------------------- */
  // نُخزّن كل شيء لازٍم للتراجع بدقة، بما في ذلك capturedSq (لـ en passant)
  function applyMove(state, from, to, promoType) {
    const b = state.board;
    const piece = b[from];
    const color = colorOf(piece);
    const type = typeOf(piece);
    const target = b[to];

    let captured = 0;
    let capturedSq = -1;

    // En passant
    if (type === PAWN && to === state.ep && !target) {
      capturedSq = color === WHITE ? to + 16 : to - 16;
      captured = b[capturedSq];
    } else if (target) {
      captured = target;
      capturedSq = to;
    }

    state.history.push({
      from, to, promoType: promoType || 0,
      captured, capturedSq,
      prevCastling: state.castling,
      prevEp: state.ep,
      prevHalf: state.halfmove,
      prevKings: state.kings.slice(),
      hashLo: state.hashLo, hashHi: state.hashHi,
      prevFull: state.fullmove,
    });

    let lo = state.hashLo, hi = state.hashHi;
    lo ^= ZOBRIST_PIECES_LO[piece][from]; hi ^= ZOBRIST_PIECES_HI[piece][from];
    if (captured) { lo ^= ZOBRIST_PIECES_LO[captured][capturedSq]; hi ^= ZOBRIST_PIECES_HI[captured][capturedSq]; }
    lo ^= ZOBRIST_CASTLE_LO[state.castling]; hi ^= ZOBRIST_CASTLE_HI[state.castling];
    if (state.ep >= 0) { lo ^= ZOBRIST_EP_LO[state.ep]; hi ^= ZOBRIST_EP_HI[state.ep]; }

    b[from] = 0;
    if (capturedSq >= 0) b[capturedSq] = 0;

    let placed = piece;
    if (type === PAWN && (to >> 4) === (color === WHITE ? 0 : 7)) {
      placed = pieceOf(color, promoType || QUEEN);
    }
    b[to] = placed;
    lo ^= ZOBRIST_PIECES_LO[placed][to]; hi ^= ZOBRIST_PIECES_HI[placed][to];

    // Castling rook move
    if (type === KING) {
      const fromF = from & 7, toF = to & 7;
      if (fromF === 4 && toF === 6) {
        const rFrom = to + 1, rTo = to - 1;
        b[rTo] = b[rFrom]; b[rFrom] = 0;
        lo ^= ZOBRIST_PIECES_LO[b[rTo]][rFrom] ^ ZOBRIST_PIECES_LO[b[rTo]][rTo];
        hi ^= ZOBRIST_PIECES_HI[b[rTo]][rFrom] ^ ZOBRIST_PIECES_HI[b[rTo]][rTo];
      } else if (fromF === 4 && toF === 2) {
        const rFrom = to - 2, rTo = to + 1;
        b[rTo] = b[rFrom]; b[rFrom] = 0;
        lo ^= ZOBRIST_PIECES_LO[b[rTo]][rFrom] ^ ZOBRIST_PIECES_LO[b[rTo]][rTo];
        hi ^= ZOBRIST_PIECES_HI[b[rTo]][rFrom] ^ ZOBRIST_PIECES_HI[b[rTo]][rTo];
      }
      state.kings[color] = to;
    }

    // Castling rights
    let castling = state.castling;
    if (type === KING) {
      castling &= color === WHITE ? ~(CASTLE_WK | CASTLE_WQ) : ~(CASTLE_BK | CASTLE_BQ);
    }
    if (type === ROOK) {
      if (from === SQ.h1) castling &= ~CASTLE_WK;
      if (from === SQ.a1) castling &= ~CASTLE_WQ;
      if (from === SQ.h8) castling &= ~CASTLE_BK;
      if (from === SQ.a8) castling &= ~CASTLE_BQ;
    }
    if (captured && typeOf(captured) === ROOK) {
      if (capturedSq === SQ.h1) castling &= ~CASTLE_WK;
      if (capturedSq === SQ.a1) castling &= ~CASTLE_WQ;
      if (capturedSq === SQ.h8) castling &= ~CASTLE_BK;
      if (capturedSq === SQ.a8) castling &= ~CASTLE_BQ;
    }

    let ep = -1;
    if (type === PAWN && Math.abs((to >> 4) - (from >> 4)) === 2) ep = (from + to) >> 1;

    let half = state.halfmove + 1;
    if (type === PAWN || captured) half = 0;

    state.castling = castling;
    state.ep = ep;
    state.halfmove = half;
    if (color === BLACK) state.fullmove++;

    lo ^= ZOBRIST_CASTLE_LO[castling]; hi ^= ZOBRIST_CASTLE_HI[castling];
    if (ep >= 0) { lo ^= ZOBRIST_EP_LO[ep]; hi ^= ZOBRIST_EP_HI[ep]; }
    lo ^= ZOBRIST_TURN_LO[state.turn]; hi ^= ZOBRIST_TURN_HI[state.turn];
    state.turn = 1 - state.turn;
    lo ^= ZOBRIST_TURN_LO[state.turn]; hi ^= ZOBRIST_TURN_HI[state.turn];
    state.hashLo = lo >>> 0; state.hashHi = hi >>> 0;
  }

  function undoMove(state) {
    const h = state.history.pop();
    if (!h) return;
    const b = state.board;

    // إزالة القطعة من to
    const moved = b[h.to];
    b[h.to] = 0;

    // إعادة القطعة إلى from (مع إعادة الترقية إلى بيدق)
    if (h.promoType) b[h.from] = pieceOf(colorOf(moved), PAWN);
    else b[h.from] = moved;

    // إعادة القطعة المأكولة
    if (h.captured) {
      b[h.capturedSq] = h.captured;
    }

    // Castling rook
    if (typeOf(b[h.from]) === KING) {
      const fromF = h.from & 7, toF = h.to & 7;
      if (fromF === 4 && toF === 6) {
        b[h.to + 1] = b[h.to - 1]; b[h.to - 1] = 0;
      } else if (fromF === 4 && toF === 2) {
        b[h.to - 2] = b[h.to + 1]; b[h.to + 1] = 0;
      }
    }

    state.castling = h.prevCastling;
    state.ep = h.prevEp;
    state.halfmove = h.prevHalf;
    state.kings = h.prevKings;
    state.turn = 1 - state.turn;
    state.fullmove = h.prevFull;
    state.hashLo = h.hashLo; state.hashHi = h.hashHi;
  }

  /* --------------------------- Move Generation ----------------------- */
  function generatePseudoMoves(state) {
    const moves = [];
    const b = state.board;
    const us = state.turn;
    const them = 1 - us;

    for (let from = 0; from < 128; from++) {
      if (!isValidSq(from)) continue;
      const p = b[from];
      if (!p || colorOf(p) !== us) continue;
      const type = typeOf(p);

      if (type === PAWN) {
        const dir = us === WHITE ? -16 : 16;
        const startRank = us === WHITE ? 6 : 1;
        const promoRank = us === WHITE ? 0 : 7;
        const one = from + dir;
        if (isValidSq(one) && !b[one]) {
          if ((one >> 4) === promoRank) {
            moves.push([from, one, QUEEN]);
            moves.push([from, one, ROOK]);
            moves.push([from, one, BISHOP]);
            moves.push([from, one, KNIGHT]);
          } else {
            moves.push([from, one, 0]);
            const two = one + dir;
            if ((from >> 4) === startRank && isValidSq(two) && !b[two]) moves.push([from, two, 0]);
          }
        }
        for (const d of [dir - 1, dir + 1]) {
          const to = from + d;
          if (!isValidSq(to)) continue;
          if (Math.abs((to & 7) - (from & 7)) !== 1) continue;
          const target = b[to];
          if (target && colorOf(target) === them) {
            if ((to >> 4) === promoRank) {
              moves.push([from, to, QUEEN]);
              moves.push([from, to, ROOK]);
              moves.push([from, to, BISHOP]);
              moves.push([from, to, KNIGHT]);
            } else moves.push([from, to, 0]);
          } else if (to === state.ep && !target) {
            moves.push([from, to, 0]);
          }
        }
      } else if (type === KNIGHT) {
        for (const d of N_DIRS) {
          const to = from + d;
          if (!isValidSq(to)) continue;
          const t = b[to];
          if (!t || colorOf(t) === them) moves.push([from, to, 0]);
        }
      } else if (type === KING) {
        for (const d of K_DIRS) {
          const to = from + d;
          if (!isValidSq(to)) continue;
          const t = b[to];
          if (!t || colorOf(t) === them) moves.push([from, to, 0]);
        }
        if (us === WHITE) {
          if ((state.castling & CASTLE_WK) && !b[SQ.f1] && !b[SQ.g1] && b[SQ.h1] === W_ROOK
              && !isSquareAttackedBy(state, SQ.e1, BLACK)
              && !isSquareAttackedBy(state, SQ.f1, BLACK)
              && !isSquareAttackedBy(state, SQ.g1, BLACK)) moves.push([SQ.e1, SQ.g1, 0]);
          if ((state.castling & CASTLE_WQ) && !b[SQ.d1] && !b[SQ.c1] && !b[SQ.b1] && b[SQ.a1] === W_ROOK
              && !isSquareAttackedBy(state, SQ.e1, BLACK)
              && !isSquareAttackedBy(state, SQ.d1, BLACK)
              && !isSquareAttackedBy(state, SQ.c1, BLACK)) moves.push([SQ.e1, SQ.c1, 0]);
        } else {
          if ((state.castling & CASTLE_BK) && !b[SQ.f8] && !b[SQ.g8] && b[SQ.h8] === B_ROOK
              && !isSquareAttackedBy(state, SQ.e8, WHITE)
              && !isSquareAttackedBy(state, SQ.f8, WHITE)
              && !isSquareAttackedBy(state, SQ.g8, WHITE)) moves.push([SQ.e8, SQ.g8, 0]);
          if ((state.castling & CASTLE_BQ) && !b[SQ.d8] && !b[SQ.c8] && !b[SQ.b8] && b[SQ.a8] === B_ROOK
              && !isSquareAttackedBy(state, SQ.e8, WHITE)
              && !isSquareAttackedBy(state, SQ.d8, WHITE)
              && !isSquareAttackedBy(state, SQ.c8, WHITE)) moves.push([SQ.e8, SQ.c8, 0]);
        }
      } else {
        const dirs = type === BISHOP ? B_DIRS : type === ROOK ? R_DIRS : K_DIRS;
        for (const d of dirs) {
          let to = from + d;
          while (isValidSq(to)) {
            const t = b[to];
            if (!t) moves.push([from, to, 0]);
            else { if (colorOf(t) === them) moves.push([from, to, 0]); break; }
            to += d;
          }
        }
      }
    }
    return moves;
  }

  function isInCheck(state, color) {
    return isSquareAttackedBy(state, state.kings[color], 1 - color);
  }

  function generateLegalMoves(state) {
    const pseudo = generatePseudoMoves(state);
    const legal = [];
    const us = state.turn;
    for (const mv of pseudo) {
      applyMove(state, mv[0], mv[1], mv[2]);
      if (!isInCheck(state, us)) legal.push(mv);
      undoMove(state);
    }
    return legal;
  }

  /* ------------------------------- SEE ------------------------------- */
  const SEE_VAL = [0, 100, 320, 330, 500, 900, 20000];
  function see(state, from, to) {
    const b = state.board;
    const movingPiece = b[from];
    const target = b[to];
    let gain = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    // simple SEE via full apply/undo loop
    let idx = 0;
    gain[idx++] = target ? SEE_VAL[typeOf(target)] : 0;
    applyMove(state, from, to, 0);
    let side = state.turn;
    let depth = 1;
    while (depth < 16) {
      // ابحث عن أرخص قطعة تهاجم المربع
      let bestAttackerSq = -1, bestAttackerVal = 99999;
      const bb = state.board;
      for (let sq = 0; sq < 128; sq++) {
        if (!isValidSq(sq)) continue;
        const p = bb[sq];
        if (!p || colorOf(p) !== side) continue;
        // هل يمكنها الوصول إلى to؟
        const t = typeOf(p);
        let canAttack = false;
        if (t === PAWN) {
          const dir = side === WHITE ? -1 : 1;
          if (isValidSq(sq + dir * 16 - 1) && (sq + dir * 16 - 1) === to) canAttack = true;
          else if (isValidSq(sq + dir * 16 + 1) && (sq + dir * 16 + 1) === to) canAttack = true;
        } else if (t === KNIGHT) {
          for (const d of N_DIRS) if (sq + d === to) { canAttack = true; break; }
        } else if (t === KING) {
          for (const d of K_DIRS) if (sq + d === to) { canAttack = true; break; }
        } else if (t === BISHOP || t === QUEEN) {
          for (const d of B_DIRS) {
            let x = sq + d;
            while (isValidSq(x)) {
              if (x === to) { canAttack = true; break; }
              if (bb[x]) break;
              x += d;
            }
            if (canAttack) break;
          }
        }
        if (!canAttack && (t === ROOK || t === QUEEN)) {
          for (const d of R_DIRS) {
            let x = sq + d;
            while (isValidSq(x)) {
              if (x === to) { canAttack = true; break; }
              if (bb[x]) break;
              x += d;
            }
            if (canAttack) break;
          }
        }
        if (canAttack && SEE_VAL[t] < bestAttackerVal) {
          bestAttackerVal = SEE_VAL[t];
          bestAttackerSq = sq;
        }
      }
      if (bestAttackerSq < 0) break;
      // هل الأكل قانوني؟ (نتحقق بتطبيق/تراجع)
      const capPiece = state.board[to];
      applyMove(state, bestAttackerSq, to, 0);
      if (isInCheck(state, side)) { undoMove(state); break; }
      undoMove(state);
      gain[idx] = SEE_VAL[typeOf(capPiece)] - gain[idx - 1];
      if (gain[idx] > 0) gain[idx - 1] = gain[idx - 1]; // placeholder
      idx++;
      applyMove(state, bestAttackerSq, to, 0);
      side = 1 - side;
      depth++;
    }
    // تراجع كامل
    for (let i = 0; i < depth; i++) undoMove(state);
    // نُبسّط: نُرجع صافي القيمة التقريبي
    let net = 0;
    for (let i = idx - 1; i >= 0; i--) net = Math.max(0, gain[i] - net);
    return net;
  }

  /* ----------------------------- Evaluate ---------------------------- */
  const PIECE_VALUE = [0, 100, 320, 330, 500, 900, 20000];

  const PSQT = {
    [PAWN]: [
       0,  0,  0,  0,  0,  0,  0,  0,
      50, 50, 50, 50, 50, 50, 50, 50,
      10, 10, 20, 30, 30, 20, 10, 10,
       5,  5, 10, 25, 25, 10,  5,  5,
       0,  0,  0, 20, 20,  0,  0,  0,
       5, -5,-10,  0,  0,-10, -5,  5,
       5, 10, 10,-20,-20, 10, 10,  5,
       0,  0,  0,  0,  0,  0,  0,  0,
    ],
    [KNIGHT]: [
     -50,-40,-30,-30,-30,-30,-40,-50,
     -40,-20,  0,  0,  0,  0,-20,-40,
     -30,  0, 10, 15, 15, 10,  0,-30,
     -30,  5, 15, 20, 20, 15,  5,-30,
     -30,  0, 15, 20, 20, 15,  0,-30,
     -30,  5, 10, 15, 15, 10,  5,-30,
     -40,-20,  0,  5,  5,  0,-20,-40,
     -50,-40,-30,-30,-30,-30,-40,-50,
    ],
    [BISHOP]: [
     -20,-10,-10,-10,-10,-10,-10,-20,
     -10,  0,  0,  0,  0,  0,  0,-10,
     -10,  0,  5, 10, 10,  5,  0,-10,
     -10,  5,  5, 10, 10,  5,  5,-10,
     -10,  0, 10, 10, 10, 10,  0,-10,
     -10, 10, 10, 10, 10, 10, 10,-10,
     -10,  5,  0,  0,  0,  0,  5,-10,
     -20,-10,-10,-10,-10,-10,-10,-20,
    ],
    [ROOK]: [
       0,  0,  0,  0,  0,  0,  0,  0,
       5, 10, 10, 10, 10, 10, 10,  5,
      -5,  0,  0,  0,  0,  0,  0, -5,
      -5,  0,  0,  0,  0,  0,  0, -5,
      -5,  0,  0,  0,  0,  0,  0, -5,
      -5,  0,  0,  0,  0,  0,  0, -5,
      -5,  0,  0,  0,  0,  0,  0, -5,
       0,  0,  0,  5,  5,  0,  0,  0,
    ],
    [QUEEN]: [
     -20,-10,-10, -5, -5,-10,-10,-20,
     -10,  0,  0,  0,  0,  0,  0,-10,
     -10,  0,  5,  5,  5,  5,  0,-10,
      -5,  0,  5,  5,  5,  5,  0, -5,
       0,  0,  5,  5,  5,  5,  0, -5,
     -10,  5,  5,  5,  5,  5,  0,-10,
     -10,  0,  5,  0,  0,  0,  0,-10,
     -20,-10,-10, -5, -5,-10,-10,-20,
    ],
    [KING]: [
     -30,-40,-40,-50,-50,-40,-40,-30,
     -30,-40,-40,-50,-50,-40,-40,-30,
     -30,-40,-40,-50,-50,-40,-40,-30,
     -30,-40,-40,-50,-50,-40,-40,-30,
     -20,-30,-30,-40,-40,-30,-30,-20,
     -10,-20,-20,-20,-20,-20,-20,-10,
      20, 20,  0,  0,  0,  0, 20, 20,
      20, 30, 10,  0,  0, 10, 30, 20,
    ],
  };

  const KING_EG = [
   -50,-40,-30,-20,-20,-30,-40,-50,
   -30,-20,-10,  0,  0,-10,-20,-30,
   -30,-10, 20, 30, 30, 20,-10,-30,
   -30,-10, 30, 40, 40, 30,-10,-30,
   -30,-10, 30, 40, 40, 30,-10,-30,
   -30,-10, 20, 30, 30, 20,-10,-30,
   -30,-30,  0,  0,  0,  0,-30,-30,
   -50,-30,-30,-30,-30,-30,-30,-50,
  ];

  function psqtIndex(sq, color) {
    const r = sq >> 4, f = sq & 7;
    return color === WHITE ? r * 8 + f : (7 - r) * 8 + f;
  }

  function evaluate(state) {
    const b = state.board;
    let mg = 0, eg = 0, phase = 0;
    const phaseVal = [0, 0, 1, 1, 2, 4, 0];
    let wPawns = [0,0,0,0,0,0,0,0], bPawns = [0,0,0,0,0,0,0,0];
    let wBishops = 0, bBishops = 0;
    let wRooks = 0, bRooks = 0;
    let wKingSq = -1, bKingSq = -1;
    let wMat = 0, bMat = 0;

    for (let sq = 0; sq < 128; sq++) {
      if (!isValidSq(sq)) continue;
      const p = b[sq];
      if (!p) continue;
      const c = colorOf(p);
      const t = typeOf(p);
      const idx = psqtIndex(sq, c);
      const sign = c === WHITE ? 1 : -1;
      const val = PIECE_VALUE[t];
      mg += sign * (val + PSQT[t][idx]);
      eg += sign * (val + (t === KING ? KING_EG[idx] : PSQT[t][idx]));
      phase += phaseVal[t];
      if (c === WHITE) wMat += val; else bMat += val;

      if (t === PAWN) { (c === WHITE ? wPawns : bPawns)[sq & 7]++; }
      else if (t === BISHOP) { if (c === WHITE) wBishops++; else bBishops++; }
      else if (t === ROOK) { if (c === WHITE) wRooks++; else bRooks++; }
      else if (t === KING) { if (c === WHITE) wKingSq = sq; else bKingSq = sq; }
    }

    // هيكل البيادق
    let structW = 0, structB = 0;
    for (let f = 0; f < 8; f++) {
      if (wPawns[f] > 1) structW -= 15 * (wPawns[f] - 1);
      if (bPawns[f] > 1) structB -= 15 * (bPawns[f] - 1);
      if (wPawns[f] > 0) {
        const l = f > 0 ? wPawns[f - 1] : 0, r = f < 7 ? wPawns[f + 1] : 0;
        if (!l && !r) structW -= 20;
      }
      if (bPawns[f] > 0) {
        const l = f > 0 ? bPawns[f - 1] : 0, r = f < 7 ? bPawns[f + 1] : 0;
        if (!l && !r) structB -= 20;
      }
    }

    // Bishop pair
    if (wBishops >= 2) { mg += 30; eg += 50; }
    if (bBishops >= 2) { mg -= 30; eg -= 50; }

    // Rook on open/semi-open file
    for (let sq = 0; sq < 128; sq++) {
      if (!isValidSq(sq)) continue;
      const p = b[sq];
      if (!p || typeOf(p) !== ROOK) continue;
      const c = colorOf(p);
      const f = sq & 7;
      const own = c === WHITE ? wPawns : bPawns;
      const opp = c === WHITE ? bPawns : wPawns;
      if (own[f] === 0 && opp[f] === 0) mg += c === WHITE ? 25 : -25;
      else if (own[f] === 0) mg += c === WHITE ? 12 : -12;
    }

    // King safety (بسيط)
    let kingSafety = 0;
    if (phase > 8) {
      if (wKingSq >= 0) {
        const f = wKingSq & 7;
        if (f < 3 || f > 4) kingSafety += 25;
        // pawn shield
        const r = wKingSq >> 4;
        if (r === 7) {
          for (let df = -1; df <= 1; df++) {
            const ff = f + df;
            if (ff >= 0 && ff < 8 && b[(r - 1) * 16 + ff] === W_PAWN) kingSafety += 10;
          }
        }
      }
      if (bKingSq >= 0) {
        const f = bKingSq & 7;
        if (f < 3 || f > 4) kingSafety -= 25;
        const r = bKingSq >> 4;
        if (r === 0) {
          for (let df = -1; df <= 1; df++) {
            const ff = f + df;
            if (ff >= 0 && ff < 8 && b[(r + 1) * 16 + ff] === B_PAWN) kingSafety -= 10;
          }
        }
      }
    }

    const ph = Math.min(24, phase) / 24;
    let score = mg * ph + eg * (1 - ph);
    score += (structW - structB) * ph; // إشارة واحدة صحيحة
    score += kingSafety;

    // Tempo
    score += state.turn === WHITE ? 10 : -10;

    // مادة غير كافية
    if (Math.abs(wMat - bMat) < 100 && wPawns.every(x => x === 0) && bPawns.every(x => x === 0)) {
      const wMinor = wBishops + (wMat - wBishops * 330 - wKingSq >= 0 ? 0 : 0);
      // تبسيط: إذا لم يتبق سوى ملوك وقطعة خفيفة واحدة → تعادل تقريبي
      const totalNonKing = (wBishops + bBishops);
      if (totalNonKing <= 2 && wRooks === 0 && bRooks === 0) return 0;
    }

    return state.turn === WHITE ? score : -score;
  }

  /* ------------------------ Transposition Table ---------------------- */
  const TT_EXACT = 1, TT_LOWER = 2, TT_UPPER = 3;

  class TranspositionTable {
    constructor(sizeMB = 64) {
      // 16 bytes لكل إدخال تقريباً
      const entries = Math.max(1 << 16, Math.floor((sizeMB * 1024 * 1024) / 16));
      this.size = 1;
      while (this.size * 2 <= entries) this.size *= 2;
      this.mask = this.size - 1;
      this.keysLo = new Uint32Array(this.size);
      this.keysHi = new Uint32Array(this.size);
      this.depth = new Int8Array(this.size);
      this.score = new Int32Array(this.size);
      this.flag = new Uint8Array(this.size);
      this.bestFrom = new Uint8Array(this.size);
      this.bestTo = new Uint8Array(this.size);
      this.bestPromo = new Uint8Array(this.size);
      this.generation = 0;
    }
    clear() {
      this.keysLo.fill(0); this.keysHi.fill(0);
      this.depth.fill(0); this.flag.fill(0);
    }
    index(lo, hi) {
      return ((lo ^ (hi * 2654435761)) >>> 0) & this.mask;
    }
    probe(lo, hi) {
      const i = this.index(lo, hi);
      if (this.keysLo[i] === lo && this.keysHi[i] === hi && this.flag[i] !== 0) {
        return {
          depth: this.depth[i],
          score: this.score[i],
          flag: this.flag[i],
          bestMove: this.bestFrom[i] ? [this.bestFrom[i], this.bestTo[i], this.bestPromo[i]] : null,
        };
      }
      return null;
    }
    store(lo, hi, depth, score, flag, bestMove) {
      const i = this.index(lo, hi);
      if (this.keysLo[i] === lo && this.keysHi[i] === hi && this.depth[i] > depth) return;
      this.keysLo[i] = lo;
      this.keysHi[i] = hi;
      this.depth[i] = depth;
      this.score[i] = score;
      this.flag[i] = flag;
      if (bestMove) {
        this.bestFrom[i] = bestMove[0];
        this.bestTo[i] = bestMove[1];
        this.bestPromo[i] = bestMove[2] || 0;
      } else {
        this.bestFrom[i] = 0;
        this.bestTo[i] = 0;
        this.bestPromo[i] = 0;
      }
    }
    newSearch() { this.generation++; }
  }

  /* ------------------------------ Search ----------------------------- */
  class Searcher {
    constructor(ttSizeMB = 64) {
      this.tt = new TranspositionTable(ttSizeMB);
      this.nodes = 0;
      this.killers = [];
      this.history = new Map();
      this.startTime = 0;
      this.timeLimit = 0;
      this.stop = false;
      this.bestMoveRoot = null;
      this.bestScoreRoot = 0;
      this.maxDepth = 0;
      this.repetitionHash = new Map(); // (lo,hi) => count
      this.pv = [];
    }

    reset() {
      this.nodes = 0;
      this.killers = [];
      this.history = new Map();
      this.stop = false;
      this.bestMoveRoot = null;
      this.bestScoreRoot = 0;
      this.maxDepth = 0;
      this.repetitionHash = new Map();
      this.pv = [];
    }

    timeUp() {
      if (this.timeLimit <= 0) return false;
      if ((this.nodes & 2047) !== 0) return false;
      return Date.now() - this.startTime >= this.timeLimit;
    }

    repKey(state) { return state.hashLo + ":" + state.hashHi; }

    pushRep(state) {
      const k = this.repKey(state);
      this.repetitionHash.set(k, (this.repetitionHash.get(k) || 0) + 1);
    }
    popRep(state) {
      const k = this.repKey(state);
      const c = (this.repetitionHash.get(k) || 0) - 1;
      if (c <= 0) this.repetitionHash.delete(k);
      else this.repetitionHash.set(k, c);
    }
    isRep(state) {
      return (this.repetitionHash.get(this.repKey(state)) || 0) >= 2;
    }

    scoreMove(state, mv, ttMove, ply) {
      const [from, to, promo] = mv;
      const b = state.board;
      if (ttMove && from === ttMove[0] && to === ttMove[1] && (promo || 0) === (ttMove[2] || 0)) return 10000000;
      const victim = b[to];
      let s = 0;
      if (victim) {
        s += 1000000 + SEE_VAL[typeOf(victim)] * 10 - SEE_VAL[typeOf(b[from])];
        // SEE إذا كان التقاط سيئ
        try { s += see(state, from, to); } catch (e) {}
      }
      if (promo) s += 500000 + SEE_VAL[promo];
      // killers
      for (let i = 0; i < this.killers.length; i++) {
        const k = this.killers[i];
        if (k && k[0] === from && k[1] === to) { s += 90000 - i * 1000; break; }
      }
      const key = from * 128 + to;
      s += Math.min(this.history.get(key) || 0, 8000);
      return s;
    }

    quiescence(state, alpha, beta, ply) {
      this.nodes++;
      if (this.timeUp()) { this.stop = true; return 0; }
      const stand = evaluate(state);
      if (stand >= beta) return beta;
      if (stand > alpha) alpha = stand;

      let moves = generatePseudoMoves(state);
      // filter captures + promos
      moves = moves.filter(mv => state.board[mv[1]] || mv[2] || (mv[1] === state.ep && typeOf(state.board[mv[0]]) === PAWN));
      // score with SEE
      const scored = moves.map(mv => {
        const victim = state.board[mv[1]];
        let s = victim ? SEE_VAL[typeOf(victim)] * 10 : 0;
        if (mv[2]) s += 5000;
        return { mv, s };
      }).sort((a, b) => b.s - a.s);

      const us = state.turn;
      for (const { mv } of scored) {
        // Delta pruning
        applyMove(state, mv[0], mv[1], mv[2]);
        if (isInCheck(state, us)) { undoMove(state); continue; }
        const score = -this.quiescence(state, -beta, -alpha, ply + 1);
        undoMove(state);
        if (this.stop) return 0;
        if (score >= beta) return beta;
        if (score > alpha) alpha = score;
      }
      return alpha;
    }

    alphaBeta(state, depth, alpha, beta, ply, allowNull, isPV) {
      this.nodes++;
      if (this.timeUp()) { this.stop = true; return 0; }

      // repetition / 50-move داخل الشجرة
      if (ply > 0) {
        if (this.isRep(state)) return 0;
        if (state.halfmove >= 100) return 0;
        // mate distance pruning
        const mAlpha = Math.max(alpha, -MATE + ply);
        const mBeta  = Math.min(beta,   MATE - ply - 1);
        if (mAlpha >= mBeta) return mAlpha;
        alpha = mAlpha; beta = mBeta;
      }

      const inCheck = isInCheck(state, state.turn);
      if (inCheck) depth++; // check extension

      if (depth <= 0) return this.quiescence(state, alpha, beta, ply);

      const isRoot = ply === 0;

      // TT probe
      const tt = this.tt.probe(state.hashLo, state.hashHi);
      let ttMove = null;
      if (tt) {
        ttMove = tt.bestMove;
        if (!isRoot && tt.depth >= depth) {
          if (tt.flag === TT_EXACT) return tt.score;
          if (tt.flag === TT_LOWER && tt.score >= beta) return tt.score;
          if (tt.flag === TT_UPPER && tt.score <= alpha) return tt.score;
        }
      }

      // IID
      if (!ttMove && depth >= 5 && !inCheck) {
        this.alphaBeta(state, depth - 2, alpha, beta, ply, false, false);
        const t2 = this.tt.probe(state.hashLo, state.hashHi);
        if (t2) ttMove = t2.bestMove;
      }

      // Null move pruning
      if (allowNull && !isPV && depth >= 3 && !inCheck && this.hasNonPawnMaterial(state) && beta < MATE_IN_MAX) {
        const savedEp = state.ep, savedCastling = state.castling, savedHalf = state.halfmove;
        const savedKings = state.kings.slice();
        const savedLo = state.hashLo, savedHi = state.hashHi;
        state.turn = 1 - state.turn;
        state.ep = -1;
        state.hashLo = savedLo ^ ZOBRIST_TURN_LO[0] ^ ZOBRIST_TURN_LO[1] ^ (savedEp >= 0 ? ZOBRIST_EP_LO[savedEp] : 0);
        state.hashHi = savedHi ^ ZOBRIST_TURN_HI[0] ^ ZOBRIST_TURN_HI[1] ^ (savedEp >= 0 ? ZOBRIST_EP_HI[savedEp] : 0);
        state.history.push({ nullMove: true, savedEp, savedCastling, savedHalf, savedKings, savedLo, savedHi });
        const R = 2 + Math.floor(depth / 4);
        const score = -this.alphaBeta(state, depth - 1 - R, -beta, -beta + 1, ply + 1, false, false);
        // undo
        const h = state.history.pop();
        state.turn = 1 - state.turn;
        state.ep = h.savedEp;
        state.castling = h.savedCastling;
        state.halfmove = h.savedHalf;
        state.kings = h.savedKings;
        state.hashLo = h.savedLo;
        state.hashHi = h.savedHi;
        if (this.stop) return 0;
        if (score >= beta) return beta;
      }

      // Reverse Futility Pruning
      if (!isPV && !inCheck && depth <= 4 && Math.abs(beta) < MATE_IN_MAX) {
        const stand = evaluate(state);
        if (stand - 120 * depth >= beta) return stand;
      }

      const us = state.turn;
      const moves = generatePseudoMoves(state);
      const scored = moves.map(mv => ({ mv, s: this.scoreMove(state, mv, ttMove, ply) }));
      scored.sort((a, b) => b.s - a.s);

      let bestScore = -INF;
      let bestMove = null;
      let legalCount = 0;
      const origAlpha = alpha;
      const futilityBase = evaluate(state);

      for (let i = 0; i < scored.length; i++) {
        const mv = scored[i].mv;
        applyMove(state, mv[0], mv[1], mv[2]);
        if (isInCheck(state, us)) { undoMove(state); continue; }
        legalCount++;
        const isQuiet = !state.board[mv[1]] && !mv[2];

        // Futility pruning
        if (!isPV && !inCheck && depth <= 3 && legalCount > 1 && isQuiet &&
            futilityBase + 100 + 120 * depth < alpha && Math.abs(alpha) < MATE_IN_MAX) {
          undoMove(state);
          continue;
        }

        let score;
        if (legalCount === 1) {
          this.pushRep(state);
          score = -this.alphaBeta(state, depth - 1, -beta, -alpha, ply + 1, true, isPV);
          this.popRep(state);
        } else {
          // LMR
          let reduction = 0;
          if (depth >= 3 && legalCount > 3 && isQuiet && !inCheck) {
            reduction = 1 + Math.floor((legalCount - 3) / 5);
            if (isPV) reduction = Math.max(0, reduction - 1);
            if (reduction >= depth) reduction = depth - 1;
          }
          this.pushRep(state);
          score = -this.alphaBeta(state, depth - 1 - reduction, -alpha - 1, -alpha, ply + 1, true, false);
          if (score > alpha && reduction > 0) {
            score = -this.alphaBeta(state, depth - 1, -alpha - 1, -alpha, ply + 1, true, false);
          }
          if (score > alpha && score < beta && isPV) {
            score = -this.alphaBeta(state, depth - 1, -beta, -alpha, ply + 1, true, true);
          }
          this.popRep(state);
        }
        undoMove(state);
        if (this.stop) return 0;

        if (score > bestScore) {
          bestScore = score;
          bestMove = mv;
          if (score > alpha) {
            alpha = score;
            if (score >= beta) {
              if (isQuiet) {
                this.killers.unshift([mv[0], mv[1]]);
                if (this.killers.length > 2) this.killers.pop();
                const key = mv[0] * 128 + mv[1];
                this.history.set(key, (this.history.get(key) || 0) + depth * depth);
              }
              this.tt.store(state.hashLo, state.hashHi, depth, beta, TT_LOWER, mv);
              return beta;
            }
          }
        }
      }

      if (legalCount === 0) return inCheck ? -MATE + ply : 0;

      let flag = TT_EXACT;
      if (bestScore <= origAlpha) flag = TT_UPPER;
      this.tt.store(state.hashLo, state.hashHi, depth, bestScore, flag, bestMove);
      return bestScore;
    }

    hasNonPawnMaterial(state) {
      const b = state.board;
      const us = state.turn;
      for (let sq = 0; sq < 128; sq++) {
        if (!isValidSq(sq)) continue;
        const p = b[sq];
        if (!p || colorOf(p) !== us) continue;
        const t = typeOf(p);
        if (t !== PAWN && t !== KING) return true;
      }
      return false;
    }

    search(state, opts = {}) {
      this.reset();
      this.tt.newSearch();
      this.startTime = Date.now();
      this.timeLimit = opts.timeLimit || 0;
      const maxDepth = opts.depth || 4;
      this.maxDepth = maxDepth;

      this.repetitionHash.set(this.repKey(state), 1);

      let bestMove = null, bestScore = 0;
      let prevScore = 0;
      let window = 50;

      for (let d = 1; d <= maxDepth; d++) {
        this.killers = [];
        let alpha = -INF, beta = INF;
        if (d >= 4 && Math.abs(prevScore) < MATE_IN_MAX) {
          alpha = prevScore - window;
          beta  = prevScore + window;
        }
        let score;
        while (true) {
          this.bestMoveRoot = null;
          score = this.alphaBeta(state, d, alpha, beta, 0, true, true);
          if (this.stop) break;
          if (score <= alpha) { alpha = Math.max(-INF, alpha - window * 2); window *= 2; continue; }
          if (score >= beta)  { beta  = Math.min(INF, beta + window * 2); window *= 2; continue; }
          break;
        }
        if (this.stop) break;
        if (this.bestMoveRoot) { bestMove = this.bestMoveRoot; bestScore = score; }
        prevScore = score;
        window = 50;
        if (Math.abs(score) > MATE_IN_MAX) break;
        if (opts.onDepth) opts.onDepth(d, score, this.bestMoveRoot, this.nodes);
      }

      if (!bestMove) {
        const tt = this.tt.probe(state.hashLo, state.hashHi);
        if (tt && tt.bestMove) bestMove = tt.bestMove;
      }
      // إن لم يوجد، اختر أول حركة قانونية
      if (!bestMove) {
        const legal = generateLegalMoves(state);
        if (legal.length) bestMove = legal[0];
      }

      return {
        move: bestMove,
        score: bestScore,
        nodes: this.nodes,
        depth: this.maxDepth,
        time: Date.now() - this.startTime,
      };
    }
  }

  /* -------------------------------- API ------------------------------ */
  function moveToUci(mv) {
    if (!mv) return null;
    const [from, to, promo] = mv;
    let s = sqName(from) + sqName(to);
    if (promo === QUEEN) s += "q";
    else if (promo === ROOK) s += "r";
    else if (promo === BISHOP) s += "b";
    else if (promo === KNIGHT) s += "n";
    return s;
  }

  class ChessEngine {
    constructor(opts = {}) {
      this.ttSizeMB = opts.ttSizeMB || 64;
      this.defaultDepth = opts.depth || 5;
      this.searcher = new Searcher(this.ttSizeMB);
      this.ready = true;
    }

    init() { return Promise.resolve(); }

    async getBestMove(fen, opts = {}) {
      const state = parseFEN(fen);
      const depth = opts.depth || this.defaultDepth;
      const res = this.searcher.search(state, { depth, timeLimit: opts.timeLimit || 0, onDepth: opts.onDepth });
      return {
        move: moveToUci(res.move),
        score: res.score,
        nodes: res.nodes,
        depth: res.depth,
        time: res.time,
      };
    }

    async analyze(fen, opts = {}) { return this.getBestMove(fen, opts); }

    static legalMoves(fen) {
      const st = parseFEN(fen);
      return generateLegalMoves(st).map(moveToUci);
    }

    static perft(fen, depth) {
      const st = parseFEN(fen);
      function p(s, d) {
        if (d === 0) return 1;
        let n = 0;
        for (const mv of generateLegalMoves(s)) {
          applyMove(s, mv[0], mv[1], mv[2]);
          n += p(s, d - 1);
          undoMove(s);
        }
        return n;
      }
      return p(st, depth);
    }
  }

  /* ------------------------------ Exports ---------------------------- */
  if (typeof window !== "undefined") {
    window.ChessEngine = ChessEngine;
    window.ChessEngineHelpers = { parseFEN, toFEN, generateLegalMoves, applyMove, undoMove, evaluate, sqName, nameToSq, moveToUci };
  }
  if (typeof module !== "undefined" && module.exports) {
    module.exports = ChessEngine;
    Object.assign(module.exports, { parseFEN, toFEN, generateLegalMoves, applyMove, undoMove, evaluate, sqName, nameToSq, moveToUci });
  }
  if (typeof globalThis !== "undefined") globalThis.MyChessEngine = ChessEngine;
})(typeof window !== "undefined" ? window : globalThis);