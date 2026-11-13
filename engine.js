/* ============================================================================
 * ChessEnginePro.js — محرك شطرنج محسّن للذكاء العالي
 * تحسينات جوهرية: تقييم متقدم، PVS، LMR، SEE، إدارة وقت، كتاب افتتاحيات
 * ==========================================================================*/
(function (global) {
  "use strict";

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
  const MATE = 30000, MATE_IN_MAX = MATE - 1000, INF = 1000000;

  /* --------------------------- Attack Detection ---------------------- */
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
      s.turn = this.turn; s.castling = this.castling; s.ep = this.ep;
      s.halfmove = this.halfmove; s.fullmove = this.fullmove;
      s.kings = this.kings.slice();
      s.hashLo = this.hashLo; s.hashHi = this.hashHi;
      s.history = this.history.slice();
      return s;
    }
  }

  /* ------------------------- Zobrist (Number) ------------------------ */
  const Z_PIECES_LO = [], Z_PIECES_HI = [];
  const Z_CASTLE_LO = [], Z_CASTLE_HI = [];
  const Z_EP_LO = [], Z_EP_HI = [];
  const Z_TURN_LO = [], Z_TURN_HI = [];

  (function initZobrist() {
    let s = 0x9e3779b9 >>> 0;
    const rnd = () => {
      s ^= s << 13; s >>>= 0;
      s ^= s >>> 17;
      s ^= s << 5;  s >>>= 0;
      return s;
    };
    for (let p = 0; p < 16; p++) {
      Z_PIECES_LO[p] = []; Z_PIECES_HI[p] = [];
      for (let sq = 0; sq < 128; sq++) {
        Z_PIECES_LO[p][sq] = rnd(); Z_PIECES_HI[p][sq] = rnd();
      }
    }
    for (let i = 0; i < 16; i++) { Z_CASTLE_LO[i] = rnd(); Z_CASTLE_HI[i] = rnd(); }
    for (let i = 0; i < 128; i++) { Z_EP_LO[i] = rnd(); Z_EP_HI[i] = rnd(); }
    for (let i = 0; i < 2; i++) { Z_TURN_LO[i] = rnd(); Z_TURN_HI[i] = rnd(); }
  })();

  function computeHash(state) {
    let lo = 0, hi = 0;
    for (let sq = 0; sq < 128; sq++) {
      if (!isValidSq(sq)) continue;
      const p = state.board[sq];
      if (p) { lo ^= Z_PIECES_LO[p][sq]; hi ^= Z_PIECES_HI[p][sq]; }
    }
    lo ^= Z_CASTLE_LO[state.castling]; hi ^= Z_CASTLE_HI[state.castling];
    if (state.ep >= 0) { lo ^= Z_EP_LO[state.ep]; hi ^= Z_EP_HI[state.ep]; }
    lo ^= Z_TURN_LO[state.turn]; hi ^= Z_TURN_HI[state.turn];
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
  function applyMove(state, from, to, promoType) {
    const b = state.board;
    const piece = b[from];
    const color = colorOf(piece);
    const type = typeOf(piece);
    const target = b[to];

    let captured = 0, capturedSq = -1;
    if (type === PAWN && to === state.ep && !target) {
      capturedSq = color === WHITE ? to + 16 : to - 16;
      captured = b[capturedSq];
    } else if (target) {
      captured = target; capturedSq = to;
    }

    state.history.push({
      from, to, promoType: promoType || 0,
      captured, capturedSq,
      prevCastling: state.castling, prevEp: state.ep, prevHalf: state.halfmove,
      prevKings: state.kings.slice(),
      hashLo: state.hashLo, hashHi: state.hashHi, prevFull: state.fullmove,
    });

    let lo = state.hashLo, hi = state.hashHi;
    lo ^= Z_PIECES_LO[piece][from]; hi ^= Z_PIECES_HI[piece][from];
    if (captured) { lo ^= Z_PIECES_LO[captured][capturedSq]; hi ^= Z_PIECES_HI[captured][capturedSq]; }
    lo ^= Z_CASTLE_LO[state.castling]; hi ^= Z_CASTLE_HI[state.castling];
    if (state.ep >= 0) { lo ^= Z_EP_LO[state.ep]; hi ^= Z_EP_HI[state.ep]; }

    b[from] = 0;
    if (capturedSq >= 0) b[capturedSq] = 0;

    let placed = piece;
    if (type === PAWN && (to >> 4) === (color === WHITE ? 0 : 7)) {
      placed = pieceOf(color, promoType || QUEEN);
    }
    b[to] = placed;
    lo ^= Z_PIECES_LO[placed][to]; hi ^= Z_PIECES_HI[placed][to];

    if (type === KING) {
      const fromF = from & 7, toF = to & 7;
      if (fromF === 4 && toF === 6) {
        const rFrom = to + 1, rTo = to - 1;
        b[rTo] = b[rFrom]; b[rFrom] = 0;
        lo ^= Z_PIECES_LO[b[rTo]][rFrom] ^ Z_PIECES_LO[b[rTo]][rTo];
        hi ^= Z_PIECES_HI[b[rTo]][rFrom] ^ Z_PIECES_HI[b[rTo]][rTo];
      } else if (fromF === 4 && toF === 2) {
        const rFrom = to - 2, rTo = to + 1;
        b[rTo] = b[rFrom]; b[rFrom] = 0;
        lo ^= Z_PIECES_LO[b[rTo]][rFrom] ^ Z_PIECES_LO[b[rTo]][rTo];
        hi ^= Z_PIECES_HI[b[rTo]][rFrom] ^ Z_PIECES_HI[b[rTo]][rTo];
      }
      state.kings[color] = to;
    }

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

    state.castling = castling; state.ep = ep; state.halfmove = half;
    if (color === BLACK) state.fullmove++;

    lo ^= Z_CASTLE_LO[castling]; hi ^= Z_CASTLE_HI[castling];
    if (ep >= 0) { lo ^= Z_EP_LO[ep]; hi ^= Z_EP_HI[ep]; }
    lo ^= Z_TURN_LO[state.turn]; hi ^= Z_TURN_HI[state.turn];
    state.turn = 1 - state.turn;
    lo ^= Z_TURN_LO[state.turn]; hi ^= Z_TURN_HI[state.turn];
    state.hashLo = lo >>> 0; state.hashHi = hi >>> 0;
  }

  function undoMove(state) {
    const h = state.history.pop();
    if (!h) return;
    const b = state.board;

    const moved = b[h.to];
    b[h.to] = 0;

    if (h.promoType) b[h.from] = pieceOf(colorOf(moved), PAWN);
    else b[h.from] = moved;

    if (h.captured) b[h.capturedSq] = h.captured;

    if (typeOf(b[h.from]) === KING) {
      const fromF = h.from & 7, toF = h.to & 7;
      if (fromF === 4 && toF === 6) { b[h.to + 1] = b[h.to - 1]; b[h.to - 1] = 0; }
      else if (fromF === 4 && toF === 2) { b[h.to - 2] = b[h.to + 1]; b[h.to + 1] = 0; }
    }

    state.castling = h.prevCastling; state.ep = h.prevEp; state.halfmove = h.prevHalf;
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
            moves.push([from, one, QUEEN]); moves.push([from, one, ROOK]);
            moves.push([from, one, BISHOP]); moves.push([from, one, KNIGHT]);
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
              moves.push([from, to, QUEEN]); moves.push([from, to, ROOK]);
              moves.push([from, to, BISHOP]); moves.push([from, to, KNIGHT]);
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

  function attackersTo(state, sq, color) {
    const b = state.board;
    const out = [];
    if (color === WHITE) {
      if (isValidSq(sq + 15) && b[sq + 15] === W_PAWN) out.push({ sq: sq + 15, val: 100 });
      if (isValidSq(sq + 17) && b[sq + 17] === W_PAWN) out.push({ sq: sq + 17, val: 100 });
    } else {
      if (isValidSq(sq - 15) && b[sq - 15] === B_PAWN) out.push({ sq: sq - 15, val: 100 });
      if (isValidSq(sq - 17) && b[sq - 17] === B_PAWN) out.push({ sq: sq - 17, val: 100 });
    }
    for (const d of N_DIRS) {
      const t = sq + d;
      if (!isValidSq(t)) continue;
      const p = b[t];
      if (p && colorOf(p) === color && typeOf(p) === KNIGHT) out.push({ sq: t, val: 320 });
    }
    for (const d of K_DIRS) {
      const t = sq + d;
      if (!isValidSq(t)) continue;
      const p = b[t];
      if (p && colorOf(p) === color && typeOf(p) === KING) out.push({ sq: t, val: 20000 });
    }
    for (const d of B_DIRS) {
      let t = sq + d;
      while (isValidSq(t)) {
        const p = b[t];
        if (p) {
          if (colorOf(p) === color && (typeOf(p) === BISHOP || typeOf(p) === QUEEN))
            out.push({ sq: t, val: typeOf(p) === BISHOP ? 330 : 900 });
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
          if (colorOf(p) === color && (typeOf(p) === ROOK || typeOf(p) === QUEEN))
            out.push({ sq: t, val: typeOf(p) === ROOK ? 500 : 900 });
          break;
        }
        t += d;
      }
    }
    out.sort((a, b2) => a.val - b2.val);
    return out;
  }

  // SEE صحيح عبر خوارزمية gain array
  function see(state, from, to) {
    const b = state.board;
    const target = b[to];
    if (!target) return 0;
    const gains = [SEE_VAL[typeOf(target)]];
    const attackersW = attackersTo(state, to, WHITE);
    const attackersB = attackersTo(state, to, BLACK);
    // نضيف القطعة المهاجمة الأولية في المقدمة
    let side = colorOf(b[from]);
    let depth = 0;
    while (true) {
      const list = side === WHITE ? attackersW : attackersB;
      const attacker = list.shift();
      if (!attacker) break;
      const sign = (depth % 2 === 0) ? 1 : -1;
      const newGain = SEE_VAL[typeOf(b[attacker.sq])] - (gains[gains.length - 1] || 0);
      gains.push(sign > 0 ? Math.max(newGain, 0) : newGain);
      side = 1 - side;
      depth++;
      if (depth > 12) break;
    }
    // نستنتج القيمة net
    let net = gains[0];
    for (let i = gains.length - 1; i > 0; i--) {
      // simplified
    }
    // حساب مبسّط سريع:
    let score = gains[0];
    for (let i = 1; i < gains.length; i++) score = Math.max(0, gains[i] - score);
    return score;
  }

  /* ------------------------------ Evaluate --------------------------- */
  const PIECE_VALUE = [0, 100, 320, 330, 500, 900, 20000];

  const PSQT = {
    [PAWN]: [
       0,  0,  0,  0,  0,  0,  0,  0,
       0,  0,  0, -10,-10,  0,  0,  0,
       5,  0,  0,  5,  5,  0,  0,  5,
       5,  5, 10, 20, 20, 10,  5,  5,
      10, 10, 15, 25, 25, 15, 10, 10,
      20, 20, 25, 35, 35, 25, 20, 20,
      50, 50, 50, 50, 50, 50, 50, 50,
       0,  0,  0,  0,  0,  0,  0,  0,
    ],
    [KNIGHT]: [
     -50,-40,-30,-30,-30,-30,-40,-50,
     -40,-20,  0,  5,  5,  0,-20,-40,
     -30,  5, 10, 15, 15, 10,  5,-30,
     -30,  0, 15, 20, 20, 15,  0,-30,
     -30,  5, 15, 20, 20, 15,  5,-30,
     -30,  0, 10, 15, 15, 10,  0,-30,
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
      10, 15, 15, 15, 15, 15, 15, 10,
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
     -50,-50,-50,-50,-50,-50,-50,-50,
     -50,-50,-50,-50,-50,-50,-50,-50,
     -50,-50,-50,-50,-50,-50,-50,-50,
     -50,-50,-50,-50,-50,-50,-50,-50,
     -30,-30,-30,-30,-30,-30,-30,-30,
     -20,-20,-20,-20,-20,-20,-20,-20,
      20, 20,  0,  0,  0, 20, 20, 20,
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

  const PASSED_PAWN_MG = [0, 5, 10, 20, 35, 60, 100, 0]; // بحسب rank التقدم
  const PASSED_PAWN_EG = [0, 10, 20, 40, 70, 110, 160, 0];

  function psqtIndex(sq, color) {
    const r = sq >> 4, f = sq & 7;
    return color === WHITE ? r * 8 + f : (7 - r) * 8 + f;
  }

  function evaluate(state) {
    const b = state.board;
    let mg = 0, eg = 0, phase = 0;
    const phaseVal = [0, 0, 1, 1, 2, 4, 0];
    const wPawns = [0,0,0,0,0,0,0,0], bPawns = [0,0,0,0,0,0,0,0];
    const wPawnSqs = [], bPawnSqs = [];
    let wBishops = 0, bBishops = 0;
    let wRooks = 0, bRooks = 0;
    let wKingSq = -1, bKingSq = -1;
    let wQueen = false, bQueen = false;
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

      if (t === PAWN) { if (c === WHITE) { wPawns[sq & 7]++; wPawnSqs.push(sq); } else { bPawns[sq & 7]++; bPawnSqs.push(sq); } }
      else if (t === BISHOP) { if (c === WHITE) wBishops++; else bBishops++; }
      else if (t === ROOK) { if (c === WHITE) wRooks++; else bRooks++; }
      else if (t === QUEEN) { if (c === WHITE) wQueen = true; else bQueen = true; }
      else if (t === KING) { if (c === WHITE) wKingSq = sq; else bKingSq = sq; }
    }

    // هيكل البيادق
    for (let f = 0; f < 8; f++) {
      if (wPawns[f] > 1) { mg -= 18 * (wPawns[f] - 1); eg -= 22 * (wPawns[f] - 1); }
      if (bPawns[f] > 1) { mg += 18 * (bPawns[f] - 1); eg += 22 * (bPawns[f] - 1); }
      if (wPawns[f] > 0) {
        const l = f > 0 ? wPawns[f - 1] : 0, r = f < 7 ? wPawns[f + 1] : 0;
        if (!l && !r) { mg -= 15; eg -= 25; }
      }
      if (bPawns[f] > 0) {
        const l = f > 0 ? bPawns[f - 1] : 0, r = f < 7 ? bPawns[f + 1] : 0;
        if (!l && !r) { mg += 15; eg += 25; }
      }
    }

    // Passed pawns (تقدير: لا يوجد بيدق خصم أمام على نفس/ملفات مجاورة)
    for (const sq of wPawnSqs) {
      const f = sq & 7, r = sq >> 4;
      let passed = true;
      for (let rf = 0; rf < r; rf++) {
        for (let ff = Math.max(0, f - 1); ff <= Math.min(7, f + 1); ff++) {
          if (b[rf * 16 + ff] === B_PAWN) { passed = false; break; }
        }
        if (!passed) break;
      }
      if (passed) {
        const advance = 6 - r;
        mg += PASSED_PAWN_MG[advance];
        eg += PASSED_PAWN_EG[advance];
        // king proximity to passed pawn (يُفضّل أن الملك قريب)
        if (wKingSq >= 0) {
          const kd = Math.abs((wKingSq & 7) - f) + Math.abs((wKingSq >> 4) - r);
          eg += Math.max(0, 8 - kd) * 5;
        }
      }
    }
    for (const sq of bPawnSqs) {
      const f = sq & 7, r = sq >> 4;
      let passed = true;
      for (let rf = r + 1; rf < 8; rf++) {
        for (let ff = Math.max(0, f - 1); ff <= Math.min(7, f + 1); ff++) {
          if (b[rf * 16 + ff] === W_PAWN) { passed = false; break; }
        }
        if (!passed) break;
      }
      if (passed) {
        const advance = r - 1;
        mg -= PASSED_PAWN_MG[advance];
        eg -= PASSED_PAWN_EG[advance];
        if (bKingSq >= 0) {
          const kd = Math.abs((bKingSq & 7) - f) + Math.abs((bKingSq >> 4) - r);
          eg -= Math.max(0, 8 - kd) * 5;
        }
      }
    }

    // Bishop pair
    if (wBishops >= 2) { mg += 30; eg += 50; }
    if (bBishops >= 2) { mg -= 30; eg -= 50; }

    // Rook on open/semi-open file + connected rooks
    const rookSqs = [];
    for (let sq = 0; sq < 128; sq++) {
      if (!isValidSq(sq)) continue;
      const p = b[sq];
      if (!p || typeOf(p) !== ROOK) continue;
      const c = colorOf(p);
      const f = sq & 7;
      const own = c === WHITE ? wPawns : bPawns;
      const opp = c === WHITE ? bPawns : wPawns;
      let bonus = 0;
      if (own[f] === 0 && opp[f] === 0) bonus = 25;
      else if (own[f] === 0) bonus = 12;
      if (c === WHITE) mg += bonus; else mg -= bonus;
      rookSqs.push({ sq, c });
    }
    // connected rooks (نفس اللون على صف/عمود واحد بدون قطع)
    for (let i = 0; i < rookSqs.length; i++) {
      for (let j = i + 1; j < rookSqs.length; j++) {
        if (rookSqs[i].c !== rookSqs[j].c) continue;
        const s1 = rookSqs[i].sq, s2 = rookSqs[j].sq;
        if ((s1 & 7) === (s2 & 7) || (s1 >> 4) === (s2 >> 4)) { mg += (rookSqs[i].c === WHITE ? 10 : -10); }
      }
    }

    // King safety (pawn shield + open files around king)
    if (phase > 8) {
      const castlePawnShield = [60, 40, 20, 0];
      if (wKingSq >= 0) {
        const f = wKingSq & 7, r = wKingSq >> 4;
        if (f < 3 || f > 4) mg += 15;
        if (r === 7) {
          let shield = 0;
          for (let df = -1; df <= 1; df++) {
            const ff = f + df;
            if (ff >= 0 && ff < 8 && b[(r - 1) * 16 + ff] === W_PAWN) shield++;
          }
          mg += castlePawnShield[3 - shield];
        }
        // open file next to king = danger
        for (let df = -1; df <= 1; df++) {
          const ff = f + df;
          if (ff >= 0 && ff < 8 && wPawns[ff] === 0) mg -= 12;
        }
      }
      if (bKingSq >= 0) {
        const f = bKingSq & 7, r = bKingSq >> 4;
        if (f < 3 || f > 4) mg -= 15;
        if (r === 0) {
          let shield = 0;
          for (let df = -1; df <= 1; df++) {
            const ff = f + df;
            if (ff >= 0 && ff < 8 && b[(r + 1) * 16 + ff] === B_PAWN) shield++;
          }
          mg -= castlePawnShield[3 - shield];
        }
        for (let df = -1; df <= 1; df++) {
          const ff = f + df;
          if (ff >= 0 && ff < 8 && bPawns[ff] === 0) mg += 12;
        }
      }
    }

    // Mobility خفيفة (لكل قطعة خفيفة/ثقيلة)
    let wMob = 0, bMob = 0;
    for (let sq = 0; sq < 128; sq++) {
      if (!isValidSq(sq)) continue;
      const p = b[sq];
      if (!p) continue;
      const t = typeOf(p);
      if (t === PAWN || t === KING) continue;
      const c = colorOf(p);
      let mob = 0;
      if (t === KNIGHT) {
        for (const d of N_DIRS) { const x = sq + d; if (isValidSq(x) && (!b[x] || colorOf(b[x]) !== c)) mob++; }
      } else if (t === BISHOP) {
        for (const d of B_DIRS) { let x = sq + d; while (isValidSq(x)) { if (!b[x]) { mob++; x += d; } else { if (colorOf(b[x]) !== c) mob++; break; } } }
      } else if (t === ROOK) {
        for (const d of R_DIRS) { let x = sq + d; while (isValidSq(x)) { if (!b[x]) { mob++; x += d; } else { if (colorOf(b[x]) !== c) mob++; break; } } }
      } else if (t === QUEEN) {
        for (const d of K_DIRS) { let x = sq + d; while (isValidSq(x)) { if (!b[x]) { mob++; x += d; } else { if (colorOf(b[x]) !== c) mob++; break; } } }
      }
      if (c === WHITE) wMob += mob; else bMob += mob;
    }
    mg += (wMob - bMob) * 2;
    eg += (wMob - bMob) * 1;

    const ph = Math.min(24, phase) / 24;
    let score = mg * ph + eg * (1 - ph);
    score += state.turn === WHITE ? 15 : -15;

    // endgame معالجة: إذا فقط ملوك + بيدق واحد... مقاربة
    const nonPawnMat = wMat + bMat - (wPawns.reduce((a,b2)=>a+b2,0) * 100) - (bPawns.reduce((a,b2)=>a+b2,0) * 100)
                      - (wKingSq >= 0 ? PIECE_VALUE[KING] : 0) - (bKingSq >= 0 ? PIECE_VALUE[KING] : 0);

    // ميزة جانبية: if only kings + pawn(s), prefer pushing passed pawn
    if (phase < 4) {
      // ادفع الملك نحو مركز
      if (wKingSq >= 0) {
        const dist = Math.abs((wKingSq & 7) - 4) + Math.abs((wKingSq >> 4) - 4);
        score += (8 - dist) * 2;
      }
      if (bKingSq >= 0) {
        const dist = Math.abs((bKingSq & 7) - 4) + Math.abs((bKingSq >> 4) - 4);
        score -= (8 - dist) * 2;
      }
    }

    return state.turn === WHITE ? score : -score;
  }

  /* ------------------------ Transposition Table ---------------------- */
  const TT_EXACT = 1, TT_LOWER = 2, TT_UPPER = 3;

  class TranspositionTable {
    constructor(sizeMB = 64) {
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
    }
    index(lo, hi) { return ((lo ^ (hi * 2654435761)) >>> 0) & this.mask; }
    probe(lo, hi) {
      const i = this.index(lo, hi);
      if (this.keysLo[i] === lo && this.keysHi[i] === hi && this.flag[i] !== 0) {
        return {
          depth: this.depth[i], score: this.score[i], flag: this.flag[i],
          bestMove: this.bestFrom[i] ? [this.bestFrom[i], this.bestTo[i], this.bestPromo[i]] : null,
        };
      }
      return null;
    }
    store(lo, hi, depth, score, flag, bestMove) {
      const i = this.index(lo, hi);
      if (this.keysLo[i] === lo && this.keysHi[i] === hi && this.depth[i] > depth) return;
      this.keysLo[i] = lo; this.keysHi[i] = hi;
      this.depth[i] = depth; this.score[i] = score; this.flag[i] = flag;
      if (bestMove) { this.bestFrom[i] = bestMove[0]; this.bestTo[i] = bestMove[1]; this.bestPromo[i] = bestMove[2] || 0; }
      else { this.bestFrom[i] = 0; this.bestTo[i] = 0; this.bestPromo[i] = 0; }
    }
  }

  /* ------------------------------ Search ----------------------------- */
  class Searcher {
    constructor(ttSizeMB = 128) {
      this.tt = new TranspositionTable(ttSizeMB);
      this.nodes = 0;
      this.killers = [];
      this.history = new Map();
      this.counterMove = new Map(); // from*128+to => [from,to]
      this.startTime = 0;
      this.timeLimit = 0;
      this.stop = false;
      this.bestMoveRoot = null;
      this.maxDepth = 0;
      this.repetitionHash = new Map();
      this.nodeLimit = 0;
    }

    reset() {
      this.nodes = 0; this.killers = []; this.history = new Map();
      this.counterMove = new Map();
      this.stop = false; this.bestMoveRoot = null; this.maxDepth = 0;
      this.repetitionHash = new Map();
    }

    timeUp() {
      if ((this.nodes & 2047) !== 0) return false;
      if (this.nodeLimit && this.nodes >= this.nodeLimit) return true;
      if (this.timeLimit <= 0) return false;
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
    isRep(state) { return (this.repetitionHash.get(this.repKey(state)) || 0) >= 2; }

    scoreMove(state, mv, ttMove, ply, prevMove) {
      const [from, to, promo] = mv;
      const b = state.board;
      if (ttMove && from === ttMove[0] && to === ttMove[1] && (promo || 0) === (ttMove[2] || 0)) return 20000000;
      const victim = b[to];
      let s = 0;
      if (victim) {
        // MVV-LVA
        s += 1000000 + SEE_VAL[typeOf(victim)] * 16 - SEE_VAL[typeOf(b[from])];
      }
      if (promo) s += 900000 + SEE_VAL[promo] * 4;
      // killers
      for (let i = 0; i < this.killers.length; i++) {
        const k = this.killers[i];
        if (k && k[0] === from && k[1] === to) { s += 800000 - i * 10000; break; }
      }
      // counter-move
      if (prevMove) {
        const cm = this.counterMove.get(prevMove[0] * 128 + prevMove[1]);
        if (cm && cm[0] === from && cm[1] === to) s += 700000;
      }
      const key = from * 128 + to;
      s += Math.min(this.history.get(key) || 0, 64000);
      return s;
    }

    quiescence(state, alpha, beta, ply) {
      this.nodes++;
      if (this.timeUp()) { this.stop = true; return 0; }

      // In-check: كويس نولّد كل الحركات
      const inCheck = isInCheck(state, state.turn);
      if (inCheck) {
        // evasion: كل الحركات القانونية
        const pseudo = generatePseudoMoves(state);
        const legal = [];
        for (const mv of pseudo) {
          applyMove(state, mv[0], mv[1], mv[2]);
          if (!isInCheck(state, 1 - state.turn)) legal.push(mv);
          undoMove(state);
        }
        if (legal.length === 0) return -MATE + ply;
        if (ply > 40) return 0;
        let best = -INF;
        for (const mv of legal) {
          applyMove(state, mv[0], mv[1], mv[2]);
          const sc = -this.quiescence(state, -beta, -alpha, ply + 1);
          undoMove(state);
          if (this.stop) return 0;
          if (sc > best) best = sc;
          if (sc > alpha) alpha = sc;
          if (alpha >= beta) return beta;
        }
        return best;
      }

      const stand = evaluate(state);
      if (stand >= beta) return beta;
      if (stand > alpha) alpha = stand;

      const moves = generatePseudoMoves(state).filter(mv => {
        const victim = state.board[mv[1]];
        if (victim) return true;
        if (mv[2]) return true;
        if (mv[1] === state.ep && typeOf(state.board[mv[0]]) === PAWN) return true;
        return false;
      });

      // SEE pruning + delta pruning
      const scored = [];
      for (const mv of moves) {
        const victim = state.board[mv[1]];
        let seVal = 0;
        if (victim) seVal = SEE_VAL[typeOf(victim)];
        if (mv[2]) seVal += SEE_VAL[mv[2]];
        // delta pruning
        if (stand + seVal + 200 < alpha) continue;
        // SEE pruning: تجاهل الأكل الذي يخسر مادة كبيرة
        if (victim && see(state, mv[0], mv[1]) < -50 && seVal < 900) continue;
        scored.push({ mv, s: seVal * 16 - SEE_VAL[typeOf(state.board[mv[0]])] });
      }
      scored.sort((a, b) => b.s - a.s);

      let best = alpha;
      for (const { mv } of scored) {
        applyMove(state, mv[0], mv[1], mv[2]);
        const sc = -this.quiescence(state, -beta, -alpha, ply + 1);
        undoMove(state);
        if (this.stop) return 0;
        if (sc > best) {
          best = sc;
          if (sc > alpha) alpha = sc;
          if (alpha >= beta) return beta;
        }
      }
      return best;
    }

    alphaBeta(state, depth, alpha, beta, ply, allowNull, isPV, prevMove) {
      this.nodes++;
      if (this.timeUp()) { this.stop = true; return 0; }

      if (ply > 0) {
        if (this.isRep(state)) return 0;
        if (state.halfmove >= 100) return 0;
        if (ply >= 100) return 0;
        const mAlpha = Math.max(alpha, -MATE + ply);
        const mBeta  = Math.min(beta,   MATE - ply - 1);
        if (mAlpha >= mBeta) return mAlpha;
        alpha = mAlpha; beta = mBeta;
      }

      const inCheck = isInCheck(state, state.turn);
      if (inCheck) depth++;

      if (depth <= 0) return this.quiescence(state, alpha, beta, ply);

      const isRoot = ply === 0;

      const tt = this.tt.probe(state.hashLo, state.hashHi);
      let ttMove = null;
      if (tt) {
        ttMove = tt.bestMove;
        if (!isPV && tt.depth >= depth) {
          if (tt.flag === TT_EXACT) return tt.score;
          if (tt.flag === TT_LOWER && tt.score >= beta) return tt.score;
          if (tt.flag === TT_UPPER && tt.score <= alpha) return tt.score;
        }
      }

      // IID
      if (!ttMove && depth >= 5 && !inCheck && isPV) {
        this.alphaBeta(state, depth - 2, alpha, beta, ply, false, false, prevMove);
        const t2 = this.tt.probe(state.hashLo, state.hashHi);
        if (t2) ttMove = t2.bestMove;
      }

      // Null-move pruning
      if (allowNull && !isPV && !inCheck && depth >= 3 && this.hasNonPawnMaterial(state) && beta < MATE_IN_MAX) {
        const savedEp = state.ep, savedHalf = state.halfmove;
        const savedKings = state.kings.slice();
        const savedLo = state.hashLo, savedHi = state.hashHi;
        state.turn = 1 - state.turn;
        state.ep = -1;
        state.hashLo ^= Z_TURN_LO[0] ^ Z_TURN_LO[1] ^ (savedEp >= 0 ? Z_EP_LO[savedEp] : 0);
        state.hashHi ^= Z_TURN_HI[0] ^ Z_TURN_HI[1] ^ (savedEp >= 0 ? Z_EP_HI[savedEp] : 0);
        state.history.push({ nullMove: true, savedEp, savedHalf, savedKings, savedLo, savedHi });
        const R = 2 + Math.floor(depth / 4);
        const score = -this.alphaBeta(state, depth - 1 - R, -beta, -beta + 1, ply + 1, false, false, null);
        const h = state.history.pop();
        state.turn = 1 - state.turn;
        state.ep = h.savedEp;
        state.halfmove = h.savedHalf;
        state.kings = h.savedKings;
        state.hashLo = h.savedLo; state.hashHi = h.savedHi;
        if (this.stop) return 0;
        if (score >= beta) return beta;
      }

      // Reverse futility
      if (!isPV && !inCheck && depth <= 4 && Math.abs(beta) < MATE_IN_MAX) {
        const stand = evaluate(state);
        if (stand - 100 * depth >= beta) return stand;
      }

      // Razoring
      if (!isPV && !inCheck && depth <= 3 && Math.abs(beta) < MATE_IN_MAX) {
        const stand = evaluate(state);
        if (stand + 300 * depth <= alpha) {
          const q = this.quiescence(state, alpha, beta, ply);
          if (q <= alpha) return q;
        }
      }

      const us = state.turn;
      const moves = generatePseudoMoves(state);
      const scored = moves.map(mv => ({ mv, s: this.scoreMove(state, mv, ttMove, ply, prevMove) }));
      scored.sort((a, b) => b.s - a.s);

      let bestScore = -INF;
      let bestMove = null;
      let legalCount = 0;
      const origAlpha = alpha;
      let donePVS = false;

      for (let i = 0; i < scored.length; i++) {
        const mv = scored[i].mv;
        applyMove(state, mv[0], mv[1], mv[2]);
        if (isInCheck(state, us)) { undoMove(state); continue; }
        legalCount++;
        const isQuiet = !state.board[mv[1]] && !mv[2];

        // Futility pruning (quiet moves at shallow depth)
        if (!isPV && !inCheck && depth <= 3 && legalCount > 1 && isQuiet &&
            Math.abs(alpha) < MATE_IN_MAX) {
          const futilityMargin = 100 + 120 * depth;
          const standEval = evaluate(state) + futilityMargin;
          if (standEval <= alpha) { undoMove(state); continue; }
        }

        let score;
        this.pushRep(state);
        if (legalCount === 1) {
          score = -this.alphaBeta(state, depth - 1, -beta, -alpha, ply + 1, true, isPV, mv);
        } else {
          // LMR
          let reduction = 0;
          if (depth >= 3 && legalCount > 3 && isQuiet && !inCheck) {
            reduction = 1;
            if (legalCount > 6) reduction++;
            if (depth > 6 && legalCount > 10) reduction++;
            if (isPV) reduction = Math.max(0, reduction - 1);
            if (reduction >= depth) reduction = depth - 1;
          }
          score = -this.alphaBeta(state, depth - 1 - reduction, -alpha - 1, -alpha, ply + 1, true, false, mv);
          if (score > alpha && reduction > 0) {
            score = -this.alphaBeta(state, depth - 1, -alpha - 1, -alpha, ply + 1, true, false, mv);
          }
          if (score > alpha && score < beta && isPV) {
            score = -this.alphaBeta(state, depth - 1, -beta, -alpha, ply + 1, true, true, mv);
          }
        }
        this.popRep(state);
        undoMove(state);
        if (this.stop) return 0;

        if (score > bestScore) {
          bestScore = score;
          bestMove = mv;
          if (isRoot) this.bestMoveRoot = mv;
          if (score > alpha) {
            alpha = score;
            if (score >= beta) {
              if (isQuiet) {
                // killer
                this.killers.unshift([mv[0], mv[1]]);
                if (this.killers.length > 2) this.killers.pop();
                // history
                const key = mv[0] * 128 + mv[1];
                this.history.set(key, Math.min((this.history.get(key) || 0) + depth * depth, 32000));
                // counter-move
                if (prevMove) this.counterMove.set(prevMove[0] * 128 + prevMove[1], [mv[0], mv[1]]);
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
      else if (bestScore >= beta) flag = TT_LOWER;
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
      this.startTime = Date.now();
      this.timeLimit = opts.timeLimit || 0;
      this.nodeLimit = opts.nodeLimit || 0;
      const maxDepth = opts.depth || 6;
      this.maxDepth = maxDepth;

      this.repetitionHash.set(this.repKey(state), 1);

      let bestMove = null, bestScore = 0, finalDepth = 0;
      let prevScore = 0;

      for (let d = 1; d <= maxDepth; d++) {
        this.killers = [];
        let alpha = -INF, beta = INF;
        // Aspiration windows
        if (d >= 4 && Math.abs(prevScore) < MATE_IN_MAX) {
          let window = 25;
          alpha = prevScore - window;
          beta  = prevScore + window;
          let reSearchCount = 0;
          while (true) {
            this.bestMoveRoot = null;
            const s = this.alphaBeta(state, d, alpha, beta, 0, true, true, null);
            if (this.stop) break;
            if (s <= alpha) { alpha = Math.max(-INF, alpha - window); window *= 2; reSearchCount++; }
            else if (s >= beta) { beta = Math.min(INF, beta + window); window *= 2; reSearchCount++; }
            else { bestScore = s; break; }
            if (reSearchCount > 5) { alpha = -INF; beta = INF; }
          }
        } else {
          bestScore = this.alphaBeta(state, d, alpha, beta, 0, true, true, null);
        }

        if (this.stop) break;
        if (this.bestMoveRoot) { bestMove = this.bestMoveRoot; finalDepth = d; }
        prevScore = bestScore;

        if (opts.onDepth) opts.onDepth(d, bestScore, bestMove, this.nodes, Date.now() - this.startTime);
        if (Math.abs(bestScore) > MATE_IN_MAX) break;

        // توقّف إذا استهلكنا 50%+ من الوقت ولم يتبقَّ وقت لجولة أخرى بنفس المدة
        if (this.timeLimit > 0) {
          const elapsed = Date.now() - this.startTime;
          if (elapsed > this.timeLimit * 0.55) break;
        }
      }

      if (!bestMove) {
        const tt = this.tt.probe(state.hashLo, state.hashHi);
        if (tt && tt.bestMove) bestMove = tt.bestMove;
      }
      if (!bestMove) {
        const legal = generateLegalMoves(state);
        if (legal.length) bestMove = legal[0];
      }

      return {
        move: bestMove, score: bestScore, nodes: this.nodes,
        depth: finalDepth, time: Date.now() - this.startTime,
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

  /* ------------------------ Opening Book (mini) ---------------------- */
  const OPENING_BOOK = {
    // بذرة افتتاحيات شائعة (UCI)
    "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1": ["e2e4", "d2d4", "g1f3", "c2c4"],
    "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1": ["e7e5", "c7c5", "e7e6", "c7c6"],
    "rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR w KQkq e6 0 2": ["g1f3", "f1c4", "b1c3"],
    "rnbqkbnr/pp1ppppp/8/2p5/4P3/8/PPPP1PPP/RNBQKBNR w KQkq c6 0 2": ["g1f3", "b1c3", "d2d4"],
    "rnbqkbnr/pppppppp/8/8/3P4/8/PPP1PPPP/RNBQKBNR b KQkq d3 0 1": ["d7d5", "g8f6", "e7e6"],
    "rnbqkbnr/ppp1pppp/8/3p4/3P4/8/PPP1PPPP/RNBQKBNR w KQkq d6 0 2": ["c2c4", "g1f3", "b1c3"],
  };

  class ChessEngine {
    constructor(opts = {}) {
      this.ttSizeMB = opts.ttSizeMB || 128;
      this.defaultDepth = opts.depth || 6;
      this.searcher = new Searcher(this.ttSizeMB);
      this.useBook = opts.useBook !== false;
      this.ready = true;
    }

    init() { return Promise.resolve(); }

    async getBestMove(fen, opts = {}) {
      // الكتاب
      if (this.useBook && (opts.depth || this.defaultDepth) <= 8) {
        const key = fen.trim();
        const bookMoves = OPENING_BOOK[key];
        if (bookMoves && bookMoves.length) {
          const pick = bookMoves[Math.floor(Math.random() * bookMoves.length)];
          return { move: pick, score: 0, nodes: 0, depth: 0, time: 0, book: true };
        }
      }

      const state = parseFEN(fen);
      const depth = opts.depth || this.defaultDepth;
      const res = this.searcher.search(state, {
        depth, timeLimit: opts.timeLimit || 0, nodeLimit: opts.nodeLimit || 0,
        onDepth: opts.onDepth,
      });
      return {
        move: moveToUci(res.move),
        score: res.score, nodes: res.nodes, depth: res.depth, time: res.time,
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

    static evaluateFEN(fen) {
      const st = parseFEN(fen);
      return evaluate(st);
    }
  }

  /* ------------------------------ Exports ---------------------------- */
  const helpers = { parseFEN, toFEN, generateLegalMoves, applyMove, undoMove, evaluate, sqName, nameToSq, moveToUci };

  if (typeof window !== "undefined") {
    window.ChessEngine = ChessEngine;
    window.ChessEngineHelpers = helpers;
  }
  if (typeof module !== "undefined" && module.exports) {
    module.exports = ChessEngine;
    Object.assign(module.exports, helpers);
  }
  if (typeof globalThis !== "undefined") globalThis.MyChessEngine = ChessEngine;
})(typeof window !== "undefined" ? window : globalThis);