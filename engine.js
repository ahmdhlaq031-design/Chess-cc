/* ============================================================================
 * engine.js — v6.1 (متوافق مع index.html)
 * ----------------------------------------------------------------------------
 * إصلاحات v6.1 (متوافقة مع الموقع):
 *   #A تصدير window.ChessEngine دائماً (كان يُفشل التحميل في المتصفح)
 *   #B ChessEngineHelpers كامل: applyMove, undoMove, toFEN, encodeMove...
 *   #C contempt متماثل: 0 عند التعادل بدل 15 (يمنع انحياز Negamax)
 *   #D evaluate أسرع: إزالة isSquareAttackedBy من حساب التهديدات
 *   #E bookEnabled على Searcher + ChessEngine (متوافق مع toggleBookBtn)
 *   #F حماية promoType في applyMove (القيم غير الصالحة → QUEEN)
 *   #G حذف BACKWARD_PAWN_PENALTY الميت
 *   #H حماية moverType=0 في quiescence
 * ==========================================================================*/

(function (global) {
  "use strict";

  /* ============================ ثوابت ============================ */
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

  /* ==================== Move Encoding ==================== */
  // ترميز الحركة: from (8bit) | to (8bit) | promo (8bit)
  const encodeMove = (from, to, promo) => (from) | (to << 8) | ((promo || 0) << 16);
  const moveFrom  = (m) => m & 0xFF;
  const moveTo    = (m) => (m >> 8) & 0xFF;
  const movePromo = (m) => (m >> 16) & 0x7;
  const decodeMove = (m) => [moveFrom(m), moveTo(m), movePromo(m)];

  /* ==================== Attack Detection ==================== */
  function isSquareAttackedBy(state, sq, byColor) {
    const b = state.board;
    if (byColor === WHITE) {
      if (isValidSq(sq + 15) && b[sq + 15] === W_PAWN) return true;
      if (isValidSq(sq + 17) && b[sq + 17] === W_PAWN) return true;
    } else {
      if (isValidSq(sq - 15) && b[sq - 15] === B_PAWN) return true;
      if (isValidSq(sq - 17) && b[sq - 17] === B_PAWN) return true;
    }
    for (let i = 0; i < 8; i++) {
      const t = sq + N_DIRS[i];
      if (!isValidSq(t)) continue;
      const p = b[t];
      if (p && colorOf(p) === byColor && typeOf(p) === KNIGHT) return true;
    }
    for (let i = 0; i < 8; i++) {
      const t = sq + K_DIRS[i];
      if (!isValidSq(t)) continue;
      const p = b[t];
      if (p && colorOf(p) === byColor && typeOf(p) === KING) return true;
    }
    for (let i = 0; i < 4; i++) {
      const d = B_DIRS[i];
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
    for (let i = 0; i < 4; i++) {
      const d = R_DIRS[i];
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

  /* ============================ State ============================ */
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
      this.uciHistory = [];
    }
  }

  /* ======================== Zobrist ======================== */
  const ZOBRIST_PIECES_LO = [], ZOBRIST_PIECES_HI = [];
  const ZOBRIST_CASTLE_LO = [], ZOBRIST_CASTLE_HI = [];
  const ZOBRIST_EP_LO = [], ZOBRIST_EP_HI = [];
  const ZOBRIST_TURN_LO = [], ZOBRIST_TURN_HI = [];

  (function initZobrist() {
    let s = 0x9e3779b9 >>> 0;
    const rnd = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s; };
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

  /* ============================= FEN ============================= */
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
      s.board[sq] = pieceOf(color, type);
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
    if (s.kings[0] < 0 || s.kings[1] < 0) throw new Error("Invalid FEN: missing king");
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

  /* ======================= Apply / Undo (Fast) ======================= */
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
      from, to, promoType: promoType || 0, captured, capturedSq,
      prevCastling: state.castling, prevEp: state.ep, prevHalf: state.halfmove,
      prevKingW: state.kings[0], prevKingB: state.kings[1],
      hashLo: state.hashLo, hashHi: state.hashHi, prevFull: state.fullmove,
    });
    let lo = state.hashLo, hi = state.hashHi;
    lo ^= ZOBRIST_PIECES_LO[piece][from]; hi ^= ZOBRIST_PIECES_HI[piece][from];
    if (captured) { lo ^= ZOBRIST_PIECES_LO[captured][capturedSq]; hi ^= ZOBRIST_PIECES_HI[captured][capturedSq]; }
    lo ^= ZOBRIST_CASTLE_LO[state.castling]; hi ^= ZOBRIST_CASTLE_HI[state.castling];
    if (state.ep >= 0) { lo ^= ZOBRIST_EP_LO[state.ep]; hi ^= ZOBRIST_EP_HI[state.ep]; }
    b[from] = 0;
    if (capturedSq >= 0) b[capturedSq] = 0;
    let placed = piece;
    // FIX #F: تحقق صريح من صحة promoType
    if (type === PAWN && (to >> 4) === (color === WHITE ? 0 : 7)) {
      const validPromo = promoType >= KNIGHT && promoType <= QUEEN ? promoType : QUEEN;
      placed = pieceOf(color, validPromo);
    }
    b[to] = placed;
    lo ^= ZOBRIST_PIECES_LO[placed][to]; hi ^= ZOBRIST_PIECES_HI[placed][to];
    if (type === KING) {
      const fromF = from & 7, toF = to & 7;
      if (fromF === 4 && toF === 6) {
        const rFrom = to + 1, rTo = to - 1;
        const rp = b[rFrom];
        b[rTo] = rp; b[rFrom] = 0;
        lo ^= ZOBRIST_PIECES_LO[rp][rFrom] ^ ZOBRIST_PIECES_LO[rp][rTo];
        hi ^= ZOBRIST_PIECES_HI[rp][rFrom] ^ ZOBRIST_PIECES_HI[rp][rTo];
      } else if (fromF === 4 && toF === 2) {
        const rFrom = to - 2, rTo = to + 1;
        const rp = b[rFrom];
        b[rTo] = rp; b[rFrom] = 0;
        lo ^= ZOBRIST_PIECES_LO[rp][rFrom] ^ ZOBRIST_PIECES_LO[rp][rTo];
        hi ^= ZOBRIST_PIECES_HI[rp][rFrom] ^ ZOBRIST_PIECES_HI[rp][rTo];
      }
      state.kings[color] = to;
    }
    let castling = state.castling;
    if (type === KING) castling &= color === WHITE ? ~(CASTLE_WK | CASTLE_WQ) : ~(CASTLE_BK | CASTLE_BQ);
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
    lo ^= ZOBRIST_CASTLE_LO[castling]; hi ^= ZOBRIST_CASTLE_HI[castling];
    if (ep >= 0) { lo ^= ZOBRIST_EP_LO[ep]; hi ^= ZOBRIST_EP_HI[ep]; }
    lo ^= ZOBRIST_TURN_LO[state.turn]; hi ^= ZOBRIST_TURN_HI[state.turn];
    state.turn = 1 - state.turn;
    lo ^= ZOBRIST_TURN_LO[state.turn]; hi ^= ZOBRIST_TURN_HI[state.turn];
    state.hashLo = lo >>> 0; state.hashHi = hi >>> 0;
  }

  function undoMove(state) {
    const h = state.history.pop();
    if (!h || h.nullMove) return;
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
    state.kings[0] = h.prevKingW; state.kings[1] = h.prevKingB;
    state.turn = 1 - state.turn;
    state.fullmove = h.prevFull; state.hashLo = h.hashLo; state.hashHi = h.hashHi;
  }

  /* ======================= Move Generation ======================= */
  function generatePseudoMoves(state) {
    const moves = [], b = state.board, us = state.turn, them = 1 - us;
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
            moves.push(encodeMove(from, one, QUEEN));
            moves.push(encodeMove(from, one, ROOK));
            moves.push(encodeMove(from, one, BISHOP));
            moves.push(encodeMove(from, one, KNIGHT));
          } else {
            moves.push(encodeMove(from, one, 0));
            const two = one + dir;
            if ((from >> 4) === startRank && isValidSq(two) && !b[two]) moves.push(encodeMove(from, two, 0));
          }
        }
        for (let k = 0; k < 2; k++) {
          const d = k === 0 ? dir - 1 : dir + 1;
          const to = from + d;
          if (!isValidSq(to)) continue;
          if (Math.abs((to & 7) - (from & 7)) !== 1) continue;
          const target = b[to];
          if (target && colorOf(target) === them) {
            if ((to >> 4) === promoRank) {
              moves.push(encodeMove(from, to, QUEEN));
              moves.push(encodeMove(from, to, ROOK));
              moves.push(encodeMove(from, to, BISHOP));
              moves.push(encodeMove(from, to, KNIGHT));
            } else moves.push(encodeMove(from, to, 0));
          } else if (to === state.ep && !target) {
            const epRank = us === WHITE ? 3 : 4;
            if ((from >> 4) === epRank) moves.push(encodeMove(from, to, 0));
          }
        }
      } else if (type === KNIGHT) {
        for (let i = 0; i < 8; i++) {
          const to = from + N_DIRS[i];
          if (!isValidSq(to)) continue;
          const t = b[to];
          if (!t || colorOf(t) === them) moves.push(encodeMove(from, to, 0));
        }
      } else if (type === KING) {
        for (let i = 0; i < 8; i++) {
          const to = from + K_DIRS[i];
          if (!isValidSq(to)) continue;
          const t = b[to];
          if (!t || colorOf(t) === them) moves.push(encodeMove(from, to, 0));
        }
        if (us === WHITE) {
          if ((state.castling & CASTLE_WK) && !b[SQ.f1] && !b[SQ.g1] && b[SQ.h1] === W_ROOK
              && !isSquareAttackedBy(state, SQ.e1, BLACK)
              && !isSquareAttackedBy(state, SQ.f1, BLACK)
              && !isSquareAttackedBy(state, SQ.g1, BLACK)) moves.push(encodeMove(SQ.e1, SQ.g1, 0));
          if ((state.castling & CASTLE_WQ) && !b[SQ.d1] && !b[SQ.c1] && !b[SQ.b1] && b[SQ.a1] === W_ROOK
              && !isSquareAttackedBy(state, SQ.e1, BLACK)
              && !isSquareAttackedBy(state, SQ.d1, BLACK)
              && !isSquareAttackedBy(state, SQ.c1, BLACK)) moves.push(encodeMove(SQ.e1, SQ.c1, 0));
        } else {
          if ((state.castling & CASTLE_BK) && !b[SQ.f8] && !b[SQ.g8] && b[SQ.h8] === B_ROOK
              && !isSquareAttackedBy(state, SQ.e8, WHITE)
              && !isSquareAttackedBy(state, SQ.f8, WHITE)
              && !isSquareAttackedBy(state, SQ.g8, WHITE)) moves.push(encodeMove(SQ.e8, SQ.g8, 0));
          if ((state.castling & CASTLE_BQ) && !b[SQ.d8] && !b[SQ.c8] && !b[SQ.b8] && b[SQ.a8] === B_ROOK
              && !isSquareAttackedBy(state, SQ.e8, WHITE)
              && !isSquareAttackedBy(state, SQ.d8, WHITE)
              && !isSquareAttackedBy(state, SQ.c8, WHITE)) moves.push(encodeMove(SQ.e8, SQ.c8, 0));
        }
      } else {
        const dirs = type === BISHOP ? B_DIRS : type === ROOK ? R_DIRS : K_DIRS;
        for (let di = 0; di < dirs.length; di++) {
          const d = dirs[di];
          let to = from + d;
          while (isValidSq(to)) {
            const t = b[to];
            if (!t) moves.push(encodeMove(from, to, 0));
            else { if (colorOf(t) === them) moves.push(encodeMove(from, to, 0)); break; }
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
    const legal = [], us = state.turn;
    for (let i = 0; i < pseudo.length; i++) {
      const m = pseudo[i];
      const from = moveFrom(m), to = moveTo(m), promo = movePromo(m);
      applyMove(state, from, to, promo);
      if (!isInCheck(state, us)) legal.push(m);
      undoMove(state);
    }
    return legal;
  }

  /* ============================= SEE ============================= */
  const SEE_VAL = [0, 100, 320, 330, 500, 900, 20000];

  function see(state, from, to, promoType) {
    const b = state.board;
    const target = b[to];
    const moverPiece = b[from];
    const moverColor = colorOf(moverPiece);
    const isEp = (to === state.ep && typeOf(moverPiece) === PAWN && !target);
    if (!target && !isEp && !promoType) return 0;
    const snapshot = b.slice();
    const kingsBackup = state.kings[0], kingsBackupB = state.kings[1];
    const gain = [];
    gain[0] = target ? SEE_VAL[typeOf(target)] : SEE_VAL[PAWN];
    let side = 1 - moverColor;
    let curType = promoType || typeOf(moverPiece);
    b[to] = pieceOf(moverColor, curType);
    b[from] = 0;
    if (isEp) b[moverColor === WHITE ? to + 16 : to - 16] = 0;
    let d = 0;
    while (d < 20) {
      d++;
      let bestSq = -1, bestType = 0, bestVal = 99999;
      for (let sq = 0; sq < 128; sq++) {
        if (!isValidSq(sq)) continue;
        const p = b[sq];
        if (!p || colorOf(p) !== side) continue;
        const t = typeOf(p);
        let attacks = false;
        if (t === PAWN) {
          const dir = side === WHITE ? -16 : 16;
          if ((sq + dir - 1 === to || sq + dir + 1 === to) && Math.abs((sq & 7) - (to & 7)) === 1) attacks = true;
        } else if (t === KNIGHT) {
          for (let i = 0; i < 8; i++) if (sq + N_DIRS[i] === to) { attacks = true; break; }
        } else if (t === KING) {
          for (let i = 0; i < 8; i++) if (sq + K_DIRS[i] === to) { attacks = true; break; }
        } else {
          const dirs = t === BISHOP ? B_DIRS : t === ROOK ? R_DIRS : K_DIRS;
          for (let di = 0; di < dirs.length; di++) {
            const dd = dirs[di];
            let x = sq + dd;
            while (isValidSq(x)) {
              if (x === to) { attacks = true; break; }
              if (b[x]) break;
              x += dd;
            }
            if (attacks) break;
          }
        }
        if (attacks && SEE_VAL[t] < bestVal) { bestVal = SEE_VAL[t]; bestSq = sq; bestType = t; }
      }
      if (bestSq < 0) break;
      gain[d] = SEE_VAL[curType] - gain[d - 1];
      curType = bestType;
      b[bestSq] = 0;
      b[to] = pieceOf(side, bestType);
      side = 1 - side;
    }
    for (let sq = 0; sq < 128; sq++) b[sq] = snapshot[sq];
    state.kings[0] = kingsBackup; state.kings[1] = kingsBackupB;
    let val = gain[d];
    for (let i = d - 1; i >= 0; i--) val = gain[i] - Math.max(0, val);
    return val;
  }

  /* ======================== Evaluation ======================== */
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
  const PASSED_BONUS = [0, 5, 15, 30, 50, 80, 130, 0];
  const PASSED_BONUS_EG = [0, 10, 25, 50, 85, 140, 220, 0];
  const ISOLATED_PAWN_PENALTY = 18;
  const DOUBLED_PAWN_PENALTY = 12;

  function psqtIndex(sq, color) {
    const r = sq >> 4, f = sq & 7;
    if (color === WHITE) return r * 8 + f;
    return (7 - r) * 8 + f;
  }

  function evaluate(state) {
    const b = state.board;
    let mg = 0, eg = 0, phase = 0;
    const phaseVal = [0, 0, 1, 1, 2, 4, 0];
    const wPawnCount = [0,0,0,0,0,0,0,0], bPawnCount = [0,0,0,0,0,0,0,0];
    let wBishops = 0, bBishops = 0, wKnights = 0, bKnights = 0;
    let wRooks = 0, bRooks = 0, wQueens = 0, bQueens = 0;
    let wKingSq = -1, bKingSq = -1;
    const wPawnSqs = [], bPawnSqs = [];
    const wKnightSqs = [], bKnightSqs = [];
    const wBishopSqs = [], bBishopSqs = [];
    const wRookSqs = [], bRookSqs = [];
    const wQueenSqs = [], bQueenSqs = [];

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
      if (t === PAWN) { (c === WHITE ? wPawnCount : bPawnCount)[sq & 7]++; (c === WHITE ? wPawnSqs : bPawnSqs).push(sq); }
      else if (t === BISHOP) { if (c === WHITE) { wBishops++; wBishopSqs.push(sq); } else { bBishops++; bBishopSqs.push(sq); } }
      else if (t === KNIGHT) { if (c === WHITE) { wKnights++; wKnightSqs.push(sq); } else { bKnights++; bKnightSqs.push(sq); } }
      else if (t === ROOK) { if (c === WHITE) { wRooks++; wRookSqs.push(sq); } else { bRooks++; bRookSqs.push(sq); } }
      else if (t === QUEEN) { if (c === WHITE) { wQueens++; wQueenSqs.push(sq); } else { bQueens++; bQueenSqs.push(sq); } }
      else if (t === KING) { if (c === WHITE) wKingSq = sq; else bKingSq = sq; }
    }

    /* Pawn structure */
    let structW = 0, structB = 0;
    for (let f = 0; f < 8; f++) {
      if (wPawnCount[f] > 1) structW -= DOUBLED_PAWN_PENALTY * (wPawnCount[f] - 1);
      if (bPawnCount[f] > 1) structB -= DOUBLED_PAWN_PENALTY * (bPawnCount[f] - 1);
      if (wPawnCount[f] > 0) {
        const l = f > 0 ? wPawnCount[f - 1] : 0, r = f < 7 ? wPawnCount[f + 1] : 0;
        if (!l && !r) structW -= ISOLATED_PAWN_PENALTY;
      }
      if (bPawnCount[f] > 0) {
        const l = f > 0 ? bPawnCount[f - 1] : 0, r = f < 7 ? bPawnCount[f + 1] : 0;
        if (!l && !r) structB -= ISOLATED_PAWN_PENALTY;
      }
    }
    mg += structW - structB; eg += structW - structB;

    /* Bishop pair */
    if (wBishops >= 2) { mg += 30; eg += 55; }
    if (bBishops >= 2) { mg -= 30; eg -= 55; }

    /* Rook on open/semi-open file + 7th rank + connected rooks */
    for (let i = 0; i < wRookSqs.length; i++) {
      const sq = wRookSqs[i];
      const f = sq & 7, r = sq >> 4;
      if (wPawnCount[f] === 0 && bPawnCount[f] === 0) { mg += 25; eg += 15; }
      else if (wPawnCount[f] === 0) { mg += 12; eg += 8; }
      if (r === 1) { mg += 25; eg += 40; }
      if (wRooks >= 2) {
        for (let j = i + 1; j < wRookSqs.length; j++) {
          const sq2 = wRookSqs[j];
          if ((sq2 >> 4) === r) {
            let blocked = false;
            const f1 = Math.min(f, sq2 & 7), f2 = Math.max(f, sq2 & 7);
            for (let ff = f1 + 1; ff < f2; ff++) {
              if (b[r * 16 + ff]) { blocked = true; break; }
            }
            if (!blocked) { mg += 12; eg += 8; }
          }
        }
      }
    }
    for (let i = 0; i < bRookSqs.length; i++) {
      const sq = bRookSqs[i];
      const f = sq & 7, r = sq >> 4;
      if (wPawnCount[f] === 0 && bPawnCount[f] === 0) { mg -= 25; eg -= 15; }
      else if (bPawnCount[f] === 0) { mg -= 12; eg -= 8; }
      if (r === 6) { mg -= 25; eg -= 40; }
      if (bRooks >= 2) {
        for (let j = i + 1; j < bRookSqs.length; j++) {
          const sq2 = bRookSqs[j];
          if ((sq2 >> 4) === r) {
            let blocked = false;
            const f1 = Math.min(f, sq2 & 7), f2 = Math.max(f, sq2 & 7);
            for (let ff = f1 + 1; ff < f2; ff++) {
              if (b[r * 16 + ff]) { blocked = true; break; }
            }
            if (!blocked) { mg -= 12; eg -= 8; }
          }
        }
      }
    }

    /* Passed pawns */
    for (let i = 0; i < wPawnSqs.length; i++) {
      const sq = wPawnSqs[i];
      const f = sq & 7, r = sq >> 4;
      let passed = true;
      for (let df = -1; df <= 1; df++) {
        const ff = f + df;
        if (ff < 0 || ff > 7) continue;
        for (let j = 0; j < bPawnSqs.length; j++) {
          const bsq = bPawnSqs[j];
          if ((bsq & 7) === ff && (bsq >> 4) < r) { passed = false; break; }
        }
        if (!passed) break;
      }
      if (passed) {
        const rank = 7 - r;
        mg += PASSED_BONUS[rank] || 0;
        eg += PASSED_BONUS_EG[rank] || 0;
      }
    }
    for (let i = 0; i < bPawnSqs.length; i++) {
      const sq = bPawnSqs[i];
      const f = sq & 7, r = sq >> 4;
      let passed = true;
      for (let df = -1; df <= 1; df++) {
        const ff = f + df;
        if (ff < 0 || ff > 7) continue;
        for (let j = 0; j < wPawnSqs.length; j++) {
          const wsq = wPawnSqs[j];
          if ((wsq & 7) === ff && (wsq >> 4) > r) { passed = false; break; }
        }
        if (!passed) break;
      }
      if (passed) {
        const rank = Math.max(0, Math.min(6, r - 1));
        mg -= PASSED_BONUS[rank] || 0;
        eg -= PASSED_BONUS_EG[rank] || 0;
      }
    }

    /* Knight mobility + outposts */
    for (let i = 0; i < wKnightSqs.length; i++) {
      const sq = wKnightSqs[i];
      let mob = 0;
      const r = sq >> 4, f = sq & 7;
      for (let d = 0; d < 8; d++) {
        const t = sq + N_DIRS[d];
        if (!isValidSq(t)) continue;
        const p = b[t];
        if (!p || colorOf(p) === BLACK) mob++;
      }
      mg += (mob - 4) * 3; eg += (mob - 4) * 3;
      if ((r === 3 || r === 4) && f >= 2 && f <= 5) {
        const defSq = sq + 16;
        if (isValidSq(defSq) && b[defSq] === W_PAWN) { mg += 20; eg += 15; }
      }
    }
    for (let i = 0; i < bKnightSqs.length; i++) {
      const sq = bKnightSqs[i];
      let mob = 0;
      const r = sq >> 4, f = sq & 7;
      for (let d = 0; d < 8; d++) {
        const t = sq + N_DIRS[d];
        if (!isValidSq(t)) continue;
        const p = b[t];
        if (!p || colorOf(p) === WHITE) mob++;
      }
      mg -= (mob - 4) * 3; eg -= (mob - 4) * 3;
      if ((r === 3 || r === 4) && f >= 2 && f <= 5) {
        const defSq = sq - 16;
        if (isValidSq(defSq) && b[defSq] === B_PAWN) { mg -= 20; eg -= 15; }
      }
    }

    /* Bishop mobility */
    for (let i = 0; i < wBishopSqs.length; i++) {
      const sq = wBishopSqs[i];
      let mob = 0;
      for (let di = 0; di < 4; di++) {
        const d = B_DIRS[di];
        let t = sq + d;
        while (isValidSq(t)) {
          const p = b[t];
          if (!p) mob++;
          else { if (colorOf(p) === BLACK) mob++; break; }
          t += d;
        }
      }
      mg += (mob - 6) * 2; eg += (mob - 6) * 2;
    }
    for (let i = 0; i < bBishopSqs.length; i++) {
      const sq = bBishopSqs[i];
      let mob = 0;
      for (let di = 0; di < 4; di++) {
        const d = B_DIRS[di];
        let t = sq + d;
        while (isValidSq(t)) {
          const p = b[t];
          if (!p) mob++;
          else { if (colorOf(p) === WHITE) mob++; break; }
          t += d;
        }
      }
      mg -= (mob - 6) * 2; eg -= (mob - 6) * 2;
    }

    /* Threats — FIX #D: مبسّط لتقليل isSquareAttackedBy */
    // نكتفي بفحص "هل القطعة الكبيرة مهددة من بيدق أو حصان" بدون استدعاء مكلف
    for (const { sq, val } of [
      ...wKnightSqs.map(s => ({ sq: s, val: 320 })),
      ...wBishopSqs.map(s => ({ sq: s, val: 330 })),
      ...wRookSqs.map(s => ({ sq: s, val: 500 })),
      ...wQueenSqs.map(s => ({ sq: s, val: 900 })),
    ]) {
      const f = sq & 7, r = sq >> 4;
      let attacked = false;
      // بيادق سوداء
      if (r < 7) {
        if (f > 0 && b[(r + 1) * 16 + (f - 1)] === B_PAWN) attacked = true;
        if (f < 7 && b[(r + 1) * 16 + (f + 1)] === B_PAWN) attacked = true;
      }
      // حصان أسود
      if (!attacked) {
        for (let d = 0; d < 8; d++) {
          const t = sq + N_DIRS[d];
          if (isValidSq(t) && b[t] === B_KNIGHT) { attacked = true; break; }
        }
      }
      if (attacked) mg -= Math.min(val * 0.15, 80);
    }
    for (const { sq, val } of [
      ...bKnightSqs.map(s => ({ sq: s, val: 320 })),
      ...bBishopSqs.map(s => ({ sq: s, val: 330 })),
      ...bRookSqs.map(s => ({ sq: s, val: 500 })),
      ...bQueenSqs.map(s => ({ sq: s, val: 900 })),
    ]) {
      const f = sq & 7, r = sq >> 4;
      let attacked = false;
      if (r > 0) {
        if (f > 0 && b[(r - 1) * 16 + (f - 1)] === W_PAWN) attacked = true;
        if (f < 7 && b[(r - 1) * 16 + (f + 1)] === W_PAWN) attacked = true;
      }
      if (!attacked) {
        for (let d = 0; d < 8; d++) {
          const t = sq + N_DIRS[d];
          if (isValidSq(t) && b[t] === W_KNIGHT) { attacked = true; break; }
        }
      }
      if (attacked) mg += Math.min(val * 0.15, 80);
    }

    /* King tropism */
    if (wKingSq >= 0 && bKingSq >= 0) {
      const wKR = wKingSq >> 4, wKF = wKingSq & 7;
      const bKR = bKingSq >> 4, bKF = bKingSq & 7;
      for (const sq of wQueenSqs) {
        const d = Math.max(Math.abs((sq >> 4) - bKR), Math.abs((sq & 7) - bKF));
        mg += (7 - d) * 2;
      }
      for (const sq of bQueenSqs) {
        const d = Math.max(Math.abs((sq >> 4) - wKR), Math.abs((sq & 7) - wKF));
        mg -= (7 - d) * 2;
      }
    }

    /* King safety */
    if (phase > 10 && wKingSq >= 0 && bKingSq >= 0) {
      const wKingF = wKingSq & 7, wKingR = wKingSq >> 4;
      const bKingF = bKingSq & 7, bKingR = bKingSq >> 4;
      let wDanger = 0, bDanger = 0;
      for (let sq = 0; sq < 128; sq++) {
        if (!isValidSq(sq)) continue;
        const p = b[sq];
        if (!p) continue;
        const t = typeOf(p);
        if (t === PAWN || t === KING) continue;
        const c = colorOf(p);
        const r = sq >> 4, f = sq & 7;
        const weight = t === QUEEN ? 6 : t === ROOK ? 4 : 3;
        if (c === BLACK) {
          const dist = Math.max(Math.abs(r - wKingR), Math.abs(f - wKingF));
          if (dist <= 2) wDanger += weight;
        } else {
          const dist = Math.max(Math.abs(r - bKingR), Math.abs(f - bKingF));
          if (dist <= 2) bDanger += weight;
        }
      }
      mg -= wDanger * 4; mg += bDanger * 4;
    }

    /* King pawn shield */
    if (phase > 8) {
      if (wKingSq >= 0) {
        const f = wKingSq & 7, r = wKingSq >> 4;
        if (r >= 6) {
          for (let df = -1; df <= 1; df++) {
            const ff = f + df;
            if (ff >= 0 && ff < 8) {
              if (b[(r - 1) * 16 + ff] === W_PAWN) mg += 12;
              else if (b[(r - 2) * 16 + ff] === W_PAWN) mg += 6;
            }
          }
        }
      }
      if (bKingSq >= 0) {
        const f = bKingSq & 7, r = bKingSq >> 4;
        if (r <= 1) {
          for (let df = -1; df <= 1; df++) {
            const ff = f + df;
            if (ff >= 0 && ff < 8) {
              if (b[(r + 1) * 16 + ff] === B_PAWN) mg -= 12;
              else if (b[(r + 2) * 16 + ff] === B_PAWN) mg -= 6;
            }
          }
        }
      }
    }

    const ph = Math.min(24, phase) / 24;
    let score = mg * ph + eg * (1 - ph);
    score += state.turn === WHITE ? 12 : -12;

    /* Draw detection */
    if (wPawnSqs.length === 0 && bPawnSqs.length === 0 &&
        wRooks === 0 && bRooks === 0 && wQueens === 0 && bQueens === 0) {
      const wMinor = wBishops + wKnights, bMinor = bBishops + bKnights;
      if (wMinor <= 1 && bMinor <= 1) return 0;
    }

    return state.turn === WHITE ? score : -score;
  }

  /* ================ Transposition Table ================ */
  const TT_EXACT = 1, TT_LOWER = 2, TT_UPPER = 3;
  const TT_BUCKET_SIZE = 4;

  class TranspositionTable {
    constructor(sizeMB = 128) {
      const totalEntries = Math.max(1 << 16, Math.floor((sizeMB * 1024 * 1024) / 24));
      this.bucketCount = 1;
      while (this.bucketCount * 2 * TT_BUCKET_SIZE <= totalEntries) this.bucketCount *= 2;
      const total = this.bucketCount * TT_BUCKET_SIZE;
      this.keysLo = new Uint32Array(total);
      this.keysHi = new Uint32Array(total);
      this.depth = new Int8Array(total);
      this.score = new Int32Array(total);
      this.flag = new Uint8Array(total);
      this.bestMoveArr = new Int32Array(total);
      this.age = new Uint8Array(total);
      this.generation = 0;
      this.mask = this.bucketCount - 1;
    }
    clear() {
      this.keysLo.fill(0); this.keysHi.fill(0); this.depth.fill(0);
      this.flag.fill(0); this.age.fill(0); this.bestMoveArr.fill(0);
    }
    bucketIndex(lo, hi) {
      return ((lo ^ (hi * 2654435761)) >>> 0) & this.mask;
    }
    probe(lo, hi) {
      const base = this.bucketIndex(lo, hi) * TT_BUCKET_SIZE;
      let bestIdx = -1, bestDepth = -1;
      for (let i = 0; i < TT_BUCKET_SIZE; i++) {
        const idx = base + i;
        if (this.flag[idx] !== 0 && this.keysLo[idx] === lo && this.keysHi[idx] === hi) {
          if (this.depth[idx] > bestDepth) { bestDepth = this.depth[idx]; bestIdx = idx; }
        }
      }
      if (bestIdx < 0) return null;
      return {
        depth: this.depth[bestIdx],
        score: this.score[bestIdx],
        flag: this.flag[bestIdx],
        bestMove: this.bestMoveArr[bestIdx] || 0,
      };
    }
    store(lo, hi, depth, score, flag, bestMove) {
      const base = this.bucketIndex(lo, hi) * TT_BUCKET_SIZE;
      for (let i = 0; i < TT_BUCKET_SIZE; i++) {
        const idx = base + i;
        if (this.flag[idx] !== 0 && this.keysLo[idx] === lo && this.keysHi[idx] === hi) {
          if (this.depth[idx] > depth && this.age[idx] === this.generation) return;
          this.depth[idx] = depth;
          this.score[idx] = score;
          this.flag[idx] = flag;
          this.age[idx] = this.generation;
          if (bestMove) this.bestMoveArr[idx] = bestMove;
          return;
        }
      }
      let worstIdx = base, worstScore = 999999;
      for (let i = 0; i < TT_BUCKET_SIZE; i++) {
        const idx = base + i;
        if (this.flag[idx] === 0) { worstIdx = idx; worstScore = -1; break; }
        const s = this.depth[idx] + (this.age[idx] === this.generation ? 1000 : 0);
        if (s < worstScore) { worstScore = s; worstIdx = idx; }
      }
      this.keysLo[worstIdx] = lo;
      this.keysHi[worstIdx] = hi;
      this.depth[worstIdx] = depth;
      this.score[worstIdx] = score;
      this.flag[worstIdx] = flag;
      this.age[worstIdx] = this.generation;
      this.bestMoveArr[worstIdx] = bestMove || 0;
    }
    newSearch() { this.generation = (this.generation + 1) & 255; }
  }

  /* ==================== OPENING BOOK ==================== */
  const OPENING_BOOK = [
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1c4","f8c5"], name: "Italian" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1c4","f8c5","c2c3"], name: "Giuoco Piano" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1c4","g8f6"], name: "Two Knights" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1c4","g8f6","d2d3"], name: "Two Knights d3" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5"], name: "Ruy Lopez" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5","a7a6"], name: "Morphy" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5","a7a6","b5a4","g8f6"], name: "Ruy Main" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5","a7a6","b5a4","g8f6","e1g1"], name: "Ruy Castled" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","d2d4"], name: "Scotch" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","d2d4","e5d4","f3d4"], name: "Scotch Main" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","d2d4","e5d4","f3d4","f8c5"], name: "Scotch Classical" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","b1c3","g8f6"], name: "Four Knights" },
    { moves: ["e2e4","e7e5","g1f3","g8f6"], name: "Petrov" },
    { moves: ["e2e4","e7e5","b1c3"], name: "Vienna" },
    { moves: ["e2e4","e7e5","b1c3","g8f6"], name: "Vienna Main" },
    { moves: ["e2e4","e7e5","f2f4"], name: "King's Gambit" },
    { moves: ["e2e4","c7c5"], name: "Sicilian" },
    { moves: ["e2e4","c7c5","g1f3","d7d6"], name: "Najdorf-ish" },
    { moves: ["e2e4","c7c5","g1f3","b8c6","d2d4","c5d4"], name: "Sicilian Open" },
    { moves: ["e2e4","c7c5","b1c3"], name: "Sicilian Closed" },
    { moves: ["e2e4","c7c5","g1f3","e7e6"], name: "Sicilian Taimanov" },
    { moves: ["e2e4","c7c5","g1f3","d7d6","d2d4","c5d4"], name: "Sicilian Open Main" },
    { moves: ["e2e4","c7c5","g1f3","b8c6","f1b5"], name: "Sicilian Rossolimo" },
    { moves: ["e2e4","e7e6"], name: "French" },
    { moves: ["e2e4","e7e6","d2d4","d7d5"], name: "French Main" },
    { moves: ["e2e4","e7e6","d2d4","d7d5","b1c3","g8f6"], name: "French Classical" },
    { moves: ["e2e4","e7e6","d2d4","d7d5","e4d5","e6d5"], name: "French Exchange" },
    { moves: ["e2e4","c7c6"], name: "Caro-Kann" },
    { moves: ["e2e4","c7c6","d2d4","d7d5"], name: "Caro Main" },
    { moves: ["e2e4","c7c6","d2d4","d7d5","b1c3","d5e4"], name: "Caro Classical" },
    { moves: ["e2e4","c7c6","d2d4","d7d5","e4e5"], name: "Caro Advance" },
    { moves: ["e2e4","d7d6","d2d4","g8f6"], name: "Pirc" },
    { moves: ["e2e4","g7g6"], name: "Modern" },
    { moves: ["e2e4","g8f6"], name: "Alekhine" },
    { moves: ["e2e4","d7d5"], name: "Scandinavian" },
    { moves: ["e2e4","d7d5","e4d5","d8d5"], name: "Scandinavian Main" },
    { moves: ["d2d4","d7d5","c2c4"], name: "Q Gambit" },
    { moves: ["d2d4","d7d5","c2c4","e7e6"], name: "QGD" },
    { moves: ["d2d4","d7d5","c2c4","c7c6"], name: "Slav" },
    { moves: ["d2d4","d7d5","c2c4","d5c4"], name: "QGA" },
    { moves: ["d2d4","d7d5","c2c4","e7e6","b1c3","g8f6"], name: "QGD Main" },
    { moves: ["d2d4","d7d5","c2c4","c7c6","g1f3","g8f6"], name: "Slav Main" },
    { moves: ["d2d4","d7d5","g1f3","g8f6","c1f4"], name: "London" },
    { moves: ["d2d4","g8f6","g1f3","e7e6","c1f4"], name: "London vs Indian" },
    { moves: ["d2d4","g8f6","c1f4"], name: "London Quick" },
    { moves: ["d2d4","d7d5","c1f4"], name: "London System" },
    { moves: ["d2d4","g8f6","c2c4","e7e6","g2g3"], name: "Catalan" },
    { moves: ["d2d4","g8f6","c2c4","e7e6","g2g3","d7d5","f1g2"], name: "Catalan Main" },
    { moves: ["d2d4","g8f6","c2c4","g7g6"], name: "KID" },
    { moves: ["d2d4","g8f6","c2c4","g7g6","b1c3","f8g7"], name: "KID Main" },
    { moves: ["d2d4","g8f6","c2c4","e7e6","b1c3","f8b4"], name: "Nimzo" },
    { moves: ["d2d4","g8f6","c2c4","e7e6","g1f3","b7b6"], name: "QID" },
    { moves: ["c2c4"], name: "English" },
    { moves: ["c2c4","e7e5"], name: "Eng Reversed Sicilian" },
    { moves: ["c2c4","g8f6","b1c3"], name: "English Main" },
    { moves: ["c2c4","c7c5"], name: "English Symm" },
    { moves: ["d2d4","f7f5"], name: "Dutch" },
    { moves: ["d2d4","f7f5","g2g3","g8f6"], name: "Dutch Leningrad" },
    { moves: ["g1f3"], name: "Reti" },
    { moves: ["g1f3","d7d5","c2c4"], name: "Reti Main" },
    { moves: ["d2d4","g8f6","c2c4","e7e5"], name: "Budapest" },
    { moves: ["d2d4","g8f6","c2c4","c7c5","d4d5","e7e6"], name: "Benoni" },
    { moves: ["d2d4","g8f6","c2c4","c7c5","d4d5","b7b5"], name: "Benko" },
    { moves: ["d2d4","g8f6","c1g5"], name: "Trompowsky" },
    { moves: ["d2d4","g8f6","g1f3","e7e6","c1g5"], name: "Torre Attack" },
  ];

  /* ==================== Learning Book ==================== */
  class LearningBook {
    constructor() {
      this.stats = new Map();
      this.bookPenalty = new Map();
      this.enabled = true;
      this.penaltyPerLoss = 250;
      this.maxPenalty = 600;
      this.rewardPerWin = 60;
      this.maxReward = 200;
    }
    static posKey(state) { return state.hashLo + ":" + state.hashHi; }
    recordMove(state, uci, result) {
      if (!this.enabled) return;
      const pk = LearningBook.posKey(state);
      if (!this.stats.has(pk)) this.stats.set(pk, {});
      const pos = this.stats.get(pk);
      if (!pos[uci]) pos[uci] = { w: 0, l: 0 };
      if (result === 'loss') pos[uci].l++;
      else if (result === 'win') pos[uci].w++;
      let bp = this.bookPenalty.get(pk) || {};
      bp[uci] = Math.min(this.maxPenalty, pos[uci].l * this.penaltyPerLoss)
              - Math.min(this.maxReward, pos[uci].w * this.rewardPerWin);
      this.bookPenalty.set(pk, bp);
    }
    getAdjustment(state, uci) {
      if (!this.enabled) return 0;
      const pk = LearningBook.posKey(state);
      const bp = this.bookPenalty.get(pk);
      if (!bp) return 0;
      return bp[uci] || 0;
    }
    export() {
      return {
        stats: Array.from(this.stats.entries()),
        bookPenalty: Array.from(this.bookPenalty.entries()),
      };
    }
    import(data) {
      if (!data) return;
      this.stats = new Map(data.stats || []);
      this.bookPenalty = new Map(data.bookPenalty || []);
    }
    saveToStorage(key = "chessEnginePro_learning") {
      if (typeof localStorage === "undefined") return false;
      try { localStorage.setItem(key, JSON.stringify(this.export())); return true; }
      catch (e) { return false; }
    }
    loadFromStorage(key = "chessEnginePro_learning") {
      if (typeof localStorage === "undefined") return false;
      try {
        const raw = localStorage.getItem(key);
        if (!raw) return false;
        this.import(JSON.parse(raw)); return true;
      } catch (e) { return false; }
    }
    clear() { this.stats.clear(); this.bookPenalty.clear(); }
  }

  /* ==================== Book Matching ==================== */
  function findBookMove(state, learningBook) {
    const hist = state.uciHistory || [];
    if (hist.length === 0) {
      const firstMoves = new Set();
      for (const entry of OPENING_BOOK) firstMoves.add(entry.moves[0]);
      const arr = Array.from(firstMoves);
      return arr[Math.floor(Math.random() * arr.length)];
    }
    const historyStr = hist.join(" ");
    const legal = generateLegalMoves(state);
    const legalUcis = new Set(legal.map(m => moveToUci(m)));
    const candidates = [];
    for (const entry of OPENING_BOOK) {
      const prefix = entry.moves.slice(0, hist.length).join(" ");
      if (prefix === historyStr && entry.moves.length > hist.length) {
        const nextMove = entry.moves[hist.length];
        if (legalUcis.has(nextMove)) {
          let adj = 0;
          if (learningBook && learningBook.enabled) {
            adj = learningBook.getAdjustment(state, nextMove);
          }
          candidates.push({ uci: nextMove, name: entry.name, adj });
        }
      }
    }
    if (candidates.length === 0) return null;
    const weights = candidates.map(c => Math.max(5, 100 - Math.max(0, c.adj)));
    const totalW = weights.reduce((a, b) => a + b, 0);
    let pick = Math.random() * totalW;
    for (let i = 0; i < candidates.length; i++) {
      pick -= weights[i];
      if (pick <= 0) return candidates[i].uci;
    }
    return candidates[candidates.length - 1].uci;
  }

  /* ==================== Insertion Sort ==================== */
  function insertionSortMoves(moves, scores) {
    for (let i = 1; i < moves.length; i++) {
      const m = moves[i], s = scores[i];
      let j = i - 1;
      while (j >= 0 && scores[j] < s) {
        moves[j + 1] = moves[j];
        scores[j + 1] = scores[j];
        j--;
      }
      moves[j + 1] = m;
      scores[j + 1] = s;
    }
  }

  /* ======================== Search ======================== */
  class Searcher {
    constructor(ttSizeMB = 128, learning = null) {
      this.tt = new TranspositionTable(ttSizeMB);
      this.learning = learning || new LearningBook();
      this.nodes = 0;
      this.killers = [];
      for (let i = 0; i < 128; i++) this.killers[i] = [];
      this.historyW = new Int32Array(128 * 128);
      this.historyB = new Int32Array(128 * 128);
      this.startTime = 0;
      this.softLimit = 0;
      this.hardLimit = 0;
      this.stop = false;
      this.bestMoveRoot = null;
      this.bestScoreRoot = 0;
      this.maxDepth = 0;
      this.repetitionHash = new Map();
      this.rootMoves = [];
      this.useBook = true;
      this.bookMoveChance = 1.0;
      this.nodesSinceCheck = 0;
      // FIX #C: contempt = 0 للتماثل
      this.contempt = 0;
    }

    reset() {
      this.nodes = 0;
      for (let i = 0; i < 128; i++) this.killers[i] = [];
      this.historyW.fill(0);
      this.historyB.fill(0);
      this.stop = false;
      this.bestMoveRoot = null;
      this.bestScoreRoot = 0;
      this.maxDepth = 0;
      this.repetitionHash = new Map();
      this.rootMoves = [];
      this.nodesSinceCheck = 0;
    }

    timeUp() {
      if (this.hardLimit <= 0) return false;
      this.nodesSinceCheck++;
      if ((this.nodesSinceCheck & 1023) !== 0) return false;
      return Date.now() - this.startTime >= this.hardLimit;
    }

    repKey(state) { return state.hashLo + ":" + state.hashHi; }
    pushRep(state) { const k = this.repKey(state); this.repetitionHash.set(k, (this.repetitionHash.get(k) || 0) + 1); }
    popRep(state) { const k = this.repKey(state); const c = (this.repetitionHash.get(k) || 0) - 1; if (c <= 0) this.repetitionHash.delete(k); else this.repetitionHash.set(k, c); }
    isRep(state) { return (this.repetitionHash.get(this.repKey(state)) || 0) >= 3; }

    scoreMove(state, mv, ttMove, ply) {
      const from = moveFrom(mv), to = moveTo(mv), promo = movePromo(mv);
      const b = state.board;
      if (ttMove && mv === ttMove) return 10000000;
      const victim = b[to];
      if (victim || promo) {
        let s = 1000000;
        if (promo) s += SEE_VAL[promo] * 10;
        if (victim) s += SEE_VAL[typeOf(victim)] * 10 - SEE_VAL[typeOf(b[from])];
        return s;
      }
      if (to === state.ep && typeOf(b[from]) === PAWN) return 1000000 + 100;
      const pk = this.killers[ply];
      for (let i = 0; i < pk.length; i++) {
        const k = pk[i];
        if (k && k[0] === from && k[1] === to) return 900000 - i * 1000;
      }
      const history = state.turn === WHITE ? this.historyW : this.historyB;
      return Math.min(history[from * 128 + to], 100000);
    }

    quiescence(state, alpha, beta, ply) {
      this.nodes++;
      if (this.timeUp()) { this.stop = true; return 0; }
      if (ply > 30) return evaluate(state);

      const stand = evaluate(state);
      if (stand >= beta) return beta;
      if (stand > alpha) alpha = stand;

      const moves = generatePseudoMoves(state);
      const qMoves = [], qScores = [];
      const b = state.board;
      for (const mv of moves) {
        const from = moveFrom(mv), to = moveTo(mv), promo = movePromo(mv);
        const victim = b[to];
        const isEp = to === state.ep && typeOf(b[from]) === PAWN && !victim;
        if (!victim && !promo && !isEp) continue;
        let s = 0;
        if (promo) s += 5000 + SEE_VAL[promo];
        if (victim) s += SEE_VAL[typeOf(victim)] * 10 - SEE_VAL[typeOf(b[from])];
        if (isEp) s += 100;
        qMoves.push(mv); qScores.push(s);
      }
      insertionSortMoves(qMoves, qScores);

      const us = state.turn;
      for (let qi = 0; qi < qMoves.length; qi++) {
        const mv = qMoves[qi];
        const from = moveFrom(mv), to = moveTo(mv), promo = movePromo(mv);
        const victim = b[to];
        // FIX #H: حماية moverType=0
        const moverType = typeOf(b[from]);
        if (moverType === 0) continue;
        if (victim && !promo) {
          if (SEE_VAL[typeOf(victim)] >= SEE_VAL[moverType]) {
            if (see(state, from, to, promo) < 0) continue;
          }
        }
        applyMove(state, from, to, promo);
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

      if (ply > 0) {
        // FIX #C: contempt = 0 متماثل
        if (this.isRep(state)) return this.contempt;
        if (state.halfmove >= 100) return this.contempt;
        const mAlpha = Math.max(alpha, -MATE + ply);
        const mBeta  = Math.min(beta,   MATE - ply - 1);
        if (mAlpha >= mBeta) return mAlpha;
        alpha = mAlpha; beta = mBeta;
      }

      const inCheck = isInCheck(state, state.turn);
      if (inCheck && ply < 64) depth++;

      if (depth <= 0) return this.quiescence(state, alpha, beta, ply);

      const isRoot = ply === 0;
      const tt = this.tt.probe(state.hashLo, state.hashHi);
      let ttMove = tt ? tt.bestMove : 0;
      if (tt && !isRoot && tt.depth >= depth) {
        if (tt.flag === TT_EXACT) return tt.score;
        if (tt.flag === TT_LOWER && tt.score >= beta) return tt.score;
        if (tt.flag === TT_UPPER && tt.score <= alpha) return tt.score;
      }

      if (!ttMove && depth >= 6 && !inCheck) {
        this.alphaBeta(state, depth - 3, alpha, beta, ply, false, false);
        const t2 = this.tt.probe(state.hashLo, state.hashHi);
        if (t2) ttMove = t2.bestMove;
      }

      if (allowNull && !isPV && depth >= 3 && !inCheck &&
          this.hasNonPawnMaterial(state) && Math.abs(beta) < MATE_IN_MAX) {
        const savedEp = state.ep, savedCastling = state.castling, savedHalf = state.halfmove;
        const savedKW = state.kings[0], savedKB = state.kings[1];
        const savedLo = state.hashLo, savedHi = state.hashHi;
        state.turn = 1 - state.turn;
        state.ep = -1;
        computeHash(state);
        state.history.push({ nullMove: true });
        const R = 3 + (depth >> 2);
        const score = -this.alphaBeta(state, depth - 1 - R, -beta, -beta + 1, ply + 1, false, false);
        state.history.pop();
        state.turn = 1 - state.turn;
        state.ep = savedEp; state.castling = savedCastling; state.halfmove = savedHalf;
        state.kings[0] = savedKW; state.kings[1] = savedKB;
        state.hashLo = savedLo; state.hashHi = savedHi;
        if (this.stop) return 0;
        if (score >= beta) {
          if (depth >= 8) {
            const v = this.alphaBeta(state, depth - R, beta - 1, beta, ply, false, isPV);
            if (this.stop) return 0;
            if (v >= beta) return beta;
          } else return beta;
        }
      }

      if (!isPV && !inCheck && depth <= 4 && Math.abs(beta) < MATE_IN_MAX) {
        const stand = evaluate(state);
        if (stand - 110 * depth >= beta) return stand;
      }

      const us = state.turn;
      const moves = generatePseudoMoves(state);
      const scores = new Array(moves.length);
      for (let i = 0; i < moves.length; i++) scores[i] = this.scoreMove(state, moves[i], ttMove, ply);
      insertionSortMoves(moves, scores);

      let bestScore = -INF, bestMove = 0, legalCount = 0;
      const origAlpha = alpha;
      const b = state.board;

      for (let i = 0; i < moves.length; i++) {
        const mv = moves[i];
        const from = moveFrom(mv), to = moveTo(mv), promo = movePromo(mv);

        const preVictim = b[to];
        const preIsQuiet = !preVictim && !promo && !(to === state.ep && typeOf(b[from]) === PAWN);
        if (!isPV && !inCheck && depth <= 3 && legalCount > 0 && preIsQuiet &&
            Math.abs(alpha) < MATE_IN_MAX) {
          const futility = evaluate(state) + 100 + 120 * depth;
          if (futility <= alpha) continue;
        }

        applyMove(state, from, to, promo);
        if (isInCheck(state, us)) { undoMove(state); continue; }
        legalCount++;

        const victim = b[to];
        const isQuiet = !victim && !promo && !(to === state.ep && typeOf(b[from]) === PAWN);

        if (!isPV && !inCheck && depth <= 4 && legalCount > 3 + depth * depth && isQuiet) {
          undoMove(state); continue;
        }

        let score;
        if (legalCount === 1) {
          this.pushRep(state);
          score = -this.alphaBeta(state, depth - 1, -beta, -alpha, ply + 1, true, isPV);
          this.popRep(state);
        } else {
          let reduction = 0;
          if (depth >= 3 && legalCount > 3 && isQuiet && !inCheck) {
            reduction = Math.floor(0.75 + Math.log(depth) * Math.log(legalCount) / 2.25);
            if (isPV) reduction -= 1;
            reduction = Math.max(0, Math.min(reduction, depth - 2));
          }
          this.pushRep(state);
          score = -this.alphaBeta(state, depth - 1 - reduction, -alpha - 1, -alpha, ply + 1, true, false);
          if (score > alpha && reduction > 0) {
            score = -this.alphaBeta(state, depth - 1, -alpha - 1, -alpha, ply + 1, true, false);
          }
          if (score > alpha && isPV) {
            score = -this.alphaBeta(state, depth - 1, -beta, -alpha, ply + 1, true, true);
          }
          this.popRep(state);
        }
        undoMove(state);
        if (this.stop) return 0;
        if (isRoot) this.rootMoves.push({ mv, score });

        if (score > bestScore) {
          bestScore = score;
          bestMove = mv;
          if (isRoot) this.bestMoveRoot = mv;
          if (score > alpha) {
            alpha = score;
            if (score >= beta) {
              if (isQuiet) {
                const k = this.killers[ply];
                if (!k[0] || k[0][0] !== from || k[0][1] !== to) {
                  k.unshift([from, to]);
                  if (k.length > 2) k.pop();
                }
                const history = state.turn === WHITE ? this.historyW : this.historyB;
                const key = from * 128 + to;
                history[key] = Math.min(100000, history[key] + depth * depth);
              }
              this.tt.store(state.hashLo, state.hashHi, depth, bestScore, TT_LOWER, mv);
              return bestScore;
            }
          }
        }
      }

      if (legalCount === 0) return inCheck ? -MATE + ply : this.contempt;
      const flag = bestScore <= origAlpha ? TT_UPPER : TT_EXACT;
      this.tt.store(state.hashLo, state.hashHi, depth, bestScore, flag, bestMove);
      return bestScore;
    }

    hasNonPawnMaterial(state) {
      const b = state.board, us = state.turn;
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
      const tl = opts.timeLimit || 0;
      this.softLimit = tl ? Math.floor(tl * 0.55) : 0;
      this.hardLimit = tl;
      this.maxDepth = opts.depth || 10;
      this.useBook = opts.useBook !== undefined ? opts.useBook : true;
      this.bookMoveChance = opts.bookChance !== undefined ? opts.bookChance : 0.9;
      const rootVariety = opts.rootVariety !== undefined ? opts.rootVariety : 12;

      if (this.useBook && (state.uciHistory || []).length < 20) {
        if (Math.random() < this.bookMoveChance) {
          const bookUci = findBookMove(state, this.learning);
          if (bookUci) {
            const legal = generateLegalMoves(state);
            const mv = legal.find(m => moveToUci(m) === bookUci);
            if (mv) {
              return { move: mv, score: 0, nodes: 0, depth: 0, time: 0, book: true };
            }
          }
        }
      }

      this.repetitionHash.set(this.repKey(state), 1);
      let bestMove = 0, bestScore = 0, prevScore = 0;
      let lastDepthTime = 0;

      for (let d = 1; d <= this.maxDepth; d++) {
        const iterStart = Date.now();
        this.rootMoves = [];

        let alpha = -INF, beta = INF;
        if (d >= 4 && Math.abs(prevScore) < MATE_IN_MAX) {
          const delta = 50;
          alpha = Math.max(-INF, prevScore - delta);
          beta  = Math.min(INF,  prevScore + delta);
        }

        let score = this.alphaBeta(state, d, alpha, beta, 0, true, true);
        if (this.stop) break;

        if (d >= 4 && (score <= alpha || score >= beta) && Math.abs(prevScore) < MATE_IN_MAX) {
          alpha = -INF; beta = INF;
          score = this.alphaBeta(state, d, alpha, beta, 0, true, true);
          if (this.stop) break;
        }

        if (this.bestMoveRoot) {
          bestMove = this.bestMoveRoot;
          bestScore = score;
        }
        prevScore = score;
        lastDepthTime = Date.now() - iterStart;

        if (Math.abs(score) > MATE_IN_MAX) break;
        if (opts.onDepth) opts.onDepth(d, score, this.bestMoveRoot, this.nodes);

        const elapsed = Date.now() - this.startTime;
        if (this.softLimit > 0) {
          if (elapsed >= this.softLimit) break;
          if (d >= 5 && elapsed + lastDepthTime * 2 > this.hardLimit) break;
        }
      }

      if (rootVariety > 0 && this.rootMoves.length > 1 && bestMove) {
        const candidates = this.rootMoves.filter(rm =>
          Math.abs(rm.score - bestScore) <= rootVariety &&
          Math.abs(rm.score) < MATE_IN_MAX
        );
        if (candidates.length > 1) {
          const chosen = candidates[Math.floor(Math.random() * candidates.length)];
          bestMove = chosen.mv;
          bestScore = chosen.score;
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
        depth: this.maxDepth, time: Date.now() - this.startTime
      };
    }
  }

  /* ======================== Helpers ======================== */
  function moveToUci(mv) {
    if (!mv) return null;
    let from, to, promo;
    if (Array.isArray(mv)) { [from, to, promo] = mv; }
    else { from = moveFrom(mv); to = moveTo(mv); promo = movePromo(mv); }
    let s = sqName(from) + sqName(to);
    if (promo === QUEEN) s += "q";
    else if (promo === ROOK) s += "r";
    else if (promo === BISHOP) s += "b";
    else if (promo === KNIGHT) s += "n";
    return s;
  }
  function uciToMove(state, uci) {
    if (!uci || uci.length < 4) return null;
    const from = nameToSq(uci.slice(0, 2));
    const to = nameToSq(uci.slice(2, 4));
    let promo = 0;
    if (uci.length > 4) {
      const c = uci[4];
      promo = c === "q" ? QUEEN : c === "r" ? ROOK : c === "b" ? BISHOP : c === "n" ? KNIGHT : 0;
    }
    const legal = generateLegalMoves(state);
    for (const mv of legal) {
      if (moveFrom(mv) === from && moveTo(mv) === to && movePromo(mv) === promo) return mv;
    }
    return null;
  }

  /* ======================== Main Engine ======================== */
  class ChessEngine {
    constructor(opts = {}) {
      this.ttSizeMB = opts.ttSizeMB || 128;
      this.defaultDepth = opts.depth || 12;
      this.learning = new LearningBook();
      this.searcher = new Searcher(this.ttSizeMB, this.learning);
      this.ready = true;
      this.uciHistory = [];
      // FIX #E: bookEnabled على ChessEngine أيضاً
      this.bookEnabled = opts.bookEnabled !== false;
      this.searcher.useBook = this.bookEnabled;
    }

    init() { return Promise.resolve(); }

    learnGame(engineColor, moves, result) {
      for (const m of moves) {
        try {
          const st = parseFEN(m.fen);
          if (colorOf(st.turn) === (engineColor === 'white' ? WHITE : BLACK)) {
            this.learning.recordMove(st, m.uci, result === 'win' ? 'loss' : result === 'loss' ? 'win' : 'draw');
          }
        } catch(e) {}
      }
    }

    async getBestMove(fen, opts = {}) {
      const state = parseFEN(fen);
      if (opts.uciHistory) state.uciHistory = opts.uciHistory.slice();
      else state.uciHistory = [];

      const depth = opts.depth || this.defaultDepth;
      const res = this.searcher.search(state, {
        depth,
        timeLimit: opts.timeLimit || 0,
        useBook: opts.useBook !== undefined ? opts.useBook : this.bookEnabled,
        bookChance: opts.bookChance !== undefined ? opts.bookChance : 0.9,
        rootVariety: opts.rootVariety !== undefined ? opts.rootVariety : 12,
        onDepth: opts.onDepth,
      });

      const uci = moveToUci(res.move);

      if (uci && !opts.uciHistory) this.uciHistory.push(uci);

      return {
        move: uci, score: res.score, nodes: res.nodes,
        depth: res.depth, time: res.time, book: !!res.book,
      };
    }

    async analyze(fen, opts = {}) { return this.getBestMove(fen, opts); }

    learnFromLoss(history) {
      for (const h of history) {
        try {
          const st = parseFEN(h.fen);
          this.learning.recordMove(st, h.uci, 'loss');
        } catch (e) {}
      }
    }
    learnFromWin(history) {
      for (const h of history) {
        try {
          const st = parseFEN(h.fen);
          this.learning.recordMove(st, h.uci, 'win');
        } catch (e) {}
      }
    }
    saveLearning(key = "chessEnginePro_learning") { return this.learning.saveToStorage(key); }
    loadLearning(key = "chessEnginePro_learning") { return this.learning.loadFromStorage(key); }
    clearLearning() { this.learning.clear(); }
    setLearningEnabled(on) { this.learning.enabled = !!on; }
    exportLearning() { return this.learning.export(); }
    importLearning(data) { this.learning.import(data); }

    static legalMoves(fen) {
      const st = parseFEN(fen);
      return generateLegalMoves(st).map(moveToUci);
    }
    static perft(fen, depth) {
      const st = parseFEN(fen);
      function p(s, d) {
        if (d === 0) return 1;
        let n = 0;
        const moves = generateLegalMoves(s);
        for (const mv of moves) {
          const from = moveFrom(mv), to = moveTo(mv), promo = movePromo(mv);
          applyMove(s, from, to, promo);
          n += p(s, d - 1);
          undoMove(s);
        }
        return n;
      }
      return p(st, depth);
    }
  }

  /* ========================= Exports (FIX #A, #B) ========================= */
  // FIX #A: تصدير آمن للمتصفح — يُضبط دائماً قبل أي شيء آخر
  const helpers = {
    parseFEN, toFEN, generateLegalMoves, applyMove, undoMove,
    evaluate, sqName, nameToSq, moveToUci, uciToMove,
    encodeMove, decodeMove, moveFrom, moveTo, movePromo,
    LearningBook, OPENING_BOOK,
    // ثوابت مفيدة للموقع
    WHITE, BLACK, PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING,
    computeHash, generatePseudoMoves, isSquareAttackedBy,
  };

  // ✅ التصدير للمتصفح دائماً — قبل أي شرط
  if (typeof window !== "undefined") {
    window.ChessEngine = ChessEngine;
    window.ChessEngineHelpers = helpers;
    window.MyChessEngine = ChessEngine;
  }

  // ✅ Node.js / CommonJS
  if (typeof module !== "undefined" && module.exports) {
    module.exports = ChessEngine;
    Object.assign(module.exports, helpers);
  }

  // ✅ Worker / globalThis (احتياطي)
  if (typeof globalThis !== "undefined" && typeof window === "undefined") {
    globalThis.MyChessEngine = ChessEngine;
    globalThis.ChessEngine = ChessEngine;
    globalThis.ChessEngineHelpers = helpers;
  }

})(typeof window !== "undefined" ? window : globalThis);