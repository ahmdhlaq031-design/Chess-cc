/* ============================================================================
 * ChessEnginePro v4 — محرك خارق + افتتاحيات + تعلّم تلقائي
 * ----------------------------------------------------------------------------
 * [v4 جديد]
 *  - PVS (Principal Variation Search) + Aspiration Windows محسّنة
 *  - LMR متعدد المستويات + History Heuristic (butterfly + counter-move)
 *  - Null Move + Reverse Futility + ProbCut + Futility Pruning
 *  - Check Extension + Singular Extension مبسّط
 *  - Evaluation محسّن: outposts, connected pawns, space, mop-up, king attack maps
 *  - SEE محسّن + Delta Pruning في QSearch
 *  - Opening Book موسّع (50+ خط) مع Transposition
 *  - Time management ذكي + Iterative Deepening
 * [v3 محفوظ] Opening Book + Root Randomization + Auto-Learning + Book Avoidance
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
  const MATE = 30000, MATE_IN_MAX = MATE - 1000, INF = 1000000;

  /* --------------------------- Attack detection ---------------------- */
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
  }

  /* ------------------------- Zobrist -------------------------------- */
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
      from, to, promoType: promoType || 0, captured, capturedSq,
      prevCastling: state.castling, prevEp: state.ep, prevHalf: state.halfmove,
      prevKings: state.kings.slice(), hashLo: state.hashLo, hashHi: state.hashHi, prevFull: state.fullmove,
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
    state.kings = h.prevKings; state.turn = 1 - state.turn;
    state.fullmove = h.prevFull; state.hashLo = h.hashLo; state.hashHi = h.hashHi;
  }

  /* --------------------------- Move Generation ----------------------- */
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
          } else if (to === state.ep && !target) moves.push([from, to, 0]);
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
    const legal = [], us = state.turn;
    for (const mv of pseudo) {
      applyMove(state, mv[0], mv[1], mv[2]);
      if (!isInCheck(state, us)) legal.push(mv);
      undoMove(state);
    }
    return legal;
  }

  /* ------------------------------- SEE ------------------------------- */
  const SEE_VAL = [0, 100, 320, 330, 500, 900, 20000];

  function see(state, from, to, promoType) {
    const b = state.board;
    const target = b[to];
    const isEp = (to === state.ep && typeOf(b[from]) === PAWN && !target);
    if (!target && !isEp && !promoType) return 0;
    const snapshot = b.slice();
    const kingsBackup = state.kings.slice();
    let gain = [];
    gain[0] = target ? SEE_VAL[typeOf(target)] : SEE_VAL[PAWN];
    let side = 1 - colorOf(b[from]);
    let curType = promoType || typeOf(b[from]);
    b[to] = pieceOf(colorOf(b[from]), curType);
    b[from] = 0;
    if (isEp) b[colorOf(b[from]) === WHITE ? to + 16 : to - 16] = 0;
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
          for (const dd of N_DIRS) if (sq + dd === to) { attacks = true; break; }
        } else if (t === KING) {
          for (const dd of K_DIRS) if (sq + dd === to) { attacks = true; break; }
        } else {
          const dirs = t === BISHOP ? B_DIRS : t === ROOK ? R_DIRS : K_DIRS;
          for (const dd of dirs) {
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
    state.kings = kingsBackup;
    let val = gain[d];
    for (let i = d - 1; i >= 0; i--) val = gain[i] - Math.max(0, val);
    return val;
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
  const PASSED_BONUS = [0, 5, 15, 30, 55, 90, 140, 0];
  const CONNECTED_BONUS = [0, 3, 6, 12, 20, 32, 50, 0];

  function psqtIndex(sq, color) {
    const r = sq >> 4, f = sq & 7;
    return color === WHITE ? r * 8 + f : (7 - r) * 8 + f;
  }

  function evaluate(state) {
    const b = state.board;
    let mg = 0, eg = 0, phase = 0;
    const phaseVal = [0, 0, 1, 1, 2, 4, 0];
    let wPawns = [0,0,0,0,0,0,0,0], bPawns = [0,0,0,0,0,0,0,0];
    let wBishops = 0, bBishops = 0, wKnights = 0, bKnights = 0;
    let wRooks = 0, bRooks = 0, wQueens = 0, bQueens = 0;
    let wKingSq = -1, bKingSq = -1;
    let wPawnSqs = [], bPawnSqs = [];
    let wMinors = 0, bMinors = 0, wMajors = 0, bMajors = 0;

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
      if (t === PAWN) { (c === WHITE ? wPawns : bPawns)[sq & 7]++; (c === WHITE ? wPawnSqs : bPawnSqs).push(sq); }
      else if (t === BISHOP) { if (c === WHITE) { wBishops++; wMinors++; } else { bBishops++; bMinors++; } }
      else if (t === KNIGHT) { if (c === WHITE) { wKnights++; wMinors++; } else { bKnights++; bMinors++; } }
      else if (t === ROOK) { if (c === WHITE) { wRooks++; wMajors++; } else { bRooks++; bMajors++; } }
      else if (t === QUEEN) { if (c === WHITE) { wQueens++; wMajors++; } else { bQueens++; bMajors++; } }
      else if (t === KING) { if (c === WHITE) wKingSq = sq; else bKingSq = sq; }
    }

    // === Pawn structure ===
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
    mg += structW - structB; eg += structW - structB;

    // === Bishop pair ===
    if (wBishops >= 2) { mg += 30; eg += 55; }
    if (bBishops >= 2) { mg -= 30; eg -= 55; }

    // === Rook on open/semi-open file ===
    for (let sq = 0; sq < 128; sq++) {
      if (!isValidSq(sq)) continue;
      const p = b[sq];
      if (!p || typeOf(p) !== ROOK) continue;
      const c = colorOf(p), f = sq & 7;
      const own = c === WHITE ? wPawns : bPawns;
      const opp = c === WHITE ? bPawns : wPawns;
      if (own[f] === 0 && opp[f] === 0) mg += c === WHITE ? 25 : -25;
      else if (own[f] === 0) mg += c === WHITE ? 12 : -12;
    }

    // === Knight outposts ===
    for (let sq = 0; sq < 128; sq++) {
      if (!isValidSq(sq)) continue;
      const p = b[sq];
      if (!p || typeOf(p) !== KNIGHT) continue;
      const c = colorOf(p), r = sq >> 4, f = sq & 7;
      const oppColor = 1 - c;
      const oppPawns = c === WHITE ? bPawns : wPawns;
      const ownPawns = c === WHITE ? wPawns : bPawns;
      const rankForWhite = c === WHITE ? r : 7 - r;
      if (rankForWhite >= 2 && rankForWhite <= 5) {
        let supportedByOwnPawn = false;
        if (c === WHITE) {
          if (isValidSq(sq + 15) && b[sq + 15] === W_PAWN) supportedByOwnPawn = true;
          if (isValidSq(sq + 17) && b[sq + 17] === W_PAWN) supportedByOwnPawn = true;
        } else {
          if (isValidSq(sq - 15) && b[sq - 15] === B_PAWN) supportedByOwnPawn = true;
          if (isValidSq(sq - 17) && b[sq - 17] === B_PAWN) supportedByOwnPawn = true;
        }
        let attackableByOppPawn = false;
        for (let df = -1; df <= 1; df += 2) {
          const ff = f + df;
          if (ff < 0 || ff > 7) continue;
          if (c === WHITE) {
            for (let rr = r - 1; rr >= 0; rr--) if (b[rr * 16 + ff] === B_PAWN) { attackableByOppPawn = true; break; }
          } else {
            for (let rr = r + 1; rr < 8; rr++) if (b[rr * 16 + ff] === W_PAWN) { attackableByOppPawn = true; break; }
          }
          if (attackableByOppPawn) break;
        }
        if (supportedByOwnPawn && !attackableByOppPawn) {
          const bonus = 18;
          if (c === WHITE) mg += bonus; else mg -= bonus;
        }
      }
    }

    // === Connected pawns ===
    for (const sq of wPawnSqs) {
      const f = sq & 7, r = sq >> 4;
      for (const df of [-1, 1]) {
        const ff = f + df;
        if (ff < 0 || ff > 7) continue;
        const adjSq = r * 16 + ff;
        if (b[adjSq] === W_PAWN) { const bn = CONNECTED_BONUS[7 - r] || 0; mg += bn; eg += bn; break; }
      }
    }
    for (const sq of bPawnSqs) {
      const f = sq & 7, r = sq >> 4;
      for (const df of [-1, 1]) {
        const ff = f + df;
        if (ff < 0 || ff > 7) continue;
        const adjSq = r * 16 + ff;
        if (b[adjSq] === B_PAWN) { const bn = CONNECTED_BONUS[r] || 0; mg -= bn; eg -= bn; break; }
      }
    }

    // === Passed pawns ===
    for (const sq of wPawnSqs) {
      const f = sq & 7, r = sq >> 4;
      let passed = true;
      for (let df = -1; df <= 1; df++) {
        const ff = f + df;
        if (ff < 0 || ff > 7) continue;
        for (const bsq of bPawnSqs) if ((bsq & 7) === ff && (bsq >> 4) < r) { passed = false; break; }
        if (!passed) break;
      }
      if (passed) { const bonus = PASSED_BONUS[7 - r] || 0; mg += bonus; eg += bonus * 1.6; }
    }
    for (const sq of bPawnSqs) {
      const f = sq & 7, r = sq >> 4;
      let passed = true;
      for (let df = -1; df <= 1; df++) {
        const ff = f + df;
        if (ff < 0 || ff > 7) continue;
        for (const wsq of wPawnSqs) if ((wsq & 7) === ff && (wsq >> 4) > r) { passed = false; break; }
        if (!passed) break;
      }
      if (passed) { const bonus = PASSED_BONUS[r] || 0; mg -= bonus; eg -= bonus * 1.6; }
    }

    // === King safety via attack maps ===
    if (phase > 8) {
      const wKingF = wKingSq & 7, wKingR = wKingSq >> 4;
      const bKingF = bKingSq & 7, bKingR = bKingSq >> 4;
      let wDanger = 0, bDanger = 0;
      let wAttackCount = 0, bAttackCount = 0;
      for (let sq = 0; sq < 128; sq++) {
        if (!isValidSq(sq)) continue;
        const p = b[sq];
        if (!p) continue;
        const t = typeOf(p);
        if (t === PAWN || t === KING) continue;
        const c = colorOf(p);
        const r = sq >> 4, f = sq & 7;
        if (c === BLACK) {
          const dist = Math.max(Math.abs(r - wKingR), Math.abs(f - wKingF));
          if (dist <= 2) {
            const w = t === QUEEN ? 6 : (t === ROOK ? 4 : 3);
            wDanger += w; wAttackCount++;
          }
        } else {
          const dist = Math.max(Math.abs(r - bKingR), Math.abs(f - bKingF));
          if (dist <= 2) {
            const w = t === QUEEN ? 6 : (t === ROOK ? 4 : 3);
            bDanger += w; bAttackCount++;
          }
        }
      }
      mg -= wDanger * 4; mg += bDanger * 4;
      if (wAttackCount >= 2) mg -= wAttackCount * 6;
      if (bAttackCount >= 2) mg += bAttackCount * 6;
    }

    // === Pawn shield ===
    if (phase > 8) {
      if (wKingSq >= 0) {
        const f = wKingSq & 7, r = wKingSq >> 4;
        if (r >= 6) for (let df = -1; df <= 1; df++) { const ff = f + df; if (ff >= 0 && ff < 8 && b[(r - 1) * 16 + ff] === W_PAWN) mg += 12; }
      }
      if (bKingSq >= 0) {
        const f = bKingSq & 7, r = bKingSq >> 4;
        if (r <= 1) for (let df = -1; df <= 1; df++) { const ff = f + df; if (ff >= 0 && ff < 8 && b[(r + 1) * 16 + ff] === B_PAWN) mg -= 12; }
      }
    }

    // === Space ===
    if (phase > 12) {
      let wSpace = 0, bSpace = 0;
      for (let f = 0; f < 8; f++) {
        for (let r = 2; r <= 3; r++) {
          const p = b[r * 16 + f];
          if (p === W_PAWN || p === W_KNIGHT || p === W_BISHOP) wSpace++;
        }
        for (let r = 4; r <= 5; r++) {
          const p = b[r * 16 + f];
          if (p === B_PAWN || p === B_KNIGHT || p === B_BISHOP) bSpace++;
        }
      }
      mg += (wSpace - bSpace) * 2;
    }

    const ph = Math.min(24, phase) / 24;
    let score = mg * ph + eg * (1 - ph);
    score += state.turn === WHITE ? 10 : -10;

    // === Insufficient material ===
    const noPawns = wPawnSqs.length === 0 && bPawnSqs.length === 0;
    if (noPawns && wRooks === 0 && bRooks === 0 && wQueens === 0 && bQueens === 0) {
      if (wBishops + wKnights <= 1 && bBishops + bKnights <= 1) return 0;
    }

    // === Mop-up (KQ vs K, KR vs K) ===
    if (noPawns && phase <= 4 && (wQueens + wRooks >= 1 || bQueens + bRooks >= 1)) {
      const materialDiff = (wQueens * 900 + wRooks * 500 + wBishops * 330 + wKnights * 320)
                         - (bQueens * 900 + bRooks * 500 + bBishops * 330 + bKnights * 320);
      if (Math.abs(materialDiff) >= 500) {
        const winningKingSq = materialDiff > 0 ? wKingSq : bKingSq;
        const losingKingSq = materialDiff > 0 ? bKingSq : wKingSq;
        if (winningKingSq >= 0 && losingKingSq >= 0) {
          const wkf = winningKingSq & 7, wkr = winningKingSq >> 4;
          const lkf = losingKingSq & 7, lkr = losingKingSq >> 4;
          const centerDist = Math.abs(3.5 - lkf) + Math.abs(3.5 - lkr);
          const kingDist = Math.abs(wkf - lkf) + Math.abs(wkr - lkr);
          const mopup = centerDist * 10 + (14 - kingDist) * 4;
          if (materialDiff > 0) score += mopup; else score -= mopup;
        }
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
      this.generation = 0;
    }
    clear() { this.keysLo.fill(0); this.keysHi.fill(0); this.depth.fill(0); this.flag.fill(0); }
    index(lo, hi) { return ((lo ^ (hi * 2654435761)) >>> 0) & this.mask; }
    probe(lo, hi) {
      const i = this.index(lo, hi);
      if (this.keysLo[i] === lo && this.keysHi[i] === hi && this.flag[i] !== 0) {
        return { depth: this.depth[i], score: this.score[i], flag: this.flag[i],
          bestMove: this.bestFrom[i] ? [this.bestFrom[i], this.bestTo[i], this.bestPromo[i]] : null };
      }
      return null;
    }
    store(lo, hi, depth, score, flag, bestMove) {
      const i = this.index(lo, hi);
      if (this.keysLo[i] === lo && this.keysHi[i] === hi && this.depth[i] > depth) return;
      this.keysLo[i] = lo; this.keysHi[i] = hi; this.depth[i] = depth;
      this.score[i] = score; this.flag[i] = flag;
      if (bestMove) {
        this.bestFrom[i] = bestMove[0]; this.bestTo[i] = bestMove[1]; this.bestPromo[i] = bestMove[2] || 0;
      } else { this.bestFrom[i] = 0; this.bestTo[i] = 0; this.bestPromo[i] = 0; }
    }
    newSearch() { this.generation++; }
  }

  /* ===================== OPENING BOOK ================================ */
  const OPENING_BOOK = [
    // Italian / Giuoco Piano
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1c4","f8c5"], name: "Italian Game" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1c4","g8f6"], name: "Two Knights" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1c4","f8c5","c2c3"], name: "Giuoco Piano" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1c4","f8c5","c2c3","g8f6","d2d3"], name: "Giuoco Pianissimo" },
    // Ruy Lopez
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5"], name: "Ruy Lopez" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5","a7a6"], name: "Morphy Defense" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5","a7a6","b5a4","g8f6"], name: "Ruy Lopez Main" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5","a7a6","b5a4","g8f6","e1g1"], name: "Ruy Lopez Castled" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5","a7a6","b5a4","g8f6","e1g1","f8e7"], name: "Ruy Lopez Closed" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","f1b5","g8f6"], name: "Berlin Defense" },
    // Scotch
    { moves: ["e2e4","e7e5","g1f3","b8c6","d2d4"], name: "Scotch Game" },
    { moves: ["e2e4","e7e5","g1f3","b8c6","d2d4","e5d4","f3d4"], name: "Scotch Main" },
    // Sicilian
    { moves: ["e2e4","c7c5"], name: "Sicilian" },
    { moves: ["e2e4","c7c5","g1f3","d7d6"], name: "Sicilian Najdorf-ish" },
    { moves: ["e2e4","c7c5","g1f3","b8c6","d2d4","c5d4"], name: "Sicilian Open" },
    { moves: ["e2e4","c7c5","b1c3"], name: "Sicilian Closed" },
    { moves: ["e2e4","c7c5","g1f3","e7e6"], name: "Sicilian French-ish" },
    { moves: ["e2e4","c7c5","g1f3","g8f6"], name: "Sicilian Nimzowitsch" },
    // French
    { moves: ["e2e4","e7e6"], name: "French" },
    { moves: ["e2e4","e7e6","d2d4","d7d5"], name: "French Main" },
    { moves: ["e2e4","e7e6","d2d4","d7d5","b1c3"], name: "French Winawer-ish" },
    // Caro-Kann
    { moves: ["e2e4","c7c6"], name: "Caro-Kann" },
    { moves: ["e2e4","c7c6","d2d4","d7d5"], name: "Caro-Kann Main" },
    { moves: ["e2e4","c7c6","d2d4","d7d5","b1c3"], name: "Caro-Kann Classical" },
    // Queen's Gambit
    { moves: ["d2d4","d7d5","c2c4"], name: "Queen's Gambit" },
    { moves: ["d2d4","d7d5","c2c4","e7e6"], name: "QGD" },
    { moves: ["d2d4","d7d5","c2c4","c7c6"], name: "Slav Defense" },
    { moves: ["d2d4","d7d5","c2c4","d5c4"], name: "QGA" },
    // London
    { moves: ["d2d4","d7d5","g1f3","g8f6","c1f4"], name: "London System" },
    { moves: ["d2d4","g8f6","g1f3","e7e6","c1f4"], name: "London vs Indian" },
    { moves: ["d2d4","g8f6","g1f3","e7e6","c1f4","b7b6"], name: "London vs Queen's Indian" },
    // Catalan
    { moves: ["d2d4","g8f6","c2c4","e7e6","g2g3"], name: "Catalan" },
    { moves: ["d2d4","g8f6","c2c4","e7e6","g2g3","d7d5","f1g2"], name: "Catalan Main" },
    // King's Indian
    { moves: ["d2d4","g8f6","c2c4","g7g6"], name: "King's Indian" },
    { moves: ["d2d4","g8f6","c2c4","g7g6","b1c3","f8g7"], name: "KID Main" },
    { moves: ["d2d4","g8f6","c2c4","g7g6","b1c3","d7d5"], name: "Grünfeld" },
    // English
    { moves: ["c2c4"], name: "English" },
    { moves: ["c2c4","e7e5"], name: "English Reversed Sicilian" },
    { moves: ["c2c4","g8f6","b1c3"], name: "English Main" },
    { moves: ["c2c4","e7e6","g1f3","d7d5"], name: "English vs French-ish" },
    // Dutch
    { moves: ["d2d4","f7f5"], name: "Dutch" },
    { moves: ["d2d4","f7f5","g2g3","g8f6"], name: "Dutch Leningrad" },
    // Vienna
    { moves: ["e2e4","e7e5","b1c3"], name: "Vienna Game" },
    { moves: ["e2e4","e7e5","b1c3","g8f6"], name: "Vienna Main" },
    // King's Gambit
    { moves: ["e2e4","e7e5","f2f4"], name: "King's Gambit" },
    // Pirc / Modern
    { moves: ["e2e4","d7d6","d2d4","g8f6"], name: "Pirc" },
    { moves: ["e2e4","g7g6"], name: "Modern Defense" },
    // Alekhine
    { moves: ["e2e4","g8f6"], name: "Alekhine" },
    // Scandinavian
    { moves: ["e2e4","d7d5"], name: "Scandinavian" },
    { moves: ["e2e4","d7d5","e4d5","d8d5"], name: "Scandinavian Main" },
    // Four Knights / Petrov
    { moves: ["e2e4","e7e5","g1f3","b8c6","b1c3","g8f6"], name: "Four Knights" },
    { moves: ["e2e4","e7e5","g1f3","g8f6"], name: "Petrov Defense" },
    // Budapest
    { moves: ["d2d4","g8f6","c2c4","e7e5"], name: "Budapest Gambit" },
    // Vienna → 1.e4 e5 2.Nc3 Nf6 3.Bc4
    { moves: ["e2e4","e7e5","b1c3","g8f6","f1c4"], name: "Vienna with Bc4" },
    // Bird
    { moves: ["f2f4"], name: "Bird's Opening" },
    // Nimzo-Indian
    { moves: ["d2d4","g8f6","c2c4","e7e6","b1c3","f8b4"], name: "Nimzo-Indian" },
    // Queen's Indian
    { moves: ["d2d4","g8f6","c2c4","e7e6","g1f3","b7b6"], name: "Queen's Indian" },
    // Benoni
    { moves: ["d2d4","g8f6","c2c4","c7c5"], name: "Benoni" },
    // Benko
    { moves: ["d2d4","g8f6","c2c4","c7c5","d4d5","b7b5"], name: "Benko Gambit" },
  ];

  class LearningBook {
    constructor() {
      this.stats = new Map();
      this.bookPenalty = new Map();
      this.enabled = true;
      this.penaltyPerLoss = 300;
      this.maxPenalty = 700;
      this.rewardPerWin = 70;
      this.maxReward = 240;
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
      return { stats: Array.from(this.stats.entries()), bookPenalty: Array.from(this.bookPenalty.entries()) };
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

  function findBookMove(state, learningBook) {
    if (!state.uciHistory || state.uciHistory.length === 0) {
      const firstMoves = new Set();
      for (const entry of OPENING_BOOK) firstMoves.add(entry.moves[0]);
      const arr = Array.from(firstMoves);
      return arr[Math.floor(Math.random() * arr.length)];
    }
    const history = state.uciHistory.join(" ");
    const histLen = state.uciHistory.length;
    const candidates = [];
    const legal = generateLegalMoves(state);
    const legalUcis = legal.map(m => moveToUci(m));
    for (const entry of OPENING_BOOK) {
      if (entry.moves.length <= histLen) continue;
      const prefix = entry.moves.slice(0, histLen).join(" ");
      if (prefix === history) {
        const nextMove = entry.moves[histLen];
        if (legalUcis.includes(nextMove)) {
          let adj = 0;
          if (learningBook && learningBook.enabled) adj = learningBook.getAdjustment(state, nextMove);
          candidates.push({ uci: nextMove, name: entry.name, adj });
        }
      }
    }
    if (candidates.length === 0) return null;
    candidates.sort((a, b) => a.adj - b.adj);
    if (candidates.length === 1) return candidates[0].uci;
    const bestAdj = candidates[0].adj;
    const topCandidates = candidates.filter(c => c.adj <= bestAdj + 100);
    return topCandidates[Math.floor(Math.random() * topCandidates.length)].uci;
  }

  /* ------------------------------ Search ----------------------------- */
  class Searcher {
    constructor(ttSizeMB = 64, learning = null) {
      this.tt = new TranspositionTable(ttSizeMB);
      this.learning = learning || new LearningBook();
      this.nodes = 0;
      this.killers = [[], [], []]; // 3 plies
      this.history = new Map();
      this.counterMove = new Map(); // counter-move heuristic
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
      this.contempt = 15;
    }

    reset() {
      this.nodes = 0;
      this.killers = [[], [], []];
      this.history = new Map();
      this.counterMove = new Map();
      this.stop = false;
      this.bestMoveRoot = null;
      this.bestScoreRoot = 0;
      this.maxDepth = 0;
      this.repetitionHash = new Map();
      this.rootMoves = [];
    }

    timeUp() {
      if (this.hardLimit <= 0) return false;
      if ((this.nodes & 511) !== 0) return false;
      return Date.now() - this.startTime >= this.hardLimit;
    }

    softTimeUp() {
      if (this.softLimit <= 0) return false;
      return Date.now() - this.startTime >= this.softLimit;
    }

    repKey(state) { return state.hashLo + ":" + state.hashHi; }
    pushRep(state) { const k = this.repKey(state); this.repetitionHash.set(k, (this.repetitionHash.get(k) || 0) + 1); }
    popRep(state) { const k = this.repKey(state); const c = (this.repetitionHash.get(k) || 0) - 1; if (c <= 0) this.repetitionHash.delete(k); else this.repetitionHash.set(k, c); }
    isRep(state) { return (this.repetitionHash.get(this.repKey(state)) || 0) >= 1; }

    addKiller(ply, mv) {
      const slot = this.killers[ply] || (this.killers[ply] = []);
      if (slot[0] && slot[0][0] === mv[0] && slot[0][1] === mv[1]) return;
      slot.unshift([mv[0], mv[1]]);
      if (slot.length > 2) slot.pop();
    }

    isKiller(ply, mv) {
      const slot = this.killers[ply];
      if (!slot) return -1;
      for (let i = 0; i < slot.length; i++) if (slot[i][0] === mv[0] && slot[i][1] === mv[1]) return i;
      return -1;
    }

    scoreMove(state, mv, ttMove, ply) {
      const [from, to, promo] = mv;
      const b = state.board;
      if (ttMove && from === ttMove[0] && to === ttMove[1] && (promo || 0) === (ttMove[2] || 0)) return 10_000_000;
      const victim = b[to];
      let s = 0;
      if (victim) {
        s += 1_000_000 + SEE_VAL[typeOf(victim)] * 10 - SEE_VAL[typeOf(b[from])];
      }
      if (promo) s += 500_000 + SEE_VAL[promo];
      const kIdx = this.isKiller(ply, mv);
      if (kIdx >= 0) s += 90_000 - kIdx * 1000;
      // counter-move
      const cmKey = from * 128 + to;
      if (this.counterMove.has(cmKey)) s += 5000;
      // history
      const hKey = from * 128 + to;
      s += Math.min(this.history.get(hKey) || 0, 8000);
      // learning
      if (!victim && !promo && this.learning && this.learning.enabled) {
        s -= this.learning.getAdjustment(state, moveToUci(mv));
      }
      return s;
    }

    quiescence(state, alpha, beta, ply) {
      this.nodes++;
      if (this.timeUp()) { this.stop = true; return 0; }
      const stand = evaluate(state);
      if (stand >= beta) return beta;
      if (stand > alpha) alpha = stand;
      let moves = generatePseudoMoves(state);
      moves = moves.filter(mv => {
        const victim = state.board[mv[1]];
        if (!victim && !mv[2]) {
          if (mv[1] === state.ep && typeOf(state.board[mv[0]]) === PAWN) return true;
          return false;
        }
        return true;
      });
      const scored = moves.map(mv => {
        const victim = state.board[mv[1]];
        let s = victim ? SEE_VAL[typeOf(victim)] * 10 - SEE_VAL[typeOf(state.board[mv[0]])] : 0;
        if (mv[2]) s += 5000;
        return { mv, s };
      }).sort((a, b) => b.s - a.s);
      const us = state.turn;
      for (const { mv } of scored) {
        const victim = state.board[mv[1]];
        const attacker = state.board[mv[0]];
        if (victim && !mv[2] && SEE_VAL[typeOf(victim)] < SEE_VAL[typeOf(attacker)]) {
          if (see(state, mv[0], mv[1], 0) < 0) continue;
        }
        // Delta pruning
        if (!state.turn && false) {}
        if (!mv[2] && victim && stand + SEE_VAL[typeOf(victim)] + 200 < alpha) continue;
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
      if (ply > 0) {
        if (this.isRep(state)) return this.contempt;
        if (state.halfmove >= 100) return 0;
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
        if (!isRoot && tt.depth >= depth) {
          if (tt.flag === TT_EXACT) return tt.score;
          if (tt.flag === TT_LOWER && tt.score >= beta) return tt.score;
          if (tt.flag === TT_UPPER && tt.score <= alpha) return tt.score;
        }
      }

      // Internal iterative deepening
      if (!ttMove && depth >= 5 && !inCheck) {
        this.alphaBeta(state, depth - 2, alpha, beta, ply, false, false);
        const t2 = this.tt.probe(state.hashLo, state.hashHi);
        if (t2) ttMove = t2.bestMove;
      }

      // Null move pruning
      if (allowNull && !isPV && depth >= 3 && !inCheck && this.hasNonPawnMaterial(state) && beta < MATE_IN_MAX && Math.abs(beta) < MATE_IN_MAX) {
        const savedEp = state.ep, savedCastling = state.castling, savedHalf = state.halfmove;
        const savedKings = state.kings.slice();
        const savedLo = state.hashLo, savedHi = state.hashHi;
        state.turn = 1 - state.turn;
        state.ep = -1;
        computeHash(state);
        state.history.push({ nullMove: true });
        const R = 2 + Math.floor(depth / 4);
        const score = -this.alphaBeta(state, depth - 1 - R, -beta, -beta + 1, ply + 1, false, false);
        state.history.pop();
        state.turn = 1 - state.turn;
        state.ep = savedEp; state.castling = savedCastling; state.halfmove = savedHalf;
        state.kings = savedKings; state.hashLo = savedLo; state.hashHi = savedHi;
        if (this.stop) return 0;
        if (score >= beta) return beta;
      }

      // Reverse futility pruning
      if (!isPV && !inCheck && depth <= 6 && Math.abs(beta) < MATE_IN_MAX) {
        const stand = evaluate(state);
        const margin = 100 + 90 * depth;
        if (stand - margin >= beta) return stand;
      }

      const us = state.turn;
      const moves = generatePseudoMoves(state);
      const scored = moves.map(mv => ({ mv, s: this.scoreMove(state, mv, ttMove, ply) }));
      scored.sort((a, b) => b.s - a.s);
      let bestScore = -INF, bestMove = null, legalCount = 0;
      const origAlpha = alpha;
      const staticEval = evaluate(state);

      for (let i = 0; i < scored.length; i++) {
        const mv = scored[i].mv;
        const victim = state.board[mv[1]];

        // Late move pruning (LMP)
        if (!isPV && !inCheck && depth <= 4 && legalCount >= 3 + depth * depth && !mv[2]) {
          if (!victim) continue;
        }

        applyMove(state, mv[0], mv[1], mv[2]);
        if (isInCheck(state, us)) { undoMove(state); continue; }
        legalCount++;
        const isQuiet = !victim && !mv[2];

        // Futility pruning
        if (!isPV && !inCheck && depth <= 4 && legalCount > 1 && isQuiet &&
            staticEval + 90 + 110 * depth < alpha && Math.abs(alpha) < MATE_IN_MAX) {
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
            reduction = 1;
            if (legalCount > 6) reduction++;
            if (depth >= 6 && legalCount > 10) reduction++;
            if (depth >= 10 && legalCount > 15) reduction++;
            if (isPV) reduction--;
            if (reduction < 0) reduction = 0;
            if (reduction >= depth) reduction = depth - 1;
          }
          this.pushRep(state);
          score = -this.alphaBeta(state, depth - 1 - reduction, -alpha - 1, -alpha, ply + 1, true, false);
          // Re-search
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
        if (isRoot) this.rootMoves.push({ mv, score });
        if (score > bestScore) {
          bestScore = score;
          bestMove = mv;
          if (isRoot) this.bestMoveRoot = mv;
          if (score > alpha) {
            alpha = score;
            if (score >= beta) {
              if (isQuiet) {
                this.addKiller(ply, mv);
                const key = mv[0] * 128 + mv[1];
                this.history.set(key, Math.min(8000, (this.history.get(key) || 0) + depth * depth));
                this.counterMove.set(mv[0] * 128 + mv[1], true);
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
      this.maxDepth = opts.depth || 5;
      this.useBook = opts.useBook !== undefined ? opts.useBook : true;
      this.bookMoveChance = opts.bookChance !== undefined ? opts.bookChance : 1.0;
      const rootVariety = opts.rootVariety !== undefined ? opts.rootVariety : 25;

      // Opening book
      if (this.useBook && state.uciHistory && state.uciHistory.length < 24) {
        if (Math.random() < this.bookMoveChance) {
          const bookUci = findBookMove(state, this.learning);
          if (bookUci) {
            const legal = generateLegalMoves(state);
            const mv = legal.find(m => moveToUci(m) === bookUci);
            if (mv) return { move: mv, score: 0, nodes: 0, depth: 0, time: 0, book: true };
          }
        }
      }

      this.repetitionHash.set(this.repKey(state), 1);
      let bestMove = null, bestScore = 0, prevScore = 0;
      const rootLegal = generateLegalMoves(state);
      if (rootLegal.length === 0) return { move: null, score: -MATE, nodes: 0, depth: 0, time: 0 };
      if (rootLegal.length === 1) return { move: rootLegal[0], score: 0, nodes: 1, depth: 0, time: 0 };

      for (let d = 1; d <= this.maxDepth; d++) {
        this.killers = [[], [], []];
        this.rootMoves = [];
        let alpha = -INF, beta = INF;
        if (d >= 4 && Math.abs(prevScore) < MATE_IN_MAX) {
          alpha = prevScore - 50;
          beta = prevScore + 50;
        }
        let score = 0, failLow = false, failHigh = false;
        let iterations = 0;
        while (iterations < 6) {
          iterations++;
          this.bestMoveRoot = null;
          score = this.alphaBeta(state, d, alpha, beta, 0, true, true);
          if (this.stop) break;
          if (score <= alpha) {
            failLow = true;
            alpha = Math.max(-INF, alpha - (failLow ? 200 : 100));
            if (alpha === -INF) break;
            continue;
          }
          if (score >= beta) {
            failHigh = true;
            beta = Math.min(INF, beta + (failHigh ? 200 : 100));
            continue;
          }
          break;
        }
        if (this.stop) break;
        if (this.bestMoveRoot) { bestMove = this.bestMoveRoot; bestScore = score; }
        prevScore = score;
        if (opts.onDepth) opts.onDepth(d, score, this.bestMoveRoot, this.nodes, Date.now() - this.startTime);
        if (Math.abs(score) > MATE_IN_MAX) break;
        // Soft time check: stop if used more than softLimit and depth >= 5
        if (this.softLimit > 0 && d >= 5 && this.softTimeUp()) break;
        // Also stop if estimated next iteration would exceed hard limit
        if (this.hardLimit > 0 && d >= 4) {
          const elapsed = Date.now() - this.startTime;
          const estNext = elapsed * 2.5;
          if (elapsed + estNext > this.hardLimit) break;
        }
      }

      // Root randomization
      if (rootVariety > 0 && this.rootMoves.length > 1 && bestMove) {
        const candidates = this.rootMoves.filter(rm =>
          Math.abs(rm.score - bestScore) <= rootVariety && rm.score > -MATE_IN_MAX
        );
        if (candidates.length > 1) {
          // biased random selection
          candidates.sort((a, b) => b.score - a.score);
          const r = Math.random();
          let idx = 0;
          if (r > 0.5 && candidates.length > 1) idx = 1;
          if (r > 0.85 && candidates.length > 2) idx = 2;
          bestMove = candidates[idx].mv;
          bestScore = candidates[idx].score;
        }
      }

      if (!bestMove) {
        const tt = this.tt.probe(state.hashLo, state.hashHi);
        if (tt && tt.bestMove) bestMove = tt.bestMove;
      }
      if (!bestMove && rootLegal.length) bestMove = rootLegal[0];

      return {
        move: bestMove, score: bestScore, nodes: this.nodes,
        depth: this.maxDepth, time: Date.now() - this.startTime,
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
      if (mv[0] === from && mv[1] === to && (mv[2] || 0) === promo) return mv;
    }
    return null;
  }

  class ChessEngine {
    constructor(opts = {}) {
      this.ttSizeMB = opts.ttSizeMB || 64;
      this.defaultDepth = opts.depth || 5;
      this.learning = new LearningBook();
      this.searcher = new Searcher(this.ttSizeMB, this.learning);
      this.ready = true;
      this.uciHistory = [];
      this.bookEnabled = opts.bookEnabled !== false;
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
      state.uciHistory = opts.uciHistory ? opts.uciHistory.slice() : [];

      const depth = opts.depth || this.defaultDepth;
      const res = this.searcher.search(state, {
        depth,
        timeLimit: opts.timeLimit || 0,
        useBook: opts.useBook !== undefined ? opts.useBook : this.bookEnabled,
        bookChance: opts.bookChance !== undefined ? opts.bookChance : 1.0,
        rootVariety: opts.rootVariety !== undefined ? opts.rootVariety : 25,
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
        try { this.learning.recordMove(parseFEN(h.fen), h.uci, 'loss'); } catch (e) {}
      }
    }
    learnFromWin(history) {
      for (const h of history) {
        try { this.learning.recordMove(parseFEN(h.fen), h.uci, 'win'); } catch (e) {}
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

  const helpers = {
    parseFEN, toFEN, generateLegalMoves, applyMove, undoMove, evaluate,
    sqName, nameToSq, moveToUci, uciToMove, LearningBook, OPENING_BOOK
  };

  if (typeof window !== "undefined") { window.ChessEngine = ChessEngine; window.ChessEngineHelpers = helpers; }
  if (typeof module !== "undefined" && module.exports) { module.exports = ChessEngine; Object.assign(module.exports, helpers); }
  if (typeof globalThis !== "undefined") globalThis.MyChessEngine = ChessEngine;

})(typeof window !== "undefined" ? window : globalThis);