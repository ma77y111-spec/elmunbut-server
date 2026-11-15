'use strict';
/*
 * ElMunBut Five Crowns — multiplayer server.
 *
 * A single Node process that is the one authority for a Five Crowns game.
 * Clients connect over WebSockets, create/join rooms with a 4-letter code,
 * and only ever receive their own hand in full; everyone else's hand is a
 * card count. Bots (simple, server-side) can fill empty seats and take over
 * a seat when a player disconnects mid-game.
 *
 * Run:  npm start            (listens on process.env.PORT || 3000)
 * Test: npm test             (see test.js)
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const BOT_DELAY_MS = Number(process.env.BOT_DELAY_MS || 1100);
const BOT_DISCARD_DELAY_MS = Number(process.env.BOT_DISCARD_DELAY_MS || 900);
const ROUND_DELAY_MS = Number(process.env.ROUND_DELAY_MS || 3000);
const F7_FLIP_MS = Number(process.env.F7_FLIP_MS || 900); // pace of forced flips (Flip Three sequences)
const MAX_RESHUFFLES = 2; // backstop: after this many stock reshuffles a round is scored as-is

/* ------------------------------------------------------------------ */
/* Cards                                                               */
/* ------------------------------------------------------------------ */
const SUITS = ['stars', 'hearts', 'spades', 'clubs', 'diamonds'];
const RANK_LABEL = { 11: 'J', 12: 'Q', 13: 'K' };
const BOT_NAMES = ['Cockatoo', 'Sly Fox', 'Wombat', 'Kookaburra', 'Platypus'];

function createDeck() {
  const cards = [];
  let n = 0;
  // Five suits, ranks 3..King, two copies of each = 110 cards.
  for (let copy = 0; copy < 2; copy++) {
    for (const suit of SUITS) {
      for (let rank = 3; rank <= 13; rank++) {
        cards.push({ id: 'c' + (++n), suit, rank });
      }
    }
  }
  // Plus 6 jokers = 116 cards total.
  for (let i = 0; i < 6; i++) cards.push({ id: 'c' + (++n), suit: 'joker', rank: 0 });
  return cards;
}

function shuffle(cards) {
  const a = [...cards];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function isWild(card, wildRank) {
  return card.suit === 'joker' || card.rank === wildRank;
}

function deadwoodValue(card, wildRank) {
  if (card.suit === 'joker') return 50;
  if (card.rank === wildRank) return 20;
  return card.rank; // 3..10 face value, J=11, Q=12, K=13
}

function handScore(hand, wildRank) {
  return hand.reduce((sum, c) => sum + deadwoodValue(c, wildRank), 0);
}

/*
 * Round-end scoring (fixed 15 Nov 2026): a player is charged only for
 * DEADWOOD — cards that cannot be part of a complete book or run.
 * Completed sets left in hand (e.g. Matthew's 6,6,wild book) score 0.
 * Exact solver: enumerate every valid meld in the hand, then find the
 * disjoint set of melds covering the most points; the rest is deadwood.
 */
function bestDeadwood(hand, wildRank) {
  const n = hand.length;
  if (n === 0) return 0;
  const meldMasks = [];
  for (let mask = 0; mask < (1 << n); mask++) {
    let bits = 0;
    for (let m = mask; m; m >>= 1) bits += m & 1;
    if (bits < 3) continue;
    const cards = hand.filter((_, i) => mask & (1 << i));
    if (validateMeld(cards, wildRank).valid) meldMasks.push(mask);
  }
  const maskValue = mask =>
    hand.reduce((s, c, i) => (mask & (1 << i)) ? s + deadwoodValue(c, wildRank) : s, 0);
  const valued = meldMasks
    .map(mask => ({ mask, value: maskValue(mask) }))
    .sort((a, b) => b.value - a.value);
  let bestCovered = 0;
  const search = (idx, used, covered) => {
    if (covered > bestCovered) bestCovered = covered;
    for (let i = idx; i < valued.length; i++) {
      if (valued[i].mask & used) continue;
      search(i + 1, used | valued[i].mask, covered + valued[i].value);
    }
  };
  search(0, 0, 0);
  return handScore(hand, wildRank) - bestCovered;
}

/* ------------------------------------------------------------------ */
/* Meld rules                                                          */
/* ------------------------------------------------------------------ */
/*
 * Book: 3+ cards, every natural (non-wild) card the same rank.
 * Run:  3+ cards (Matthew's rule, 15 Nov 2026: "anything 3 cards and
 *       over"), every natural card the same suit, natural ranks all
 *       different, and the naturals plus wilds can form one sequence
 *       inside 3..King. A meld of nothing but wild cards also counts
 *       (Matthew, 15 Nov 2026: "I can't see why 3 wilds can't be a
 *       hand") — wilds stand for anything, including a full set.
 */
function validateMeld(cards, wildRank) {
  if (!Array.isArray(cards) || cards.length < 3) return { valid: false };
  const nats = cards.filter(c => !isWild(c, wildRank));
  if (nats.length === 0) return { valid: true, type: 'book' };
  if (nats.every(c => c.rank === nats[0].rank)) return { valid: true, type: 'book' };
  if (nats.every(c => c.suit === nats[0].suit)) {
    const ranks = nats.map(c => c.rank);
    if (new Set(ranks).size === ranks.length) {
      const n = cards.length;
      const min = Math.min(...ranks), max = Math.max(...ranks);
      // A start position a works if a <= min, max <= a+n-1, 3 <= a, a+n-1 <= 13.
      const lo = Math.max(3, max - n + 1);
      const hi = Math.min(min, 13 - n + 1);
      if (lo <= hi) return { valid: true, type: 'run' };
    }
  }
  return { valid: false };
}

/* ------------------------------------------------------------------ */
/* Simple playing strategy — shared by server bots and the test client */
/* ------------------------------------------------------------------ */
/* Greedily pull melds out of a hand. Returns an array of melds (card arrays). */
function findMelds(hand, wildRank) {
  const melds = [];
  let pool = [...hand];
  const wildsInPool = () => pool.filter(c => isWild(c, wildRank));
  const take = cards => {
    melds.push(cards);
    const ids = new Set(cards.map(c => c.id));
    pool = pool.filter(c => !ids.has(c.id));
  };

  // Books first: 3+ naturals, or a pair plus one wild.
  const byRank = new Map();
  for (const c of pool.filter(c => !isWild(c, wildRank))) {
    if (!byRank.has(c.rank)) byRank.set(c.rank, []);
    byRank.get(c.rank).push(c);
  }
  const groups = [...byRank.values()].sort((a, b) => b.length - a.length);
  for (const g of groups) {
    if (!g.every(c => pool.includes(c))) continue;
    if (g.length >= 3) take([...g]);
    else if (g.length === 2 && wildsInPool().length >= 1) take([...g, wildsInPool()[0]]);
  }

  // Runs: per suit, walk the sorted naturals and fill gaps with wilds.
  const bySuit = new Map();
  for (const c of pool.filter(c => !isWild(c, wildRank))) {
    if (!bySuit.has(c.suit)) bySuit.set(c.suit, []);
    bySuit.get(c.suit).push(c);
  }
  for (const list of bySuit.values()) {
    let rem = [...list].sort((a, b) => a.rank - b.rank);
    let i = 0;
    while (i < rem.length) {
      const seq = [rem[i]];
      let gaps = 0, last = rem[i].rank, j = i + 1;
      while (j < rem.length) {
        const gap = rem[j].rank - last - 1;
        if (gap < 0) { j++; continue; } // duplicate rank can't join a run
        if (gaps + gap > wildsInPool().length) break;
        gaps += gap; seq.push(rem[j]); last = rem[j].rank; j++;
      }
      const extra = Math.max(0, 3 - (seq.length + gaps));
      const need = gaps + extra;
      const totalLen = seq.length + gaps + extra;
      const lo = Math.max(3, seq[seq.length - 1].rank - totalLen + 1);
      const hi = Math.min(seq[0].rank, 13 - totalLen + 1);
      if (totalLen >= 3 && need <= wildsInPool().length && lo <= hi) {
        take([...seq, ...wildsInPool().slice(0, need)]);
        const used = new Set(seq.map(c => c.id));
        rem = rem.filter(c => !used.has(c.id));
        i = 0;
      } else {
        i++;
      }
    }
  }

  // Leftover wilds: 3+ of them on their own are a valid meld too.
  while (wildsInPool().length >= 3) take(wildsInPool().slice(0, 3));
  return melds;
}

/* Can this hand be fully melded (optionally discarding one card)? */
function tryOut(hand, wildRank) {
  const all = findMelds(hand, wildRank);
  if (all.flat().length === hand.length && hand.length > 0) return { melds: all, discard: null };
  for (const c of hand) {
    const rest = hand.filter(x => x.id !== c.id);
    const m = findMelds(rest, wildRank);
    if (m.flat().length === rest.length) return { melds: m, discard: c };
  }
  return null;
}

/* Pick a discard: shed the highest-value card that isn't wild, part of a
 * pair, or sitting next to a same-suit neighbour, if we can. */
function chooseDiscard(hand, wildRank) {
  if (!hand.length) return null;
  const nats = hand.filter(c => !isWild(c, wildRank));
  const pool = nats.length ? nats : hand;
  const rankCount = new Map();
  for (const c of nats) rankCount.set(c.rank, (rankCount.get(c.rank) || 0) + 1);
  const connected = c => nats.some(o => o.id !== c.id && o.suit === c.suit && Math.abs(o.rank - c.rank) <= 2);
  const score = c =>
    (rankCount.get(c.rank) > 1 ? 0 : 2) + (connected(c) ? 0 : 1); // higher = safer to shed
  return [...pool].sort((a, b) =>
    score(b) - score(a) || deadwoodValue(b, wildRank) - deadwoodValue(a, wildRank)
  )[0];
}

function chooseDrawSource(room, player) {
  const top = room.discard[room.discard.length - 1];
  if (!top) return 'stock';
  if (isWild(top, room.wildRank)) return 'discard';
  const nats = player.hand.filter(c => !isWild(c, room.wildRank));
  if (nats.some(c => c.rank === top.rank)) return 'discard';
  if (nats.some(c => c.suit === top.suit && Math.abs(c.rank - top.rank) <= 2)) return 'discard';
  return 'stock';
}

/* ------------------------------------------------------------------ */
/* Rooms and game state                                                */
/* ------------------------------------------------------------------ */
const rooms = new Map();
let playerSeq = 0;

function makeCode() {
  const letters = 'ABCDEFGHJKMNPQRSTUVWXYZ';
  let code;
  do {
    code = Array.from({ length: 4 }, () => letters[Math.floor(Math.random() * letters.length)]).join('');
  } while (rooms.has(code));
  return code;
}

function makePlayer(name, isBot) {
  return {
    id: 'p' + (++playerSeq) + Math.random().toString(36).slice(2, 7),
    name, isBot: !!isBot, connected: false, ws: null,
    hand: [], groups: [], totalScore: 0,
    // Flip 7 per-round state (unused in Five Crowns rooms).
    line: [], status: 'in', banked: 0, roundGained: 0,
  };
}

function currentPlayer(room) {
  return room.players.find(p => p.id === room.currentPlayerId) || null;
}

function stateFor(room, viewer) {
  if (room.game === 'flip7') return f7StateFor(room, viewer);
  return {
    type: 'state',
    game: 'fivecrowns',
    version: room.version,
    code: room.code,
    phase: room.phase, // lobby | playing | round_end | game_end
    round: room.round,
    wildRank: room.wildRank,
    wildLabel: room.wildRank ? (RANK_LABEL[room.wildRank] || String(room.wildRank)) : null,
    turnPhase: room.turnPhase, // draw | play
    turnCount: room.turnCount,
    currentPlayerId: room.currentPlayerId,
    outPlayerId: room.outPlayerId,
    stockCount: room.stock.length,
    discardTop: room.discard.length ? room.discard[room.discard.length - 1] : null,
    you: viewer ? { id: viewer.id, hand: viewer.hand, groups: viewer.groups } : null,
    players: room.players.map(p => ({
      id: p.id,
      name: p.name,
      isBot: p.isBot,
      connected: p.isBot ? true : p.connected,
      isHost: p.id === room.hostId,
      isCurrent: p.id === room.currentPlayerId,
      handCount: p.hand.length, // counts only while the round is in play
      groups: p.groups, // empty until that player goes out — then revealed
      // Hands stay hidden until the round is over; at round_end / game_end
      // every player's remaining cards are revealed for the results.
      hand: (room.phase === 'round_end' || room.phase === 'game_end') ? p.hand : undefined,
      totalScore: p.totalScore,
    })),
    lastRoundResult: room.lastRoundResult,
    winners: room.winners,
    lastEvent: room.lastEvent,
  };
}

function send(ws, obj) {
  if (ws && ws.readyState === 1) ws.send(JSON.stringify(obj));
}

function broadcast(room) {
  room.version++;
  for (const p of room.players) {
    if (!p.isBot && p.ws) send(p.ws, stateFor(room, p));
  }
}

function broadcastEvent(room, event, data) {
  for (const p of room.players) {
    if (!p.isBot && p.ws) send(p.ws, { type: 'event', event, data });
  }
}

/* ------------------------------------------------------------------ */
/* Turn flow                                                           */
/* ------------------------------------------------------------------ */
function setTurn(room, playerId) {
  room.currentPlayerId = playerId;
  room.turnPhase = 'draw';
  room.turnCount++;
  broadcast(room);
  scheduleBot(room);
}

function endTurn(room, player, wentOut) {
  if (wentOut && !room.outPlayerId) {
    room.outPlayerId = player.id;
    room.lastEvent = player.name + ' went out';
    broadcastEvent(room, 'went_out', { playerId: player.id, name: player.name });
    const idx = room.players.indexOf(player);
    room.finalPending = [];
    for (let k = 1; k < room.players.length; k++) {
      room.finalPending.push(room.players[(idx + k) % room.players.length].id);
    }
  }
  if (room.finalPending) {
    // Final turns: every other player gets exactly one more turn.
    if (room.finalPending.length === 0) { scoreRound(room); return; }
    setTurn(room, room.finalPending.shift());
    return;
  }
  const idx = room.players.indexOf(player);
  setTurn(room, room.players[(idx + 1) % room.players.length].id);
}

function scoreRound(room) {
  room.phase = 'round_end';
  room.finalPending = null;
  const results = room.players.map(p => {
    const deadwood = bestDeadwood(p.hand, room.wildRank);
    p.totalScore += deadwood;
    return { playerId: p.id, name: p.name, deadwood, total: p.totalScore };
  });
  room.lastRoundResult = { round: room.round, outPlayerId: room.outPlayerId, results };
  room.lastEvent = 'Round ' + room.round + ' scored';
  broadcastEvent(room, 'round_scored', room.lastRoundResult);
  broadcast(room);
  setTimeout(() => {
    if (room.phase !== 'round_end') return;
    if (room.round >= 11) {
      room.phase = 'game_end';
      const best = Math.min(...room.players.map(p => p.totalScore));
      room.winners = room.players.filter(p => p.totalScore === best).map(p => p.id);
      room.lastEvent = 'Game over';
      broadcastEvent(room, 'game_over', {
        winners: room.winners,
        standings: room.players.map(p => ({ playerId: p.id, name: p.name, total: p.totalScore })),
      });
      broadcast(room);
    } else {
      room.round++;
      startRound(room);
    }
  }, ROUND_DELAY_MS);
}

function startRound(room) {
  const deck = shuffle(createDeck());
  const handSize = room.round + 2; // round 1 = 3 cards ... round 11 = 13 cards
  room.wildRank = room.round + 2;  // round 1: 3s wild ... round 11: Kings wild
  for (const p of room.players) { p.hand = []; p.groups = []; }
  for (let i = 0; i < handSize; i++) {
    for (const p of room.players) p.hand.push(deck.pop());
  }
  room.stock = deck;
  room.discard = [room.stock.pop()];
  room.outPlayerId = null;
  room.finalPending = null;
  room.reshuffles = 0;
  room.phase = 'playing';
  room.lastEvent = 'Round ' + room.round + ' dealt — ' + (RANK_LABEL[room.wildRank] || room.wildRank) + 's are wild';
  const first = room.players[(room.round - 1) % room.players.length];
  room.currentPlayerId = first.id;
  room.turnPhase = 'draw';
  room.turnCount++;
  broadcast(room);
  scheduleBot(room);
}

/* ------------------------------------------------------------------ */
/* Actions — every move is validated here; clients never self-report   */
/* ------------------------------------------------------------------ */
function doDraw(room, player, source) {
  if (room.phase !== 'playing') return 'game is not in play';
  if (currentPlayer(room) !== player) return 'not your turn';
  if (room.turnPhase !== 'draw') return 'you have already drawn';
  if (source === 'discard') {
    if (!room.discard.length) return 'discard pile is empty';
    player.hand.push(room.discard.pop());
  } else {
    if (!room.stock.length) {
      if (room.reshuffles >= MAX_RESHUFFLES || room.discard.length <= 1) {
        scoreRound(room); // backstop so a round always terminates
        return null;
      }
      const top = room.discard.pop();
      room.stock = shuffle(room.discard);
      room.discard = [top];
      room.reshuffles++;
    }
    player.hand.push(room.stock.pop());
  }
  room.turnPhase = 'play';
  broadcast(room);
  return null;
}

/* Going out is the ONLY way cards leave a hand face-up: every card except
 * the final discard must sit in a valid book or run. Groups are staged
 * privately in the client during the round and are only revealed here.
 * `groups` may be omitted, in which case the server partitions the hand
 * itself (used by the plain test page and as a fallback). */
function doGoOut(room, player, groupIds, discardId) {
  if (room.phase !== 'playing') return 'game is not in play';
  if (currentPlayer(room) !== player) return 'not your turn';
  if (room.turnPhase !== 'play') return 'draw a card first';
  const discard = player.hand.find(c => c.id === discardId);
  if (!discard) return 'choose a card to discard';
  let groups;
  if (Array.isArray(groupIds) && groupIds.length) {
    const seen = new Set();
    groups = [];
    for (const g of groupIds) {
      if (!Array.isArray(g) || !g.length) return 'a group is empty';
      const cards = g.map(id => player.hand.find(c => c.id === id));
      if (cards.some(c => !c)) return 'a grouped card is not in your hand';
      for (const c of cards) {
        if (seen.has(c.id) || c.id === discardId) return 'a card is used twice';
        seen.add(c.id);
      }
      const check = validateMeld(cards, room.wildRank);
      if (!check.valid) return 'every group must be a valid book (3+ of a rank) or run (3+ of a suit in sequence)';
      groups.push(cards);
    }
    if (seen.size !== player.hand.length - 1) return 'all cards except your discard must be in groups to go out';
  } else {
    const rest = player.hand.filter(c => c.id !== discardId);
    const out = tryOut(rest, room.wildRank);
    if (!out || out.discard) return 'you cannot go out yet — not all your cards form books or runs';
    groups = out.melds;
  }
  player.groups = groups;
  player.hand = [];
  room.discard.push(discard);
  room.lastEvent = player.name + ' went out';
  broadcast(room);
  endTurn(room, player, true);
  return null;
}

function doDiscard(room, player, cardId) {
  if (room.phase !== 'playing') return 'game is not in play';
  if (currentPlayer(room) !== player) return 'not your turn';
  if (room.turnPhase !== 'play') return 'draw a card first';
  const idx = player.hand.findIndex(c => c.id === cardId);
  if (idx === -1) return 'that card is not in your hand';
  const [card] = player.hand.splice(idx, 1);
  room.discard.push(card);
  room.lastEvent = player.name + ' discarded';
  const wentOut = player.hand.length === 0;
  broadcast(room);
  endTurn(room, player, wentOut);
  return null;
}

/* ------------------------------------------------------------------ */
/* Bots                                                                */
/* ------------------------------------------------------------------ */
function scheduleBot(room) {
  if (room.game !== 'fivecrowns') return;
  if (room.phase !== 'playing' || room.botScheduled) return;
  const p = currentPlayer(room);
  if (!p || !p.isBot) return;
  room.botScheduled = true;
  setTimeout(() => {
    room.botScheduled = false;
    if (room.phase !== 'playing' || currentPlayer(room) !== p) return;
    botDrawStep(room, p);
  }, BOT_DELAY_MS);
}

/* Bot turns run in two beats so the table can follow them (Matthew,
 * 15 Nov 2026: bots were "operating instantly"): draw first, pause,
 * then discard or go out. */
function botDrawStep(room, player) {
  if (room.turnPhase === 'draw') {
    doDraw(room, player, chooseDrawSource(room, player));
    if (room.phase !== 'playing' || currentPlayer(room) !== player) return;
  }
  if (room.phase !== 'playing' || currentPlayer(room) !== player || room.turnPhase !== 'play') return;
  room.botScheduled = true;
  setTimeout(() => {
    room.botScheduled = false;
    if (room.phase !== 'playing' || currentPlayer(room) !== player) return;
    botPlayStep(room, player);
  }, BOT_DISCARD_DELAY_MS);
}

function botPlayStep(room, player) {
  const out = tryOut(player.hand, room.wildRank);
  if (out) {
    if (out.discard) {
      doGoOut(room, player, out.melds.map(m => m.map(c => c.id)), out.discard.id);
    } else {
      // Whole hand melds with nothing spare: discard one card and let the
      // server partition the rest; fall back to a plain discard if that fails.
      const d = chooseDiscard(player.hand, room.wildRank);
      if (d && doGoOut(room, player, null, d.id) && room.phase === 'playing' &&
          currentPlayer(room) === player && room.turnPhase === 'play') {
        doDiscard(room, player, d.id);
      }
    }
    return;
  }
  if (room.phase === 'playing' && currentPlayer(room) === player && room.turnPhase === 'play' && player.hand.length) {
    const d = chooseDiscard(player.hand, room.wildRank);
    if (d) doDiscard(room, player, d.id);
  }
}

/* ------------------------------------------------------------------ */
/* Flip 7                                                              */
/*                                                                     */
/* Same room/lobby shell as Five Crowns, different game. All flipped   */
/* cards are public. On your turn you flip ONE card or stay and bank;  */
/* play then passes. A duplicate number busts (a held Second Chance    */
/* saves you once — on a normal turn play simply passes; inside a      */
/* Flip Three the sequence carries on). Freeze banks a player at       */
/* their current score; Flip Three forces three flips; flipping 7      */
/* unique numbers scores +15 and ends the round for everyone. First    */
/* to 200 at the end of a round wins. Deck: 94 cards — numbers 0–12    */
/* (copies equal to face value, plus a single 0), modifiers +2/+4/+6/  */
/* +8/+10 and ×2 (one each), actions Freeze/Flip Three/Second Chance   */
/* (three each) — mirroring the games app.                             */
/* ------------------------------------------------------------------ */
let f7Seq = 0;

function f7CreateDeck() {
  const cards = [];
  const add = (c) => cards.push(Object.assign({ id: 'f' + (++f7Seq) }, c));
  for (let v = 1; v <= 12; v++) for (let i = 0; i < v; i++) add({ kind: 'number', value: v });
  add({ kind: 'number', value: 0 });
  for (const m of [2, 4, 6, 8, 10]) add({ kind: 'modifier', value: m, mod: 'plus' });
  add({ kind: 'modifier', value: 2, mod: 'times' });
  for (let i = 0; i < 3; i++) add({ kind: 'action', action: 'freeze' });
  for (let i = 0; i < 3; i++) add({ kind: 'action', action: 'flip3' });
  for (let i = 0; i < 3; i++) add({ kind: 'action', action: 'second' });
  return cards;
}

function f7UniqueCount(p) {
  return new Set(p.line.filter(c => c.kind === 'number').map(c => c.value)).size;
}
function f7HasSecond(p) {
  return p.line.some(c => c.kind === 'action' && c.action === 'second');
}
function f7LineScore(p) {
  let sum = 0, plus = 0, times = false;
  for (const c of p.line) {
    if (c.bust) continue; // the card that busted (or was saved): visible, scores nothing
    if (c.kind === 'number') sum += c.value;
    else if (c.kind === 'modifier') { if (c.mod === 'times') times = true; else plus += c.value; }
  }
  return (times ? sum * 2 : sum) + plus;
}
function f7Worth(p) {
  if (p.status === 'busted') return 0;
  if (p.status === 'in') return f7LineScore(p);
  return p.banked; // banked / frozen: locked-in amount
}

function f7StateFor(room, viewer) {
  return {
    type: 'state',
    game: 'flip7',
    version: room.version,
    code: room.code,
    phase: room.phase, // lobby | playing | round_end | game_end
    round: room.round,
    currentPlayerId: room.currentPlayerId,
    deckCount: room.stock.length,
    flipping: room.f7seq.length > 0, // a Flip Three sequence is mid-flight
    pendingAction: room.pendingAction ? { kind: room.pendingAction.kind, byId: room.pendingAction.byId } : null,
    you: viewer ? { id: viewer.id } : null,
    players: room.players.map(p => ({
      id: p.id,
      name: p.name,
      isBot: p.isBot,
      connected: p.isBot ? true : p.connected,
      isHost: p.id === room.hostId,
      isCurrent: p.id === room.currentPlayerId,
      totalScore: p.totalScore,
      status: p.status, // in | banked | busted | frozen
      line: p.line, // every flipped card is public in Flip 7
      uniqueCount: f7UniqueCount(p),
      lineScore: f7Worth(p),
      hasSecondChance: f7HasSecond(p),
      roundGained: p.roundGained || 0,
    })),
    lastRoundResult: room.lastRoundResult,
    winners: room.winners,
    lastEvent: room.lastEvent,
  };
}

function f7StartRound(room) {
  room.stock = shuffle(f7CreateDeck());
  room.f7discard = [];
  room.f7seq = [];
  room.pendingAction = null;
  room.pendingCard = null;
  room.f7Stage = 'decide';
  room.flip7PlayerId = null;
  for (const p of room.players) {
    p.line = [];
    p.status = 'in';
    p.banked = 0;
    p.roundGained = 0;
  }
  // No opening deal — matching the offline game, your first turn is your
  // first flip. Everyone starts the round with an empty line.
  room.phase = 'playing';
  const starter = room.players[(room.round - 1) % room.players.length];
  room.currentPlayerId = starter.id;
  room.lastEvent = 'Round ' + room.round + ' dealt — ' + starter.name + ' to play';
  broadcast(room);
  f7Continue(room);
}

function f7Draw(room) {
  if (!room.stock.length) {
    if (!room.f7discard.length) return null;
    room.stock = shuffle(room.f7discard);
    room.f7discard = [];
  }
  return room.stock.pop();
}

/* One driver for everything that happens next, so turn flips, Flip Three
 * sequences, target prompts and bots can never fight over the flow. */
function f7Continue(room) {
  if (room.phase !== 'playing') return;
  if (room.pendingAction) {
    const by = room.players.find(p => p.id === room.pendingAction.byId);
    if (by && by.isBot) f7Schedule(room, BOT_DISCARD_DELAY_MS, () => f7BotTarget(room));
    return;
  }
  if (room.f7seq.length) {
    f7Schedule(room, F7_FLIP_MS, () => f7SeqStep(room));
    return;
  }
  if (room.f7Stage === 'resolving') { f7Advance(room); return; }
  const p = currentPlayer(room);
  if (!p || p.status !== 'in') { f7Advance(room); return; }
  if (p.isBot) f7Schedule(room, BOT_DELAY_MS, () => f7BotDecision(room));
}

function f7Schedule(room, delay, fn) {
  if (room.f7Scheduled) return;
  room.f7Scheduled = true;
  setTimeout(() => {
    room.f7Scheduled = false;
    if (room.phase !== 'playing') return;
    fn();
  }, delay);
}

function f7Advance(room) {
  const n = room.players.length;
  const cur = room.players.findIndex(p => p.id === room.currentPlayerId);
  for (let step = 1; step <= n; step++) {
    const cand = room.players[(cur + step) % n];
    if (cand.status === 'in') {
      room.currentPlayerId = cand.id;
      room.f7Stage = 'decide';
      room.lastEvent = cand.name + ' to play';
      broadcast(room);
      f7Continue(room);
      return;
    }
  }
  f7ScoreRound(room);
}

function f7DoHit(room, player) {
  if (room.phase !== 'playing') return 'the game is not in play';
  if (room.pendingAction) return 'choose a target first';
  if (room.f7seq.length) return 'cards are still flipping';
  if (currentPlayer(room) !== player) return 'not your turn';
  if (room.f7Stage !== 'decide') return 'you have already flipped';
  if (player.status !== 'in') return 'you are out of this round';
  room.f7Stage = 'resolving';
  const card = f7Draw(room);
  if (!card) { f7ScoreRound(room); return null; }
  f7ResolveDrawn(room, player, card);
  broadcast(room);
  f7Continue(room);
  return null;
}

function f7DoStay(room, player) {
  if (room.phase !== 'playing') return 'the game is not in play';
  if (room.pendingAction) return 'choose a target first';
  if (room.f7seq.length) return 'cards are still flipping';
  if (currentPlayer(room) !== player) return 'not your turn';
  if (room.f7Stage !== 'decide') return 'you have already flipped';
  if (player.status !== 'in') return 'you are out of this round';
  player.banked = f7LineScore(player);
  player.status = 'banked';
  room.lastEvent = player.name + ' stayed and banked ' + player.banked;
  broadcast(room);
  f7Advance(room);
  return null;
}

/* Resolve a freshly flipped card for `player`. May set a pending target
 * prompt (Freeze / Flip Three / a second Second Chance to give away),
 * bust the player, or end the round (Flip 7). */
function f7ResolveDrawn(room, player, card) {
  if (card.kind === 'number') {
    const dup = player.line.some(c => c.kind === 'number' && !c.bust && c.value === card.value);
    if (dup) {
      // The drawn card stays in the line, flagged, so the player can SEE
      // what they drew — it scores nothing either way.
      card.bust = true;
      player.line.push(card);
      if (f7HasSecond(player)) {
        player.line = player.line.filter(c => !(c.kind === 'action' && c.action === 'second'));
        room.lastEvent = player.name + ' flipped a duplicate ' + card.value + ' — Second Chance saved them';
        return;
      }
      player.status = 'busted';
      room.lastEvent = player.name + ' flipped a duplicate ' + card.value + ' and busted';
      return;
    }
    player.line.push(card);
    room.lastEvent = player.name + ' flipped ' + card.value;
    if (f7UniqueCount(player) >= 7) {
      player.banked = f7LineScore(player) + 15;
      player.status = 'banked';
      room.flip7PlayerId = player.id;
      for (const p of room.players) {
        if (p.status === 'in') { p.banked = f7LineScore(p); p.status = 'banked'; }
      }
      room.lastEvent = player.name + ' flipped 7 unique numbers — Flip 7! +15';
      f7ScoreRound(room);
    }
    return;
  }
  if (card.kind === 'modifier') {
    player.line.push(card);
    room.lastEvent = player.name + ' flipped ' + (card.mod === 'times' ? '×2' : '+' + card.value);
    return;
  }
  // Action cards.
  if (card.action === 'second') {
    if (!f7HasSecond(player)) {
      player.line.push(card);
      room.lastEvent = player.name + ' picked up a Second Chance';
      return;
    }
    // Already holding one: it must be given to another player still in
    // the round who hasn't got one — or discarded if there is nobody.
    const takers = room.players.filter(p => p !== player && p.status === 'in' && !f7HasSecond(p));
    if (!takers.length) {
      room.f7discard.push(card);
      room.lastEvent = player.name + ' flipped a Second Chance but already had one';
      return;
    }
    room.pendingAction = { kind: 'gift', byId: player.id };
    room.pendingCard = card;
    room.lastEvent = player.name + ' must give away a Second Chance';
    return;
  }
  room.pendingAction = { kind: card.action, byId: player.id }; // freeze | flip3
  room.pendingCard = card;
  room.lastEvent = player.name + ' flipped ' + (card.action === 'freeze' ? 'Freeze — choose who banks now' : 'Flip Three — choose who flips 3');
}

function f7ApplyTarget(room, player, targetId) {
  if (room.phase !== 'playing') return 'the game is not in play';
  if (!room.pendingAction) return 'nothing needs a target';
  if (room.pendingAction.byId !== player.id) return 'someone else is choosing a target';
  const target = room.players.find(p => p.id === targetId);
  if (!target) return 'choose a player';
  const kind = room.pendingAction.kind;
  const card = room.pendingCard;
  if (kind === 'gift') {
    if (target === player || target.status !== 'in' || f7HasSecond(target)) {
      return 'choose a player still in the round without a Second Chance';
    }
    target.line.push(card);
    room.lastEvent = player.name + ' gave a Second Chance to ' + target.name;
  } else {
    if (target.status !== 'in') return 'choose a player still in the round';
    room.f7discard.push(card);
    if (kind === 'freeze') {
      target.banked = f7LineScore(target);
      target.status = 'frozen';
      room.f7seq = room.f7seq.filter(s => s.playerId !== target.id);
      room.lastEvent = target.name + ' was frozen and banked ' + target.banked;
    } else { // flip3
      room.f7seq.push({ playerId: target.id, left: 3 });
      room.lastEvent = target.name + ' must flip three';
    }
  }
  room.pendingAction = null;
  room.pendingCard = null;
  broadcast(room);
  f7Continue(room);
  return null;
}

function f7SeqStep(room) {
  const top = room.f7seq[room.f7seq.length - 1];
  if (!top) { f7Continue(room); return; }
  const p = room.players.find(x => x.id === top.playerId);
  if (!p || p.status !== 'in') {
    room.f7seq = room.f7seq.filter(s => s !== top);
    f7Continue(room);
    return;
  }
  const card = f7Draw(room);
  if (!card) { f7ScoreRound(room); return; }
  top.left--;
  f7ResolveDrawn(room, p, card);
  if (room.phase !== 'playing') return; // Flip 7 ended the round mid-sequence
  if (p.status !== 'in') room.f7seq = room.f7seq.filter(s => s.playerId !== p.id);
  else if (top.left <= 0) room.f7seq = room.f7seq.filter(s => s !== top);
  broadcast(room);
  f7Continue(room);
}

function f7ScoreRound(room) {
  room.phase = 'round_end';
  room.f7seq = [];
  room.pendingAction = null;
  room.pendingCard = null;
  const results = room.players.map(p => {
    const gained = p.status === 'busted' ? 0
      : p.status === 'in' ? f7LineScore(p) : p.banked;
    p.roundGained = gained;
    p.totalScore += gained;
    if (p.status === 'in') { p.banked = gained; p.status = 'banked'; }
    return { playerId: p.id, name: p.name, gained, total: p.totalScore, status: p.status };
  });
  room.lastRoundResult = { round: room.round, flip7PlayerId: room.flip7PlayerId, results };
  broadcastEvent(room, 'round_scored', room.lastRoundResult);
  broadcast(room);
  setTimeout(() => {
    if (room.phase !== 'round_end') return;
    const top = Math.max(...room.players.map(p => p.totalScore));
    if (top >= 200) {
      room.phase = 'game_end';
      room.winners = room.players.filter(p => p.totalScore === top).map(p => p.id);
      room.lastEvent = 'Game over';
      broadcastEvent(room, 'game_over', { winners: room.winners });
      broadcast(room);
    } else {
      room.round++;
      f7StartRound(room);
    }
  }, ROUND_DELAY_MS);
}

/* Flip 7 bots: flip while the score is small or the line is short; stay
 * once the points are worth banking. Freeze the biggest threat, Flip
 * Three onto whoever is closest to busting (or themselves early). */
function f7BotDecision(room) {
  const p = currentPlayer(room);
  if (!p || !p.isBot || p.status !== 'in' || room.f7Stage !== 'decide') return;
  if (room.pendingAction || room.f7seq.length) return;
  const score = f7LineScore(p);
  const uniques = f7UniqueCount(p);
  const stay = score >= 24 || uniques >= 5 || (score >= 16 && uniques >= 4);
  if (stay) f7DoStay(room, p);
  else f7DoHit(room, p);
}

function f7BotTarget(room) {
  const pending = room.pendingAction;
  if (!pending) return;
  const bot = room.players.find(p => p.id === pending.byId);
  if (!bot || !bot.isBot) return;
  let target = null;
  if (pending.kind === 'freeze') {
    const inPlay = room.players.filter(p => p.status === 'in');
    target = inPlay.sort((a, b) => f7LineScore(b) - f7LineScore(a))[0];
  } else if (pending.kind === 'flip3') {
    if (f7UniqueCount(bot) <= 1) target = bot;
    else {
      const others = room.players.filter(p => p !== bot && p.status === 'in');
      target = others.length
        ? others.sort((a, b) => f7UniqueCount(b) - f7UniqueCount(a))[0]
        : bot;
    }
  } else if (pending.kind === 'gift') {
    const takers = room.players.filter(p => p !== bot && p.status === 'in' && !f7HasSecond(p));
    target = takers.sort((a, b) => f7LineScore(a) - f7LineScore(b))[0];
  }
  if (target) f7ApplyTarget(room, bot, target.id);
}

/* ------------------------------------------------------------------ */
/* HTTP + WebSocket server                                             */
/* ------------------------------------------------------------------ */
function startServer(port) {
  const server = http.createServer((req, res) => {
    if (req.url === '/healthz') { res.writeHead(200); res.end('ok'); return; }
    if (req.url === '/' || req.url === '/index.html') {
      const file = path.join(__dirname, 'public', 'index.html');
      fs.readFile(file, (err, data) => {
        if (err) { res.writeHead(500); res.end('test page missing'); return; }
        res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
        res.end(data);
      });
      return;
    }
    res.writeHead(404); res.end('not found');
  });

  const wss = new WebSocketServer({ server });

  wss.on('connection', ws => {
    let me = null;   // player object
    let room = null; // room object

    ws.on('message', raw => {
      let msg;
      try { msg = JSON.parse(raw.toString()); } catch { return; }
      const fail = text => send(ws, { type: 'error', message: text });

      switch (msg.type) {
        case 'create_room': {
          if (me) return fail('you are already in a room');
          const name = String(msg.name || '').trim().slice(0, 24);
          if (!name) return fail('a display name is required');
          room = {
            code: makeCode(), hostId: null, players: [], phase: 'lobby',
            game: msg.game === 'flip7' ? 'flip7' : 'fivecrowns',
            round: 1, wildRank: null, stock: [], discard: [],
            currentPlayerId: null, turnPhase: 'draw', turnCount: 0,
            outPlayerId: null, finalPending: null, reshuffles: 0,
            lastRoundResult: null, winners: null, lastEvent: 'Room created',
            version: 0, botScheduled: false,
            // Flip 7 state (unused in Five Crowns rooms). The flip deck
            // lives in room.stock; f7discard is its reshuffle pile.
            f7seq: [], pendingAction: null, pendingCard: null,
            f7Stage: 'decide', f7Scheduled: false, flip7PlayerId: null,
            f7discard: [],
          };
          me = makePlayer(name, false);
          me.ws = ws; me.connected = true;
          room.hostId = me.id;
          room.players.push(me);
          rooms.set(room.code, room);
          send(ws, { type: 'room_joined', code: room.code, playerId: me.id });
          broadcast(room);
          break;
        }
        case 'join_room': {
          if (me) return fail('you are already in a room');
          const name = String(msg.name || '').trim().slice(0, 24);
          if (!name) return fail('a display name is required');
          const target = rooms.get(String(msg.code || '').trim().toUpperCase());
          if (!target) return fail('no room with that code');
          if (target.phase !== 'lobby') return fail('that game has already started');
          if (target.players.length >= 6) return fail('that room is full');
          room = target;
          me = makePlayer(name, false);
          me.ws = ws; me.connected = true;
          room.players.push(me);
          room.lastEvent = name + ' joined';
          send(ws, { type: 'room_joined', code: room.code, playerId: me.id });
          broadcast(room);
          break;
        }
        case 'add_bot': {
          if (!room || !me) return fail('join a room first');
          if (room.hostId !== me.id) return fail('only the host can add bots');
          if (room.phase !== 'lobby') return fail('the game has started');
          if (room.players.length >= 6) return fail('the room is full');
          const used = new Set(room.players.map(p => p.name));
          const botName = BOT_NAMES.find(n => !used.has(n)) || 'Bot ' + (room.players.length + 1);
          room.players.push(makePlayer(botName, true));
          room.lastEvent = botName + ' (bot) added';
          broadcast(room);
          break;
        }
        case 'start_game': {
          if (!room || !me) return fail('join a room first');
          if (room.hostId !== me.id) return fail('only the host can start the game');
          if (room.phase !== 'lobby' && room.phase !== 'game_end') return fail('the game is already running');
          if (msg.fillWithBots) {
            while (room.players.length < 6) {
              const used = new Set(room.players.map(p => p.name));
              const botName = BOT_NAMES.find(n => !used.has(n)) || 'Bot ' + (room.players.length + 1);
              room.players.push(makePlayer(botName, true));
            }
          }
          if (room.players.length < 2) return fail('need at least 2 seats filled to start');
          for (const p of room.players) p.totalScore = 0;
          room.round = 1;
          room.lastRoundResult = null;
          room.winners = null;
          if (room.game === 'flip7') f7StartRound(room);
          else startRound(room);
          break;
        }
        case 'draw': {
          if (!room || !me) return fail('join a room first');
          if (room.game !== 'fivecrowns') return fail('that move is for Five Crowns');
          const err = doDraw(room, me, msg.source === 'discard' ? 'discard' : 'stock');
          if (err) fail(err);
          break;
        }
        case 'go_out': {
          if (!room || !me) return fail('join a room first');
          if (room.game !== 'fivecrowns') return fail('that move is for Five Crowns');
          const err = doGoOut(room, me, msg.groups, msg.discardId);
          if (err) fail(err);
          break;
        }
        case 'discard': {
          if (!room || !me) return fail('join a room first');
          if (room.game !== 'fivecrowns') return fail('that move is for Five Crowns');
          const err = doDiscard(room, me, msg.cardId);
          if (err) fail(err);
          break;
        }
        case 'f7_hit': {
          if (!room || !me) return fail('join a room first');
          if (room.game !== 'flip7') return fail('that move is for Flip 7');
          const err = f7DoHit(room, me);
          if (err) fail(err);
          break;
        }
        case 'f7_stay': {
          if (!room || !me) return fail('join a room first');
          if (room.game !== 'flip7') return fail('that move is for Flip 7');
          const err = f7DoStay(room, me);
          if (err) fail(err);
          break;
        }
        case 'f7_target': {
          if (!room || !me) return fail('join a room first');
          if (room.game !== 'flip7') return fail('that move is for Flip 7');
          const err = f7ApplyTarget(room, me, String(msg.targetId || ''));
          if (err) fail(err);
          break;
        }
        default:
          fail('unknown message type');
      }
    });

    ws.on('close', () => {
      if (!room || !me) return;
      me.connected = false;
      me.ws = null;
      if (room.phase === 'lobby') {
        room.players = room.players.filter(p => p !== me);
        if (!room.players.length) { rooms.delete(room.code); return; }
        if (room.hostId === me.id) room.hostId = room.players[0].id;
        room.lastEvent = me.name + ' left';
        broadcast(room);
      } else {
        // Mid-game: a bot takes over the seat so the game can finish.
        me.isBot = true;
        room.lastEvent = me.name + ' disconnected — a bot has taken their seat';
        broadcast(room);
        if (room.game === 'flip7') f7Continue(room);
        else scheduleBot(room);
      }
    });
  });

  server.listen(port, () => {
    console.log('Five Crowns multiplayer server listening on port ' + port);
  });
  return server;
}

if (require.main === module) startServer(PORT);

module.exports = {
  createDeck, validateMeld, findMelds, tryOut, chooseDiscard, deadwoodValue, handScore, isWild, startServer,
  f7CreateDeck, f7LineScore, f7UniqueCount,
};
