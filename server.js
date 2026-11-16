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
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const BOT_DELAY_MS = Number(process.env.BOT_DELAY_MS || 1100);
const BOT_DISCARD_DELAY_MS = Number(process.env.BOT_DISCARD_DELAY_MS || 900);
const ROUND_DELAY_MS = Number(process.env.ROUND_DELAY_MS || 3000);
const F7_FLIP_MS = Number(process.env.F7_FLIP_MS || 1100); // pace of forced flips (Flip Three sequences)
const F7_END_BEAT_MS = Number(process.env.F7_END_BEAT_MS || 1800); // hold after the round's last card lands, before results
const F7_BOT_DELAY_MS = Number(process.env.F7_BOT_DELAY_MS || 1500); // bot thinking time before a Flip 7 decision — the table needs time to see each card land (Matthew, 15 Nov 2026)
const F7_BOT_TARGET_MS = Number(process.env.F7_BOT_TARGET_MS || 1100); // bot thinking time before choosing a target
const MAX_RESHUFFLES = 2; // backstop: after this many stock reshuffles a round is scored as-is

/* ------------------------------------------------------------------ */
/* Cards                                                               */
/* ------------------------------------------------------------------ */
const SUITS = ['stars', 'hearts', 'spades', 'clubs', 'diamonds'];
const RANK_LABEL = { 11: 'J', 12: 'Q', 13: 'K' };
const BOT_NAMES = ['"Millard"', 'Discoveray', 'Expanda', 'Invy', 'Warbie'];
/* How long a disconnected human's seat is held for rejoin before it is
   given up (lobby/game-end seat removed; mid-game seat stays a bot).
   Phones drop the socket when the app is backgrounded (e.g. the player
   switches to Messenger to send the room code), so this must comfortably
   cover a few minutes away. Env override exists for tests. */
const REJOIN_GRACE_MS = Number(process.env.REJOIN_GRACE_MS) || 300000;

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
    // Reconnect support (Matthew, 16 Nov 2026): a human seat survives a
    // dropped connection for a grace period so the player can rejoin.
    // botCover = a bot is playing this human's seat while they are away.
    humanSeat: !isBot, botCover: false, reclaimable: true, disconnectTimer: null,
    identityToken: null, // remembered-identity token bound to this seat, if any
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
      recordGameResult(room, 'Five Crowns');
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
  if (room.round === 1) room.scoreRecorded = false;
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
    ending: !!room.f7Ending, // the round's last card has landed; results follow in a beat
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
  if (!Array.isArray(room.f7Used)) room.f7Used = [];
  if (room.round === 1 || !room.f7DeckInPlay) {
    // A new game always starts from a fresh, full deck.
    room.stock = shuffle(f7CreateDeck());
    room.f7Used = [];
    room.f7DeckInPlay = true;
  } else {
    // Play the deck in full (Matthew, 16 Nov 2026): no fresh deck each
    // round. Cards flipped in earlier rounds move to the used pile and
    // stay out of circulation; the round starts from what is left of
    // the stock, and the used pile is only shuffled back in when the
    // stock runs dry (see f7Draw).
    for (const p of room.players) room.f7Used.push(...p.line);
    room.f7Used.push(...room.f7discard);
  }
  room.f7discard = [];
  room.f7seq = [];
  room.pendingAction = null;
  room.pendingCard = null;
  room.f7Stage = 'decide';
  room.flip7PlayerId = null;
  room.f7Ending = false;
  for (const p of room.players) {
    p.line = [];
    p.status = 'in';
    p.banked = 0;
    p.roundGained = 0;
  }
  // No opening deal — matching the offline game, your first turn is your
  // first flip. Everyone starts the round with an empty line.
  room.phase = 'playing';
  if (room.round === 1) room.scoreRecorded = false;
  const starter = room.players[(room.round - 1) % room.players.length];
  room.currentPlayerId = starter.id;
  room.lastEvent = 'Round ' + room.round + ' dealt — ' + starter.name + ' to play';
  broadcast(room);
  f7Continue(room);
}

function f7Draw(room) {
  if (!room.stock.length) {
    // Stock ran dry mid-round: the used pile (earlier rounds' cards)
    // plus this round's discards shuffle back in. Cards currently in
    // players' lines are never part of the recycle.
    const back = [...(room.f7Used || []), ...room.f7discard];
    if (!back.length) return null;
    room.stock = shuffle(back);
    room.f7Used = [];
    room.f7discard = [];
    // Tell the table the shuffled deck has been applied (Matthew,
    // 16 Nov 2026): clients pop up a "deck shuffled" notification.
    room.lastEvent = 'Deck shuffled — used cards are back in';
    broadcastEvent(room, 'deck_shuffled', {});
  }
  return room.stock.pop();
}

/* One driver for everything that happens next, so turn flips, Flip Three
 * sequences, target prompts and bots can never fight over the flow. */
function f7Continue(room) {
  if (room.phase !== 'playing' || room.f7Ending) return;
  if (room.pendingAction) {
    const by = room.players.find(p => p.id === room.pendingAction.byId);
    if (by && by.isBot) f7Schedule(room, F7_BOT_TARGET_MS, () => f7BotTarget(room));
    return;
  }
  if (room.f7seq.length) {
    f7Schedule(room, F7_FLIP_MS, () => f7SeqStep(room));
    return;
  }
  if (room.f7Stage === 'resolving') { f7Advance(room); return; }
  const p = currentPlayer(room);
  if (!p || p.status !== 'in') { f7Advance(room); return; }
  if (p.isBot) f7Schedule(room, F7_BOT_DELAY_MS, () => f7BotDecision(room));
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
  f7EndRound(room);
}

/* The round is over, but the last card flipped must be SEEN to land
 * first (Matthew, 15 Nov 2026: a bust by the last player in jumped
 * straight to the results — "the drawing and landing of the card is
 * important; lands, if bust, then the game moves on"). So the table
 * holds for a beat in the playing state before scoring. */
function f7EndRound(room) {
  if (room.phase !== 'playing' || room.f7Ending) return;
  room.f7Ending = true;
  broadcast(room);
  setTimeout(() => {
    if (room.phase === 'playing') f7ScoreRound(room);
  }, F7_END_BEAT_MS);
}

function f7DoHit(room, player) {
  if (room.phase !== 'playing') return 'the game is not in play';
  if (room.f7Ending) return 'the round is ending';
  if (room.pendingAction) return 'choose a target first';
  if (room.f7seq.length) return 'cards are still flipping';
  if (currentPlayer(room) !== player) return 'not your turn';
  if (room.f7Stage !== 'decide') return 'you have already flipped';
  if (player.status !== 'in') return 'you are out of this round';
  room.f7Stage = 'resolving';
  const card = f7Draw(room);
  if (!card) { f7EndRound(room); return null; }
  f7ResolveDrawn(room, player, card);
  broadcast(room);
  f7Continue(room);
  return null;
}

function f7DoStay(room, player) {
  if (room.phase !== 'playing') return 'the game is not in play';
  if (room.f7Ending) return 'the round is ending';
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
      f7EndRound(room);
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
  if (!card) { f7EndRound(room); return; }
  top.left--;
  f7ResolveDrawn(room, p, card);
  if (room.phase !== 'playing') return; // Flip 7 ended the round mid-sequence
  if (room.f7Ending) { broadcast(room); return; } // hold the table on the landed card
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
      recordGameResult(room, 'Flip 7');
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
/* Shared ElMunBut score table                                         */
/*                                                                     */
/* One synced table for the whole crew (Matthew, 15 Nov 2026): every   */
/* finished online game is recorded here by the server itself, and     */
/* manual Score Card entries are posted here by the app, so the tally  */
/* everyone sees matches regardless of who played or whose phone       */
/* entered it. Entry: {id, ts, game, source, players:[{name,score}],   */
/* winners:[name]}. The durable copy is scores.json in the             */
/* elmunbut-games GitHub repo, written via the GitHub API when         */
/* GITHUB_TOKEN is set (Render env var); without a token the table     */
/* still works in memory for the life of the process.                  */
/* ------------------------------------------------------------------ */
const SCORES_REPO = 'ma77y111-spec/elmunbut-games';
const SCORES_PATH = 'scores.json';
const SCORES_KEY = 'elmunbut'; // crew word the app sends with manual posts; deters casual spam, nothing more
let SCORES = [];
let scoresSha = null;
let scoresPersistTimer = null;
let scoresPersisting = false;
let scoresDirty = false;

function ghApi(method, apiPath, body) {
  return new Promise((resolve, reject) => {
    const data = body ? JSON.stringify(body) : null;
    const req = https.request({
      hostname: 'api.github.com', path: apiPath, method,
      headers: {
        'User-Agent': 'elmunbut-server',
        'Accept': 'application/vnd.github+json',
        ...(process.env.GITHUB_TOKEN ? { Authorization: 'Bearer ' + process.env.GITHUB_TOKEN } : {}),
        ...(data ? { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(data) } : {}),
      },
    }, res => {
      let buf = '';
      res.on('data', d => { buf += d; });
      res.on('end', () => {
        if (res.statusCode >= 200 && res.statusCode < 300) {
          try { resolve(buf ? JSON.parse(buf) : {}); } catch { resolve({}); }
        } else reject(new Error('GitHub ' + method + ' ' + apiPath + ' -> ' + res.statusCode));
      });
    });
    req.on('error', reject);
    if (data) req.write(data);
    req.end();
  });
}

async function loadScores() {
  try {
    const file = await ghApi('GET', '/repos/' + SCORES_REPO + '/contents/' + SCORES_PATH);
    const parsed = JSON.parse(Buffer.from(file.content || '', 'base64').toString('utf8'));
    if (Array.isArray(parsed)) { SCORES = parsed; scoresSha = file.sha || null; }
    console.log('scores: loaded ' + SCORES.length + ' entries from GitHub');
  } catch (err) {
    console.log('scores: starting empty (' + err.message + ')');
  }
}

function persistScores() {
  if (!process.env.GITHUB_TOKEN) return; // in-memory only until the token is set
  scoresDirty = true;
  if (scoresPersistTimer) return;
  scoresPersistTimer = setTimeout(async () => {
    scoresPersistTimer = null;
    if (scoresPersisting || !scoresDirty) return;
    scoresPersisting = true; scoresDirty = false;
    try {
      if (!scoresSha) {
        try {
          const file = await ghApi('GET', '/repos/' + SCORES_REPO + '/contents/' + SCORES_PATH);
          scoresSha = file.sha || null;
        } catch { scoresSha = null; }
      }
      const content = Buffer.from(JSON.stringify(SCORES, null, 2)).toString('base64');
      const out = await ghApi('PUT', '/repos/' + SCORES_REPO + '/contents/' + SCORES_PATH, {
        message: 'scores: update shared table', content, ...(scoresSha ? { sha: scoresSha } : {}),
      });
      if (out && out.content) scoresSha = out.content.sha;
      console.log('scores: persisted ' + SCORES.length + ' entries');
    } catch (err) {
      console.log('scores: persist failed (' + err.message + ')');
      scoresDirty = true;
    }
    scoresPersisting = false;
    if (scoresDirty) persistScores();
  }, 3000);
}

/* Remembered identity (Matthew, 16 Nov 2026): no logins, no passwords.
 * The server issues each player name a private token once; the app
 * stores it on the device and presents it on every connect, so a
 * refresh or a reopened page knows who you are, your name cannot be
 * borrowed by another device, and a held seat can be reclaimed by
 * token alone. Tokens persist to identities.json in the games repo,
 * beside scores.json, under the same GitHub token. If a device loses
 * its token (browser data cleared), the name stays bound — Marles can
 * free it by removing the entry from identities.json. */
const IDENT_PATH = 'identities.json';
const IDENTITIES = new Map(); // token -> { name, createdAt }
const tokenByName = new Map(); // lowercase name -> token
let identSha = null;
let identTimer = null;
let identPersisting = false;
let identDirty = false;

function normalisePlayerName(raw) {
  let n = String(raw || '').trim().slice(0, 24);
  if (/^matt$/i.test(n)) n = 'Matthew';
  return n;
}

function presentedToken(msg, ws) {
  return String((msg && msg.token) || (ws && ws.identityToken) || '');
}

/* Find a user's existing seat: by identity token when one is
   presented, otherwise by name — but a name match only counts when
   the seat is not bound to a different remembered identity. Used to
   stop duplicate rooms/seats when the app glitches or is reopened,
   and to auto-place a player back into their game when they pick
   that game in the app (Matthew, 16 Nov 2026). */
function findUserSeat(game, identityToken, name) {
  for (const r of rooms.values()) {
    if (game && r.game !== game) continue;
    const seat = r.players.find(p => {
      if (!p.humanSeat || !p.reclaimable) return false;
      if (identityToken && p.identityToken === identityToken) return true;
      return !!name && p.name.toLowerCase() === name.toLowerCase()
        && (!p.identityToken || p.identityToken === identityToken);
    });
    if (seat) return { room: r, seat };
  }
  return null;
}

function heldSeatForToken(token) {
  // The token proves this is the same device, so the seat counts as
  // held even if its old socket still looks connected — a backgrounded
  // phone often leaves a zombie socket the server has not seen close
  // yet, and treating the seat as taken created duplicate seats
  // (Matthew, 16 Nov 2026: two of the same player in one room).
  for (const r of rooms.values()) {
    const seat = r.players.find(p => p.humanSeat && p.identityToken === token && p.reclaimable);
    if (seat) return { room: r, seat };
  }
  return null;
}

async function loadIdentities() {
  try {
    const file = await ghApi('GET', '/repos/' + SCORES_REPO + '/contents/' + IDENT_PATH);
    const parsed = JSON.parse(Buffer.from(file.content || '', 'base64').toString('utf8'));
    if (Array.isArray(parsed)) {
      const merged = new Map();
      for (const rec of parsed) {
        if (rec && rec.token && rec.name) {
          merged.set(rec.token, { name: rec.name, createdAt: rec.createdAt || 0 });
        }
      }
      // Keep identities issued since startup that the stored file
      // does not know about yet (their persist may still be in
      // flight) — a slow load must never wipe a token a device was
      // just handed.
      for (const [tok, rec] of IDENTITIES) if (!merged.has(tok)) merged.set(tok, rec);
      IDENTITIES.clear(); tokenByName.clear();
      for (const [tok, rec] of merged) {
        IDENTITIES.set(tok, rec);
        tokenByName.set(String(rec.name).toLowerCase(), tok);
      }
      identSha = file.sha || null;
    }
    console.log('identities: loaded ' + IDENTITIES.size + ' from GitHub');
  } catch (err) {
    console.log('identities: starting empty (' + err.message + ')');
  }
}

function persistIdentities() {
  if (!process.env.GITHUB_TOKEN) return;
  identDirty = true;
  if (identTimer) return;
  identTimer = setTimeout(async () => {
    identTimer = null;
    if (identPersisting || !identDirty) return;
    identPersisting = true; identDirty = false;
    try {
      if (!identSha) {
        try {
          const file = await ghApi('GET', '/repos/' + SCORES_REPO + '/contents/' + IDENT_PATH);
          identSha = file.sha || null;
        } catch { identSha = null; }
      }
      const list = [...IDENTITIES.entries()].map(([token, rec]) => ({ token, name: rec.name, createdAt: rec.createdAt }));
      const content = Buffer.from(JSON.stringify(list, null, 2)).toString('base64');
      const out = await ghApi('PUT', '/repos/' + SCORES_REPO + '/contents/' + IDENT_PATH, {
        message: 'identities: update remembered identities', content, ...(identSha ? { sha: identSha } : {}),
      });
      if (out && out.content) identSha = out.content.sha;
      console.log('identities: persisted ' + list.length);
    } catch (err) {
      console.log('identities: persist failed (' + err.message + ')');
      identDirty = true;
    }
    identPersisting = false;
    if (identDirty) persistIdentities();
  }, 3000);
}

function issueIdentity(name) {
  const token = crypto.randomBytes(24).toString('hex');
  IDENTITIES.set(token, { name, createdAt: Date.now() });
  tokenByName.set(name.toLowerCase(), token);
  persistIdentities();
  return token;
}

function recordScore(entry) {
  const clean = {
    id: 's' + Date.now().toString(36) + Math.random().toString(36).slice(2, 8),
    ts: Date.now(),
    game: String(entry.game || ''),
    source: entry.source || 'online',
    players: (entry.players || []).map(p => ({ name: String(p.name || '').slice(0, 24), score: Number(p.score) || 0 })),
    winners: (entry.winners || []).map(n => String(n).slice(0, 24)),
  };
  if (!clean.game || !clean.players.length) return null;
  SCORES.push(clean);
  persistScores();
  return clean;
}

function recordGameResult(room, gameLabel) {
  if (room.scoreRecorded) return;
  room.scoreRecorded = true;
  /* Matthew, 16 Nov 2026: games against the bots must NOT go into the
     shared scoring table — only real online games between crew members
     are tallied. A room with fewer than 2 human players is a bot game
     (solo practice via an online room), so it is never recorded. Rooms
     with 2+ humans are recorded in full, including any bot fill-ins. */
  const humans = room.players.filter(p => p.humanSeat);
  if (humans.length < 2) return;
  recordScore({
    game: gameLabel, source: 'online',
    players: room.players.map(p => ({ name: p.name, score: p.totalScore })),
    winners: room.players.filter(p => (room.winners || []).includes(p.id)).map(p => p.name),
  });
}

/* ------------------------------------------------------------------ */
/* HTTP + WebSocket server                                             */
/* ------------------------------------------------------------------ */
function startServer(port) {
  const server = http.createServer((req, res) => {
    if (req.url === '/healthz') { res.writeHead(200); res.end('ok'); return; }
    if (req.url === '/scores' && req.method === 'GET') {
      res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
      res.end(JSON.stringify({ entries: SCORES }));
      return;
    }
    if ((req.url === '/scores/manual' || req.url === '/scores/delete') && req.method === 'OPTIONS') {
      res.writeHead(204, { 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Methods': 'POST', 'Access-Control-Allow-Headers': 'Content-Type' });
      res.end();
      return;
    }
    if ((req.url === '/scores/manual' || req.url === '/scores/delete') && req.method === 'POST') {
      let buf = '';
      req.on('data', d => { buf += d; if (buf.length > 65536) req.destroy(); });
      req.on('end', () => {
        let msg = null;
        try { msg = JSON.parse(buf); } catch { /* handled below */ }
        if (!msg || msg.key !== SCORES_KEY) { res.writeHead(403, { 'Access-Control-Allow-Origin': '*' }); res.end('forbidden'); return; }
        if (req.url === '/scores/delete') {
          const before = SCORES.length;
          SCORES = SCORES.filter(e => e.id !== String(msg.id || ''));
          if (SCORES.length !== before) persistScores();
          res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
          res.end(JSON.stringify({ ok: true, removed: before - SCORES.length }));
          return;
        }
        const saved = recordScore({ game: String(msg.game || ''), source: 'manual', players: msg.players, winners: msg.winners });
        if (!saved) { res.writeHead(400, { 'Access-Control-Allow-Origin': '*' }); res.end('bad entry'); return; }
        res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
        res.end(JSON.stringify({ ok: true, entry: saved }));
      });
      return;
    }
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

  /* Reconnect helpers. holdSeat starts the grace clock when a human's
     socket drops; expireSeat gives the seat up when it runs out;
     reclaimSeat binds a fresh socket back onto a held seat. */
  function expireSeat(roomRef, player) {
    player.disconnectTimer = null;
    if (player.connected) return;
    if (roomRef.phase === 'lobby' || roomRef.phase === 'game_end') {
      roomRef.players = roomRef.players.filter(p => p !== player);
      if (!roomRef.players.length) { rooms.delete(roomRef.code); return; }
      if (roomRef.hostId === player.id) {
        // A bot must never host a room a person created (Matthew,
        // 16 Nov 2026): host passes to a human seat only — a present
        // one first — and if only bots are left the room closes
        // instead of leaving a bot in charge.
        const humans = roomRef.players.filter(p => p.humanSeat);
        const next = humans.find(p => p.connected && !p.botCover) || humans.find(p => !p.botCover) || humans[0];
        if (!next) { rooms.delete(roomRef.code); return; }
        roomRef.hostId = next.id;
      }
      roomRef.lastEvent = player.name + ' left';
      broadcast(roomRef);
    } else {
      // Mid-game the bot keeps the seat for good; it just can't be
      // reclaimed any more. Make sure the bot is actually covering it
      // (the seat may have been held from the lobby when the game
      // started) and that play moves forward.
      player.reclaimable = false;
      // If the departing host's seat is now a bot for good, hand host
      // to another human seat so a person stays in charge of the room.
      if (roomRef.hostId === player.id) {
        const next = roomRef.players.find(p => p !== player && p.humanSeat && !p.botCover)
          || roomRef.players.find(p => p !== player && p.humanSeat);
        if (next) roomRef.hostId = next.id;
      }
      if (player.humanSeat && !player.isBot) {
        player.botCover = true;
        player.isBot = true;
        broadcast(roomRef);
        if (roomRef.game === 'flip7') f7Continue(roomRef);
        else scheduleBot(roomRef);
      }
    }
  }
  function holdSeat(roomRef, player) {
    if (player.disconnectTimer) clearTimeout(player.disconnectTimer);
    player.disconnectTimer = setTimeout(() => expireSeat(roomRef, player), REJOIN_GRACE_MS);
    if (player.disconnectTimer.unref) player.disconnectTimer.unref();
  }
  function reclaimSeat(roomRef, player, socket) {
    const oldWs = player.ws;
    if (player.disconnectTimer) { clearTimeout(player.disconnectTimer); player.disconnectTimer = null; }
    player.ws = socket;
    player.connected = true;
    // One seat per user per room: if the seat's previous socket is
    // still hanging around (zombie from a backgrounded app), close it
    // so the newest connection is the only one bound to the seat. Its
    // close handler sees the seat is bound to a different socket and
    // leaves the seat alone.
    if (oldWs && oldWs !== socket) { try { oldWs.close(); } catch { /* already gone */ } }
    if (player.identityToken) socket.identityToken = player.identityToken;
    if (player.botCover) { player.botCover = false; player.isBot = false; }
    roomRef.lastEvent = player.name + ' reconnected';
    send(socket, { type: 'room_joined', code: roomRef.code, playerId: player.id });
    broadcast(roomRef);
  }
  function findReclaimable(roomRef, pred, allowConnected) {
    // allowConnected: the caller has proven this is the same user
    // (their seat id, their identity token, or their name on a
    // name-only seat), so a seat whose old socket has not timed out
    // yet is still theirs to take back — never a reason to seat them
    // twice.
    return roomRef.players.find(p => p.humanSeat && p.reclaimable && (allowConnected || !p.connected || p.botCover) && pred(p)) || null;
  }

  const wss = new WebSocketServer({ server });

  wss.on('connection', ws => {
    let me = null;   // player object
    let room = null; // room object

    ws.on('message', raw => {
      let msg;
      try { msg = JSON.parse(raw.toString()); } catch { return; }
      const fail = text => send(ws, { type: 'error', message: text });

      switch (msg.type) {
        case 'identify': {
          // Remembered identity handshake: a known token restores the
          // name bound to it (and reports any held seat); a new name
          // gets a fresh token; a name already bound to another device
          // is refused so names cannot be borrowed.
          const token = String(msg.token || '');
          if (token && IDENTITIES.has(token)) {
            ws.identityToken = token;
            const rec = IDENTITIES.get(token);
            const held = heldSeatForToken(token);
            send(ws, {
              type: 'identity', token, name: rec.name,
              heldSeat: held ? { code: held.room.code, game: held.room.game, playerId: held.seat.id } : null,
            });
          } else if (msg.name) {
            const name = normalisePlayerName(msg.name);
            if (!name) { send(ws, { type: 'identity_error', message: 'Enter your name first' }); break; }
            if (tokenByName.has(name.toLowerCase())) {
              send(ws, { type: 'identity_error', message: name + ' is already set up on another device' });
              break;
            }
            const fresh = issueIdentity(name);
            ws.identityToken = fresh;
            send(ws, { type: 'identity', token: fresh, name, heldSeat: null });
          } else {
            send(ws, { type: 'identity_error', message: 'No identity on this device yet' });
          }
          break;
        }
        case 'find_my_room': {
          // Auto-placement (Matthew, 16 Nov 2026): when a player picks
          // a game in the app, if they already have a seat in a room
          // for that game they are put straight back into it — the app
          // asks here, then rejoins with the seat it is handed.
          const presented = presentedToken(msg, ws);
          let identityToken = null;
          let name = normalisePlayerName(msg.name);
          if (presented && IDENTITIES.has(presented)) {
            name = IDENTITIES.get(presented).name;
            identityToken = presented;
          }
          const gameFilter = msg.game === 'flip7' ? 'flip7' : (msg.game === 'fivecrowns' ? 'fivecrowns' : null);
          const found = (identityToken || name) ? findUserSeat(gameFilter, identityToken, name) : null;
          send(ws, {
            type: 'my_room', game: gameFilter,
            found: found ? {
              code: found.room.code, game: found.room.game,
              playerId: found.seat.id, phase: found.room.phase,
              isHost: found.room.hostId === found.seat.id,
            } : null,
          });
          break;
        }
        case 'create_room': {
          if (me) return fail('you are already in a room');
          const presented = presentedToken(msg, ws);
          let identityToken = null;
          let name = normalisePlayerName(msg.name);
          if (presented && IDENTITIES.has(presented)) {
            name = IDENTITIES.get(presented).name;
            identityToken = presented;
          } else if (name && tokenByName.has(name.toLowerCase())) {
            return fail(name + ' is set up as a remembered identity on another device — open the page on that device, or use a different name');
          }
          if (!name) return fail('a display name is required');
          const gameWanted = msg.game === 'flip7' ? 'flip7' : 'fivecrowns';
          // Already in a lobby for this game? Creating again (the app
          // glitched, or the page was reopened) returns that room
          // instead of piling up duplicate lobbies for the same user.
          const existing = findUserSeat(gameWanted, identityToken, name);
          if (existing && existing.room.phase === 'lobby') {
            room = existing.room;
            me = existing.seat;
            reclaimSeat(room, me, ws);
            break;
          }
          room = {
            code: makeCode(), hostId: null, players: [], phase: 'lobby',
            game: gameWanted,
            round: 1, wildRank: null, stock: [], discard: [],
            currentPlayerId: null, turnPhase: 'draw', turnCount: 0,
            outPlayerId: null, finalPending: null, reshuffles: 0,
            lastRoundResult: null, winners: null, lastEvent: 'Room created',
            version: 0, botScheduled: false,
            // Flip 7 state (unused in Five Crowns rooms). The flip deck
            // lives in room.stock; f7discard is its reshuffle pile.
            f7seq: [], pendingAction: null, pendingCard: null,
            f7Stage: 'decide', f7Scheduled: false, flip7PlayerId: null,
            f7discard: [], f7Ending: false, scoreRecorded: false,
            f7Used: [], f7DeckInPlay: false,
          };
          me = makePlayer(name, false);
          me.ws = ws; me.connected = true;
          me.identityToken = identityToken;
          room.hostId = me.id;
          room.players.push(me);
          rooms.set(room.code, room);
          send(ws, { type: 'room_joined', code: room.code, playerId: me.id });
          broadcast(room);
          break;
        }
        case 'list_rooms': {
          // Open games list (Matthew, 16 Nov 2026): lobby rooms waiting
          // for players, so the crew can join straight from the page
          // without swapping to a messenger app for the room code.
          const gameFilter = msg.game === 'flip7' ? 'flip7' : (msg.game === 'fivecrowns' ? 'fivecrowns' : null);
          const open = [];
          for (const r of rooms.values()) {
            if (r.phase !== 'lobby' || r.players.length >= 6) continue;
            if (gameFilter && r.game !== gameFilter) continue;
            const host = r.players.find(p => p.id === r.hostId);
            if (!host || !host.humanSeat) continue; // a bot never hosts; don't list such a room
            open.push({
              code: r.code, game: r.game,
              host: host ? host.name : '',
              players: r.players.map(p => p.name),
              seatsFree: 6 - r.players.length,
            });
          }
          send(ws, { type: 'rooms_list', rooms: open });
          break;
        }
        case 'rejoin_room': {
          if (me) return fail('you are already in a room');
          // Token-only rejoin: a reopened page may have lost its seat
          // id but still holds its identity token — find the held seat
          // by token and rejoin it.
          if (!msg.playerId && msg.token && IDENTITIES.has(String(msg.token))) {
            const found = heldSeatForToken(String(msg.token));
            if (found) { msg.playerId = found.seat.id; msg.code = found.room.code; }
          }
          const target = rooms.get(String(msg.code || '').trim().toUpperCase());
          if (!target) return fail('no room with that code');
          const seat = findReclaimable(target, p => p.id === String(msg.playerId || ''), true);
          if (!seat) return fail('that seat is no longer available');
          room = target;
          me = seat;
          reclaimSeat(room, me, ws);
          break;
        }
        case 'join_room': {
          if (me) return fail('you are already in a room');
          const presented = presentedToken(msg, ws);
          let identityToken = null;
          let name = normalisePlayerName(msg.name);
          if (presented && IDENTITIES.has(presented)) {
            name = IDENTITIES.get(presented).name;
            identityToken = presented;
          }
          if (!name) return fail('a display name is required');
          const target = rooms.get(String(msg.code || '').trim().toUpperCase());
          if (!target) return fail('no room with that code');
          // A player coming back (app was backgrounded, socket dropped)
          // reclaims their held seat instead of joining twice — this
          // works mid-game too, where a fresh join is refused. The seat
          // is matched by identity token when one is presented, else by
          // name, and it is reclaimed even if the old socket still
          // looks connected: there is only ever one seat per user in a
          // room (Matthew, 16 Nov 2026). A seat bound to a remembered
          // identity can only be reclaimed by the device holding that
          // identity's token.
          const held = findReclaimable(target, p =>
            (identityToken && p.identityToken === identityToken) ||
            p.name.toLowerCase() === name.toLowerCase(), true);
          if (held && held.identityToken && held.identityToken !== identityToken) {
            return fail('That seat is held for ' + name + "'s device — it can only be rejoined from that device");
          }
          if (held) {
            room = target;
            me = held;
            reclaimSeat(room, me, ws);
            break;
          }
          if (!identityToken && tokenByName.has(name.toLowerCase())) {
            return fail(name + ' is set up as a remembered identity on another device — open the page on that device, or use a different name');
          }
          if (target.phase !== 'lobby') return fail('that game has already started');
          if (target.players.length >= 6) return fail('that room is full');
          room = target;
          me = makePlayer(name, false);
          me.ws = ws; me.connected = true;
          me.identityToken = identityToken;
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
          // A human whose socket dropped in the lobby (seat held) starts
          // the game covered by a bot; they can reclaim the seat mid-game.
          for (const p of room.players) {
            if (p.humanSeat && !p.connected) { p.botCover = true; p.isBot = true; }
          }
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
      // Only the socket currently bound to the seat counts; a stale
      // socket closing after a rejoin must not drop the player again.
      if (me.ws !== ws) return;
      me.connected = false;
      me.ws = null;
      if (room.phase === 'lobby' || room.phase === 'game_end') {
        // Hold the seat for the grace period — phones drop the socket
        // when the app is backgrounded, and the player usually comes
        // straight back (e.g. after sending the room code by message).
        holdSeat(room, me);
        room.lastEvent = me.name + ' disconnected — seat held, they can rejoin';
        broadcast(room);
      } else {
        // Mid-game: a bot covers the seat so the game can continue, but
        // the human can still reclaim it within the grace period.
        me.botCover = true;
        me.isBot = true;
        holdSeat(room, me);
        room.lastEvent = me.name + ' disconnected — a bot is covering their seat, they can rejoin';
        broadcast(room);
        if (room.game === 'flip7') f7Continue(room);
        else scheduleBot(room);
      }
    });
  });

  server.listen(port, () => {
    console.log('Five Crowns multiplayer server listening on port ' + port);
    loadScores();
    loadIdentities();
  });
  return server;
}

if (require.main === module) startServer(PORT);

module.exports = {
  createDeck, validateMeld, findMelds, tryOut, chooseDiscard, deadwoodValue, handScore, isWild, startServer,
  f7CreateDeck, f7LineScore, f7UniqueCount,
};
