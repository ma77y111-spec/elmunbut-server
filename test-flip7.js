'use strict';
/*
 * Flip 7 end-to-end test: boots the real server on a scratch port, then
 * plays a full game with two scripted WebSocket clients plus bots.
 * Both humans hit until their line is worth 15+, then stay; target
 * prompts are answered with the first legal target. Asserts the game
 * reaches game_end with a winner on 200+, both clients agree on the
 * final totals, every line shown is internally consistent (no duplicate
 * numbers in a live line), and no client ever sees an error.
 *
 * Run: node test-flip7.js
 */
process.env.BOT_DELAY_MS = '20';
process.env.BOT_DISCARD_DELAY_MS = '15';
process.env.F7_FLIP_MS = '15';
process.env.ROUND_DELAY_MS = '250';

const WebSocket = require('ws');
const { startServer } = require('./server');

const PORT = 3217;
const URL = 'ws://127.0.0.1:' + PORT;

let failures = 0;
function check(cond, label) {
  if (cond) console.log('  ok  ' + label);
  else { failures++; console.log('  FAIL ' + label); }
}

function makeClient(name) {
  const c = {
    name, ws: null, id: null, code: null, state: null,
    errors: [], done: false, actedOnVersion: -1, firstPlaying: null,
  };
  c.send = (obj) => c.ws.send(JSON.stringify(obj));
  c.connect = () => new Promise((resolve, reject) => {
    c.ws = new WebSocket(URL);
    c.ws.on('open', resolve);
    c.ws.on('error', reject);
    c.ws.on('message', (buf) => {
      const msg = JSON.parse(buf.toString());
      if (msg.type === 'room_joined') { c.id = msg.playerId; c.code = msg.code; }
      if (msg.type === 'error') {
        // A move sent from a stale 'playing' view can land just after the
        // round/game ended server-side; the client already knows the game
        // moved on, so that rejection is benign. Anything else is real.
        const stalePhase = msg.message === 'the game is not in play'
          && c.state && c.state.phase !== 'playing';
        if (!stalePhase) c.errors.push(msg.message);
      }
      if (msg.type === 'state') {
        c.state = msg;
        if (msg.phase === 'playing' && !c.firstPlaying) c.firstPlaying = msg;
        maybeAct(c);
      }
    });
  });
  return c;
}

function myPlayer(c) {
  return c.state.players.find(p => p.id === c.id);
}

function maybeAct(c) {
  const s = c.state;
  if (!s || s.game !== 'flip7' || s.phase !== 'playing') return;
  if (s.version === c.actedOnVersion) return;
  c.actedOnVersion = s.version;
  const me = myPlayer(c);
  if (!me) return;
  // Answer a target prompt if it is ours.
  if (s.pendingAction && s.pendingAction.byId === c.id) {
    const kind = s.pendingAction.kind;
    let target = null;
    if (kind === 'gift') {
      target = s.players.find(p => p.id !== c.id && p.status === 'in' && !p.hasSecondChance);
    } else if (kind === 'freeze') {
      target = s.players.filter(p => p.status === 'in')
        .sort((a, b) => b.lineScore - a.lineScore)[0];
    } else if (kind === 'flip3') {
      target = me.uniqueCount <= 1 ? me
        : (s.players.filter(p => p.id !== c.id && p.status === 'in')
            .sort((a, b) => b.uniqueCount - a.uniqueCount)[0] || me);
    }
    if (target) setTimeout(() => {
      if (!c.state || c.state.phase !== 'playing') return;
      if (!c.state.pendingAction || c.state.pendingAction.byId !== c.id) return;
      c.send({ type: 'f7_target', targetId: target.id });
    }, 5);
    return;
  }
  // Our decision turn: hit below 15, stay at 15+.
  if (s.currentPlayerId === c.id && me.status === 'in' && !s.pendingAction && !s.flipping) {
    setTimeout(() => {
      if (!c.state || c.state.phase !== 'playing') return;
      const m = myPlayer(c);
      if (c.state.currentPlayerId !== c.id || !m || m.status !== 'in') return;
      if (c.state.pendingAction || c.state.flipping) return;
      c.send({ type: m.lineScore >= 15 ? 'f7_stay' : 'f7_hit' });
    }, 5);
  }
}

function waitFor(fn, label, timeoutMs) {
  return new Promise((resolve, reject) => {
    const t0 = Date.now();
    const iv = setInterval(() => {
      let v;
      try { v = fn(); } catch (e) { v = false; }
      if (v) { clearInterval(iv); resolve(v); }
      else if (Date.now() - t0 > timeoutMs) {
        clearInterval(iv);
        reject(new Error('timed out waiting for: ' + label));
      }
    }, 50);
  });
}

async function main() {
  const server = startServer(PORT);
  await new Promise(r => server.on('listening', r));
  console.log('server up on ' + PORT);

  const a = makeClient('Alice');
  const b = makeClient('Bob');
  await a.connect();
  await b.connect();

  a.send({ type: 'create_room', name: 'Alice', game: 'flip7' });
  await waitFor(() => a.code && a.state, 'Alice creates a flip7 room', 5000);
  check(a.state.game === 'flip7', 'room is a Flip 7 room');

  b.send({ type: 'join_room', name: 'Bob', code: a.code });
  await waitFor(() => b.id && b.state && b.state.players.length === 2, 'Bob joins', 5000);

  a.send({ type: 'add_bot' });
  a.send({ type: 'add_bot' });
  await waitFor(() => a.state.players.length === 4, 'two bots added', 5000);

  a.send({ type: 'start_game' });
  await waitFor(() => a.firstPlaying, 'game starts', 5000);
  check(a.firstPlaying.players.every(p => p.line.length === 0),
    'no opening deal — everyone starts with an empty line, like the offline game');

  // Watch for invariant violations across the whole game.
  let dupViolation = 0;
  const watcher = setInterval(() => {
    const s = a.state;
    if (!s || s.phase !== 'playing') return;
    for (const p of s.players) {
      // Bust-flagged cards are shown in the line on purpose (the card that
      // busted you, or was saved by a Second Chance) — they don't count.
      const nums = p.line.filter(x => x.kind === 'number' && !x.bust).map(x => x.value);
      if (new Set(nums).size !== nums.length && p.status === 'in') dupViolation++;
    }
  }, 30);

  const endState = await waitFor(
    () => a.state && a.state.phase === 'game_end' && a.state,
    'game reaches game_end', 180000);
  clearInterval(watcher);

  check(dupViolation === 0, 'no live line ever held a duplicate number');
  const top = Math.max(...endState.players.map(p => p.totalScore));
  check(top >= 200, 'winner reached 200+ (top=' + top + ')');
  check(Array.isArray(endState.winners) && endState.winners.length >= 1, 'winners recorded');
  const winner = endState.players.find(p => p.id === endState.winners[0]);
  check(winner && winner.totalScore === top, 'winner holds the top score: ' + (winner && winner.name));

  await waitFor(() => b.state && b.state.phase === 'game_end', 'Bob also sees game_end', 5000);
  const totalsA = endState.players.map(p => p.name + ':' + p.totalScore).sort().join(',');
  const totalsB = b.state.players.map(p => p.name + ':' + p.totalScore).sort().join(',');
  check(totalsA === totalsB, 'both clients agree on final totals');
  console.log('  final totals: ' + totalsA);
  console.log('  rounds played: ' + endState.round + ', last event: ' + endState.lastEvent);

  check(a.errors.length === 0, 'Alice saw no errors' + (a.errors.length ? ' — ' + a.errors.join('; ') : ''));
  check(b.errors.length === 0, 'Bob saw no errors' + (b.errors.length ? ' — ' + b.errors.join('; ') : ''));

  a.ws.close(); b.ws.close();
  server.close();
  console.log(failures === 0 ? '\nALL FLIP 7 CHECKS PASSED' : '\n' + failures + ' CHECK(S) FAILED');
  process.exit(failures === 0 ? 0 : 1);
}

main().catch(e => { console.error(e); process.exit(1); });
