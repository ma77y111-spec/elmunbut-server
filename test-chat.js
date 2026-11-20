/* Chat test: two players exchange a room message; a late joiner gets
   the history replay; a socket outside a room is refused. */
const WebSocket = require('ws');
const { startServer } = require('./server.js');

const PORT = 18741;
startServer(PORT);
const url = 'ws://127.0.0.1:' + PORT;

function client(name) {
  const ws = new WebSocket(url);
  const c = { ws, name, inbox: [], waiters: [] };
  ws.on('message', raw => {
    const m = JSON.parse(raw.toString());
    c.inbox.push(m);
    c.waiters = c.waiters.filter(w => !w(m));
  });
  c.send = obj => ws.send(JSON.stringify(obj));
  c.waitFor = (pred, ms = 4000) => new Promise((res, rej) => {
    const hit = c.inbox.find(pred);
    if (hit) return res(hit);
    const w = m => { if (pred(m)) { clearTimeout(t); res(m); return true; } return false; };
    const t = setTimeout(() => rej(new Error(name + ' timed out waiting')), ms);
    c.waiters.push(w);
  });
  c.open = new Promise(r => ws.on('open', r));
  return c;
}
const isChat = text => m => m.type === 'event' && m.event === 'chat' && m.data && m.data.text === text;
const sleep = ms => new Promise(r => setTimeout(r, ms));

(async () => {
  const a = client('A'), b = client('B'), c = client('C'), d = client('D');
  await Promise.all([a.open, b.open, c.open, d.open]);

  // D is not in a room: chat must be refused.
  d.send({ type: 'chat', text: 'hello from nowhere' });
  const err = await d.waitFor(m => m.type === 'error');
  console.log('outsider refused:', err.message);

  a.send({ type: 'create_room', name: 'Alice', game: 'fivecrowns' });
  const joined = await a.waitFor(m => m.type === 'room_joined');
  const code = joined.code;
  const histA = await a.waitFor(m => m.type === 'chat_history');
  console.log('creator history empty:', Array.isArray(histA.messages) && histA.messages.length === 0);

  b.send({ type: 'join_room', code, name: 'Bob' });
  await b.waitFor(m => m.type === 'room_joined');

  a.send({ type: 'chat', text: 'Good luck everyone' });
  const [echoA, gotB] = await Promise.all([a.waitFor(isChat('Good luck everyone')), b.waitFor(isChat('Good luck everyone'))]);
  console.log('sender echo + peer received:', echoA.data.name === 'Alice' && gotB.data.name === 'Alice');

  await sleep(700); // stay outside the rate limit
  b.send({ type: 'chat', text: 'You too Alice' });
  await a.waitFor(isChat('You too Alice'));
  console.log('reply received by A: true');

  // Rate limit: two sends back to back — the second must be refused.
  await sleep(700); // clear the previous message's rate-limit window first
  b.send({ type: 'chat', text: 'fast one' });
  b.send({ type: 'chat', text: 'fast two' });
  await b.waitFor(m => m.type === 'error' && /too fast/.test(m.message));
  console.log('rate limit enforced: true');

  // Late joiner replays history (fast one got through, fast two did not).
  c.send({ type: 'join_room', code, name: 'Carol' });
  await c.waitFor(m => m.type === 'room_joined');
  const histC = await c.waitFor(m => m.type === 'chat_history');
  const texts = histC.messages.map(m => m.text);
  console.log('late joiner history:', JSON.stringify(texts));
  console.log('history correct:', texts.includes('Good luck everyone') && texts.includes('You too Alice') && texts.includes('fast one') && !texts.includes('fast two'));

  for (const x of [a, b, c, d]) x.ws.close();
  console.log('CHAT TEST DONE');
  process.exit(0);
})().catch(e => { console.error('CHAT TEST FAILED:', e.message); process.exit(1); });
