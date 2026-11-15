# ElMunBut Five Crowns — Multiplayer Server

An authoritative WebSocket game server for Five Crowns, built to sit behind
the existing single-player app so the ElMunBut crew can play live from
separate phones. The server — never the clients — owns the deck, the hands,
the turn order and the scores.

## What's in here

| File | What it is |
| --- | --- |
| `server.js` | The whole game server: HTTP (test page + health check) and WebSockets on one port. |
| `public/index.html` | A deliberately plain browser test page served by the server itself. Create a room in one tab, join with the code in another, play a basic game. The polished client comes later. |
| `test.js` | Automated end-to-end test: two simulated WebSocket clients + bots play a full round against the real server. |
| `render.yaml` | Render blueprint (free web service, Singapore region) for one-click-ish deployment. |
| `package.json` | `npm start` runs the server on `process.env.PORT`; `npm test` runs the test. Only dependency: `ws`. |

## How the game works here

- **Rooms** are identified by a 4-letter private code. The host creates a
  room; up to 5 others join with the code and a display name (2–6 seats).
- **Lobby:** the host can add bots one at a time, or fill all empty seats
  with bots when starting. Only the host can start.
- **Rules** match the single-player app: 116-card deck (five suits — stars,
  hearts, spades, clubs, diamonds — ranks 3 to King in duplicate, plus 6
  jokers); 11 rounds; round *r* deals *r*+2 cards and that rank is wild
  (jokers always wild). A turn is: draw from stock or discard, then discard.
  Cards are never laid down mid-round — players stage groups privately in
  their client and may rearrange them freely. You go out only when every
  card except your final discard sits in a valid book (3+ of a rank) or run
  (4+ of a suit in sequence, wilds may substitute); going out reveals your
  groups, and every other player then gets exactly one final turn. Deadwood scores face value 3–10, J=11, Q=12, K=13, wild
  cards 20, jokers 50. Lowest total after 11 rounds wins.
- **Privacy:** a client only ever receives its own hand in full. Other
  players are sent as card counts plus their public laid-down groups. Every
  move is validated server-side; public state is broadcast after every move.
- **Disconnects:** if a player drops out mid-game, a bot takes over their
  seat so the game can finish. (In the lobby, a leaver's seat is removed.)
- **Bots** use a simple greedy strategy: take a useful discard, go out when their
  whole hand forms books and runs, shed their highest deadwood card otherwise.
- **Backstop:** if the stock is reshuffled twice in a round, the round is
  scored on the cards in hand so a round can never stall forever.

Client → server messages: `create_room {name}`, `join_room {code, name}`,
`add_bot`, `start_game {fillWithBots}`, `draw {source}`,
`go_out {groups, discardId}` (groups optional — the server can partition
the hand itself), `discard {cardId}`. Server → client: a personalised `state` snapshot after
every change, plus `event` messages (`went_out`, `round_scored`,
`game_over`) and `error` replies for illegal moves.

## Run it locally

```bash
cd ~/workspace/elmunbut-multiplayer
npm install
npm start            # listens on PORT, default 3000
```

Then open <http://localhost:3000> in two browser tabs: create a room in
one, join with the 4-letter code in the other, fill with bots and start.

Useful knobs: `BOT_DELAY_MS` (default 600) and `ROUND_DELAY_MS`
(default 3000) shorten bot thinking and the pause between rounds.

## Test result

`npm test` — **PASSED, three consecutive runs** (15 Nov 2026, Node 24).

Each run: the test spawned the real server, connected two simulated
clients, confirmed a bad room code is rejected, created a room, joined it,
filled the remaining 4 seats with bots, and played round 1 with legal moves
only until it scored. It asserted:

- both clients received identical `round_scored` results, and the totals
  added up (sample run: Alice +0, Bob +34, Cockatoo +19, Sly Fox +0,
  Wombat +21, Kookaburra +0);
- 38 identical public state snapshots were shared between the two clients
  in the sampled run, and every hand count one client saw matched the
  owner's real hand size;
- no client ever received another player's cards (privacy checked on every
  state message);
- round 2 then began, dealing 4 cards with 4s wild.

Separate unit checks confirmed the deck is exactly 116 cards (22 per suit +
6 jokers), book/run validation (including wild substitution, and rejecting
3-card runs and mixed-suit runs), and deadwood values (K=13, wild=20,
joker=50).

**Not tested:** a full 11-round game end-to-end (the test drives round 1 to
completion and confirms round 2 starts), a human playing in a real browser,
reconnecting to a seat after disconnecting (a bot takes the seat over
instead, by design), and more than one room running at once (the code
supports it; the test doesn't exercise it).

## Deploy to Render (free tier)

Nothing here needs an account or purchase to run locally. Deploying needs
Matthew's own Render account and a Git repo Render can see — those two
steps are his; everything else is in this folder.

1. Put this folder in a Git repository and push it to GitHub (or GitLab /
   Bitbucket) under Matthew's account.
2. Sign in at <https://render.com>, choose **New → Blueprint**, and select
   that repo. Render reads `render.yaml` and proposes the
   `elmunbut-five-crowns` web service: free plan, Singapore region,
   build `npm install`, start `npm start`. Confirm/create it.
   *(Equivalent manual route: New → Web Service, connect the repo, choose
   the Free instance type and Singapore region, same build/start commands.)*
3. Render assigns an address like `https://elmunbut-five-crowns.onrender.com`
   and provides `PORT` automatically — `server.js` already reads it. Open
   the address to reach the test page; WebSocket connections use the same
   host over `wss://`.
4. Later, a custom domain can be attached in Render's service settings
   (Settings → Custom Domains) with a DNS record at GoDaddy — no code
   change needed.

Free-tier reality check: the service spins down after ~15 minutes idle and
takes about a minute to wake on the next connection, and Render's free
database (not used here — game state is in memory) expires after 30 days.
For a family card game that's acceptable for testing; the US$7/month
always-on instance is the step up if the wake-up wait annoys. Because state
is in memory, any process restart — a redeploy, a crash, or a spin-down
wake — ends any game in progress; a room only lives while the service
stays up.
