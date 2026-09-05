# chess search

What is the shape of brute-force chess search? Not the game-path count
(Shannon, 10^120) and not even the position count (Tromp, ~5×10^44), but
the number of *distinguishable* positions under a proof — the measure the
[shard search playground](../shard-search-playground) showed is what a
superposed search actually pays for.

The plan mirrors that playground: a ground-truth engine and a superposed
engine race on the same oracle-based move generator, on boards small enough
that the ground truth is exact.

```
cargo run --release -- retro [N] [MATERIAL]   # e.g. retro 4 KRvK, retro 5 KQvKR
cargo test --release
```

## Engine

`src/board.rs`: N×N board (2..8), pieces K Q R B N (no pawns yet), fixed
piece *slots* (a captured slot is off-board). Move generation, attack
detection and legality are written once against an `Oracle` trait — "which
slot is on square s?", "where is slot k?" — that a concrete position answers
immediately and a superposed region may answer with `Blocked(query)`, so the
same generator drives both engines. Attack detection scans outward from the
attacked square, consulting squares rather than piece locations, so a region
can often answer it without pinning every piece.

`src/retro.rs`: retrograde ground truth. Every index (each slot on any
square or captured, both sides to move) is classified legal/illegal and
solved to Win/Draw/Loss with distance-to-mate in plies by forward fixpoint
iteration. Checkmate = loss, stalemate = draw, kings only = draw, no
move-count rules. `verify` re-derives every value from forward move
generation and fails loudly; it runs after every solve.

## First numbers

| board | material | legal positions | up to symmetry | max DTM (plies) | proof DAG from the longest | reachable from it |
|---|---|---|---|---|---|---|
| 4×4 | KRvK | 3,808 | 485 | 14 | 90 | 3,636 |
| 4×4 | KQvK | 3,308 | 420 | 8 | 17 | 3,152 |
| 5×5 | KRvK | 18,440 | 2,346 | 20 | 432 | 17,960 |
| 4×4 | KQvKR | 35,772 | 4,488 | 40 | 1,149 | 35,292 |
| 4×4 | KRvKN | 48,592 | 6,095 | 28 | 656 | 47,984 |
| 4×4 | KBNvK | 54,780 | 6,864 | 28 | 257 | 27,888 |

"Proof DAG" is the concrete proof of the longest win: one DTM-optimal move at
the winner's nodes, every reply at the loser's, counted as distinct
positions. It is the checkers-style reduction (Schaeffer's proof touched
~10^14 of 5×10^20 positions) measured here: 2–4% of what is reachable, before
any superposition. The superposed engine's job is to show whether the count
of *regions* a proof needs is smaller still, and how it scales.
