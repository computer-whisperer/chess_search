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
cargo run --release -- retro [N] [MATERIAL]              # ground truth, e.g. retro 4 KRvK, retro 5 KQvKR
cargo run --release -- narrow [N] [MATERIAL] [--direct]  # superposed solve, verified against the table
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

`src/narrow.rs`: the superposed engine. A *region* is one square-domain per
slot (plus "captured"), read as every assignment of slots to distinct
squares within the domains. The same move generator runs against a
recording oracle over the region: a query the region decides is answered
and logged; an undecided one forks the region into disjoint children (one
per slot that could be on the square, plus "empty"; or one per square the
slot could be on). The AND/OR search generates moves one slot at a time and
tries each at once, so a region forks only on what the tried move needs.
Every verdict carries a *pattern*: the conjunction of facts it consulted,
itself a domain product. A child's pattern is pulled back through the move
that reached it; an "any" verdict (a mating move, an escape) keeps only its
own move's facts and its child's pattern, an "all" verdict keeps everything.
Patterns are the memo: a region covered by a stored pattern takes its
verdict without forking. Attack detection only scans for the kinds the
attacker actually has. The horizon deepens one ply at a time up to the
table's maximum DTM (or `--direct` evaluates the full horizon at once, for
win/draw/loss only). Verification against the table checks that every
legal position lies in exactly one leaf, that every leaf's verdict matches
the table on every position it contains, and that every pattern's verdict
holds on every legal position the pattern matches.

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
any superposition.

## The superposed partition: no smaller than the position set

The question the narrowing engine answers is how many *regions* a complete
proof of the material needs — the count of positions distinguishable under
the proof, which is what the shard playground found the search actually
pays for. Value leaves exclude the illegal ones; "positions per pattern" is
the mean number of legal positions matched by a leaf's consulted-fact
pattern, i.e. how far a verdict generalizes beyond the region that produced
it.

| board | material | legal positions | value leaves | leaves / position | positions per pattern | queries / position (narrowing) | queries / position (retrograde) |
|---|---|---|---|---|---|---|---|
| 4×4 | KRvK | 3,808 | 3,808 | 1.000 | 1.00 | 407 | 51 |
| 4×4 | KQvK | 3,308 | 3,308 | 1.000 | 1.00 | 267 | — |
| 5×5 | KRvK | 18,440 | 18,440 | 1.000 | 1.00 | 857 | — |
| 6×6 | KRvK | 62,880 | 62,880 | 1.000 | 1.00 | 1,391 | — |
| 4×4 | KRRvK | 45,488 | 44,936 | 0.988 | 1.02 | 319 | — |
| 5×5 | KRRvK | 368,664 | 365,770 | 0.992 | 1.02 | 655 | — |

`--direct` (win/draw/loss only, no deepening) gives the same partition on
every row. Exact agreement with the table holds on every row.

The result is flat: **the proof partition is the position set.** Every
piece in these materials takes part in every proof — the rook must be
located to be moved, the black king is located at every black node, and
the legality scan for each black escape square walks the rook's rays to
their blockers, which on these boards is the whole board. The don't-care
that the playground's memo exploited (a hole never consulted) needs a piece
no proof line ever moves or scans past; with three or four pieces on up to
36 squares there is none. Two rooks do not create one: the second rook is
scanned as a blocker or an attacker along the black king's escape rays even
in lines that never move it, and only 1.2% of positions end up sharing a
leaf.

What this says about the tweet argument: the reduction from paths to
positions is real and the reduction from positions to a proof DAG is real,
but the further reduction to *distinguishable* positions — the compression
a superposed search buys for free — is a property of the material, not of
the search, and it is absent exactly where a solve spends its effort: at
the retrograde frontier, in endgames where every piece matters. Whatever
"solve and compress" buys must come from value regularity (why 7-man
tablebases fit in a fraction of a bit per position), which is a different
quotient — relational, translation-shaped ("rook on the king's rank"),
not the per-square product this engine's patterns can express.
