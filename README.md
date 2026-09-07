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

## A different proof object: the codex_idea nonloss certificate

`codex_idea/` holds a report, a browser demo and measurements from another
model's experiment on the same question. It gives up on proving wins and
proves a draw instead: a **nonloss certificate** for one side is a set of
positions `I` such that the start is in `I`, the protected side always has
a move that stays in `I` (or is stalemated), every opponent move stays in
`I`, and no position in `I` has the protected side mated. That is an
inductive safety invariant. Checking it needs only one-ply obligations and
no distance to mate. `I` is described by a decision DAG over 36 relational
features (edge and corner tests, distances, alignment, clear rays, and
one-ply tactics such as move count and "can mate"), discovered by
predicate abstraction to a fixpoint, then shrunk by *restricting the
protected side's strategy* ("never put your own rook in a corner") so that
a simpler invariant suffices. The game is KRvKR from a fixed start.

This matters for the question above because a win proof is a least
fixpoint — every position on it carries a progress measure, and the
position set is the only thing fine enough to express it, which is what
the flat 1.0 measures — while a draw proof is a greatest fixpoint with no
progress measure: any inductive set closed under the obligations will do,
and that freedom is what makes it compressible. Chess from the start is
conjecturally a draw, so "solve chess" plausibly means two nonloss
invariants and no tablebase at all.

### Port and independent check

`src/cert.rs` ports the 36 features and the DAG evaluator onto the
`Oracle` trait; `chess_search cert N [--cert4] [--symbolic]` checks the
embedded 4×4 and 5×5 certificates against our retrograde table with a
third, independent rules implementation. Every count in
`codex_idea/mini_rook_chess_results.json` is reproduced exactly: legal
states, safe states, own- and opponent-turn obligations and edges, zero
violations, both deterministic strategy graphs, and the 4→5 transfer
failure (852 own-turn positions with no preserving move plus 816
opponent-turn positions with an escape = their 1,668). In addition, no
position in either invariant is lost for the protected side according to
the table. The transferred 4×4 certificate admits 1,324 positions on 5×5
that the table says are lost, which is why it is not inductive there.

| board | legal | safe | nonlosing (table) | decisions | own obligations | opponent obligations |
|---|---:|---:|---:|---:|---:|---:|
| 4×4 | 42,552 | 25,380 | 31,716 | 60 | 15,464 | 9,916 |
| 5×5 | 352,432 | 231,632 | 271,628 | 261 | 141,640 | 89,992 |

### Can the certificate be checked without enumerating the game?

The report's stated next step is checking obligations "symbolically over
families rather than by enumerating every concrete member". That is what
the recording oracle does, so `src/symcert.rs` evaluates the DAG and both
obligations over superposed regions, forking only on the queries the
features actually make. The result is cross-checked against the concrete
evaluation on every legal position (exact cover, same membership).

| board | legal positions | membership leaves | leaves/position | own-turn leaves/position | opponent-turn leaves/position |
|---|---:|---:|---:|---:|---:|
| 4×4 | 42,552 | 37,560 | 0.883 | 1.000 | 1.000 |
| 5×5 | 352,432 | 352,432 | 1.000 | 1.000 | 1.000 |

The certificate is small to *state* but not to *evaluate*: on 4×4, 79% of
positions' membership walks consult `can_remove_own_rook`, 54% consult
`legal_move_count` and `can_mate`, all of which generate every legal move
(and for `can_mate` every reply), which locates every piece. The tree
learner chose them because they are free on a concrete position; the
one-fact feature `own_rook_missing` that `can_remove_own_rook` mostly
stands in for is consulted on 1% of positions. On 5×5 the DAG's root node
*is* `can_remove_own_rook`, so every membership walk generates every legal
move and the partition is exactly the position set. Once a leaf is safe, the
obligation check generates moves anyway, so the obligation partition is
exactly the position set. Symbolic checking as it stands saves nothing; a
version that could would have to synthesize the certificate under a
*symbolic* cost model, preferring features that a region can answer
without locating everything — a concrete, unimplemented next experiment.
