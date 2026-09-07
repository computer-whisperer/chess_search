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

### Synthesizing under a symbolic cost model

`src/synth.rs` redoes the discovery in Rust: feature cells, greatest-fixpoint
closure, an exact decision tree, hash-consing. With the full vocabulary it
reproduces codex_idea's fixpoint exactly on 4×4 (5,220 cells, the same 18
removal rounds, 31,716 safe states). The cost model is the vocabulary:
`--vocab geo` keeps only the 29 features a region can decide by
*splitting a slot's domain by the tested predicate* (side to move, missing
rooks, edge and corner tests, pair distances, alignments, clear rays) and
drops the seven that generate moves. `src/symcert.rs` gained the matching
abstract evaluator: a threshold test on one piece splits that piece's
domain into the squares that pass and the squares that fail, a pair test
splits the unpinned side against the pinned one, a clear-ray test splits a
potential blocker's domain on the between-squares. Only when both pieces of
a pair are unpinned and the test is undecided does it fall back to pinning.
Every partition is still cross-checked position by position against the
concrete evaluation.

An inductive certificate exists without any move-generation feature, and
it is nearly the whole nonlosing region:

| board | vocabulary | cells | safe states | nonlosing | decision nodes | membership leaves/position (pinning) | (abstract) | obligation leaves/position |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| 4×4 | full (36) | 5,220 | 31,716 | 31,716 | 87 | — | — | — |
| 4×4 | geo (29) | 5,044 | 31,700 | 31,716 | 152 | 0.775 | **0.140** | 1.000 |
| 5×5 | geo (29) | 37,136 | 270,016 | 271,628 | 442 | 0.583 | **0.125** | 0.992 / 0.996 |

So the membership question — is this position in the invariant? — is now
answered on 7 to 8 times fewer regions than positions, exactly and without
enumeration.

### Abstract move generation

The obligations were the remaining enumeration: the ordinary move
generator against the recording oracle must locate the mover and scan
rays for legality. `src/absmove.rs` replaces it with a move generator on
regions. A candidate move is a (slot, destination) pair applied to a whole
region, which is split until "this slot can legally move to `t`" is
decided everywhere: the mover's domain is narrowed to the origins that
reach `t` (never pinned), other pieces are split on `t` for occupancy, a
rook's blockers are split on the union of its paths, and legality after
the move is decided by the same attack test as the features (adjacency
split on the enemy king's domain; alignment split, then blockers, for the
enemy rook). On the decided-yes parts the successor is again a product,
and a sub-region of it pulls back exactly to a product. Every part is
cross-checked position by position against the concrete obligation.

Two ways to use it. `AbstractMoves` refines one disjoint partition of the
leaf move by move, as before. `Cover` analyses every candidate move on the
whole leaf independently, giving an overlapping cover by witness regions
(own turn) or a list of per-move violation regions (opponent turn), and
charges the number of cases against the concrete edge count.

| board | own-turn leaves/position (Rec) | (AbstractMoves) | opponent-turn (Rec) | (AbstractMoves) | Cover: cases | concrete edges | witnesses per own-turn position |
|---|---:|---:|---:|---:|---:|---:|---:|
| 4×4 | 1.000 | 0.724 | 1.000 | 0.995 | 580,216 | 169,904 | 2.0 |
| 5×5 | 0.992 | 0.822 | 0.996 | 0.882 | 6,181,194 | 2,162,432 | 2.2 |

Exact on every run, and it does not pay. The disjoint partition cannot
get coarse: for an "all replies" obligation the surviving region must be
refined by the predicates of *every* candidate move, and the destinations
of a king and a rook cover the board, so occupancy tests alone pin the
other pieces. The overlapping cover avoids that but costs three times the
concrete edges, because each candidate move needs its own case analysis
whose size does not shrink with the leaf, and the leaves are small: 7 to
8 positions on average, since all four pieces take part in the
invariant's description. Symbolic obligation checking can only win when
membership leaves are large, which needs pieces the invariant does not
mention — the same condition the win-proof partition needed, reached from
the other direction.

### Anchor-relative regions: the translation quotient

The fragmentation above comes from the region representation, not from
the invariant. The invariant's description is already mostly relative —
distances, alignments and clear rays between pairs — but products of
*absolute* square sets cannot express "rook on the king's rank" without
pinning one of the two pieces, so every relational test on two unpinned
pieces fell back to a pin.

`src/rel.rs` changes the representation: a region is the protected king's
absolute square set (the *anchor*) times one *offset* domain per other
piece, with the board boundary as the only coupling. Distances, alignments
and clear rays are then predicates on offsets alone; the anchor's edge
distance is a split on the anchor set alone; an anchor move translates
every offset domain by a constant and a rook move changes one offset, so
successors and pullbacks stay products. One witness region with a
relative move covers every translation of a pattern at once. The
certificate is re-synthesized under the matching vocabulary (`--vocab
rel`: the anchor's edge and corner features plus all pair relations; no
edge features of other pieces), which still admits inductive invariants
close to the whole nonlosing region. Every run below is exact under the
same per-position cross-checks.

| board | legal positions | rel safe / nonlosing | decision nodes | membership leaves/position: absolute | relative | Cover cases / concrete edges: absolute | relative |
|---|---:|---:|---:|---:|---:|---:|---:|
| 4×4 | 42,552 | 31,676 / 31,716 | 145 | 0.140 | 0.079 | 3.4 | 1.93 |
| 5×5 | 352,432 | 258,364 / 271,628 | 687 | 0.125 | 0.062 | 2.9 | 1.42 |
| 6×6 | 1,828,480 | 1,432,360 / 1,457,528 | 912 | 0.242 | 0.024 | 4.5 | **0.60** |
| 7×7 | 7,076,040 | 5,745,304 / 5,804,220 | 1,245 | 0.442 | 0.0125 | 5.3 | **0.31** |
| 8×8 | LEGAL8 | REL8 |

The two representations move in opposite directions as the board grows.
Absolute regions get *worse*: the certificate needs more nodes, the leaves
stay small, and the per-move case analysis does not shrink. Relative
regions get better at every step, and at 6×6 the symbolic check crosses
over: 9.0 million cases against 15.0 million concrete edges, with 98% of
the opponent-turn leaves settled whole (no move escapes anywhere in the
region) and one witness region per 1.7 own-turn positions. Membership is
decided on 41 times fewer regions than there are positions. At 7×7 the
ratio is 0.31 (22.6 million cases against 73.9 million edges), membership
needs 80 times fewer regions than positions, and one witness region
covers 3.6 own-turn positions.

Where that leaves the tweet argument: the drawn game's proof object is an
inductive invariant and it *is* compressible (152 relational decisions
for 42,552 positions here; 442 for 352,432), but discovering and checking
it still touched every position in this project, and the only mechanism
found for avoiding that — reasoning over regions — is limited by exactly
the property that made the win-proof partition flat: on boards this small
every piece matters to every proof step. Whether large boards with
genuinely irrelevant material change that is the open experiment, and
the region machinery here is what would run it.
