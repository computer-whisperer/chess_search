# Mini rook chess: weak solving with executable safety certificates

This is a small, reproducible experiment in **synthesizing an invariant and using it as a nonlosing policy**, then changing the permitted strategy region to reduce certificate complexity. It is not a claim of a new minichess record, a general chess solution, or an exponential speedup.

**Result:** the specified initial position is a draw on both 4×4 and 5×5 boards. Each result has an independently checked constructive nonloss certificate for both colors. The browser demo executes those certificates without a tablebase.

## Run it

Open `play.html` in a browser. It is self-contained and needs no server or network access. Select either board size and either color. The policy can miss wins: its guarantee is not losing, not maximizing playing strength.

To check an existing certificate, no third-party Python packages are required:

```sh
python reference.py certificate_weak4.json
python reference.py certificate_weak5.json
python test_rules.py
```

To reproduce discovery and all exact checks:

```sh
python -m pip install -r requirements.txt
python reproduce.py               # both board sizes, plus a negative transfer test
python reproduce.py --four-only   # smaller experiment only
```

Discovery needs Python 3.10+, NumPy, scikit-learn, and g++ or clang++ with C++17 support. The graph files use native little-endian integers. The certificate checker uses only Python's standard library. Node.js is optional for `node test_runtime.js`. Browser automation is optional and is not a reproduction dependency.

## Precisely which game?

Each side begins with one king and one rook. White moves first. For 4×4:

```text
4   . . r k
3   . . . .
2   . . . .
1   K R . .
    a b c d
```

For 5×5, Black starts with king e5 and rook d5; White still starts Ka1/Rb1.

King moves, rook moves, blocking, captures, check, and checkmate use their usual chess meanings. Kings cannot be captured and cannot become adjacent. A move cannot leave the moving side's king attacked. There is **no castling, no pawn, no en-passant state, no move clock, and no repetition-claim state**. Stalemate and infinite play are draws. Bare kings are not a separately enforced terminal condition, but cannot produce a win under these rules.

The browser additionally stops at three occurrences of a position, as a usability convention. This only adds drawn terminations and cannot invalidate either nonloss guarantee. The discovery graph and verifier use the history-free infinite-play convention instead.

A state is `(white king, white rook, black king, black rook, side to move)`. Squares are numbered rank-major from a1 = 0; a captured rook is represented by `board_size**2`. Legal-state enumeration includes locally legal positions unreachable from the chosen start. The side that just moved must not be in check.

## Results

| Quantity | 4×4 | 5×5 |
|---|---:|---:|
| All legal states | 42,552 | 352,432 |
| All legal transitions | 225,120 | 2,765,312 |
| States reachable from start with unrestricted legal play | 41,576 | 349,440 |
| Reference result at the starting position | Draw | Draw |
| States in the optimized safe region | 25,380 | 231,632 |
| Decision-tree nodes before subtree sharing | 131 | 565 |
| Unique internal decisions after sharing | 60 | 261 |
| Shared terminal values | 2 | 2 |
| Binary certificate parameter bytes | 369 | 1,575 |
| Failed certificate obligations | 0 | 0 |

The binary sizes include a 9-byte header and 6 bytes per decision record. They **exclude** the move generator, feature implementation, and verifier. In particular, the whole chess policy is not a 369-byte program. A fair total-code accounting must include those components. A one-bit-per-legal-state membership table would occupy 5,319 bytes for 4×4, excluding its indexing machinery; the modest toy size makes constant overhead important.

The fixed deterministic policy has reachable strategy graphs of 10,018 states for White's nonloss guarantee and 10,704 states for Black's on 4×4. The corresponding 5×5 counts are 109,430 and 109,758. The invariant covers more states than these particular policy graphs, which enables a shared description instead of explicit enumeration in the deployed player.

Machine-readable measurements are in `results.json`, `weak_search_results.json`, `synthesis5_results.json`, and the independent verification JSON files.

## How synthesis works

### 1. Build an exact reference

`solve.cpp` enumerates the complete finite game graph and performs retrograde win/draw/loss analysis. Checkmates seed the losing positions. A predecessor with a losing child wins; one whose every child wins loses. Unresolved states draw. Finite win/loss distances are propagated as well, and the resulting values are checked against the minimax recurrence.

The reference establishes ground truth and provides diagnostic measurements. **The actual safety synthesis scripts do not consult the WDL or distance-to-mate arrays.** `lab.py` loads those arrays lazily only when a diagnostic explicitly requests them. As an additional audit, the abstraction and discovered corner restriction were recomputed with both outcome-array files physically unavailable, reproducing the 25,380-state, 131-node result (`no_outcome_audit.json`). Synthesis still uses the complete move graph; this is not a claim of table-free discovery in the broader sense of avoiding state enumeration.

### 2. Search a predicate abstraction

The feature library contains 36 geometry and bounded-local-tactics features: side to move, missing rooks, edge and corner occupancy, king/piece distances, aligned and unblocked lines, legal-move counts, and whether a legal successor has a certain material configuration, check, mate, or stalemate.

These are computed from the rules, not from engine evaluation or solved outcome labels. Some feature names use `can_remove_*`; precisely, they ask whether a successor has the specified rook absent, and therefore can also fire when it was already absent.

States sharing the entire feature vector form a candidate cell. Initially every cell is permitted. A cell is removed if **any** of its concrete members violates a nonloss obligation. This repeats to a fixed point:

* The protected player must not be checkmated in a permitted state.
* At a nonterminal protected-player turn, at least one move must remain inside the permitted region.
* At an opponent turn, every legal move must remain inside it.

Removing an entire cell is conservative. The cell is not assumed to contain strategically equivalent states. Membership is retained only if the same safety promise is valid for all its members.

For 4×4 the initial abstraction has 5,220 cells and converges to a safe region of 31,716 states. An exact decision tree represents it with 189 nodes (seed 0). At that rung it happens to cover the full nonlosing region; this is checked diagnostically, not used as a training label. The 5×5 abstraction is slightly conservative even before additional restrictions.

### 3. Change the strategy region to lower proof cost

`weak_search.py` tries elementary feature-threshold restrictions, closes each surviving candidate under the same adversarial obligations, and fits an exact decision tree. It retains a restriction only if both color-normalized initial positions survive and the tree is smaller. It tries several deterministic tree tie-break seeds. This is a heuristic search, not a proof that the final tree is minimal.

A useful discovered restriction on 4×4 was:

> While the opponent still has a rook, do not occupy a corner with your own rook.

This is **not sufficient by itself to guarantee a draw**. It is an additional restriction on the already-certified safe region. On 4×4 it removes 6,336 states without any additional closure propagation. The resulting invariant admits nonlosing policies from both starting perspectives, while its tree is smaller: 131 nodes, or 60 unique decision nodes after subtree sharing.

For 5×5, the same *type of restriction* was imposed on a freshly synthesized region and required three extra closure rounds. Its certificate was learned afresh; it is not the transferred 4×4 certificate.

### 4. Execute the invariant as a policy

The policy is intentionally simple:

```text
normalize the position so the protected player is called White
for each legal successor in deterministic order:
    if the invariant accepts that successor:
        play that move
```

The full algorithm checks terminal positions and refuses to claim a guarantee outside its invariant. It may select a drawing move when a winning move exists. This is permissible for a constructive nonloss proof from a drawn start.

A small DAG implements invariant membership. The leaves are shared `false` and `true` terminals; internal nodes test a feature against an integer threshold. Hash-consing also merges repeated internal subtrees. The runtime calculates the features through local move generation; it performs no tablebase lookup and no unbounded search.

## Why the certificate is enough

Let `I` be the region described by the decision DAG. Both required initial perspectives are in `I`. At the protected player's turn the policy can select a legal successor still in `I`; at the opponent's turn every legal successor is in `I`. Therefore every play following the policy remains in `I`. No protected-player checkmate is in `I`, so the policy cannot lose. Stalemate or infinite continuation is a draw, and checkmating the opponent is harmless to a nonloss guarantee.

Applying the verified white-relative construction to White and, by color relabeling, to Black supplies a nonlosing policy for each. Together they establish a draw at the specified starting position. There is no claim that local circular consistency proves a forced win; this is an inductive **safety** argument under a draw-on-infinite-play convention.

## Independent verification and negative controls

`reference.py` has a separate rules implementation. Instead of the C++ generator's directional ray walking, it scans candidate target squares and checks blocking with coordinate-between tests. It independently enumerates the state universe and legal transitions, evaluates the certificate, and exhaustively checks the obligations above. It does not load the discovery graph or outcome table. With `--compare`, it additionally confirms that every legal state and every legal transition matches the C++ implementation.

For the optimized 4×4 certificate the verifier checked 15,464 protected-player positions and 9,916 opponent positions inside the invariant, including all 48,324 outgoing opponent transitions. For 5×5 those counts are 141,640, 89,992, and 696,052. All checks passed.

The test suite includes rook blocking, captures, pins, king safety, color symmetry, rejection of a cyclic certificate encoding, rejection of an always-true invariant, and rejection of an empty invariant. All ten tests passed.

The browser runtime was compared with the independent Python implementation on 2,004 sampled states across both board sizes: all 36 feature values, every legal successor in each sample, and certificate memberships matched. 743 sampled policy moves were additionally checked. Headless browser tests exercised both colors on both boards, including actual piece selection, opponent replies, and undo, without page errors. These runtime samples supplement, rather than replace, the exhaustive Python certificate checks.

This is an exhaustively checked finite certificate, not a Lean/Isabelle formalization. The rules interpretation, checker implementation, and software/hardware execution remain in the trusted base. Differential implementation and negative controls reduce the risk of coding mistakes; they do not eliminate every possible shared conceptual error.

## The transfer experiment failed in an informative way

Applying the unchanged optimized 4×4 certificate to 5×5 still accepts both initial perspectives but produces **1,668 failed inductiveness obligations**. This is not merely an issue with unreachable positions. Following its fixed policy from the 5×5 start permits this line:

```text
1. Rc1 Kd4
2. Rb1 Kc3
3. Rc1 Kd2
4. Rb1 Re5
5. Rb2 Kc3
```

At that point the policy has no legal successor that its old invariant accepts. The position is still drawn according to the exact reference. Thus this witness shows a failure of the proposed invariant/policy representation, not a forced loss in the game. A Black-relative transfer also leaves its claimed invariant after nine plies. Raw state sequences are in `transfer_reachable_counterexamples.json`.

Fresh synthesis on 5×5 succeeds, but that is additional discovery work. No size-independent theorem was found.

## What this does and does not show

The successful part is architectural: a reusable predicate can replace an explicit deployed strategy table; both policies and adversarial closure can be checked; and restricting permitted play can make the resulting certificate smaller.

The unsuccessful part is the stronger computational claim. **Discovery and checking still enumerate the entire concrete state graph.** The C++ reference build and solve took about 13 ms on 4×4 and 120 ms on 5×5 in this environment. The Python-based synthesis and proof-size search took seconds. This is not a fair language-matched algorithm benchmark, but it certainly is not evidence that this prototype beats retrograde solving.

Two board sizes do not establish an asymptotic compression rate, and the fixed hand-written feature vocabulary did not yield automatic generalization. The most direct next experiment is to learn additional reusable relational predicates from the failed obligations, then verify obligations symbolically over families rather than by enumerating every concrete member. That part has not been implemented here.

## File guide

`solve.cpp` is the exact reference solver. `lab.py` loads game graphs; `explore.py` defines features and the conservative abstraction closure. `initial4.py`, `weak_search.py`, and `synthesize5.py` perform discovery. `export.py` produces decision DAGs. `reference.py` is the standalone independent verifier. `engine.js` and `play.html` are the table-free deployed policy. `reproduce.py` rebuilds the principal experiment. JSON files preserve certificates, measurements, checks, and transfer failures. The `.bin` files are optional compact encodings of the same DAG parameters; the checker reads JSON.
