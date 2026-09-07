//! Synthesize a nonloss certificate the way codex_idea did, in Rust and
//! under a chosen feature vocabulary:
//!
//! 1. every legal position gets a feature vector over the vocabulary; the
//!    positions sharing a vector form a *cell*;
//! 2. a cell is removed if any member violates a nonloss obligation for the
//!    protected side (White; Black is handled by relabeling), to a fixpoint;
//! 3. the surviving cells are described by an exact decision tree over the
//!    vocabulary, hash-consed into a DAG in the certificate format.
//!
//! The vocabulary is the cost model: restricting it to features a region can
//! decide by splitting a domain (`GEO`) rather than generating moves is what
//! would let the symbolic check pay off.

use crate::board::*;
use crate::cert::{self, Roles, FEATURE_NAMES, NFEAT};
use crate::certs::Cert;
use crate::retro::{Table, Val};
use std::collections::HashMap;

/// Geometric features: side to move, missing rooks, edge/corner tests, pair
/// distances, alignments and clear rays. No move generation.
pub const GEO: std::ops::Range<usize> = 0..29;
/// Everything, including the one-ply tactical features.
pub const FULL: std::ops::Range<usize> = 0..NFEAT;
/// Anchor-relative: only the protected king's edge/corner features are
/// absolute; everything else is a relation between two pieces. This is the
/// vocabulary an anchor-relative region can decide by splitting offset
/// domains, with the anchor's own domain split only by its edge distance.
pub fn rel_vocab() -> Vec<usize> {
    let mut v = vec![0, 1, 2, 3, 4];
    v.extend(11..29);
    v
}

pub struct Synthesis {
    pub vocab: Vec<usize>,
    pub cells: usize,
    pub rounds: usize,
    pub removed_by_round: Vec<usize>,
    pub safe_cells: usize,
    pub safe_states: usize,
    /// Start position permitted from White's and from Black's perspective.
    pub roots_ok: [bool; 2],
    pub tree_nodes: usize,
    pub cert: Cert,
}

struct Node {
    feat: usize,
    thr: i32,
    left: Box<Tree>,
    right: Box<Tree>,
}

enum Tree {
    Leaf(bool),
    Split(Node),
}

/// Greedy top-down exact tree over distinct cell vectors (weighted Gini).
fn fit(vecs: &[Vec<i32>], label: &[bool], weight: &[usize], rows: Vec<usize>, count: &mut usize) -> Tree {
    let pos: usize = rows.iter().filter(|&&r| label[r]).map(|&r| weight[r]).sum();
    let tot: usize = rows.iter().map(|&r| weight[r]).sum();
    if pos == 0 || pos == tot {
        return Tree::Leaf(pos == tot);
    }
    *count += 1;
    let nf = vecs[rows[0]].len();
    let mut best: Option<(f64, usize, i32)> = None;
    for f in 0..nf {
        let mut vals: Vec<i32> = rows.iter().map(|&r| vecs[r][f]).collect();
        vals.sort_unstable();
        vals.dedup();
        for &thr in &vals[..vals.len() - 1] {
            let (mut lp, mut lt) = (0usize, 0usize);
            for &r in &rows {
                if vecs[r][f] <= thr {
                    lt += weight[r];
                    lp += label[r] as usize * weight[r];
                }
            }
            let (rp, rt) = (pos - lp, tot - lt);
            let gini = |p: usize, t: usize| {
                if t == 0 { 0.0 } else { let q = p as f64 / t as f64; 2.0 * q * (1.0 - q) * t as f64 }
            };
            let score = gini(lp, lt) + gini(rp, rt);
            if best.is_none_or(|(s, _, _)| score < s - 1e-12) {
                best = Some((score, f, thr));
            }
        }
    }
    let (_, f, thr) = best.expect("distinct vectors with different labels are separable");
    let (l, r): (Vec<usize>, Vec<usize>) = rows.iter().partition(|&&row| vecs[row][f] <= thr);
    Tree::Split(Node {
        feat: f,
        thr,
        left: Box::new(fit(vecs, label, weight, l, count)),
        right: Box::new(fit(vecs, label, weight, r, count)),
    })
}

/// Hash-cons the tree into the certificate's node table.
fn cons(t: &Tree, vocab: &[usize], nodes: &mut Vec<[i32; 4]>, memo: &mut HashMap<[i32; 4], u32>) -> u32 {
    match t {
        Tree::Leaf(b) => *b as u32,
        Tree::Split(n) => {
            let l = cons(&n.left, vocab, nodes, memo);
            let r = cons(&n.right, vocab, nodes, memo);
            let key = [vocab[n.feat] as i32, n.thr, l as i32, r as i32];
            *memo.entry(key).or_insert_with(|| {
                nodes.push(key);
                (nodes.len() + 1) as u32
            })
        }
    }
}

pub fn synthesize(table: &Table, vocab: &[usize]) -> Synthesis {
    let setup = &table.setup;
    let roles = Roles::new(setup, Color::White);
    // Legal positions, their cells, and their successors.
    let mut idx: Vec<usize> = Vec::new();
    let mut slot_of = vec![usize::MAX; table.vals.len()];
    for (i, &v) in table.vals.iter().enumerate() {
        if v != Val::Illegal {
            slot_of[i] = idx.len();
            idx.push(i);
        }
    }
    let mut cell_id: HashMap<Vec<i32>, usize> = HashMap::new();
    let mut cell_vec: Vec<Vec<i32>> = Vec::new();
    let mut cell_of = vec![0usize; idx.len()];
    let mut stm_white = vec![false; idx.len()];
    let mut mated = vec![false; idx.len()];
    let mut succ: Vec<Vec<usize>> = Vec::with_capacity(idx.len());
    for (k, &i) in idx.iter().enumerate() {
        let p = Table::position(setup, i);
        let v: Vec<i32> = vocab.iter().map(|&f| cert::feature(setup, &p, p.stm, &roles, f).unwrap()).collect();
        let next = cell_vec.len();
        let c = *cell_id.entry(v.clone()).or_insert(next);
        if c == next {
            cell_vec.push(v);
        }
        cell_of[k] = c;
        stm_white[k] = p.stm == Color::White;
        let moves = legal_moves(setup, &p, p.stm).unwrap();
        mated[k] = moves.is_empty() && in_check(setup, &p, p.stm).unwrap();
        succ.push(moves.iter().map(|&mv| slot_of[Table::index(setup, &p.play(mv))]).collect());
    }
    let cells = cell_vec.len();
    // Greatest fixpoint: drop cells with a violating member.
    let mut permitted = vec![true; cells];
    let mut removed_by_round = Vec::new();
    loop {
        let mut kill = vec![false; cells];
        for k in 0..idx.len() {
            let c = cell_of[k];
            if !permitted[c] || kill[c] {
                continue;
            }
            let bad = if stm_white[k] {
                if succ[k].is_empty() { mated[k] } else { !succ[k].iter().any(|&s| permitted[cell_of[s]]) }
            } else {
                !succ[k].iter().all(|&s| permitted[cell_of[s]])
            };
            if bad {
                kill[c] = true;
            }
        }
        let n = kill.iter().filter(|&&b| b).count();
        if n == 0 {
            break;
        }
        removed_by_round.push(n);
        for c in 0..cells {
            if kill[c] {
                permitted[c] = false;
            }
        }
    }
    let safe_states = (0..idx.len()).filter(|&k| permitted[cell_of[k]]).count();
    let mut weight = vec![0usize; cells];
    for &c in &cell_of {
        weight[c] += 1;
    }
    // Roots: the start seen from White, and the start seen from Black
    // (= its colour-swapped image with Black to move), both white-relative.
    let start = cert::start(setup);
    let mut swapped = start.clone();
    for (a, b) in [(roles.own_k, roles.opp_k), (roles.own_r, roles.opp_r)] {
        swapped.sqs.swap(a as usize, b as usize);
    }
    swapped.stm = Color::Black;
    let ok = |p: &Position| {
        let v: Vec<i32> = vocab.iter().map(|&f| cert::feature(setup, p, p.stm, &roles, f).unwrap()).collect();
        cell_id.get(&v).is_some_and(|&c| permitted[c])
    };
    let roots_ok = [ok(&start), ok(&swapped)];
    // Exact tree over the cells, then a DAG.
    let mut tree_nodes = 0;
    let tree = fit(&cell_vec, &permitted, &weight, (0..cells).collect(), &mut tree_nodes);
    let mut nodes = Vec::new();
    let root = cons(&tree, vocab, &mut nodes, &mut HashMap::new());
    Synthesis {
        vocab: vocab.to_vec(),
        cells,
        rounds: removed_by_round.len(),
        removed_by_round,
        safe_cells: permitted.iter().filter(|&&b| b).count(),
        safe_states,
        roots_ok,
        tree_nodes,
        cert: Cert { board: setup.n, root, nodes },
    }
}

/// The certificate in codex_idea's JSON format.
pub fn to_json(c: &Cert, vocab: &[usize]) -> String {
    let nodes: Vec<String> = c.nodes.iter().map(|n| format!("[{},{},{},{}]", n[0], n[1], n[2], n[3])).collect();
    let names: Vec<String> = vocab.iter().map(|&f| format!("\"{}\"", FEATURE_NAMES[f])).collect();
    format!(
        "{{\"format\":\"mini-rook-safety-dag-v1\",\"board\":{},\"root\":{},\"nodes\":[{}],\"vocabulary\":[{}]}}",
        c.board, c.root, nodes.join(","), names.join(",")
    )
}
