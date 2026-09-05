//! Retrograde ground truth: every position of a material setup, solved to
//! win/draw/loss with distance-to-mate by forward fixpoint iteration.
//!
//! Semantics: checkmate = loss for the side to move; stalemate = draw;
//! kings only = draw; no move-count rules. Values are the infinite-game
//! values, as in standard tablebases.

use crate::board::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Val {
    /// Not a legal position (never reached).
    Illegal,
    /// Not yet decided during solving; a draw once solving has converged.
    Draw,
    /// Side to move mates in `d` plies (d odd for the actual mate, but counted in plies).
    Win(u16),
    /// Side to move is mated in `d` plies.
    Loss(u16),
}

pub struct Table {
    pub setup: Setup,
    pub vals: Vec<Val>,
    pub passes: u32,
    /// Oracle queries spent by the solve (legality + one move generation per position).
    pub queries: u64,
}

/// A position wrapper that counts oracle queries.
struct Counting<'a> {
    p: &'a Position,
    n: &'a std::cell::Cell<u64>,
}
impl Oracle for Counting<'_> {
    fn at(&self, sq: Sq) -> Res<Option<SlotId>> {
        self.n.set(self.n.get() + 1);
        self.p.at(sq)
    }
    fn locate(&self, s: SlotId) -> Res<Option<Sq>> {
        self.n.set(self.n.get() + 1);
        self.p.locate(s)
    }
}

impl Table {
    pub fn radix(setup: &Setup) -> usize {
        setup.area() + 1
    }

    pub fn size(setup: &Setup) -> usize {
        2 * Self::radix(setup).pow(setup.slots.len() as u32)
    }

    pub fn index(setup: &Setup, p: &Position) -> usize {
        let radix = Self::radix(setup);
        let mut i = 0usize;
        for &sq in p.sqs.iter().rev() {
            i = i * radix + sq.map(|s| s as usize).unwrap_or(radix - 1);
        }
        i * 2 + p.stm.idx()
    }

    pub fn position(setup: &Setup, mut i: usize) -> Position {
        let radix = Self::radix(setup);
        let stm = if i % 2 == 0 { Color::White } else { Color::Black };
        i /= 2;
        let mut sqs = Vec::with_capacity(setup.slots.len());
        for _ in 0..setup.slots.len() {
            let v = i % radix;
            i /= radix;
            sqs.push(if v == radix - 1 { None } else { Some(v as Sq) });
        }
        Position { sqs, stm }
    }

    pub fn get(&self, p: &Position) -> Val {
        self.vals[Self::index(&self.setup, p)]
    }

    /// Solve by iterating to a fixpoint. Pass k discovers Win(k) and Loss(k).
    pub fn solve(setup: Setup) -> Table {
        let size = Self::size(&setup);
        let mut vals = vec![Val::Illegal; size];
        let mut legal: Vec<usize> = Vec::new();
        let mut moves: Vec<Vec<usize>> = Vec::new(); // successor indices per legal position, parallel to `legal`
        let nq = std::cell::Cell::new(0u64);
        // Pass 0: legality, terminal positions, successor lists.
        for i in 0..size {
            let p = Self::position(&setup, i);
            let o = Counting { p: &p, n: &nq };
            if !p.is_legal_via(&setup, &o) {
                continue;
            }
            if p.only_kings(&setup) {
                vals[i] = Val::Draw;
                continue;
            }
            let lm = legal_moves(&setup, &o, p.stm).unwrap();
            if lm.is_empty() {
                vals[i] = if in_check(&setup, &o, p.stm).unwrap() { Val::Loss(0) } else { Val::Draw };
                continue;
            }
            vals[i] = Val::Draw;
            legal.push(i);
            moves.push(lm.iter().map(|&m| Self::index(&setup, &p.play(m))).collect());
        }
        let mut undecided: Vec<usize> = (0..legal.len()).collect();
        let mut passes = 0;
        loop {
            passes += 1;
            // Pass p finds Win(2p-1) and Loss(2p): each pass adds one
            // white-move/black-move ply pair to the longest known mate.
            let d: u16 = 2 * passes as u16 - 1;
            let mut changed = false;
            // Wins in d: some successor is a loss in < d.
            let mut new_wins = Vec::new();
            for &k in &undecided {
                if moves[k].iter().any(|&j| matches!(vals[j], Val::Loss(m) if m < d)) {
                    new_wins.push(k);
                }
            }
            for &k in &new_wins {
                vals[legal[k]] = Val::Win(d);
                changed = true;
            }
            undecided.retain(|k| !matches!(vals[legal[*k]], Val::Win(_)));
            // Losses in d+1: every successor is a win (in <= d); at least one is
            // exactly d, else this would have been found in an earlier pass.
            let mut new_losses = Vec::new();
            for &k in &undecided {
                if moves[k].iter().all(|&j| matches!(vals[j], Val::Win(_))) {
                    new_losses.push(k);
                }
            }
            for &k in &new_losses {
                vals[legal[k]] = Val::Loss(d + 1);
                changed = true;
            }
            undecided.retain(|k| !matches!(vals[legal[*k]], Val::Loss(_)));
            if !changed {
                break;
            }
        }
        Table { setup, vals, passes, queries: nq.get() }
    }

    /// Full self-consistency check of the solved table against forward move
    /// generation. Returns the first violation found, as text.
    pub fn verify(&self) -> Result<(), String> {
        let setup = &self.setup;
        for (i, &v) in self.vals.iter().enumerate() {
            if v == Val::Illegal {
                continue;
            }
            let p = Self::position(setup, i);
            if !p.is_legal(setup) {
                return Err(format!("index {i} marked {v:?} but illegal"));
            }
            if p.only_kings(setup) {
                if v != Val::Draw {
                    return Err(format!("kings-only position {i} is {v:?}"));
                }
                continue;
            }
            let lm = legal_moves(setup, &p, p.stm).unwrap();
            let succ: Vec<Val> = lm.iter().map(|&m| self.get(&p.play(m))).collect();
            if succ.iter().any(|s| *s == Val::Illegal) {
                return Err(format!("position {i} has an illegal successor"));
            }
            let check = in_check(setup, &p, p.stm).unwrap();
            match v {
                Val::Illegal => unreachable!(),
                Val::Draw => {
                    if lm.is_empty() && check {
                        return Err(format!("position {i} is checkmated but marked Draw"));
                    }
                    if succ.iter().any(|s| matches!(s, Val::Loss(_))) {
                        return Err(format!("position {i} is Draw but can move to a Loss"));
                    }
                    if !lm.is_empty() && succ.iter().all(|s| matches!(s, Val::Win(_))) {
                        return Err(format!("position {i} is Draw but every move loses"));
                    }
                }
                Val::Win(d) => {
                    let best = succ
                        .iter()
                        .filter_map(|s| if let Val::Loss(m) = s { Some(*m) } else { None })
                        .min();
                    if best != Some(d - 1) {
                        return Err(format!("position {i} Win({d}) but best successor loss is {best:?}"));
                    }
                }
                Val::Loss(d) => {
                    if d == 0 {
                        if !(lm.is_empty() && check) {
                            return Err(format!("position {i} Loss(0) but not checkmated"));
                        }
                        continue;
                    }
                    if lm.is_empty() {
                        return Err(format!("position {i} Loss({d}) with no moves"));
                    }
                    let worst = succ
                        .iter()
                        .map(|s| if let Val::Win(m) = s { Some(*m) } else { None })
                        .collect::<Option<Vec<u16>>>()
                        .and_then(|w| w.into_iter().max());
                    if worst != Some(d - 1) {
                        return Err(format!("position {i} Loss({d}) but successors give {worst:?}"));
                    }
                }
            }
        }
        Ok(())
    }

    /// Principal variation from `p` (best play for both sides by DTM).
    pub fn pv(&self, p: &Position) -> Vec<Move> {
        let setup = &self.setup;
        let mut out = Vec::new();
        let mut cur = p.clone();
        loop {
            let v = self.get(&cur);
            let lm = legal_moves(setup, &cur, cur.stm).unwrap();
            let pick = match v {
                Val::Win(d) => lm.iter().copied().find(|&m| self.get(&cur.play(m)) == Val::Loss(d - 1)),
                Val::Loss(d) if d > 0 => lm.iter().copied().find(|&m| self.get(&cur.play(m)) == Val::Win(d - 1)),
                _ => None,
            };
            match pick {
                Some(m) => {
                    out.push(m);
                    cur = cur.play(m);
                }
                None => return out,
            }
        }
    }
}

#[derive(Default, Debug)]
pub struct Stats {
    pub slots: usize,
    pub legal: usize,
    pub canonical: usize,
    pub wins: [usize; 2],
    pub losses: [usize; 2],
    pub draws: [usize; 2],
    pub max_dtm: u16,
    pub dtm_hist: Vec<usize>,
    pub longest: Option<Position>,
}

impl Table {
    pub fn stats(&self) -> Stats {
        let setup = &self.setup;
        let syms = setup.symmetries();
        let mut st = Stats { slots: self.vals.len(), ..Default::default() };
        let mut seen = vec![false; self.vals.len()];
        for (i, &v) in self.vals.iter().enumerate() {
            if v == Val::Illegal {
                continue;
            }
            st.legal += 1;
            let p = Self::position(setup, i);
            let canon = syms.iter().map(|m| Self::index(setup, &p.transform(m))).min().unwrap();
            if !seen[canon] {
                seen[canon] = true;
                st.canonical += 1;
            }
            let c = p.stm.idx();
            match v {
                Val::Win(d) | Val::Loss(d) => {
                    if let Val::Win(_) = v { st.wins[c] += 1 } else { st.losses[c] += 1 }
                    if st.dtm_hist.len() <= d as usize {
                        st.dtm_hist.resize(d as usize + 1, 0);
                    }
                    st.dtm_hist[d as usize] += 1;
                    if d > st.max_dtm || st.longest.is_none() {
                        st.max_dtm = d;
                        st.longest = Some(p);
                    }
                }
                Val::Draw => st.draws[c] += 1,
                Val::Illegal => {}
            }
        }
        st
    }
}

/// Sizes of the proof of a won position, as a DAG over concrete positions:
/// at the winner's nodes one DTM-optimal move, at the loser's nodes every
/// legal reply. `reachable` is the set of positions reachable from `p` under
/// any play, for comparison.
pub struct ProofSize {
    pub proof_positions: usize,
    pub reachable: usize,
}

impl Table {
    pub fn proof_size(&self, p: &Position) -> ProofSize {
        let setup = &self.setup;
        let winner = match self.get(p) {
            Val::Win(_) => p.stm,
            Val::Loss(_) => p.stm.flip(),
            _ => return ProofSize { proof_positions: 0, reachable: self.reachable(p) },
        };
        let mut seen = vec![false; self.vals.len()];
        let mut stack = vec![p.clone()];
        let mut count = 0;
        while let Some(cur) = stack.pop() {
            let i = Self::index(setup, &cur);
            if seen[i] {
                continue;
            }
            seen[i] = true;
            count += 1;
            let lm = legal_moves(setup, &cur, cur.stm).unwrap();
            if cur.stm == winner {
                if let Val::Win(d) = self.get(&cur) {
                    let m = lm
                        .iter()
                        .copied()
                        .find(|&m| self.get(&cur.play(m)) == Val::Loss(d - 1))
                        .expect("winning move");
                    stack.push(cur.play(m));
                }
            } else {
                for m in lm {
                    stack.push(cur.play(m));
                }
            }
        }
        ProofSize { proof_positions: count, reachable: self.reachable(p) }
    }

    pub fn reachable(&self, p: &Position) -> usize {
        let setup = &self.setup;
        let mut seen = vec![false; self.vals.len()];
        let mut stack = vec![p.clone()];
        let mut count = 0;
        while let Some(cur) = stack.pop() {
            let i = Self::index(setup, &cur);
            if seen[i] {
                continue;
            }
            seen[i] = true;
            count += 1;
            if cur.only_kings(setup) {
                continue;
            }
            for m in legal_moves(setup, &cur, cur.stm).unwrap() {
                stack.push(cur.play(m));
            }
        }
        count
    }
}
