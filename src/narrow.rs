//! The superposed engine: evaluate the game value over a *region* (a set of
//! positions given as one square-domain per slot) by running the ordinary
//! move generator against an oracle that answers only what the region
//! decides, and forking the region when a query is undecided.
//!
//! Every decided answer is recorded into a *pattern*: the conjunction of
//! facts the verdict depended on, itself a product of per-slot domains. A
//! verdict therefore holds for every position matching its pattern, not just
//! for the region that produced it — this is the consulted-set memo of the
//! shard playground, with squares as the holes.

use crate::board::*;
use std::cell::RefCell;
use std::collections::HashMap;

/// Where a slot may be: a set of squares, and possibly captured.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Dom {
    pub sq: u64,
    pub cap: bool,
}

impl Dom {
    pub fn full(setup: &Setup, may_capture: bool) -> Dom {
        let area = setup.area();
        let sq = if area == 64 { u64::MAX } else { (1u64 << area) - 1 };
        Dom { sq, cap: may_capture }
    }
    pub fn pinned(sq: Sq) -> Dom {
        Dom { sq: 1 << sq, cap: false }
    }
    pub fn captured() -> Dom {
        Dom { sq: 0, cap: true }
    }
    pub fn is_empty(self) -> bool {
        self.sq == 0 && !self.cap
    }
    pub fn has(self, sq: Sq) -> bool {
        self.sq & (1 << sq) != 0
    }
    pub fn is_pinned(self) -> Option<Sq> {
        if !self.cap && self.sq.count_ones() == 1 { Some(self.sq.trailing_zeros() as Sq) } else { None }
    }
    pub fn is_captured(self) -> bool {
        self.sq == 0 && self.cap
    }
    pub fn subset_of(self, other: Dom) -> bool {
        self.sq & !other.sq == 0 && (!self.cap || other.cap)
    }
    pub fn meet(self, other: Dom) -> Dom {
        Dom { sq: self.sq & other.sq, cap: self.cap && other.cap }
    }
    pub fn size(self) -> usize {
        self.sq.count_ones() as usize + self.cap as usize
    }
    pub fn squares(self) -> impl Iterator<Item = Sq> {
        let mut bits = self.sq;
        std::iter::from_fn(move || {
            if bits == 0 {
                None
            } else {
                let s = bits.trailing_zeros() as Sq;
                bits &= bits - 1;
                Some(s)
            }
        })
    }
}

/// A set of positions: every assignment of slots to distinct squares within
/// the domains, with `stm` to move. Kept normalized: a pinned square is
/// excluded from every other slot's domain.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Region {
    pub dom: Vec<Dom>,
    pub stm: Color,
}

impl Region {
    pub fn root(setup: &Setup, stm: Color) -> Region {
        let dom = (0..setup.slots.len() as SlotId)
            .map(|s| Dom::full(setup, setup.kind(s) != Kind::King))
            .collect();
        Region { dom, stm }
    }

    pub fn is_empty(&self) -> bool {
        self.dom.iter().any(|d| d.is_empty())
    }

    /// Propagate pinned squares out of the other domains until stable.
    /// Returns false if the region became empty.
    pub fn normalize(&mut self) -> bool {
        loop {
            let mut changed = false;
            for k in 0..self.dom.len() {
                if let Some(sq) = self.dom[k].is_pinned() {
                    for j in 0..self.dom.len() {
                        if j != k && self.dom[j].has(sq) {
                            self.dom[j].sq &= !(1 << sq);
                            changed = true;
                        }
                    }
                }
            }
            if self.is_empty() {
                return false;
            }
            if !changed {
                return true;
            }
        }
    }

    fn with(&self, f: impl FnOnce(&mut Region)) -> Option<Region> {
        let mut r = self.clone();
        f(&mut r);
        if r.normalize() { Some(r) } else { None }
    }

    /// Split the region on an undecided query into disjoint children.
    pub fn fork(&self, q: Blocked) -> Vec<Region> {
        let mut out = Vec::new();
        match q {
            Blocked::At(sq) => {
                for k in 0..self.dom.len() {
                    if self.dom[k].has(sq) {
                        out.extend(self.with(|r| r.dom[k] = Dom::pinned(sq)));
                    }
                }
                out.extend(self.with(|r| {
                    for d in r.dom.iter_mut() {
                        d.sq &= !(1 << sq);
                    }
                }));
            }
            Blocked::Locate(k) => {
                let k = k as usize;
                for sq in self.dom[k].squares() {
                    out.extend(self.with(|r| r.dom[k] = Dom::pinned(sq)));
                }
                if self.dom[k].cap {
                    out.extend(self.with(|r| r.dom[k] = Dom::captured()));
                }
            }
        }
        out
    }

    /// The region after `mv` (which the oracle decided is legal throughout).
    pub fn play(&self, mv: Move) -> Region {
        let mut r = self.clone();
        r.dom[mv.slot as usize] = Dom::pinned(mv.to);
        if let Some(c) = mv.capture {
            r.dom[c as usize] = Dom::captured();
        }
        r.stm = self.stm.flip();
        assert!(r.normalize());
        r
    }

    /// Undo `mv` on a sub-region of `self.play(mv)`.
    pub fn pullback(child: &Region, mv: Move) -> Region {
        let mut r = child.clone();
        r.dom[mv.slot as usize] = Dom::pinned(mv.from);
        if let Some(c) = mv.capture {
            r.dom[c as usize] = Dom::pinned(mv.to);
        }
        r.stm = child.stm.flip();
        assert!(r.normalize());
        r
    }

    /// Every distinct assignment in the region (no legality filtering).
    pub fn positions(&self) -> Vec<Position> {
        let mut out = Vec::new();
        let mut sqs: Vec<Option<Sq>> = Vec::with_capacity(self.dom.len());
        self.enumerate(0, &mut sqs, &mut out);
        out
    }
    fn enumerate(&self, k: usize, sqs: &mut Vec<Option<Sq>>, out: &mut Vec<Position>) {
        if k == self.dom.len() {
            out.push(Position { sqs: sqs.clone(), stm: self.stm });
            return;
        }
        for sq in self.dom[k].squares() {
            if sqs.contains(&Some(sq)) {
                continue;
            }
            sqs.push(Some(sq));
            self.enumerate(k + 1, sqs, out);
            sqs.pop();
        }
        if self.dom[k].cap {
            sqs.push(None);
            self.enumerate(k + 1, sqs, out);
            sqs.pop();
        }
    }

    pub fn only_kings(&self, setup: &Setup) -> bool {
        (0..self.dom.len()).all(|s| setup.kind(s as SlotId) == Kind::King || self.dom[s].is_captured())
    }
}

/// The facts a verdict consulted, as the set of positions satisfying them.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Pattern {
    pub dom: Vec<Dom>,
}

impl Pattern {
    pub fn full(setup: &Setup) -> Pattern {
        Pattern { dom: (0..setup.slots.len()).map(|_| Dom::full(setup, true)).collect() }
    }
    /// The facts "every non-king slot is captured".
    pub fn kings_only(setup: &Setup) -> Pattern {
        let mut p = Pattern::full(setup);
        for s in 0..setup.slots.len() {
            if setup.kind(s as SlotId) != Kind::King {
                p.dom[s] = Dom::captured();
            }
        }
        p
    }
    pub fn covers(&self, r: &Region) -> bool {
        r.dom.iter().zip(&self.dom).all(|(a, b)| a.subset_of(*b))
    }
    pub fn covers_position(&self, p: &Position) -> bool {
        p.sqs.iter().zip(&self.dom).all(|(s, d)| match s {
            Some(sq) => d.has(*sq),
            None => d.cap,
        })
    }
    /// Conjunction of two fact sets.
    pub fn meet(&self, other: &Pattern) -> Pattern {
        Pattern { dom: self.dom.iter().zip(&other.dom).map(|(a, b)| a.meet(*b)).collect() }
    }
    pub fn record_at(&mut self, sq: Sq, ans: Option<SlotId>) {
        match ans {
            Some(k) => self.dom[k as usize] = Dom::pinned(sq),
            None => {
                for d in self.dom.iter_mut() {
                    d.sq &= !(1 << sq);
                }
            }
        }
    }
    pub fn record_locate(&mut self, k: SlotId, ans: Option<Sq>) {
        self.dom[k as usize] = match ans {
            Some(sq) => Dom::pinned(sq),
            None => Dom::captured(),
        };
    }
    /// Facts about the position after `mv`, restated about the position before.
    pub fn pullback(&self, mv: Move) -> Pattern {
        let mut p = self.clone();
        p.dom[mv.slot as usize] = Dom::pinned(mv.from);
        if let Some(c) = mv.capture {
            p.dom[c as usize] = Dom::pinned(mv.to);
        }
        p
    }
    pub fn size(&self) -> f64 {
        self.dom.iter().map(|d| d.size() as f64).product()
    }
}

/// Oracle over a region that records every decided answer.
pub struct Rec<'a> {
    pub r: &'a Region,
    pub log: RefCell<Pattern>,
    pub queries: &'a std::cell::Cell<u64>,
}

impl Oracle for Rec<'_> {
    fn at(&self, sq: Sq) -> Res<Option<SlotId>> {
        let mut holder = None;
        for (k, d) in self.r.dom.iter().enumerate() {
            if d.has(sq) {
                if d.is_pinned().is_some() {
                    holder = Some(k as SlotId);
                } else {
                    return Err(Blocked::At(sq));
                }
            }
        }
        self.queries.set(self.queries.get() + 1);
        self.log.borrow_mut().record_at(sq, holder);
        Ok(holder)
    }
    fn locate(&self, s: SlotId) -> Res<Option<Sq>> {
        let d = self.r.dom[s as usize];
        let ans = if let Some(sq) = d.is_pinned() {
            Some(sq)
        } else if d.is_captured() {
            None
        } else {
            return Err(Blocked::Locate(s));
        };
        self.queries.set(self.queries.get() + 1);
        self.log.borrow_mut().record_locate(s, ans);
        Ok(ans)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Verdict {
    Illegal,
    Win(u16),
    Loss(u16),
    Draw,
}

#[derive(Clone, Debug)]
pub struct Leaf {
    pub region: Region,
    pub verdict: Verdict,
    pub pattern: Pattern,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Q {
    MateIn,
    MatedIn,
}

#[derive(Default, Debug, Clone)]
pub struct Counters {
    pub queries: u64,
    pub forks: u64,
    pub nodes: u64,
    pub memo_hits: u64,
    pub memo_entries: u64,
}

pub struct Engine {
    pub setup: Setup,
    pub counters: Counters,
    queries: std::cell::Cell<u64>,
    memo: HashMap<(Q, u16, Color), Vec<(Pattern, bool)>>,
    pub use_memo: bool,
    /// Try the slots in reverse order (e.g. rook before king).
    pub reverse_slots: bool,
}

/// A bool-valued partition of a region, each part with the facts it used.
type Parts = Vec<(Region, bool, Pattern)>;

/// Facts sufficient for `mv` to be a legal move: the mover's location, the
/// squares it passes over and lands on, and the safety of the own king
/// afterwards. Re-derived on a region where those queries are decided.
fn move_facts(setup: &Setup, r: &Region, mv: Move, queries: &std::cell::Cell<u64>) -> Pattern {
    let rec = Rec { r, log: RefCell::new(Pattern::full(setup)), queries };
    let go = || -> Res<()> {
        rec.locate(mv.slot)?;
        let (f0, r0) = setup.file_rank(mv.from);
        let (f1, r1) = setup.file_rank(mv.to);
        let (df, dr) = ((f1 - f0).signum(), (r1 - r0).signum());
        let slides = !matches!(setup.kind(mv.slot), Kind::King | Kind::Knight);
        if slides {
            let mut cur = mv.from;
            loop {
                cur = setup.step(cur, df, dr).expect("ray stays on board");
                if cur == mv.to {
                    break;
                }
                rec.at(cur)?;
            }
        }
        rec.at(mv.to)?;
        let after = Played { base: &rec, mv };
        in_check(setup, &after, setup.color(mv.slot))?;
        Ok(())
    };
    go().expect("move facts are decided on a region where the move was generated");
    rec.log.into_inner()
}

/// Legal moves of one slot only.
fn slot_moves<O: Oracle>(setup: &Setup, o: &O, s: SlotId) -> Res<Vec<Move>> {
    let Some(from) = o.locate(s)? else { return Ok(Vec::new()) };
    let mut pseudo = Vec::new();
    piece_moves(setup, o, s, from, &mut pseudo)?;
    let mut legal = Vec::with_capacity(pseudo.len());
    for mv in pseudo {
        let after = Played { base: o, mv };
        if !in_check(setup, &after, setup.color(s))? {
            legal.push(mv);
        }
    }
    Ok(legal)
}

impl Engine {
    pub fn new(setup: Setup) -> Engine {
        Engine {
            setup,
            counters: Counters::default(),
            queries: Default::default(),
            memo: HashMap::new(),
            use_memo: true,
            reverse_slots: false,
        }
    }

    fn lookup(&mut self, q: Q, d: u16, r: &Region) -> Option<(bool, Pattern)> {
        if !self.use_memo {
            return None;
        }
        let entries = self.memo.get(&(q, d, r.stm))?;
        for (p, v) in entries {
            if p.covers(r) {
                self.counters.memo_hits += 1;
                return Some((*v, p.clone()));
            }
        }
        None
    }

    fn store(&mut self, q: Q, d: u16, stm: Color, parts: &Parts) {
        if !self.use_memo {
            return;
        }
        let entries = self.memo.entry((q, d, stm)).or_default();
        for (_, v, p) in parts {
            if !entries.iter().any(|(e, _)| e == p) {
                entries.push((p.clone(), *v));
                self.counters.memo_entries += 1;
            }
        }
    }

    /// Run `f` against a recording oracle on `r`. On a block, fork and
    /// return the children; otherwise return the result and the facts used.
    fn consult<T>(&mut self, r: &Region, f: impl Fn(&Rec) -> Res<T>) -> Result<(T, Pattern), Vec<Region>> {
        let rec = Rec { r, log: RefCell::new(Pattern::full(&self.setup)), queries: &self.queries };
        match f(&rec) {
            Ok(t) => Ok((t, rec.log.into_inner())),
            Err(q) => {
                self.counters.forks += 1;
                Err(r.fork(q))
            }
        }
    }

    fn mate_in(&mut self, r: Region, d: u16) -> Parts {
        self.search(r, d, Q::MateIn)
    }

    fn mated_in(&mut self, r: Region, d: u16) -> Parts {
        self.search(r, d, Q::MatedIn)
    }

    /// `MateIn`: can the side to move force mate within `d` plies?
    /// `MatedIn`: is the side to move mated within `d` plies (mated now counts)?
    ///
    /// Both are one AND/OR search: moves are generated one slot at a time and
    /// tried at once, so the region forks only on what the tried move needs.
    /// An "any" verdict (a mating move, an escape) keeps only that move's
    /// facts and its child's pattern; an "all" verdict keeps everything.
    fn search(&mut self, r: Region, d: u16, q: Q) -> Parts {
        self.counters.nodes += 1;
        let setup = self.setup.clone();
        if q == Q::MateIn && d == 0 {
            return vec![(r, false, Pattern::full(&setup))];
        }
        if r.only_kings(&setup) {
            let p = Pattern::kings_only(&setup);
            return vec![(r, false, p)];
        }
        if let Some((v, p)) = self.lookup(q, d, &r) {
            return vec![(r, v, p)];
        }
        let stm = r.stm;
        // The child verdict that settles this node at once, and what it settles it to.
        let (trigger, any_result) = match q {
            Q::MateIn => (true, true),   // a reply that is mated -> we mate
            Q::MatedIn => (false, false), // a reply that is not mated -> we escape
        };
        let other = match q {
            Q::MateIn => Q::MatedIn,
            Q::MatedIn => Q::MateIn,
        };
        let mut slots: Vec<SlotId> = setup.slots_of(stm).collect();
        if self.reverse_slots {
            slots.reverse();
        }
        let mut done: Parts = Vec::new();
        // Sub-regions not yet settled: (region, facts so far, had any legal move).
        let mut cur: Vec<(Region, Pattern, bool)> = vec![(r.clone(), Pattern::full(&setup), false)];
        for s in slots {
            let mut next_cur = Vec::new();
            let mut stack = cur;
            while let Some((sub, acc, had)) = stack.pop() {
                let (moves, facts) = match self.consult(&sub, |o| slot_moves(&setup, o, s)) {
                    Ok(x) => x,
                    Err(children) => {
                        stack.extend(children.into_iter().map(|c| (c, acc.clone(), had)));
                        continue;
                    }
                };
                let had = had || !moves.is_empty();
                let mut rem = vec![(sub, acc.meet(&facts))];
                for mv in moves {
                    let mut nrem = Vec::new();
                    for (sub2, a) in rem {
                        if q == Q::MatedIn && d == 0 {
                            // Any legal move is an escape from mate-now.
                            let mf = move_facts(&setup, &sub2, mv, &self.queries);
                            done.push((sub2, false, mf));
                            continue;
                        }
                        for (child, v, cp) in self.search(sub2.play(mv), d - 1, other) {
                            let back = Region::pullback(&child, mv);
                            let cp = cp.pullback(mv);
                            if v == trigger {
                                let mf = move_facts(&setup, &back, mv, &self.queries);
                                done.push((back, any_result, mf.meet(&cp)));
                            } else {
                                nrem.push((back, a.meet(&cp)));
                            }
                        }
                    }
                    rem = nrem;
                    if rem.is_empty() {
                        break;
                    }
                }
                next_cur.extend(rem.into_iter().map(|(sub, a)| (sub, a, had)));
            }
            cur = next_cur;
        }
        // No settling move anywhere in these: the "all" verdict, or no moves at all.
        for (sub, acc, had) in cur {
            match q {
                Q::MateIn => done.push((sub, false, acc)),
                Q::MatedIn if had => done.push((sub, true, acc)),
                Q::MatedIn => {
                    let mut stack = vec![sub];
                    while let Some(sub) = stack.pop() {
                        match self.consult(&sub, |o| in_check(&setup, o, stm)) {
                            Ok((check, f)) => done.push((sub, check, acc.meet(&f))),
                            Err(children) => stack.extend(children),
                        }
                    }
                }
            }
        }
        self.store(q, d, stm, &done);
        done
    }

    /// Partition `root` by game value, deepening the mate horizon one ply at
    /// a time up to `dmax` (so a Win/Loss leaf carries its exact DTM). Draw
    /// means "no forced mate within dmax" — exact when dmax is the true
    /// maximum DTM of the material.
    pub fn solve(&mut self, root: Region, dmax: u16) -> Vec<Leaf> {
        self.solve_with(root, dmax, false)
    }

    /// `direct`: evaluate the full horizon at once (WDL only, DTM reported
    /// as the horizon) instead of deepening ply by ply.
    pub fn solve_with(&mut self, root: Region, dmax: u16, direct: bool) -> Vec<Leaf> {
        let setup = self.setup.clone();
        let mut leaves = Vec::new();
        // Legality of the side not to move.
        let mut open: Vec<(Region, Pattern)> = Vec::new();
        let mut stack = vec![root];
        while let Some(r) = stack.pop() {
            let not_stm = r.stm.flip();
            match self.consult(&r, |o| in_check(&setup, o, not_stm)) {
                Ok((true, p)) => leaves.push(Leaf { region: r, verdict: Verdict::Illegal, pattern: p }),
                Ok((false, p)) => open.push((r, p)),
                Err(children) => stack.extend(children),
            }
        }
        let win_depths: Vec<u16> = if direct { vec![dmax | 1] } else { (1..=dmax).step_by(2).collect() };
        let loss_depths: Vec<u16> = if direct { vec![dmax & !1] } else { (0..=dmax).step_by(2).collect() };
        // Wins for the side to move, shallowest first.
        for d in win_depths {
            let mut next = Vec::new();
            for (r, acc) in open {
                for (sub, v, p) in self.mate_in(r, d) {
                    if v {
                        leaves.push(Leaf { region: sub, verdict: Verdict::Win(d), pattern: acc.meet(&p) });
                    } else {
                        next.push((sub, acc.meet(&p)));
                    }
                }
            }
            open = next;
        }
        // Losses for the side to move among the rest, shallowest first.
        for d in loss_depths {
            let mut next = Vec::new();
            for (r, acc) in open {
                for (sub, v, p) in self.mated_in(r, d) {
                    if v {
                        leaves.push(Leaf { region: sub, verdict: Verdict::Loss(d), pattern: acc.meet(&p) });
                    } else {
                        next.push((sub, acc.meet(&p)));
                    }
                }
            }
            open = next;
        }
        leaves.extend(open.into_iter().map(|(r, p)| Leaf { region: r, verdict: Verdict::Draw, pattern: p }));
        self.counters.queries = self.queries.get();
        leaves
    }
}
