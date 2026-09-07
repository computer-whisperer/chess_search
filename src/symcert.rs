//! Symbolic check of the codex_idea nonloss certificate: evaluate the
//! feature DAG and its obligations over superposed regions instead of one
//! concrete position at a time. The recording oracle answers what a region
//! decides and forks it on the first undecided query, so every leaf here is
//! a set of positions that the certificate treats identically *for the facts
//! it actually consulted*. The leaf count against the position count
//! measures how far verification can get without enumerating the game.

use crate::absmove;
use crate::board::*;
use crate::cert::{self, Roles};
use crate::certs::Cert;
use crate::narrow::{Dom, Pattern, Rec, Region};
use crate::retro::{Table, Val};
use std::cell::{Cell, RefCell};

/// A region with a boolean answer (membership, or an obligation's outcome).
pub type Parts = Vec<(Region, bool)>;

enum Eval {
    Decided(bool),
    Split(Vec<Region>),
}

/// Whether slot `s` is present on the whole region (`Some`), or undecided.
fn presence(r: &Region, s: SlotId) -> Option<bool> {
    let d = r.dom[s as usize];
    if d.is_captured() { Some(false) } else if !d.cap { Some(true) } else { None }
}

fn restrict(r: &Region, s: SlotId, d: Dom) -> Option<Region> {
    let mut c = r.clone();
    c.dom[s as usize] = d;
    if c.normalize() { Some(c) } else { None }
}

fn split_presence(r: &Region, s: SlotId) -> Vec<Region> {
    let d = r.dom[s as usize];
    [Dom { sq: d.sq, cap: false }, Dom::captured()].into_iter().filter_map(|d| restrict(r, s, d)).collect()
}

/// Split slot `s` (present) into the squares inside `mask` and outside it.
fn split_mask(r: &Region, s: SlotId, mask: u64) -> Vec<Region> {
    let d = r.dom[s as usize];
    [Dom { sq: d.sq & mask, cap: false }, Dom { sq: d.sq & !mask, cap: d.cap }]
        .into_iter()
        .filter_map(|d| restrict(r, s, d))
        .collect()
}

/// Decide a predicate on slot `s`'s square over its domain, or split it.
fn split_by(r: &Region, s: SlotId, pred: impl Fn(Sq) -> bool) -> Eval {
    let d = r.dom[s as usize];
    let mask: u64 = d.squares().filter(|&p| pred(p)).map(|p| 1u64 << p).sum();
    if mask == d.sq {
        Eval::Decided(true)
    } else if mask == 0 {
        Eval::Decided(false)
    } else {
        Eval::Split(split_mask(r, s, mask))
    }
}

/// Decide a predicate on two present slots over the product of their
/// domains; if undecided, split the unpinned side by the predicate when the
/// other is pinned, else pin the smaller domain.
fn split_pair(r: &Region, a: SlotId, b: SlotId, pred: impl Fn(Sq, Sq) -> bool) -> Eval {
    let (da, db) = (r.dom[a as usize], r.dom[b as usize]);
    match (da.is_pinned(), db.is_pinned()) {
        (Some(p), _) => split_by(r, b, |q| pred(p, q)),
        (_, Some(q)) => split_by(r, a, |p| pred(p, q)),
        _ => {
            let mut seen = [false; 2];
            for p in da.squares() {
                for q in db.squares() {
                    if p != q {
                        seen[pred(p, q) as usize] = true;
                    }
                }
            }
            match seen {
                [false, true] => Eval::Decided(true),
                [true, false] => Eval::Decided(false),
                _ => Eval::Split(pin_smaller(r, a, b)),
            }
        }
    }
}

/// Pin the unpinned slot with the smaller domain (never an already pinned one).
fn pin_smaller(r: &Region, a: SlotId, b: SlotId) -> Vec<Region> {
    let (da, db) = (r.dom[a as usize], r.dom[b as usize]);
    let s = match (da.is_pinned(), db.is_pinned()) {
        (Some(_), None) => b,
        (None, Some(_)) => a,
        (None, None) => if da.size() <= db.size() { a } else { b },
        (Some(_), Some(_)) => unreachable!("pin_smaller on two pinned slots"),
    };
    r.dom[s as usize].squares().filter_map(|p| restrict(r, s, Dom::pinned(p))).collect()
}

fn between_mask(setup: &Setup, p: Sq, q: Sq) -> u64 {
    let (px, py) = setup.file_rank(p);
    let (qx, qy) = setup.file_rank(q);
    let (df, dr) = ((qx - px).signum(), (qy - py).signum());
    let mut mask = 0u64;
    let mut cur = setup.step(p, df, dr).unwrap();
    while cur != q {
        mask |= 1 << cur;
        cur = setup.step(cur, df, dr).unwrap();
    }
    mask
}

/// How much of the check runs on regions rather than on pinned positions.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// Everything through the recording oracle: every consulted piece is pinned.
    Pinning,
    /// Geometric features decided by domain splits; moves still generated
    /// through the recording oracle.
    Abstract,
    /// Domain splits for features, legality and move generation; the
    /// obligations refine one disjoint partition move by move.
    AbstractMoves,
    /// As `AbstractMoves`, but every candidate move is analysed on the whole
    /// leaf independently, giving an overlapping cover of witnesses (own
    /// turn) or a list of per-move violations (opponent turn). The cost is
    /// the number of cases, compared against the concrete edge count.
    Cover,
}

pub struct Sym<'a> {
    pub setup: &'a Setup,
    pub cert: &'a Cert,
    pub roles: Roles,
    pub queries: Cell<u64>,
    pub forks: Cell<u64>,
    /// Cover mode: decided move cases plus membership classifications.
    pub cases: Cell<u64>,
    pub witnesses: Cell<u64>,
    pub mode: Mode,
}

impl<'a> Sym<'a> {
    pub fn new(setup: &'a Setup, cert: &'a Cert, protected: Color, mode: Mode) -> Sym<'a> {
        Sym { setup, cert, roles: Roles::new(setup, protected), queries: Cell::new(0), forks: Cell::new(0), cases: Cell::new(0), witnesses: Cell::new(0), mode }
    }

    fn member(&self, r: Region) -> Parts {
        if self.mode == Mode::Pinning { self.classify(r) } else { self.classify_abs(r) }
    }

    /// The legal part of `r` (side not to move not in check).
    pub fn legal_by_mode(&self, r: Region) -> Vec<Region> {
        if self.mode != Mode::AbstractMoves {
            return self.legal(r);
        }
        let king = self.setup.king_slot(r.stm.flip());
        match (absmove::View { r: &r, mover: None, captured: None }).attacked(self.setup, king, r.stm) {
            absmove::Step::Decided(true) => vec![],
            absmove::Step::Decided(false) => vec![r],
            absmove::Step::Split(children) => children.into_iter().flat_map(|c| self.legal_by_mode(c)).collect(),
        }
    }

    fn exists_by_mode(&self, r: Region) -> Parts {
        match self.mode {
            Mode::AbstractMoves => self.exists_safe_abs(r),
            Mode::Cover => self.exists_cover(r),
            _ => self.exists_safe(r),
        }
    }

    fn all_by_mode(&self, r: Region) -> Parts {
        match self.mode {
            Mode::AbstractMoves => self.all_safe_abs(r),
            Mode::Cover => self.all_cover(r),
            _ => self.all_safe(r),
        }
    }

    /// Own turn as an overlapping cover: for each candidate move on the whole
    /// leaf, the sub-regions where it is legal and enters the safe region are
    /// witnesses. Positions under no witness are then settled concretely
    /// (stalemate or violation) and returned as singletons, so the parts
    /// still cover the leaf exactly for the caller's accounting.
    pub fn exists_cover(&self, r: Region) -> Parts {
        let setup = self.setup;
        let mut witnesses: Vec<Region> = Vec::new();
        for (s, t) in self.candidates(r.stm) {
            for (case, legal) in absmove::can_move(setup, r.clone(), s, t) {
                self.cases.set(self.cases.get() + 1);
                let Some(capture) = legal else { continue };
                let succ = absmove::play(setup, &case, s, t, capture);
                for (child, ok) in self.member(succ) {
                    self.cases.set(self.cases.get() + 1);
                    if ok {
                        witnesses.extend(absmove::pullback(setup, &case, &child, s, t, capture));
                    }
                }
            }
        }
        self.witnesses.set(self.witnesses.get() + witnesses.len() as u64);
        // Coverage accounting (concrete): the disjoint parts reported are the
        // witnesses made disjoint by first-witness ownership, plus singletons.
        let mut out: Vec<(Region, bool)> = Vec::new();
        let mut owned: Vec<Vec<Position>> = vec![Vec::new(); witnesses.len()];
        for p in r.positions() {
            match witnesses.iter().position(|w| contains(w, &p)) {
                Some(i) => owned[i].push(p),
                None => {
                    let ok = legal_moves(setup, &p, p.stm).unwrap().is_empty() && !in_check(setup, &p, p.stm).unwrap();
                    out.push((pin_all(&p), ok));
                }
            }
        }
        for (w, ps) in witnesses.into_iter().zip(owned) {
            if ps.is_empty() {
                continue;
            }
            if ps.len() == w.positions().len() {
                out.push((w, true));
            } else {
                out.extend(ps.iter().map(|p| (pin_all(p), true)));
            }
        }
        out
    }

    /// Opponent turn as independent per-move checks: each candidate move's
    /// legal cases whose successor leaves the safe region are violations.
    pub fn all_cover(&self, r: Region) -> Parts {
        let setup = self.setup;
        let mut bad: Vec<Region> = Vec::new();
        for (s, t) in self.candidates(r.stm) {
            for (case, legal) in absmove::can_move(setup, r.clone(), s, t) {
                self.cases.set(self.cases.get() + 1);
                let Some(capture) = legal else { continue };
                let succ = absmove::play(setup, &case, s, t, capture);
                for (child, ok) in self.member(succ) {
                    self.cases.set(self.cases.get() + 1);
                    if !ok {
                        bad.extend(absmove::pullback(setup, &case, &child, s, t, capture));
                    }
                }
            }
        }
        if bad.is_empty() {
            return vec![(r, true)];
        }
        r.positions().into_iter().map(|p| { let b = bad.iter().any(|b| contains(b, &p)); (pin_all(&p), !b) }).collect()
    }

    fn candidates(&self, stm: Color) -> Vec<(SlotId, Sq)> {
        let mut out = Vec::new();
        for s in self.setup.slots_of(stm) {
            for t in 0..self.setup.area() as Sq {
                out.push((s, t));
            }
        }
        out
    }

    /// Protected side to move, with abstract moves: does some legal move
    /// enter the safe region? Regions never touched by a legal move are
    /// stalemates (fine) or checkmates (violations).
    pub fn exists_safe_abs(&self, r: Region) -> Parts {
        let setup = self.setup;
        let mut out = Vec::new();
        // (region, had a legal move)
        let mut remaining: Vec<(Region, bool)> = vec![(r, false)];
        for (s, t) in self.candidates(remaining[0].0.stm) {
            let mut next = Vec::new();
            for (sub, had) in remaining {
                for (case, legal) in absmove::can_move(setup, sub, s, t) {
                    let Some(capture) = legal else {
                        next.push((case, had));
                        continue;
                    };
                    let succ = absmove::play(setup, &case, s, t, capture);
                    for (child, ok) in self.member(succ) {
                        if let Some(back) = absmove::pullback(setup, &case, &child, s, t, capture) {
                            if ok { out.push((back, true)) } else { next.push((back, true)) }
                        }
                    }
                }
            }
            remaining = next;
            if remaining.is_empty() {
                break;
            }
        }
        for (sub, had) in remaining {
            if had {
                out.push((sub, false));
                continue;
            }
            // No legal move at all: stalemate unless in check.
            let king = setup.king_slot(sub.stm);
            let mut stack = vec![sub];
            while let Some(q) = stack.pop() {
                match (absmove::View { r: &q, mover: None, captured: None }).attacked(setup, king, q.stm.flip()) {
                    absmove::Step::Decided(mated) => out.push((q, !mated)),
                    absmove::Step::Split(children) => stack.extend(children),
                }
            }
        }
        out
    }

    /// Opponent to move, with abstract moves: does every legal move stay in
    /// the safe region?
    pub fn all_safe_abs(&self, r: Region) -> Parts {
        let setup = self.setup;
        let mut out = Vec::new();
        let mut remaining = vec![r];
        for (s, t) in self.candidates(remaining[0].stm) {
            let mut next = Vec::new();
            for sub in remaining {
                for (case, legal) in absmove::can_move(setup, sub, s, t) {
                    let Some(capture) = legal else {
                        next.push(case);
                        continue;
                    };
                    let succ = absmove::play(setup, &case, s, t, capture);
                    for (child, ok) in self.member(succ) {
                        if let Some(back) = absmove::pullback(setup, &case, &child, s, t, capture) {
                            if ok { next.push(back) } else { out.push((back, false)) }
                        }
                    }
                }
            }
            remaining = next;
            if remaining.is_empty() {
                break;
            }
        }
        out.extend(remaining.into_iter().map(|s| (s, true)));
        out
    }

    /// Run `f` against the region; on an undecided query, fork.
    fn consult<T>(&self, r: &Region, f: impl Fn(&Rec) -> Res<T>) -> Result<T, Vec<Region>> {
        let rec = Rec { r, log: RefCell::new(Pattern::full(self.setup)), queries: &self.queries };
        f(&rec).map_err(|q| {
            self.forks.set(self.forks.get() + 1);
            r.fork(q)
        })
    }

    /// Partition `r` by certificate membership.
    pub fn classify(&self, r: Region) -> Parts {
        match self.consult(&r, |o| cert::evaluate(self.setup, self.cert, o, r.stm, &self.roles)) {
            Ok(b) => vec![(r, b)],
            Err(children) => children.into_iter().flat_map(|c| self.classify(c)).collect(),
        }
    }

    /// Partition `r` by certificate membership, deciding geometric features
    /// abstractly over the domain product (splitting a domain by the tested
    /// predicate) and falling back to the recording oracle for the rest.
    pub fn classify_abs(&self, r: Region) -> Parts {
        self.classify_from(r, self.cert.root)
    }

    fn classify_from(&self, r: Region, mut node: u32) -> Parts {
        while node >= 2 {
            let [feat, thr, l, rt] = self.cert.nodes[node as usize - 2];
            match self.test(&r, feat as usize, thr) {
                Eval::Decided(b) => node = if b { l } else { rt } as u32,
                Eval::Split(children) => {
                    return children.into_iter().flat_map(|c| self.classify_from(c, node)).collect();
                }
            }
        }
        vec![(r, node == 1)]
    }

    /// Is `feature <= thr` decided on the whole region? If not, split it.
    fn test(&self, r: &Region, feat: usize, thr: i32) -> Eval {
        let setup = self.setup;
        let n = setup.n as i32;
        let roles = &self.roles;
        let le = |v: i32| Eval::Decided(v <= thr);
        match feat {
            0 => le((r.stm != roles.protected) as i32),
            1 | 2 => {
                let s = if feat == 1 { roles.own_r } else { roles.opp_r };
                match presence(r, s) {
                    Some(present) => le(!present as i32),
                    None => Eval::Split(split_presence(r, s)),
                }
            }
            3..=10 => {
                let s = cert::piece_slots(roles)[(feat - 3) / 2];
                let edge = (feat - 3) % 2 == 0;
                match presence(r, s) {
                    None => Eval::Split(split_presence(r, s)),
                    Some(false) => le(if edge { -1 } else { 0 }),
                    Some(true) => split_by(r, s, |p| {
                        let (x, y) = setup.file_rank(p);
                        let v = if edge {
                            x.min(y).min(n - 1 - x).min(n - 1 - y)
                        } else {
                            ((x == 0 || x == n - 1) && (y == 0 || y == n - 1)) as i32
                        };
                        v <= thr
                    }),
                }
            }
            11..=28 => {
                let (a, b) = cert::pair_slots(roles)[(feat - 11) / 3];
                let kind = (feat - 11) % 3;
                for s in [a, b] {
                    match presence(r, s) {
                        None => return Eval::Split(split_presence(r, s)),
                        Some(false) => return le(if kind == 0 { 99 } else { 0 }),
                        Some(true) => {}
                    }
                }
                if kind == 2 {
                    return self.test_clear(r, a, b, thr);
                }
                let val = |p: Sq, q: Sq| -> i32 {
                    if kind == 0 { cert::distance(setup, p, q) } else { cert::aligned(setup, p, q) as i32 }
                };
                split_pair(r, a, b, |p, q| val(p, q) <= thr)
            }
            _ => match self.consult(r, |o| cert::feature(setup, o, r.stm, roles, feat)) {
                Ok(v) => le(v),
                Err(children) => Eval::Split(children),
            },
        }
    }

    /// `clear_ray(a, b) <= thr` with both present: aligned and nothing
    /// strictly between. Splits a blocker's domain on the between-set when
    /// that decides it.
    fn test_clear(&self, r: &Region, a: SlotId, b: SlotId, thr: i32) -> Eval {
        let setup = self.setup;
        let (da, db) = (r.dom[a as usize], r.dom[b as usize]);
        match (da.is_pinned(), db.is_pinned()) {
            (Some(p), Some(q)) => {
                if !cert::aligned(setup, p, q) {
                    return Eval::Decided(0 <= thr);
                }
                let between = between_mask(setup, p, q);
                let mut candidate = None;
                for (c, d) in r.dom.iter().enumerate() {
                    if c == a as usize || c == b as usize || d.sq & between == 0 {
                        continue;
                    }
                    if d.sq & !between == 0 && !d.cap {
                        return Eval::Decided(0 <= thr); // a blocker is certainly between
                    }
                    candidate.get_or_insert(c);
                }
                match candidate {
                    None => Eval::Decided(1 <= thr),
                    Some(c) => Eval::Split(split_mask(r, c as SlotId, between)),
                }
            }
            _ => {
                // Decided if no assignment is even aligned; otherwise pin the
                // smaller domain.
                let any_aligned = da.squares().any(|p| db.squares().any(|q| p != q && cert::aligned(setup, p, q)));
                if !any_aligned {
                    return Eval::Decided(0 <= thr);
                }
                Eval::Split(pin_smaller(r, a, b))
            }
        }
    }

    /// Drop the positions where the side not to move is in check (illegal).
    pub fn legal(&self, r: Region) -> Vec<Region> {
        match self.consult(&r, |o| in_check(self.setup, o, r.stm.flip())) {
            Ok(true) => vec![],
            Ok(false) => vec![r],
            Err(children) => children.into_iter().flat_map(|c| self.legal(c)).collect(),
        }
    }

    /// Protected side to move: is there a legal move into the safe region?
    /// A stalemate counts as satisfied; a checkmate does not.
    pub fn exists_safe(&self, r: Region) -> Parts {
        let moves = match self.consult(&r, |o| legal_moves(self.setup, o, r.stm)) {
            Ok(m) => m,
            Err(children) => return children.into_iter().flat_map(|c| self.exists_safe(c)).collect(),
        };
        if moves.is_empty() {
            return match self.consult(&r, |o| in_check(self.setup, o, r.stm)) {
                Ok(mated) => vec![(r, !mated)],
                Err(children) => children.into_iter().flat_map(|c| self.exists_safe(c)).collect(),
            };
        }
        let mut out = Vec::new();
        let mut remaining = vec![r];
        for mv in moves {
            let mut next = Vec::new();
            for sub in remaining {
                for (child, ok) in self.member(sub.play(mv)) {
                    let back = Region::pullback(&child, mv);
                    if ok { out.push((back, true)) } else { next.push(back) }
                }
            }
            remaining = next;
            if remaining.is_empty() {
                break;
            }
        }
        out.extend(remaining.into_iter().map(|s| (s, false)));
        out
    }

    /// Opponent to move: does every legal move stay in the safe region?
    pub fn all_safe(&self, r: Region) -> Parts {
        let moves = match self.consult(&r, |o| legal_moves(self.setup, o, r.stm)) {
            Ok(m) => m,
            Err(children) => return children.into_iter().flat_map(|c| self.all_safe(c)).collect(),
        };
        let mut out = Vec::new();
        let mut remaining = vec![r];
        for mv in moves {
            let mut next = Vec::new();
            for sub in remaining {
                for (child, ok) in self.member(sub.play(mv)) {
                    let back = Region::pullback(&child, mv);
                    if ok { next.push(back) } else { out.push((back, false)) }
                }
            }
            remaining = next;
            if remaining.is_empty() {
                break;
            }
        }
        out.extend(remaining.into_iter().map(|s| (s, true)));
        out
    }
}

#[derive(Default, Debug, Clone)]
pub struct SymReport {
    pub protected: Option<Color>,
    pub legal_positions: usize,
    /// Membership partition of the legal positions (leaves holding at least
    /// one legal position; `empty_leaves` held none).
    pub member_leaves: usize,
    pub empty_leaves: usize,
    pub safe_leaves: usize,
    pub safe_positions: usize,
    /// Obligation partition of the safe positions.
    pub own_leaves: usize,
    pub own_positions: usize,
    pub opp_leaves: usize,
    pub opp_positions: usize,
    /// Positions in leaves whose obligation failed.
    pub violating_positions: usize,
    pub queries: u64,
    pub forks: u64,
    /// Cover mode: decided move cases plus membership classifications, and
    /// witness regions found.
    pub cases: u64,
    pub witnesses: u64,
    /// Cross-check against the concrete verifier: positions covered by
    /// several or no membership leaves, or classified differently.
    pub cover_errors: usize,
    pub mismatches: usize,
    /// Obligation parts whose outcome disagrees with the concrete obligation
    /// on some position they contain.
    pub obligation_mismatches: usize,
    /// Legal positions whose membership walk consulted each feature
    /// (traced concretely on one representative per membership leaf).
    pub feature_positions: Vec<usize>,
    /// Legal positions whose membership walk needed move generation
    /// (any of the features from `in_check` on).
    pub movegen_positions: usize,
    /// Membership leaf sizes: [1, 2..=3, 4..=15, 16+] positions.
    pub leaf_size_hist: [usize; 4],
}

/// Check the certificate symbolically for one protected colour, and
/// cross-check the membership partition against the concrete evaluation on
/// every legal position of the table.
pub fn verify(table: &Table, cert: &Cert, protected: Color, mode: Mode) -> SymReport {
    let setup = &table.setup;
    let sym = Sym::new(setup, cert, protected, mode);
    let mut rep = SymReport { protected: Some(protected), feature_positions: vec![0; cert::NFEAT], ..SymReport::default() };
    let mut seen: Vec<u8> = vec![0; table.vals.len()];
    for stm in [Color::White, Color::Black] {
        let root = Region::root(setup, stm);
        // Membership is classified over every assignment, legal or not: the
        // certificate is a predicate on positions and its partition should
        // not be charged for the legality scan. Illegal positions are then
        // ignored in the counts, and the obligations start from the legal
        // part of each safe leaf.
        let parts = sym.member(root);
        for (leaf, member) in parts {
            let ps: Vec<Position> = leaf.positions().into_iter().filter(|p| table.vals[Table::index(setup, p)] != Val::Illegal).collect();
            if ps.is_empty() {
                rep.empty_leaves += 1;
                continue;
            }
            {
                rep.member_leaves += 1;
                rep.leaf_size_hist[match ps.len() { 1 => 0, 2..=3 => 1, 4..=15 => 2, _ => 3 }] += 1;
                let mut used = [false; cert::NFEAT];
                cert::evaluate_traced(setup, cert, &ps[0], ps[0].stm, &sym.roles, &mut |i| used[i] = true).unwrap();
                for (i, &u) in used.iter().enumerate() {
                    if u {
                        rep.feature_positions[i] += ps.len();
                    }
                }
                if used[29..].iter().any(|&u| u) {
                    rep.movegen_positions += ps.len();
                }
                for p in &ps {
                    let i = Table::index(setup, p);
                    seen[i] += 1;
                    if cert::safe(setup, cert, p, &sym.roles) != member {
                        rep.mismatches += 1;
                    }
                }
                if !member {
                    continue;
                }
                rep.safe_leaves += 1;
                rep.safe_positions += ps.len();
                let (leaves, positions) = if stm == protected {
                    (&mut rep.own_leaves, &mut rep.own_positions)
                } else {
                    (&mut rep.opp_leaves, &mut rep.opp_positions)
                };
                let mut covered = 0;
                for legal in sym.legal_by_mode(leaf.clone()) {
                    let parts = if stm == protected { sym.exists_by_mode(legal) } else { sym.all_by_mode(legal) };
                    for (part, ok) in parts {
                        *leaves += 1;
                        let pps = part.positions();
                        covered += pps.len();
                        if !ok {
                            rep.violating_positions += pps.len();
                        }
                        // Per-position cross-check of the obligation outcome.
                        for p in &pps {
                            if concrete_obligation(setup, cert, p, &sym.roles) != ok {
                                rep.obligation_mismatches += 1;
                            }
                        }
                    }
                }
                *positions += covered;
                if covered != ps.len() {
                    rep.cover_errors += 1;
                    if std::env::var_os("CHESS_DEBUG").is_some() && rep.cover_errors <= 2 {
                        eprintln!("cover error: leaf {:?} stm {:?} has {} legal positions, parts cover {}", leaf.dom, leaf.stm, ps.len(), covered);
                        let mut seen_parts: Vec<Position> = Vec::new();
                        for legal in sym.legal_by_mode(leaf.clone()) {
                            eprintln!("  legal part {:?}", legal.dom);
                            let parts = if stm == protected { sym.exists_by_mode(legal) } else { sym.all_by_mode(legal) };
                            for (part, ok) in parts {
                                eprintln!("    part {:?} -> {}", part.dom, ok);
                                seen_parts.extend(part.positions());
                            }
                        }
                        for p in &ps {
                            if !seen_parts.contains(p) {
                                eprintln!("  MISSING {:?}\n{}", p.sqs, p.render(setup));
                            }
                        }
                    }
                }
            }
        }
    }
    for (i, &v) in table.vals.iter().enumerate() {
        if v != Val::Illegal {
            rep.legal_positions += 1;
            if seen[i] != 1 {
                rep.cover_errors += 1;
            }
        }
    }
    rep.queries = sym.queries.get();
    rep.forks = sym.forks.get();
    rep.cases = sym.cases.get();
    rep.witnesses = sym.witnesses.get();
    rep
}

fn contains(r: &Region, p: &Position) -> bool {
    r.stm == p.stm
        && r.dom.iter().zip(&p.sqs).all(|(d, sq)| match sq {
            Some(sq) => d.has(*sq),
            None => d.cap,
        })
}

fn pin_all(p: &Position) -> Region {
    Region {
        dom: p.sqs.iter().map(|sq| sq.map_or(Dom::captured(), Dom::pinned)).collect(),
        stm: p.stm,
    }
}

/// The concrete obligation at `p` for the protected side: at its own turn,
/// some legal move enters the region or it is stalemated; at the opponent's
/// turn, every legal move stays in the region.
fn concrete_obligation(setup: &Setup, cert: &Cert, p: &Position, roles: &Roles) -> bool {
    let moves = legal_moves(setup, p, p.stm).unwrap();
    if p.stm == roles.protected {
        if moves.is_empty() {
            return !in_check(setup, p, p.stm).unwrap();
        }
        moves.iter().any(|&mv| cert::safe(setup, cert, &p.play(mv), roles))
    } else {
        moves.iter().all(|&mv| cert::safe(setup, cert, &p.play(mv), roles))
    }
}
