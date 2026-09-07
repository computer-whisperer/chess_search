//! Symbolic check of the codex_idea nonloss certificate: evaluate the
//! feature DAG and its obligations over superposed regions instead of one
//! concrete position at a time. The recording oracle answers what a region
//! decides and forks it on the first undecided query, so every leaf here is
//! a set of positions that the certificate treats identically *for the facts
//! it actually consulted*. The leaf count against the position count
//! measures how far verification can get without enumerating the game.

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

pub struct Sym<'a> {
    pub setup: &'a Setup,
    pub cert: &'a Cert,
    pub roles: Roles,
    pub queries: Cell<u64>,
    pub forks: Cell<u64>,
    /// Decide geometric features abstractly (domain splits) instead of
    /// through the recording oracle (pins).
    pub abstract_eval: bool,
}

impl<'a> Sym<'a> {
    pub fn new(setup: &'a Setup, cert: &'a Cert, protected: Color, abstract_eval: bool) -> Sym<'a> {
        Sym { setup, cert, roles: Roles::new(setup, protected), queries: Cell::new(0), forks: Cell::new(0), abstract_eval }
    }

    fn member(&self, r: Region) -> Parts {
        if self.abstract_eval { self.classify_abs(r) } else { self.classify(r) }
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
    /// Cross-check against the concrete verifier: positions covered by
    /// several or no membership leaves, or classified differently.
    pub cover_errors: usize,
    pub mismatches: usize,
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
pub fn verify(table: &Table, cert: &Cert, protected: Color, abstract_eval: bool) -> SymReport {
    let setup = &table.setup;
    let sym = Sym::new(setup, cert, protected, abstract_eval);
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
                for legal in sym.legal(leaf) {
                    let parts = if stm == protected { sym.exists_safe(legal) } else { sym.all_safe(legal) };
                    for (part, ok) in parts {
                        *leaves += 1;
                        let k = part.positions().len();
                        covered += k;
                        if !ok {
                            rep.violating_positions += k;
                        }
                    }
                }
                *positions += covered;
                if covered != ps.len() {
                    rep.cover_errors += 1;
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
    rep
}
