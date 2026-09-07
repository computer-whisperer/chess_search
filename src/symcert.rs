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
use crate::narrow::{Pattern, Rec, Region};
use crate::retro::{Table, Val};
use std::cell::{Cell, RefCell};

/// A region with a boolean answer (membership, or an obligation's outcome).
pub type Parts = Vec<(Region, bool)>;

pub struct Sym<'a> {
    pub setup: &'a Setup,
    pub cert: &'a Cert,
    pub roles: Roles,
    pub queries: Cell<u64>,
    pub forks: Cell<u64>,
}

impl<'a> Sym<'a> {
    pub fn new(setup: &'a Setup, cert: &'a Cert, protected: Color) -> Sym<'a> {
        Sym { setup, cert, roles: Roles::new(setup, protected), queries: Cell::new(0), forks: Cell::new(0) }
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
                for (child, ok) in self.classify(sub.play(mv)) {
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
                for (child, ok) in self.classify(sub.play(mv)) {
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
    /// Membership partition of the legal positions.
    pub member_leaves: usize,
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
pub fn verify(table: &Table, cert: &Cert, protected: Color) -> SymReport {
    let setup = &table.setup;
    let sym = Sym::new(setup, cert, protected);
    let mut rep = SymReport { protected: Some(protected), feature_positions: vec![0; cert::NFEAT], ..SymReport::default() };
    let mut seen: Vec<u8> = vec![0; table.vals.len()];
    for stm in [Color::White, Color::Black] {
        for r in sym.legal(Region::root(setup, stm)) {
            for (leaf, member) in sym.classify(r) {
                rep.member_leaves += 1;
                let ps = leaf.positions();
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
                    if table.vals[i] == Val::Illegal || cert::safe(setup, cert, p, &sym.roles) != member {
                        rep.mismatches += 1;
                    }
                }
                if !member {
                    continue;
                }
                rep.safe_leaves += 1;
                rep.safe_positions += ps.len();
                let (parts, leaves, positions) = if stm == protected {
                    (sym.exists_safe(leaf), &mut rep.own_leaves, &mut rep.own_positions)
                } else {
                    (sym.all_safe(leaf), &mut rep.opp_leaves, &mut rep.opp_positions)
                };
                let mut covered = 0;
                for (part, ok) in parts {
                    *leaves += 1;
                    let k = part.positions().len();
                    covered += k;
                    if !ok {
                        rep.violating_positions += k;
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
