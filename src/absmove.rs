//! Abstract move generation over regions (products of per-slot square
//! sets). A candidate move is a (slot, destination) pair applied to a whole
//! region: the region is split until "this slot can legally move to `t`" is
//! decided everywhere, and on the decided-yes parts the successor is again a
//! product (mover pinned at `t`, a captured rook removed, everything else
//! unchanged) whose sub-regions pull back exactly to products. The mover's
//! origin is never pinned: its domain is only narrowed to the squares that
//! can reach `t`.
//!
//! Attack detection is written for kings and rooks (the certificate's
//! material); other kinds are rejected.

use crate::board::*;
use crate::narrow::{Dom, Region};

pub enum Step<T> {
    Decided(T),
    Split(Vec<Region>),
}

fn restrict(r: &Region, s: SlotId, d: Dom) -> Option<Region> {
    let mut c = r.clone();
    c.dom[s as usize] = d;
    if c.normalize() { Some(c) } else { None }
}

pub fn split_presence(r: &Region, s: SlotId) -> Vec<Region> {
    let d = r.dom[s as usize];
    [Dom { sq: d.sq, cap: false }, Dom::captured()].into_iter().filter_map(|d| restrict(r, s, d)).collect()
}

/// Squares of slot `s` inside `mask` (present) and outside it.
pub fn split_mask(r: &Region, s: SlotId, mask: u64) -> Vec<Region> {
    let d = r.dom[s as usize];
    [Dom { sq: d.sq & mask, cap: false }, Dom { sq: d.sq & !mask, cap: d.cap }]
        .into_iter()
        .filter_map(|d| restrict(r, s, d))
        .collect()
}

/// Pin slot `s` at each of its squares inside `mask`; one more child for
/// "outside `mask`".
fn split_pin_in(r: &Region, s: SlotId, mask: u64) -> Vec<Region> {
    let d = r.dom[s as usize];
    let mut out: Vec<Region> = Dom { sq: d.sq & mask, cap: false }
        .squares()
        .filter_map(|p| restrict(r, s, Dom::pinned(p)))
        .collect();
    out.extend(restrict(r, s, Dom { sq: d.sq & !mask, cap: d.cap }));
    out
}

pub fn adjacent(setup: &Setup, p: Sq, q: Sq) -> bool {
    let (px, py) = setup.file_rank(p);
    let (qx, qy) = setup.file_rank(q);
    p != q && (px - qx).abs() <= 1 && (py - qy).abs() <= 1
}

pub fn aligned(setup: &Setup, p: Sq, q: Sq) -> bool {
    let (px, py) = setup.file_rank(p);
    let (qx, qy) = setup.file_rank(q);
    p != q && (px == qx || py == qy)
}

pub fn between_mask(setup: &Setup, p: Sq, q: Sq) -> u64 {
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

fn mask_where(setup: &Setup, pred: impl Fn(Sq) -> bool) -> u64 {
    (0..setup.area() as Sq).filter(|&p| pred(p)).map(|p| 1u64 << p).sum()
}

/// A region seen after a hypothetical move: the mover sits on `to`, a
/// captured slot is gone, everything else is as in `r`. Splits produced by
/// tests on the view always name an unchanged slot, so they apply to `r`.
pub struct View<'a> {
    pub r: &'a Region,
    pub mover: Option<(SlotId, Sq)>,
    pub captured: Option<SlotId>,
}

impl View<'_> {
    pub fn dom(&self, c: SlotId) -> Dom {
        match (self.mover, self.captured) {
            (Some((m, to)), _) if m == c => Dom::pinned(to),
            (_, Some(x)) if x == c => Dom::captured(),
            _ => self.r.dom[c as usize],
        }
    }

    fn presence(&self, c: SlotId) -> Option<bool> {
        let d = self.dom(c);
        if d.is_captured() { Some(false) } else if !d.cap { Some(true) } else { None }
    }

    /// Is the king in slot `king` attacked by a piece of colour `by`?
    pub fn attacked(&self, setup: &Setup, king: SlotId, by: Color) -> Step<bool> {
        let k = self.dom(king);
        debug_assert!(!k.cap);
        for a in setup.slots_of(by) {
            match self.presence(a) {
                None => return Step::Split(split_presence(self.r, a)),
                Some(false) => continue,
                Some(true) => {}
            }
            match setup.kind(a) {
                Kind::King => match self.pair(setup, a, king, |p, q| adjacent(setup, p, q)) {
                    Step::Decided(false) => {}
                    other => return other,
                },
                Kind::Rook => match self.rook_hits(setup, a, king) {
                    Step::Decided(false) => {}
                    other => return other,
                },
                other => panic!("abstract attack detection only handles kings and rooks, not {other:?}"),
            }
        }
        Step::Decided(false)
    }

    /// Decide `pred` over the product of two present slots' domains, or
    /// split (the unpinned side by the predicate; else pin the smaller).
    fn pair(&self, _setup: &Setup, a: SlotId, b: SlotId, pred: impl Fn(Sq, Sq) -> bool) -> Step<bool> {
        let (da, db) = (self.dom(a), self.dom(b));
        let split_by = |s: SlotId, d: Dom, f: &dyn Fn(Sq) -> bool| -> Step<bool> {
            let mask: u64 = d.squares().filter(|&p| f(p)).map(|p| 1u64 << p).sum();
            if mask == d.sq {
                Step::Decided(true)
            } else if mask == 0 {
                Step::Decided(false)
            } else {
                Step::Split(split_mask(self.r, s, mask))
            }
        };
        match (da.is_pinned(), db.is_pinned()) {
            (Some(p), Some(q)) => Step::Decided(pred(p, q)),
            (Some(p), None) => split_by(b, db, &|q| pred(p, q)),
            (None, Some(q)) => split_by(a, da, &|p| pred(p, q)),
            (None, None) => {
                let mut seen = [false; 2];
                for p in da.squares() {
                    for q in db.squares() {
                        if p != q {
                            seen[pred(p, q) as usize] = true;
                        }
                    }
                }
                match seen {
                    [false, true] => Step::Decided(true),
                    [true, false] => Step::Decided(false),
                    _ => {
                        let s = if da.size() <= db.size() { a } else { b };
                        Step::Split(self.dom(s).squares().filter_map(|p| restrict(self.r, s, Dom::pinned(p))).collect())
                    }
                }
            }
        }
    }

    /// Pin the unpinned one of `a`, `b` with the smaller domain.
    fn pin_smaller(&self, a: SlotId, b: SlotId) -> Step<bool> {
        let (da, db) = (self.dom(a), self.dom(b));
        let s = match (da.is_pinned(), db.is_pinned()) {
            (Some(_), None) => b,
            (None, Some(_)) => a,
            (None, None) => if da.size() <= db.size() { a } else { b },
            (Some(_), Some(_)) => unreachable!(),
        };
        Step::Split(self.dom(s).squares().filter_map(|p| restrict(self.r, s, Dom::pinned(p))).collect())
    }

    /// Does the present rook in slot `rook` have a clear line to `king`?
    fn rook_hits(&self, setup: &Setup, rook: SlotId, king: SlotId) -> Step<bool> {
        let (dr, dk) = (self.dom(rook), self.dom(king));
        let (Some(p), Some(q)) = (dr.is_pinned(), dk.is_pinned()) else {
            // With one side pinned, split the other on alignment first, so
            // the non-aligned part is decided without a pin.
            if let Some(q) = dk.is_pinned() {
                let al = mask_where(setup, |p| aligned(setup, p, q));
                if dr.sq & !al != 0 && dr.sq & al != 0 {
                    return Step::Split(split_mask(self.r, rook, al));
                }
            } else if let Some(p) = dr.is_pinned() {
                let al = mask_where(setup, |q| aligned(setup, p, q));
                if dk.sq & !al != 0 && dk.sq & al != 0 {
                    return Step::Split(split_mask(self.r, king, al));
                }
            }
            // Decided only if no assignment is aligned; otherwise pin.
            let any = dr.squares().any(|p| dk.squares().any(|q| aligned(setup, p, q)));
            return if any { self.pin_smaller(rook, king) } else { Step::Decided(false) };
        };
        if !aligned(setup, p, q) {
            return Step::Decided(false);
        }
        let between = between_mask(setup, p, q);
        for c in 0..self.r.dom.len() as SlotId {
            if c == rook || c == king {
                continue;
            }
            let d = self.dom(c);
            if d.sq & between == 0 {
                continue;
            }
            if d.sq & !between == 0 && !d.cap {
                return Step::Decided(false); // certainly blocked
            }
            // `c` is never the mover (pinned) nor captured (no squares).
            return Step::Split(split_mask(self.r, c, between));
        }
        Step::Decided(true)
    }
}

/// Outcome of a candidate move on a region: `Some(capture)` if every
/// position can legally play it, `None` if none can.
pub type CanMove = Option<bool>;

/// One refinement step towards deciding whether slot `s` can legally move
/// to `t` on all of `r`.
fn step(setup: &Setup, r: &Region, s: SlotId, t: Sq) -> Step<CanMove> {
    let stm = r.stm;
    debug_assert_eq!(setup.color(s), stm);
    let enemy = stm.flip();
    let own_k = setup.king_slot(stm);
    let d = r.dom[s as usize];
    // 1. The mover must be present.
    if d.is_captured() {
        return Step::Decided(None);
    }
    if d.cap {
        return Step::Split(split_presence(r, s));
    }
    // 2. Only origins that reach `t`.
    let geom = match setup.kind(s) {
        Kind::King => mask_where(setup, |p| adjacent(setup, p, t)),
        Kind::Rook => mask_where(setup, |p| aligned(setup, p, t)),
        other => panic!("abstract move generation only handles kings and rooks, not {other:?}"),
    };
    if d.sq & geom == 0 {
        return Step::Decided(None);
    }
    if d.sq & !geom != 0 {
        return Step::Split(split_mask(r, s, geom));
    }
    // 3. Occupancy of `t`: own pieces and the enemy king forbid it, an
    //    enemy rook is captured.
    let mut capture = None;
    for c in 0..r.dom.len() as SlotId {
        if c == s || !r.dom[c as usize].has(t) {
            continue;
        }
        if r.dom[c as usize].is_pinned().is_none() {
            return Step::Split(split_mask(r, c, 1 << t));
        }
        if setup.color(c) == stm || setup.kind(c) == Kind::King {
            return Step::Decided(None);
        }
        capture = Some(c);
    }
    // 4. A rook needs a clear path from every remaining origin.
    if setup.kind(s) == Kind::Rook {
        let path: u64 = d.squares().map(|p| between_mask(setup, p, t)).fold(0, |a, b| a | b);
        for c in 0..r.dom.len() as SlotId {
            if c == s || r.dom[c as usize].sq & path == 0 {
                continue;
            }
            match r.dom[c as usize].is_pinned() {
                None => return Step::Split(split_pin_in(r, c, path)),
                Some(x) => {
                    // Origins beyond the blocker on its ray are cut off.
                    let keep = mask_where(setup, |p| {
                        d.has(p) && !(aligned(setup, p, t) && between_mask(setup, p, t) & (1 << x) != 0)
                    });
                    if keep == 0 {
                        return Step::Decided(None);
                    }
                    // Both parts: the cut-off origins decide "no move" next.
                    return Step::Split(split_mask(r, s, keep));
                }
            }
        }
    }
    // 5. Own king not attacked afterwards.
    let view = View { r, mover: Some((s, t)), captured: capture };
    match view.attacked(setup, own_k, enemy) {
        Step::Decided(true) => Step::Decided(None),
        Step::Decided(false) => Step::Decided(Some(capture.is_some())),
        Step::Split(ch) => Step::Split(ch),
    }
}

/// Partition `r` by whether slot `s` can legally move to `t`.
pub fn can_move(setup: &Setup, r: Region, s: SlotId, t: Sq) -> Vec<(Region, CanMove)> {
    match step(setup, &r, s, t) {
        Step::Decided(x) => vec![(r, x)],
        Step::Split(children) => children.into_iter().flat_map(|c| can_move(setup, c, s, t)).collect(),
    }
}

/// The successor region of a decided-yes case.
pub fn play(setup: &Setup, r: &Region, s: SlotId, t: Sq, capture: bool) -> Region {
    let mut c = r.clone();
    c.dom[s as usize] = Dom::pinned(t);
    if capture {
        let victim = setup.slots_of(r.stm.flip()).find(|&v| r.dom[v as usize].is_pinned() == Some(t)).expect("captured piece pinned at t");
        c.dom[victim as usize] = Dom::captured();
    }
    c.stm = r.stm.flip();
    assert!(c.normalize(), "successor of a decided move is non-empty");
    c
}

/// The positions of `case` whose successor lies in `child` (a sub-region
/// of `play(case, s, t, capture)`): a product again.
pub fn pullback(setup: &Setup, case: &Region, child: &Region, s: SlotId, t: Sq, capture: bool) -> Option<Region> {
    let mut r = child.clone();
    r.dom[s as usize] = case.dom[s as usize];
    if capture {
        let victim = setup.slots_of(case.stm.flip()).find(|&v| case.dom[v as usize].is_pinned() == Some(t)).unwrap();
        r.dom[victim as usize] = Dom::pinned(t);
    }
    r.stm = case.stm;
    if r.normalize() { Some(r) } else { None }
}
