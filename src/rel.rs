//! Anchor-relative regions: the translation quotient made explicit.
//!
//! A region is the *anchor's* (the protected king's) absolute square set
//! times one *offset* domain per other piece, with the board boundary the
//! only coupling between them. Positions are all (anchor square, offsets)
//! with every piece on the board and all squares distinct. Distances,
//! alignments and clear rays are then predicates on offsets alone, decided
//! by splitting offset domains; the anchor's edge distance is a split on
//! the anchor set alone; an anchor move translates every offset domain and
//! a rook move changes one offset. One witness region with a relative move
//! covers every translation of a pattern at once.
//!
//! Material: kings and rooks only (the certificate's material).

use crate::board::*;
use crate::cert::{self, Roles};
use crate::certs::Cert;
use crate::retro::{Table, Val};

/// Offset (dx, dy) with |dx|, |dy| < n, encoded as one index.
pub type Off = u16;
/// Bitset over offset indices ((2n-1)^2 <= 225 for n <= 8).
pub type OffSet = [u64; 4];

fn set_has(s: &OffSet, o: Off) -> bool {
    s[(o / 64) as usize] & (1u64 << (o % 64)) != 0
}
fn set_add(s: &mut OffSet, o: Off) {
    s[(o / 64) as usize] |= 1u64 << (o % 64);
}
fn set_del(s: &mut OffSet, o: Off) {
    s[(o / 64) as usize] &= !(1u64 << (o % 64));
}
fn set_and(a: &OffSet, b: &OffSet) -> OffSet {
    [a[0] & b[0], a[1] & b[1], a[2] & b[2], a[3] & b[3]]
}
fn set_andnot(a: &OffSet, b: &OffSet) -> OffSet {
    [a[0] & !b[0], a[1] & !b[1], a[2] & !b[2], a[3] & !b[3]]
}
fn set_empty(s: &OffSet) -> bool {
    s.iter().all(|&w| w == 0)
}
fn set_count(s: &OffSet) -> u32 {
    s.iter().map(|w| w.count_ones()).sum()
}
fn set_iter(s: &OffSet) -> impl Iterator<Item = Off> + '_ {
    (0..4).flat_map(move |w| {
        let mut bits = s[w];
        std::iter::from_fn(move || {
            if bits == 0 {
                None
            } else {
                let b = bits.trailing_zeros();
                bits &= bits - 1;
                Some((w * 64) as Off + b as Off)
            }
        })
    })
}
fn set_single(s: &OffSet) -> Option<Off> {
    if set_count(s) == 1 { set_iter(s).next() } else { None }
}
fn set_from(iter: impl Iterator<Item = Off>) -> OffSet {
    let mut s = [0; 4];
    for o in iter {
        set_add(&mut s, o);
    }
    s
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct OffDom {
    pub set: OffSet,
    pub cap: bool,
}

impl OffDom {
    fn present(&self) -> Option<bool> {
        if set_empty(&self.set) && self.cap { Some(false) } else if !self.cap { Some(true) } else { None }
    }
    fn pinned(&self) -> Option<Off> {
        if self.cap { None } else { set_single(&self.set) }
    }
}

/// Board geometry in offset space.
pub struct Geo<'a> {
    pub setup: &'a Setup,
    pub n: i32,
    pub anchor: SlotId,
}

impl Geo<'_> {
    pub fn w(&self) -> i32 {
        2 * self.n - 1
    }
    pub fn off(&self, dx: i32, dy: i32) -> Off {
        ((dy + self.n - 1) * self.w() + (dx + self.n - 1)) as Off
    }
    pub fn dxy(&self, o: Off) -> (i32, i32) {
        let (w, n) = (self.w(), self.n);
        ((o as i32 % w) - (n - 1), (o as i32 / w) - (n - 1))
    }
    pub fn zero(&self) -> Off {
        self.off(0, 0)
    }
    pub fn all_offsets(&self) -> OffSet {
        set_from((0..(self.w() * self.w()) as Off).filter(|&o| o != self.zero()))
    }
    /// Square at `a + o`, if on the board.
    pub fn at(&self, a: Sq, o: Off) -> Option<Sq> {
        let (f, r) = self.setup.file_rank(a);
        let (dx, dy) = self.dxy(o);
        self.setup.sq(f + dx, r + dy)
    }
    pub fn off_between(&self, a: Sq, q: Sq) -> Off {
        let (fa, ra) = self.setup.file_rank(a);
        let (fq, rq) = self.setup.file_rank(q);
        self.off(fq - fa, rq - ra)
    }
    pub fn dist(&self, o: Off) -> i32 {
        let (dx, dy) = self.dxy(o);
        dx.abs().max(dy.abs())
    }
    pub fn aligned(&self, o: Off) -> bool {
        let (dx, dy) = self.dxy(o);
        o != self.zero() && (dx == 0 || dy == 0)
    }
    /// Offset difference `b - a`, if representable.
    pub fn diff(&self, a: Off, b: Off) -> Option<Off> {
        let (ax, ay) = self.dxy(a);
        let (bx, by) = self.dxy(b);
        let (dx, dy) = (bx - ax, by - ay);
        (dx.abs() < self.n && dy.abs() < self.n).then(|| self.off(dx, dy))
    }
    pub fn add(&self, a: Off, b: Off) -> Option<Off> {
        let (ax, ay) = self.dxy(a);
        let (bx, by) = self.dxy(b);
        let (dx, dy) = (ax + bx, ay + by);
        (dx.abs() < self.n && dy.abs() < self.n).then(|| self.off(dx, dy))
    }
    /// Offsets strictly between `p` and `q` (both offsets, aligned).
    pub fn between(&self, p: Off, q: Off) -> OffSet {
        let (px, py) = self.dxy(p);
        let (qx, qy) = self.dxy(q);
        let (sx, sy) = ((qx - px).signum(), (qy - py).signum());
        let mut s = [0; 4];
        let (mut x, mut y) = (px + sx, py + sy);
        while (x, y) != (qx, qy) {
            set_add(&mut s, self.off(x, y));
            x += sx;
            y += sy;
        }
        s
    }
    pub fn aligned_pair(&self, p: Off, q: Off) -> bool {
        let (px, py) = self.dxy(p);
        let (qx, qy) = self.dxy(q);
        p != q && (px == qx || py == qy)
    }
    pub fn dist_pair(&self, p: Off, q: Off) -> i32 {
        let (px, py) = self.dxy(p);
        let (qx, qy) = self.dxy(q);
        (px - qx).abs().max((py - qy).abs())
    }
    /// Shift a set by `-d` (an anchor move by `d`).
    pub fn shift(&self, s: &OffSet, d: Off, sign: i32) -> OffSet {
        let (dx, dy) = self.dxy(d);
        set_from(set_iter(s).filter_map(|o| {
            let (ox, oy) = self.dxy(o);
            let (nx, ny) = (ox + sign * dx, oy + sign * dy);
            (nx.abs() < self.n && ny.abs() < self.n).then(|| self.off(nx, ny))
        }))
    }
}

/// An anchor-relative region.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Rel {
    /// Anchor squares.
    pub a: u64,
    /// Offset domains per slot (the anchor's own entry is unused).
    pub off: Vec<OffDom>,
    pub stm: Color,
}

impl Rel {
    pub fn root(g: &Geo, stm: Color) -> Rel {
        let setup = g.setup;
        let area = setup.area();
        let a = if area == 64 { u64::MAX } else { (1u64 << area) - 1 };
        let off = (0..setup.slots.len() as SlotId)
            .map(|s| OffDom { set: if s == g.anchor { [0; 4] } else { g.all_offsets() }, cap: s != g.anchor && setup.kind(s) != Kind::King })
            .collect();
        let mut r = Rel { a, off, stm };
        assert!(r.normalize(g));
        r
    }

    /// Exclude the anchor's offset, propagate pinned offsets, and prune the
    /// anchor set and the offset sets against the board. False if empty.
    pub fn normalize(&mut self, g: &Geo) -> bool {
        let zero = g.zero();
        let slots: Vec<SlotId> = (0..self.off.len() as SlotId).filter(|&s| s != g.anchor).collect();
        loop {
            let mut changed = false;
            for &s in &slots {
                if set_has(&self.off[s as usize].set, zero) {
                    set_del(&mut self.off[s as usize].set, zero);
                    changed = true;
                }
                if let Some(o) = self.off[s as usize].pinned() {
                    for &t in &slots {
                        if t != s && set_has(&self.off[t as usize].set, o) {
                            set_del(&mut self.off[t as usize].set, o);
                            changed = true;
                        }
                    }
                }
            }
            // Anchor squares from which some required piece has no on-board offset.
            let mut a = self.a;
            for sq in 0..g.setup.area() as Sq {
                if a & (1 << sq) == 0 {
                    continue;
                }
                for &s in &slots {
                    let d = &self.off[s as usize];
                    if d.cap {
                        continue;
                    }
                    if !set_iter(&d.set).any(|o| g.at(sq, o).is_some()) {
                        a &= !(1 << sq);
                        break;
                    }
                }
            }
            if a != self.a {
                self.a = a;
                changed = true;
            }
            // Offsets that are off the board from every anchor square.
            for &s in &slots {
                let d = self.off[s as usize];
                let keep = set_from(set_iter(&d.set).filter(|&o| (0..g.setup.area() as Sq).any(|sq| self.a & (1 << sq) != 0 && g.at(sq, o).is_some())));
                if keep != d.set {
                    self.off[s as usize].set = keep;
                    changed = true;
                }
            }
            if self.a == 0 || slots.iter().any(|&s| set_empty(&self.off[s as usize].set) && !self.off[s as usize].cap) {
                return false;
            }
            if !changed {
                return true;
            }
        }
    }

    fn with(&self, g: &Geo, f: impl FnOnce(&mut Rel)) -> Option<Rel> {
        let mut r = self.clone();
        f(&mut r);
        if r.normalize(g) { Some(r) } else { None }
    }

    pub fn contains(&self, g: &Geo, p: &Position) -> bool {
        if p.stm != self.stm {
            return false;
        }
        let Some(a) = p.sqs[g.anchor as usize] else { return false };
        if self.a & (1 << a) == 0 {
            return false;
        }
        (0..self.off.len() as SlotId).filter(|&s| s != g.anchor).all(|s| match p.sqs[s as usize] {
            Some(q) => set_has(&self.off[s as usize].set, g.off_between(a, q)),
            None => self.off[s as usize].cap,
        })
    }

    /// Every position in the region.
    pub fn positions(&self, g: &Geo) -> Vec<Position> {
        let slots: Vec<SlotId> = (0..self.off.len() as SlotId).filter(|&s| s != g.anchor).collect();
        let mut out = Vec::new();
        for a in 0..g.setup.area() as Sq {
            if self.a & (1 << a) == 0 {
                continue;
            }
            let mut sqs = vec![None; self.off.len()];
            sqs[g.anchor as usize] = Some(a);
            self.enumerate(g, &slots, 0, a, &mut sqs, &mut out);
        }
        out
    }
    fn enumerate(&self, g: &Geo, slots: &[SlotId], k: usize, a: Sq, sqs: &mut Vec<Option<Sq>>, out: &mut Vec<Position>) {
        if k == slots.len() {
            out.push(Position { sqs: sqs.clone(), stm: self.stm });
            return;
        }
        let s = slots[k];
        let d = &self.off[s as usize];
        for o in set_iter(&d.set) {
            if let Some(q) = g.at(a, o) {
                if !sqs.contains(&Some(q)) {
                    sqs[s as usize] = Some(q);
                    self.enumerate(g, slots, k + 1, a, sqs, out);
                    sqs[s as usize] = None;
                }
            }
        }
        if d.cap {
            self.enumerate(g, slots, k + 1, a, sqs, out);
        }
    }
}

pub enum Step<T> {
    Decided(T),
    Split(Vec<Rel>),
}

// ---- splitting helpers ----

fn split_presence(g: &Geo, r: &Rel, s: SlotId) -> Vec<Rel> {
    let d = r.off[s as usize];
    let present = r.with(g, |r| r.off[s as usize] = OffDom { set: d.set, cap: false });
    let gone = r.with(g, |r| r.off[s as usize] = OffDom { set: [0; 4], cap: true });
    present.into_iter().chain(gone).collect()
}

/// Split slot `s` (present) into offsets inside `mask` and outside it.
fn split_mask(g: &Geo, r: &Rel, s: SlotId, mask: &OffSet) -> Vec<Rel> {
    let d = r.off[s as usize];
    let inside = r.with(g, |r| r.off[s as usize] = OffDom { set: set_and(&d.set, mask), cap: false });
    let outside = r.with(g, |r| r.off[s as usize] = OffDom { set: set_andnot(&d.set, mask), cap: d.cap });
    inside.into_iter().chain(outside).collect()
}

/// Pin slot `s` at each offset inside `mask`; one more child for outside.
fn split_pin_in(g: &Geo, r: &Rel, s: SlotId, mask: &OffSet) -> Vec<Rel> {
    let d = r.off[s as usize];
    let mut out: Vec<Rel> = set_iter(&set_and(&d.set, mask))
        .filter_map(|o| r.with(g, |r| r.off[s as usize] = OffDom { set: set_from(std::iter::once(o)), cap: false }))
        .collect();
    out.extend(r.with(g, |r| r.off[s as usize] = OffDom { set: set_andnot(&d.set, mask), cap: d.cap }));
    out
}

fn pin_all(g: &Geo, r: &Rel, s: SlotId) -> Vec<Rel> {
    set_iter(&r.off[s as usize].set)
        .filter_map(|o| r.with(g, |r| r.off[s as usize] = OffDom { set: set_from(std::iter::once(o)), cap: false }))
        .collect()
}

/// Split the anchor set by a predicate on squares.
fn split_anchor(g: &Geo, r: &Rel, pred: impl Fn(Sq) -> bool) -> Step<bool> {
    let mask: u64 = (0..g.setup.area() as Sq).filter(|&a| r.a & (1 << a) != 0 && pred(a)).map(|a| 1u64 << a).sum();
    if mask == r.a {
        Step::Decided(true)
    } else if mask == 0 {
        Step::Decided(false)
    } else {
        Step::Split(
            [mask, r.a & !mask].into_iter().filter_map(|m| r.with(g, |r| r.a = m)).collect(),
        )
    }
}

/// Decide a predicate on one present slot's offset, or split it.
fn split_by(g: &Geo, r: &Rel, s: SlotId, pred: impl Fn(Off) -> bool) -> Step<bool> {
    let d = r.off[s as usize];
    let mask = set_from(set_iter(&d.set).filter(|&o| pred(o)));
    if mask == d.set {
        Step::Decided(true)
    } else if set_empty(&mask) {
        Step::Decided(false)
    } else {
        Step::Split(split_mask(g, r, s, &mask))
    }
}

/// Where a piece is, in offset space, possibly overridden by a hypothetical move.
#[derive(Clone, Copy)]
pub struct View {
    pub mover: Option<(SlotId, Off)>,
    pub captured: Option<SlotId>,
    /// The anchor has moved to this offset (pre-move coordinates); its old
    /// square (offset zero) is vacant.
    pub anchor_at: Option<Off>,
}

impl View {
    const NONE: View = View { mover: None, captured: None, anchor_at: None };

    fn dom(&self, r: &Rel, s: SlotId) -> OffDom {
        match (self.mover, self.captured) {
            (Some((m, o)), _) if m == s => OffDom { set: set_from(std::iter::once(o)), cap: false },
            (_, Some(x)) if x == s => OffDom { set: [0; 4], cap: true },
            _ => r.off[s as usize],
        }
    }
}

/// Where the king under attack stands.
#[derive(Clone, Copy)]
pub enum KingPos {
    /// The anchor, at offset zero (or at `View::anchor_at`).
    Anchor,
    /// A non-anchor king slot (its domain, possibly overridden).
    Slot(SlotId),
}

pub struct Engine<'a> {
    pub g: Geo<'a>,
    pub cert: &'a Cert,
    pub roles: Roles,
    pub cases: std::cell::Cell<u64>,
    pub witnesses: std::cell::Cell<u64>,
}

impl<'a> Engine<'a> {
    pub fn new(setup: &'a Setup, cert: &'a Cert, protected: Color) -> Engine<'a> {
        let roles = Roles::new(setup, protected);
        Engine {
            g: Geo { setup, n: setup.n as i32, anchor: roles.own_k },
            cert,
            roles,
            cases: std::cell::Cell::new(0),
            witnesses: std::cell::Cell::new(0),
        }
    }

    /// Offset of the king in `kp` if pinned (anchor: zero or moved-to).
    fn king_off(&self, r: &Rel, v: &View, kp: KingPos) -> Result<Off, OffDom> {
        match kp {
            KingPos::Anchor => Ok(v.anchor_at.unwrap_or(self.g.zero())),
            KingPos::Slot(s) => {
                let d = v.dom(r, s);
                d.pinned().ok_or(d)
            }
        }
    }

    /// Is the king attacked by a piece of colour `by`?
    fn attacked(&self, r: &Rel, v: &View, kp: KingPos, by: Color) -> Step<bool> {
        let g = &self.g;
        for att in g.setup.slots_of(by) {
            if att == g.anchor {
                // The anchor attacks as a king: adjacency to a non-anchor king.
                let KingPos::Slot(ks) = kp else { continue };
                let a_off = v.anchor_at.unwrap_or(g.zero());
                // The king may be the mover: use the view's domain.
                let step = match v.dom(r, ks).pinned() {
                    Some(k) => Step::Decided(g.dist_pair(k, a_off) <= 1),
                    None => split_by(g, r, ks, |o| g.dist_pair(o, a_off) <= 1),
                };
                match step {
                    Step::Decided(false) => continue,
                    other => return other,
                }
            }
            let d = v.dom(r, att);
            match d.present() {
                None => return Step::Split(split_presence(g, r, att)),
                Some(false) => continue,
                Some(true) => {}
            }
            let step = match g.setup.kind(att) {
                Kind::King => self.pair(r, v, att, kp, |o, k| g.dist_pair(o, k) <= 1),
                Kind::Rook => self.rook_hits(r, v, att, kp),
                other => panic!("relative engine handles kings and rooks, not {other:?}"),
            };
            match step {
                Step::Decided(false) => continue,
                other => return other,
            }
        }
        Step::Decided(false)
    }

    /// Predicate between a present non-anchor slot and the king.
    fn pair(&self, r: &Rel, v: &View, s: SlotId, kp: KingPos, pred: impl Fn(Off, Off) -> bool) -> Step<bool> {
        let g = &self.g;
        let ds = v.dom(r, s);
        match self.king_off(r, v, kp) {
            Ok(k) => {
                if let Some(o) = ds.pinned() {
                    return Step::Decided(pred(o, k));
                }
                split_by(g, r, s, |o| pred(o, k))
            }
            Err(dk) => {
                let ks = match kp { KingPos::Slot(ks) => ks, KingPos::Anchor => unreachable!() };
                if let Some(o) = ds.pinned() {
                    return split_by(g, r, ks, |k| pred(o, k));
                }
                let mut seen = [false; 2];
                for o in set_iter(&ds.set) {
                    for k in set_iter(&dk.set) {
                        if o != k {
                            seen[pred(o, k) as usize] = true;
                        }
                    }
                }
                match seen {
                    [false, true] => Step::Decided(true),
                    [true, false] => Step::Decided(false),
                    _ => Step::Split(pin_all(g, r, if set_count(&ds.set) <= set_count(&dk.set) { s } else { ks })),
                }
            }
        }
    }

    /// Does the present rook `rook` have a clear line to the king?
    fn rook_hits(&self, r: &Rel, v: &View, rook: SlotId, kp: KingPos) -> Step<bool> {
        let g = &self.g;
        let dr = v.dom(r, rook);
        let (p, k) = match (dr.pinned(), self.king_off(r, v, kp)) {
            (Some(p), Ok(k)) => (p, k),
            (None, Ok(k)) => {
                // Split the rook on alignment with the king first.
                return match split_by(g, r, rook, |o| g.aligned_pair(o, k)) {
                    Step::Decided(false) => Step::Decided(false),
                    Step::Decided(true) => Step::Split(pin_all(g, r, rook)),
                    split => split,
                };
            }
            (Some(p), Err(_)) => {
                let KingPos::Slot(ks) = kp else { unreachable!() };
                return match split_by(g, r, ks, |k| g.aligned_pair(p, k)) {
                    Step::Decided(false) => Step::Decided(false),
                    Step::Decided(true) => Step::Split(pin_all(g, r, ks)),
                    split => split,
                };
            }
            (None, Err(dk)) => {
                let KingPos::Slot(ks) = kp else { unreachable!() };
                let any = set_iter(&dr.set).any(|o| set_iter(&dk.set).any(|k| g.aligned_pair(o, k)));
                return if any {
                    Step::Split(pin_all(g, r, if set_count(&dr.set) <= set_count(&dk.set) { rook } else { ks }))
                } else {
                    Step::Decided(false)
                };
            }
        };
        if !g.aligned_pair(p, k) {
            return Step::Decided(false);
        }
        let between = g.between(p, k);
        // The anchor blocks at zero unless it is the king or has moved away.
        let anchor_blocks = !matches!(kp, KingPos::Anchor) && v.anchor_at.is_none();
        if anchor_blocks && set_has(&between, g.zero()) {
            return Step::Decided(false);
        }
        for c in 0..r.off.len() as SlotId {
            if c == rook || c == g.anchor || matches!(kp, KingPos::Slot(ks) if ks == c) {
                continue;
            }
            let d = v.dom(r, c);
            let inside = set_and(&d.set, &between);
            if set_empty(&inside) {
                continue;
            }
            if inside == d.set && !d.cap {
                return Step::Decided(false);
            }
            return Step::Split(split_mask(g, r, c, &between));
        }
        Step::Decided(true)
    }

    // ---- certificate features ----

    /// `feature <= thr` on the region, or a split.
    fn test(&self, r: &Rel, feat: usize, thr: i32) -> Step<bool> {
        let g = &self.g;
        let roles = &self.roles;
        let le = |v: i32| Step::Decided(v <= thr);
        let n = g.n;
        match feat {
            0 => le((r.stm != roles.protected) as i32),
            1 | 2 => {
                let s = if feat == 1 { roles.own_r } else { roles.opp_r };
                match r.off[s as usize].present() {
                    Some(p) => le(!p as i32),
                    None => Step::Split(split_presence(g, r, s)),
                }
            }
            3 | 4 => split_anchor(g, r, |a| {
                let (x, y) = g.setup.file_rank(a);
                let v = if feat == 3 {
                    x.min(y).min(n - 1 - x).min(n - 1 - y)
                } else {
                    ((x == 0 || x == n - 1) && (y == 0 || y == n - 1)) as i32
                };
                v <= thr
            }),
            11..=28 => {
                let (a, b) = cert::pair_slots(roles)[(feat - 11) / 3];
                let kind = (feat - 11) % 3;
                for s in [a, b] {
                    if s == g.anchor {
                        continue;
                    }
                    match r.off[s as usize].present() {
                        None => return Step::Split(split_presence(g, r, s)),
                        Some(false) => return le(if kind == 0 { 99 } else { 0 }),
                        Some(true) => {}
                    }
                }
                let val = |p: Off, q: Off| -> i32 {
                    if kind == 0 { g.dist_pair(p, q) } else { g.aligned_pair(p, q) as i32 }
                };
                if kind == 2 {
                    return self.test_clear(r, a, b, thr);
                }
                let zero = g.zero();
                if a == g.anchor || b == g.anchor {
                    let s = if a == g.anchor { b } else { a };
                    return split_by(g, r, s, |o| val(o, zero) <= thr);
                }
                let (da, db) = (r.off[a as usize], r.off[b as usize]);
                match (da.pinned(), db.pinned()) {
                    (Some(p), _) => split_by(g, r, b, |q| val(p, q) <= thr),
                    (_, Some(q)) => split_by(g, r, a, |p| val(p, q) <= thr),
                    _ => {
                        let mut seen = [false; 2];
                        for p in set_iter(&da.set) {
                            for q in set_iter(&db.set) {
                                if p != q {
                                    seen[(val(p, q) <= thr) as usize] = true;
                                }
                            }
                        }
                        match seen {
                            [false, true] => Step::Decided(true),
                            [true, false] => Step::Decided(false),
                            _ => Step::Split(pin_all(g, r, if set_count(&da.set) <= set_count(&db.set) { a } else { b })),
                        }
                    }
                }
            }
            other => panic!("feature {other} is not in the anchor-relative vocabulary"),
        }
    }

    /// `clear_ray(a, b) <= thr` with both present.
    fn test_clear(&self, r: &Rel, a: SlotId, b: SlotId, thr: i32) -> Step<bool> {
        let g = &self.g;
        let zero = g.zero();
        let pos = |s: SlotId| -> Result<Off, OffDom> {
            if s == g.anchor { Ok(zero) } else { r.off[s as usize].pinned().ok_or(r.off[s as usize]) }
        };
        let (p, q) = match (pos(a), pos(b)) {
            (Ok(p), Ok(q)) => (p, q),
            (Ok(p), Err(_)) => {
                return match split_by(g, r, b, |q| g.aligned_pair(p, q)) {
                    Step::Decided(false) => Step::Decided(0 <= thr),
                    Step::Decided(true) => Step::Split(pin_all(g, r, b)),
                    split => split,
                };
            }
            (Err(_), Ok(q)) => {
                return match split_by(g, r, a, |p| g.aligned_pair(p, q)) {
                    Step::Decided(false) => Step::Decided(0 <= thr),
                    Step::Decided(true) => Step::Split(pin_all(g, r, a)),
                    split => split,
                };
            }
            (Err(da), Err(db)) => {
                let any = set_iter(&da.set).any(|p| set_iter(&db.set).any(|q| g.aligned_pair(p, q)));
                return if any {
                    Step::Split(pin_all(g, r, if set_count(&da.set) <= set_count(&db.set) { a } else { b }))
                } else {
                    Step::Decided(0 <= thr)
                };
            }
        };
        if !g.aligned_pair(p, q) {
            return Step::Decided(0 <= thr);
        }
        let between = g.between(p, q);
        if a != g.anchor && b != g.anchor && set_has(&between, zero) {
            return Step::Decided(0 <= thr); // the anchor blocks
        }
        for c in 0..r.off.len() as SlotId {
            if c == a || c == b || c == g.anchor {
                continue;
            }
            let d = r.off[c as usize];
            let inside = set_and(&d.set, &between);
            if set_empty(&inside) {
                continue;
            }
            if inside == d.set && !d.cap {
                return Step::Decided(0 <= thr);
            }
            return Step::Split(split_mask(g, r, c, &between));
        }
        Step::Decided(1 <= thr)
    }

    /// Partition by certificate membership.
    pub fn classify(&self, r: Rel) -> Vec<(Rel, bool)> {
        self.classify_from(r, self.cert.root)
    }
    fn classify_from(&self, r: Rel, mut node: u32) -> Vec<(Rel, bool)> {
        while node >= 2 {
            let [feat, thr, l, rt] = self.cert.nodes[node as usize - 2];
            match self.test(&r, feat as usize, thr) {
                Step::Decided(b) => node = if b { l } else { rt } as u32,
                Step::Split(children) => return children.into_iter().flat_map(|c| self.classify_from(c, node)).collect(),
            }
        }
        vec![(r, node == 1)]
    }

    // ---- moves ----

    /// Candidate moves for `stm`: anchor steps, or offsets for other slots.
    fn candidates(&self, stm: Color) -> Vec<Cand> {
        let g = &self.g;
        let mut out = Vec::new();
        for s in g.setup.slots_of(stm) {
            if s == g.anchor {
                for dy in -1..=1 {
                    for dx in -1..=1 {
                        if (dx, dy) != (0, 0) {
                            out.push(Cand::Anchor(g.off(dx, dy)));
                        }
                    }
                }
            } else {
                out.extend(set_iter(&g.all_offsets()).map(|o| Cand::Slot(s, o)));
            }
        }
        out
    }

    fn step(&self, r: &Rel, c: Cand) -> Step<Option<bool>> {
        let g = &self.g;
        let stm = r.stm;
        let zero = g.zero();
        match c {
            Cand::Anchor(d) => {
                // 1. Target on the board.
                match split_anchor(g, r, |a| g.at(a, d).is_some()) {
                    Step::Decided(true) => {}
                    Step::Decided(false) => return Step::Decided(None),
                    Step::Split(ch) => return Step::Split(ch),
                }
                // 2. Occupancy of the target offset.
                let mut capture = None;
                for s in 0..r.off.len() as SlotId {
                    if s == g.anchor || !set_has(&r.off[s as usize].set, d) {
                        continue;
                    }
                    if r.off[s as usize].pinned().is_none() {
                        return Step::Split(split_mask(g, r, s, &set_from(std::iter::once(d))));
                    }
                    if g.setup.color(s) == stm || g.setup.kind(s) == Kind::King {
                        return Step::Decided(None);
                    }
                    capture = Some(s);
                }
                // 3. Not attacked afterwards.
                let v = View { mover: None, captured: capture, anchor_at: Some(d) };
                match self.attacked(r, &v, KingPos::Anchor, stm.flip()) {
                    Step::Decided(true) => Step::Decided(None),
                    Step::Decided(false) => Step::Decided(Some(capture.is_some())),
                    Step::Split(ch) => Step::Split(ch),
                }
            }
            Cand::Slot(s, t) => {
                let d = r.off[s as usize];
                if d.present() == Some(false) {
                    return Step::Decided(None);
                }
                if d.cap {
                    return Step::Split(split_presence(g, r, s));
                }
                if t == zero {
                    return Step::Decided(None);
                }
                // 1. Origins that reach `t`.
                let geom = match g.setup.kind(s) {
                    Kind::King => set_from(set_iter(&g.all_offsets()).filter(|&o| g.dist_pair(o, t) == 1)),
                    Kind::Rook => set_from(set_iter(&g.all_offsets()).filter(|&o| g.aligned_pair(o, t))),
                    other => panic!("relative engine handles kings and rooks, not {other:?}"),
                };
                let inside = set_and(&d.set, &geom);
                if set_empty(&inside) {
                    return Step::Decided(None);
                }
                if inside != d.set {
                    return Step::Split(split_mask(g, r, s, &geom));
                }
                // 2. Target on the board from every anchor square.
                match split_anchor(g, r, |a| g.at(a, t).is_some()) {
                    Step::Decided(true) => {}
                    Step::Decided(false) => return Step::Decided(None),
                    Step::Split(ch) => return Step::Split(ch),
                }
                // 3. Occupancy of `t`.
                let mut capture = None;
                for c in 0..r.off.len() as SlotId {
                    if c == s || c == g.anchor || !set_has(&r.off[c as usize].set, t) {
                        continue;
                    }
                    if r.off[c as usize].pinned().is_none() {
                        return Step::Split(split_mask(g, r, c, &set_from(std::iter::once(t))));
                    }
                    if g.setup.color(c) == stm || g.setup.kind(c) == Kind::King {
                        return Step::Decided(None);
                    }
                    capture = Some(c);
                }
                // 4. A rook's path must be clear from every origin.
                if g.setup.kind(s) == Kind::Rook {
                    let mut path = [0u64; 4];
                    for o in set_iter(&d.set) {
                        let b = g.between(o, t);
                        for w in 0..4 {
                            path[w] |= b[w];
                        }
                    }
                    let cut = |x: Off| -> OffSet {
                        set_from(set_iter(&d.set).filter(|&o| !set_has(&g.between(o, t), x)))
                    };
                    if set_has(&path, zero) {
                        let keep = cut(zero);
                        if set_empty(&keep) {
                            return Step::Decided(None);
                        }
                        return Step::Split(split_mask(g, r, s, &keep));
                    }
                    for c in 0..r.off.len() as SlotId {
                        if c == s || c == g.anchor || set_empty(&set_and(&r.off[c as usize].set, &path)) {
                            continue;
                        }
                        match r.off[c as usize].pinned() {
                            None => return Step::Split(split_pin_in(g, r, c, &path)),
                            Some(x) => {
                                let keep = cut(x);
                                if set_empty(&keep) {
                                    return Step::Decided(None);
                                }
                                return Step::Split(split_mask(g, r, s, &keep));
                            }
                        }
                    }
                }
                // 5. Own king not attacked afterwards.
                let v = View { mover: Some((s, t)), captured: capture, anchor_at: None };
                let kp = if stm == self.roles.protected { KingPos::Anchor } else { KingPos::Slot(g.setup.king_slot(stm)) };
                match self.attacked(r, &v, kp, stm.flip()) {
                    Step::Decided(true) => Step::Decided(None),
                    Step::Decided(false) => Step::Decided(Some(capture.is_some())),
                    Step::Split(ch) => Step::Split(ch),
                }
            }
        }
    }

    pub fn can_move(&self, r: Rel, c: Cand) -> Vec<(Rel, Option<bool>)> {
        match self.step(&r, c) {
            Step::Decided(x) => vec![(r, x)],
            Step::Split(children) => children.into_iter().flat_map(|ch| self.can_move(ch, c)).collect(),
        }
    }

    fn victim(&self, r: &Rel, t: Off) -> SlotId {
        self.g.setup.slots_of(r.stm.flip()).find(|&v| v != self.g.anchor && r.off[v as usize].pinned() == Some(t)).expect("victim pinned at target")
    }

    pub fn play(&self, r: &Rel, c: Cand, capture: bool) -> Rel {
        let g = &self.g;
        let mut s = r.clone();
        match c {
            Cand::Anchor(d) => {
                if capture {
                    let v = self.victim(r, d);
                    s.off[v as usize] = OffDom { set: [0; 4], cap: true };
                }
                s.a = (0..g.setup.area() as Sq).filter(|&a| r.a & (1 << a) != 0).filter_map(|a| g.at(a, d)).map(|a| 1u64 << a).sum();
                for x in 0..s.off.len() as SlotId {
                    if x != g.anchor {
                        s.off[x as usize].set = g.shift(&s.off[x as usize].set, d, -1);
                    }
                }
            }
            Cand::Slot(m, t) => {
                if capture {
                    let v = self.victim(r, t);
                    s.off[v as usize] = OffDom { set: [0; 4], cap: true };
                }
                s.off[m as usize] = OffDom { set: set_from(std::iter::once(t)), cap: false };
            }
        }
        s.stm = r.stm.flip();
        assert!(s.normalize(g), "successor of a decided move is non-empty");
        s
    }

    pub fn pullback(&self, case: &Rel, child: &Rel, c: Cand, capture: bool) -> Option<Rel> {
        let g = &self.g;
        let mut r = child.clone();
        match c {
            Cand::Anchor(d) => {
                r.a = (0..g.setup.area() as Sq).filter(|&a| child.a & (1 << a) != 0).filter_map(|a| g.at(a, g.shift_off(d))).map(|a| 1u64 << a).sum();
                for x in 0..r.off.len() as SlotId {
                    if x != g.anchor {
                        r.off[x as usize].set = g.shift(&child.off[x as usize].set, d, 1);
                    }
                }
                if capture {
                    let v = self.victim(case, d);
                    r.off[v as usize] = OffDom { set: set_from(std::iter::once(d)), cap: false };
                }
            }
            Cand::Slot(m, t) => {
                r.off[m as usize] = case.off[m as usize];
                if capture {
                    let v = self.victim(case, t);
                    r.off[v as usize] = OffDom { set: set_from(std::iter::once(t)), cap: false };
                }
            }
        }
        r.stm = case.stm;
        if r.normalize(g) { Some(r) } else { None }
    }

    /// Legal part of `r` (side not to move not in check).
    pub fn legal(&self, r: Rel) -> Vec<Rel> {
        let not_stm = r.stm.flip();
        let kp = if not_stm == self.roles.protected { KingPos::Anchor } else { KingPos::Slot(self.g.setup.king_slot(not_stm)) };
        match self.attacked(&r, &View::NONE, kp, r.stm) {
            Step::Decided(true) => vec![],
            Step::Decided(false) => vec![r],
            Step::Split(ch) => ch.into_iter().flat_map(|c| self.legal(c)).collect(),
        }
    }

    fn mated_parts(&self, r: Rel) -> Vec<(Rel, bool)> {
        let stm = r.stm;
        let kp = if stm == self.roles.protected { KingPos::Anchor } else { KingPos::Slot(self.g.setup.king_slot(stm)) };
        match self.attacked(&r, &View::NONE, kp, stm.flip()) {
            Step::Decided(mated) => vec![(r, !mated)],
            Step::Split(ch) => ch.into_iter().flat_map(|c| self.mated_parts(c)).collect(),
        }
    }

    /// Own turn, disjoint refinement.
    pub fn exists_abs(&self, r: Rel) -> Vec<(Rel, bool)> {
        let mut out = Vec::new();
        let mut remaining: Vec<(Rel, bool)> = vec![(r, false)];
        for c in self.candidates(remaining[0].0.stm) {
            let mut next = Vec::new();
            for (sub, had) in remaining {
                for (case, legal) in self.can_move(sub, c) {
                    let Some(capture) = legal else { next.push((case, had)); continue };
                    let succ = self.play(&case, c, capture);
                    for (child, ok) in self.classify(succ) {
                        if let Some(back) = self.pullback(&case, &child, c, capture) {
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
            if had { out.push((sub, false)) } else { out.extend(self.mated_parts(sub)) }
        }
        out
    }

    /// Opponent turn, disjoint refinement.
    pub fn all_abs(&self, r: Rel) -> Vec<(Rel, bool)> {
        let mut out = Vec::new();
        let mut remaining = vec![r];
        for c in self.candidates(remaining[0].stm) {
            let mut next = Vec::new();
            for sub in remaining {
                for (case, legal) in self.can_move(sub, c) {
                    let Some(capture) = legal else { next.push(case); continue };
                    let succ = self.play(&case, c, capture);
                    for (child, ok) in self.classify(succ) {
                        if let Some(back) = self.pullback(&case, &child, c, capture) {
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

    /// Own turn as an overlapping cover of witness regions; positions under
    /// no witness are settled concretely.
    pub fn exists_cover(&self, r: Rel) -> Vec<(Rel, bool)> {
        let g = &self.g;
        let mut witnesses: Vec<Rel> = Vec::new();
        for c in self.candidates(r.stm) {
            for (case, legal) in self.can_move(r.clone(), c) {
                self.cases.set(self.cases.get() + 1);
                let Some(capture) = legal else { continue };
                let succ = self.play(&case, c, capture);
                for (child, ok) in self.classify(succ) {
                    self.cases.set(self.cases.get() + 1);
                    if ok {
                        witnesses.extend(self.pullback(&case, &child, c, capture));
                    }
                }
            }
        }
        self.witnesses.set(self.witnesses.get() + witnesses.len() as u64);
        let mut out = Vec::new();
        let mut owned: Vec<Vec<Position>> = vec![Vec::new(); witnesses.len()];
        for p in r.positions(g) {
            match witnesses.iter().position(|w| w.contains(g, &p)) {
                Some(i) => owned[i].push(p),
                None => {
                    let ok = legal_moves(g.setup, &p, p.stm).unwrap().is_empty() && !in_check(g.setup, &p, p.stm).unwrap();
                    out.push((self.single(&p), ok));
                }
            }
        }
        for (w, ps) in witnesses.into_iter().zip(owned) {
            if ps.is_empty() {
                continue;
            }
            if ps.len() == w.positions(g).len() {
                out.push((w, true));
            } else {
                out.extend(ps.iter().map(|p| (self.single(p), true)));
            }
        }
        out
    }

    /// Opponent turn as independent per-move checks.
    pub fn all_cover(&self, r: Rel) -> Vec<(Rel, bool)> {
        let g = &self.g;
        let mut bad: Vec<Rel> = Vec::new();
        for c in self.candidates(r.stm) {
            for (case, legal) in self.can_move(r.clone(), c) {
                self.cases.set(self.cases.get() + 1);
                let Some(capture) = legal else { continue };
                let succ = self.play(&case, c, capture);
                for (child, ok) in self.classify(succ) {
                    self.cases.set(self.cases.get() + 1);
                    if !ok {
                        bad.extend(self.pullback(&case, &child, c, capture));
                    }
                }
            }
        }
        if bad.is_empty() {
            return vec![(r, true)];
        }
        r.positions(g).into_iter().map(|p| { let b = bad.iter().any(|b| b.contains(g, &p)); (self.single(&p), !b) }).collect()
    }

    /// Debug: replay every candidate move on the single-position region of
    /// `p`, printing the abstract verdicts next to the concrete ones.
    pub fn explain(&self, p: &Position) {
        let g = &self.g;
        let r = self.single(p);
        let concrete: Vec<(Position, bool)> = legal_moves(g.setup, p, p.stm)
            .unwrap()
            .into_iter()
            .map(|mv| { let c = p.play(mv); let ok = cert::safe(g.setup, self.cert, &c, &self.roles); (c, ok) })
            .collect();
        let mut found: Vec<Position> = Vec::new();
        for c in self.candidates(r.stm) {
            for (case, legal) in self.can_move(r.clone(), c) {
                let Some(capture) = legal else { continue };
                let succ = self.play(&case, c, capture);
                let sp = succ.positions(g);
                for (child, ok) in self.classify(succ.clone()) {
                    let cp = child.positions(g);
                    for q in &cp {
                        let conc = concrete.iter().find(|(c, _)| c == q);
                        let cok = conc.map(|(_, ok)| *ok);
                        if conc.is_none() || cok != Some(ok) {
                            eprintln!("  {c:?} case {:?}\n  successor region {:?} ({} positions) -> abstract {ok}, concrete {cok:?}\n{}", case, succ, sp.len(), q.render(g.setup));
                        }
                        found.push(q.clone());
                    }
                }
            }
        }
        for (c, ok) in &concrete {
            if !found.contains(c) {
                eprintln!("  concrete successor not generated (safe {ok}):\n{}", c.render(g.setup));
            }
        }
    }

    fn single(&self, p: &Position) -> Rel {
        let g = &self.g;
        let a = p.sqs[g.anchor as usize].unwrap();
        Rel {
            a: 1 << a,
            off: (0..p.sqs.len() as SlotId)
                .map(|s| {
                    if s == g.anchor {
                        OffDom { set: [0; 4], cap: false }
                    } else {
                        match p.sqs[s as usize] {
                            Some(q) => OffDom { set: set_from(std::iter::once(g.off_between(a, q))), cap: false },
                            None => OffDom { set: [0; 4], cap: true },
                        }
                    }
                })
                .collect(),
            stm: p.stm,
        }
    }
}

impl Geo<'_> {
    /// The offset `-d`.
    fn shift_off(&self, d: Off) -> Off {
        let (dx, dy) = self.dxy(d);
        self.off(-dx, -dy)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Cand {
    /// The anchor steps by this offset.
    Anchor(Off),
    /// A non-anchor slot moves to this offset.
    Slot(SlotId, Off),
}

#[derive(Default, Debug, Clone)]
pub struct RelReport {
    pub legal_positions: usize,
    pub member_leaves: usize,
    pub safe_leaves: usize,
    pub safe_positions: usize,
    pub own_leaves: usize,
    pub own_positions: usize,
    pub opp_leaves: usize,
    pub opp_positions: usize,
    pub violating_positions: usize,
    pub cover_errors: usize,
    pub mismatches: usize,
    pub obligation_mismatches: usize,
    pub cases: u64,
    pub witnesses: u64,
    pub leaf_size_hist: [usize; 4],
}

/// Check the certificate over anchor-relative regions; `cover` selects the
/// overlapping-cover obligations instead of the disjoint refinement.
pub fn verify(table: &Table, cert: &Cert, protected: Color, cover: bool) -> RelReport {
    let setup = &table.setup;
    let eng = Engine::new(setup, cert, protected);
    let g = &eng.g;
    let mut rep = RelReport::default();
    let mut seen: Vec<u8> = vec![0; table.vals.len()];
    for stm in [Color::White, Color::Black] {
        for (leaf, member) in eng.classify(Rel::root(g, stm)) {
            let ps: Vec<Position> = leaf.positions(g).into_iter().filter(|p| table.vals[Table::index(setup, p)] != Val::Illegal).collect();
            if ps.is_empty() {
                continue;
            }
            rep.member_leaves += 1;
            rep.leaf_size_hist[match ps.len() { 1 => 0, 2..=3 => 1, 4..=15 => 2, _ => 3 }] += 1;
            for p in &ps {
                let i = Table::index(setup, p);
                seen[i] += 1;
                if cert::safe(setup, cert, p, &eng.roles) != member {
                    rep.mismatches += 1;
                }
            }
            if !member {
                continue;
            }
            rep.safe_leaves += 1;
            rep.safe_positions += ps.len();
            let own = stm == protected;
            let mut covered = 0;
            for legal in eng.legal(leaf) {
                let parts = match (own, cover) {
                    (true, false) => eng.exists_abs(legal),
                    (true, true) => eng.exists_cover(legal),
                    (false, false) => eng.all_abs(legal),
                    (false, true) => eng.all_cover(legal),
                };
                for (part, ok) in parts {
                    if own { rep.own_leaves += 1 } else { rep.opp_leaves += 1 }
                    let pps = part.positions(g);
                    covered += pps.len();
                    if !ok {
                        rep.violating_positions += pps.len();
                    }
                    for p in &pps {
                        if crate::symcert::concrete_obligation(setup, cert, p, &eng.roles) != ok {
                            rep.obligation_mismatches += 1;
                            if std::env::var_os("CHESS_DEBUG").is_some() && rep.obligation_mismatches <= 3 {
                                eprintln!("obligation mismatch: abstract says {ok}, part {:?}\n{}", part, p.render(setup));
                                eng.explain(p);
                            }
                        }
                    }
                }
            }
            if own { rep.own_positions += covered } else { rep.opp_positions += covered }
            if covered != ps.len() {
                rep.cover_errors += 1;
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
    rep.cases = eng.cases.get();
    rep.witnesses = eng.witnesses.get();
    rep
}
