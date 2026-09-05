//! Board geometry, piece model, and move generation over an *oracle*.
//!
//! Every query about the position goes through [`Oracle`]: "which slot sits
//! on square `sq`?" and "where is slot `s`?". A concrete [`Position`] answers
//! immediately. A superposed region (a set of positions) may not be able to
//! answer yet; it returns [`Blocked`] naming the query so the driver can fork
//! on its alternatives. Move generation is therefore written once and shared
//! by the retrograde ground-truth engine and the narrowing engine.

use std::fmt;

pub type Sq = u8;
pub type SlotId = u8;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Color {
    White,
    Black,
}

impl Color {
    pub fn flip(self) -> Color {
        match self {
            Color::White => Color::Black,
            Color::Black => Color::White,
        }
    }
    pub fn idx(self) -> usize {
        match self {
            Color::White => 0,
            Color::Black => 1,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Kind {
    King,
    Queen,
    Rook,
    Bishop,
    Knight,
}

impl Kind {
    pub fn letter(self) -> char {
        match self {
            Kind::King => 'K',
            Kind::Queen => 'Q',
            Kind::Rook => 'R',
            Kind::Bishop => 'B',
            Kind::Knight => 'N',
        }
    }
    pub fn parse(c: char) -> Option<Kind> {
        Some(match c.to_ascii_uppercase() {
            'K' => Kind::King,
            'Q' => Kind::Queen,
            'R' => Kind::Rook,
            'B' => Kind::Bishop,
            'N' => Kind::Knight,
            _ => return None,
        })
    }
    fn slides_orthogonal(self) -> bool {
        matches!(self, Kind::Queen | Kind::Rook)
    }
    fn slides_diagonal(self) -> bool {
        matches!(self, Kind::Queen | Kind::Bishop)
    }
}

/// The static part of a problem: board size and the piece slots. Slots are
/// fixed for the life of a search; a captured slot is simply off-board.
#[derive(Clone, Debug)]
pub struct Setup {
    pub n: u8,
    pub slots: Vec<(Color, Kind)>,
}

impl Setup {
    /// Parse "KRvK", "KQvKR", ... (white pieces, 'v', black pieces).
    pub fn parse(n: u8, spec: &str) -> Result<Setup, String> {
        let (w, b) = spec
            .split_once(['v', 'V'])
            .ok_or_else(|| format!("bad material spec {spec:?}: expected e.g. KRvK"))?;
        let mut slots = Vec::new();
        for (color, part) in [(Color::White, w), (Color::Black, b)] {
            for c in part.chars() {
                let k = Kind::parse(c).ok_or_else(|| format!("bad piece letter {c:?}"))?;
                slots.push((color, k));
            }
        }
        let kings = |c: Color| slots.iter().filter(|s| s.0 == c && s.1 == Kind::King).count();
        if kings(Color::White) != 1 || kings(Color::Black) != 1 {
            return Err("each side needs exactly one king".into());
        }
        if n < 2 || n > 8 {
            return Err("board size must be 2..=8".into());
        }
        Ok(Setup { n, slots })
    }
    pub fn area(&self) -> usize {
        self.n as usize * self.n as usize
    }
    pub fn king_slot(&self, c: Color) -> SlotId {
        self.slots
            .iter()
            .position(|s| s.0 == c && s.1 == Kind::King)
            .expect("king slot") as SlotId
    }
    pub fn slots_of(&self, c: Color) -> impl Iterator<Item = SlotId> + '_ {
        (0..self.slots.len() as SlotId).filter(move |&s| self.slots[s as usize].0 == c)
    }
    pub fn color(&self, s: SlotId) -> Color {
        self.slots[s as usize].0
    }
    pub fn kind(&self, s: SlotId) -> Kind {
        self.slots[s as usize].1
    }
    pub fn name(&self) -> String {
        let part = |c: Color| -> String {
            self.slots_of(c).map(|s| self.kind(s).letter()).collect()
        };
        format!("{}v{}", part(Color::White), part(Color::Black))
    }
    pub fn sq(&self, file: i32, rank: i32) -> Option<Sq> {
        let n = self.n as i32;
        if (0..n).contains(&file) && (0..n).contains(&rank) {
            Some((rank * n + file) as Sq)
        } else {
            None
        }
    }
    pub fn file_rank(&self, sq: Sq) -> (i32, i32) {
        ((sq % self.n) as i32, (sq / self.n) as i32)
    }
    pub fn step(&self, sq: Sq, df: i32, dr: i32) -> Option<Sq> {
        let (f, r) = self.file_rank(sq);
        self.sq(f + df, r + dr)
    }
    pub fn sq_name(&self, sq: Sq) -> String {
        let (f, r) = self.file_rank(sq);
        format!("{}{}", (b'a' + f as u8) as char, r + 1)
    }
    /// The 8 symmetries of the square board (pawnless chess), as square maps.
    pub fn symmetries(&self) -> Vec<Vec<Sq>> {
        let n = self.n as i32;
        let mut out = Vec::new();
        for flip_f in [false, true] {
            for flip_r in [false, true] {
                for transpose in [false, true] {
                    let map = (0..self.area() as Sq)
                        .map(|sq| {
                            let (mut f, mut r) = self.file_rank(sq);
                            if flip_f {
                                f = n - 1 - f;
                            }
                            if flip_r {
                                r = n - 1 - r;
                            }
                            if transpose {
                                std::mem::swap(&mut f, &mut r);
                            }
                            self.sq(f, r).unwrap()
                        })
                        .collect();
                    out.push(map);
                }
            }
        }
        out
    }
}

/// A query the oracle could not answer on the current region.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Blocked {
    /// Contents of a square are undecided.
    At(Sq),
    /// Location of a slot is undecided.
    Locate(SlotId),
}

pub type Res<T> = Result<T, Blocked>;

pub trait Oracle {
    /// Which slot occupies `sq`, if any.
    fn at(&self, sq: Sq) -> Res<Option<SlotId>>;
    /// Where slot `s` is; `None` means captured.
    fn locate(&self, s: SlotId) -> Res<Option<Sq>>;
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Move {
    pub slot: SlotId,
    pub from: Sq,
    pub to: Sq,
    pub capture: Option<SlotId>,
}

/// An oracle view of `base` after `mv` has been played.
pub struct Played<'a, O: Oracle> {
    pub base: &'a O,
    pub mv: Move,
}

impl<O: Oracle> Oracle for Played<'_, O> {
    fn at(&self, sq: Sq) -> Res<Option<SlotId>> {
        if sq == self.mv.to {
            Ok(Some(self.mv.slot))
        } else if sq == self.mv.from {
            Ok(None)
        } else {
            self.base.at(sq)
        }
    }
    fn locate(&self, s: SlotId) -> Res<Option<Sq>> {
        if s == self.mv.slot {
            Ok(Some(self.mv.to))
        } else if Some(s) == self.mv.capture {
            Ok(None)
        } else {
            self.base.locate(s)
        }
    }
}

const ORTHO: [(i32, i32); 4] = [(1, 0), (-1, 0), (0, 1), (0, -1)];
const DIAG: [(i32, i32); 4] = [(1, 1), (1, -1), (-1, 1), (-1, -1)];
const KNIGHT: [(i32, i32); 8] = [
    (1, 2),
    (2, 1),
    (-1, 2),
    (-2, 1),
    (1, -2),
    (2, -1),
    (-1, -2),
    (-2, -1),
];

/// Is `sq` attacked by any piece of color `by`? Scans outward from `sq`, so
/// it consults squares, not piece locations — a region can answer this
/// without knowing where every piece is.
pub fn attacked<O: Oracle>(setup: &Setup, o: &O, sq: Sq, by: Color) -> Res<bool> {
    // Sliders and adjacent king along the 8 rays.
    for (dirs, diag) in [(&ORTHO, false), (&DIAG, true)] {
        for &(df, dr) in dirs.iter() {
            let mut cur = sq;
            let mut dist = 0;
            while let Some(next) = setup.step(cur, df, dr) {
                dist += 1;
                if let Some(s) = o.at(next)? {
                    if setup.color(s) == by {
                        let k = setup.kind(s);
                        let hits = (dist == 1 && k == Kind::King)
                            || (diag && k.slides_diagonal())
                            || (!diag && k.slides_orthogonal());
                        if hits {
                            return Ok(true);
                        }
                    }
                    break;
                }
                cur = next;
            }
        }
    }
    for &(df, dr) in KNIGHT.iter() {
        if let Some(t) = setup.step(sq, df, dr) {
            if let Some(s) = o.at(t)? {
                if setup.color(s) == by && setup.kind(s) == Kind::Knight {
                    return Ok(true);
                }
            }
        }
    }
    Ok(false)
}

pub fn in_check<O: Oracle>(setup: &Setup, o: &O, c: Color) -> Res<bool> {
    match o.locate(setup.king_slot(c))? {
        Some(k) => attacked(setup, o, k, c.flip()),
        None => Ok(false),
    }
}

/// Pseudo-legal moves of slot `s` from `from` (destination empty or enemy).
fn piece_moves<O: Oracle>(
    setup: &Setup,
    o: &O,
    s: SlotId,
    from: Sq,
    out: &mut Vec<Move>,
) -> Res<()> {
    let color = setup.color(s);
    let kind = setup.kind(s);
    let consider = |to: Sq, out: &mut Vec<Move>| -> Res<bool> {
        // Returns whether the ray continues past `to`.
        match o.at(to)? {
            None => {
                out.push(Move { slot: s, from, to, capture: None });
                Ok(true)
            }
            Some(t) => {
                if setup.color(t) != color {
                    out.push(Move { slot: s, from, to, capture: Some(t) });
                }
                Ok(false)
            }
        }
    };
    match kind {
        Kind::King => {
            for &(df, dr) in ORTHO.iter().chain(DIAG.iter()) {
                if let Some(t) = setup.step(from, df, dr) {
                    consider(t, out)?;
                }
            }
        }
        Kind::Knight => {
            for &(df, dr) in KNIGHT.iter() {
                if let Some(t) = setup.step(from, df, dr) {
                    consider(t, out)?;
                }
            }
        }
        _ => {
            let dirs: Vec<(i32, i32)> = match kind {
                Kind::Queen => ORTHO.iter().chain(DIAG.iter()).copied().collect(),
                Kind::Rook => ORTHO.to_vec(),
                Kind::Bishop => DIAG.to_vec(),
                _ => unreachable!(),
            };
            for (df, dr) in dirs {
                let mut cur = from;
                while let Some(t) = setup.step(cur, df, dr) {
                    if !consider(t, out)? {
                        break;
                    }
                    cur = t;
                }
            }
        }
    }
    Ok(())
}

/// All legal moves for `stm`. Legality = own king not attacked afterwards.
pub fn legal_moves<O: Oracle>(setup: &Setup, o: &O, stm: Color) -> Res<Vec<Move>> {
    let mut pseudo = Vec::new();
    for s in setup.slots_of(stm) {
        if let Some(from) = o.locate(s)? {
            piece_moves(setup, o, s, from, &mut pseudo)?;
        }
    }
    let mut legal = Vec::with_capacity(pseudo.len());
    for mv in pseudo {
        let after = Played { base: o, mv };
        if !in_check(setup, &after, stm)? {
            legal.push(mv);
        }
    }
    Ok(legal)
}

/// A concrete position: one square (or none, if captured) per slot.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Position {
    pub sqs: Vec<Option<Sq>>,
    pub stm: Color,
}

impl Oracle for Position {
    fn at(&self, sq: Sq) -> Res<Option<SlotId>> {
        Ok(self
            .sqs
            .iter()
            .position(|&p| p == Some(sq))
            .map(|i| i as SlotId))
    }
    fn locate(&self, s: SlotId) -> Res<Option<Sq>> {
        Ok(self.sqs[s as usize])
    }
}

impl Position {
    pub fn play(&self, mv: Move) -> Position {
        let mut sqs = self.sqs.clone();
        sqs[mv.slot as usize] = Some(mv.to);
        if let Some(c) = mv.capture {
            sqs[c as usize] = None;
        }
        Position { sqs, stm: self.stm.flip() }
    }

    /// Basic legality: kings present, no square shared, the side not to move
    /// is not in check (it would have been captured otherwise).
    pub fn is_legal(&self, setup: &Setup) -> bool {
        for c in [Color::White, Color::Black] {
            if self.sqs[setup.king_slot(c) as usize].is_none() {
                return false;
            }
        }
        for i in 0..self.sqs.len() {
            for j in (i + 1)..self.sqs.len() {
                if self.sqs[i].is_some() && self.sqs[i] == self.sqs[j] {
                    return false;
                }
            }
        }
        !in_check(setup, self, self.stm.flip()).unwrap()
    }

    pub fn only_kings(&self, setup: &Setup) -> bool {
        (0..self.sqs.len() as SlotId)
            .all(|s| setup.kind(s) == Kind::King || self.sqs[s as usize].is_none())
    }

    pub fn transform(&self, map: &[Sq]) -> Position {
        Position {
            sqs: self.sqs.iter().map(|p| p.map(|sq| map[sq as usize])).collect(),
            stm: self.stm,
        }
    }

    pub fn render(&self, setup: &Setup) -> String {
        let mut s = String::new();
        for r in (0..setup.n as i32).rev() {
            s.push_str(&format!("{} ", r + 1));
            for f in 0..setup.n as i32 {
                let sq = setup.sq(f, r).unwrap();
                let ch = match self.at(sq).unwrap() {
                    Some(slot) => {
                        let l = setup.kind(slot).letter();
                        if setup.color(slot) == Color::White { l } else { l.to_ascii_lowercase() }
                    }
                    None => '.',
                };
                s.push(ch);
                s.push(' ');
            }
            s.push('\n');
        }
        s.push_str("  ");
        for f in 0..setup.n {
            s.push((b'a' + f) as char);
            s.push(' ');
        }
        s.push_str(&format!("  {:?} to move\n", self.stm));
        s
    }
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}->{}{}", self.from, self.to, if self.capture.is_some() { "x" } else { "" })
    }
}

pub fn move_str(setup: &Setup, mv: Move) -> String {
    format!(
        "{}{}{}{}",
        setup.kind(mv.slot).letter(),
        setup.sq_name(mv.from),
        if mv.capture.is_some() { "x" } else { "-" },
        setup.sq_name(mv.to)
    )
}
