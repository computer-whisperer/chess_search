//! Port of the "mini rook chess" nonloss certificate (codex_idea/): a decision
//! DAG over 36 relational features that describes an inductive safe region
//! for one side (the "protected" side), and the obligations that make it a
//! constructive nonloss proof:
//!
//! * the start position is in the region for both perspectives;
//! * at the protected side's turn, some legal move stays in the region
//!   (or the position is a stalemate);
//! * at the opponent's turn, every legal move stays in the region;
//! * no position in the region has the protected side checkmated.
//!
//! Features are computed through the `Oracle` trait so the same code runs
//! on a concrete `Position` and on a superposed region (see `symcert`).

use crate::board::*;
use crate::certs::Cert;
use crate::retro::{Table, Val};
use std::collections::{HashSet, VecDeque};

pub const NFEAT: usize = 36;

pub static FEATURE_NAMES: [&str; NFEAT] = [
    "opponent_to_move",
    "own_rook_missing",
    "opponent_rook_missing",
    "own_king_edge_distance",
    "own_king_corner",
    "opponent_king_edge_distance",
    "opponent_king_corner",
    "own_rook_edge_distance",
    "own_rook_corner",
    "opponent_rook_edge_distance",
    "opponent_rook_corner",
    "kings_distance",
    "kings_aligned",
    "kings_clear_ray",
    "own_king_rook_distance",
    "own_king_rook_aligned",
    "own_king_rook_clear_ray",
    "opponent_king_rook_distance",
    "opponent_king_rook_aligned",
    "opponent_king_rook_clear_ray",
    "own_king_enemy_rook_distance",
    "own_king_enemy_rook_aligned",
    "own_king_enemy_rook_clear_ray",
    "opponent_king_enemy_rook_distance",
    "opponent_king_enemy_rook_aligned",
    "opponent_king_enemy_rook_clear_ray",
    "rooks_distance",
    "rooks_aligned",
    "rooks_clear_ray",
    "in_check",
    "legal_move_count",
    "can_remove_opponent_rook",
    "can_remove_own_rook",
    "can_give_check",
    "can_mate",
    "can_stalemate",
];

/// Slot roles from the protected side's perspective (the certificate is
/// written for "White"; the other colour is handled by relabeling).
#[derive(Clone, Copy, Debug)]
pub struct Roles {
    pub protected: Color,
    pub own_k: SlotId,
    pub own_r: SlotId,
    pub opp_k: SlotId,
    pub opp_r: SlotId,
}

impl Roles {
    pub fn new(setup: &Setup, protected: Color) -> Roles {
        let rook = |c: Color| {
            let s: Vec<SlotId> = setup.slots_of(c).filter(|&s| setup.kind(s) == Kind::Rook).collect();
            assert_eq!(s.len(), 1, "certificate needs exactly one rook per side (KRvKR)");
            s[0]
        };
        let opp = protected.flip();
        Roles {
            protected,
            own_k: setup.king_slot(protected),
            own_r: rook(protected),
            opp_k: setup.king_slot(opp),
            opp_r: rook(opp),
        }
    }
    /// Slots in the certificate's normalized order [own K, own R, opp K, opp R].
    pub fn order(&self) -> [SlotId; 4] {
        [self.own_k, self.own_r, self.opp_k, self.opp_r]
    }
}

/// Chebyshev distance.
pub fn distance(setup: &Setup, p: Sq, q: Sq) -> i32 {
    let (px, py) = setup.file_rank(p);
    let (qx, qy) = setup.file_rank(q);
    (px - qx).abs().max((py - qy).abs())
}

pub fn aligned(setup: &Setup, p: Sq, q: Sq) -> bool {
    let (px, py) = setup.file_rank(p);
    let (qx, qy) = setup.file_rank(q);
    px == qx || py == qy
}

/// Aligned and no piece strictly between. Walks the squares between with
/// `at`, which is equivalent to the original's "any piece on a square
/// strictly between" test but lets a region answer without locating every
/// piece.
fn clear<O: Oracle>(setup: &Setup, o: &O, p: Sq, q: Sq) -> Res<bool> {
    if p == q || !aligned(setup, p, q) {
        return Ok(false);
    }
    let (px, py) = setup.file_rank(p);
    let (qx, qy) = setup.file_rank(q);
    let (df, dr) = ((qx - px).signum(), (qy - py).signum());
    let mut cur = setup.step(p, df, dr).unwrap();
    while cur != q {
        if o.at(cur)?.is_some() {
            return Ok(false);
        }
        cur = setup.step(cur, df, dr).unwrap();
    }
    Ok(true)
}

/// Slots in the certificate's piece order [own K, opp K, own R, opp R]
/// used by the edge/corner features.
pub fn piece_slots(roles: &Roles) -> [SlotId; 4] {
    [roles.own_k, roles.opp_k, roles.own_r, roles.opp_r]
}

/// Slot pairs of the relational features, in the certificate's order.
pub fn pair_slots(roles: &Roles) -> [(SlotId, SlotId); 6] {
    [
        (roles.own_k, roles.opp_k),
        (roles.own_k, roles.own_r),
        (roles.opp_k, roles.opp_r),
        (roles.own_k, roles.opp_r),
        (roles.opp_k, roles.own_r),
        (roles.own_r, roles.opp_r),
    ]
}

/// Feature `i` of the position seen by `o` (with `stm` to move), from the
/// perspective of `roles.protected`. Consults only what feature `i` needs,
/// so a region pays only for the features the DAG actually asks.
pub fn feature<O: Oracle>(setup: &Setup, o: &O, stm: Color, roles: &Roles, i: usize) -> Res<i32> {
    let n = setup.n as i32;
    Ok(match i {
        0 => (stm != roles.protected) as i32,
        1 => o.locate(roles.own_r)?.is_none() as i32,
        2 => o.locate(roles.opp_r)?.is_none() as i32,
        3..=10 => {
            let s = piece_slots(roles)[(i - 3) / 2];
            match o.locate(s)? {
                Some(p) => {
                    let (x, y) = setup.file_rank(p);
                    if (i - 3) % 2 == 0 {
                        x.min(y).min(n - 1 - x).min(n - 1 - y)
                    } else {
                        ((x == 0 || x == n - 1) && (y == 0 || y == n - 1)) as i32
                    }
                }
                None => {
                    if (i - 3) % 2 == 0 { -1 } else { 0 }
                }
            }
        }
        11..=28 => {
            let (a, b) = pair_slots(roles)[(i - 11) / 3];
            match (o.locate(a)?, o.locate(b)?) {
                (Some(p), Some(q)) => match (i - 11) % 3 {
                    0 => distance(setup, p, q),
                    1 => aligned(setup, p, q) as i32,
                    _ => clear(setup, o, p, q)? as i32,
                },
                _ => {
                    if (i - 11) % 3 == 0 { 99 } else { 0 }
                }
            }
        }
        29 => in_check(setup, o, stm)? as i32,
        30 => legal_moves(setup, o, stm)?.len() as i32,
        31..=35 => {
            let mut found = false;
            for mv in legal_moves(setup, o, stm)? {
                let t = Played { base: o, mv };
                found = match i {
                    31 => t.locate(roles.opp_r)?.is_none() && t.locate(roles.own_r)?.is_some(),
                    32 => t.locate(roles.own_r)?.is_none(),
                    33 => in_check(setup, &t, stm.flip())?,
                    34 => in_check(setup, &t, stm.flip())? && legal_moves(setup, &t, stm.flip())?.is_empty(),
                    _ => !in_check(setup, &t, stm.flip())? && legal_moves(setup, &t, stm.flip())?.is_empty(),
                };
                if found {
                    break;
                }
            }
            found as i32
        }
        _ => panic!("no feature {i}"),
    })
}

/// Walk the DAG on the position seen by `o`, computing features on demand.
/// Node ids 0/1 are the false/true terminals.
pub fn evaluate<O: Oracle>(setup: &Setup, cert: &Cert, o: &O, stm: Color, roles: &Roles) -> Res<bool> {
    evaluate_traced(setup, cert, o, stm, roles, &mut |_| {})
}

/// `evaluate`, reporting each feature index the walk consults.
pub fn evaluate_traced<O: Oracle>(
    setup: &Setup,
    cert: &Cert,
    o: &O,
    stm: Color,
    roles: &Roles,
    on_feature: &mut impl FnMut(usize),
) -> Res<bool> {
    let mut node = cert.root;
    while node >= 2 {
        let [feat, thr, l, r] = cert.nodes[node as usize - 2];
        on_feature(feat as usize);
        node = if feature(setup, o, stm, roles, feat as usize)? <= thr { l } else { r } as u32;
    }
    Ok(node == 1)
}

pub fn safe(setup: &Setup, cert: &Cert, p: &Position, roles: &Roles) -> bool {
    evaluate(setup, cert, p, p.stm, roles).expect("concrete positions never block")
}

/// The experiment's start: White Ka1 Rb1, Black K in the far corner with
/// the rook beside it, White to move.
pub fn start(setup: &Setup) -> Position {
    let m = setup.area() as Sq;
    let roles = Roles::new(setup, Color::White);
    let mut sqs = vec![None; setup.slots.len()];
    sqs[roles.own_k as usize] = Some(0);
    sqs[roles.own_r as usize] = Some(1);
    sqs[roles.opp_k as usize] = Some(m - 1);
    sqs[roles.opp_r as usize] = Some(m - 2);
    Position { sqs, stm: Color::White }
}

/// Sort key matching the original's deterministic policy: lexicographic on
/// the normalized state [own K, own R, opp K, opp R], captured = area.
fn policy_key(setup: &Setup, p: &Position, roles: &Roles) -> [u8; 4] {
    let m = setup.area() as u8;
    roles.order().map(|s| p.sqs[s as usize].unwrap_or(m))
}

#[derive(Default, Debug, Clone)]
pub struct Report {
    pub protected: Option<Color>,
    pub legal_states: usize,
    pub root_in_invariant: bool,
    pub safe_states: usize,
    pub own_turn_obligations: usize,
    pub opponent_turn_obligations: usize,
    pub own_candidate_edges: usize,
    pub opponent_edges: usize,
    /// Obligation failures: mated inside, no preserving move, opponent escape.
    pub mated_inside: usize,
    pub no_preserving_move: usize,
    pub opponent_escapes: usize,
    /// Opponent-turn positions with at least one escaping edge.
    pub opponent_escape_states: usize,
    /// Independent check against the retrograde table: safe positions that the
    /// table says the protected side loses (should be 0 if the certificate holds).
    pub unsound_vs_table: usize,
    /// Positions the table says are not lost for the protected side.
    pub nonlosing_in_table: usize,
    /// The deterministic policy's reachable strategy graph.
    pub strategy_states: usize,
    pub strategy_edges: usize,
    pub strategy_own_checkmates: usize,
    pub strategy_stuck: usize,
}

impl Report {
    pub fn violations(&self) -> usize {
        self.mated_inside + self.no_preserving_move + self.opponent_escapes
    }
}

/// Exhaustively check the certificate for one protected colour against every
/// legal position of the table, then walk the deterministic policy's strategy
/// graph from the start position.
pub fn verify(table: &Table, cert: &Cert, protected: Color) -> Report {
    let setup = &table.setup;
    let roles = Roles::new(setup, protected);
    let mut rep = Report { protected: Some(protected), ..Report::default() };
    let root = start(setup);
    rep.root_in_invariant = safe(setup, cert, &root, &roles);
    for (i, &v) in table.vals.iter().enumerate() {
        if v == Val::Illegal {
            continue;
        }
        rep.legal_states += 1;
        let p = Table::position(setup, i);
        let lost = match v {
            Val::Loss(_) => p.stm == protected,
            Val::Win(_) => p.stm != protected,
            _ => false,
        };
        if !lost {
            rep.nonlosing_in_table += 1;
        }
        if !safe(setup, cert, &p, &roles) {
            continue;
        }
        rep.safe_states += 1;
        if lost {
            rep.unsound_vs_table += 1;
        }
        let moves = legal_moves(setup, &p, p.stm).unwrap();
        if p.stm == protected {
            rep.own_turn_obligations += 1;
            if moves.is_empty() {
                if in_check(setup, &p, p.stm).unwrap() {
                    rep.mated_inside += 1;
                }
                continue;
            }
            rep.own_candidate_edges += moves.len();
            if !moves.iter().any(|&mv| safe(setup, cert, &p.play(mv), &roles)) {
                rep.no_preserving_move += 1;
            }
        } else {
            rep.opponent_turn_obligations += 1;
            let mut escaped = false;
            for mv in moves {
                rep.opponent_edges += 1;
                if !safe(setup, cert, &p.play(mv), &roles) {
                    rep.opponent_escapes += 1;
                    escaped = true;
                }
            }
            rep.opponent_escape_states += escaped as usize;
        }
    }
    // Strategy graph of the fixed policy: first preserving successor in
    // normalized lexicographic order; all opponent replies.
    let mut seen: HashSet<Position> = HashSet::new();
    let mut queue = VecDeque::new();
    seen.insert(root.clone());
    queue.push_back(root);
    while let Some(p) = queue.pop_front() {
        rep.strategy_states += 1;
        let moves = legal_moves(setup, &p, p.stm).unwrap();
        let mut next: Vec<Position> = Vec::new();
        if p.stm == protected {
            if moves.is_empty() {
                if in_check(setup, &p, p.stm).unwrap() {
                    rep.strategy_own_checkmates += 1;
                }
                continue;
            }
            let mut cands: Vec<Position> = moves.iter().map(|&mv| p.play(mv)).collect();
            cands.sort_by_key(|c| policy_key(setup, c, &roles));
            match cands.into_iter().find(|c| safe(setup, cert, c, &roles)) {
                Some(c) => next.push(c),
                None => rep.strategy_stuck += 1,
            }
        } else {
            next.extend(moves.iter().map(|&mv| p.play(mv)));
        }
        for c in next {
            rep.strategy_edges += 1;
            if seen.insert(c.clone()) {
                queue.push_back(c);
            }
        }
    }
    rep
}
