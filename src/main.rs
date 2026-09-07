mod absmove;
mod board;
mod cert;
mod certs;
mod narrow;
mod retro;
mod symcert;
mod synth;

use board::*;
use cert::NFEAT;
use symcert::Mode;

const MODES: [Mode; 4] = [Mode::Pinning, Mode::Abstract, Mode::AbstractMoves, Mode::Cover];
use narrow::*;
use retro::*;
use std::time::Instant;

fn usage() -> ! {
    eprintln!(
        "usage:\n  chess_search retro [N] [MATERIAL]   solve by retrograde analysis (default 4 KRvK)\n  chess_search narrow [N] [MATERIAL] [--no-memo]   superposed (narrowing) solve, verified against the table\n  chess_search cert [N] [--cert4] [--symbolic]   check the codex_idea nonloss certificate for KRvKR on NxN (--cert4: apply the 4x4 certificate; --symbolic: also check over regions)\n  chess_search synth [N] [--vocab full|geo] [--symbolic]   synthesize a nonloss certificate for KRvKR on NxN under a feature vocabulary, then check it"
    );
    std::process::exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cmd = args.first().map(String::as_str).unwrap_or("retro");
    let n: u8 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(4);
    let material = if cmd == "cert" || cmd == "synth" { "KRvKR" } else { args.get(2).map(String::as_str).unwrap_or("KRvK") };
    let setup = match Setup::parse(n, material) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{e}");
            usage()
        }
    };
    match cmd {
        "retro" => {
            let t0 = Instant::now();
            let table = Table::solve(setup.clone());
            let solve_time = t0.elapsed();
            let st = table.stats();
            println!("{} on {}x{}: {} index slots, {} legal positions, {} up to symmetry",
                setup.name(), n, n, st.slots, st.legal, st.canonical);
            println!("solved in {} passes, {:.2?}, {} oracle queries ({:.1} per legal position)",
                table.passes, solve_time, table.queries, table.queries as f64 / st.legal as f64);
            for c in [Color::White, Color::Black] {
                let i = c.idx();
                println!("  {:?} to move: {} wins, {} losses, {} draws", c, st.wins[i], st.losses[i], st.draws[i]);
            }
            println!("max DTM {} plies", st.max_dtm);
            let hist: Vec<String> = st.dtm_hist.iter().enumerate().map(|(d, c)| format!("{d}:{c}")).collect();
            println!("DTM histogram (plies:count): {}", hist.join(" "));
            if let Some(p) = &st.longest {
                println!("longest: {:?}\n{}", table.get(p), p.render(&setup));
                let pv = table.pv(p);
                println!("PV: {}", pv.iter().map(|&m| move_str(&setup, m)).collect::<Vec<_>>().join(" "));
                let ps = table.proof_size(p);
                println!("proof DAG from longest: {} positions, of {} reachable", ps.proof_positions, ps.reachable);
            }
            let t1 = Instant::now();
            match table.verify() {
                Ok(()) => println!("verify: OK ({:.2?})", t1.elapsed()),
                Err(e) => {
                    println!("verify: FAILED: {e}");
                    std::process::exit(1);
                }
            }
        }
        "narrow" => {
            let no_memo = args.iter().any(|a| a == "--no-memo");
            let direct = args.iter().any(|a| a == "--direct");
            let reverse = args.iter().any(|a| a == "--reverse");
            let table = Table::solve(setup.clone());
            let st = table.stats();
            let t0 = Instant::now();
            let mut eng = Engine::new(setup.clone());
            eng.use_memo = !no_memo;
            eng.reverse_slots = reverse;
            let mut leaves = Vec::new();
            for stm in [Color::White, Color::Black] {
                leaves.extend(eng.solve_with(Region::root(&setup, stm), st.max_dtm, direct));
            }
            let elapsed = t0.elapsed();
            let rep = narrow_report(&table, &leaves, direct);
            println!("{} on {}x{}: {} legal positions ({} up to symmetry), max DTM {}",
                setup.name(), n, n, st.legal, st.canonical, st.max_dtm);
            println!("narrowing: {} leaves ({} illegal, {} win, {} loss, {} draw) in {:.2?}",
                leaves.len(), rep.illegal, rep.win, rep.loss, rep.draw, elapsed);
            println!("  work: {} oracle queries, {} forks, {} nodes, memo {} entries / {} hits",
                eng.counters.queries, eng.counters.forks, eng.counters.nodes, eng.counters.memo_entries, eng.counters.memo_hits);
            println!("  value leaves per legal position: {:.4}; queries per legal position: {:.3}",
                (leaves.len() - rep.illegal) as f64 / st.legal as f64, eng.counters.queries as f64 / st.legal as f64);
            println!("  distinct patterns: {}, legal positions matched per pattern (mean): {:.2}",
                rep.patterns, rep.pattern_matches as f64 / rep.patterns.max(1) as f64);
            match rep.error {
                None => println!("verify: OK (every legal position in exactly one leaf, verdicts and patterns agree with the table)"),
                Some(e) => {
                    println!("verify: FAILED: {e}");
                    std::process::exit(1);
                }
            }
        }
        "cert" => {
            let cert: certs::Cert = if args.iter().any(|a| a == "--cert4") || n == 4 {
                certs::weak4()
            } else if n == 5 {
                certs::weak5()
            } else {
                eprintln!("no certificate for {n}x{n}; use --cert4 to transfer the 4x4 one");
                std::process::exit(2);
            };
            let table = Table::solve(setup.clone());
            let st = table.stats();
            println!("{} on {}x{}: {} legal positions; certificate for {}x{} ({} decision nodes, root {})",
                setup.name(), n, n, st.legal, cert.board, cert.board, cert.nodes.len(), cert.root);
            for protected in [Color::White, Color::Black] {
                let t0 = Instant::now();
                let r = cert::verify(&table, &cert, protected);
                println!("protected {:?} ({:.2?}): root in invariant: {}; safe states {} of {} nonlosing ({:.1}%)",
                    protected, t0.elapsed(), r.root_in_invariant, r.safe_states, r.nonlosing_in_table,
                    100.0 * r.safe_states as f64 / r.nonlosing_in_table as f64);
                println!("  obligations: {} own-turn ({} candidate edges), {} opponent-turn ({} edges)",
                    r.own_turn_obligations, r.own_candidate_edges, r.opponent_turn_obligations, r.opponent_edges);
                println!("  violations: {} (mated inside {}, no preserving move {}, opponent escapes {} edges from {} states); unsound vs table: {}",
                    r.violations(), r.mated_inside, r.no_preserving_move, r.opponent_escapes, r.opponent_escape_states, r.unsound_vs_table);
                println!("  strategy graph: {} states, {} edges, {} own checkmates, {} stuck",
                    r.strategy_states, r.strategy_edges, r.strategy_own_checkmates, r.strategy_stuck);
                for mode in MODES.into_iter().filter(|_| args.iter().any(|a| a == "--symbolic")) {
                    let t0 = Instant::now();
                    let s = symcert::verify(&table, &cert, protected, mode);
                    println!("  symbolic, {:?} ({:.2?}): {} membership leaves over {} legal positions ({:.3} per position), {} safe leaves over {} safe positions",
                        mode, t0.elapsed(), s.member_leaves, s.legal_positions, s.member_leaves as f64 / s.legal_positions as f64,
                        s.safe_leaves, s.safe_positions);
                    println!("    obligations: own-turn {} leaves over {} positions ({:.3}); opponent-turn {} leaves over {} positions ({:.3}); violating positions {}",
                        s.own_leaves, s.own_positions, s.own_leaves as f64 / s.own_positions.max(1) as f64,
                        s.opp_leaves, s.opp_positions, s.opp_leaves as f64 / s.opp_positions.max(1) as f64, s.violating_positions);
                    println!("    work: {} oracle queries ({:.1} per legal position), {} forks; cross-check: {} cover errors, {} membership mismatches, {} obligation mismatches",
                        s.queries, s.queries as f64 / s.legal_positions as f64, s.forks, s.cover_errors, s.mismatches, s.obligation_mismatches);
                    println!("    membership leaf sizes: {} singletons, {} of 2-3, {} of 4-15, {} of 16+; walks needing move generation cover {} positions ({:.1}%)",
                        s.leaf_size_hist[0], s.leaf_size_hist[1], s.leaf_size_hist[2], s.leaf_size_hist[3],
                        s.movegen_positions, 100.0 * s.movegen_positions as f64 / s.legal_positions as f64);
                    let mut used: Vec<(usize, usize)> = s.feature_positions.iter().copied().enumerate().filter(|&(_, k)| k > 0).collect();
                    used.sort_by_key(|&(i, k)| (std::cmp::Reverse(k), i));
                    println!("    features consulted (positions): {}", used.iter()
                        .map(|&(i, k)| format!("{}={:.0}%", cert::FEATURE_NAMES[i], 100.0 * k as f64 / s.legal_positions as f64))
                        .collect::<Vec<_>>().join(" "));
                }
            }
        }
        "synth" => {
            let vocab: Vec<usize> = match args.iter().position(|a| a == "--vocab").and_then(|i| args.get(i + 1)).map(String::as_str) {
                None | Some("geo") => synth::GEO.collect(),
                Some("full") => synth::FULL.collect(),
                Some(v) => {
                    eprintln!("unknown vocabulary {v}");
                    std::process::exit(2);
                }
            };
            let table = Table::solve(setup.clone());
            let st = table.stats();
            let t0 = Instant::now();
            let sy = synth::synthesize(&table, &vocab);
            println!("{} on {}x{}: {} legal positions; vocabulary of {} features ({:.2?})",
                setup.name(), n, n, st.legal, vocab.len(), t0.elapsed());
            println!("  {} cells; fixpoint in {} rounds (removed {:?}); {} safe cells, {} safe states; roots ok {:?}",
                sy.cells, sy.rounds, sy.removed_by_round, sy.safe_cells, sy.safe_states, sy.roots_ok);
            println!("  tree: {} nodes before sharing, {} decision nodes after", sy.tree_nodes, sy.cert.nodes.len());
            let _ = std::fs::create_dir_all("out");
            let path = format!("out/synth_{}x{}_{}.json", n, n, if vocab.len() == NFEAT { "full" } else { "geo" });
            std::fs::write(&path, synth::to_json(&sy.cert, &vocab)).unwrap();
            println!("  certificate written to {path}");
            if !sy.roots_ok.iter().all(|&b| b) {
                println!("  the start position is not covered: this vocabulary admits no certificate for the start");
            }
            for protected in [Color::White, Color::Black] {
                let r = cert::verify(&table, &sy.cert, protected);
                println!("protected {:?}: root in invariant: {}; safe states {} of {} nonlosing; violations {}; unsound vs table {}",
                    protected, r.root_in_invariant, r.safe_states, r.nonlosing_in_table, r.violations(), r.unsound_vs_table);
                for mode in MODES.into_iter().filter(|_| args.iter().any(|a| a == "--symbolic")) {
                    let t0 = Instant::now();
                    let s = symcert::verify(&table, &sy.cert, protected, mode);
                    println!("  symbolic, {:?} ({:.2?}): {} membership leaves (+{} without legal positions) over {} legal positions ({:.3}); own-turn {} leaves / {} positions ({:.3}); opponent-turn {} / {} ({:.3}); violating {}; cross-check {} cover errors, {} membership mismatches, {} obligation mismatches",
                        mode, t0.elapsed(), s.member_leaves, s.empty_leaves, s.legal_positions, s.member_leaves as f64 / s.legal_positions as f64,
                        s.own_leaves, s.own_positions, s.own_leaves as f64 / s.own_positions.max(1) as f64,
                        s.opp_leaves, s.opp_positions, s.opp_leaves as f64 / s.opp_positions.max(1) as f64,
                        s.violating_positions, s.cover_errors, s.mismatches, s.obligation_mismatches);
                    println!("    leaf sizes: {:?}; move generation in {:.1}% of membership walks", s.leaf_size_hist,
                        100.0 * s.movegen_positions as f64 / s.legal_positions as f64);
                    if mode == Mode::Cover {
                        println!("    cover: {} cases (move decisions + membership classifications), {} witness regions, against {} concrete edges",
                            s.cases, s.witnesses, r.own_candidate_edges + r.opponent_edges);
                    }
                }
            }
        }
        _ => usage(),
    }
}

struct NarrowReport {
    illegal: usize,
    win: usize,
    loss: usize,
    draw: usize,
    patterns: usize,
    pattern_matches: usize,
    error: Option<String>,
}

/// Check the leaves against the table: exact cover of the legal positions,
/// verdict agreement per position, and pattern soundness (every legal
/// position matching a leaf's pattern has the leaf's verdict).
fn narrow_report(table: &Table, leaves: &[Leaf], direct: bool) -> NarrowReport {
    let setup = &table.setup;
    let mut rep = NarrowReport { illegal: 0, loss: 0, win: 0, draw: 0, patterns: 0, pattern_matches: 0, error: None };
    let mut seen = vec![false; table.vals.len()];
    let mut patterns = std::collections::HashSet::new();
    let legal: Vec<(usize, Position, Val)> = table
        .vals
        .iter()
        .enumerate()
        .filter(|(_, v)| **v != Val::Illegal)
        .map(|(i, v)| (i, Table::position(setup, i), *v))
        .collect();
    let agrees = |verdict: Verdict, v: Val| match (verdict, v) {
        (Verdict::Win(d), Val::Win(e)) => if direct { e <= d } else { d == e },
        (Verdict::Loss(d), Val::Loss(e)) => if direct { e <= d } else { d == e },
        (Verdict::Draw, Val::Draw) => true,
        _ => false,
    };
    for leaf in leaves {
        match leaf.verdict {
            Verdict::Illegal => rep.illegal += 1,
            Verdict::Win(_) => rep.win += 1,
            Verdict::Loss(_) => rep.loss += 1,
            Verdict::Draw => rep.draw += 1,
        }
        if !leaf.pattern.covers(&leaf.region) {
            rep.error = Some(format!("leaf pattern does not cover its region: {:?}", leaf));
            return rep;
        }
        for p in leaf.region.positions() {
            let i = Table::index(setup, &p);
            let v = table.vals[i];
            if leaf.verdict == Verdict::Illegal {
                if v != Val::Illegal {
                    rep.error = Some(format!("legal position {i} in an Illegal leaf"));
                    return rep;
                }
                continue;
            }
            if v == Val::Illegal {
                rep.error = Some(format!("illegal position {i} in a {:?} leaf", leaf.verdict));
                return rep;
            }
            if seen[i] {
                rep.error = Some(format!("position {i} covered twice"));
                return rep;
            }
            seen[i] = true;
            if !agrees(leaf.verdict, v) {
                rep.error = Some(format!("position {i}: leaf says {:?}, table says {v:?}\n{}", leaf.verdict, p.render(setup)));
                return rep;
            }
        }
        if leaf.verdict != Verdict::Illegal && patterns.insert((leaf.region.stm, leaf.pattern.clone())) {
            rep.patterns += 1;
            for (i, p, v) in &legal {
                if p.stm == leaf.region.stm && leaf.pattern.covers_position(p) {
                    rep.pattern_matches += 1;
                    if !agrees(leaf.verdict, *v) {
                        rep.error = Some(format!("pattern unsound: position {i} is {v:?} but pattern says {:?}\n{}", leaf.verdict, p.render(setup)));
                        return rep;
                    }
                }
            }
        }
    }
    if let Some((i, _, _)) = legal.iter().find(|(i, _, _)| !seen[*i]) {
        rep.error = Some(format!("legal position {i} not covered by any leaf"));
    }
    rep
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn krk_4x4_solves_and_verifies() {
        let setup = Setup::parse(4, "KRvK").unwrap();
        let table = Table::solve(setup);
        table.verify().unwrap();
        let st = table.stats();
        assert!(st.legal > 0);
        assert!(st.wins[0] > 0, "white should have some wins");
    }

    #[test]
    fn narrowing_agrees_with_table_krk_4x4() {
        let setup = Setup::parse(4, "KRvK").unwrap();
        let table = Table::solve(setup.clone());
        let dmax = table.stats().max_dtm;
        let mut eng = Engine::new(setup.clone());
        let mut leaves = Vec::new();
        for stm in [Color::White, Color::Black] {
            leaves.extend(eng.solve(Region::root(&setup, stm), dmax));
        }
        let rep = narrow_report(&table, &leaves, false);
        assert_eq!(rep.error, None);
    }

    #[test]
    fn back_rank_mate_is_loss_zero() {
        // 4x4: white Kb2? Use: black king a4 (sq 12), white king a2? Simplest:
        // black K at a4, white K at b2? Not adjacent-diagonal... place white K at b2 (sq 5):
        // a4 neighbors are a3, b3, b4. b2 does not touch a4. White rook on d4 (sq 15)
        // gives check along rank 4; escape squares a3 (attacked by Kb2), b3 (Kb2), b4 (rook, Kb2).
        let setup = Setup::parse(4, "KRvK").unwrap();
        let p = Position { sqs: vec![Some(5), Some(15), Some(12)], stm: Color::Black };
        assert!(p.is_legal(&setup));
        assert!(legal_moves(&setup, &p, Color::Black).unwrap().is_empty());
        let table = Table::solve(setup);
        assert_eq!(table.get(&p), Val::Loss(0));
    }
    /// The codex_idea 4x4 certificate, checked against the numbers in
    /// codex_idea/mini_rook_chess_results.json (verification4).
    #[test]
    fn codex_certificate_weak4_matches_reported_counts_and_table() {
        let setup = Setup::parse(4, "KRvKR").unwrap();
        let table = Table::solve(setup);
        let w = cert::verify(&table, &certs::weak4(), Color::White);
        assert_eq!(w.legal_states, 42552);
        assert!(w.root_in_invariant);
        assert_eq!(w.safe_states, 25380);
        assert_eq!(w.own_turn_obligations, 15464);
        assert_eq!(w.opponent_turn_obligations, 9916);
        assert_eq!(w.own_candidate_edges, 88696);
        assert_eq!(w.opponent_edges, 48324);
        assert_eq!(w.violations(), 0);
        assert_eq!(w.unsound_vs_table, 0);
        assert_eq!((w.strategy_states, w.strategy_edges, w.strategy_own_checkmates), (10018, 23891, 0));
        let b = cert::verify(&table, &certs::weak4(), Color::Black);
        assert!(b.root_in_invariant);
        assert_eq!(b.violations(), 0);
        assert_eq!(b.unsound_vs_table, 0);
        assert_eq!((b.strategy_states, b.strategy_edges, b.strategy_own_checkmates), (10704, 25451, 0));
    }

    /// The symbolic (region) check of the 4x4 certificate must partition the
    /// legal positions exactly and agree with the concrete evaluation.
    #[test]
    fn codex_certificate_weak4_symbolic_check_is_exact() {
        let setup = Setup::parse(4, "KRvKR").unwrap();
        let table = Table::solve(setup);
        let s = symcert::verify(&table, &certs::weak4(), Color::White, Mode::Pinning);
        assert_eq!(s.legal_positions, 42552);
        assert_eq!(s.safe_positions, 25380);
        assert_eq!((s.cover_errors, s.mismatches, s.violating_positions), (0, 0, 0));
        assert_eq!(s.own_positions + s.opp_positions, 25380);
    }

    /// Synthesis control: the full vocabulary must reproduce codex_idea's
    /// fixpoint (5,220 cells, 31,716 safe states); the geometric vocabulary
    /// must still yield an inductive certificate, and its abstract symbolic
    /// check must be exact.
    #[test]
    fn synthesis_reproduces_fixpoint_and_geo_certificate_is_inductive() {
        let setup = Setup::parse(4, "KRvKR").unwrap();
        let table = Table::solve(setup);
        let full = synth::synthesize(&table, &synth::FULL.collect::<Vec<_>>());
        assert_eq!((full.cells, full.safe_states, full.roots_ok), (5220, 31716, [true, true]));
        let geo = synth::synthesize(&table, &synth::GEO.collect::<Vec<_>>());
        assert_eq!((geo.safe_states, geo.roots_ok), (31700, [true, true]));
        for protected in [Color::White, Color::Black] {
            let r = cert::verify(&table, &geo.cert, protected);
            assert!(r.root_in_invariant);
            assert_eq!((r.violations(), r.unsound_vs_table), (0, 0));
            let s = symcert::verify(&table, &geo.cert, protected, Mode::Abstract);
            assert_eq!((s.cover_errors, s.mismatches, s.violating_positions), (0, 0, 0));
            assert!(s.member_leaves < s.legal_positions / 5, "abstract membership should be coarse: {}", s.member_leaves);
            assert_eq!(s.own_positions + s.opp_positions, 31700);
        }
    }

}
