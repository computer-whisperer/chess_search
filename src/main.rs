mod board;
mod retro;

use board::*;
use retro::*;
use std::time::Instant;

fn usage() -> ! {
    eprintln!(
        "usage:\n  chess_search retro [N] [MATERIAL]   solve by retrograde analysis (default 4 KRvK)\n  chess_search pv [N] [MATERIAL] [SLOT=SQ ...] [w|b]   print the PV from a position"
    );
    std::process::exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cmd = args.first().map(String::as_str).unwrap_or("retro");
    let n: u8 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(4);
    let material = args.get(2).map(String::as_str).unwrap_or("KRvK");
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
            println!("solved in {} passes, {:.2?}", table.passes, solve_time);
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
        _ => usage(),
    }
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
}
