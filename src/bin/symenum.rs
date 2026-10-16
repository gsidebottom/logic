//! Incremental AllSAT enumeration of the cyclic-quotient CNF: one
//! persistent CaDiCaL solver, block each solution's projection onto the
//! orbit-representative variables, re-solve.  Learned clauses persist
//! across solutions (the point: fresh-process kissat re-learns from
//! scratch every step and the census tail grows).
//!
//! Prints one `b <621 bits>` line per solution (the expansion of the
//! model through the orbit map; the Python driver re-verifies against
//! the full Brent system) and `s EXHAUSTED` when the instance goes
//! UNSAT — the census-complete certificate for the ansatz.
//!
//! usage: symenum cnf map [--max N]

use logic::cadical;

fn arg_val<T: std::str::FromStr>(args: &[String], key: &str) -> Option<T> {
    args.iter()
        .position(|a| a == key)
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cnf_path = &args[0];
    let map_path = &args[1];
    let max: usize = arg_val(&args, "--max").unwrap_or(usize::MAX);

    let mut solver: cadical::Solver = cadical::Solver::new();
    let txt = std::fs::read_to_string(cnf_path).expect("cnf");
    for line in txt.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('p') || line.starts_with('c') {
            continue;
        }
        let lits: Vec<i32> = line
            .split_whitespace()
            .map(|t| t.parse().unwrap())
            .take_while(|&l| l != 0)
            .collect();
        if !lits.is_empty() {
            solver.add_clause(lits.iter().copied());
        }
    }

    let mut map = vec![0u32; 621];
    for line in std::fs::read_to_string(map_path).expect("map").lines() {
        let mut it = line.split_whitespace();
        if let (Some(v), Some(r)) = (it.next(), it.next()) {
            let v: usize = v.parse().unwrap();
            map[v] = r.parse().unwrap();
        }
    }
    let mut reps: Vec<u32> = map.clone();
    reps.sort_unstable();
    reps.dedup();

    if let Some(dir) = args
        .iter()
        .position(|a| a == "--preblock-dir")
        .and_then(|i| args.get(i + 1))
    {
        let mut nb = 0usize;
        let mut names: Vec<_> = std::fs::read_dir(dir)
            .expect("preblock dir")
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|q| {
                q.extension().map(|x| x == "bits").unwrap_or(false)
            })
            .collect();
        names.sort();
        for path in names {
            let txt = std::fs::read_to_string(&path).unwrap();
            let bits: Vec<u8> = txt
                .split_whitespace()
                .last()
                .unwrap()
                .bytes()
                .map(|b| b - b'0')
                .collect();
            if bits.len() != 621 {
                continue;
            }
            let block: Vec<i32> = reps
                .iter()
                .map(|&r| {
                    let lit = (r + 1) as i32;
                    if bits[r as usize] == 1 { -lit } else { lit }
                })
                .collect();
            solver.add_clause(block.iter().copied());
            nb += 1;
        }
        eprintln!("c preblocked {nb} archived solutions");
    }

    let mut n = 0usize;
    while n < max {
        match solver.solve() {
            Some(true) => {}
            Some(false) => {
                println!("s EXHAUSTED after {n} solutions");
                return;
            }
            None => {
                println!("s UNKNOWN after {n} solutions");
                return;
            }
        }
        n += 1;
        let bits: String = (0..621)
            .map(|v| {
                let lit = (map[v] + 1) as i32;
                if solver.value(lit).unwrap_or(false) { '1' } else { '0' }
            })
            .collect();
        println!("b {bits}");
        use std::io::Write;
        std::io::stdout().flush().unwrap();
        let block: Vec<i32> = reps
            .iter()
            .map(|&r| {
                let lit = (r + 1) as i32;
                if solver.value(lit).unwrap_or(false) { -lit } else { lit }
            })
            .collect();
        solver.add_clause(block.iter().copied());
    }
    println!("s MAX reached ({n})");
}
