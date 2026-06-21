//! `gmi` — exact-rational Gomory cutting-plane refutation (see `src/gmi.rs`).
//!
//! Reads DIMACS CNF on stdin; on UNSAT-by-cutting-planes, emits a VeriPB proof.
//!
//! Usage:  gmi [--out FILE] [--max-rounds N] [--n-obj N] < problem.cnf
//! Verify: veripb problem.cnf FILE

use logic::gmi;
use std::io::{self, Read, Write};

fn parse_dimacs(s: &str) -> (usize, Vec<Vec<i32>>) {
    let mut nvars = 0usize;
    let mut clauses = Vec::new();
    let mut cur = Vec::new();
    for line in s.lines() {
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') || t.starts_with('%') {
            continue;
        }
        if let Some(rest) = t.strip_prefix("p cnf") {
            if let Some(v) = rest.split_whitespace().next() {
                nvars = v.parse().unwrap_or(0);
            }
            continue;
        }
        for tok in t.split_whitespace() {
            let lit: i32 = match tok.parse() {
                Ok(x) => x,
                Err(_) => continue,
            };
            if lit == 0 {
                clauses.push(std::mem::take(&mut cur));
            } else {
                cur.push(lit);
                let a = lit.unsigned_abs() as usize;
                if a > nvars {
                    nvars = a;
                }
            }
        }
    }
    if !cur.is_empty() {
        clauses.push(cur);
    }
    (nvars, clauses)
}

fn main() {
    let mut out: Option<String> = None;
    let mut max_rounds = 200usize;
    let mut n_obj = 4usize;
    let mut max_secs = 0.0f64;
    let args: Vec<String> = std::env::args().collect();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--out" => {
                i += 1;
                out = Some(args[i].clone());
            }
            "--max-rounds" => {
                i += 1;
                max_rounds = args[i].parse().unwrap_or(200);
            }
            "--n-obj" => {
                i += 1;
                n_obj = args[i].parse().unwrap_or(4);
            }
            "--max-secs" => {
                i += 1;
                max_secs = args[i].parse().unwrap_or(0.0);
            }
            _ => {}
        }
        i += 1;
    }

    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read stdin");
    let (nvars, clauses) = parse_dimacs(&input);

    let t0 = std::time::Instant::now();
    match gmi::refute(&clauses, nvars, max_rounds, n_obj, max_secs) {
        Some(r) => {
            let dt = t0.elapsed().as_secs_f64();
            let proof = gmi::emit(r.cons_len, &r);
            eprintln!(
                "c gmi: refuted — {} Gomory cuts + Farkas in {:.3}s",
                r.cuts.len(),
                dt
            );
            if let Some(path) = out {
                std::fs::write(&path, &proof).expect("write proof");
                eprintln!("c gmi: wrote {}", path);
            } else {
                io::stdout().write_all(proof.as_bytes()).ok();
            }
            println!("s UNSATISFIABLE");
        }
        None => {
            eprintln!("c gmi: not refuted by Gomory cuts (LP-feasible or round limit)");
            println!("s UNKNOWN");
        }
    }
}
