//! Orbit-wide GF(2) side-cost floors for 3x3x23 schemes (fast Rust
//! port of matmul/orbitscan.py's exhaustive table scan).
//!
//! Usage:
//!   floors FILE.bits [FILE2.bits ...]
//!     [--variants 012345] [--cutoff 57] [--max-slack 3]
//!     [--node-cap 10000000] [--floors-only] [--emit-cands DIR]
//!     [--max-emit 200] [--threads N]
//!
//! Per S3 variant: builds the three 168x168 exact-GF(2) side-cost
//! tables (A on (P,Q), B on (Q,R), C-greedy-estimate on (R,P)) and
//! scans all 168^3 sandwiches.  `floor` lines are SOUND orbit-wide
//! lower bounds on Z input-side additions; `est` values are ranking
//! estimates (C is greedy).  --floors-only skips the C table (A+B
//! floors only, ~2/3 the work) — the mode for database-wide sweeps.
//! --emit-cands writes candidate representatives (est <= cutoff) as
//! .bits files for exact Z re-scoring in Python (matmul/sidemin.py).

use logic::floors::*;
use std::time::Instant;

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut opt = |name: &str, default: Option<&str>| -> Option<String> {
        if let Some(i) = args.iter().position(|a| a == name) {
            let v = args.get(i + 1).cloned();
            args.drain(i..=i);
            if v.is_some() {
                args.remove(i);
            }
            v
        } else {
            default.map(String::from)
        }
    };
    let variants: Vec<usize> = opt("--variants", Some("012345"))
        .unwrap()
        .chars()
        .map(|c| c.to_digit(10).unwrap() as usize)
        .collect();
    let cutoff: u32 = opt("--cutoff", Some("57")).unwrap().parse().unwrap();
    let max_slack: u32 =
        opt("--max-slack", Some("3")).unwrap().parse().unwrap();
    let node_cap: u64 =
        opt("--node-cap", Some("10000000")).unwrap().parse().unwrap();
    let emit_dir = opt("--emit-cands", None);
    // emit EVERY distinct rep with exact GF2 sides A+B <= this budget
    // (the sides-exhaust enumeration; C table skipped) — feed zrescore
    let emit_sides: Option<u32> =
        opt("--emit-sides", None).map(|s| s.parse().unwrap());
    let max_emit: usize =
        opt("--max-emit", Some("200000")).unwrap().parse().unwrap();
    if let Some(n) = opt("--threads", None) {
        rayon::ThreadPoolBuilder::new()
            .num_threads(n.parse().unwrap())
            .build_global()
            .unwrap();
    }
    let floors_only = if let Some(i) =
        args.iter().position(|a| a == "--floors-only")
    {
        args.remove(i);
        true
    } else {
        false
    };
    let files: Vec<String> =
        args.into_iter().filter(|a| !a.starts_with("--")).collect();
    if files.is_empty() {
        eprintln!("usage: floors FILE.bits ... (see source header)");
        std::process::exit(2);
    }
    let gl = gl3();
    if let Some(d) = &emit_dir {
        std::fs::create_dir_all(d).unwrap();
    }

    for path in &files {
        let s = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("{path}: {e}"));
        let tok = s.split_whitespace().last().expect("empty bits file");
        assert_eq!(tok.len(), 621, "{path}: expected 621 bits");
        let bits: Vec<u8> = tok.chars().map(|c| (c as u8) - b'0').collect();
        let sm = bits_to_summands(&bits);
        assert_eq!(brent_bad(&sm), 0, "{path}: Brent mod-2 check failed");
        let stem = path
            .rsplit('/')
            .next()
            .unwrap()
            .trim_end_matches(".bits");
        let vlist = s3_variants(&sm);
        let mut file_floor = u32::MAX;
        let mut file_best_est = u32::MAX;
        let mut emitted = 0usize;
        let mut seen = std::collections::HashSet::new();
        for &vi in &variants {
            let t0 = Instant::now();
            if let Some(budget) = emit_sides {
                let dir = emit_dir.as_ref().expect(
                    "--emit-sides requires --emit-cands DIR");
                let t = side_tables(&vlist[vi], &gl, max_slack, node_cap,
                                    false);
                let mut n_triples = 0usize;
                for q in 0..NG {
                    for p in 0..NG {
                        let a = t.a[p * NG + q] as u32;
                        if a + (0..NG)
                            .map(|r_| t.b[q * NG + r_] as u32)
                            .min()
                            .unwrap()
                            > budget
                        {
                            continue;
                        }
                        for r_ in 0..NG {
                            if a + t.b[q * NG + r_] as u32 > budget {
                                continue;
                            }
                            n_triples += 1;
                            if emitted >= max_emit {
                                continue;
                            }
                            let img =
                                apply_pqr(&vlist[vi], &gl, p, q, r_);
                            let nb = summands_to_bits(&img);
                            let key: String = nb
                                .iter()
                                .map(|b| (b + b'0') as char)
                                .collect();
                            if !seen.insert(key.clone()) {
                                continue;
                            }
                            let sd = a + t.b[q * NG + r_] as u32;
                            let fname = format!(
                                "{dir}/{stem}-v{vi}-s{sd}-{p}_{q}_{r_}.bits"
                            );
                            std::fs::write(&fname, key + "\n").unwrap();
                            emitted += 1;
                        }
                    }
                }
                println!(
                    "{stem} v{vi} sides<={budget}: {n_triples} triples, \
                     {emitted} distinct emitted so far  [{:.2}s]",
                    t0.elapsed().as_secs_f64()
                );
                continue;
            }
            let t = side_tables(&vlist[vi], &gl, max_slack, node_cap,
                                !floors_only);
            let r = scan(&t, cutoff);
            file_floor = file_floor.min(r.floor_sides);
            let dt = t0.elapsed().as_secs_f64();
            if floors_only {
                println!(
                    "{stem} v{vi} floor {}  [{dt:.2}s{}]",
                    r.floor_sides,
                    if t.open_cells > 0 {
                        format!(", {} open cells", t.open_cells)
                    } else {
                        String::new()
                    }
                );
            } else {
                file_best_est = file_best_est.min(r.best_est);
                println!(
                    "{stem} v{vi} floor {}  est-best {}  cands<= {}: {}  \
                     [{dt:.2}s{}]",
                    r.floor_sides,
                    r.best_est,
                    cutoff,
                    r.cands.len(),
                    if t.open_cells > 0 {
                        format!(", {} open cells", t.open_cells)
                    } else {
                        String::new()
                    }
                );
                if let Some(dir) = &emit_dir {
                    for &(est, p, q, r_) in &r.cands {
                        if emitted >= max_emit {
                            break;
                        }
                        let img = apply_pqr(
                            &vlist[vi],
                            &gl,
                            p as usize,
                            q as usize,
                            r_ as usize,
                        );
                        let nb = summands_to_bits(&img);
                        let key: String =
                            nb.iter().map(|b| (b + b'0') as char).collect();
                        if !seen.insert(key.clone()) {
                            continue;
                        }
                        let fname = format!(
                            "{dir}/{stem}-v{vi}-e{est}-{p}_{q}_{r_}.bits"
                        );
                        std::fs::write(&fname, key + "\n").unwrap();
                        emitted += 1;
                    }
                }
            }
        }
        if emit_sides.is_some() {
            println!("{stem} EMITTED {emitted} distinct reps");
        } else if floors_only {
            println!("{stem} FLOOR {file_floor}");
        } else {
            println!(
                "{stem} FLOOR {file_floor}  EST-BEST {file_best_est}{}",
                if emit_dir.is_some() {
                    format!("  emitted {emitted}")
                } else {
                    String::new()
                }
            );
        }
    }
}
