//! Exact Z-rescoring of 3x3x23 candidate representatives, in-process
//! and parallel — the fast follow-up to `floors --emit-cands`.
//!
//! Usage:
//!   zrescore FILE.bits [FILE2.bits ...] [--models 24] [--crestarts 300]
//!            [--max-slack 3] [--node-cap 10000000] [--threads N]
//!            [--jackpot 55] [--quiet]
//!
//! Per file: enumerate Z-verified sign models (in-process CaDiCaL),
//! exact signed side minimization for A/B, restart-greedy C; prints
//! the best total per file and a JACKPOT banner at <= --jackpot.
//! Files are scored in parallel (embarrassingly parallel candidates).

use logic::zrescore::*;
use rayon::prelude::*;

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
    let models: usize = opt("--models", Some("24")).unwrap().parse().unwrap();
    let crestarts: u32 =
        opt("--crestarts", Some("300")).unwrap().parse().unwrap();
    let max_slack: u32 =
        opt("--max-slack", Some("3")).unwrap().parse().unwrap();
    let node_cap: u64 =
        opt("--node-cap", Some("10000000")).unwrap().parse().unwrap();
    let jackpot: u32 = opt("--jackpot", Some("55")).unwrap().parse().unwrap();
    if let Some(n) = opt("--threads", None) {
        rayon::ThreadPoolBuilder::new()
            .num_threads(n.parse().unwrap())
            .build_global()
            .unwrap();
    }
    let quiet = if let Some(i) = args.iter().position(|a| a == "--quiet") {
        args.remove(i);
        true
    } else {
        false
    };
    let files: Vec<String> =
        args.into_iter().filter(|a| !a.starts_with("--")).collect();
    if files.is_empty() {
        eprintln!("usage: zrescore FILE.bits ... (see source header)");
        std::process::exit(2);
    }
    let eqs = brent_equations();
    let t0 = std::time::Instant::now();
    let mut results: Vec<(String, Option<Score>)> = files
        .par_iter()
        .map(|path| {
            let s = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("{path}: {e}"));
            let tok = s.split_whitespace().last().expect("empty bits");
            assert_eq!(tok.len(), 621, "{path}: expected 621 bits");
            let bits: Vec<u8> =
                tok.chars().map(|c| (c as u8) - b'0').collect();
            assert_eq!(mod2_bad(&bits, &eqs), 0, "{path}: invalid mod 2");
            let sc = score_bits(&bits, &eqs, models, crestarts,
                                max_slack, node_cap);
            let stem = path
                .rsplit('/')
                .next()
                .unwrap()
                .trim_end_matches(".bits")
                .to_string();
            (stem, sc)
        })
        .collect();
    results.sort_by_key(|(_, sc)| sc.as_ref().map_or(u32::MAX, |s| s.total));
    let mut best_total = u32::MAX;
    for (stem, sc) in &results {
        match sc {
            None => println!("{stem:32} NOT +-1-liftable"),
            Some(s) => {
                best_total = best_total.min(s.total);
                let flag = if s.exact_sides { "" } else { " (sides open!)" };
                if !quiet || s.total <= jackpot {
                    println!(
                        "{stem:32} {} = {}+{}+{} (m{}){flag}",
                        s.total, s.a, s.b, s.c, s.model
                    );
                }
                if s.total <= jackpot {
                    println!("*** JACKPOT {} <= {jackpot}: {stem} ***",
                             s.total);
                }
            }
        }
    }
    eprintln!(
        "zrescore: {} files, best {} [{:.2}s]",
        results.len(),
        best_total,
        t0.elapsed().as_secs_f64()
    );
}
