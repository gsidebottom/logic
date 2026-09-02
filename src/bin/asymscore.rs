//! Asymmetric (free-weight-side) rescoring: zkML-inference objective.
//!
//! For a fixed weight matrix W, every add on the scheme side that
//! lands on W is precomputed once — free. Score = min over the 6
//! tensor orientations and sign models of (x-side adds + output-side
//! adds), with the weight side rotated to whichever slot is cheapest
//! to give away.
//!
//! Usage:
//!   asymscore FILE.bits [...] [--models 24] [--max-slack 3]
//!             [--node-cap 10000000] [--threads N] [--jackpot 40]

use logic::zrescore::{asym_score_bits, brent_equations, NV};
use rayon::prelude::*;

fn load_bits(path: &str) -> Vec<u8> {
    std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("{path}: {e}"))
        .chars()
        .filter(|c| c.is_ascii_digit())
        .map(|c| (c as u8) - b'0')
        .collect()
}

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
    let max_slack: u32 = opt("--max-slack", Some("3")).unwrap().parse().unwrap();
    let node_cap: u64 =
        opt("--node-cap", Some("10000000")).unwrap().parse().unwrap();
    let jackpot: u32 = opt("--jackpot", Some("40")).unwrap().parse().unwrap();
    if let Some(n) = opt("--threads", None) {
        rayon::ThreadPoolBuilder::new()
            .num_threads(n.parse().unwrap())
            .build_global()
            .unwrap();
    }
    let mut files: Vec<String> =
        args.into_iter().filter(|a| !a.starts_with("--")).collect();
    if let Ok(v) = std::env::var("ASYM_LIST") {
        files.extend(
            std::fs::read_to_string(&v)
                .unwrap_or_else(|e| panic!("{v}: {e}"))
                .lines()
                .map(str::to_string),
        );
    }
    if files.is_empty() {
        eprintln!("usage: asymscore FILE.bits ... (see source header)");
        std::process::exit(2);
    }
    let eqs = brent_equations();
    let t0 = std::time::Instant::now();
    use std::io::Write as _;
    let out = std::sync::Mutex::new(std::io::BufWriter::new(std::io::stdout()));
    let done = std::sync::atomic::AtomicUsize::new(0);
    let n_total = files.len();
    files.par_iter().for_each(|path| {
        let bits = load_bits(path);
        if bits.len() != NV {
            return; // not a 3x3x23 file
        }
        let tf = std::time::Instant::now();
        let sc = asym_score_bits(&bits, &eqs, models, max_slack, node_cap);
        let secs = tf.elapsed().as_secs_f64();
        if secs > 10.0 {
            eprintln!("SLOW {path}: {:.1}s", secs);
        }
        {
            let mut o = out.lock().unwrap();
            match sc {
                Some(s) => {
                    let _ = writeln!(o,
                        "{path}: online {} = b{}+c{}  (free a{}, orient {}, model {}, exact {})",
                        s.online, s.b_side, s.c_side, s.free_a, s.orientation,
                        s.model, s.exact);
                }
                None => { let _ = writeln!(o, "{path}: no sign model"); }
            }
            let _ = o.flush();
        }
        if let Some(s) = sc {
            if s.online <= jackpot {
                eprintln!("JACKPOT {path}: online {} = b{}+c{} (a{} free, o{}, m{})",
                          s.online, s.b_side, s.c_side, s.free_a,
                          s.orientation, s.model);
            }
        }
        let d = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
        if d % 2000 == 0 {
            eprintln!("progress: {d}/{n_total} in {:.0}s", t0.elapsed().as_secs_f64());
        }
    });
    eprintln!("{} files in {:.1}s", n_total, t0.elapsed().as_secs_f64());
}
