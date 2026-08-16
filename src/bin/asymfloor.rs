//! Certified GF(2) floor for the asymmetric (free-weight-side) objective.
//!
//! Per class: min over the 6 tensor orientations of
//!   b_floor + c_floor, where
//!   b_floor = exact GF(2) XOR-adds for the x-side rows, and
//!   c_floor = exact GF(2) XOR-adds for gamma rows + (nonzero products - 9)
//!             (transposition principle, field-agnostic).
//! These floors lower-bound every {-1,0,1}-signed realization of the
//! class (support = bits, so the mod-2 image is the support itself).
//!
//! Usage: asymfloor FILE.bits ... | ASYM_LIST=file  [--max-slack 2]
//!        [--node-cap 5000000] [--threads N]

use logic::floors::*;
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
    let max_slack: u32 = opt("--max-slack", Some("2")).unwrap().parse().unwrap();
    let node_cap: u64 =
        opt("--node-cap", Some("5000000")).unwrap().parse().unwrap();
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
        eprintln!("usage: asymfloor FILE.bits ... (see source header)");
        std::process::exit(2);
    }
    use std::io::Write as _;
    let out = std::sync::Mutex::new(std::io::BufWriter::new(std::io::stdout()));
    let t0 = std::time::Instant::now();
    let done = std::sync::atomic::AtomicUsize::new(0);
    let n_total = files.len();
    files.par_iter().for_each(|path| {
        let bits = load_bits(path);
        if bits.len() != 621 {
            return;
        }
        let sm = bits_to_summands(&bits);
        debug_assert_eq!(brent_bad(&sm), 0);
        let mut best: Option<(u32, u32, u32, usize, bool)> = None;
        for (oi, var) in s3_variants(&sm).iter().enumerate() {
            let brows: Vec<u16> = var.iter().map(|&(_, b, _)| b).collect();
            // gamma rows = transpose of the summand's c-hat
            let grows: Vec<u16> =
                var.iter().map(|&(_, _, ct)| mat_transpose(ct)).collect();
            let nzp = grows.iter().filter(|&&g| g != 0).count() as u32;
            let rb = gf2_min_side(&brows, max_slack, node_cap);
            let rc = gf2_min_side(&grows, max_slack, node_cap);
            let cfl = rc.adds + nzp - 9;
            let fl = rb.adds + cfl;
            let ex = rb.exact && rc.exact;
            if best.map_or(true, |b| fl < b.0) {
                best = Some((fl, rb.adds, cfl, oi, ex));
            }
        }
        let (fl, bf, cf, oi, ex) = best.unwrap();
        {
            let mut o = out.lock().unwrap();
            let _ = writeln!(o,
                "{path}: floor {fl} = b{bf}+c{cf}  (orient {oi}, exact {ex})");
            let _ = o.flush();
        }
        let d = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
        if d % 5000 == 0 {
            eprintln!("progress: {d}/{n_total} in {:.0}s", t0.elapsed().as_secs_f64());
        }
    });
    eprintln!("{n_total} files in {:.1}s", t0.elapsed().as_secs_f64());
}
