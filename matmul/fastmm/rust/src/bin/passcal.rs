//! The Rust passes against the C library's calibration, entry by entry.
//!
//! Reads the pass entries of a calibration file written by the C library (kind m k n seconds, for
//! the levels SW, D48, R336, R363, R633: the three passes of the level whose products have shape
//! (m x k)(k x n)), measures each in Rust as the Rust calibration does (measure::level_pass_time)
//! and prints both with their ratio, then the geometric mean of the ratios by block size.
//!
//!   cargo run --release --bin passcal ../results/calib5_f32.txt [max block elements, default 1200^2]
//!
//! FMM_PASS_DISPATCH=iter|gcd picks another pass driver (exec::run_par), FMM_THREADS the pool's size.

use fmm::measure::level_pass_time;
use fmm::plan::{Level, Shape};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let path = args.first().expect("a calibration file of the C library");
    let maxel: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1200 * 1200);
    let text = std::fs::read_to_string(path).expect("reading the calibration file");
    let f64 = text.lines().next().is_some_and(|l| l.contains("f64"));
    println!("# Rust passes against the C library's calibrated passes ({}), {}; FMM_PASS_DISPATCH={} FMM_THREADS={}",
             path, if f64 { "f64" } else { "f32" }, std::env::var("FMM_PASS_DISPATCH").unwrap_or_else(|_| "spawn (default)".into()),
             std::env::var("FMM_THREADS").unwrap_or_else(|_| "all cores (default)".into()));
    let mut by_size: Vec<(usize, f64)> = vec![];
    for line in text.lines() {
        let w: Vec<&str> = line.split_whitespace().collect();
        if w.len() != 5 {
            continue;
        }
        let lv = match w[0] {
            "SW" => Level::Sw,
            "D48" => Level::D48,
            "R336" => Level::R336,
            "R363" => Level::R363,
            "R633" => Level::R633,
            _ => continue,
        };
        let (Ok(m), Ok(k), Ok(n), Ok(tc)) = (w[1].parse::<usize>(), w[2].parse::<usize>(), w[3].parse::<usize>(), w[4].parse::<f64>())
        else {
            continue;
        };
        let el = (m * k).max(k * n).max(m * n);
        if el > maxel || tc <= 0.0 {
            continue;
        }
        let t = Shape { m, k, n };
        let tr = if f64 { level_pass_time::<f64>(lv, t) } else { level_pass_time::<f32>(lv, t) };
        println!("{:<5} {:>5} {:>5} {:>5}  rust {:9.1} us  c {:9.1} us  rust/c {:5.2}", w[0], m, k, n, tr * 1e6, tc * 1e6, tr / tc);
        by_size.push((el, tr / tc));
    }
    for (lo, hi) in [(0usize, 300 * 300), (300 * 300, 600 * 600), (600 * 600, 1200 * 1200), (1200 * 1200, usize::MAX)] {
        let r: Vec<f64> = by_size.iter().filter(|(e, _)| *e > lo && *e <= hi).map(|x| x.1).collect();
        if !r.is_empty() {
            let gm = (r.iter().map(|x| x.ln()).sum::<f64>() / r.len() as f64).exp();
            let (mn, mx) = r.iter().fold((f64::MAX, 0f64), |(a, b), &x| (a.min(x), b.max(x)));
            println!("# largest block side {:>4} to {:>4}: {:3} entries, rust/c geometric mean {:.2} (min {:.2}, max {:.2})",
                     (lo as f64).sqrt() as usize, if hi == usize::MAX { 9999 } else { (hi as f64).sqrt() as usize }, r.len(), gm, mn, mx);
        }
    }
}
