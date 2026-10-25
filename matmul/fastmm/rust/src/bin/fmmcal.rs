//! Fill the calibration cache once per machine (as bench_fmm -p for the C library): every entry
//! the planner needs for sizes up to n (a power of two), in each precision, then the plan and
//! predicted time per power of two.  Minutes; the machine should be otherwise idle.
//!
//!   cargo run --release --bin fmmcal [n [f32|f64]]       (FMM_CALIB_DIR picks the cache)

use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let n: usize = args.first().and_then(|s| s.parse().ok()).unwrap_or(16384);
    let precisions = match args.get(1).map(String::as_str) {
        Some("f32") => vec![false],
        Some("f64") => vec![true],
        _ => vec![false, true],
    };
    for f64 in precisions {
        let name = if f64 { "f64" } else { "f32" };
        let t = Instant::now();
        let cnt = fmm::calibrate(n, f64);
        println!("# {name}: {cnt} entries measured in {:.0} s, cache {}", t.elapsed().as_secs_f64(),
                 fmm::calib::path(f64).display());
        let mut m = 1024;
        while m <= n {
            let p = fmm::plan(m, f64, 0.0);
            let pred = p.predicted.map_or("-".to_string(), |t| format!("{t:.4} s"));
            let err = p.predicted_error.map_or("-".to_string(), |e| format!("{e:.2e}"));
            println!("{name} n={m:<6} plan {:<20} predicted {pred:>9}  error {err}", p.plan.to_string());
            m *= 2;
        }
    }
}
