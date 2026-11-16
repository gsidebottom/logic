//! Is each library deterministic?  The same product twice in Rust and twice in C (cbench), on the
//! shared calibration; counts the entries that differ between the runs.
//!   FMM_CALIB_DIR=.../results cargo run --release --features cbench --example determinism [n] [f64]
#![allow(unsafe_code)]
unsafe extern "C" {
    fn fmm_dgemm(n: usize, a: *const f64, lda: usize, b: *const f64, ldb: usize, c: *mut f64, ldc: usize, g: f64) -> i32;
    fn fmm_sgemm(n: usize, a: *const f32, lda: usize, b: *const f32, ldb: usize, c: *mut f32, ldc: usize, g: f64) -> i32;
    fn fmm_run_plan(plan: *const std::ffi::c_char, n: usize, f64: i32, a: *const f64, b: *const f64, c: *mut f64) -> i32;
}

/// the same named plan in both libraries (f64): entries that differ
fn plan_both(p: &str, n: usize, a: &[f64], b: &[f64]) -> usize {
    let plan = fmm::Plan::parse(p).unwrap();
    let s = fmm::Shape::sq(n);
    let mut work = vec![0.0f64; plan.work(s) + 16];
    let mut cr = vec![0.0f64; n * n];
    fmm::in_pool(|| fmm::exec::exec(&plan.0, s, a, n, b, n, &mut cr, n, &mut work));
    let mut cc = vec![0.0f64; n * n];
    let name = std::ffi::CString::new(p).unwrap();
    assert_eq!(unsafe { fmm_run_plan(name.as_ptr(), n, 1, a.as_ptr(), b.as_ptr(), cc.as_mut_ptr()) }, 0);
    cr.iter().zip(&cc).filter(|(x, y)| x.to_bits() != y.to_bits()).count()
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(6912);
    let f64 = args.get(2).is_some_and(|s| s == "f64");
    let mut s = 0x9e3779b97f4a7c15u64;
    let mut u = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; (s >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0 };
    println!("n {n} {} plan {}", if f64 { "f64" } else { "f32" }, fmm::plan(n, f64, 0.0).plan);
    if f64 {
        let a: Vec<f64> = (0..n * n).map(|_| u()).collect();
        let b: Vec<f64> = (0..n * n).map(|_| u()).collect();
        let run_r = || { let mut c = vec![0.0; n * n]; fmm::dgemm(n, &a, n, &b, n, &mut c, n, 0.0).unwrap(); c };
        let run_c = || { let mut c = vec![0.0; n * n]; unsafe { fmm_dgemm(n, a.as_ptr(), n, b.as_ptr(), n, c.as_mut_ptr(), n, 0.0) }; c };
        let d = |x: &[f64], y: &[f64]| x.iter().zip(y).filter(|(p, q)| p.to_bits() != q.to_bits()).count();
        let (r1, r2, c1, c2) = (run_r(), run_r(), run_c(), run_c());
        println!("rust vs rust {}  c vs c {}  rust vs c {}", d(&r1, &r2), d(&c1, &c2), d(&r1, &c1));
        for p in ["R336/G", "R363/G", "R633/G", "R336/G6", "R336/R363/G", "R336/R363/G6", "R336+2/R363/G6", "R363/R336/G", "D48/R363/G",
                  "R363/D48/G", "D48/G", "SW/G"] {
            if fmm::Plan::parse(p).is_some_and(|q| q.divides(fmm::Shape::sq(n))) {
                println!("  {p:<16} rust vs c {}", plan_both(p, n, &a, &b));
            }
        }
    } else {
        let a: Vec<f32> = (0..n * n).map(|_| u() as f32).collect();
        let b: Vec<f32> = (0..n * n).map(|_| u() as f32).collect();
        let run_r = || { let mut c = vec![0.0; n * n]; fmm::sgemm(n, &a, n, &b, n, &mut c, n, 0.0).unwrap(); c };
        let run_c = || { let mut c = vec![0.0; n * n]; unsafe { fmm_sgemm(n, a.as_ptr(), n, b.as_ptr(), n, c.as_mut_ptr(), n, 0.0) }; c };
        let d = |x: &[f32], y: &[f32]| x.iter().zip(y).filter(|(p, q)| p.to_bits() != q.to_bits()).count();
        let (r1, r2, c1, c2) = (run_r(), run_r(), run_c(), run_c());
        println!("rust vs rust {}  c vs c {}  rust vs c {}", d(&r1, &r2), d(&c1, &c2), d(&r1, &c1));
    }
}
