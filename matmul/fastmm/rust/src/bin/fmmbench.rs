//! The library's entry points against Accelerate's GEMM, as test_fmm.c for the C library: the
//! plan used, correctness (max-norm relative difference), time (median of 3 after a warm-up),
//! leading dimensions larger than n, an error budget, sizes that are not powers of two, and
//! rectangular problems (one calibrated for its shape, the others priced by the planner's
//! estimates from the square calibration).
//!
//!   FMM_CALIB_DIR=../results cargo run --release --bin fmmbench [n ...]

use fmm::{Real, Shape};
use std::time::Instant;

/// the entry points of each precision: the square ones for a square shape, else the m, k, n ones
trait Fmm: Real {
    fn fmm(s: Shape, a: &[Self], lda: usize, b: &[Self], ldb: usize, c: &mut [Self], ldc: usize, g: f64) -> Result<(), fmm::Error>;
}
impl Fmm for f32 {
    fn fmm(s: Shape, a: &[f32], lda: usize, b: &[f32], ldb: usize, c: &mut [f32], ldc: usize, g: f64) -> Result<(), fmm::Error> {
        if s.is_sq() { fmm::sgemm(s.m, a, lda, b, ldb, c, ldc, g) } else { fmm::sgemm_mkn(s.m, s.k, s.n, a, lda, b, ldb, c, ldc, g) }
    }
}
impl Fmm for f64 {
    fn fmm(s: Shape, a: &[f64], lda: usize, b: &[f64], ldb: usize, c: &mut [f64], ldc: usize, g: f64) -> Result<(), fmm::Error> {
        if s.is_sq() { fmm::dgemm(s.m, a, lda, b, ldb, c, ldc, g) } else { fmm::dgemm_mkn(s.m, s.k, s.n, a, lda, b, ldb, c, ldc, g) }
    }
}

/// test_fmm.c's generator: uniform on [-1, 1), one state through all the cases
fn urand(s: &mut u64) -> f64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    (*s >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0
}

/// one case: an m x k matrix A (leading dimension lda), k x n B (ldb), m x n C (ldc), error
/// budget g, calibrated for the shape first when `calibrate` is set; the same inputs as test_fmm.c
/// (a square case draws a and b alternately, a rectangular one A then B)
fn run<T: Fmm>(s: Shape, lda: usize, ldb: usize, ldc: usize, g: f64, calibrate: bool, rng: &mut u64, failures: &mut usize) {
    let (na, nb, nc) = (s.m * lda, s.k * ldb, s.m * ldc);
    let (mut a, mut b) = (Vec::with_capacity(na), Vec::with_capacity(nb));
    if s.is_sq() && lda == ldb {
        for _ in 0..na {
            a.push(T::from_f64(urand(rng)));
            b.push(T::from_f64(urand(rng)));
        }
    } else {
        a.extend((0..na).map(|_| T::from_f64(urand(rng))));
        b.extend((0..nb).map(|_| T::from_f64(urand(rng))));
    }
    let mut c = vec![T::default(); nc];
    let mut r = vec![T::default(); nc];
    let mut tcal = 0.0;
    if calibrate {
        let t = Instant::now();
        fmm::calibrate_mkn(s.m, s.k, s.n, T::F64);
        tcal = t.elapsed().as_secs_f64();
    }
    let t = Instant::now();
    let info = fmm::plan_mkn(s.m, s.k, s.n, T::F64, g);
    let tplan = t.elapsed().as_secs_f64();
    let (mut tf, mut tr) = (vec![], vec![]);
    for rep in 0..4 {
        let t = Instant::now();
        let res = T::fmm(s, &a, lda, &b, ldb, &mut c, ldc, g);
        let dt = t.elapsed().as_secs_f64();
        if let Err(e) = res {
            println!("{e}");
            *failures += 1;
        }
        // the reference on this thread, as test_fmm (on a pool thread right after the fmm call
        // it runs up to 20% slower: examples/reference_after_fmm.rs)
        let t = Instant::now();
        T::gemm(s, &a, lda, &b, ldb, 0.0, &mut r, ldc);
        let dr = t.elapsed().as_secs_f64();
        if rep > 0 {
            tf.push(dt);
            tr.push(dr);
        }
    }
    tf.sort_by(|x, y| x.partial_cmp(y).unwrap());
    tr.sort_by(|x, y| x.partial_cmp(y).unwrap());
    let (mut err, mut mx) = (0.0f64, 0.0f64);
    for i in 0..s.m {
        for j in 0..s.n {
            err = err.max((c[i * ldc + j].to_f64() - r[i * ldc + j].to_f64()).abs());
            mx = mx.max(r[i * ldc + j].to_f64().abs());
        }
    }
    let rel = err / mx;
    let ok = rel < if T::F64 { 1e-11 } else { 1e-3 };
    *failures += !ok as usize;
    let plan = if info.spad != s { format!("{} padded to {}", info.plan, info.spad) } else { info.plan.to_string() };
    let pred = info.predicted.map_or("-".to_string(), |t| format!("{t:.4} s"));
    println!("{} {:<14} ld={:<5} budget {:<4} plan {:<30} fmm {:8.4} s  Accelerate {:8.4} s  speedup {:5.2}  rel. difference {}  {}  \
              (predicted {pred}{}; planning {tplan:.3} s)",
             if T::F64 { "f64" } else { "f32" }, s.to_string(), lda, g, plan, tf[1], tr[1], tr[1] / tf[1], fmm::calib::fmt_e(rel, 2),
             if ok { "ok" } else { "WRONG" }, if calibrate { ", calibrated for this shape" } else if s.is_sq() { "" } else { ", estimated" });
    if tcal > 1.0 {
        println!("   calibration {tcal:.0} s");
    }
}

fn main() {
    let mut sizes: Vec<usize> = std::env::args().skip(1).filter_map(|s| s.parse().ok()).collect();
    if sizes.is_empty() {
        sizes = vec![1000, 2048, 3000, 4096, 5000, 8192, 9000];
    }
    let (mut failures, mut rng) = (0, 0x9e3779b97f4a7c15u64);
    for f64 in [false, true] {
        let mut case = |s: Shape, lda, ldb, ldc, g, cal| {
            if f64 { run::<f64>(s, lda, ldb, ldc, g, cal, &mut rng, &mut failures) } else { run::<f32>(s, lda, ldb, ldc, g, cal, &mut rng, &mut failures) }
        };
        for &n in &sizes {
            case(Shape::sq(n), n, n, n, 0.0, false);
        }
        case(Shape::sq(4096), 4096 + 64, 4096 + 64, 4096 + 64, 0.0, false);     // leading dimensions larger than n
        case(Shape::sq(8192), 8192, 8192, 8192, 4.0, false);                    // an error budget
        for (s, cal) in [(Shape::new(3456, 3456, 1728), true), (Shape::new(1000, 3000, 2000), false),
                         (Shape::new(2048, 4096, 1024), false), (Shape::new(6912, 6912, 3456), false)] {
            case(s, s.k + 8, s.n + 8, s.n + 8, 0.0, cal);                       // rectangular problems, as test_fmm.c's
        }
    }
    fmm::release();
    println!("{}", if failures > 0 { "FAILED" } else { "all ok" });
    std::process::exit((failures > 0) as i32);
}
