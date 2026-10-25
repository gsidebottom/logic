//! The library's entry points against Accelerate's GEMM, as test_fmm.c for the C library: the
//! plan used, correctness (max-norm relative difference), time (median of 3 after a warm-up),
//! leading dimensions larger than n, an error budget, sizes that are not powers of two.
//!
//!   FMM_CALIB_DIR=../results cargo run --release --bin fmmbench [n ...]

use fmm::Real;
use std::time::Instant;

/// the entry point of each precision
trait Fmm: Real {
    fn fmm(n: usize, a: &[Self], lda: usize, b: &[Self], ldb: usize, c: &mut [Self], ldc: usize, g: f64) -> Result<(), fmm::Error>;
}
impl Fmm for f32 {
    fn fmm(n: usize, a: &[f32], lda: usize, b: &[f32], ldb: usize, c: &mut [f32], ldc: usize, g: f64) -> Result<(), fmm::Error> {
        fmm::sgemm(n, a, lda, b, ldb, c, ldc, g)
    }
}
impl Fmm for f64 {
    fn fmm(n: usize, a: &[f64], lda: usize, b: &[f64], ldb: usize, c: &mut [f64], ldc: usize, g: f64) -> Result<(), fmm::Error> {
        fmm::dgemm(n, a, lda, b, ldb, c, ldc, g)
    }
}

/// test_fmm.c's generator: uniform on [-1, 1), one state through all the cases
fn urand(s: &mut u64) -> f64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    (*s >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0
}

/// one case: n x n inside ld x ld storage, error budget g; the same inputs as test_fmm.c's
fn run<T: Fmm>(n: usize, ld: usize, g: f64, rng: &mut u64, failures: &mut usize) {
    let cnt = n * ld;
    let (mut a, mut b) = (Vec::with_capacity(cnt), Vec::with_capacity(cnt));
    for _ in 0..cnt {
        a.push(T::from_f64(urand(rng)));
        b.push(T::from_f64(urand(rng)));
    }
    let mut c = vec![T::default(); cnt];
    let mut r = vec![T::default(); cnt];
    let info = fmm::plan(n, T::F64, g);
    let (mut tf, mut tr) = (vec![], vec![]);
    for rep in 0..4 {
        let t = Instant::now();
        let res = T::fmm(n, &a, ld, &b, ld, &mut c, ld, g);
        let dt = t.elapsed().as_secs_f64();
        if let Err(e) = res {
            println!("{e}");
            *failures += 1;
        }
        // the reference on this thread, as test_fmm (on a pool thread right after the fmm call
        // it runs up to 20% slower: examples/reference_after_fmm.rs)
        let t = Instant::now();
        T::gemm(n, &a, ld, &b, ld, 0.0, &mut r, ld);
        let dr = t.elapsed().as_secs_f64();
        if rep > 0 {
            tf.push(dt);
            tr.push(dr);
        }
    }
    tf.sort_by(|x, y| x.partial_cmp(y).unwrap());
    tr.sort_by(|x, y| x.partial_cmp(y).unwrap());
    let (mut err, mut mx) = (0.0f64, 0.0f64);
    for i in 0..n {
        for j in 0..n {
            err = err.max((c[i * ld + j].to_f64() - r[i * ld + j].to_f64()).abs());
            mx = mx.max(r[i * ld + j].to_f64().abs());
        }
    }
    let rel = err / mx;
    let ok = rel < if T::F64 { 1e-11 } else { 1e-3 };
    *failures += !ok as usize;
    let plan = if info.npad != n { format!("{} padded to {}", info.plan, info.npad) } else { info.plan.to_string() };
    println!("{} n={:<5} ld={:<5} budget {:<4} plan {:<30} fmm {:8.4} s  Accelerate {:8.4} s  speedup {:5.2}  rel. difference {}  {}",
             if T::F64 { "f64" } else { "f32" }, n, ld, g, plan, tf[1], tr[1], tr[1] / tf[1], fmm::calib::fmt_e(rel, 2), if ok { "ok" } else { "WRONG" });
}

fn main() {
    let mut sizes: Vec<usize> = std::env::args().skip(1).filter_map(|s| s.parse().ok()).collect();
    if sizes.is_empty() {
        sizes = vec![1000, 2048, 3000, 4096, 5000, 8192, 9000];
    }
    let (mut failures, mut rng) = (0, 0x9e3779b97f4a7c15u64);
    for f64 in [false, true] {
        let mut case = |n, ld, g| {
            if f64 { run::<f64>(n, ld, g, &mut rng, &mut failures) } else { run::<f32>(n, ld, g, &mut rng, &mut failures) }
        };
        for &n in &sizes {
            case(n, n, 0.0);
        }
        case(4096, 4096 + 64, 0.0);   // leading dimensions larger than n
        case(8192, 8192, 4.0);        // an error budget
    }
    fmm::release();
    println!("{}", if failures > 0 { "FAILED" } else { "all ok" });
    std::process::exit((failures > 0) as i32);
}
