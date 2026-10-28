//! The Rust library against the C library (matmul/fastmm/build/libfmm.a, linked in) on the same
//! inputs and calibration cache: the plan each picks and their results, bit for bit.  The cases
//! of test_fmm.c (sizes, a leading dimension larger than n, an error budget, rectangular problems
//! calibrated and estimated).
//!
//!   make build/libfmm.a    (in matmul/fastmm)
//!   FMM_CALIB_DIR=../results cargo run --release --features cbench --bin crosscheck [n ...]
#![allow(unsafe_code)]

use fmm::{Real, Shape};
use std::ffi::{c_char, CStr};

unsafe extern "C" {
    fn fmm_sgemm(n: usize, a: *const f32, lda: usize, b: *const f32, ldb: usize, c: *mut f32, ldc: usize, g: f64) -> i32;
    fn fmm_dgemm(n: usize, a: *const f64, lda: usize, b: *const f64, ldb: usize, c: *mut f64, ldc: usize, g: f64) -> i32;
    fn fmm_sgemm_mkn(m: usize, k: usize, n: usize, a: *const f32, lda: usize, b: *const f32, ldb: usize, c: *mut f32, ldc: usize,
                     g: f64) -> i32;
    fn fmm_dgemm_mkn(m: usize, k: usize, n: usize, a: *const f64, lda: usize, b: *const f64, ldb: usize, c: *mut f64, ldc: usize,
                     g: f64) -> i32;
    fn fmm_plan(n: usize, f64: i32, g: f64, predicted: *mut f64) -> *const c_char;
    fn fmm_plan_mkn(m: usize, k: usize, n: usize, f64: i32, g: f64, predicted: *mut f64) -> *const c_char;
    fn fmm_release();
}

/// both libraries' entry points in one precision (the square ones for a square shape)
trait Both: Real {
    fn bits(x: Self) -> u64;
    fn rust(s: Shape, a: &[Self], lda: usize, b: &[Self], ldb: usize, c: &mut [Self], ldc: usize, g: f64) -> Result<(), fmm::Error>;
    fn c(s: Shape, a: &[Self], lda: usize, b: &[Self], ldb: usize, c: &mut [Self], ldc: usize, g: f64) -> i32;
}

impl Both for f32 {
    fn bits(x: f32) -> u64 {
        x.to_bits() as u64
    }
    fn rust(s: Shape, a: &[f32], lda: usize, b: &[f32], ldb: usize, c: &mut [f32], ldc: usize, g: f64) -> Result<(), fmm::Error> {
        if s.is_sq() { fmm::sgemm(s.m, a, lda, b, ldb, c, ldc, g) } else { fmm::sgemm_mkn(s.m, s.k, s.n, a, lda, b, ldb, c, ldc, g) }
    }
    fn c(s: Shape, a: &[f32], lda: usize, b: &[f32], ldb: usize, c: &mut [f32], ldc: usize, g: f64) -> i32 {
        check(s, a.len(), lda, b.len(), ldb, c.len(), ldc);
        // SAFETY: the slices hold the matrices with these leading dimensions (checked)
        unsafe {
            if s.is_sq() {
                fmm_sgemm(s.m, a.as_ptr(), lda, b.as_ptr(), ldb, c.as_mut_ptr(), ldc, g)
            } else {
                fmm_sgemm_mkn(s.m, s.k, s.n, a.as_ptr(), lda, b.as_ptr(), ldb, c.as_mut_ptr(), ldc, g)
            }
        }
    }
}

impl Both for f64 {
    fn bits(x: f64) -> u64 {
        x.to_bits()
    }
    fn rust(s: Shape, a: &[f64], lda: usize, b: &[f64], ldb: usize, c: &mut [f64], ldc: usize, g: f64) -> Result<(), fmm::Error> {
        if s.is_sq() { fmm::dgemm(s.m, a, lda, b, ldb, c, ldc, g) } else { fmm::dgemm_mkn(s.m, s.k, s.n, a, lda, b, ldb, c, ldc, g) }
    }
    fn c(s: Shape, a: &[f64], lda: usize, b: &[f64], ldb: usize, c: &mut [f64], ldc: usize, g: f64) -> i32 {
        check(s, a.len(), lda, b.len(), ldb, c.len(), ldc);
        // SAFETY: as for f32
        unsafe {
            if s.is_sq() {
                fmm_dgemm(s.m, a.as_ptr(), lda, b.as_ptr(), ldb, c.as_mut_ptr(), ldc, g)
            } else {
                fmm_dgemm_mkn(s.m, s.k, s.n, a.as_ptr(), lda, b.as_ptr(), ldb, c.as_mut_ptr(), ldc, g)
            }
        }
    }
}

fn check(s: Shape, la: usize, lda: usize, lb: usize, ldb: usize, lc: usize, ldc: usize) {
    assert!(lda >= s.k && ldb >= s.n && ldc >= s.n);
    assert!(la >= fmm::sys::extent(s.m, s.k, lda) && lb >= fmm::sys::extent(s.k, s.n, ldb) && lc >= fmm::sys::extent(s.m, s.n, ldc));
}

fn urand(s: &mut u64) -> f64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    (*s >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0
}

/// one case; true if the plans and the results are the same
fn case<T: Both>(s: Shape, ld: usize, g: f64, rng: &mut u64) -> bool {
    let (lda, ldb, ldc) = if s.is_sq() { (ld, ld, ld) } else { (s.k + 8, s.n + 8, s.n + 8) };
    let (na, nb, nc) = (s.m * lda, s.k * ldb, s.m * ldc);
    let (mut a, mut b) = (Vec::with_capacity(na), Vec::with_capacity(nb));
    if s.is_sq() {
        for _ in 0..na {
            a.push(T::from_f64(urand(rng)));
            b.push(T::from_f64(urand(rng)));
        }
    } else {
        a.extend((0..na).map(|_| T::from_f64(urand(rng))));
        b.extend((0..nb).map(|_| T::from_f64(urand(rng))));
    }
    let (mut cr, mut cc) = (vec![T::default(); nc], vec![T::default(); nc]);
    let pr = fmm::plan_mkn(s.m, s.k, s.n, T::F64, g);
    let (pred_r, pr) = (pr.predicted, if pr.spad != s { format!("{} padded to {}", pr.plan, pr.spad) } else { pr.plan.to_string() });
    let mut pred_c = 0.0;
    // SAFETY: fmm_plan returns its static buffer (valid until the next call), copied at once
    let pc = unsafe {
        let p = if s.is_sq() { fmm_plan(s.m, T::F64 as i32, g, &mut pred_c) } else { fmm_plan_mkn(s.m, s.k, s.n, T::F64 as i32, g, &mut pred_c) };
        CStr::from_ptr(p)
    }
    .to_string_lossy()
    .into_owned();
    T::rust(s, &a, lda, &b, ldb, &mut cr, ldc, g).expect("fmm");
    assert_eq!(T::c(s, &a, lda, &b, ldb, &mut cc, ldc, g), 0);
    // and both right: against Accelerate's GEMM, as test_fmm
    let mut r = vec![T::default(); nc];
    T::gemm(s, &a, lda, &b, ldb, 0.0, &mut r, ldc);
    let (mut differ, mut dmax, mut err, mut rmax) = (0usize, 0.0f64, 0.0f64, 0.0f64);
    for i in 0..s.m {
        for j in 0..s.n {
            let (x, y) = (cr[i * ldc + j], cc[i * ldc + j]);
            if T::bits(x) != T::bits(y) {
                differ += 1;
                dmax = dmax.max((x.to_f64() - y.to_f64()).abs());
            }
            err = err.max((x.to_f64() - r[i * ldc + j].to_f64()).abs());
            rmax = rmax.max(r[i * ldc + j].to_f64().abs());
        }
    }
    let right = err / rmax < if T::F64 { 1e-11 } else { 1e-3 };
    let same_pred = match pred_r {
        Some(t) => (t - pred_c).abs() <= 1e-9 * t.abs().max(1e-12),
        None => pred_c < 0.0,
    };
    println!("{} {:<14} ld={:<5} budget {:<4} plan rust {:<30} c {:<30} predicted {} / {}  results {}  rel. difference from Accelerate {}{}",
             if T::F64 { "f64" } else { "f32" }, s.to_string(), lda, g, pr, pc, pred_r.map_or("-".to_string(), |t| format!("{t:.6}")),
             if pred_c < 0.0 { "-".to_string() } else { format!("{pred_c:.6}") },
             if differ == 0 { "identical".to_string() } else { format!("{differ} entries differ, max {dmax:e}") },
             fmm::calib::fmt_e(err / rmax, 2), if right { "" } else { " WRONG" });
    pc == pr && differ == 0 && right && same_pred
}

fn main() {
    let mut sizes: Vec<usize> = std::env::args().skip(1).filter_map(|s| s.parse().ok()).collect();
    if sizes.is_empty() {
        sizes = vec![1000, 2048, 3000, 4096, 5000, 8192, 9000];
    }
    let (mut bad, mut rng) = (0, 0x9e3779b97f4a7c15u64);
    for f64 in [false, true] {
        let mut run = |s: Shape, ld, g| {
            let ok = if f64 { case::<f64>(s, ld, g, &mut rng) } else { case::<f32>(s, ld, g, &mut rng) };
            bad += !ok as usize;
        };
        for &n in &sizes {
            run(Shape::sq(n), n, 0.0);
        }
        run(Shape::sq(4096), 4096 + 64, 0.0);
        run(Shape::sq(8192), 8192, 4.0);
        for s in [Shape::new(3456, 3456, 1728), Shape::new(1000, 3000, 2000), Shape::new(2048, 4096, 1024), Shape::new(6912, 6912, 3456)] {
            run(s, 0, 0.0);
        }
    }
    fmm::release();
    // SAFETY: no C library call is in flight
    unsafe { fmm_release() };
    println!("{}", if bad == 0 { "all identical" } else { "DIFFERENCES" });
    std::process::exit((bad > 0) as i32);
}
