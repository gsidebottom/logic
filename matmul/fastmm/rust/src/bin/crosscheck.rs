//! The Rust library against the C library (matmul/fastmm/build/libfmm.a, linked in) on the same
//! inputs and calibration cache: the plan each picks and their results, bit for bit.  The cases
//! of test_fmm.c (sizes, a leading dimension larger than n, an error budget).
//!
//!   make build/libfmm.a    (in matmul/fastmm)
//!   FMM_CALIB_DIR=../results cargo run --release --features cbench --bin crosscheck [n ...]
#![allow(unsafe_code)]

use fmm::Real;
use std::ffi::{c_char, CStr};

unsafe extern "C" {
    fn fmm_sgemm(n: usize, a: *const f32, lda: usize, b: *const f32, ldb: usize, c: *mut f32, ldc: usize, g: f64) -> i32;
    fn fmm_dgemm(n: usize, a: *const f64, lda: usize, b: *const f64, ldb: usize, c: *mut f64, ldc: usize, g: f64) -> i32;
    fn fmm_plan(n: usize, f64: i32, g: f64, predicted: *mut f64) -> *const c_char;
    fn fmm_release();
}

/// both libraries' entry points in one precision
trait Both: Real {
    fn bits(x: Self) -> u64;
    fn rust(n: usize, a: &[Self], ld: usize, b: &[Self], c: &mut [Self], g: f64) -> Result<(), fmm::Error>;
    fn c(n: usize, a: &[Self], ld: usize, b: &[Self], c: &mut [Self], g: f64) -> i32;
}

impl Both for f32 {
    fn bits(x: f32) -> u64 {
        x.to_bits() as u64
    }
    fn rust(n: usize, a: &[f32], ld: usize, b: &[f32], c: &mut [f32], g: f64) -> Result<(), fmm::Error> {
        fmm::sgemm(n, a, ld, b, ld, c, ld, g)
    }
    fn c(n: usize, a: &[f32], ld: usize, b: &[f32], c: &mut [f32], g: f64) -> i32 {
        assert!(a.len() >= fmm::sys::extent(n, ld) && b.len() >= fmm::sys::extent(n, ld) && c.len() >= fmm::sys::extent(n, ld));
        // SAFETY: the slices hold the n x n matrices with leading dimension ld (checked)
        unsafe { fmm_sgemm(n, a.as_ptr(), ld, b.as_ptr(), ld, c.as_mut_ptr(), ld, g) }
    }
}

impl Both for f64 {
    fn bits(x: f64) -> u64 {
        x.to_bits()
    }
    fn rust(n: usize, a: &[f64], ld: usize, b: &[f64], c: &mut [f64], g: f64) -> Result<(), fmm::Error> {
        fmm::dgemm(n, a, ld, b, ld, c, ld, g)
    }
    fn c(n: usize, a: &[f64], ld: usize, b: &[f64], c: &mut [f64], g: f64) -> i32 {
        assert!(a.len() >= fmm::sys::extent(n, ld) && b.len() >= fmm::sys::extent(n, ld) && c.len() >= fmm::sys::extent(n, ld));
        // SAFETY: as for f32
        unsafe { fmm_dgemm(n, a.as_ptr(), ld, b.as_ptr(), ld, c.as_mut_ptr(), ld, g) }
    }
}

fn urand(s: &mut u64) -> f64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    (*s >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0
}

/// one case; true if the plans and the results are the same
fn case<T: Both>(n: usize, ld: usize, g: f64, rng: &mut u64) -> bool {
    let cnt = n * ld;
    let (mut a, mut b) = (Vec::with_capacity(cnt), Vec::with_capacity(cnt));
    for _ in 0..cnt {
        a.push(T::from_f64(urand(rng)));
        b.push(T::from_f64(urand(rng)));
    }
    let (mut cr, mut cc) = (vec![T::default(); cnt], vec![T::default(); cnt]);
    let pr = fmm::plan(n, T::F64, g);
    let pr = if pr.npad != n { format!("{} padded to {}", pr.plan, pr.npad) } else { pr.plan.to_string() };
    let mut pred = 0.0;
    // SAFETY: fmm_plan returns its static buffer (valid until the next call), copied at once
    let pc = unsafe { CStr::from_ptr(fmm_plan(n, T::F64 as i32, g, &mut pred)) }.to_string_lossy().into_owned();
    T::rust(n, &a, ld, &b, &mut cr, g).expect("fmm");
    assert_eq!(T::c(n, &a, ld, &b, &mut cc, g), 0);
    // and both right: against Accelerate's GEMM, as test_fmm
    let mut r = vec![T::default(); cnt];
    T::gemm(n, &a, ld, &b, ld, 0.0, &mut r, ld);
    let (mut differ, mut dmax, mut err, mut rmax) = (0usize, 0.0f64, 0.0f64, 0.0f64);
    for i in 0..n {
        for j in 0..n {
            let (x, y) = (cr[i * ld + j], cc[i * ld + j]);
            if T::bits(x) != T::bits(y) {
                differ += 1;
                dmax = dmax.max((x.to_f64() - y.to_f64()).abs());
            }
            err = err.max((x.to_f64() - r[i * ld + j].to_f64()).abs());
            rmax = rmax.max(r[i * ld + j].to_f64().abs());
        }
    }
    let right = err / rmax < if T::F64 { 1e-11 } else { 1e-3 };
    println!("{} n={:<5} ld={:<5} budget {:<4} plan rust {:<30} c {:<30} results {}  rel. difference from Accelerate {}{}",
             if T::F64 { "f64" } else { "f32" }, n, ld, g, pr, pc,
             if differ == 0 { "identical".to_string() } else { format!("{differ} entries differ, max {dmax:e}") },
             fmm::calib::fmt_e(err / rmax, 2), if right { "" } else { " WRONG" });
    pc == pr && differ == 0 && right
}

fn main() {
    let mut sizes: Vec<usize> = std::env::args().skip(1).filter_map(|s| s.parse().ok()).collect();
    if sizes.is_empty() {
        sizes = vec![1000, 2048, 3000, 4096, 5000, 8192, 9000];
    }
    let (mut bad, mut rng) = (0, 0x9e3779b97f4a7c15u64);
    for f64 in [false, true] {
        let mut run = |n, ld, g| {
            let ok = if f64 { case::<f64>(n, ld, g, &mut rng) } else { case::<f32>(n, ld, g, &mut rng) };
            bad += !ok as usize;
        };
        for &n in &sizes {
            run(n, n, 0.0);
        }
        run(4096, 4096 + 64, 0.0);
        run(8192, 8192, 4.0);
    }
    fmm::release();
    // SAFETY: no C library call is in flight
    unsafe { fmm_release() };
    println!("{}", if bad == 0 { "all identical" } else { "DIFFERENCES" });
    std::process::exit((bad > 0) as i32);
}
