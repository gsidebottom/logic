//! The boundary to the operating system and Apple's Accelerate: the crate's only unsafe code.
//! Safe wrappers check that the slices hold the matrices the C functions will touch.
#![allow(unsafe_code)]

use crate::plan::Shape;
use std::os::raw::c_int;

const ROW_MAJOR: c_int = 101;
const NO_TRANS: c_int = 111;
const QOS_CLASS_USER_INTERACTIVE: u32 = 0x21;

// Accelerate's current BLAS (the symbols C code gets with ACCELERATE_NEW_LAPACK)
unsafe extern "C" {
    #[link_name = "cblas_sgemm$NEWLAPACK"]
    fn cblas_sgemm(order: c_int, ta: c_int, tb: c_int, m: c_int, n: c_int, k: c_int, alpha: f32, a: *const f32,
                   lda: c_int, b: *const f32, ldb: c_int, beta: f32, c: *mut f32, ldc: c_int);
    #[link_name = "cblas_dgemm$NEWLAPACK"]
    fn cblas_dgemm(order: c_int, ta: c_int, tb: c_int, m: c_int, n: c_int, k: c_int, alpha: f64, a: *const f64,
                   lda: c_int, b: *const f64, ldb: c_int, beta: f64, c: *mut f64, ldc: c_int);
    fn BLASSetThreading(threading: u32) -> c_int;
    fn pthread_set_qos_class_self_np(qos: u32, relative_priority: c_int) -> c_int;
}

/// the extent of a rows x cols row-major matrix with leading dimension ld, in elements
pub fn extent(rows: usize, cols: usize, ld: usize) -> usize {
    if rows == 0 || cols == 0 { 0 } else { (rows - 1) * ld + cols }
}

fn check(s: Shape, la: usize, lda: usize, lb: usize, ldb: usize, lc: usize, ldc: usize) {
    assert!(lda >= s.k && ldb >= s.n && ldc >= s.n, "leading dimensions below the matrices' columns");
    assert!(la >= extent(s.m, s.k, lda) && lb >= extent(s.k, s.n, ldb) && lc >= extent(s.m, s.n, ldc), "slices too short");
    assert!(s.m.max(s.k).max(s.n) <= c_int::MAX as usize && lda.max(ldb).max(ldc) <= c_int::MAX as usize, "too large for BLAS");
}

/// C = A B + beta C for an m x k matrix A and a k x n matrix B, row-major
pub fn sgemm(s: Shape, a: &[f32], lda: usize, b: &[f32], ldb: usize, beta: f32, c: &mut [f32], ldc: usize) {
    check(s, a.len(), lda, b.len(), ldb, c.len(), ldc);
    if s.m == 0 || s.n == 0 || s.k == 0 {
        return;     // BLAS rejects leading dimensions below 1; an empty sum leaves C (beta = 0 here means zero)
    }
    let (m, n, k, la, lb, lc) = (s.m as c_int, s.n as c_int, s.k as c_int, lda as c_int, ldb as c_int, ldc as c_int);
    // SAFETY: the slices hold the matrices (checked above); c is exclusively borrowed
    unsafe { cblas_sgemm(ROW_MAJOR, NO_TRANS, NO_TRANS, m, n, k, 1.0, a.as_ptr(), la, b.as_ptr(), lb, beta, c.as_mut_ptr(), lc) }
}

/// C = A B + beta C for an m x k matrix A and a k x n matrix B, row-major
pub fn dgemm(s: Shape, a: &[f64], lda: usize, b: &[f64], ldb: usize, beta: f64, c: &mut [f64], ldc: usize) {
    check(s, a.len(), lda, b.len(), ldb, c.len(), ldc);
    if s.m == 0 || s.n == 0 || s.k == 0 {
        return;
    }
    let (m, n, k, la, lb, lc) = (s.m as c_int, s.n as c_int, s.k as c_int, lda as c_int, ldb as c_int, ldc as c_int);
    // SAFETY: as in sgemm
    unsafe { cblas_dgemm(ROW_MAJOR, NO_TRANS, NO_TRANS, m, n, k, 1.0, a.as_ptr(), la, b.as_ptr(), lb, beta, c.as_mut_ptr(), lc) }
}

/// Accelerate's BLAS on the calling thread single-threaded (GEMM streams) or with its own threading
pub fn set_single_threaded(single: bool) {
    // SAFETY: a thread-local setting, no memory involved
    unsafe { BLASSetThreading(if single { 1 } else { 0 }) };
}

/// the calling thread at user-interactive priority, as GCD runs the C library's work
pub fn set_qos_user_interactive() {
    // SAFETY: changes the calling thread's scheduling class only
    unsafe { pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0) };
}
