//! The boundary to the operating system and Apple's Accelerate: the crate's only unsafe code.
//! Safe wrappers check that the slices hold the matrices the C functions will touch.
#![allow(unsafe_code)]

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

/// the extent of an m x m row-major matrix with leading dimension ld, in elements
pub fn extent(m: usize, ld: usize) -> usize {
    if m == 0 { 0 } else { (m - 1) * ld + m }
}

fn check(m: usize, la: usize, lda: usize, lb: usize, ldb: usize, lc: usize, ldc: usize) {
    assert!(lda >= m && ldb >= m && ldc >= m, "leading dimensions below m");
    assert!(la >= extent(m, lda) && lb >= extent(m, ldb) && lc >= extent(m, ldc), "slices too short");
    assert!(m <= c_int::MAX as usize && lda.max(ldb).max(ldc) <= c_int::MAX as usize, "too large for BLAS");
}

/// C = A B + beta C for m x m row-major matrices
pub fn sgemm(m: usize, a: &[f32], lda: usize, b: &[f32], ldb: usize, beta: f32, c: &mut [f32], ldc: usize) {
    check(m, a.len(), lda, b.len(), ldb, c.len(), ldc);
    if m == 0 {
        return;     // BLAS rejects leading dimensions below 1
    }
    let (mi, la, lb, lc) = (m as c_int, lda as c_int, ldb as c_int, ldc as c_int);
    // SAFETY: the slices hold the matrices (checked above); c is exclusively borrowed
    unsafe { cblas_sgemm(ROW_MAJOR, NO_TRANS, NO_TRANS, mi, mi, mi, 1.0, a.as_ptr(), la, b.as_ptr(), lb, beta, c.as_mut_ptr(), lc) }
}

/// C = A B + beta C for m x m row-major matrices
pub fn dgemm(m: usize, a: &[f64], lda: usize, b: &[f64], ldb: usize, beta: f64, c: &mut [f64], ldc: usize) {
    check(m, a.len(), lda, b.len(), ldb, c.len(), ldc);
    if m == 0 {
        return;     // BLAS rejects leading dimensions below 1
    }
    let (mi, la, lb, lc) = (m as c_int, lda as c_int, ldb as c_int, ldc as c_int);
    // SAFETY: as in sgemm
    unsafe { cblas_dgemm(ROW_MAJOR, NO_TRANS, NO_TRANS, mi, mi, mi, 1.0, a.as_ptr(), la, b.as_ptr(), lb, beta, c.as_mut_ptr(), lc) }
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
