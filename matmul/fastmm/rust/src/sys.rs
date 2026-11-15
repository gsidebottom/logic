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

/// The size in bytes of the block DC ZVA zeroes (64 on Apple silicon), or 0 if the passes should
/// not claim their output lines: FMM_ZVA=0, an architecture other than aarch64, or DC ZVA
/// prohibited (bit 4 of DCZID_EL0).  Read once.  See claim_lines and fmm.c's fmm_zva().
pub fn zva_block() -> usize {
    static ZB: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *ZB.get_or_init(|| {
        if std::env::var("FMM_ZVA").is_ok_and(|v| v.trim().parse::<i64>().is_ok_and(|x| x == 0)) {
            return 0;
        }
        dczid().map_or(0, |id| if id & 16 != 0 { 0 } else { 4usize << (id & 15) })
    })
}

#[cfg(target_arch = "aarch64")]
fn dczid() -> Option<u64> {
    let id: u64;
    // SAFETY: DCZID_EL0 is readable at EL0 on every aarch64 system; reading it has no effect
    unsafe { std::arch::asm!("mrs {0}, dczid_el0", out(reg) id, options(nomem, nostack, preserves_flags)) };
    Some(id)
}

#[cfg(not(target_arch = "aarch64"))]
fn dczid() -> Option<u64> {
    None
}

/// Claims the cache lines of `out` that the caller is about to overwrite completely: every
/// aligned block of `zb` bytes (zva_block()) lying wholly inside the slice is zeroed by DC ZVA,
/// which allocates the line in the cache without reading it from memory, so the stores that
/// follow do not fetch it first (a pass that writes 48 blocks and reads 16 otherwise moves 112
/// blocks through the memory system instead of 64).  Only bytes inside `out` change, and to
/// zero, so the call is safe whatever the caller does next; zb = 0 does nothing.
pub fn claim_lines<T: Copy>(out: &mut [T], zb: usize) {
    if zb == 0 {
        return;
    }
    debug_assert!(zb.is_power_of_two());
    let start = out.as_mut_ptr() as usize;
    let end = start + std::mem::size_of_val(out);
    let mut x = (start + zb - 1) & !(zb - 1);    // round in at both ends, never out
    while x + zb <= end {
        zero_block(x);
        x += zb;
    }
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn zero_block(x: usize) {
    // SAFETY: claim_lines passes only addresses of zb-aligned blocks wholly inside a slice it holds
    // exclusively; DC ZVA writes zeros to exactly that block (no `nomem`: it writes memory)
    unsafe { std::arch::asm!("dc zva, {0}", in(reg) x, options(nostack, preserves_flags)) };
}

#[cfg(not(target_arch = "aarch64"))]
#[inline(always)]
fn zero_block(_x: usize) {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn claim_lines_zeroes_only_whole_lines_inside_the_slice() {
        let zb = zva_block();
        for (lo, hi) in [(0usize, 1000usize), (3, 997), (17, 18), (5, 5), (1, 40)] {
            let mut v = vec![1.0f32; 1024];
            claim_lines(&mut v[lo..hi], zb);
            let (base, sz) = (v.as_ptr() as usize, std::mem::size_of::<f32>());
            for (j, x) in v.iter().enumerate() {
                let a = base + j * sz;
                let line = a & !(zb.max(1) - 1);
                let inside = zb > 0 && j >= lo && j < hi && line >= base + lo * sz && line + zb <= base + hi * sz;
                assert_eq!(*x == 0.0, inside, "element {j} of slice {lo}..{hi}, zb {zb}");
            }
        }
        #[cfg(target_arch = "aarch64")]
        if std::env::var("FMM_ZVA").is_err() {
            assert!(zb >= 16, "DC ZVA available on this aarch64 machine");
        }
    }
}
