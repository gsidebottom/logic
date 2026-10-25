//! Feasibility benchmark: the D48 left-factor pass (16 blocks in, 48 out, the scheme's program per
//! element) in safe Rust against the C library's kernel, at n = 8192 and 16384, f32 and f64.
//!
//!   rust:  the safe Rust kernel with the library's driver (row chunks on its thread pool)
//!   c:     the C kernel on the same threads (through FFI; harness only)
//!   c-gcd: the C kernel with the C library's own driver (GCD, 64 row chunks)
//!
//! Interleaved rounds, medians; the outputs of the Rust and C kernels are compared bit for bit.
//! Also one Accelerate GEMM through the crate's safe wrapper.
//!
//!   cargo run --release --features cbench --bin passbench [threads]    (make build/libfmm.a first)
#![allow(unsafe_code)]

use fmm::exec::{self, Side};
use fmm::plan::Level;
use fmm::kernels;
use std::time::Instant;

unsafe extern "C" {
    fn c_dps48_l_f32(m: usize, ld_in: usize, ld_out: usize, i: *const *const f32, o: *const *mut f32, r0: usize, r1: usize);
    fn c_dps48_l_f64(m: usize, ld_in: usize, ld_out: usize, i: *const *const f64, o: *const *mut f64, r0: usize, r1: usize);
    fn c_pass_dps48_l_f32(m: usize, ld_in: usize, ld_out: usize, i: *const *const f32, o: *const *mut f32);
    fn c_pass_dps48_l_f64(m: usize, ld_in: usize, ld_out: usize, i: *const *const f64, o: *const *mut f64);
}

const PAD: usize = 1040;

trait Elem: fmm::Real {
    unsafe fn c_kernel(m: usize, ld_in: usize, ld_out: usize, i: *const *const Self, o: *const *mut Self, r0: usize, r1: usize);
    unsafe fn c_pass(m: usize, ld_in: usize, ld_out: usize, i: *const *const Self, o: *const *mut Self);
}

impl Elem for f32 {
    unsafe fn c_kernel(m: usize, li: usize, lo: usize, i: *const *const f32, o: *const *mut f32, r0: usize, r1: usize) {
        unsafe { c_dps48_l_f32(m, li, lo, i, o, r0, r1) }
    }
    unsafe fn c_pass(m: usize, li: usize, lo: usize, i: *const *const f32, o: *const *mut f32) {
        unsafe { c_pass_dps48_l_f32(m, li, lo, i, o) }
    }
}

impl Elem for f64 {
    unsafe fn c_kernel(m: usize, li: usize, lo: usize, i: *const *const f64, o: *const *mut f64, r0: usize, r1: usize) {
        unsafe { c_dps48_l_f64(m, li, lo, i, o, r0, r1) }
    }
    unsafe fn c_pass(m: usize, li: usize, lo: usize, i: *const *const f64, o: *const *mut f64) {
        unsafe { c_pass_dps48_l_f64(m, li, lo, i, o) }
    }
}

/// raw block pointers for the C kernels (harness only)
struct Ptrs<T> {
    i: [*const T; 16],
    o: [*mut T; 48],
}
unsafe impl<T> Send for Ptrs<T> {}
unsafe impl<T> Sync for Ptrs<T> {}

fn ptrs<T>(n: usize, a: &[T], out: &mut [T], bs: usize) -> Ptrs<T> {
    let m = n / 4;
    let i = std::array::from_fn(|b| unsafe { a.as_ptr().add((b / 4) * m * n + (b % 4) * m) });
    let o = std::array::from_fn(|k| unsafe { out.as_mut_ptr().add(k * bs) });
    Ptrs { i, o }
}

fn median(v: &mut [f64]) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

fn run<T: Elem>(n: usize, threads: usize, reps: usize) {
    let m = n / 4;
    let bs = m * m + PAD;
    let mut s: u64 = 0x9e3779b97f4a7c15;
    let a: Vec<T> = (0..n * n)
        .map(|_| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            T::from_f64((s >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0)
        })
        .collect();
    let mut out_r: Vec<T> = vec![T::default(); 48 * bs];
    let mut out_c: Vec<T> = vec![T::default(); 48 * bs];
    let (mut tr, mut tc, mut tg) = (vec![], vec![], vec![]);
    for rep in 0..=reps {
        // safe Rust kernel, the library's driver
        let t = Instant::now();
        fmm::in_pool(|| exec::run_par(exec::factor_chunks::<T>(Level::D48, Side::L, &a, n, m, &mut out_r, bs, 64)));
        let dr = t.elapsed().as_secs_f64();
        // C kernel, same threads
        let p = ptrs(n, &a, &mut out_c, bs);
        let rows = m.div_ceil(threads);
        let t = Instant::now();
        std::thread::scope(|sc| {
            for th in 0..threads {
                let p = &p;
                let (r0, r1) = (th * rows, ((th + 1) * rows).min(m));
                if r0 < r1 {
                    sc.spawn(move || unsafe { T::c_kernel(m, n, m, p.i.as_ptr(), p.o.as_ptr(), r0, r1) });
                }
            }
        });
        let dc = t.elapsed().as_secs_f64();
        // C kernel, the C library's GCD driver
        let t = Instant::now();
        unsafe { T::c_pass(m, n, m, p.i.as_ptr(), p.o.as_ptr()) };
        let dg = t.elapsed().as_secs_f64();
        if rep > 0 {
            tr.push(dr);
            tc.push(dc);
            tg.push(dg);
        }
    }
    let same = (0..48).all(|k| out_r[k * bs..k * bs + m * m] == out_c[k * bs..k * bs + m * m]);
    let (r, c, g) = (median(&mut tr), median(&mut tc), median(&mut tg));
    let gb = (16 + 48) as f64 * (m * m) as f64 * std::mem::size_of::<T>() as f64 / 1e9;
    println!(
        "{} n={:<5} threads {:<2}  rust {:7.4} s ({:5.1} GB/s)  c {:7.4} s ({:5.1} GB/s)  c-gcd {:7.4} s ({:5.1} GB/s)  rust/c-gcd {:.3}  outputs {}",
        (if T::F64 { "f64" } else { "f32" }), n, threads, r, gb / r, c, gb / c, g, gb / g, r / g, if same { "identical" } else { "DIFFER" }
    );
}

fn gemm_check<T: Elem>(m: usize) {
    let a: Vec<T> = (0..m * m).map(|i| T::from_f64(((i % 7) as f64) / 7.0)).collect();
    let b: Vec<T> = (0..m * m).map(|i| T::from_f64(((i % 5) as f64) / 5.0)).collect();
    let mut c: Vec<T> = vec![T::default(); m * m];
    <T as fmm::Real>::gemm(m, &a, m, &b, m, 0.0, &mut c, m);
    let mut ts = vec![];
    for _ in 0..7 {
        let t = Instant::now();
        <T as fmm::Real>::gemm(m, &a, m, &b, m, 0.0, &mut c, m);
        ts.push(t.elapsed().as_secs_f64());
    }
    let t = median(&mut ts);
    println!("{} gemm m={}  {:.5} s  {:.0} GFLOP/s (Accelerate through the safe wrapper)", (if T::F64 { "f64" } else { "f32" }), m, t, 2.0 * (m as f64).powi(3) / t / 1e9);
}

fn main() {
    let threads: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(10);
    println!("# D48 left-factor pass ({}, {} operations in the whole program): safe Rust vs C", kernels::DPS48_PROGRAM, kernels::DPS48_OPS);
    gemm_check::<f32>(2048);
    gemm_check::<f64>(2048);
    for &n in &[8192usize, 16384] {
        run::<f32>(n, threads, 7);
        run::<f64>(n, threads, 7);
    }
}
