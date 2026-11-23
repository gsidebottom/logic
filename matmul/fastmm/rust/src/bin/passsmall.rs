//! Passes on small blocks: the library's driver against the C library's.
//!
//! The D48 left-factor pass (16 blocks of A in, 48 left factors out) on blocks of m x m for small
//! m, timed inside the library's pool as the calibration times it:
//!
//!   rust:   the library's pass, exec::run_par(exec::factor_chunks(..))
//!   build:  building the chunks only (no kernel)
//!   seq:    the same chunks run one after another on the calling thread
//!   c-gcd:  the C kernel with the C library's driver (GCD, 64 row chunks; no DC ZVA: compare
//!           with FMM_ZVA=0)
//!
//! Minimum and median over the repetitions, in microseconds; the outputs of the Rust and C
//! kernels are compared bit for bit.
//!
//!   cargo run --release --features cbench --bin passsmall [reps]     (make build/libfmm.a first)
#![allow(unsafe_code)]

use fmm::exec::{self, Side};
use fmm::plan::{Level, Shape};
use std::time::Instant;

unsafe extern "C" {
    fn c_pass_dps48_l_f32(m: usize, ld_in: usize, ld_out: usize, i: *const *const f32, o: *const *mut f32);
    fn c_pass_dps48_l_f64(m: usize, ld_in: usize, ld_out: usize, i: *const *const f64, o: *const *mut f64);
}

const PAD: usize = 1040;

trait Elem: fmm::Real {
    unsafe fn c_pass(m: usize, ld_in: usize, ld_out: usize, i: *const *const Self, o: *const *mut Self);
}
impl Elem for f32 {
    unsafe fn c_pass(m: usize, li: usize, lo: usize, i: *const *const f32, o: *const *mut f32) {
        unsafe { c_pass_dps48_l_f32(m, li, lo, i, o) }
    }
}
impl Elem for f64 {
    unsafe fn c_pass(m: usize, li: usize, lo: usize, i: *const *const f64, o: *const *mut f64) {
        unsafe { c_pass_dps48_l_f64(m, li, lo, i, o) }
    }
}

struct Ptrs<T> {
    i: [*const T; 16],
    o: [*mut T; 48],
}
unsafe impl<T> Send for Ptrs<T> {}
unsafe impl<T> Sync for Ptrs<T> {}

fn stats(v: &mut [f64]) -> (f64, f64) {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (v[0] * 1e6, v[v.len() / 2] * 1e6)
}

fn run<T: Elem>(m: usize, reps: usize) {
    let n = 4 * m;
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
    let mut out_r: Vec<T> = vec![T::from_f64(1.0); 48 * bs];
    let mut out_c: Vec<T> = vec![T::from_f64(1.0); 48 * bs];
    let p = Ptrs {
        i: std::array::from_fn(|b| unsafe { a.as_ptr().add((b / 4) * m * n + (b % 4) * m) }),
        o: std::array::from_fn(|k| unsafe { out_c.as_mut_ptr().add(k * bs) }),
    };
    let (mut tr, mut tb, mut ts, mut tg) = (vec![], vec![], vec![], vec![]);
    fmm::in_pool(|| {
        let p = &p;
        for rep in 0..reps + 3 {
            let t = Instant::now();
            exec::run_par(exec::factor_chunks::<T>(Level::D48, Side::L, &a, n, Shape::sq(m), &mut out_r, bs, 64));
            let dr = t.elapsed().as_secs_f64();
            let t = Instant::now();
            let ch = exec::factor_chunks::<T>(Level::D48, Side::L, &a, n, Shape::sq(m), &mut out_r, bs, 64);
            let db = t.elapsed().as_secs_f64();
            let t = Instant::now();
            for c in ch {
                c.run();
            }
            let ds = t.elapsed().as_secs_f64();
            let t = Instant::now();
            unsafe { T::c_pass(m, n, m, p.i.as_ptr(), p.o.as_ptr()) };
            let dg = t.elapsed().as_secs_f64();
            if rep >= 3 {
                tr.push(dr);
                tb.push(db);
                ts.push(ds);
                tg.push(dg);
            }
        }
    });
    let same = (0..48).all(|k| out_r[k * bs..k * bs + m * m] == out_c[k * bs..k * bs + m * m]);
    let ((r0, r1), (b0, b1), (s0, s1), (g0, g1)) = (stats(&mut tr), stats(&mut tb), stats(&mut ts), stats(&mut tg));
    println!(
        "{} m={:<5} rust {:8.1} / {:8.1}  build {:6.1} / {:6.1}  seq {:8.1} / {:8.1}  c-gcd {:8.1} / {:8.1}  rust/c-gcd {:5.2} / {:5.2}  {}",
        (if T::F64 { "f64" } else { "f32" }), m, r0, r1, b0, b1, s0, s1, g0, g1, r0 / g0, r1 / g1, if same { "identical" } else { "DIFFER" }
    );
}

fn main() {
    let reps: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(200);
    println!("# D48 left-factor pass on m x m blocks, microseconds as min / median over {reps} repetitions; FMM_ZVA={}",
             std::env::var("FMM_ZVA").unwrap_or_else(|_| "default".into()));
    for &m in &[96usize, 144, 192, 288, 384, 576, 768, 1024, 2048] {
        run::<f32>(m, if m > 1000 { reps / 10 } else { reps });
        run::<f64>(m, if m > 1000 { reps / 10 } else { reps });
    }
}
