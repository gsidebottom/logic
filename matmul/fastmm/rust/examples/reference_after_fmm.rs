//! fmmbench's sequence: an fmm call (pool, streams), then Accelerate's GEMM as the reference.
//! The reference called four ways right after the fmm call, in rotating order, 5 rounds,
//! medians: on the main thread, on a pool thread, on a fresh thread, and on the main thread
//! after 13 scoped threads touched 128 MB.
//!
//!   FMM_CALIB_DIR=../results cargo run --release --example reference_after_fmm

use fmm::Real;
use std::time::Instant;

fn med(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

fn run<T: Real>(n: usize, fmm: fn(usize, &[T], &[T], &mut [T])) {
    let a: Vec<T> = (0..n * n).map(|i| T::from_f64(1.0 / (1 + i % 7) as f64)).collect();
    let b: Vec<T> = (0..n * n).map(|i| T::from_f64(1.0 / (1 + i % 5) as f64)).collect();
    let mut c = vec![T::from_f64(1.0); n * n];
    let mut r = vec![T::from_f64(1.0); n * n];
    let mut buf = vec![1u8; 128 << 20];
    let mut t: [Vec<f64>; 4] = Default::default();
    for round in 0..20 {
        let way = round % 4;
        fmm(n, &a, &b, &mut c);
        let dt = match way {
            0 => {
                let s = Instant::now();
                T::gemm(n, &a, n, &b, n, 0.0, &mut r, n);
                s.elapsed().as_secs_f64()
            }
            1 => fmm::in_pool(|| {
                let s = Instant::now();
                T::gemm(n, &a, n, &b, n, 0.0, &mut r, n);
                s.elapsed().as_secs_f64()
            }),
            2 => std::thread::scope(|sc| {
                sc.spawn(|| {
                    let s = Instant::now();
                    T::gemm(n, &a, n, &b, n, 0.0, &mut r, n);
                    s.elapsed().as_secs_f64()
                })
                .join()
                .unwrap()
            }),
            _ => {
                let len = buf.len().div_ceil(13);
                std::thread::scope(|sc| {
                    for part in buf.chunks_mut(len) {
                        sc.spawn(move || part.fill(round as u8));
                    }
                });
                let s = Instant::now();
                T::gemm(n, &a, n, &b, n, 0.0, &mut r, n);
                s.elapsed().as_secs_f64()
            }
        };
        if round >= 4 {
            t[way].push(dt);
        }
    }
    let [m0, m1, m2, m3] = t.map(med);
    println!("{} n={n:<5} reference after the fmm call: main {m0:.6}  pool {m1:.6}  fresh thread {m2:.6}  main after scoped work {m3:.6}",
             if T::F64 { "f64" } else { "f32" });
}

fn main() {
    for n in [2048, 4096] {
        run::<f32>(n, |n, a, b, c| fmm::sgemm(n, a, n, b, n, c, n, 0.0).unwrap());
        run::<f64>(n, |n, a, b, c| fmm::dgemm(n, a, n, b, n, c, n, 0.0).unwrap());
    }
}
