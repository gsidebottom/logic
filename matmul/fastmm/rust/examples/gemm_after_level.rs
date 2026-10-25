//! Does running fused levels on the pool change the time of a later lone GEMM?  G m (evict +
//! one GEMM, 15 runs, median) four ways in a fresh process, after each plan run 3 times on the
//! pool, and after 2 s idle.
//!
//!   cargo run --release --example gemm_after_level

use fmm::{exec, Plan, Real};
use rayon::prelude::*;
use std::time::Instant;

fn med(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

fn evict_scoped(buf: &mut [u8], v: u8) {
    let len = buf.len().div_ceil(13);
    std::thread::scope(|s| {
        for part in buf.chunks_mut(len) {
            s.spawn(move || part.fill(v));
        }
    });
}

/// G m four ways: pool thread after a pool eviction (V1), main thread after scoped threads (V2),
/// main thread after a pool eviction (V3), pool thread after scoped threads (V4)
fn variants<T: Real>(m: usize, a: &[T], b: &[T], c: &mut [T], buf: &mut [u8]) -> [f64; 4] {
    let gt = |c: &mut [T]| {
        let t = Instant::now();
        T::gemm(m, a, m, b, m, 0.0, c, m);
        t.elapsed().as_secs_f64()
    };
    let v1 = fmm::in_pool(|| med((0..15u8).map(|r| { buf.par_chunks_mut(2 << 20).for_each(|ch| ch.fill(r)); gt(&mut *c) }).collect()));
    let v2 = med((0..15u8).map(|r| { evict_scoped(buf, r); gt(&mut *c) }).collect());
    let v3 = med((0..15u8).map(|r| { fmm::in_pool(|| buf.par_chunks_mut(2 << 20).for_each(|ch| ch.fill(r))); gt(&mut *c) }).collect());
    let v4 = fmm::in_pool(|| med((0..15u8).map(|r| { evict_scoped(buf, r); gt(&mut *c) }).collect()));
    [v1, v2, v3, v4]
}

fn main() {
    let mut buf = vec![1u8; 128 << 20];
    let m = 2048;
    let n = 4096;
    let a: Vec<f32> = (0..n * n).map(|i| 1.0 / (1 + i % 7) as f32).collect();
    let b: Vec<f32> = (0..n * n).map(|i| 1.0 / (1 + i % 5) as f32).collect();
    let mut c: Vec<f32> = vec![1.0; n * n];
    let show = |what: &str, v: [f64; 4]| {
        println!("f32 G {m} {what:<28} V1 pool/pool {:.6}  V2 main/scoped {:.6}  V3 main/pool {:.6}  V4 pool/scoped {:.6}", v[0], v[1], v[2], v[3])
    };
    show("fresh process", variants(m, &a, &b, &mut c, &mut buf));
    for plan in ["D48/G", "D48/G6", "SW+3/D48/G6"] {
        let p = Plan::parse(plan).unwrap();
        let mut work: Vec<f32> = vec![1.0; p.work(n)];
        fmm::in_pool(|| {
            for _ in 0..3 {
                exec::exec(&p.0, n, &a, n, &b, n, &mut c, n, &mut work);
            }
        });
        show(&format!("after {plan} x3"), variants(m, &a, &b, &mut c, &mut buf));
    }
    std::thread::sleep(std::time::Duration::from_secs(2));
    show("after 2 s idle", variants(m, &a, &b, &mut c, &mut buf));
}
