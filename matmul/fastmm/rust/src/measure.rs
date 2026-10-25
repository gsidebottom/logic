//! The calibration's measurements, as the C library's: one GEMM and one blocked call alone at
//! each size, a fused level's passes and its GEMM time per product (each stream count), the steady
//! time and fill and drain of pipelines (from 2 and 10 synthetic sub-problems), and the error
//! model's three measurements; caches evicted before each timed run.
//!
//! Each runs where the library runs it: the leaves alone (a classical plan) on the calling
//! thread, after an eviction by scoped threads; the levels, pipelines and the error model's plans
//! on the library's pool, after an eviction on the pool.  A lone GEMM right after work on the
//! pool runs 15-25% slower once GEMM streams have run there (examples/gemm_after_level.rs), so
//! timing the leaves on the pool, as at first, overstated them and the planner passed over the
//! classical GEMM at 2048 f32.

use crate::calib::{self, Calib, Kind, N_E, STREAMS};
use crate::exec::{self, Blocks, BlocksMut, Real, Side};
use crate::plan::{pad, Entry, Level, Plan};
use rayon::prelude::*;
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

/// a buffer with its pages mapped, as the C library's memset: a zeroed Vec gets its pages from
/// the system on first write, which would land in the first timed run (the only one at the
/// largest sizes); written with a nonzero value, which no allocation can skip
pub fn mapped<T: Real>(len: usize) -> Vec<T> {
    let mut v = Vec::with_capacity(len);
    v.resize(len, T::from_f64(1.0));
    v
}

/// where an eviction runs: on the pool (inside it), or on threads started for it
#[derive(Clone, Copy)]
enum Evict {
    Pool,
    Scoped,
}

/// write 128 MB from every core: the next timed run starts with cold caches, as a sub-product
/// does inside a plan
fn evict(how: Evict) {
    static BUF: OnceLock<Mutex<Vec<u8>>> = OnceLock::new();
    let buf = BUF.get_or_init(|| Mutex::new(vec![0u8; 128 << 20]));
    let mut b = buf.lock().unwrap();
    let v = b[0].wrapping_add(1);
    match how {
        Evict::Pool => b.par_chunks_mut(2 << 20).for_each(|c| c.fill(v)),
        Evict::Scoped => {
            let threads = std::thread::available_parallelism().map_or(8, |n| n.get());
            let len = b.len().div_ceil(threads);
            std::thread::scope(|s| {
                for part in b.chunks_mut(len) {
                    s.spawn(move || part.fill(v));
                }
            });
        }
    }
}

/// repeated until 3 runs and 0.3 s, or 2 s, or 15 runs; the median (the lower middle for an even
/// count) of each of the values a run returns
fn repeat<const K: usize>(how: Evict, mut run: impl FnMut() -> [f64; K]) -> [f64; K] {
    let (mut cols, mut tot, mut cnt): ([Vec<f64>; K], f64, usize) = (std::array::from_fn(|_| vec![]), 0.0, 0);
    while cnt < 15 && tot < 2.0 && !(cnt >= 3 && tot >= 0.3) {
        evict(how);
        let t = Instant::now();
        let v = run();
        tot += t.elapsed().as_secs_f64();
        for (c, x) in cols.iter_mut().zip(v) {
            c.push(x);
        }
        cnt += 1;
    }
    cols.map(|mut c| {
        c.sort_by(|a, b| a.partial_cmp(b).unwrap());
        c[(c.len() - 1) / 2]
    })
}

/// a leaf alone, on the calling thread (as the library runs a classical plan)
fn time_plan<T: Real>(plan: &Plan, n: usize, a: &[T], b: &[T], c: &mut [T], work: &mut [T]) -> f64 {
    repeat(Evict::Scoped, || {
        let t = Instant::now();
        exec::exec(&plan.0, n, a, n, b, n, c, n, work);
        [t.elapsed().as_secs_f64()]
    })[0]
}

/// one fused level of type lv with blocks m and GEMM products (as `streams` streams): the medians
/// of its pass time and of its GEMM time per product
fn time_level<T: Real>(lv: Level, m: usize, streams: usize, a: &[T], b: &[T], c: &mut [T], work: &mut [T]) -> (f64, f64) {
    let (g, r) = (lv.grid(), lv.rank());
    let n = g * m;
    let bs = m * m + pad();
    let [p, q] = repeat(Evict::Pool, || {
        let (s_all, rest) = work.split_at_mut(r * bs);
        let (t_all, rest) = rest.split_at_mut(r * bs);
        let m_all = &mut rest[..r * bs];
        let t0 = Instant::now();
        exec::run_par(exec::factor_chunks(lv, Side::L, a, n, m, &mut *s_all, bs, 64));
        exec::run_par(exec::factor_chunks(lv, Side::R, b, n, m, &mut *t_all, bs, 64));
        let t1 = Instant::now();
        if streams > 0 {
            exec::gemm_streams(r, m, s_all, t_all, &mut *m_all, bs, streams);
        } else {
            for k in 0..r {
                T::gemm(m, &s_all[k * bs..k * bs + m * m], m, &t_all[k * bs..k * bs + m * m], m, 0.0,
                        &mut m_all[k * bs..k * bs + m * m], m);
            }
        }
        let t2 = Instant::now();
        exec::run_par(exec::product_chunks(lv, &*m_all, bs, m, &mut c[..], n, 64));
        let t3 = Instant::now();
        [(t1 - t0 + (t3 - t2)).as_secs_f64(), (t2 - t1).as_secs_f64() / r as f64]
    });
    (p, q)
}

/// every sub-problem reads the same matrix
struct Same<'a, T>(&'a [T]);
impl<T: Sync> Blocks<T> for Same<'_, T> {
    fn get(&self, _: usize) -> &[T] {
        self.0
    }
}
/// every sub-problem writes the same matrix (one at a time)
struct SameMut<'a, T>(&'a mut [T]);
impl<T> BlocksMut<T> for SameMut<'_, T> {
    fn get_mut(&mut self, _: usize) -> &mut [T] {
        self.0
    }
}

/// a pipeline of q sub-problems, each a level ly with blocks my over k streams with p pass
/// threads, on synthetic inputs: the slope of the times for 2 and 10 sub-problems is the steady
/// time per sub-problem, the rest the fill and drain
fn time_pipe<T: Real>(ly: Level, my: usize, k: u8, p: usize, a: &[T], b: &[T], c: &mut [T], work: &mut [T]) -> (f64, f64) {
    let mx = my * ly.grid();
    let py = [Entry::new(ly), Entry::gemm(k)];
    let (sx, tx) = (Same(&a[..mx * mx]), Same(&b[..mx * mx]));
    let [t2, t10] = repeat(Evict::Pool, || {
        let mut out = [0.0; 2];
        for (slot, q) in [(0, 2), (1, 10)] {
            let mut cx = SameMut(&mut c[..mx * mx]);
            let t = Instant::now();
            exec::pipeline(&py, mx, q, &sx, &tx, &mut cx, work, p);
            out[slot] = t.elapsed().as_secs_f64();
        }
        out
    });
    let slope = (t10 - t2) / 8.0;
    let steady = if slope > 0.0 { slope } else { t10 / 10.0 };
    (steady, (t2 - 2.0 * steady).max(0.0))
}

/// the error model's measurements: SW/G, D48/G and D48/D48/G at N_E on uniform random inputs
/// (the C library's generator), each against the classical GEMM
fn calib_errors<T: Real>(c: &mut Calib) {
    let (n, nn) = (N_E, N_E * N_E);
    let mut s: u64 = 0x2545f4914f6cdd1d;
    let mut a = vec![T::default(); nn];
    let mut b = vec![T::default(); nn];
    for i in 0..nn {
        for x in [&mut a[i], &mut b[i]] {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            *x = T::from_f64((s >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0);
        }
    }
    let mut r = vec![T::default(); nn];
    T::gemm(n, &a, n, &b, n, 0.0, &mut r, n);
    let rmax = r.iter().fold(0.0f64, |m, x| m.max(x.to_f64().abs()));
    let plans = ["SW/G", "D48/G", "D48/D48/G"].map(|s| Plan::parse(s).unwrap());
    let mut work = vec![T::default(); plans.iter().map(|p| p.work(n)).max().unwrap()];
    let mut cm = vec![T::default(); nn];
    for (i, p) in plans.iter().enumerate() {
        exec::exec(&p.0, n, &a, n, &b, n, &mut cm, n, &mut work);
        let e = cm.iter().zip(&r).fold(0.0f64, |m, (x, y)| m.max((x.to_f64() - y.to_f64()).abs()));
        c.put(Kind::Err(i as u8), N_E, e / rmax);
        println!("#   {:<7} m={:<6} {} (error of {} against the classical GEMM)", Kind::Err(i as u8).name(), N_E,
                 calib::fmt_e(e / rmax, 3), p);
    }
}

/// measure the entries the planner needs for n that the calibration lacks, and save it; a, b, c
/// hold n*n elements, smaller problems use their first m*m as contiguous m x m matrices;
/// returns the number of entries measured
pub fn calibrate<T: Real>(cal: &mut Calib, n: usize, a: &[T], b: &[T], c: &mut [T]) -> usize {
    let need = calib::need(n);
    let missing = |cal: &Calib, (kind, m): (Kind, usize)| -> bool {
        match kind {
            Kind::Err(_) => cal.get(kind, m).is_none(),
            Kind::Pipe { over: true, .. } | Kind::Gin(..) => false,     // measured with their partners
            Kind::Pipe { level, streams, passes, over: false } => {
                cal.get(kind, m).is_none() || cal.get(Kind::Pipe { level, streams, passes, over: true }, m).is_none()
            }
            Kind::Passes(lv) => cal.get(kind, m).is_none() || STREAMS.iter().any(|&k| cal.get(Kind::Gin(lv, k), m).is_none()),
            Kind::Leaf(_) => cal.get(kind, m).is_none(),
        }
    };
    let todo: Vec<(Kind, usize)> = need.into_iter().filter(|&e| missing(cal, e)).collect();
    if todo.is_empty() {
        return 0;
    }
    let count = todo.len();
    println!("# calibrating {count} entries ({})", if T::F64 { "f64" } else { "f32" });
    let wmax = todo
        .iter()
        .map(|&(kind, m)| match kind {
            Kind::Passes(lv) => Plan(vec![Entry::new(lv), Entry::new(Level::G)]).work(lv.grid() * m),
            Kind::Pipe { level, .. } => 2 * Plan(vec![Entry::new(level), Entry::new(Level::G)]).work(level.grid() * m),
            _ => 0,
        })
        .max()
        .unwrap_or(0);
    let mut work = mapped::<T>(wmax + 16);
    let mut errors_done = false;
    for (kind, m) in todo {
        match kind {
            Kind::Err(_) => {
                if !errors_done {
                    crate::pool().install(|| calib_errors::<T>(cal));
                    errors_done = true;
                }
            }
            Kind::Leaf(lv) => {
                let t = time_plan(&Plan(vec![Entry::new(lv)]), m, a, b, c, &mut work);
                cal.put(kind, m, t);
                println!("#   {:<4} m={:<6} {:.6} s", kind.name(), m, t);
            }
            Kind::Passes(lv) => {
                print!("#   {:<4} m={:<6}", kind.name(), m);
                for (i, &k) in STREAMS.iter().enumerate() {
                    let (tp, tg) = crate::pool().install(|| time_level(lv, m, k as usize, a, b, c, &mut work));
                    if i == 0 {
                        cal.put(kind, m, tp);
                        print!(" {tp:.6} s ");
                    }
                    cal.put(Kind::Gin(lv, k), m, tg);
                    print!("  {} {tg:.6}", Kind::Gin(lv, k).name());
                }
                println!();
            }
            Kind::Pipe { level, streams, passes, .. } => {
                let (st, ov) = crate::pool().install(|| time_pipe(level, m, streams, passes as usize, a, b, c, &mut work));
                cal.put(kind, m, st);
                cal.put(Kind::Pipe { level, streams, passes, over: true }, m, ov);
                println!("#   {:<10} m={:<6} {st:.6} s   fill+drain {ov:.6} s", kind.name(), m);
            }
            Kind::Gin(..) => {}
        }
    }
    if let Err(e) = calib::save(cal, T::F64) {
        eprintln!("fmm: saving the calibration to {}: {e}", calib::path(T::F64).display());
    }
    count
}
