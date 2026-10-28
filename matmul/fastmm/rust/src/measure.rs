//! The calibration's measurements, as the C library's: one GEMM and one blocked call alone at
//! each shape, a fused level's passes and its GEMM time per product (each stream count), the
//! steady time and fill and drain of pipelines (from 2 and 10 synthetic sub-problems), and the
//! error model's measurements; caches evicted before each timed run.
//!
//! Each runs where the library runs it: the leaves alone (a classical plan) on the calling
//! thread, after an eviction by scoped threads; the levels, pipelines and the error model's plans
//! on the library's pool, after an eviction on the pool.  A lone GEMM right after work on the
//! pool runs 15-25% slower once GEMM streams have run there (examples/gemm_after_level.rs), so
//! timing the leaves on the pool, as at first, overstated them and the planner passed over the
//! classical GEMM at 2048 f32.

use crate::calib::{self, Calib, Kind, ERR_PLANS, N_E, STREAMS};
use crate::exec::{self, Blocks, BlocksMut, Real, Side};
use crate::plan::{Entry, Level, Plan, Shape};
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

/// a leaf alone on a problem of shape s (A, B, C contiguous), on the calling thread (as the
/// library runs a classical plan)
fn time_plan<T: Real>(plan: &Plan, s: Shape, a: &[T], b: &[T], c: &mut [T], work: &mut [T]) -> f64 {
    repeat(Evict::Scoped, || {
        let t = Instant::now();
        exec::exec(&plan.0, s, a, s.k, b, s.n, c, s.n, work);
        [t.elapsed().as_secs_f64()]
    })[0]
}

/// one fused level of type lv whose products have shape t, with GEMM products (as `streams`
/// streams): the medians of its pass time and of its GEMM time per product
fn time_level<T: Real>(lv: Level, t: Shape, streams: usize, a: &[T], b: &[T], c: &mut [T], work: &mut [T]) -> (f64, f64) {
    let r = lv.rank();
    let s = lv.up(t);
    let (bss, bst, bsm) = exec::block_strides(t);
    let [p, q] = repeat(Evict::Pool, || {
        let (s_all, rest) = work.split_at_mut(r * bss);
        let (t_all, rest) = rest.split_at_mut(r * bst);
        let m_all = &mut rest[..r * bsm];
        let t0 = Instant::now();
        exec::run_par(exec::factor_chunks(lv, Side::L, a, s.k, t, &mut *s_all, bss, 64));
        exec::run_par(exec::factor_chunks(lv, Side::R, b, s.n, t, &mut *t_all, bst, 64));
        let t1 = Instant::now();
        if streams > 0 {
            exec::gemm_streams(r, t, s_all, t_all, &mut *m_all, bss, bst, bsm, streams);
        } else {
            for k in 0..r {
                T::gemm(t, &s_all[k * bss..k * bss + t.m * t.k], t.k, &t_all[k * bst..k * bst + t.k * t.n], t.n, 0.0,
                        &mut m_all[k * bsm..k * bsm + t.m * t.n], t.n);
            }
        }
        let t2 = Instant::now();
        exec::run_par(exec::product_chunks(lv, &*m_all, bsm, t, &mut c[..], s.n, 64));
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

/// a pipeline of q sub-problems, each a level ly whose products have shape ty over k streams with
/// p pass threads, on synthetic inputs: the slope of the times for 2 and 10 sub-problems is the
/// steady time per sub-problem, the rest the fill and drain
fn time_pipe<T: Real>(ly: Level, ty: Shape, k: u8, p: usize, a: &[T], b: &[T], c: &mut [T], work: &mut [T]) -> (f64, f64) {
    let t = ly.up(ty);
    let py = [Entry::new(ly), Entry::gemm(k)];
    let (sx, tx) = (Same(&a[..t.m * t.k]), Same(&b[..t.k * t.n]));
    let [t2, t10] = repeat(Evict::Pool, || {
        let mut out = [0.0; 2];
        for (slot, q) in [(0, 2), (1, 10)] {
            let mut cx = SameMut(&mut c[..t.m * t.n]);
            let tm = Instant::now();
            exec::pipeline(&py, t, q, &sx, &tx, &mut cx, work, p);
            out[slot] = tm.elapsed().as_secs_f64();
        }
        out
    });
    let slope = (t10 - t2) / 8.0;
    let steady = if slope > 0.0 { slope } else { t10 / 10.0 };
    (steady, (t2 - 2.0 * steady).max(0.0))
}

/// the error model's measurements: the ERR_PLANS at N_E on uniform random inputs (the C library's
/// generator), each against the classical GEMM
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
    let sq = Shape::sq(n);
    let mut r = vec![T::default(); nn];
    T::gemm(sq, &a, n, &b, n, 0.0, &mut r, n);
    let rmax = r.iter().fold(0.0f64, |m, x| m.max(x.to_f64().abs()));
    let plans = ERR_PLANS.map(|s| Plan::parse(s).unwrap());
    let mut work = vec![T::default(); plans.iter().map(|p| p.work(sq)).max().unwrap()];
    let mut cm = vec![T::default(); nn];
    for (i, p) in plans.iter().enumerate() {
        exec::exec(&p.0, sq, &a, n, &b, n, &mut cm, n, &mut work);
        let e = cm.iter().zip(&r).fold(0.0f64, |m, (x, y)| m.max((x.to_f64() - y.to_f64()).abs()));
        c.put(Kind::Err(i as u8), sq, e / rmax);
        println!("#   {:<7} m={:<6} {} (error of {} against the classical GEMM)", Kind::Err(i as u8).name(), N_E,
                 calib::fmt_e(e / rmax, 3), p);
    }
}

/// measure the entries the planner needs for the shape s0 that the calibration lacks, and save it;
/// a, b, c hold s0.m*s0.k, s0.k*s0.n and s0.m*s0.n elements, smaller problems use their first
/// elements as contiguous matrices; returns the number of entries measured
pub fn calibrate<T: Real>(cal: &mut Calib, s0: Shape, a: &[T], b: &[T], c: &mut [T]) -> usize {
    let need = calib::need(s0);
    let missing = |cal: &Calib, (kind, s): (Kind, Shape)| -> bool {
        match kind {
            Kind::Err(_) => cal.get(kind, s).is_none(),
            Kind::Pipe { over: true, .. } | Kind::Gin(..) => false,     // measured with their partners
            Kind::Pipe { level, streams, passes, over: false } => {
                cal.get(kind, s).is_none() || cal.get(Kind::Pipe { level, streams, passes, over: true }, s).is_none()
            }
            Kind::Passes(lv) => cal.get(kind, s).is_none() || STREAMS.iter().any(|&k| cal.get(Kind::Gin(lv, k), s).is_none()),
            Kind::Leaf(_) => cal.get(kind, s).is_none(),
        }
    };
    let todo: Vec<(Kind, Shape)> = need.into_iter().filter(|&e| missing(cal, e)).collect();
    if todo.is_empty() {
        return 0;
    }
    let count = todo.len();
    println!("# calibrating {count} entries ({})", if T::F64 { "f64" } else { "f32" });
    let wmax = todo
        .iter()
        .map(|&(kind, s)| match kind {
            Kind::Passes(lv) => Plan(vec![Entry::new(lv), Entry::new(Level::G)]).work(lv.up(s)),
            Kind::Pipe { level, .. } => 2 * Plan(vec![Entry::new(level), Entry::new(Level::G)]).work(level.up(s)),
            _ => 0,
        })
        .max()
        .unwrap_or(0);
    let mut work = mapped::<T>(wmax + 16);
    let mut errors_done = false;
    for (kind, s) in todo {
        match kind {
            Kind::Err(_) => {
                if !errors_done {
                    crate::pool().install(|| calib_errors::<T>(cal));
                    errors_done = true;
                }
            }
            Kind::Leaf(lv) => {
                let t = time_plan(&Plan(vec![Entry::new(lv)]), s, a, b, c, &mut work);
                cal.put(kind, s, t);
                println!("#   {:<4} m={:<14} {:.6} s", kind.name(), s.to_string(), t);
            }
            Kind::Passes(lv) => {
                print!("#   {:<4} m={:<14}", kind.name(), s.to_string());
                for (i, &k) in STREAMS.iter().enumerate() {
                    let (tp, tg) = crate::pool().install(|| time_level(lv, s, k as usize, a, b, c, &mut work));
                    if i == 0 {
                        cal.put(kind, s, tp);
                        print!(" {tp:.6} s ");
                    }
                    cal.put(Kind::Gin(lv, k), s, tg);
                    print!("  {} {tg:.6}", Kind::Gin(lv, k).name());
                }
                println!();
            }
            Kind::Pipe { level, streams, passes, .. } => {
                let (st, ov) = crate::pool().install(|| time_pipe(level, s, streams, passes as usize, a, b, c, &mut work));
                cal.put(kind, s, st);
                cal.put(Kind::Pipe { level, streams, passes, over: true }, s, ov);
                println!("#   {:<10} m={:<14} {st:.6} s   fill+drain {ov:.6} s", kind.name(), s.to_string());
            }
            Kind::Gin(..) => {}
        }
    }
    if let Err(e) = calib::save(cal, T::F64) {
        eprintln!("fmm: saving the calibration to {}: {e}", calib::path(T::F64).display());
    }
    count
}
