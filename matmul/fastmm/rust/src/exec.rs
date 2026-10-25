//! The executor: C = A B at size n by a plan.  A fused level splits A, B, C into a g x g grid of
//! blocks of m = n / g, writes the r factors S_k and T_k (one pass per side), computes the
//! products M_k = S_k T_k by the rest of the plan and writes C from the M_k (one pass).  Passes
//! run as row chunks on the library's thread pool, each chunk owning its rows of every output
//! block; GEMM streams take products from a shared queue; a pipelined level runs its
//! sub-problems' passes on a few threads while the streams compute.  All borrows are disjoint by
//! construction and checked by the compiler: no unsafe code here.

use crate::kernels;
use crate::plan::{pad, Entry, Level};
use crate::sys;
use rayon::prelude::*;
use std::sync::Mutex;

/// row chunks per pass
const NCH: usize = 64;

/// f32 or f64: Accelerate's GEMM and the generated kernels
pub trait Real: Copy + Send + Sync + Default + PartialEq + std::fmt::Debug + 'static {
    const F64: bool;
    const SW_L: fn(usize, [&[Self]; 4], [&mut [Self]; 7]);
    const SW_R: fn(usize, [&[Self]; 4], [&mut [Self]; 7]);
    const SW_P: fn(usize, [&[Self]; 7], [&mut [Self]; 4]);
    const D48_L: fn(usize, [&[Self]; 16], [&mut [Self]; 48]);
    const D48_R: fn(usize, [&[Self]; 16], [&mut [Self]; 48]);
    const D48_P: fn(usize, [&[Self]; 48], [&mut [Self]; 16]);
    /// C = A B + beta C, m x m row-major
    fn gemm(m: usize, a: &[Self], lda: usize, b: &[Self], ldb: usize, beta: f64, c: &mut [Self], ldc: usize);
    fn from_f64(x: f64) -> Self;
    fn to_f64(self) -> f64;
}

impl Real for f32 {
    const F64: bool = false;
    const SW_L: fn(usize, [&[f32]; 4], [&mut [f32]; 7]) = kernels::sw_l_f32;
    const SW_R: fn(usize, [&[f32]; 4], [&mut [f32]; 7]) = kernels::sw_r_f32;
    const SW_P: fn(usize, [&[f32]; 7], [&mut [f32]; 4]) = kernels::sw_p_f32;
    const D48_L: fn(usize, [&[f32]; 16], [&mut [f32]; 48]) = kernels::dps48_l_f32;
    const D48_R: fn(usize, [&[f32]; 16], [&mut [f32]; 48]) = kernels::dps48_r_f32;
    const D48_P: fn(usize, [&[f32]; 48], [&mut [f32]; 16]) = kernels::dps48_p_f32;
    fn gemm(m: usize, a: &[f32], lda: usize, b: &[f32], ldb: usize, beta: f64, c: &mut [f32], ldc: usize) {
        sys::sgemm(m, a, lda, b, ldb, beta as f32, c, ldc)
    }
    fn from_f64(x: f64) -> f32 {
        x as f32
    }
    fn to_f64(self) -> f64 {
        self as f64
    }
}

impl Real for f64 {
    const F64: bool = true;
    const SW_L: fn(usize, [&[f64]; 4], [&mut [f64]; 7]) = kernels::sw_l_f64;
    const SW_R: fn(usize, [&[f64]; 4], [&mut [f64]; 7]) = kernels::sw_r_f64;
    const SW_P: fn(usize, [&[f64]; 7], [&mut [f64]; 4]) = kernels::sw_p_f64;
    const D48_L: fn(usize, [&[f64]; 16], [&mut [f64]; 48]) = kernels::dps48_l_f64;
    const D48_R: fn(usize, [&[f64]; 16], [&mut [f64]; 48]) = kernels::dps48_r_f64;
    const D48_P: fn(usize, [&[f64]; 48], [&mut [f64]; 16]) = kernels::dps48_p_f64;
    fn gemm(m: usize, a: &[f64], lda: usize, b: &[f64], ldb: usize, beta: f64, c: &mut [f64], ldc: usize) {
        sys::dgemm(m, a, lda, b, ldb, beta, c, ldc)
    }
    fn from_f64(x: f64) -> f64 {
        x
    }
    fn to_f64(self) -> f64 {
        self
    }
}

// ---- passes as row chunks ------------------------------------------------------------------

/// rows r0..r1 of a pass from the g x g blocks of a matrix x (leading dimension ldx) to R
/// contiguous blocks (leading dimension m): `out` holds those rows of every output block
pub struct Split<'a, T, const NB: usize, const R: usize> {
    kern: fn(usize, [&[T]; NB], [&mut [T]; R]),
    x: &'a [T],
    ldx: usize,
    g: usize,
    m: usize,
    r0: usize,
    r1: usize,
    out: [&'a mut [T]; R],
}

impl<T: Copy, const NB: usize, const R: usize> Split<'_, T, NB, R> {
    fn run(mut self) {
        let (g, m, ldx, x) = (self.g, self.m, self.ldx, self.x);
        for (k, r) in (self.r0..self.r1).enumerate() {
            let i: [&[T]; NB] = std::array::from_fn(|b| {
                let s = ((b / g) * m + r) * ldx + (b % g) * m;
                &x[s..s + m]
            });
            let mut it = self.out.iter_mut();
            let o: [&mut [T]; R] = std::array::from_fn(|_| {
                let ch = it.next().unwrap();
                &mut ch[k * m..k * m + m]
            });
            (self.kern)(m, i, o);
        }
    }
}

/// rows r0..r1 of a pass from R contiguous blocks (bs apart, leading dimension m) to the g x g
/// blocks of a matrix y (leading dimension ldy): `segs` holds rows i m + r0 .. i m + r1 of y for
/// every block row i
pub struct Merge<'a, T, const R: usize, const NB: usize> {
    kern: fn(usize, [&[T]; R], [&mut [T]; NB]),
    inp: &'a [T],
    bs: usize,
    g: usize,
    m: usize,
    r0: usize,
    r1: usize,
    segs: Vec<&'a mut [T]>,
    ldy: usize,
}

impl<T: Copy, const R: usize, const NB: usize> Merge<'_, T, R, NB> {
    fn run(mut self) {
        let (g, m, bs, ldy, inp) = (self.g, self.m, self.bs, self.ldy, self.inp);
        for (k, r) in (self.r0..self.r1).enumerate() {
            let i: [&[T]; R] = std::array::from_fn(|q| &inp[q * bs + r * m..q * bs + r * m + m]);
            let mut it = self.segs.iter_mut().flat_map(|seg| seg[k * ldy..k * ldy + g * m].chunks_exact_mut(m));
            let o: [&mut [T]; NB] = std::array::from_fn(|_| it.next().unwrap());
            (self.kern)(m, i, o);
        }
    }
}

/// a chunk of any pass of the two fused level types
pub enum Chunk<'a, T> {
    SwSplit(Split<'a, T, 4, 7>),
    SwMerge(Merge<'a, T, 7, 4>),
    DSplit(Split<'a, T, 16, 48>),
    DMerge(Merge<'a, T, 48, 16>),
}

impl<T: Copy> Chunk<'_, T> {
    pub fn run(self) {
        match self {
            Chunk::SwSplit(c) => c.run(),
            Chunk::SwMerge(c) => c.run(),
            Chunk::DSplit(c) => c.run(),
            Chunk::DMerge(c) => c.run(),
        }
    }
}

fn row_ranges(m: usize, nch: usize) -> Vec<(usize, usize)> {
    let step = m.div_ceil(nch.max(1)).max(1);
    (0..m.div_ceil(step)).map(|c| (c * step, ((c + 1) * step).min(m))).collect()
}

fn split_chunks<'a, T, const NB: usize, const R: usize>(kern: fn(usize, [&[T]; NB], [&mut [T]; R]), g: usize, m: usize,
                                                        x: &'a [T], ldx: usize, out: &'a mut [T], bs: usize,
                                                        nch: usize) -> Vec<Split<'a, T, NB, R>> {
    let ranges = row_ranges(m, nch);
    let step = ranges.first().map_or(1, |r| r.1 - r.0);
    let mut per_block: Vec<std::slice::ChunksMut<'a, T>> =
        out.chunks_mut(bs).take(R).map(|b| b.split_at_mut(m * m).0.chunks_mut(step * m)).collect();
    assert_eq!(per_block.len(), R, "scratch too short for the level's blocks");
    ranges
        .into_iter()
        .map(|(r0, r1)| {
            let mut it = per_block.iter_mut();
            let out: [&'a mut [T]; R] = std::array::from_fn(|_| it.next().unwrap().next().unwrap());
            Split { kern, x, ldx, g, m, r0, r1, out }
        })
        .collect()
}

fn merge_chunks<'a, T, const R: usize, const NB: usize>(kern: fn(usize, [&[T]; R], [&mut [T]; NB]), g: usize, m: usize,
                                                        inp: &'a [T], bs: usize, y: &'a mut [T], ldy: usize,
                                                        nch: usize) -> Vec<Merge<'a, T, R, NB>> {
    let ranges = row_ranges(m, nch);
    let mut segs: Vec<Vec<&'a mut [T]>> = ranges.iter().map(|_| Vec::with_capacity(g)).collect();
    let mut rest: &'a mut [T] = y;
    for i in 0..g {
        for (c, &(r0, r1)) in ranges.iter().enumerate() {
            let last = i == g - 1 && c == ranges.len() - 1;
            let len = if last { rest.len() } else { (r1 - r0) * ldy };
            let (seg, tail) = std::mem::take(&mut rest).split_at_mut(len);
            rest = tail;
            let _ = (i, r0);
            segs[c].push(seg);
        }
    }
    ranges
        .into_iter()
        .zip(segs)
        .map(|((r0, r1), segs)| Merge { kern, inp, bs, g, m, r0, r1, segs, ldy })
        .collect()
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Side {
    L,
    R,
}

/// the chunks of a level's L or R pass: the g x g blocks of x into its r scratch blocks
pub fn factor_chunks<'a, T: Real>(lv: Level, side: Side, x: &'a [T], ldx: usize, m: usize, out: &'a mut [T], bs: usize,
                                  nch: usize) -> Vec<Chunk<'a, T>> {
    match lv {
        Level::Sw => {
            let k = if side == Side::L { T::SW_L } else { T::SW_R };
            split_chunks(k, 2, m, x, ldx, out, bs, nch).into_iter().map(Chunk::SwSplit).collect()
        }
        Level::D48 => {
            let k = if side == Side::L { T::D48_L } else { T::D48_R };
            split_chunks(k, 4, m, x, ldx, out, bs, nch).into_iter().map(Chunk::DSplit).collect()
        }
        _ => unreachable!("not a fused level"),
    }
}

/// the chunks of a level's P pass: its r products into the g x g blocks of y
pub fn product_chunks<'a, T: Real>(lv: Level, inp: &'a [T], bs: usize, m: usize, y: &'a mut [T], ldy: usize,
                                   nch: usize) -> Vec<Chunk<'a, T>> {
    match lv {
        Level::Sw => merge_chunks(T::SW_P, 2, m, inp, bs, y, ldy, nch).into_iter().map(Chunk::SwMerge).collect(),
        Level::D48 => merge_chunks(T::D48_P, 4, m, inp, bs, y, ldy, nch).into_iter().map(Chunk::DMerge).collect(),
        _ => unreachable!("not a fused level"),
    }
}

/// run chunks on every thread of the pool
pub fn run_par<T: Real>(chunks: Vec<Chunk<'_, T>>) {
    chunks.into_par_iter().for_each(Chunk::run);
}

// ---- products ------------------------------------------------------------------------------

/// the r products of a level as k single-threaded GEMM streams taking products in turn
pub fn gemm_streams<T: Real>(r: usize, m: usize, s_all: &[T], t_all: &[T], m_all: &mut [T], bs: usize, k: usize) {
    let items: Vec<(&[T], &[T], &mut [T])> = m_all
        .chunks_mut(bs)
        .take(r)
        .enumerate()
        .map(|(q, mm)| (&s_all[q * bs..q * bs + m * m], &t_all[q * bs..q * bs + m * m], mm.split_at_mut(m * m).0))
        .collect();
    let queue = Mutex::new(items.into_iter());
    rayon::scope(|s| {
        for _ in 0..k {
            s.spawn(|_| {
                sys::set_single_threaded(true);
                loop {
                    let next = queue.lock().unwrap().next();
                    let Some((sa, ta, ma)) = next else { break };
                    T::gemm(m, sa, m, ta, m, 0.0, ma, m);
                }
                sys::set_single_threaded(false);
            });
        }
    });
}

/// inputs of a pipeline's sub-problems: sub-problem q's m x m matrix (leading dimension m)
pub trait Blocks<T>: Sync {
    fn get(&self, q: usize) -> &[T];
}

/// outputs of a pipeline's sub-problems
pub trait BlocksMut<T> {
    fn get_mut(&mut self, q: usize) -> &mut [T];
}

/// blocks of size len, bs apart in buf
pub struct Strided<'a, T> {
    pub buf: &'a [T],
    pub bs: usize,
    pub len: usize,
}

impl<T: Sync> Blocks<T> for Strided<'_, T> {
    fn get(&self, q: usize) -> &[T] {
        &self.buf[q * self.bs..q * self.bs + self.len]
    }
}

pub struct StridedMut<'a, T> {
    pub buf: &'a mut [T],
    pub bs: usize,
    pub len: usize,
}

impl<T> BlocksMut<T> for StridedMut<'_, T> {
    fn get_mut(&mut self, q: usize) -> &mut [T] {
        &mut self.buf[q * self.bs..q * self.bs + self.len]
    }
}

/// r sub-problems, each a level Y (py[0]) over k GEMM streams (py[1]), pipelined: in step q the
/// streams compute the products of sub-problem q while w pass threads write the result of
/// sub-problem q - 1 (Y's P pass) and the factors of sub-problem q + 1 (Y's L and R passes); Y's
/// scratch is double-buffered (sets q % 2), so each step borrows one set for the streams and the
/// other for the passes.  The first factors and the last result run on every thread.
pub fn pipeline<T: Real>(py: &[Entry], m: usize, r: usize, sx: &dyn Blocks<T>, tx: &dyn Blocks<T>,
                         mx: &mut dyn BlocksMut<T>, work: &mut [T], w: usize) {
    let (ly, k) = (py[0].level, py[1].streams as usize);
    let (gy, ry) = (ly.grid(), ly.rank());
    let my = m / gy;
    let bsy = my * my + pad();
    let set = 3 * ry * bsy;
    let (set0, rest) = work.split_at_mut(set);
    let set1 = &mut rest[..set];
    for q in -1..=(r as isize) {
        let gq = q >= 0 && (q as usize) < r;
        let (gset, oset): (&mut [T], &mut [T]) =
            if q.rem_euclid(2) == 0 { (&mut set0[..], &mut set1[..]) } else { (&mut set1[..], &mut set0[..]) };
        let (gs, grest) = gset.split_at_mut(ry * bsy);
        let (gt, gm) = grest.split_at_mut(ry * bsy);
        let (os, orest) = oset.split_at_mut(ry * bsy);
        let (ot, om) = orest.split_at_mut(ry * bsy);
        let mut chunks: Vec<Chunk<'_, T>> = vec![];
        if q >= 1 {
            chunks.extend(product_chunks(ly, &*om, bsy, my, mx.get_mut(q as usize - 1), m, 16));
        }
        if q + 1 < r as isize {
            let qi = (q + 1) as usize;
            chunks.extend(factor_chunks(ly, Side::L, sx.get(qi), m, my, os, bsy, 16));
            chunks.extend(factor_chunks(ly, Side::R, tx.get(qi), m, my, ot, bsy, 16));
        }
        if !gq {
            run_par(chunks);                // fill and drain: nothing to hide the passes behind
            continue;
        }
        let gemms: Vec<(&[T], &[T], &mut [T])> = gm
            .chunks_mut(bsy)
            .take(ry)
            .enumerate()
            .map(|(j, mm)| (&gs[j * bsy..j * bsy + my * my], &gt[j * bsy..j * bsy + my * my], mm.split_at_mut(my * my).0))
            .collect();
        let gq_items = Mutex::new(gemms.into_iter());
        let pq_items = Mutex::new(chunks.into_iter());
        rayon::scope(|s| {
            for _ in 0..k {
                s.spawn(|_| {
                    sys::set_single_threaded(true);
                    loop {
                        let next = gq_items.lock().unwrap().next();
                        let Some((sa, ta, ma)) = next else { break };
                        T::gemm(my, sa, my, ta, my, 0.0, ma, my);
                    }
                    sys::set_single_threaded(false);
                });
            }
            for _ in 0..w {
                s.spawn(|_| loop {
                    let next = pq_items.lock().unwrap().next();
                    let Some(c) = next else { break };
                    c.run();
                });
            }
        });
    }
}

// ---- the executor ----------------------------------------------------------------------------

/// classical C = A B as g^3 block GEMMs of size n / g accumulating into C
fn classical_blocked<T: Real>(g: usize, n: usize, a: &[T], lda: usize, b: &[T], ldb: usize, c: &mut [T], ldc: usize) {
    let m = n / g;
    for i in 0..g {
        for j in 0..g {
            for kk in 0..g {
                T::gemm(m, &a[i * m * lda + kk * m..], lda, &b[kk * m * ldb + j * m..], ldb,
                        if kk > 0 { 1.0 } else { 0.0 }, &mut c[i * m * ldc + j * m..], ldc);
            }
        }
    }
}

/// C = A B at size n by a plan; work holds plan.work(n) elements
pub fn exec<T: Real>(plan: &[Entry], n: usize, a: &[T], lda: usize, b: &[T], ldb: usize, c: &mut [T], ldc: usize,
                     work: &mut [T]) {
    let e = plan[0];
    match e.level {
        Level::G => T::gemm(n, a, lda, b, ldb, 0.0, c, ldc),
        Level::B2 => classical_blocked(2, n, a, lda, b, ldb, c, ldc),
        lv => {
            let (g, r) = (lv.grid(), lv.rank());
            let m = n / g;
            let bs = m * m + pad();
            let (s_all, rest) = work.split_at_mut(r * bs);
            let (t_all, rest) = rest.split_at_mut(r * bs);
            let (m_all, deeper) = rest.split_at_mut(r * bs);
            run_par(factor_chunks(lv, Side::L, a, lda, m, &mut *s_all, bs, NCH));
            run_par(factor_chunks(lv, Side::R, b, ldb, m, &mut *t_all, bs, NCH));
            let (s_all, t_all) = (&*s_all, &*t_all);
            let next = plan[1];
            if e.pipe.is_some() && !next.level.is_leaf() && plan.get(2).is_some_and(|l| l.level == Level::G && l.streams > 0) {
                let sx = Strided { buf: s_all, bs, len: m * m };
                let tx = Strided { buf: t_all, bs, len: m * m };
                let mut mx = StridedMut { buf: &mut *m_all, bs, len: m * m };
                pipeline(&plan[1..3], m, r, &sx, &tx, &mut mx, deeper, e.pass_threads());
            } else if next.level == Level::G && next.streams > 0 {
                gemm_streams(r, m, s_all, t_all, &mut *m_all, bs, next.streams as usize);
            } else {
                for q in 0..r {
                    let mq = &mut m_all[q * bs..q * bs + m * m];
                    exec(&plan[1..], m, &s_all[q * bs..q * bs + m * m], m, &t_all[q * bs..q * bs + m * m], m, mq, m,
                         &mut *deeper);
                }
            }
            run_par(product_chunks(lv, &*m_all, bs, m, c, ldc, NCH));
        }
    }
}

/// scratch elements for running a plan at the padded size npad >= n
pub fn padded_work(plan: &crate::plan::Plan, n: usize, npad: usize) -> usize {
    (if npad != n { 3 * npad * npad } else { 0 }) + plan.work(npad)
}

/// C = A B at size n through a plan at the padded size npad >= n: A and B copied into zeroed
/// npad x npad matrices, the result's top-left n x n copied to C
pub fn exec_padded<T: Real>(plan: &[Entry], n: usize, npad: usize, a: &[T], lda: usize, b: &[T], ldb: usize,
                            c: &mut [T], ldc: usize, work: &mut [T]) {
    if npad == n {
        return exec(plan, n, a, lda, b, ldb, c, ldc, work);
    }
    let nn = npad * npad;
    let (ap, rest) = work.split_at_mut(nn);
    let (bp, rest) = rest.split_at_mut(nn);
    let (cp, rest) = rest.split_at_mut(nn);
    for (dst, src, ld) in [(&mut *ap, a, lda), (&mut *bp, b, ldb)] {
        dst.par_chunks_mut(npad).enumerate().for_each(|(i, row)| {
            if i < n {
                row[..n].copy_from_slice(&src[i * ld..i * ld + n]);
                row[n..].fill(T::default());
            } else {
                row.fill(T::default());
            }
        });
    }
    exec(plan, npad, ap, npad, bp, npad, cp, npad, rest);
    let cp = &*cp;
    c.par_chunks_mut(ldc).take(n).enumerate().for_each(|(i, row)| row[..n].copy_from_slice(&cp[i * npad..i * npad + n]));
}
