//! The executor: C = A B on a problem of shape (m x k)(k x n) by a plan.  A fused level of grid
//! g1 x g2 x g3 splits A into g1 x g2 blocks of m/g1 x k/g2, B into g2 x g3 blocks of k/g2 x n/g3
//! and C into g1 x g3 blocks of m/g1 x n/g3, writes the r factors S_q and T_q (one pass per side),
//! computes the products M_q = S_q T_q by the rest of the plan and writes C from the M_q (one
//! pass).  Passes run as row chunks on the library's thread pool, each chunk owning its rows of
//! every output block; GEMM streams take products from a shared queue; a pipelined level runs its
//! sub-problems' passes on a few threads while the streams compute.  All borrows are disjoint by
//! construction and checked by the compiler: no unsafe code here.

use crate::kernels;
use crate::plan::{pad, Entry, Level, Shape};
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
    const R336_L: fn(usize, [&[Self]; 9], [&mut [Self]; 40]);
    const R336_R: fn(usize, [&[Self]; 18], [&mut [Self]; 40]);
    const R336_P: fn(usize, [&[Self]; 40], [&mut [Self]; 18]);
    const R363_L: fn(usize, [&[Self]; 18], [&mut [Self]; 40]);
    const R363_R: fn(usize, [&[Self]; 18], [&mut [Self]; 40]);
    const R363_P: fn(usize, [&[Self]; 40], [&mut [Self]; 9]);
    const R633_L: fn(usize, [&[Self]; 18], [&mut [Self]; 40]);
    const R633_R: fn(usize, [&[Self]; 9], [&mut [Self]; 40]);
    const R633_P: fn(usize, [&[Self]; 40], [&mut [Self]; 18]);
    /// C = A B + beta C for an m x k matrix A and a k x n matrix B, row-major
    fn gemm(s: Shape, a: &[Self], lda: usize, b: &[Self], ldb: usize, beta: f64, c: &mut [Self], ldc: usize);
    fn from_f64(x: f64) -> Self;
    fn to_f64(self) -> f64;
}

macro_rules! real_impl {
    ($t:tt, $f64:expr, $sgemm:path) => {
        impl Real for $t {
            const F64: bool = $f64;
            const SW_L: fn(usize, [&[$t]; 4], [&mut [$t]; 7]) = paste_kernel!(sw_l, $t);
            const SW_R: fn(usize, [&[$t]; 4], [&mut [$t]; 7]) = paste_kernel!(sw_r, $t);
            const SW_P: fn(usize, [&[$t]; 7], [&mut [$t]; 4]) = paste_kernel!(sw_p, $t);
            const D48_L: fn(usize, [&[$t]; 16], [&mut [$t]; 48]) = paste_kernel!(dps48_l, $t);
            const D48_R: fn(usize, [&[$t]; 16], [&mut [$t]; 48]) = paste_kernel!(dps48_r, $t);
            const D48_P: fn(usize, [&[$t]; 48], [&mut [$t]; 16]) = paste_kernel!(dps48_p, $t);
            const R336_L: fn(usize, [&[$t]; 9], [&mut [$t]; 40]) = paste_kernel!(r336_l, $t);
            const R336_R: fn(usize, [&[$t]; 18], [&mut [$t]; 40]) = paste_kernel!(r336_r, $t);
            const R336_P: fn(usize, [&[$t]; 40], [&mut [$t]; 18]) = paste_kernel!(r336_p, $t);
            const R363_L: fn(usize, [&[$t]; 18], [&mut [$t]; 40]) = paste_kernel!(r363_l, $t);
            const R363_R: fn(usize, [&[$t]; 18], [&mut [$t]; 40]) = paste_kernel!(r363_r, $t);
            const R363_P: fn(usize, [&[$t]; 40], [&mut [$t]; 9]) = paste_kernel!(r363_p, $t);
            const R633_L: fn(usize, [&[$t]; 18], [&mut [$t]; 40]) = paste_kernel!(r633_l, $t);
            const R633_R: fn(usize, [&[$t]; 9], [&mut [$t]; 40]) = paste_kernel!(r633_r, $t);
            const R633_P: fn(usize, [&[$t]; 40], [&mut [$t]; 18]) = paste_kernel!(r633_p, $t);
            fn gemm(s: Shape, a: &[$t], lda: usize, b: &[$t], ldb: usize, beta: f64, c: &mut [$t], ldc: usize) {
                $sgemm(s, a, lda, b, ldb, beta as $t, c, ldc)
            }
            fn from_f64(x: f64) -> $t {
                x as $t
            }
            fn to_f64(self) -> f64 {
                self as f64
            }
        }
    };
}

/// the generated kernel of a program for one element type (kernels.rs names them name_f32, name_f64)
macro_rules! paste_kernel {
    (sw_l, f32) => { kernels::sw_l_f32 }; (sw_l, f64) => { kernels::sw_l_f64 };
    (sw_r, f32) => { kernels::sw_r_f32 }; (sw_r, f64) => { kernels::sw_r_f64 };
    (sw_p, f32) => { kernels::sw_p_f32 }; (sw_p, f64) => { kernels::sw_p_f64 };
    (dps48_l, f32) => { kernels::dps48_l_f32 }; (dps48_l, f64) => { kernels::dps48_l_f64 };
    (dps48_r, f32) => { kernels::dps48_r_f32 }; (dps48_r, f64) => { kernels::dps48_r_f64 };
    (dps48_p, f32) => { kernels::dps48_p_f32 }; (dps48_p, f64) => { kernels::dps48_p_f64 };
    (r336_l, f32) => { kernels::r336_l_f32 }; (r336_l, f64) => { kernels::r336_l_f64 };
    (r336_r, f32) => { kernels::r336_r_f32 }; (r336_r, f64) => { kernels::r336_r_f64 };
    (r336_p, f32) => { kernels::r336_p_f32 }; (r336_p, f64) => { kernels::r336_p_f64 };
    (r363_l, f32) => { kernels::r363_l_f32 }; (r363_l, f64) => { kernels::r363_l_f64 };
    (r363_r, f32) => { kernels::r363_r_f32 }; (r363_r, f64) => { kernels::r363_r_f64 };
    (r363_p, f32) => { kernels::r363_p_f32 }; (r363_p, f64) => { kernels::r363_p_f64 };
    (r633_l, f32) => { kernels::r633_l_f32 }; (r633_l, f64) => { kernels::r633_l_f64 };
    (r633_r, f32) => { kernels::r633_r_f32 }; (r633_r, f64) => { kernels::r633_r_f64 };
    (r633_p, f32) => { kernels::r633_p_f32 }; (r633_p, f64) => { kernels::r633_p_f64 };
}

real_impl!(f32, false, sys::sgemm);
real_impl!(f64, true, sys::dgemm);

// ---- passes as row chunks ------------------------------------------------------------------

/// rows r0..r1 of a pass from a grid of blocks of `rows` x `cols` (gc blocks per grid row) of a
/// matrix x (leading dimension ldx) to R contiguous blocks (leading dimension cols): `out` holds
/// those rows of every output block
pub struct Split<'a, T, const NB: usize, const R: usize> {
    kern: fn(usize, [&[T]; NB], [&mut [T]; R]),
    x: &'a [T],
    ldx: usize,
    gc: usize,
    rows: usize,
    cols: usize,
    r0: usize,
    r1: usize,
    out: [&'a mut [T]; R],
}

impl<T: Copy, const NB: usize, const R: usize> Split<'_, T, NB, R> {
    fn run(mut self) {
        let (gc, rows, cols, ldx, x) = (self.gc, self.rows, self.cols, self.ldx, self.x);
        for (k, r) in (self.r0..self.r1).enumerate() {
            let i: [&[T]; NB] = std::array::from_fn(|b| {
                let s = ((b / gc) * rows + r) * ldx + (b % gc) * cols;
                &x[s..s + cols]
            });
            let mut it = self.out.iter_mut();
            let o: [&mut [T]; R] = std::array::from_fn(|_| {
                let ch = it.next().unwrap();
                &mut ch[k * cols..k * cols + cols]
            });
            (self.kern)(cols, i, o);
        }
    }
}

/// rows r0..r1 of a pass from R contiguous blocks of `rows` x `cols` (bs apart, leading dimension
/// cols) to the gr x gc grid of blocks of a matrix y (leading dimension ldy): `segs` holds rows
/// i rows + r0 .. i rows + r1 of y for every block row i
pub struct Merge<'a, T, const R: usize, const NB: usize> {
    kern: fn(usize, [&[T]; R], [&mut [T]; NB]),
    inp: &'a [T],
    bs: usize,
    gc: usize,
    rows: usize,
    cols: usize,
    r0: usize,
    r1: usize,
    segs: Vec<&'a mut [T]>,
    ldy: usize,
}

impl<T: Copy, const R: usize, const NB: usize> Merge<'_, T, R, NB> {
    fn run(mut self) {
        let (gc, cols, bs, ldy, inp) = (self.gc, self.cols, self.bs, self.ldy, self.inp);
        let _ = self.rows;
        for (k, r) in (self.r0..self.r1).enumerate() {
            let i: [&[T]; R] = std::array::from_fn(|q| &inp[q * bs + r * cols..q * bs + r * cols + cols]);
            let mut it = self.segs.iter_mut().flat_map(|seg| seg[k * ldy..k * ldy + gc * cols].chunks_exact_mut(cols));
            let o: [&mut [T]; NB] = std::array::from_fn(|_| it.next().unwrap());
            (self.kern)(cols, i, o);
        }
    }
}

/// a chunk of any pass of the fused level types
pub enum Chunk<'a, T> {
    SwSplit(Split<'a, T, 4, 7>),
    SwMerge(Merge<'a, T, 7, 4>),
    DSplit(Split<'a, T, 16, 48>),
    DMerge(Merge<'a, T, 48, 16>),
    R9Split(Split<'a, T, 9, 40>),
    R18Split(Split<'a, T, 18, 40>),
    R18Merge(Merge<'a, T, 40, 18>),
    R9Merge(Merge<'a, T, 40, 9>),
}

impl<T: Copy> Chunk<'_, T> {
    pub fn run(self) {
        match self {
            Chunk::SwSplit(c) => c.run(),
            Chunk::SwMerge(c) => c.run(),
            Chunk::DSplit(c) => c.run(),
            Chunk::DMerge(c) => c.run(),
            Chunk::R9Split(c) => c.run(),
            Chunk::R18Split(c) => c.run(),
            Chunk::R18Merge(c) => c.run(),
            Chunk::R9Merge(c) => c.run(),
        }
    }
}

fn row_ranges(rows: usize, nch: usize) -> Vec<(usize, usize)> {
    let step = rows.div_ceil(nch.max(1)).max(1);
    (0..rows.div_ceil(step)).map(|c| (c * step, ((c + 1) * step).min(rows))).collect()
}

fn split_chunks<'a, T, const NB: usize, const R: usize>(kern: fn(usize, [&[T]; NB], [&mut [T]; R]), gc: usize,
                                                        rows: usize, cols: usize, x: &'a [T], ldx: usize,
                                                        out: &'a mut [T], bs: usize, nch: usize) -> Vec<Split<'a, T, NB, R>> {
    let ranges = row_ranges(rows, nch);
    let step = ranges.first().map_or(1, |r| r.1 - r.0);
    let mut per_block: Vec<std::slice::ChunksMut<'a, T>> =
        out.chunks_mut(bs).take(R).map(|b| b.split_at_mut(rows * cols).0.chunks_mut(step * cols)).collect();
    assert_eq!(per_block.len(), R, "scratch too short for the level's blocks");
    ranges
        .into_iter()
        .map(|(r0, r1)| {
            let mut it = per_block.iter_mut();
            let out: [&'a mut [T]; R] = std::array::from_fn(|_| it.next().unwrap().next().unwrap());
            Split { kern, x, ldx, gc, rows, cols, r0, r1, out }
        })
        .collect()
}

fn merge_chunks<'a, T, const R: usize, const NB: usize>(kern: fn(usize, [&[T]; R], [&mut [T]; NB]), gr: usize, gc: usize,
                                                        rows: usize, cols: usize, inp: &'a [T], bs: usize, y: &'a mut [T],
                                                        ldy: usize, nch: usize) -> Vec<Merge<'a, T, R, NB>> {
    let ranges = row_ranges(rows, nch);
    let mut segs: Vec<Vec<&'a mut [T]>> = ranges.iter().map(|_| Vec::with_capacity(gr)).collect();
    let mut rest: &'a mut [T] = y;
    for i in 0..gr {
        for (c, &(r0, r1)) in ranges.iter().enumerate() {
            let last = i == gr - 1 && c == ranges.len() - 1;
            let len = if last { rest.len() } else { (r1 - r0) * ldy };
            let (seg, tail) = std::mem::take(&mut rest).split_at_mut(len);
            rest = tail;
            segs[c].push(seg);
        }
    }
    ranges
        .into_iter()
        .zip(segs)
        .map(|((r0, r1), segs)| Merge { kern, inp, bs, gc, rows, cols, r0, r1, segs, ldy })
        .collect()
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Side {
    L,
    R,
}

/// the scratch block sizes (elements, pad included) of a level whose products have shape t: S
/// blocks (as A's), T blocks (as B's), M blocks (as C's)
pub fn block_strides(t: Shape) -> (usize, usize, usize) {
    (t.m * t.k + pad(), t.k * t.n + pad(), t.m * t.n + pad())
}

/// the chunks of a level's L or R pass: the blocks of x (A for L: g1 x g2 blocks of t.m x t.k; B
/// for R: g2 x g3 blocks of t.k x t.n) into its r scratch blocks, bs apart
pub fn factor_chunks<'a, T: Real>(lv: Level, side: Side, x: &'a [T], ldx: usize, t: Shape, out: &'a mut [T], bs: usize,
                                  nch: usize) -> Vec<Chunk<'a, T>> {
    let (_, g2, g3) = lv.grid();
    let (gc, rows, cols) = if side == Side::L { (g2, t.m, t.k) } else { (g3, t.k, t.n) };
    macro_rules! split {
        ($k:expr, $v:ident) => {
            split_chunks($k, gc, rows, cols, x, ldx, out, bs, nch).into_iter().map(Chunk::$v).collect()
        };
    }
    match (lv, side) {
        (Level::Sw, Side::L) => split!(T::SW_L, SwSplit),
        (Level::Sw, Side::R) => split!(T::SW_R, SwSplit),
        (Level::D48, Side::L) => split!(T::D48_L, DSplit),
        (Level::D48, Side::R) => split!(T::D48_R, DSplit),
        (Level::R336, Side::L) => split!(T::R336_L, R9Split),
        (Level::R336, Side::R) => split!(T::R336_R, R18Split),
        (Level::R363, Side::L) => split!(T::R363_L, R18Split),
        (Level::R363, Side::R) => split!(T::R363_R, R18Split),
        (Level::R633, Side::L) => split!(T::R633_L, R18Split),
        (Level::R633, Side::R) => split!(T::R633_R, R9Split),
        _ => unreachable!("not a fused level"),
    }
}

/// the chunks of a level's P pass: its r products (t.m x t.n blocks, bs apart) into the g1 x g3
/// blocks of y
pub fn product_chunks<'a, T: Real>(lv: Level, inp: &'a [T], bs: usize, t: Shape, y: &'a mut [T], ldy: usize,
                                   nch: usize) -> Vec<Chunk<'a, T>> {
    let (g1, _, g3) = lv.grid();
    macro_rules! merge {
        ($k:expr, $v:ident) => {
            merge_chunks($k, g1, g3, t.m, t.n, inp, bs, y, ldy, nch).into_iter().map(Chunk::$v).collect()
        };
    }
    match lv {
        Level::Sw => merge!(T::SW_P, SwMerge),
        Level::D48 => merge!(T::D48_P, DMerge),
        Level::R336 => merge!(T::R336_P, R18Merge),
        Level::R363 => merge!(T::R363_P, R9Merge),
        Level::R633 => merge!(T::R633_P, R18Merge),
        _ => unreachable!("not a fused level"),
    }
}

/// run chunks on every thread of the pool
pub fn run_par<T: Real>(chunks: Vec<Chunk<'_, T>>) {
    chunks.into_par_iter().for_each(Chunk::run);
}

// ---- products ------------------------------------------------------------------------------

/// the r products of a level, of shape t, as k single-threaded GEMM streams taking products in
/// turn; the S, T and M blocks are bss, bst and bsm apart
pub fn gemm_streams<T: Real>(r: usize, t: Shape, s_all: &[T], t_all: &[T], m_all: &mut [T], bss: usize, bst: usize,
                             bsm: usize, k: usize) {
    let items: Vec<(&[T], &[T], &mut [T])> = m_all
        .chunks_mut(bsm)
        .take(r)
        .enumerate()
        .map(|(q, mm)| (&s_all[q * bss..q * bss + t.m * t.k], &t_all[q * bst..q * bst + t.k * t.n], mm.split_at_mut(t.m * t.n).0))
        .collect();
    let queue = Mutex::new(items.into_iter());
    rayon::scope(|s| {
        for _ in 0..k {
            s.spawn(|_| {
                sys::set_single_threaded(true);
                loop {
                    let next = queue.lock().unwrap().next();
                    let Some((sa, ta, ma)) = next else { break };
                    T::gemm(t, sa, t.k, ta, t.n, 0.0, ma, t.n);
                }
                sys::set_single_threaded(false);
            });
        }
    });
}

/// inputs of a pipeline's sub-problems: sub-problem q's matrix, contiguous (leading dimension its
/// columns)
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

/// r sub-problems of shape t (SX[q] t.m x t.k, TX[q] t.k x t.n, MX[q] t.m x t.n, each contiguous),
/// each a level Y (py[0]) over k GEMM streams (py[1]), pipelined: in step q the streams compute
/// the products of sub-problem q while w pass threads write the result of sub-problem q - 1 (Y's P
/// pass) and the factors of sub-problem q + 1 (Y's L and R passes); Y's scratch is
/// double-buffered (sets q % 2), so each step borrows one set for the streams and the other for
/// the passes.  The first factors and the last result run on every thread.
pub fn pipeline<T: Real>(py: &[Entry], t: Shape, r: usize, sx: &dyn Blocks<T>, tx: &dyn Blocks<T>,
                         mx: &mut dyn BlocksMut<T>, work: &mut [T], w: usize) {
    let (ly, k) = (py[0].level, py[1].streams as usize);
    let ry = ly.rank();
    let ty = ly.sub(t);
    let (bss, bst, bsm) = block_strides(ty);
    let set = ry * (bss + bst + bsm);
    let (set0, rest) = work.split_at_mut(set);
    let set1 = &mut rest[..set];
    for q in -1..=(r as isize) {
        let gq = q >= 0 && (q as usize) < r;
        let (gset, oset): (&mut [T], &mut [T]) =
            if q.rem_euclid(2) == 0 { (&mut set0[..], &mut set1[..]) } else { (&mut set1[..], &mut set0[..]) };
        let (gs, grest) = gset.split_at_mut(ry * bss);
        let (gt, gm) = grest.split_at_mut(ry * bst);
        let (os, orest) = oset.split_at_mut(ry * bss);
        let (ot, om) = orest.split_at_mut(ry * bst);
        let mut chunks: Vec<Chunk<'_, T>> = vec![];
        if q >= 1 {
            chunks.extend(product_chunks(ly, &*om, bsm, ty, mx.get_mut(q as usize - 1), t.n, 16));
        }
        if q + 1 < r as isize {
            let qi = (q + 1) as usize;
            chunks.extend(factor_chunks(ly, Side::L, sx.get(qi), t.k, ty, os, bss, 16));
            chunks.extend(factor_chunks(ly, Side::R, tx.get(qi), t.n, ty, ot, bst, 16));
        }
        if !gq {
            run_par(chunks);                // fill and drain: nothing to hide the passes behind
            continue;
        }
        let gemms: Vec<(&[T], &[T], &mut [T])> = gm
            .chunks_mut(bsm)
            .take(ry)
            .enumerate()
            .map(|(j, mm)| (&gs[j * bss..j * bss + ty.m * ty.k], &gt[j * bst..j * bst + ty.k * ty.n], mm.split_at_mut(ty.m * ty.n).0))
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
                        T::gemm(ty, sa, ty.k, ta, ty.n, 0.0, ma, ty.n);
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

/// classical C = A B as g^3 block GEMMs accumulating into C
fn classical_blocked<T: Real>(g: usize, s: Shape, a: &[T], lda: usize, b: &[T], ldb: usize, c: &mut [T], ldc: usize) {
    let (mb, kb, nb) = (s.m / g, s.k / g, s.n / g);
    let blk = Shape::new(mb, kb, nb);
    for i in 0..g {
        for j in 0..g {
            for kk in 0..g {
                T::gemm(blk, &a[i * mb * lda + kk * kb..], lda, &b[kk * kb * ldb + j * nb..], ldb,
                        if kk > 0 { 1.0 } else { 0.0 }, &mut c[i * mb * ldc + j * nb..], ldc);
            }
        }
    }
}

/// C = A B on a problem of shape s by a plan; work holds plan.work(s) elements
pub fn exec<T: Real>(plan: &[Entry], s: Shape, a: &[T], lda: usize, b: &[T], ldb: usize, c: &mut [T], ldc: usize,
                     work: &mut [T]) {
    let e = plan[0];
    match e.level {
        Level::G => T::gemm(s, a, lda, b, ldb, 0.0, c, ldc),
        Level::B2 => classical_blocked(2, s, a, lda, b, ldb, c, ldc),
        lv => {
            let r = lv.rank();
            let t = lv.sub(s);
            let (bss, bst, bsm) = block_strides(t);
            let (s_all, rest) = work.split_at_mut(r * bss);
            let (t_all, rest) = rest.split_at_mut(r * bst);
            let (m_all, deeper) = rest.split_at_mut(r * bsm);
            run_par(factor_chunks(lv, Side::L, a, lda, t, &mut *s_all, bss, NCH));
            run_par(factor_chunks(lv, Side::R, b, ldb, t, &mut *t_all, bst, NCH));
            let (s_all, t_all) = (&*s_all, &*t_all);
            let next = plan[1];
            if e.pipe.is_some() && !next.level.is_leaf() && plan.get(2).is_some_and(|l| l.level == Level::G && l.streams > 0) {
                let sx = Strided { buf: s_all, bs: bss, len: t.m * t.k };
                let tx = Strided { buf: t_all, bs: bst, len: t.k * t.n };
                let mut mx = StridedMut { buf: &mut *m_all, bs: bsm, len: t.m * t.n };
                pipeline(&plan[1..3], t, r, &sx, &tx, &mut mx, deeper, e.pass_threads());
            } else if next.level == Level::G && next.streams > 0 {
                gemm_streams(r, t, s_all, t_all, &mut *m_all, bss, bst, bsm, next.streams as usize);
            } else {
                for q in 0..r {
                    let mq = &mut m_all[q * bsm..q * bsm + t.m * t.n];
                    exec(&plan[1..], t, &s_all[q * bss..q * bss + t.m * t.k], t.k, &t_all[q * bst..q * bst + t.k * t.n], t.n, mq,
                         t.n, &mut *deeper);
                }
            }
            run_par(product_chunks(lv, &*m_all, bsm, t, c, ldc, NCH));
        }
    }
}

/// workspace elements for running a plan on shape s at the padded shape sp >= s: the padded copies
/// of A, B and C, then the plan's scratch
pub fn padded_work(plan: &crate::plan::Plan, s: Shape, sp: Shape) -> usize {
    (if sp != s { sp.m * sp.k + sp.k * sp.n + sp.m * sp.n } else { 0 }) + plan.work(sp)
}

/// copy the top-left rows x cols of x (leading dimension ldx) into the zeroed rows_p x cols_p
/// matrix y (contiguous), rows in parallel
fn pad_copy<T: Real>(x: &[T], ldx: usize, rows: usize, cols: usize, y: &mut [T], rows_p: usize, cols_p: usize) {
    debug_assert!(y.len() >= rows_p * cols_p);
    y[..rows_p * cols_p].par_chunks_mut(cols_p).enumerate().for_each(|(i, row)| {
        if i < rows {
            row[..cols].copy_from_slice(&x[i * ldx..i * ldx + cols]);
            row[cols..].fill(T::default());
        } else {
            row.fill(T::default());
        }
    });
}

/// C = A B on shape s through a plan at the padded shape sp >= s: A and B copied into zeroed
/// padded matrices, the result's top-left s.m x s.n copied to C
pub fn exec_padded<T: Real>(plan: &[Entry], s: Shape, sp: Shape, a: &[T], lda: usize, b: &[T], ldb: usize, c: &mut [T],
                            ldc: usize, work: &mut [T]) {
    if sp == s {
        return exec(plan, s, a, lda, b, ldb, c, ldc, work);
    }
    let (ap, rest) = work.split_at_mut(sp.m * sp.k);
    let (bp, rest) = rest.split_at_mut(sp.k * sp.n);
    let (cp, rest) = rest.split_at_mut(sp.m * sp.n);
    pad_copy(a, lda, s.m, s.k, ap, sp.m, sp.k);
    pad_copy(b, ldb, s.k, s.n, bp, sp.k, sp.n);
    exec(plan, sp, ap, sp.k, bp, sp.n, cp, sp.n, rest);
    let cp = &*cp;
    c.par_chunks_mut(ldc).take(s.m).enumerate().for_each(|(i, row)| row[..s.n].copy_from_slice(&cp[i * sp.n..i * sp.n + s.n]));
}
