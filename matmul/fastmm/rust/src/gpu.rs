//! The GPU as a second engine for a level's f32 products (the feature `gpu`): the C library's
//! gpu_leaf.m (Metal Performance Shaders' matrix multiplication on shared, uncopied memory), linked
//! in by build.rs, behind safe wrappers.  The GPU's f32 product is the k-ordered chain of fused
//! multiply-adds, bit for bit Accelerate's sgemm, so sharing a level's products with it leaves a
//! plan's result unchanged.
//!
//! The GPU reads and writes memory through regions wrapped as Metal buffers.  A region is only
//! ever memory this crate holds for as long as it is wrapped: a `Pinned` buffer (the workspace,
//! the calibration's matrices), wrapped from its creation to its drop, or a caller's matrices,
//! wrapped for the duration of one call (`with_attached`).  A batch names its blocks by slices,
//! which the wrapper checks against the matrices' extents; the C side refuses a batch whose blocks
//! are not inside wrapped regions (and the caller then computes it on the CPU).  Without the
//! feature every function here reports no GPU.
#![allow(unsafe_code)]

use crate::plan::Shape;

/// the page size of Apple silicon, the granularity of a wrapped region
pub const PAGE: usize = 16384;

#[cfg(feature = "gpu")]
mod ffi {
    use std::os::raw::{c_int, c_void};
    unsafe extern "C" {
        pub fn fmm_gpu_attach(base: *const c_void, bytes: usize) -> c_int;
        pub fn fmm_gpu_detach(base: *const c_void);
        pub fn fmm_gpu_available() -> c_int;
        pub fn fmm_gpu_sgemm_batch(m: usize, k: usize, n: usize, count: c_int, a: *const *const f32, lda: usize,
                                   b: *const *const f32, ldb: usize, c: *const *mut f32, ldc: usize) -> c_int;
    }
}

/// whether there is a GPU to share products with (always false without the feature)
pub fn available() -> bool {
    #[cfg(feature = "gpu")]
    {
        static OK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        // SAFETY: no arguments; initializes the Metal device once
        *OK.get_or_init(|| unsafe { ffi::fmm_gpu_available() } != 0)
    }
    #[cfg(not(feature = "gpu"))]
    false
}

/// wrap [base, base + bytes) for the GPU; the caller guarantees the memory stays valid and is
/// detached before it is freed (Pinned's drop, with_attached's guard)
#[cfg(feature = "gpu")]
fn attach(base: usize, bytes: usize) -> bool {
    debug_assert!(base % PAGE == 0 && bytes % PAGE == 0 && bytes > 0);
    // SAFETY: the region is page-aligned whole pages of memory the caller holds (see above);
    // wrapping it copies nothing and the GPU touches it only inside sgemm_batch
    unsafe { ffi::fmm_gpu_attach(base as *const std::os::raw::c_void, bytes) == 0 }
}

#[cfg(not(feature = "gpu"))]
fn attach(_base: usize, _bytes: usize) -> bool {
    false
}

#[cfg(feature = "gpu")]
fn detach(base: usize) {
    // SAFETY: drops the wrapper of a region attached here; no batch is in flight (they wait)
    unsafe { ffi::fmm_gpu_detach(base as *const std::os::raw::c_void) }
}

#[cfg(not(feature = "gpu"))]
fn detach(_base: usize) {}

/// detaches a region on drop (also when unwinding)
struct Guard(usize);

impl Drop for Guard {
    fn drop(&mut self) {
        detach(self.0);
    }
}

/// the whole pages of a slice from its first element: Some((base, bytes)) if the slice starts
/// on a page and its whole pages cover `need` elements (the extent the GPU may touch)
fn pages_of<T>(s: &[T], need: usize) -> Option<(usize, usize)> {
    let (base, bytes) = (s.as_ptr() as usize, std::mem::size_of_val(s) / PAGE * PAGE);
    (base % PAGE == 0 && bytes > 0 && bytes >= need * std::mem::size_of::<T>()).then_some((base, bytes))
}

/// f(a, b, c) with the three matrices wrapped for the GPU (a K level's strips are the operands
/// themselves), each over its extent `ext` in elements; None, without calling f, if they cannot be
/// wrapped (not starting on a page, or the GPU absent).  The C library wraps a matrix that starts
/// on a page whatever its length (malloc's allocations are page-granular there); a slice may end
/// anywhere inside its allocation, so here only its whole pages are wrapped, and they must cover
/// the extent.
pub fn with_attached<T, R>(a: &[T], b: &[T], c: &mut [T], ext: [usize; 3], f: impl FnOnce(&[T], &[T], &mut [T]) -> R)
                           -> Option<R> {
    let regions = [pages_of(a, ext[0])?, pages_of(b, ext[1])?, pages_of(c, ext[2])?];
    let mut guards = Vec::with_capacity(3);
    for (base, bytes) in regions {
        if !attach(base, bytes) {
            return None;            // the guards detach what was attached
        }
        guards.push(Guard(base));
    }
    let r = f(a, b, c);
    drop(guards);
    Some(r)
}

/// A buffer of `len` elements starting on a page, wrapped for the GPU (if `attach` and there is
/// one) from its creation until it is dropped; its storage never moves.
pub struct Pinned<T> {
    v: Vec<T>,
    off: usize,
    len: usize,
    guard: Option<Guard>,
}

impl<T: Copy + Default> Pinned<T> {
    /// None if the memory cannot be allocated; the elements are `fill`
    pub fn new(len: usize, fill: T, attach_gpu: bool) -> Option<Pinned<T>> {
        let sz = std::mem::size_of::<T>().max(1);
        let slack = 2 * PAGE / sz;          // to start on a page and to end on one
        let mut v = Vec::new();
        v.try_reserve_exact(len + slack).ok()?;
        v.resize(len + slack, fill);
        let addr = v.as_ptr() as usize;
        let off = (addr.next_multiple_of(PAGE) - addr) / sz;
        let base = addr + off * sz;
        let bytes = (len * sz).next_multiple_of(PAGE).max(PAGE);
        debug_assert!(off * sz + bytes <= v.len() * sz);
        let guard = (attach_gpu && available() && attach(base, bytes)).then_some(Guard(base));
        Some(Pinned { v, off, len, guard })
    }
}

impl<T> Pinned<T> {
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    /// whether the GPU can read and write it
    pub fn attached(&self) -> bool {
        self.guard.is_some()
    }
    pub fn as_slice(&self) -> &[T] {
        &self.v[self.off..self.off + self.len]
    }
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.v[self.off..self.off + self.len]
    }
}

impl<T> Default for Pinned<T> {
    fn default() -> Pinned<T> {
        Pinned { v: Vec::new(), off: 0, len: 0, guard: None }
    }
}

impl<T> Drop for Pinned<T> {
    fn drop(&mut self) {
        self.guard.take();          // detach before the storage is freed
    }
}

static PRODUCTS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// the number of products the GPU has computed in this process (a diagnostic: a plan with the
/// GPU whose products were all refused computes the same result on the CPU alone)
pub fn products_done() -> usize {
    PRODUCTS.load(std::sync::atomic::Ordering::Relaxed)
}

/// C[i] = A[i] B[i] (t.m x t.k by t.k x t.n, leading dimensions lda, ldb, ldc) on the GPU for every
/// item, in one command buffer, waited for; false if it was not done (no GPU, more than 64 items,
/// or a block outside the wrapped regions), in which case nothing was written
pub fn sgemm_batch(t: Shape, items: &mut [(&[f32], &[f32], &mut [f32])], lda: usize, ldb: usize, ldc: usize) -> bool {
    use crate::sys::extent;
    if items.is_empty() || items.len() > 64 || !available() || lda < t.k || ldb < t.n || ldc < t.n {
        return false;
    }
    for (a, b, c) in items.iter() {
        assert!(a.len() >= extent(t.m, t.k, lda) && b.len() >= extent(t.k, t.n, ldb) && c.len() >= extent(t.m, t.n, ldc),
                "fmm: a GPU product's slices are too short");
    }
    #[cfg(feature = "gpu")]
    {
        let pa: Vec<*const f32> = items.iter().map(|x| x.0.as_ptr()).collect();
        let pb: Vec<*const f32> = items.iter().map(|x| x.1.as_ptr()).collect();
        let pc: Vec<*mut f32> = items.iter_mut().map(|x| x.2.as_mut_ptr()).collect();
        // SAFETY: each block is a slice holding its matrix's extent (checked), the C blocks are
        // exclusively borrowed and pairwise disjoint (distinct &mut), the call waits for the GPU
        // to finish; MPS reads t.m rows of t.k (t.k rows of t.n) and writes t.m rows of t.n
        // elements at the leading dimensions given, all inside those extents
        let rc = unsafe {
            ffi::fmm_gpu_sgemm_batch(t.m, t.k, t.n, items.len() as std::os::raw::c_int, pa.as_ptr(), lda, pb.as_ptr(), ldb,
                                     pc.as_ptr(), ldc)
        };
        if rc == 0 {
            PRODUCTS.fetch_add(items.len(), std::sync::atomic::Ordering::Relaxed);
        }
        rc == 0
    }
    #[cfg(not(feature = "gpu"))]
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pinned_starts_on_a_page() {
        let mut p = Pinned::<f32>::new(10_000, 1.0, true).unwrap();
        assert_eq!(p.as_slice().as_ptr() as usize % PAGE, 0);
        assert_eq!(p.len(), 10_000);
        assert!(p.as_mut_slice().iter().all(|x| *x == 1.0));
        assert_eq!(p.attached(), available());
    }

    #[test]
    fn a_batch_matches_accelerate_bit_for_bit() {
        if !available() {
            return;
        }
        let t = Shape::new(576, 640, 704);
        let mut rng = 0x2545f4914f6cdd1du64;
        let mut fill = |p: &mut Pinned<f32>| {
            for x in p.as_mut_slice() {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                *x = ((rng >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0) as f32;
            }
        };
        let (mut a, mut b) = (Pinned::new(2 * t.m * t.k, 0.0, true).unwrap(), Pinned::new(t.k * t.n, 0.0, true).unwrap());
        fill(&mut a);
        fill(&mut b);
        let mut c = Pinned::new(2 * t.m * t.n, 0.0f32, true).unwrap();
        let mut r = vec![0.0f32; t.m * t.n];
        {
            let (a, b) = (a.as_slice(), b.as_slice());
            let (c0, c1) = c.as_mut_slice().split_at_mut(t.m * t.n);
            let mut items = [(&a[..t.m * t.k], b, c0), (&a[t.m * t.k..], b, c1)];
            assert!(sgemm_batch(t, &mut items, t.k, t.n, t.n));
        }
        for i in 0..2 {
            crate::sys::sgemm(t, &a.as_slice()[i * t.m * t.k..], t.k, b.as_slice(), t.n, 0.0, &mut r, t.n);
            let ci = &c.as_slice()[i * t.m * t.n..(i + 1) * t.m * t.n];
            assert!(ci.iter().zip(&r).all(|(x, y)| x.to_bits() == y.to_bits()), "product {i} differs from Accelerate's");
        }
        // a block outside every wrapped region is refused, and nothing is written
        let outside = vec![0.5f32; t.m * t.k];
        let mut cc = vec![7.0f32; t.m * t.n];
        let mut items = [(&outside[..], b.as_slice(), &mut cc[..])];
        assert!(!sgemm_batch(t, &mut items, t.k, t.n, t.n));
        assert!(cc.iter().all(|x| *x == 7.0));
    }

    /// plans with the GPU's leaves compute what the same plans compute on the CPU, bit for bit:
    /// a shared leaf, a pipeline over one, and the classical product in strips (against the GEMM)
    #[test]
    fn plans_with_the_gpu_match_the_cpu_bit_for_bit() {
        use crate::exec::exec;
        use crate::plan::Plan;
        let n = 1728;
        let s = Shape::sq(n);
        let mut rng = 0x9e3779b97f4a7c15u64;
        let mut a = Pinned::new(n * n, 0.0f32, true).unwrap();
        let mut b = Pinned::new(n * n, 0.0f32, true).unwrap();
        for x in a.as_mut_slice().iter_mut().chain(b.as_mut_slice().iter_mut()) {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            *x = ((rng >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0) as f32;
        }
        let run = |p: &str| -> Vec<f32> {
            let plan = Plan::parse(p).unwrap();
            let mut w = Pinned::new(plan.work(s).max(1), 0.0f32, true).unwrap();
            let mut c = Pinned::new(n * n, 0.0f32, true).unwrap();
            exec(&plan.0, s, a.as_slice(), n, b.as_slice(), n, c.as_mut_slice(), n, w.as_mut_slice());
            c.as_slice().to_vec()
        };
        for (gpu, cpu) in [("R363/G6M", "R363/G6"), ("R363/GM", "R363/G"), ("R363+4/R336/G6M", "R363/R336/G6"), ("K32/G6M", "G"),
                           ("K64/GM", "G")] {
            let before = products_done();
            let x = run(gpu);
            assert!(products_done() > before, "{gpu}: the GPU computed no product");
            let y = run(cpu);
            let differ = x.iter().zip(&y).filter(|(p, q)| p.to_bits() != q.to_bits()).count();
            assert_eq!(differ, 0, "{gpu} against {cpu}");
        }
    }
}
