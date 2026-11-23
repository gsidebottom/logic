//! fmm: fast matrix multiplication on Apple silicon.
//!
//! `sgemm` / `dgemm` compute C = A B for n x n row-major matrices with leading dimensions (in
//! elements), `sgemm_mkn` / `dgemm_mkn` for an m x k matrix A and a k x n matrix B, by the plan
//! a calibrated cost model picks for this machine, shape and precision: fused levels of the
//! rank-48 <4x4x4:48> scheme of Dumas, Pernet and Sedoglavic (their 262-operation accurate
//! program), of their accurate <3x3x6:40> scheme in its three orientations (rectangular levels, so
//! a plan tracks the shape of every level's products) and of a <2x2x2:7> level (DPS's most
//! accurate point, in Q(sqrt 3), of ISSAC 2024, or Strassen-Winograd) over Accelerate's
//! GEMM, with GEMM streams and pipelined passes; `max_growth` is the error budget (0: the default
//! of 1, a plan predicted no less accurate than the GEMM; positive: that budget; negative: none,
//! the fastest plan) on the plan's predicted error growth
//! over the classical GEMM's.  A port of the C library in matmul/fastmm (fmm.h): the same planner
//! and calibration cache file, so both pick the same plans.  With the feature `gpu`, in f32, a
//! level's products are shared between the GEMM streams and the GPU, as in the C library's GPU
//! build (libfmm_gpu.a): its plans, the GPU's calibration file beside the cache, and results bit
//! for bit the same, since the GPU's product is Accelerate's (FMM_GPU=0 plans without it).
//!
//! The plans come from the calibration cache (FMM_CALIB_DIR, default ~/Library/Caches/fmm);
//! square sizes between calibrated ones are interpolated, rectangular shapes must have been
//! calibrated (`calibrate_mkn`) or pad to a calibrated shape, and a problem is padded when that
//! pays; without a calibration covering it the classical GEMM runs, so results are always correct.
//! `calibrate` measures what the planner needs, once per machine (minutes).  Calls are serialized
//! (each uses the whole machine); the workspace is kept between calls until `release`.
//!
//! Unsafe code: only the FFI declarations in `sys` (Accelerate's GEMM and threading switch,
//! the threads' scheduling class) and the passes' two DC ZVA instructions there, and in `gpu`
//! (the GPU's leaf, gpu_leaf.m), behind safe wrappers.
#![deny(unsafe_code)]

pub mod calib;
pub mod exec;
pub mod gpu;
pub mod kernels;
pub mod measure;
pub mod plan;
pub mod planner;
pub mod sys;

pub use exec::Real;
pub use plan::{Plan, Shape};

use calib::Calib;
use std::sync::{Mutex, OnceLock};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// a leading dimension below a matrix's columns, or a slice too short for its matrix
    Shape(&'static str),
    /// the workspace could not be allocated
    Workspace,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Shape(s) => write!(f, "fmm: {s}"),
            Error::Workspace => write!(f, "fmm: cannot allocate the workspace"),
        }
    }
}

impl std::error::Error for Error {}

/// the plan a call runs: the plan, the shape it runs at (the problem's, or padded), its predicted
/// time and error (None without a calibration)
#[derive(Debug, Clone)]
pub struct PlanInfo {
    pub plan: Plan,
    pub spad: Shape,
    pub predicted: Option<f64>,
    pub predicted_error: Option<f64>,
}

impl PlanInfo {
    /// the size the plan runs at, for a square problem (the padded shape's)
    pub fn npad(&self) -> usize {
        self.spad.m
    }
    /// whether the problem is padded
    pub fn padded(&self, s: Shape) -> bool {
        self.spad != s
    }
}

struct State {
    cal: [Option<Calib>; 2],
    /// (shape, f64, budget, nok) -> plan
    plans: Vec<(Shape, bool, u64, bool, PlanInfo)>,
    /// the workspaces, starting on a page and, with the GPU, wrapped for it
    ws32: Option<gpu::Pinned<f32>>,
    ws64: Option<gpu::Pinned<f64>>,
}

static STATE: Mutex<State> = Mutex::new(State { cal: [None, None], plans: Vec::new(), ws32: None, ws64: None });

/// the library's threads: one per core, at user-interactive priority (as the C library's GCD work)
pub(crate) fn pool() -> &'static rayon::ThreadPool {
    static POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    POOL.get_or_init(|| {
        let n = std::env::var("FMM_THREADS").ok().and_then(|v| v.trim().parse::<usize>().ok()).filter(|&n| n > 0)
            .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8));
        rayon::ThreadPoolBuilder::new()
            .num_threads(n)
            .thread_name(|i| format!("fmm-{i}"))
            .start_handler(|_| sys::set_qos_user_interactive())
            .build()
            .expect("fmm: thread pool")
    })
}

fn calib_of(st: &mut State, f64: bool) -> &Calib {
    st.cal[f64 as usize].get_or_insert_with(|| calib::load(f64))
}

/// the plan for (shape, precision, budget); nok: without a K level (the caller's matrices cannot be
/// wrapped for the GPU)
fn plan_of(st: &mut State, s: Shape, f64: bool, gmax: f64, nok: bool) -> PlanInfo {
    if let Some((.., p)) = st.plans.iter().find(|(sh, f, g, k, _)| *sh == s && *f == f64 && *g == gmax.to_bits() && *k == nok) {
        return p.clone();
    }
    let c = calib_of(st, f64);
    let v = planner::View { nok, ..planner::View::of(c) };
    let info = match planner::best_padded_with(v, s, gmax, f64) {
        Some((plan, spad, t)) => {
            let err = c.err_model().map(|e| planner::predicted_error(&e, &plan, spad));
            PlanInfo { plan, spad, predicted: Some(t), predicted_error: err }
        }
        None => PlanInfo { plan: Plan::classical(), spad: s, predicted: None, predicted_error: None },
    };
    if st.plans.len() >= 64 {
        st.plans.remove(0);
    }
    st.plans.push((s, f64, gmax.to_bits(), nok, info.clone()));
    info
}

fn check(s: Shape, la: usize, lda: usize, lb: usize, ldb: usize, lc: usize, ldc: usize) -> Result<(), Error> {
    if lda < s.k || ldb < s.n || ldc < s.n {
        return Err(Error::Shape("a leading dimension is below its matrix's columns"));
    }
    if la < sys::extent(s.m, s.k, lda) || lb < sys::extent(s.k, s.n, ldb) || lc < sys::extent(s.m, s.n, ldc) {
        return Err(Error::Shape("a slice is too short for its matrix"));
    }
    Ok(())
}

fn gemm_with<T: Real>(s: Shape, a: &[T], lda: usize, b: &[T], ldb: usize, c: &mut [T], ldc: usize, gmax: f64,
                      ws: fn(&mut State) -> &mut Option<gpu::Pinned<T>>) -> Result<(), Error> {
    if s.m == 0 || s.n == 0 {               // an empty product: nothing to read or write (as the C library)
        return Ok(());
    }
    check(s, a.len(), lda, b.len(), ldb, c.len(), ldc)?;
    if s.k == 0 {                           // an empty sum: C = 0
        for row in c.chunks_mut(ldc).take(s.m) {
            row[..s.n].fill(T::default());
        }
        return Ok(());
    }
    let mut st = STATE.lock().unwrap_or_else(|e| e.into_inner());
    let gpu = calib_of(&mut st, T::F64).gpu;
    let mut info = plan_of(&mut st, s, T::F64, gmax, false);
    // a K level's products are strips of A, B and C themselves: the GPU needs them wrapped, which
    // takes matrices starting on a page; otherwise the best plan without a K level runs
    let ext = [sys::extent(s.m, s.k, lda), sys::extent(s.k, s.n, ldb), sys::extent(s.m, s.n, ldc)];
    let k_plan = info.plan.0[0].level.is_split() && info.spad == s;
    if k_plan && gpu::with_attached(a, b, &mut *c, ext, |_, _, _| ()).is_none() {
        info = plan_of(&mut st, s, T::F64, gmax, true);
    }
    let need = exec::padded_work(&info.plan, s, info.spad);
    let w = ws(&mut st);
    if w.as_ref().is_none_or(|w| w.len() < need) {
        *w = None;                          // the old one released (and detached) first
        *w = Some(gpu::Pinned::new(need, T::default(), gpu).ok_or(Error::Workspace)?);
    }
    let work = &mut w.as_mut().unwrap().as_mut_slice()[..need];
    if info.plan.0[0].level.is_leaf() && info.spad == s {
        // classical: Accelerate's own threading from the calling thread, as the C library
        exec::exec(&info.plan.0, s, a, lda, b, ldb, c, ldc, work);
    } else if info.plan.0[0].level.is_split() && info.spad == s {
        let run = |a: &[T], b: &[T], c: &mut [T]| pool().install(|| exec::exec(&info.plan.0, s, a, lda, b, ldb, c, ldc, work));
        if gpu::with_attached(a, b, &mut *c, ext, run).is_none() {
            return Err(Error::Workspace);   // wrapped a moment ago: the GPU's region table is full
        }
    } else {
        pool().install(|| exec::exec_padded(&info.plan.0, s, info.spad, a, lda, b, ldb, c, ldc, work));
    }
    Ok(())
}

/// C = A B for n x n row-major f32 matrices; max_growth is the error budget (0 the default of 1,
/// positive that budget, negative none) on the plan's predicted error growth over the
/// classical GEMM's
pub fn sgemm(n: usize, a: &[f32], lda: usize, b: &[f32], ldb: usize, c: &mut [f32], ldc: usize, max_growth: f64)
             -> Result<(), Error> {
    gemm_with(Shape::sq(n), a, lda, b, ldb, c, ldc, max_growth, |s| &mut s.ws32)
}

/// C = A B for n x n row-major f64 matrices
pub fn dgemm(n: usize, a: &[f64], lda: usize, b: &[f64], ldb: usize, c: &mut [f64], ldc: usize, max_growth: f64)
             -> Result<(), Error> {
    gemm_with(Shape::sq(n), a, lda, b, ldb, c, ldc, max_growth, |s| &mut s.ws64)
}

/// C = A B for an m x k matrix A and a k x n matrix B, row-major f32 (C is m x n)
pub fn sgemm_mkn(m: usize, k: usize, n: usize, a: &[f32], lda: usize, b: &[f32], ldb: usize, c: &mut [f32], ldc: usize,
                 max_growth: f64) -> Result<(), Error> {
    gemm_with(Shape::new(m, k, n), a, lda, b, ldb, c, ldc, max_growth, |s| &mut s.ws32)
}

/// C = A B for an m x k matrix A and a k x n matrix B, row-major f64
pub fn dgemm_mkn(m: usize, k: usize, n: usize, a: &[f64], lda: usize, b: &[f64], ldb: usize, c: &mut [f64], ldc: usize,
                 max_growth: f64) -> Result<(), Error> {
    gemm_with(Shape::new(m, k, n), a, lda, b, ldb, c, ldc, max_growth, |s| &mut s.ws64)
}

/// the plan sgemm (f64 false) or dgemm (true) runs for n
pub fn plan(n: usize, f64: bool, max_growth: f64) -> PlanInfo {
    plan_mkn(n, n, n, f64, max_growth)
}

/// the plan sgemm_mkn or dgemm_mkn runs for the shape (m, k, n)
pub fn plan_mkn(m: usize, k: usize, n: usize, f64: bool, max_growth: f64) -> PlanInfo {
    let mut st = STATE.lock().unwrap_or_else(|e| e.into_inner());
    plan_of(&mut st, Shape::new(m, k, n), f64, max_growth, false)
}

/// measure the calibration the planner needs for sizes up to n in one precision and add it to
/// the cache; returns the number of entries measured
pub fn calibrate(n: usize, f64: bool) -> usize {
    calibrate_mkn(n, n, n, f64)
}

/// measure the calibration the planner needs for the shape (m, k, n) in one precision
pub fn calibrate_mkn(m: usize, k: usize, n: usize, f64: bool) -> usize {
    fn run<T: Real>(s: Shape, c: &mut Calib) -> usize {
        // with the GPU the matrices are wrapped for it (a K level's products are their strips)
        let mut a = gpu::Pinned::new(s.m * s.k, T::default(), c.gpu).expect("fmm: calibration matrices");
        let mut b = gpu::Pinned::new(s.k * s.n, T::default(), c.gpu).expect("fmm: calibration matrices");
        let mut cm = gpu::Pinned::new(s.m * s.n, T::from_f64(1.0), c.gpu).expect("fmm: calibration matrices");
        a.as_mut_slice().iter_mut().enumerate().for_each(|(i, x)| *x = T::from_f64(1.0 / (1 + i % 7) as f64));
        b.as_mut_slice().iter_mut().enumerate().for_each(|(i, x)| *x = T::from_f64(1.0 / (1 + i % 5) as f64));
        measure::calibrate(c, s, a.as_slice(), b.as_slice(), cm.as_mut_slice())
    }
    let s = Shape::new(m, k, n);
    let mut st = STATE.lock().unwrap_or_else(|e| e.into_inner());
    let mut c = calib_of(&mut st, f64).clone();
    let cnt = if f64 { run::<f64>(s, &mut c) } else { run::<f32>(s, &mut c) };
    st.cal[f64 as usize] = Some(c);
    st.plans.clear();
    cnt
}

/// run f on the library's threads (passes and streams started inside use them)
pub fn in_pool<R: Send>(f: impl FnOnce() -> R + Send) -> R {
    pool().install(f)
}

/// free the workspace and the cached calibration and plans
pub fn release() {
    let mut st = STATE.lock().unwrap_or_else(|e| e.into_inner());
    st.cal = [None, None];
    st.plans.clear();
    st.ws32 = None;
    st.ws64 = None;
}
