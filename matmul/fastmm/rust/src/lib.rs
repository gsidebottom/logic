//! fmm: fast matrix multiplication on Apple silicon.
//!
//! `sgemm` / `dgemm` compute C = A B for n x n row-major matrices with leading dimensions (in
//! elements) by the plan a calibrated cost model picks for this machine, size and precision:
//! fused levels of the rank-48 <4x4x4:48> scheme of Dumas, Pernet and Sedoglavic (its accurate
//! program) and of Strassen-Winograd over Accelerate's GEMM, with GEMM streams and pipelined
//! passes; `max_growth > 0` limits the plan's error growth over the classical GEMM's.  A port of
//! the C library in matmul/fastmm (fmm.h): the same planner and calibration cache file, so both
//! pick the same plans.
//!
//! The plans come from the calibration cache (FMM_CALIB_DIR, default ~/Library/Caches/fmm);
//! sizes between calibrated ones are interpolated and padded when that pays; without a
//! calibration covering n the classical GEMM runs, so results are always correct.  `calibrate`
//! measures what the planner needs, once per machine (minutes).  Calls are serialized (each uses
//! the whole machine); the workspace is kept between calls until `release`.
//!
//! Unsafe code: only the FFI declarations in `sys` (Accelerate's GEMM and threading switch,
//! the threads' scheduling class), behind safe wrappers.
#![deny(unsafe_code)]

pub mod calib;
pub mod exec;
pub mod kernels;
pub mod measure;
pub mod plan;
pub mod planner;
pub mod sys;

pub use exec::Real;
pub use plan::Plan;

use calib::Calib;
use std::sync::{Mutex, OnceLock};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// a leading dimension below n, or a slice too short for its matrix
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

/// the plan a call runs: the plan, the size it runs at (n, or padded), its predicted time and
/// error (None without a calibration)
#[derive(Debug, Clone)]
pub struct PlanInfo {
    pub plan: Plan,
    pub npad: usize,
    pub predicted: Option<f64>,
    pub predicted_error: Option<f64>,
}

struct State {
    cal: [Option<Calib>; 2],
    plans: Vec<(usize, bool, u64, PlanInfo)>,
    ws32: Vec<f32>,
    ws64: Vec<f64>,
}

static STATE: Mutex<State> = Mutex::new(State { cal: [None, None], plans: Vec::new(), ws32: Vec::new(), ws64: Vec::new() });

/// the library's threads: one per core, at user-interactive priority (as the C library's GCD work)
pub(crate) fn pool() -> &'static rayon::ThreadPool {
    static POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    POOL.get_or_init(|| {
        let n = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8);
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

fn plan_of(st: &mut State, n: usize, f64: bool, gmax: f64) -> PlanInfo {
    if let Some((_, _, _, p)) = st.plans.iter().find(|(m, f, g, _)| *m == n && *f == f64 && *g == gmax.to_bits()) {
        return p.clone();
    }
    let c = calib_of(st, f64);
    let info = match planner::best_padded(c, n, gmax, f64) {
        Some((plan, npad, t)) => {
            let err = c.err_model().map(|e| planner::predicted_error(&e, &plan, npad));
            PlanInfo { plan, npad, predicted: Some(t), predicted_error: err }
        }
        None => PlanInfo { plan: Plan::classical(), npad: n, predicted: None, predicted_error: None },
    };
    if st.plans.len() >= 64 {
        st.plans.remove(0);
    }
    st.plans.push((n, f64, gmax.to_bits(), info.clone()));
    info
}

fn check(n: usize, la: usize, lda: usize, lb: usize, ldb: usize, lc: usize, ldc: usize) -> Result<(), Error> {
    if lda < n || ldb < n || ldc < n {
        return Err(Error::Shape("a leading dimension is below n"));
    }
    if la < sys::extent(n, lda) || lb < sys::extent(n, ldb) || lc < sys::extent(n, ldc) {
        return Err(Error::Shape("a slice is too short for its matrix"));
    }
    Ok(())
}

fn gemm_with<T: Real>(n: usize, a: &[T], lda: usize, b: &[T], ldb: usize, c: &mut [T], ldc: usize, gmax: f64,
                      ws: fn(&mut State) -> &mut Vec<T>) -> Result<(), Error> {
    check(n, a.len(), lda, b.len(), ldb, c.len(), ldc)?;
    if n == 0 {
        return Ok(());
    }
    let mut st = STATE.lock().unwrap_or_else(|e| e.into_inner());
    let info = plan_of(&mut st, n, T::F64, gmax);
    let need = exec::padded_work(&info.plan, n, info.npad);
    let w = ws(&mut st);
    if w.len() < need {
        w.clear();
        w.shrink_to_fit();
        w.try_reserve_exact(need).map_err(|_| Error::Workspace)?;
        w.resize(need, T::default());
    }
    let work = &mut w[..need];
    if info.plan.0[0].level.is_leaf() && info.npad == n {
        // classical: Accelerate's own threading from the calling thread, as the C library
        exec::exec(&info.plan.0, n, a, lda, b, ldb, c, ldc, work);
    } else {
        pool().install(|| exec::exec_padded(&info.plan.0, n, info.npad, a, lda, b, ldb, c, ldc, work));
    }
    Ok(())
}

/// C = A B for n x n row-major f32 matrices; max_growth > 0 bounds the error growth over the
/// classical GEMM (0: the fastest plan)
pub fn sgemm(n: usize, a: &[f32], lda: usize, b: &[f32], ldb: usize, c: &mut [f32], ldc: usize, max_growth: f64)
             -> Result<(), Error> {
    gemm_with(n, a, lda, b, ldb, c, ldc, max_growth, |s| &mut s.ws32)
}

/// C = A B for n x n row-major f64 matrices
pub fn dgemm(n: usize, a: &[f64], lda: usize, b: &[f64], ldb: usize, c: &mut [f64], ldc: usize, max_growth: f64)
             -> Result<(), Error> {
    gemm_with(n, a, lda, b, ldb, c, ldc, max_growth, |s| &mut s.ws64)
}

/// the plan sgemm (f64 false) or dgemm (true) runs for n
pub fn plan(n: usize, f64: bool, max_growth: f64) -> PlanInfo {
    let mut st = STATE.lock().unwrap_or_else(|e| e.into_inner());
    plan_of(&mut st, n, f64, max_growth)
}

/// measure the calibration the planner needs for sizes up to n in one precision and add it to
/// the cache; returns the number of entries measured
pub fn calibrate(n: usize, f64: bool) -> usize {
    fn run<T: Real>(n: usize, c: &mut Calib) -> usize {
        let nn = n * n;
        let a: Vec<T> = (0..nn).map(|i| T::from_f64(1.0 / (1 + i % 7) as f64)).collect();
        let b: Vec<T> = (0..nn).map(|i| T::from_f64(1.0 / (1 + i % 5) as f64)).collect();
        let mut cm = measure::mapped::<T>(nn);
        measure::calibrate(c, n, &a, &b, &mut cm)
    }
    let mut st = STATE.lock().unwrap_or_else(|e| e.into_inner());
    let mut c = calib_of(&mut st, f64).clone();
    let cnt = if f64 { run::<f64>(n, &mut c) } else { run::<f32>(n, &mut c) };
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
    st.ws32 = Vec::new();
    st.ws64 = Vec::new();
}
