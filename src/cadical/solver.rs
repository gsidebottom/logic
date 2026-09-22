//! CaDiCaL as a library — the reference CDCL solver this crate measures
//! itself against, and the engine behind `sat --backend cadical` and the
//! web UI's learned-clause panel.
//!
//! The source is vendored at `vendor/cadical-3.0.1/` and built by
//! `/build.rs`; `shim.cpp` next to this file is the C ABI in between.
//!
//! **Why vendored.**  Until 2026-09-17 this was the `cadical` crate, whose
//! last release (0.1.16) bundles CaDiCaL **1.9.5** — while every certified
//! path in `tools/` shells out to the `cadical` on `PATH`, which here is
//! 3.0.0.  The two are not close: 170 s versus 19 s on
//! `toughsat_factoring_895s`.  So "faster than CaDiCaL" meant one thing in
//! `doc/box_candidates_satcomp.md` and another in the certification logs,
//! and neither said which.  One vendored solver, one number.
//!
//! The API is deliberately the crate's, so the call sites did not change:
//! [`Solver`] parameterized by a [`Callbacks`] implementation, `solve`
//! returning `Option<bool>` with `None` for "terminated without an answer".
//! What changed is `value`'s `Option`: CaDiCaL 3 gives
//! declared-but-unused variables a default value, so a model covers every
//! variable in range, and `value` answers `None` only outside a satisfied
//! state.  `reserve` is still here, but backed by 3.0.1's
//! `declare_more_variables` rather than the `reserve` it renamed to
//! `resize` — see [`Solver::reserve`], which is a correctness requirement
//! and not just an optimization now.

use std::ffi::{CStr, CString, c_char, c_int, c_void};
use std::panic::AssertUnwindSafe;
use std::time::{Duration, Instant};

type TerminateFn = extern "C" fn(*mut c_void) -> c_int;
type LearnFn = extern "C" fn(*mut c_void, *const c_int, usize);

unsafe extern "C" {
    fn c3_new() -> *mut c_void;
    fn c3_delete(s: *mut c_void);
    fn c3_signature() -> *const c_char;
    fn c3_add_clause(s: *mut c_void, lits: *const c_int, len: usize);
    fn c3_solve(s: *mut c_void) -> c_int;
    fn c3_status(s: *mut c_void) -> c_int;
    fn c3_val(s: *mut c_void, lit: c_int) -> c_int;
    fn c3_max_var(s: *mut c_void) -> c_int;
    fn c3_conflicts(s: *mut c_void) -> i64;
    fn c3_decisions(s: *mut c_void) -> i64;
    fn c3_propagations(s: *mut c_void) -> i64;
    fn c3_declare_vars(s: *mut c_void, n: c_int) -> c_int;
    fn c3_set_option(s: *mut c_void, name: *const c_char, val: c_int) -> c_int;
    fn c3_connect(
        s: *mut c_void,
        data: *mut c_void,
        terminate: Option<TerminateFn>,
        learn: Option<LearnFn>,
        max_length: c_int,
    );
    fn c3_disconnect(s: *mut c_void);
}

/// The two options release **3.0.0** had on and 3.0.1 ships off.
///
/// A release's defaults are part of its identity, and these two are worth
/// 1.73× by geomean over this repo's benchmark set — measured both ways
/// (`doc/data/cadical_vendored_options_2026-09-18.txt`): 3.0.1 with them on
/// matches 3.0.0's default times, and 3.0.0 with them off matches 3.0.1's.
/// On `php9_8` it is 0.01 s against 0.22 s.
///
/// Nothing applies them: `sat -b cadical` runs the vendored release's own
/// defaults, because 3.0.1 *with* them on is slower than 3.0.1 without on
/// four of the six instances measured — 3.0.0 is faster than both, but not
/// for a reason either configuration of 3.0.1 reproduces.  They are named
/// here because every "vs CaDiCaL" number in `doc/` predates the vendoring
/// and was taken against a solver that had them on, and
/// `sat -b cadical --cadical-opt factor=1 --cadical-opt preprocesslight=1`
/// is how to ask for that configuration.
pub const RELEASE_3_0_0_DEFAULTS: [(&str, i32); 2] = [("factor", 1), ("preprocesslight", 1)];

/// CaDiCaL's build identification, e.g. `3.0.1 <sha> <date> <compiler>`.
pub fn signature() -> &'static str {
    // Static storage in the library; valid for the process.
    unsafe { CStr::from_ptr(c3_signature()) }.to_str().unwrap_or("unknown")
}

// ─── Callbacks ───────────────────────────────────────────────────────────────

/// Hooks CaDiCaL offers during the search.
///
/// Both are polled from inside `solve`, on the solver's own thread.  A
/// panic in either is caught at the ABI boundary (unwinding into C++ is
/// undefined) and turned into a termination request.
pub trait Callbacks {
    /// Called at the start of each `solve`, before any search.
    fn started(&mut self) {}

    /// Polled regularly; `true` abandons the search, and `solve` answers
    /// `None`.
    fn terminate(&mut self) -> bool {
        false
    }

    /// Longest learned clause to export through [`Callbacks::learn`].
    ///
    /// **Zero or less disconnects the learner entirely**, which is the
    /// point: CaDiCaL skips its export path when no learner is connected,
    /// so a caller that only wants `terminate` pays nothing per conflict.
    fn max_length(&self) -> i32 {
        0
    }

    /// Each learned clause no longer than [`Callbacks::max_length`].
    fn learn(&mut self, clause: &[i32]) {
        let _ = clause;
    }
}

/// Stop after a wall-clock budget, measured from the start of `solve`.
pub struct Timeout {
    pub budget: Duration,
    started: Instant,
}

impl Timeout {
    pub fn new(seconds: f32) -> Timeout {
        Timeout { budget: Duration::from_secs_f32(seconds.max(0.0)), started: Instant::now() }
    }
}

impl Callbacks for Timeout {
    fn started(&mut self) {
        self.started = Instant::now();
    }

    fn terminate(&mut self) -> bool {
        self.started.elapsed() >= self.budget
    }
}

extern "C" fn terminate_trampoline<C: Callbacks>(data: *mut c_void) -> c_int {
    let cbs = unsafe { &mut *(data as *mut C) };
    match std::panic::catch_unwind(AssertUnwindSafe(|| cbs.terminate())) {
        Ok(stop) => c_int::from(stop),
        Err(_) => 1, // do not unwind into C++; give up instead
    }
}

extern "C" fn learn_trampoline<C: Callbacks>(data: *mut c_void, lits: *const c_int, len: usize) {
    let cbs = unsafe { &mut *(data as *mut C) };
    // An empty `std::vector`'s `data()` may be null, which `from_raw_parts`
    // does not accept.
    let clause: &[i32] = if len == 0 { &[] } else { unsafe { std::slice::from_raw_parts(lits, len) } };
    let _ = std::panic::catch_unwind(AssertUnwindSafe(|| cbs.learn(clause)));
}

// ─── Solver ──────────────────────────────────────────────────────────────────

/// A CaDiCaL instance.  Incremental: clauses may be added after a solve,
/// and the next solve continues from what was learned.
pub struct Solver<C: Callbacks = Timeout> {
    ptr: *mut c_void,
    /// Boxed for a stable address to hand the trampolines.
    cbs: Option<Box<C>>,
    /// Still in CaDiCaL's `CONFIGURING` state — options may be set.
    configuring: bool,
    /// Reused by `add_clause`, so a clause per call is not an allocation
    /// per call.
    buf: Vec<c_int>,
}

// Each instance owns its own solver; CaDiCaL keeps no shared mutable state
// unless its signal handlers are connected, which this shim never does.
unsafe impl<C: Callbacks + Send> Send for Solver<C> {}

impl<C: Callbacks> Default for Solver<C> {
    fn default() -> Solver<C> {
        Solver::new()
    }
}

impl<C: Callbacks> Solver<C> {
    pub fn new() -> Solver<C> {
        let ptr = unsafe { c3_new() };
        assert!(!ptr.is_null(), "CaDiCaL allocation failed");
        Solver { ptr, cbs: None, configuring: true, buf: Vec::new() }
    }

    /// CaDiCaL's build identification — see [`signature`].
    pub fn signature() -> &'static str {
        signature()
    }

    /// Connect callbacks, or disconnect them with `None`.
    pub fn set_callbacks(&mut self, cbs: Option<C>) {
        match cbs {
            None => {
                unsafe { c3_disconnect(self.ptr) };
                self.cbs = None;
            }
            Some(cbs) => {
                let max_length = cbs.max_length();
                let mut boxed = Box::new(cbs);
                let data = (&raw mut *boxed).cast::<c_void>();
                self.cbs = Some(boxed); // the box moves; the pointee does not
                unsafe {
                    c3_connect(
                        self.ptr,
                        data,
                        Some(terminate_trampoline::<C>),
                        (max_length > 0).then_some(learn_trampoline::<C> as LearnFn),
                        max_length,
                    )
                };
            }
        }
    }

    pub fn get_callbacks(&self) -> Option<&C> {
        self.cbs.as_deref()
    }

    pub fn get_callbacks_mut(&mut self) -> Option<&mut C> {
        self.cbs.as_deref_mut()
    }

    /// Add one clause.  An empty clause makes the formula unsatisfiable,
    /// as in DIMACS.
    pub fn add_clause<I: IntoIterator<Item = i32>>(&mut self, clause: I) {
        self.buf.clear();
        self.buf.extend(clause);
        self.configuring = false;
        unsafe { c3_add_clause(self.ptr, self.buf.as_ptr(), self.buf.len()) };
    }

    /// Search.  `Some(true)` satisfiable, `Some(false)` unsatisfiable,
    /// `None` terminated by a callback without deciding.
    pub fn solve(&mut self) -> Option<bool> {
        self.configuring = false;
        if let Some(cbs) = self.cbs.as_deref_mut() {
            cbs.started();
        }
        decode(unsafe { c3_solve(self.ptr) })
    }

    /// The last verdict, without searching.
    pub fn status(&self) -> Option<bool> {
        decode(unsafe { c3_status(self.ptr) })
    }

    /// A literal's value in the current model, or `None` if the solver is
    /// not in a satisfied state.
    pub fn value(&self, lit: i32) -> Option<bool> {
        match unsafe { c3_val(self.ptr, lit) } {
            0 => None,
            v => Some(v == lit),
        }
    }

    /// The largest variable index seen so far.
    pub fn max_variable(&self) -> i32 {
        unsafe { c3_max_var(self.ptr) }
    }

    /// Search statistics so far (CaDiCaL's own counters; propagations are
    /// the search's, not preprocessing's).
    pub fn conflicts(&self) -> i64 { unsafe { c3_conflicts(self.ptr) } }
    pub fn decisions(&self) -> i64 { unsafe { c3_decisions(self.ptr) } }
    pub fn propagations(&self) -> i64 { unsafe { c3_propagations(self.ptr) } }

    /// Declare variables up to `max_var` before adding clauses.
    ///
    /// Not merely an optimization: with `factor` (bounded variable
    /// addition) enabled, CaDiCaL 3.0.1 **aborts the process** on a clause
    /// mentioning a variable that was never declared, because BVA needs to
    /// know which indices are the caller's to keep (`factorcheck`).  The
    /// standalone binary declares them from the `p cnf` header; a caller
    /// going through this API has to say so itself.
    ///
    /// CaDiCaL leaves its configuring state here, so
    /// [`Solver::set_option`] must come first — and afterwards answers
    /// `false` rather than letting CaDiCaL abort.
    pub fn reserve(&mut self, max_var: i32) {
        let have = unsafe { c3_max_var(self.ptr) };
        if max_var > have {
            self.configuring = false;
            unsafe { c3_declare_vars(self.ptr, max_var - have) };
        }
    }

    /// Set a CaDiCaL option (`"restart"`, `"chrono"`, …), as
    /// `cadical --help` lists them.
    ///
    /// Answers `false` for an unknown option, and — since CaDiCaL only
    /// accepts most options before the first clause — for any call after
    /// one, rather than letting it abort the process.
    pub fn set_option(&mut self, name: &str, value: i32) -> bool {
        if !self.configuring {
            return false;
        }
        let Ok(name) = CString::new(name) else { return false };
        unsafe { c3_set_option(self.ptr, name.as_ptr(), value) != 0 }
    }
}

/// CaDiCaL's IPASIR status codes.
fn decode(status: c_int) -> Option<bool> {
    match status {
        10 => Some(true),
        20 => Some(false),
        _ => None,
    }
}

impl<C: Callbacks> Drop for Solver<C> {
    fn drop(&mut self) {
        // Before the callbacks' box does.
        unsafe {
            c3_disconnect(self.ptr);
            c3_delete(self.ptr);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The reason this module exists: a silent downgrade to the 1.9.x that
    /// the `cadical` crate shipped would invalidate every "vs CaDiCaL"
    /// number in `doc/`.  The signature is built from `build.rs`'s
    /// `-DVERSION`, so comparing it with the vendored `VERSION` file also
    /// catches the two drifting apart.
    #[test]
    fn the_vendored_solver_is_cadical_3() {
        let want = include_str!("../../vendor/cadical-3.0.1/VERSION").trim();
        assert!(want.starts_with("3."), "vendored VERSION says {want:?}, expected 3.x");
        let got = signature();
        assert_eq!(got, format!("cadical-{want}"), "the built solver is not the vendored one");
    }

    #[test]
    fn solves_and_reads_back_a_model() {
        let mut solver: Solver = Solver::new();
        solver.add_clause([1, -2]);
        solver.add_clause([2, 3]);
        solver.add_clause([-1, -3]);
        assert_eq!(solver.solve(), Some(true));
        assert_eq!(solver.status(), Some(true));
        let v = |l: i32| solver.value(l).expect("a satisfied solver values every literal");
        assert!(v(1) || !v(2));
        assert!(v(2) || v(3));
        assert!(!v(1) || !v(3));
        // Sign convention: `value(-l) == !value(l)`.
        assert_eq!(solver.value(-1), Some(!v(1)));
        // Declared but unused: answered by default, not refused.
        assert!(solver.value(9).is_some());
    }

    #[test]
    fn refutes_the_pigeonhole_and_the_empty_clause() {
        // 4 pigeons, 3 holes.
        let mut solver: Solver = Solver::new();
        let x = |p: i32, h: i32| p * 3 + h + 1;
        for p in 0..4 {
            solver.add_clause((0..3).map(|h| x(p, h)));
        }
        for h in 0..3 {
            for p in 0..4 {
                for q in p + 1..4 {
                    solver.add_clause([-x(p, h), -x(q, h)]);
                }
            }
        }
        assert_eq!(solver.solve(), Some(false));
        assert_eq!(solver.value(1), None, "no model to read after UNSAT");

        let mut empty: Solver = Solver::new();
        empty.add_clause(std::iter::empty());
        assert_eq!(empty.solve(), Some(false));
    }

    #[test]
    fn a_clause_added_after_a_solve_is_honoured() {
        let mut solver: Solver = Solver::new();
        solver.add_clause([1, 2]);
        assert_eq!(solver.solve(), Some(true));
        solver.add_clause([-1]);
        solver.add_clause([-2]);
        assert_eq!(solver.solve(), Some(false));
    }

    struct Watch {
        stop_at: usize,
        polls: usize,
        learned: Vec<Vec<i32>>,
        max_length: i32,
    }

    impl Callbacks for Watch {
        fn started(&mut self) {
            self.polls = 0;
        }
        fn terminate(&mut self) -> bool {
            self.polls += 1;
            self.polls > self.stop_at
        }
        fn max_length(&self) -> i32 {
            self.max_length
        }
        fn learn(&mut self, clause: &[i32]) {
            self.learned.push(clause.to_vec());
        }
    }

    #[test]
    fn terminate_abandons_the_search() {
        let mut solver: Solver<Watch> = Solver::new();
        solver.set_callbacks(Some(Watch { stop_at: 0, polls: 0, learned: Vec::new(), max_length: 0 }));
        // A hard instance: without the terminator this would not finish.
        let x = |p: i32, h: i32| p * 11 + h + 1;
        for p in 0..12 {
            solver.add_clause((0..11).map(|h| x(p, h)));
        }
        for h in 0..11 {
            for p in 0..12 {
                for q in p + 1..12 {
                    solver.add_clause([-x(p, h), -x(q, h)]);
                }
            }
        }
        assert_eq!(solver.solve(), None, "the terminator should have stopped it");
        assert!(solver.get_callbacks().expect("callbacks").polls > 0);
    }

    #[test]
    fn learned_clauses_reach_the_learner_and_are_implied() {
        let mut solver: Solver<Watch> = Solver::new();
        solver.set_callbacks(Some(Watch {
            stop_at: usize::MAX,
            polls: 0,
            learned: Vec::new(),
            max_length: i32::MAX,
        }));
        let x = |p: i32, h: i32| p * 6 + h + 1;
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        for p in 0..7 {
            clauses.push((0..6).map(|h| x(p, h)).collect());
        }
        for h in 0..6 {
            for p in 0..7 {
                for q in p + 1..7 {
                    clauses.push(vec![-x(p, h), -x(q, h)]);
                }
            }
        }
        for c in &clauses {
            solver.add_clause(c.iter().copied());
        }
        assert_eq!(solver.solve(), Some(false));
        let learned = &solver.get_callbacks().expect("callbacks").learned;
        assert!(!learned.is_empty(), "PHP-7-6 should export learned clauses");
        assert!(learned.iter().all(|c| c.iter().all(|&l| l != 0)), "no terminating zeros in the clause");
        // Each exported clause must be implied: asserting its negation on
        // top of the formula is unsatisfiable.
        for c in learned.iter().take(20) {
            let mut check: Solver = Solver::new();
            for f in &clauses {
                check.add_clause(f.iter().copied());
            }
            for &l in c {
                check.add_clause([-l]);
            }
            assert_eq!(check.solve(), Some(false), "learned clause {c:?} is not implied");
        }
    }

    #[test]
    fn a_zero_max_length_leaves_the_learner_disconnected() {
        let mut solver: Solver<Watch> = Solver::new();
        solver.set_callbacks(Some(Watch { stop_at: usize::MAX, polls: 0, learned: Vec::new(), max_length: 0 }));
        let x = |p: i32, h: i32| p * 5 + h + 1;
        for p in 0..6 {
            solver.add_clause((0..5).map(|h| x(p, h)));
        }
        for h in 0..5 {
            for p in 0..6 {
                for q in p + 1..6 {
                    solver.add_clause([-x(p, h), -x(q, h)]);
                }
            }
        }
        assert_eq!(solver.solve(), Some(false));
        assert!(solver.get_callbacks().expect("callbacks").learned.is_empty());
    }

    #[test]
    fn options_are_settable_before_the_first_clause_only() {
        let mut solver: Solver = Solver::new();
        assert!(solver.set_option("restart", 0));
        assert!(!solver.set_option("no-such-option", 1));
        solver.add_clause([1]);
        assert!(!solver.set_option("restart", 1), "too late to configure");
        assert_eq!(solver.solve(), Some(true));
        assert_eq!(solver.max_variable(), 1);
    }

    /// If a re-vendoring renames or drops one of these, the reference
    /// configuration silently stops being applied — which is the failure
    /// this constant exists to prevent.
    #[test]
    fn the_reference_options_still_exist() {
        let mut solver: Solver = Solver::new();
        for (name, value) in RELEASE_3_0_0_DEFAULTS {
            assert!(solver.set_option(name, value), "CaDiCaL 3.0.1 has no option {name:?}");
        }
        // `factor` is on: without this the next line aborts the process.
        solver.reserve(2);
        assert!(!solver.set_option("factor", 1), "no options after a declaration");
        solver.add_clause([1, 2]);
        solver.add_clause([-1]);
        assert_eq!(solver.solve(), Some(true));
        assert_eq!(solver.value(2), Some(true));
        assert!(solver.max_variable() >= 2);
    }

    #[test]
    fn reserving_does_not_disturb_the_answer() {
        let mut a: Solver = Solver::new();
        let mut b: Solver = Solver::new();
        b.reserve(5);
        for s in [&mut a, &mut b] {
            s.add_clause([1, 2]);
            s.add_clause([-1, 3]);
            s.add_clause([-3, -2]);
        }
        assert_eq!(a.solve(), Some(true));
        assert_eq!(b.solve(), Some(true));
        // Declared but unmentioned: valued, not refused.
        assert!(b.value(5).is_some());
        assert!(b.max_variable() >= 5);
    }

    #[test]
    fn a_timeout_gives_up() {
        let mut solver: Solver<Timeout> = Solver::new();
        solver.set_callbacks(Some(Timeout::new(0.05)));
        let x = |p: i32, h: i32| p * 13 + h + 1;
        for p in 0..14 {
            solver.add_clause((0..13).map(|h| x(p, h)));
        }
        for h in 0..13 {
            for p in 0..14 {
                for q in p + 1..14 {
                    solver.add_clause([-x(p, h), -x(q, h)]);
                }
            }
        }
        let t = Instant::now();
        assert_eq!(solver.solve(), None);
        assert!(t.elapsed() < Duration::from_secs(10), "took {:?}", t.elapsed());
    }
}
