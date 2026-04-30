//! `StateQueryWrapper` — composes any inner [`PathSearchController`]
//! with the dual-framework's cover-state query layer.
//!
//! The wrapper sits between the DFS engine and the inner controller.
//! On every step it (1) consults the inner first so the inner's
//! state stays accurate, (2) checks the cancel flag, and (3) if the
//! inner says "continue", asks the shared
//! [`crate::dual::CoverState`] whether the current `ProdPath` is
//! already covered by some pair A has registered — if yes, the
//! wrapper returns `Some(0)` to skip the subtree.
//!
//! Wrapping is *generic* over the inner controller type, so the
//! same wrapper composes with `BacktrackWhenCoveredController`,
//! `SmartController`, and `CdclController` alike.  Each gets the
//! same cover-state-driven pruning on top of its own search logic.
//!
//! Instrumentation counters (`state_query_count`,
//! `state_prune_count`) are printed on drop when `CDCL_INSTR=1` is
//! set in the environment.

use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};

use crate::controller::PathSearchController;
use crate::dual::{CoverState, PathOutcome};
use crate::matrix::{Lit, NNF, PathPrefix, PathsClass, ProdPath};

pub struct StateQueryWrapper<Inner: PathSearchController, S: CoverState> {
    pub inner:  Inner,
    pub state:  Arc<Mutex<S>>,
    pub cancel: Arc<AtomicBool>,
    pub state_query_count: usize,
    pub state_prune_count: usize,
}

impl<Inner: PathSearchController, S: CoverState> StateQueryWrapper<Inner, S> {
    pub fn new(inner: Inner, state: Arc<Mutex<S>>, cancel: Arc<AtomicBool>) -> Self {
        Self {
            inner,
            state,
            cancel,
            state_query_count: 0,
            state_prune_count: 0,
        }
    }
}

impl<Inner: PathSearchController, S: CoverState> Drop for StateQueryWrapper<Inner, S> {
    fn drop(&mut self) {
        if std::env::var("CDCL_INSTR").is_ok() {
            eprintln!("c [dual.path] state_queries={} state_prunes={}",
                      self.state_query_count, self.state_prune_count);
        }
    }
}

impl<Inner: PathSearchController, S: CoverState> PathSearchController for StateQueryWrapper<Inner, S> {
    /// Composite isn't constructed via `with_on_class`; it's built
    /// from an already-constructed inner.  The trait's default-panic
    /// constructor impls are appropriate.
    type OnClass = ();

    fn should_continue_on_prefix(
        &mut self,
        prefix_literals:  &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        prefix_prod_path: &ProdPath,
        is_complete:      bool,
    ) -> Option<usize> {
        // Cooperative cancellation: bail out fast.
        if self.cancel.load(Ordering::SeqCst) {
            return Some(0);
        }
        // Inner first — its lit-counter / propagation state must
        // reflect the current prefix before we check anything else.
        let r = self.inner.should_continue_on_prefix(
            prefix_literals, prefix_positions, prefix_prod_path, is_complete,
        );
        if r.is_some() { return r; }
        // Then consult A's cover state.  Only meaningful when
        // is_complete == false (mid-prefix); on a complete path the
        // inner already classified it.
        if !is_complete {
            self.state_query_count += 1;
            let s = self.state.lock().unwrap();
            if s.is_prefix_covered(prefix_prod_path) {
                self.state_prune_count += 1;
                return Some(0);
            }
        }
        None
    }

    fn should_continue_on_paths_class(&mut self, paths_class: PathsClass, hit_limit: bool) -> bool {
        self.inner.should_continue_on_paths_class(paths_class, hit_limit)
    }

    fn needs_cover(&self) -> bool { self.inner.needs_cover() }

    fn sum_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.sum_ord(children)
    }

    fn prod_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.prod_ord(children)
    }

    fn path_count(&self) -> usize { self.inner.path_count() }
    fn covered_prefix_count(&self) -> usize { self.inner.covered_prefix_count() }
    fn uncovered_path_count(&self) -> usize { self.inner.uncovered_path_count() }
    fn paths_classified(&self) -> f64 { self.inner.paths_classified() }
    fn is_restart_pending(&self) -> bool { self.inner.is_restart_pending() }
    fn complete_restart(&mut self) { self.inner.complete_restart() }
}

/// Run the cover-aware DFS with restart support — mirrors the
/// outer restart loop in
/// [`crate::matrix::NNF::classify_paths_uncovered_only`].  Without
/// this loop, when the inner controller (e.g. [`CdclController`])
/// requests a restart by returning `Some(usize::MAX)`, the engine
/// unwinds to the top and the dual's `run()` would falsely
/// interpret an empty uncovered slot as "exhausted" → UNSAT.
///
/// Repeatedly:
/// 1. Drive the DFS to completion (or unwind).
/// 2. If the uncovered slot got filled this iteration, return
///    `Uncovered(pp)`.
/// 3. Else if the inner asked for a restart and no Uncovered was
///    found, call `complete_restart()` and re-run.
/// 4. Else return `Exhausted`.
///
/// Cancellation is checked at every restart boundary; mid-DFS
/// cancellation is handled by the inner returning `Some(0)` from
/// `should_continue_on_prefix` when `cancel.is_set()`.
pub fn run_dfs_with_restarts<Inner, S>(
    composite: &mut StateQueryWrapper<Inner, S>,
    nnf: &NNF,
    uncovered: &Mutex<Option<ProdPath>>,
) -> PathOutcome
where
    Inner: PathSearchController,
    S: CoverState,
{
    loop {
        if composite.cancel.load(Ordering::SeqCst) {
            return PathOutcome::Cancelled;
        }
        nnf.for_each_path_prefix_with_controller(composite);
        if composite.cancel.load(Ordering::SeqCst) {
            return PathOutcome::Cancelled;
        }
        // Snapshot the uncovered slot — leave it filled so the
        // outer driver can read it after we return.
        if uncovered.lock().unwrap().is_some() {
            // Take it so the caller's match expression sees the
            // value cleanly without re-locking.
            let pp = uncovered.lock().unwrap().take().unwrap();
            return PathOutcome::Uncovered(pp);
        }
        if composite.is_restart_pending() {
            composite.complete_restart();
            continue;
        }
        return PathOutcome::Exhausted;
    }
}
