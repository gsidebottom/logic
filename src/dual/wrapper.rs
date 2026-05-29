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
            // Pass `prefix_positions` (absolute tree positions, in
            // declaration-order coordinates) — *not* `prefix_prod_path`
            // (DFS-visit order, which `EffectiveCountWrapper::sum_ord`
            // can permute).  See the trait-level doc for the
            // soundness rationale.
            if s.is_prefix_covered(prefix_positions) {
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

    fn sum_ord<'a>(&mut self, parent: &'a NNF, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.sum_ord(parent, children)
    }

    fn prod_ord<'a>(&mut self, parent: &'a NNF, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.prod_ord(parent, children)
    }

    fn path_count(&self) -> usize { self.inner.path_count() }
    fn covered_prefix_count(&self) -> usize { self.inner.covered_prefix_count() }
    fn uncovered_path_count(&self) -> usize { self.inner.uncovered_path_count() }
    fn paths_classified(&self) -> f64 { self.inner.paths_classified() }
    fn pre_leaf_pruning_credit(&self) -> f64 { self.inner.pre_leaf_pruning_credit() }
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
    run_dfs_with_restarts_impl(composite, nnf, uncovered, /*bubble_up=*/ false)
}

/// Bubble-up variant of [`run_dfs_with_restarts`].  Drives the DFS
/// via [`NNF::for_each_path_prefix_with_controller_bubble_up`], which
/// short-circuits CDCL's multi-level restart signal via the engine's
/// `Some(k>0) → Some(k-1)` bubble-up instead of "exhausting each
/// sibling one at a time."
///
/// **EXPERIMENTAL — known soundness issue:** see the doc comment on
/// [`NNF::for_each_path_prefix_ord_bubble_up`].  Used by the
/// `basic_effb` / `greedy_effb` dual backends for benchmarking.
pub fn run_dfs_with_restarts_bubble_up<Inner, S>(
    composite: &mut StateQueryWrapper<Inner, S>,
    nnf: &NNF,
    uncovered: &Mutex<Option<ProdPath>>,
) -> PathOutcome
where
    Inner: PathSearchController,
    S: CoverState,
{
    run_dfs_with_restarts_impl(composite, nnf, uncovered, /*bubble_up=*/ true)
}

fn run_dfs_with_restarts_impl<Inner, S>(
    composite: &mut StateQueryWrapper<Inner, S>,
    nnf: &NNF,
    uncovered: &Mutex<Option<ProdPath>>,
    bubble_up: bool,
) -> PathOutcome
where
    Inner: PathSearchController,
    S: CoverState,
{
    loop {
        if composite.cancel.load(Ordering::SeqCst) {
            return PathOutcome::Cancelled;
        }
        if bubble_up {
            nnf.for_each_path_prefix_with_controller_bubble_up(composite);
        } else {
            nnf.for_each_path_prefix_with_controller(composite);
        }
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

/// Cover-mult-weighted variant of [`run_dfs_with_restarts`].  Mirrors
/// the arena driver's `classify_paths_with_arena_impl` accounting:
/// maintains a driver-side `paths_classified: f64` counter that
/// detects new Covered events via `composite.covered_prefix_count()`
/// and credits each by the cover multiplier the NNF engine threads
/// through `for_each_path_prefix_with_controller_weighted`.
/// Uncovered events count 1 each.  Periodically publishes
/// `driver_side + composite.paths_classified()` (where the
/// `composite.paths_classified()` carries any pre-leaf contribution
/// like the `EffectiveCountWrapper`'s `pruned_paths_peak`) into the
/// supplied progress atom.
///
/// Pair with `ProgressWrapper::with_publish_disabled()` — without
/// that, the wrapper's own un-weighted publishes would race and
/// overwrite the weighted value.
pub fn run_dfs_with_restarts_weighted<Inner, S>(
    composite: &mut StateQueryWrapper<Inner, S>,
    nnf: &NNF,
    uncovered: &Mutex<Option<ProdPath>>,
    progress: Arc<std::sync::atomic::AtomicU64>,
) -> PathOutcome
where
    Inner: PathSearchController,
    S: CoverState,
{
    run_dfs_with_restarts_weighted_impl(composite, nnf, uncovered, progress, /*bubble_up=*/ false)
}

/// Bubble-up variant — same soundness caveat as
/// [`run_dfs_with_restarts_bubble_up`].
pub fn run_dfs_with_restarts_weighted_bubble_up<Inner, S>(
    composite: &mut StateQueryWrapper<Inner, S>,
    nnf: &NNF,
    uncovered: &Mutex<Option<ProdPath>>,
    progress: Arc<std::sync::atomic::AtomicU64>,
) -> PathOutcome
where
    Inner: PathSearchController,
    S: CoverState,
{
    run_dfs_with_restarts_weighted_impl(composite, nnf, uncovered, progress, /*bubble_up=*/ true)
}

fn run_dfs_with_restarts_weighted_impl<Inner, S>(
    composite: &mut StateQueryWrapper<Inner, S>,
    nnf: &NNF,
    uncovered: &Mutex<Option<ProdPath>>,
    progress: Arc<std::sync::atomic::AtomicU64>,
    bubble_up: bool,
) -> PathOutcome
where
    Inner: PathSearchController,
    S: CoverState,
{
    // Driver-side cover-mult-weighted `paths_classified`.  Persists
    // across restart iterations so the published value is cumulative.
    let mut paths_classified: f64 = 0.0;
    let mut prev_cov: usize = 0;
    let mut prev_unc: usize = 0;
    let mut step: u64 = 0;
    // Total path count for the safety `debug_assert!`s below.  May
    // be `f64::INFINITY` on huge formulas (path_count() does naive
    // multiplication); the assertion skips itself in that case.
    let total_nnf = nnf.path_count();
    loop {
        if composite.cancel.load(Ordering::SeqCst) {
            return PathOutcome::Cancelled;
        }
        // Build the cover-mult post_hook.  Closure captures the
        // accumulators above and the progress atom; called after
        // every `should_continue_on_prefix` with the current mult.
        let cancel_for_hook = composite.cancel.clone();
        let progress_for_hook = progress.clone();
        let mut post_hook = |ctrl: &mut StateQueryWrapper<Inner, S>, mult: f64| -> bool {
            if cancel_for_hook.load(Ordering::SeqCst) {
                return false;
            }
            let cov = ctrl.covered_prefix_count();
            let unc = ctrl.uncovered_path_count();
            if cov > prev_cov {
                // Each new Covered event covers `mult` complete
                // paths through the NNF.
                paths_classified += mult * (cov - prev_cov) as f64;
                prev_cov = cov;
            }
            if unc > prev_unc {
                paths_classified += (unc - prev_unc) as f64;
                prev_unc = unc;
            }
            step = step.wrapping_add(1);
            if step & 0xFFF == 0 {
                // Add the controller stack's own contribution
                // (e.g. the `EffectiveCountWrapper`'s
                // `pruned_paths_peak` for pre-leaf pruning).
                // Disjoint from leaf events by construction.
                let pre_leaf = ctrl.pre_leaf_pruning_credit();
                let total_now = paths_classified + pre_leaf;
                // Safety invariant: never publish above total path count.
                debug_assert!(
                    !total_nnf.is_finite() || total_now <= total_nnf * 1.001,
                    "dual driver: paths_classified ({}) + pre_leaf ({}) = {} exceeds total {}",
                    paths_classified, pre_leaf, total_now, total_nnf,
                );
                progress_for_hook.store(total_now.to_bits(), Ordering::Relaxed);
            }
            true
        };
        if bubble_up {
            nnf.for_each_path_prefix_with_controller_weighted_bubble_up(composite, &mut post_hook);
        } else {
            nnf.for_each_path_prefix_with_controller_weighted(composite, &mut post_hook);
        }
        if composite.cancel.load(Ordering::SeqCst) {
            return PathOutcome::Cancelled;
        }
        if uncovered.lock().unwrap().is_some() {
            let pp = uncovered.lock().unwrap().take().unwrap();
            // Final publish for this attempt before returning.
            let pre_leaf = composite.pre_leaf_pruning_credit();
            let final_total = paths_classified + pre_leaf;
            debug_assert!(
                !total_nnf.is_finite() || final_total <= total_nnf * 1.001,
                "dual driver Uncovered exit: total {} exceeds total path count {}",
                final_total, total_nnf,
            );
            progress.store(final_total.to_bits(), Ordering::Relaxed);
            return PathOutcome::Uncovered(pp);
        }
        if composite.is_restart_pending() {
            composite.complete_restart();
            continue;
        }
        // Search exhausted; final publish so the last batch lands.
        let pre_leaf = composite.pre_leaf_pruning_credit();
        let final_total = paths_classified + pre_leaf;
        debug_assert!(
            !total_nnf.is_finite() || final_total <= total_nnf * 1.001,
            "dual driver Exhausted exit: total {} exceeds total path count {}",
            final_total, total_nnf,
        );
        progress.store(final_total.to_bits(), Ordering::Relaxed);
        return PathOutcome::Exhausted;
    }
}


/// `ProgressWrapper` — wraps any [`PathSearchController`] and
/// periodically publishes its `paths_classified()` value into a
/// shared `Arc<AtomicU64>` (the `PathClassificationHandle`'s paths
/// atom).  Used by the dual path controllers, which don't go
/// through the `CancelController` wrapping that single-DFS callers
/// get for free — without this, the progress bar would see a
/// constant zero for the dual configs.
///
/// Publishes every 4096 `should_continue_on_prefix` calls (same
/// cadence as `CancelController`), encoded as `f64::to_bits()` to
/// match `PathClassificationHandle::record_paths`.
pub struct ProgressWrapper<Inner: PathSearchController> {
    pub inner:    Inner,
    pub progress: Arc<std::sync::atomic::AtomicU64>,
    step: u64,
    /// When `true`, the wrapper stops self-publishing inside
    /// `should_continue_on_prefix`.  Used by the dual driver's
    /// weighted variant (`run_dfs_with_restarts_weighted`), which
    /// publishes a cover-mult-weighted value driver-side — without
    /// this flag the wrapper would race and overwrite it with an
    /// unweighted `inner.paths_classified()`.  Mirrors the same
    /// flag on `CancelController` for the arena driver path.
    publish_disabled: bool,
}

impl<Inner: PathSearchController> ProgressWrapper<Inner> {
    pub fn new(inner: Inner, progress: Arc<std::sync::atomic::AtomicU64>) -> Self {
        Self { inner, progress, step: 0, publish_disabled: false }
    }

    /// Builder: suppress this wrapper's `publish_progress` calls
    /// from inside `should_continue_on_prefix`.  Use when the
    /// surrounding driver publishes its own (better) value.
    pub fn with_publish_disabled(mut self) -> Self {
        self.publish_disabled = true;
        self
    }

    /// Publish once explicitly — for use after the DFS completes so
    /// the final count is reflected even if the last 4096-step
    /// boundary wasn't crossed.  No-op when `publish_disabled` is set.
    pub fn publish_progress(&self) {
        if !self.publish_disabled {
            self.progress.store(
                self.inner.paths_classified().to_bits(),
                std::sync::atomic::Ordering::Relaxed,
            );
        }
    }
}

impl<Inner: PathSearchController> PathSearchController for ProgressWrapper<Inner> {
    type OnClass = ();

    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        prefix_prod_path: &ProdPath,
        is_complete: bool,
    ) -> Option<usize> {
        self.step = self.step.wrapping_add(1);
        if self.step & 0xFFF == 0 && !self.publish_disabled {
            self.publish_progress();
        }
        self.inner.should_continue_on_prefix(
            prefix_literals, prefix_positions, prefix_prod_path, is_complete,
        )
    }

    fn should_continue_on_paths_class(&mut self, paths_class: PathsClass, hit_limit: bool) -> bool {
        self.inner.should_continue_on_paths_class(paths_class, hit_limit)
    }

    fn needs_cover(&self) -> bool { self.inner.needs_cover() }

    fn sum_ord<'a>(&mut self, parent: &'a NNF, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.sum_ord(parent, children)
    }

    fn prod_ord<'a>(&mut self, parent: &'a NNF, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.prod_ord(parent, children)
    }

    fn path_count(&self) -> usize { self.inner.path_count() }
    fn covered_prefix_count(&self) -> usize { self.inner.covered_prefix_count() }
    fn uncovered_path_count(&self) -> usize { self.inner.uncovered_path_count() }
    fn paths_classified(&self) -> f64 { self.inner.paths_classified() }
    fn pre_leaf_pruning_credit(&self) -> f64 { self.inner.pre_leaf_pruning_credit() }

    fn is_restart_pending(&self) -> bool { self.inner.is_restart_pending() }
    fn complete_restart(&mut self) { self.inner.complete_restart(); }
}

