//! `EffectivePathController` — DualPathSearchController that uses
//! [`EffectiveCountWrapper`] to sort Sum/Prod children by ascending
//! effective path count (most-constrained first), filter
//! provably-blocked Prod alts, and short-circuit when the root's
//! effective count drops to zero.
//!
//! Composition is the same shape as the existing
//! [`crate::dual::CdclDualPathController`]:
//!
//! ```text
//!   StateQueryWrapper                 (Phase 2 — A's cover state queries)
//!     └── EffectiveCountWrapper        (this file — count-aware ordering)
//!           └── CdclController          (cover-mode + propagation + 1UIP)
//! ```
//!
//! The inner is a `CdclController` since CDCL has been the strongest
//! B side on every benchmark.  The Effective layer adds value on
//! non-flat NNFs (e.g. `plus(a;b;c;w) ∧ pinning`) where CDCL's own
//! cross-clause propagation is dormant — the count layer gives
//! matrix-DFS a structural-NNF analog of unit propagation.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use crate::controller::{CdclController, PathSearchController};
use crate::dual::effective_count::{DeltaFrame, EffectiveCountIndex, EffectiveCounts};
use crate::dual::wrapper::{run_dfs_with_restarts_weighted, run_dfs_with_restarts_weighted_bubble_up, StateQueryWrapper};
use crate::dual::{
    BasicCoverState, CoverState, DualPathSearchController, PairPool, PathOutcome, SearchMode,
};
use crate::matrix::{Lit, PathParams, PathPrefix, PathsClass, ProdPath, NNF};

pub struct EffectivePathController<S: CoverState = BasicCoverState> {
    _state: std::marker::PhantomData<S>,
    /// Optional UI streaming sink — when set, every `PathsClass` event
    /// the path search emits is forwarded here (in addition to the
    /// dual framework's internal pool / uncovered handling).  Used by
    /// the web UI so the `greedy×eff` backend can populate cover
    /// groups and the uncovered-path list the same way single-DFS
    /// backends do.
    stream_tx: Option<tokio::sync::mpsc::Sender<(PathsClass, bool)>>,
    /// Optional progress atom.  When set, the run wraps the composite
    /// stack in a `ProgressWrapper` that publishes
    /// `paths_classified()` here every ~4096 DFS steps.  Required
    /// because dual path controllers don't get the
    /// `CancelController` wrapping that single-DFS callers receive,
    /// and `EffectivePathController`'s search work is mostly
    /// invisible to leaf-level Covered detection (the Effective
    /// layer's count-based pruning short-circuits before the leaf).
    progress: Option<Arc<std::sync::atomic::AtomicU64>>,
    /// Optional CDCL trailing-indicator stats atoms — see
    /// [`crate::dual::wrapper::ProgressAtoms`] for the rationale.
    cdcl_conflicts: Option<Arc<std::sync::atomic::AtomicU64>>,
    cdcl_restarts:  Option<Arc<std::sync::atomic::AtomicU64>>,
    /// EXPERIMENTAL: when `true`, drive the DFS via the bubble-up
    /// variant of `run_dfs_with_restarts`.  See
    /// [`crate::dual::wrapper::run_dfs_with_restarts_bubble_up`] for
    /// the soundness caveat.  Set via [`Self::with_bubble_up`] for
    /// the `basic_effb` / `greedy_effb` backends.
    bubble_up: bool,
    /// **Variance-gated Sum reordering threshold.**  When a Sum node's
    /// children have effective counts that span at least `10^tau` in
    /// magnitude (i.e. `log10(max_count / min_count) >= tau`), the
    /// wrapper applies its usual ascending-by-count reordering.  When
    /// siblings are within `10^tau` of each other, reordering is
    /// *skipped* (children stay in inner order) on the theory that
    /// no meaningfully better order exists at that node — and that
    /// re-imposing one disrupts CDCL's VSIDS heuristic for no gain.
    ///
    /// Default 0.0 = always reorder (pre-gate behavior; preserves
    /// existing test results).  Higher τ values progressively suppress
    /// reordering on uniform-cost Sums (e.g. Steiner / PHP / random
    /// 3-SAT — formulas where every clause-complement Prod has the
    /// same effective count, making the eff metric uninformative).
    /// `f64::INFINITY` ≈ "never reorder" → wrapper degrades to a
    /// no-op for Sum, keeping only the (sound) Prod zero-count filter.
    ///
    /// Only affects `sum_ord` — `prod_ord`'s zero-count filter is
    /// sound regardless and stays unconditionally active.
    sum_reorder_tau: f64,
}

impl<S: CoverState> Default for EffectivePathController<S> {
    fn default() -> Self { Self::new() }
}

impl<S: CoverState> EffectivePathController<S> {
    pub fn new() -> Self {
        Self {
            _state: std::marker::PhantomData,
            stream_tx: None,
            progress: None,
            cdcl_conflicts: None,
            cdcl_restarts: None,
            bubble_up: false,
            sum_reorder_tau: 0.0,
        }
    }

    /// Build the controller with a UI-streaming sender.  Every
    /// `PathsClass` event is cloned and `blocking_send`'d to `tx`
    /// before the dual framework's internal handler runs.
    pub fn with_stream(tx: tokio::sync::mpsc::Sender<(PathsClass, bool)>) -> Self {
        Self {
            _state: std::marker::PhantomData,
            stream_tx: Some(tx),
            progress: None,
            cdcl_conflicts: None,
            cdcl_restarts: None,
            bubble_up: false,
            sum_reorder_tau: 0.0,
        }
    }

    /// Configure the controller to publish progress
    /// (`paths_classified()`) into `atom` every ~4096 DFS steps.
    /// Pair with `PathClassificationHandle::paths_atom()` so a
    /// progress observer's `paths_so_far()` reader sees the
    /// published values.  Builder; chainable with `with_stream`.
    pub fn with_progress(mut self, atom: Arc<std::sync::atomic::AtomicU64>) -> Self {
        self.progress = Some(atom);
        self
    }

    /// Configure CDCL trailing-indicator atoms — `conflicts` and
    /// `restarts` get published at the same cadence as `progress`.
    /// See [`crate::dual::wrapper::ProgressAtoms`] for the rationale.
    /// Builder; chainable.
    pub fn with_cdcl_stats(
        mut self,
        conflicts: Arc<std::sync::atomic::AtomicU64>,
        restarts:  Arc<std::sync::atomic::AtomicU64>,
    ) -> Self {
        self.cdcl_conflicts = Some(conflicts);
        self.cdcl_restarts  = Some(restarts);
        self
    }

    /// Enable bubble-up restart-handling on the DFS driver.  See
    /// [`crate::dual::wrapper::run_dfs_with_restarts_bubble_up`] for
    /// the soundness caveat.  Builder; chainable.
    pub fn with_bubble_up(mut self) -> Self {
        self.bubble_up = true;
        self
    }

    /// Gate Sum-child reordering on the spread of sibling effective
    /// counts: reorder only when `log10(max_count / min_count) >= tau`.
    /// See `EffectiveCountWrapper::sum_reorder_tau` for the full
    /// rationale.  `tau == 0.0` (the default) preserves the
    /// pre-gate behavior of always reordering.
    pub fn with_eff_tau(mut self, tau: f64) -> Self {
        self.sum_reorder_tau = tau;
        self
    }
}

impl<S: CoverState + 'static> DualPathSearchController for EffectivePathController<S> {
    type State = S;

    fn run(
        self,
        nnf: &NNF,
        _mode: SearchMode,
        pool: Arc<PairPool>,
        state: Arc<Mutex<Self::State>>,
        cancel: Arc<AtomicBool>,
    ) -> PathOutcome {
        // Build the effective-count index for this NNF.  The index
        // stores raw `*const NNF` pointers, so the NNF must outlive
        // the controller — `nnf` is borrowed for the run, satisfying
        // that.
        let idx = EffectiveCountIndex::build(nnf);
        let counts = EffectiveCounts::new(&idx);

        let uncovered: Arc<Mutex<Option<ProdPath>>> = Arc::new(Mutex::new(None));
        let stream_tx = self.stream_tx;

        let on_class = {
            let pool = pool.clone();
            let uncovered = uncovered.clone();
            let cancel = cancel.clone();
            move |class: PathsClass, hit_limit: bool| -> bool {
                if cancel.load(Ordering::SeqCst) { return false; }
                // Tee to the UI stream first (clone, since the inner
                // match below moves `class`).  Use `try_send` (not
                // `blocking_send`) so that a slow / contended drainer
                // can't hold B's std-thread hostage — when the channel
                // is full or the receiver is dropped, we just drop
                // the event.  The dual framework's internal logic
                // (pool / uncovered) is unaffected; only the UI's
                // cover-group display loses some events under load,
                // which is a fine tradeoff for keeping cancel
                // responsive across back-to-back re-runs.
                if let Some(ref tx) = stream_tx {
                    let _ = tx.try_send((class.clone(), hit_limit));
                }
                match class {
                    PathsClass::Covered(cpp) => { pool.push(cpp.cover); true }
                    PathsClass::Uncovered(up) => {
                        let mut slot = uncovered.lock().unwrap();
                        if slot.is_none() { *slot = Some(up.prod_path); }
                        false
                    }
                }
            }
        };

        let params = PathParams {
            uncovered_path_limit: 1,
            paths_class_limit:    usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover:             false,
        };

        let inner = CdclController::for_nnf_with_cover(nnf, Some(params), on_class);
        let counted = EffectiveCountWrapper::new_with_tau(inner, idx, counts, self.sum_reorder_tau);
        // Wrap with a ProgressWrapper.  When no progress atom was
        // configured via `with_progress`, fall back to a private
        // throwaway atomic the wrapper writes to but nobody reads —
        // costs one `AtomicU64::store` per 4096 DFS calls, trivial.
        let progress_atom = self.progress.clone().unwrap_or_else(
            || Arc::new(std::sync::atomic::AtomicU64::new(0)));
        let conflicts_atom = self.cdcl_conflicts.clone().unwrap_or_else(
            || Arc::new(std::sync::atomic::AtomicU64::new(0)));
        let restarts_atom = self.cdcl_restarts.clone().unwrap_or_else(
            || Arc::new(std::sync::atomic::AtomicU64::new(0)));
        let atoms = crate::dual::wrapper::ProgressAtoms {
            paths: progress_atom.clone(),
            conflicts: conflicts_atom,
            restarts: restarts_atom,
        };
        // **Weighted driver wiring.**  Cover-mult-weighted progress
        // for the eff dual backends (greedy_eff, basic_eff,
        // greedy_effb, basic_effb).  Disabling the wrapper's own
        // publish prevents it from racing the driver's weighted
        // value with an unweighted one.  See
        // `wrapper.rs::run_dfs_with_restarts_weighted_impl` for the
        // driver's accounting + the `pre_leaf_pruning_credit` trait
        // method for how the eff wrapper's peak is surfaced.
        let with_progress = crate::dual::wrapper::ProgressWrapper::new(counted, progress_atom)
            .with_publish_disabled();
        let mut composite = StateQueryWrapper::new(with_progress, state, cancel);
        if self.bubble_up {
            run_dfs_with_restarts_weighted_bubble_up(&mut composite, nnf, &*uncovered, atoms)
        } else {
            run_dfs_with_restarts_weighted(&mut composite, nnf, &*uncovered, atoms)
        }
    }
}

/// Adapts an inner cover-aware [`PathSearchController`] with
/// effective-count maintenance.  On every step:
///
/// 1. Sync count state with the prefix (push/pop deltas).
/// 2. If root count drops to zero, return `Some(0)` for early prune.
/// 3. Delegate to the inner controller.
///
/// Sum/Prod ordering is delegated to the inner first, then re-sorted
/// by ascending effective count.  For Prod, alts whose count is zero
/// are filtered out — this is sound because Prod picks one and a
/// zero-count alt is provably blocked.  For Sum, all (non-zero)
/// children are kept; zero-count Sum-children are also filtered, but
/// zeroing one child zeroes the Sum which surfaces via the root
/// count check on the next call.
pub struct EffectiveCountWrapper<Inner: PathSearchController> {
    pub inner:  Inner,
    pub idx:    EffectiveCountIndex,
    pub counts: EffectiveCounts,
    /// Min log10(max/min) of sibling effective-counts required for
    /// `sum_ord` to actually reorder.  See
    /// `EffectivePathController::sum_reorder_tau` for the full
    /// rationale.  0.0 = always reorder (pre-gate behavior).
    sum_reorder_tau: f64,
    /// One delta-frame per pushed lit.  `frames.len()` mirrors
    /// `prefix_literals.len()` after `should_continue_on_prefix`
    /// has synced.
    frames: Vec<DeltaFrame>,
    /// Mirror of the prefix length so we can detect grows / shrinks.
    our_counted_len: usize,
    /// Diagnostics: count of root-zero prunes.
    pub root_zero_prunes: usize,
    /// Diagnostics: count of `prod_ord` calls where filtering reduced
    /// the alt list (i.e. unit-propagation-equivalent forced choices
    /// or pruned alts).
    pub prod_ord_filters: usize,
    /// Diagnostics: count of `sum_ord` calls where the variance gate
    /// skipped a sort (children too uniform — `log10(max/min) < tau`).
    pub sum_ord_gate_skips: usize,
    /// **Progress accounting — pruning credit stack.**
    ///
    /// One entry per pushed literal: the marginal root-effective-count
    /// drop that push caused (= paths blocked by this literal given
    /// the prior prefix).  Pushed on `sync_to_prefix`'s push branch,
    /// popped on the pop branch.  Stays in lockstep with `frames`.
    ///
    /// `pruned_paths_current = sum(pruning_credits)` — by telescoping,
    /// this equals `R₀ − R_depth` where R is the root effective count.
    /// Always ≤ `total_path_count` (because R_depth ≥ 0).  Computed
    /// incrementally to avoid summing the stack every read.
    ///
    /// `pruned_paths_peak` is the all-time max of `current`, monotone
    /// non-decreasing across the whole search (incl. CDCL restarts —
    /// restart pops the trail, so `current` resets to 0, but `peak`
    /// persists).  This is what `paths_classified()` publishes: the
    /// "best fraction of path-space ever provably eliminated under
    /// any single attempt's prefix."
    ///
    /// **Why a stack rather than a single cumulative counter.**  The
    /// pre-fix design (`pruned_paths += old_root - new_root`, pops do
    /// nothing) double-counted whenever the DFS backtracked: the
    /// drop credited to lit L1 stayed on the books after we popped
    /// L1, then we'd credit the drop from sibling alternative L2,
    /// even though some paths between them overlap.  The stack-based
    /// design self-cancels on backtrack — once we pop past L1, its
    /// credit is reversed, leaving room for L2's credit without
    /// double-counting.  Net effect: `current` is always exactly
    /// `R₀ − R_depth`, never an artifact of search history.
    pruning_credits: Vec<f64>,
    pruned_paths_current: f64,
    pub pruned_paths_peak: f64,
}

impl<Inner: PathSearchController> EffectiveCountWrapper<Inner> {
    /// Build a wrapper with the default (always-reorder) policy —
    /// equivalent to `new_with_tau(.., .., .., 0.0)`.  Kept for
    /// callers that don't care about variance-gating.
    pub fn new(inner: Inner, idx: EffectiveCountIndex, counts: EffectiveCounts) -> Self {
        Self::new_with_tau(inner, idx, counts, 0.0)
    }

    /// Build a wrapper with a custom variance threshold τ on Sum
    /// reordering.  When a Sum's children's effective-counts have
    /// `log10(max/min) < tau`, reordering is skipped — they stay in
    /// inner-controller order.  Use `tau = 0.0` for the legacy
    /// "always reorder" behavior; `tau = f64::INFINITY` for "never
    /// reorder" (Sum becomes a passthrough; only the Prod zero-count
    /// filter remains).  Higher values progressively suppress
    /// reordering on uniform-cost formulas.
    pub fn new_with_tau(
        inner: Inner,
        idx: EffectiveCountIndex,
        counts: EffectiveCounts,
        sum_reorder_tau: f64,
    ) -> Self {
        Self {
            inner, idx, counts,
            sum_reorder_tau,
            frames: Vec::new(),
            our_counted_len: 0,
            root_zero_prunes: 0,
            prod_ord_filters: 0,
            sum_ord_gate_skips: 0,
            pruning_credits: Vec::new(),
            pruned_paths_current: 0.0,
            pruned_paths_peak: 0.0,
        }
    }

    fn sync_to_prefix(&mut self, prefix_literals: &Vec<&Lit>) {
        // ── Pop branch ──
        // Each pop reverses the count layer's leaf updates AND
        // decrements `pruned_paths_current` by the credit we charged
        // at the corresponding push.  This is what stops the
        // double-counting that the old (pop-is-no-op) design suffered
        // from: the credit only lives while its literal is on the
        // current prefix.
        while self.our_counted_len > prefix_literals.len() {
            let frame = self.frames.pop().expect("frames underflow");
            self.counts.pop_undo(frame);
            if let Some(credit) = self.pruning_credits.pop() {
                self.pruned_paths_current -= credit;
                // Clamp at 0 — float arithmetic over many push/pops
                // can drift slightly negative even though the math is
                // exact in real numbers.
                if self.pruned_paths_current < 0.0 {
                    self.pruned_paths_current = 0.0;
                }
            }
            self.our_counted_len -= 1;
        }
        // ── Push branch ──
        // Each push commits to one literal of the DFS path; the
        // literal may immediately block some paths (the ones whose
        // path-leaves require the complementary polarity somewhere
        // downstream).  Push the root-drop onto the credit stack,
        // add it to `current`, and refresh `peak` if current is now
        // higher than any value we've ever observed.
        let root_id = self.idx.root_id();
        while self.our_counted_len < prefix_literals.len() {
            let old_root = self.counts.count_of(root_id);
            let lit: Lit = prefix_literals[self.our_counted_len].clone();
            let frame = self.counts.push(&self.idx, &lit);
            self.frames.push(frame);
            self.our_counted_len += 1;
            let new_root = self.counts.count_of(root_id);
            let drop = if new_root < old_root { old_root - new_root } else { 0.0 };
            self.pruning_credits.push(drop);
            self.pruned_paths_current += drop;
            if self.pruned_paths_current > self.pruned_paths_peak {
                self.pruned_paths_peak = self.pruned_paths_current;
            }
        }
    }
}

impl<Inner: PathSearchController> Drop for EffectiveCountWrapper<Inner> {
    fn drop(&mut self) {
        if std::env::var("CDCL_INSTR").is_ok() {
            eprintln!(
                "c [dual.effective] root_zero_prunes={} prod_ord_filters={} sum_ord_gate_skips={} sum_reorder_tau={} pruned_paths_peak={:.3e}",
                self.root_zero_prunes, self.prod_ord_filters,
                self.sum_ord_gate_skips, self.sum_reorder_tau,
                self.pruned_paths_peak,
            );
        }
    }
}

/// Variance gate for Sum-child reordering.  Returns `true` iff the
/// children's effective counts span at least `10^tau` in magnitude
/// — i.e., `log10(max_count / min_count) >= tau` — making it worth
/// re-sorting by ascending count.  When the spread is below `tau`,
/// no reordering would meaningfully improve search direction at
/// this Sum, so we skip the sort and let CDCL's own variable-order
/// heuristics dominate (preserves VSIDS activity locality).
///
/// Special cases:
/// - `tau == 0.0` → always `true` (legacy "always reorder" behavior).
/// - fewer than 2 children → `false` (nothing to reorder).
/// - mix of zero and non-zero counts → `true` (zero-count children
///   are valuable to surface early so the inner's cover detection
///   fires quickly — reorder regardless of `tau`).
/// - all counts identical (incl. all zero) → `false` (max/min = 1
///   → log10 = 0 → ≥ tau only when tau = 0, handled above).
fn should_reorder_sum(counts: &[f64], tau: f64) -> bool {
    if counts.len() < 2 { return false; }
    if tau == 0.0 { return true; }
    let mut min_nz: f64 = f64::INFINITY;
    let mut max_nz: f64 = 0.0;
    let mut any_zero = false;
    let mut any_nonzero = false;
    for &c in counts {
        if !c.is_finite() {
            // `inf` here means "no precomputed count" (parent not in
            // the index).  Treat as max — always reorder when one
            // sibling has unknown count.
            return true;
        }
        if c == 0.0 {
            any_zero = true;
        } else {
            any_nonzero = true;
            if c < min_nz { min_nz = c; }
            if c > max_nz { max_nz = c; }
        }
    }
    if any_zero && any_nonzero { return true; }
    if !any_nonzero { return false; }      // all zero — order doesn't matter
    if min_nz <= 0.0 || max_nz <= 0.0 { return false; }
    (max_nz / min_nz).log10() >= tau
}

#[cfg(test)]
mod gate_tests {
    use super::should_reorder_sum;
    #[test] fn tau_zero_always_reorders_with_2plus_children() {
        assert!( should_reorder_sum(&[1.0, 1.0], 0.0));
        assert!( should_reorder_sum(&[1.0, 1.0, 1.0], 0.0));
    }
    #[test] fn lone_or_empty_child_never_reorders() {
        assert!(!should_reorder_sum(&[], 0.0));
        assert!(!should_reorder_sum(&[42.0], 0.0));
        assert!(!should_reorder_sum(&[], 1.0));
    }
    #[test] fn uniform_counts_skip_when_tau_positive() {
        // log10(1.0/1.0) = 0 < 0.5 → skip
        assert!(!should_reorder_sum(&[3.0, 3.0, 3.0, 3.0], 0.5));
        // log10(3.0/3.0) = 0 < 0.001 → skip
        assert!(!should_reorder_sum(&[3.0, 3.0], 0.001));
    }
    #[test] fn high_spread_triggers_reorder() {
        // log10(100/1) = 2 >= 1 → reorder
        assert!( should_reorder_sum(&[1.0, 100.0], 1.0));
        // log10(1000/1) = 3 >= 2 → reorder
        assert!( should_reorder_sum(&[1.0, 10.0, 100.0, 1000.0], 2.0));
    }
    #[test] fn modest_spread_threshold_dependent() {
        // log10(10/1) = 1
        assert!( should_reorder_sum(&[1.0, 10.0], 0.5));   // 1.0 >= 0.5
        assert!( should_reorder_sum(&[1.0, 10.0], 1.0));   // 1.0 >= 1.0
        assert!(!should_reorder_sum(&[1.0, 10.0], 1.001)); // 1.0 < 1.001
    }
    #[test] fn mixed_zero_nonzero_always_reorders() {
        // Zero-count children should always be surfaced first.
        assert!( should_reorder_sum(&[0.0, 5.0, 5.0], 1000.0));
        assert!( should_reorder_sum(&[1.0, 0.0], 99.9));
    }
    #[test] fn infinite_count_triggers_reorder() {
        // f64::INFINITY = "unknown count" (parent not indexed).
        // Reorder to be safe.
        assert!( should_reorder_sum(&[f64::INFINITY, 5.0], 100.0));
    }
    #[test] fn never_reorder_with_infinite_tau() {
        assert!(!should_reorder_sum(&[1.0, 1e10], f64::INFINITY));
    }
}

impl<Inner: PathSearchController> PathSearchController for EffectiveCountWrapper<Inner> {
    type OnClass = ();

    fn should_continue_on_prefix(
        &mut self,
        prefix_literals:  &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        prefix_prod_path: &ProdPath,
        is_complete:      bool,
    ) -> Option<usize> {
        self.sync_to_prefix(prefix_literals);

        // Root-zero prune: every assignment extending this prefix
        // would close some required Sum-child.
        if !is_complete && self.counts.count_of(self.idx.root_id()) == 0.0 {
            self.root_zero_prunes += 1;
            return Some(0);
        }

        self.inner.should_continue_on_prefix(
            prefix_literals, prefix_positions, prefix_prod_path, is_complete)
    }

    fn should_continue_on_paths_class(&mut self, class: PathsClass, hit_limit: bool) -> bool {
        self.inner.should_continue_on_paths_class(class, hit_limit)
    }

    fn needs_cover(&self) -> bool { self.inner.needs_cover() }

    fn sum_ord<'a>(&mut self, parent: &'a NNF, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        // Start from inner's order (None ⇒ declaration order).
        let base: Vec<(usize, &'a NNF)> = match self.inner.sum_ord(parent, children) {
            Some(v) => v,
            None    => children.iter().enumerate().collect(),
        };
        // Annotate with effective counts and re-sort ascending — but
        // do NOT filter zero-count children.  Sum is visit-all; its
        // path-search semantics require visiting every child to
        // collect their lits, so skipping a zero-count child would
        // produce a path whose lit-set is missing those lits and
        // therefore doesn't represent a real assignment.  We only
        // re-order: zero-count children visited first surface their
        // closing lit early so the inner's cover detection fires
        // and we backtrack out of the wrong branch quickly.
        //
        // Resolve the parent once (pointer-hash lookup), then index
        // into the precomputed children-id table for each child —
        // avoids one HashMap lookup per child and means the index
        // only needs entries for Sum/Prod nodes.  For
        // industrial-scale CNFs (millions of Lit leaves) that cuts
        // the `by_ptr` HashMap by ~75 %.
        let parent_id_opt = self.idx.id_of(parent);
        let parent_children_ids: Option<&[usize]> = parent_id_opt
            .map(|pid| self.idx.children_ids(pid));
        let mut annotated: Vec<(usize, &'a NNF, f64)> = base.into_iter()
            .map(|(i, c)| {
                let count = parent_children_ids
                    .map(|ids| self.counts.count_of(ids[i]))
                    .unwrap_or(f64::INFINITY);
                (i, c, count)
            })
            .collect();
        // Variance gate: skip the sort when sibling counts are within
        // 10^τ of each other (no meaningful reorder available).
        let only_counts: Vec<f64> = annotated.iter().map(|(_, _, c)| *c).collect();
        if !should_reorder_sum(&only_counts, self.sum_reorder_tau) {
            self.sum_ord_gate_skips += 1;
            return Some(annotated.into_iter().map(|(i, c, _)| (i, c)).collect());
        }
        annotated.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal));
        Some(annotated.into_iter().map(|(i, c, _)| (i, c)).collect())
    }

    fn prod_ord<'a>(&mut self, parent: &'a NNF, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        // Inner first — its propagation filter (e.g. SmartController
        // / CdclController) prunes alts whose lits are blocked by
        // the trail.  We further filter zero-count alts (provably
        // blocked by the prefix) and re-sort ascending.
        let base: Vec<(usize, &'a NNF)> = match self.inner.prod_ord(parent, children) {
            Some(v) => v,
            None    => children.iter().enumerate().collect(),
        };
        let base_len = base.len();
        // See `sum_ord` for the parent-id optimisation rationale.
        let parent_id_opt = self.idx.id_of(parent);
        let parent_children_ids: Option<&[usize]> = parent_id_opt
            .map(|pid| self.idx.children_ids(pid));
        let mut annotated: Vec<(usize, &'a NNF, f64)> = base.into_iter()
            .map(|(i, c)| {
                let count = parent_children_ids
                    .map(|ids| self.counts.count_of(ids[i]))
                    .unwrap_or(f64::INFINITY);
                (i, c, count)
            })
            .filter(|(_, _, c)| *c > 0.0)
            .collect();
        annotated.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal));
        if annotated.len() < base_len {
            self.prod_ord_filters += 1;
        }
        Some(annotated.into_iter().map(|(i, c, _)| (i, c)).collect())
    }

    fn path_count(&self) -> usize { self.inner.path_count() }
    fn covered_prefix_count(&self) -> usize { self.inner.covered_prefix_count() }
    fn uncovered_path_count(&self) -> usize { self.inner.uncovered_path_count() }
    fn paths_classified(&self) -> f64 {
        // Pre-leaf eff-pruning credit, surfaced for non-weighted
        // callers (the old publish path).  Weighted drivers use
        // `pre_leaf_pruning_credit()` (see below) instead, which is
        // the same value but a less-overloaded method name.
        self.pruned_paths_peak
    }

    fn pre_leaf_pruning_credit(&self) -> f64 {
        // Same value as `paths_classified()` above — paths the eff
        // layer's root-zero short-circuit killed without descending
        // to a leaf.  Disjoint from the cover-mult-weighted leaf
        // events the weighted driver counts on its own side.
        self.pruned_paths_peak
    }
    fn cdcl_conflict_count(&self) -> usize { self.inner.cdcl_conflict_count() }
    fn cdcl_restart_count(&self) -> usize { self.inner.cdcl_restart_count() }
    fn is_restart_pending(&self) -> bool { self.inner.is_restart_pending() }
    fn complete_restart(&mut self) {
        // CDCL restart clears the trail; our prefix tracking will
        // resync at the next `should_continue_on_prefix` call (we'll
        // see `prefix_literals.len()` shrink to 0).  At that point
        // `sync_to_prefix` runs its pop branch all the way down,
        // organically restoring `pruned_paths_current` to 0 by
        // popping every credit.  `pruned_paths_peak` persists across
        // restarts — it captures the high-water mark of any single
        // attempt, which is what the renderer's
        // "furthest progress" indicator surfaces.  **No manual reset
        // needed here** with the stack-based scheme; the previous
        // "blanket reset on restart" trick is no longer required and
        // would actually clobber genuine peak progress.
        self.inner.complete_restart();
    }
}

/// Arena-engine version of [`EffectiveCountWrapper`]'s controller
/// hooks.  Same root-zero pruning, same Sum-by-count re-ordering,
/// same Prod zero-count filter — but with arena-shaped signatures.
///
/// **Crucial layout invariant:** the arena's `NnfId` and this
/// wrapper's `EffectiveCountIndex` NodeId are numerically the same
/// integer for any given node, provided the index was built via
/// [`crate::dual::effective_count::EffectiveCountIndex::build_from_arena`]
/// (both walk the arena in identical DFS pre-order from the root).
/// So we can skip the `by_ptr` lookup entirely: a parent `NnfId`
/// IS its NodeId, and we index `idx.children_ids(parent_id)`
/// directly.  This is faster and uses no HashMap.
impl<Inner: crate::nnf_arena::ArenaPathSearchController + PathSearchController>
    crate::nnf_arena::ArenaPathSearchController for EffectiveCountWrapper<Inner>
{
    fn should_continue_on_prefix(
        &mut self,
        arena: &crate::nnf_arena::NnfArena,
        lits: &[Lit],
        prefix_prod_path: &ProdPath,
        is_complete: bool,
    ) -> Option<usize> {
        self.sync_to_prefix_arena(lits);
        // Root-zero prune (same as the NNF impl).
        if !is_complete && self.counts.count_of(self.idx.root_id()) == 0.0 {
            self.root_zero_prunes += 1;
            return Some(0);
        }
        crate::nnf_arena::ArenaPathSearchController::should_continue_on_prefix(
            &mut self.inner, arena, lits, prefix_prod_path, is_complete,
        )
    }

    fn sum_ord(
        &mut self,
        arena: &crate::nnf_arena::NnfArena,
        parent: crate::nnf_arena::NnfId,
        children: &[crate::nnf_arena::NnfId],
    ) -> Option<Vec<crate::nnf_arena::NnfId>> {
        // Inner first.
        let base: Vec<crate::nnf_arena::NnfId> = match
            crate::nnf_arena::ArenaPathSearchController::sum_ord(&mut self.inner, arena, parent, children)
        {
            Some(v) => v,
            None    => children.to_vec(),
        };
        // No `by_ptr` HashMap lookup — parent NnfId == NodeId by
        // construction.  Look up each child's count via the
        // precomputed `children_ids[parent_id]` slice; the i-th
        // entry there matches the i-th original child.
        let parent_children_ids = self.idx.children_ids(parent as usize);
        // Map original `NnfId` → original index → precomputed
        // count.  Hashing children's NnfIds into a small map keyed
        // by NnfId would be over-engineering for typical Sum
        // arities; a linear scan over `children` is fine.
        let mut annotated: Vec<(crate::nnf_arena::NnfId, f64)> = base.iter()
            .map(|&c| {
                let orig_idx = children.iter().position(|&id| id == c)
                    .expect("inner sum_ord returned a NnfId not in children");
                let cnt = self.counts.count_of(parent_children_ids[orig_idx]);
                (c, cnt)
            })
            .collect();
        // Variance gate — same logic as the NNF sum_ord path above.
        let only_counts: Vec<f64> = annotated.iter().map(|(_, c)| *c).collect();
        if !should_reorder_sum(&only_counts, self.sum_reorder_tau) {
            self.sum_ord_gate_skips += 1;
            return Some(annotated.into_iter().map(|(c, _)| c).collect());
        }
        annotated.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));
        Some(annotated.into_iter().map(|(c, _)| c).collect())
    }

    fn prod_ord(
        &mut self,
        arena: &crate::nnf_arena::NnfArena,
        parent: crate::nnf_arena::NnfId,
        children: &[crate::nnf_arena::NnfId],
    ) -> Option<Vec<crate::nnf_arena::NnfId>> {
        let base: Vec<crate::nnf_arena::NnfId> = match
            crate::nnf_arena::ArenaPathSearchController::prod_ord(&mut self.inner, arena, parent, children)
        {
            Some(v) => v,
            None    => children.to_vec(),
        };
        let base_len = base.len();
        let parent_children_ids = self.idx.children_ids(parent as usize);
        let mut annotated: Vec<(crate::nnf_arena::NnfId, f64)> = base.into_iter()
            .map(|c| {
                let orig_idx = children.iter().position(|&id| id == c)
                    .expect("inner prod_ord returned a NnfId not in children");
                let cnt = self.counts.count_of(parent_children_ids[orig_idx]);
                (c, cnt)
            })
            .filter(|(_, c)| *c > 0.0)
            .collect();
        annotated.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));
        if annotated.len() < base_len {
            self.prod_ord_filters += 1;
        }
        Some(annotated.into_iter().map(|(c, _)| c).collect())
    }
}

impl<Inner: PathSearchController> EffectiveCountWrapper<Inner> {
    /// Arena counterpart of `sync_to_prefix`.  `lits` is `&[Lit]`
    /// (owned) instead of `&Vec<&Lit>`, but logic is identical —
    /// same stack-based credit accounting (see `sync_to_prefix`'s
    /// doc comment for the rationale).
    fn sync_to_prefix_arena(&mut self, prefix_literals: &[Lit]) {
        // ── Pop branch — reverse the leaf updates AND decrement
        //    the per-push credit that lives at the top of the stack.
        while self.our_counted_len > prefix_literals.len() {
            let frame = self.frames.pop().expect("frames underflow");
            self.counts.pop_undo(frame);
            if let Some(credit) = self.pruning_credits.pop() {
                self.pruned_paths_current -= credit;
                if self.pruned_paths_current < 0.0 {
                    self.pruned_paths_current = 0.0;
                }
            }
            self.our_counted_len -= 1;
        }
        // ── Push branch — credit the marginal root drop, then
        //    refresh `peak` if `current` is now higher than ever.
        let root_id = self.idx.root_id();
        while self.our_counted_len < prefix_literals.len() {
            let old_root = self.counts.count_of(root_id);
            let lit: Lit = prefix_literals[self.our_counted_len].clone();
            let frame = self.counts.push(&self.idx, &lit);
            self.frames.push(frame);
            self.our_counted_len += 1;
            let new_root = self.counts.count_of(root_id);
            let drop = if new_root < old_root { old_root - new_root } else { 0.0 };
            self.pruning_credits.push(drop);
            self.pruned_paths_current += drop;
            if self.pruned_paths_current > self.pruned_paths_peak {
                self.pruned_paths_peak = self.pruned_paths_current;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dual::{solve_dual, BasicCoverController, Outcome, SearchMode};

    /// **End-to-end driver test for cover-mult-weighted accounting.**
    ///
    /// Runs a small UNSAT problem through the full dual-path stack
    /// (StateQueryWrapper → ProgressWrapper → EffectiveCountWrapper
    /// → CdclController) with a real progress atom attached.  After
    /// the search exits Exhausted, reads the atom and verifies the
    /// published value is in the legal range: `[0, total]`.  If the
    /// weighted-driver accounting ever regresses to overcount (as it
    /// did during initial Step-2 development before
    /// `pre_leaf_pruning_credit` was introduced to prevent
    /// event-count double-counting), this test catches it.
    #[test]
    fn dual_weighted_progress_never_overcounts() {
        use std::sync::Arc;
        use std::sync::atomic::AtomicU64;
        let matrix = crate::matrix::Matrix::try_from("a*a'").expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let total = nnf.path_count();
        assert!(total > 0.0 && total.is_finite(),
                "test formula must have a small finite path count; got {}", total);

        let progress = Arc::new(AtomicU64::new(0));
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            EffectivePathController::default().with_progress(progress.clone()),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat,
            "trivial-UNSAT formula should be detected by the dual");

        let published = f64::from_bits(progress.load(std::sync::atomic::Ordering::Relaxed));
        assert!(published >= 0.0,
            "published value must be non-negative; got {}", published);
        assert!(published <= total * 1.001,
            "published value {} must not exceed total path count {} (within 0.1% f64 slack)",
            published, total);
    }

    /// **Same end-to-end check, but for `CdclDualPathController`
    /// (no `EffectiveCountWrapper` in the stack).**  This is the
    /// regression test for the specific bug I introduced when
    /// `composite.paths_classified()` in the weighted driver was
    /// returning the default `path_count() as f64` (event count)
    /// for non-eff controller chains — causing the leaf events to be
    /// double-counted (once driver-side as cover-mult-weighted,
    /// once via the default impl).  Fix was the new
    /// `pre_leaf_pruning_credit` trait method (default 0.0).
    #[test]
    fn dual_weighted_cdcl_only_never_overcounts() {
        use std::sync::Arc;
        use std::sync::atomic::AtomicU64;
        use crate::dual::CdclDualPathController;
        let matrix = crate::matrix::Matrix::try_from("a*a'").expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let total = nnf.path_count();

        let progress = Arc::new(AtomicU64::new(0));
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            CdclDualPathController::default().with_progress(progress.clone()),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);

        let published = f64::from_bits(progress.load(std::sync::atomic::Ordering::Relaxed));
        assert!(published >= 0.0 && published <= total * 1.001,
            "CDCL-only weighted dual: published {} must be in [0, {}]",
            published, total);
    }

    /// **Invariant test for the stack-based credit accounting.**
    ///
    /// `pruned_paths_current` must always equal `R₀ - R_depth` (the
    /// telescoping sum), so it can never exceed `total_path_count`
    /// = `R₀`.  We construct a small NNF, simulate a sequence of
    /// pushes followed by pops, and check the invariant at every
    /// step.  This is the surgical guard against the
    /// "paths_so_far > total" regression.
    #[test]
    fn pruned_paths_current_equals_root_drop() {
        use crate::dual::effective_count::{EffectiveCountIndex, EffectiveCounts};
        // Sum(Lit(a), Prod(Lit(b), Lit(c)))  → 1 * (1+1) = 2 paths total.
        let nnf = NNF::Sum(vec![
            NNF::Lit(Lit::pos(0)),
            NNF::Prod(vec![NNF::Lit(Lit::pos(1)), NNF::Lit(Lit::pos(2))]),
        ]);
        let idx = EffectiveCountIndex::build(&nnf);
        let counts = EffectiveCounts::new(&idx);
        let inner = crate::controller::BacktrackWhenCoveredController::from(None);
        let mut w = EffectiveCountWrapper::new(inner, idx, counts);
        let r0 = w.counts.count_of(w.idx.root_id());
        assert_eq!(r0, 2.0, "empty-prefix root count should equal total paths");

        // Helper: build the &Vec<&Lit> shape `sync_to_prefix` expects.
        let a = Lit::pos(0);
        let b = Lit::pos(1);
        let c = Lit::pos(2);
        let na = Lit::neg(0);

        // Push [a] — should affect Lit(¬a) if any (none here),
        // so root unchanged at 2.0.  current = R₀ - R₁ = 0.
        let prefix1: Vec<&Lit> = vec![&a];
        w.sync_to_prefix(&prefix1);
        let r1 = w.counts.count_of(w.idx.root_id());
        assert!((w.pruned_paths_current - (r0 - r1)).abs() < 1e-9,
                "after push [a]: current={} ≠ R₀-R₁={}", w.pruned_paths_current, r0 - r1);
        assert!(w.pruned_paths_current <= r0,
                "current={} must never exceed total={}", w.pruned_paths_current, r0);

        // Push [a, b] — Lit(b)→1, others unchanged.  Still r2 = 2.0.
        let prefix2: Vec<&Lit> = vec![&a, &b];
        w.sync_to_prefix(&prefix2);
        let r2 = w.counts.count_of(w.idx.root_id());
        assert!((w.pruned_paths_current - (r0 - r2)).abs() < 1e-9,
                "after push [a,b]: current={} ≠ R₀-R₂={}", w.pruned_paths_current, r0 - r2);

        // Pop back to [a] — current must drop by exactly the credit
        // we added for `b`'s push.  invariant: current = R₀ - R₁.
        w.sync_to_prefix(&prefix1);
        let r1b = w.counts.count_of(w.idx.root_id());
        assert!((w.pruned_paths_current - (r0 - r1b)).abs() < 1e-9,
                "after pop to [a]: current={} ≠ R₀-R₁={}", w.pruned_paths_current, r0 - r1b);

        // Try the OTHER Prod alternative: push [a, c].  Without the
        // stack-based fix this would have double-credited the
        // pruning that the (popped) `b` push had charged.  With it,
        // current is exactly R₀ - R_depth at this new prefix.
        let prefix3: Vec<&Lit> = vec![&a, &c];
        w.sync_to_prefix(&prefix3);
        let r3 = w.counts.count_of(w.idx.root_id());
        assert!((w.pruned_paths_current - (r0 - r3)).abs() < 1e-9,
                "after [a,c]: current={} ≠ R₀-R₃={}", w.pruned_paths_current, r0 - r3);
        assert!(w.pruned_paths_current <= r0,
                "current={} must never exceed total={} even after backtrack+retry",
                w.pruned_paths_current, r0);

        // Push a conflicting lit: [a, c, ¬a].  Root drops to 0
        // (every path now blocked).  current must equal r0 (since
        // R_depth = 0).  Peak must equal r0.
        let prefix4: Vec<&Lit> = vec![&a, &c, &na];
        w.sync_to_prefix(&prefix4);
        let r4 = w.counts.count_of(w.idx.root_id());
        assert_eq!(r4, 0.0, "[a,c,¬a] should zero the root");
        assert!((w.pruned_paths_current - r0).abs() < 1e-9,
                "fully-blocked prefix: current={} should equal total={}", w.pruned_paths_current, r0);
        assert!(w.pruned_paths_peak >= w.pruned_paths_current,
                "peak={} must be ≥ current={}", w.pruned_paths_peak, w.pruned_paths_current);

        // Pop all the way back — current returns to 0, peak holds.
        let empty: Vec<&Lit> = vec![];
        w.sync_to_prefix(&empty);
        assert!(w.pruned_paths_current.abs() < 1e-9,
                "empty prefix: current={} should be 0", w.pruned_paths_current);
        assert!((w.pruned_paths_peak - r0).abs() < 1e-9,
                "peak={} should still equal total={}", w.pruned_paths_peak, r0);
    }

    #[test]
    fn effective_detects_satisfiable() {
        let matrix = crate::matrix::Matrix::try_from("a + b").expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            EffectivePathController::default(),
            SearchMode::Satisfiable,
        );
        assert!(matches!(outcome, Outcome::Sat(_)));
    }

    #[test]
    fn effective_detects_unsatisfiable() {
        let matrix = crate::matrix::Matrix::try_from("a*a'").expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            EffectivePathController::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }

    /// On the worked example formula (3-bit plus with a=b=3, c=6 →
    /// a unique SAT model), confirm the controller agrees with the
    /// existing solver.
    #[test]
    fn effective_solves_3bit_plus_with_pinning() {
        // Hand-rolled 3-bit add formula with input pinning.
        // (c_0=a_0⊕b_0)(c_1=a_1⊕b_1⊕(a_0 b_0))(c_2=a_2⊕b_2⊕carry₂)(no-overflow)
        // a=011 b=011 c=110 → a₂=0 a₁=1 a₀=1, b₂=0 b₁=1 b₀=1, c₂=1 c₁=1 c₀=0
        let formula = "(c_0 = a_0 ⊕ b_0) \
                       (c_1 = a_1 ⊕ b_1 ⊕ (a_0 b_0)) \
                       (c_2 = a_2 ⊕ b_2 ⊕ (a_0 b_0 (a_1 + b_1) + a_1 b_1)) \
                       (a_0 b_0 (a_1 + b_1) (a_2 + b_2) + a_1 b_1 (a_2 + b_2) + a_2 b_2)' \
                       a_2' a_1 a_0 b_2' b_1 b_0 c_2 c_1 c_0'";
        let matrix = crate::matrix::Matrix::try_from(formula).expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            EffectivePathController::default(),
            SearchMode::Satisfiable,
        );
        assert!(matches!(outcome, Outcome::Sat(_)),
            "3+3=6 should be SAT under EffectivePathController");
    }
}
