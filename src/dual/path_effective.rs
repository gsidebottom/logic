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

use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};

use crate::controller::{CdclController, PathSearchController};
use crate::dual::{
    BasicCoverState, CoverState, DualPathSearchController, PairPool, PathOutcome, SearchMode,
};
use crate::dual::effective_count::{DeltaFrame, EffectiveCountIndex, EffectiveCounts};
use crate::dual::wrapper::{StateQueryWrapper, run_dfs_with_restarts};
use crate::matrix::{Lit, NNF, PathParams, PathPrefix, PathsClass, ProdPath};

pub struct EffectivePathController<S: CoverState = BasicCoverState> {
    _state: std::marker::PhantomData<S>,
}

impl<S: CoverState> Default for EffectivePathController<S> {
    fn default() -> Self { Self::new() }
}

impl<S: CoverState> EffectivePathController<S> {
    pub fn new() -> Self {
        Self { _state: std::marker::PhantomData }
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

        let on_class = {
            let pool = pool.clone();
            let uncovered = uncovered.clone();
            let cancel = cancel.clone();
            move |class: PathsClass, _hit_limit: bool| -> bool {
                if cancel.load(Ordering::SeqCst) { return false; }
                match class {
                    PathsClass::Covered(cpp) => { pool.push(cpp.cover); true }
                    PathsClass::Uncovered(pp) => {
                        let mut slot = uncovered.lock().unwrap();
                        if slot.is_none() { *slot = Some(pp); }
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
        let counted = EffectiveCountWrapper::new(inner, idx, counts);
        let mut composite = StateQueryWrapper::new(counted, state, cancel);
        run_dfs_with_restarts(&mut composite, nnf, &*uncovered)
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
}

impl<Inner: PathSearchController> EffectiveCountWrapper<Inner> {
    pub fn new(inner: Inner, idx: EffectiveCountIndex, counts: EffectiveCounts) -> Self {
        Self {
            inner, idx, counts,
            frames: Vec::new(),
            our_counted_len: 0,
            root_zero_prunes: 0,
            prod_ord_filters: 0,
        }
    }

    fn sync_to_prefix(&mut self, prefix_literals: &Vec<&Lit>) {
        // Pop frames for popped lits.
        while self.our_counted_len > prefix_literals.len() {
            let frame = self.frames.pop().expect("frames underflow");
            self.counts.pop_undo(frame);
            self.our_counted_len -= 1;
        }
        // Push frames for new lits.
        while self.our_counted_len < prefix_literals.len() {
            let lit: Lit = prefix_literals[self.our_counted_len].clone();
            let frame = self.counts.push(&self.idx, &lit);
            self.frames.push(frame);
            self.our_counted_len += 1;
        }
    }
}

impl<Inner: PathSearchController> Drop for EffectiveCountWrapper<Inner> {
    fn drop(&mut self) {
        if std::env::var("CDCL_INSTR").is_ok() {
            eprintln!("c [dual.effective] root_zero_prunes={} prod_ord_filters={}",
                      self.root_zero_prunes, self.prod_ord_filters);
        }
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

    fn sum_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        // Start from inner's order (None ⇒ declaration order).
        let base: Vec<(usize, &'a NNF)> = match self.inner.sum_ord(children) {
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
        let mut annotated: Vec<(usize, &'a NNF, f64)> = base.into_iter()
            .map(|(i, c)| {
                let count = self.idx.id_of(c)
                    .map(|nid| self.counts.count_of(nid))
                    .unwrap_or(f64::INFINITY);
                (i, c, count)
            })
            .collect();
        annotated.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal));
        Some(annotated.into_iter().map(|(i, c, _)| (i, c)).collect())
    }

    fn prod_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        // Inner first — its propagation filter (e.g. SmartController
        // / CdclController) prunes alts whose lits are blocked by
        // the trail.  We further filter zero-count alts (provably
        // blocked by the prefix) and re-sort ascending.
        let base: Vec<(usize, &'a NNF)> = match self.inner.prod_ord(children) {
            Some(v) => v,
            None    => children.iter().enumerate().collect(),
        };
        let base_len = base.len();
        let mut annotated: Vec<(usize, &'a NNF, f64)> = base.into_iter()
            .map(|(i, c)| {
                let count = self.idx.id_of(c)
                    .map(|nid| self.counts.count_of(nid))
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
    fn paths_classified(&self) -> f64 { self.inner.paths_classified() }
    fn is_restart_pending(&self) -> bool { self.inner.is_restart_pending() }
    fn complete_restart(&mut self) {
        // CDCL restart clears the trail; our prefix tracking will
        // resync at the next `should_continue_on_prefix` call (we'll
        // see prefix_literals.len() shrink to 0).
        self.inner.complete_restart();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dual::{BasicCoverController, Outcome, SearchMode, solve_dual};

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
