//! `BasicDualPathController` — dual-framework path-search controller.
//!
//! Wraps [`crate::controller::BacktrackWhenCoveredController`] with two
//! dual-specific extensions:
//!
//! 1. Every `PathsClass::Covered` detection is translated into a
//!    `Pair` push on the shared `PairPool`.  The first
//!    `PathsClass::Uncovered` event terminates the search.
//! 2. (Phase 2) On every step, query A's `CoverState` for whether
//!    the current `ProdPath` is already covered by some pair A has
//!    registered.  If so, backtrack early — saving the work of
//!    descending into a subtree we already know is dead.
//!
//! The state-query layer is a thin
//! [`PathSearchController`] adapter ([`StateQueryWrapper`]) that
//! sits between the DFS engine and the inner
//! `BacktrackWhenCoveredController`.  Its instrumentation counters
//! (`query_count`, `prune_count`) are printed on drop when
//! `CDCL_INSTR=1` is set in the environment, so Phase 2's pruning
//! contribution can be measured.

use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};

use crate::controller::{BacktrackWhenCoveredController, PathSearchController};
use crate::dual::{
    BasicCoverState, CoverState, DualPathSearchController, PairPool, PathOutcome, SearchMode,
};
use crate::dual::wrapper::{StateQueryWrapper, run_dfs_with_restarts};
use crate::matrix::{NNF, PathParams, PathsClass, ProdPath};

/// Dual-framework path-search controller.
pub struct BasicDualPathController<S: CoverState = BasicCoverState> {
    _state: std::marker::PhantomData<S>,
}

impl<S: CoverState> Default for BasicDualPathController<S> {
    fn default() -> Self { Self::new() }
}

impl<S: CoverState> BasicDualPathController<S> {
    pub fn new() -> Self {
        Self { _state: std::marker::PhantomData }
    }
}

impl<S: CoverState + 'static> DualPathSearchController for BasicDualPathController<S> {
    type State = S;

    fn run(
        self,
        nnf: &NNF,
        _mode: SearchMode,
        pool: Arc<PairPool>,
        state: Arc<Mutex<Self::State>>,
        cancel: Arc<AtomicBool>,
    ) -> PathOutcome {
        // Holds the first uncovered path the search finds.
        let uncovered: Arc<Mutex<Option<ProdPath>>> = Arc::new(Mutex::new(None));

        // Inner on_class: pipes Covered events into the pool, stops
        // on the first Uncovered event, honours cancellation.
        let on_class = {
            let pool = pool.clone();
            let uncovered = uncovered.clone();
            let cancel = cancel.clone();
            move |class: PathsClass, _hit_limit: bool| -> bool {
                if cancel.load(Ordering::SeqCst) {
                    return false;
                }
                match class {
                    PathsClass::Covered(cpp) => {
                        pool.push(cpp.cover);
                        true
                    }
                    PathsClass::Uncovered(pp) => {
                        let mut slot = uncovered.lock().unwrap();
                        if slot.is_none() {
                            *slot = Some(pp);
                        }
                        false
                    }
                }
            }
        };

        // Stop after the first uncovered path; let coverage
        // detection run unbounded.
        let params = PathParams {
            uncovered_path_limit: 1,
            paths_class_limit:    usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover:             false,
        };

        let inner = <BacktrackWhenCoveredController<_> as PathSearchController>::with_on_class(
            Some(params),
            on_class,
        );
        let mut composite = StateQueryWrapper::new(inner, state, cancel);

        // Drive with the restart loop (no-op for Basic — it never
        // requests a restart — but keeps the call shape uniform
        // with Smart and CDCL).
        run_dfs_with_restarts(&mut composite, nnf, &*uncovered)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dual::{BasicCoverController, Outcome, solve_dual, SearchMode};

    #[test]
    fn detects_satisfiable_via_uncovered_path() {
        // `(a + b)` complement = `a' * b'`.  Path: pick a', pick b'
        // — no complementary pair, so SAT.
        let matrix = crate::matrix::Matrix::try_from("a + b").expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            BasicDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert!(matches!(outcome, Outcome::Sat(_)));
    }

    #[test]
    fn detects_unsatisfiable_via_full_cover() {
        let matrix = crate::matrix::Matrix::try_from("a * a'").expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            BasicDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }

    /// Pre-register pairs in the state and confirm that
    /// `StateQueryWrapper` reports prunes.  This is the Phase 2
    /// state-query layer earning its keep.
    #[test]
    fn state_query_layer_prunes_when_state_already_covers() {
        use crate::dual::flat::mine_pairs;
        let matrix = crate::matrix::Matrix::try_from("(a + b)*(a' + b')")
            .expect("matrix");
        let nnf = matrix.nnf_complement.clone();

        // Pre-populate the state with every cross-clause pair
        // (so the state knows about every cover before B starts).
        let mut state = BasicCoverState::new(&nnf);
        for pair in mine_pairs(&nnf) {
            state.add_pair(pair);
        }

        // Build the wrapper directly (bypassing the run() helper)
        // so we can access the instrumentation counters after the
        // DFS completes.
        let pool = std::sync::Arc::new(crate::dual::PairPool::new());
        let cancel = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));

        let uncov: std::sync::Arc<std::sync::Mutex<Option<crate::matrix::ProdPath>>> =
            std::sync::Arc::new(std::sync::Mutex::new(None));
        let on_class = {
            let pool = pool.clone();
            let uncov = uncov.clone();
            move |class: crate::matrix::PathsClass, _hl: bool| -> bool {
                match class {
                    crate::matrix::PathsClass::Covered(cpp) => {
                        pool.push(cpp.cover); true
                    }
                    crate::matrix::PathsClass::Uncovered(pp) => {
                        let mut s = uncov.lock().unwrap();
                        if s.is_none() { *s = Some(pp); }
                        false
                    }
                }
            }
        };
        let inner = <BacktrackWhenCoveredController<_> as PathSearchController>::with_on_class(
            Some(crate::matrix::PathParams {
                uncovered_path_limit: 1, paths_class_limit: usize::MAX,
                covered_prefix_limit: usize::MAX, no_cover: false,
            }),
            on_class,
        );
        let state_arc = std::sync::Arc::new(std::sync::Mutex::new(state));
        let mut wrapper = StateQueryWrapper::new(inner, state_arc, cancel);
        nnf.for_each_path_prefix_with_controller(&mut wrapper);

        assert!(wrapper.state_query_count > 0,
            "expected at least one state query during search");
        // For an UNSAT formula with pre-loaded covers, prunes
        // should fire — every covered prefix B explores has a
        // matching pre-registered pair.  We assert >0 (not a
        // specific count) because the relative ordering of B's
        // local detection vs the wrapper's state-query is
        // implementation-detail-y.
        assert!(wrapper.state_prune_count > 0,
            "expected at least one state-driven prune (had {} queries, {} prunes)",
            wrapper.state_query_count, wrapper.state_prune_count);
    }

    #[test]
    fn pairs_emitted_to_pool_during_search() {
        use crate::dual::PairPool;
        let matrix = crate::matrix::Matrix::try_from("(a + b)*(a' + b)*(a + b')*(a' + b')")
            .expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let pool = PairPool::new();
        let state: Arc<Mutex<BasicCoverState>> = Arc::new(Mutex::new(BasicCoverState::new(&nnf)));
        let cancel = Arc::new(AtomicBool::new(false));
        let ctrl = BasicDualPathController::<BasicCoverState>::default();
        let outcome = ctrl.run(&nnf, SearchMode::Satisfiable,
                               pool.clone(), state, cancel);
        assert!(matches!(outcome, PathOutcome::Exhausted));
        assert!(pool.len() > 0,
            "expected at least one pair in the pool after exhaustive UNSAT search");
    }
}
