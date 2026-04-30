//! `CdclDualPathController` — dual-framework path-search controller
//! using [`crate::controller::CdclController`] as the inner.
//!
//! Same shape as [`crate::dual::SmartDualPathController`], but with
//! the full CDCL stack: 1UIP conflict analysis, learned clauses,
//! Luby restarts, VSIDS variable activity, phase saving, and
//! LBD-based learned-clause deletion.  Pairs from
//! `PathsClass::Covered` events still flow into the shared pool;
//! CDCL's learned clauses themselves are not (yet) shared with A
//! because the dual framework's `Pair` type is exactly two
//! positions and doesn't generalise to k-ary cubes — that's
//! flagged for Phase 4 (k-tuple constraints).
//!
//! The state-query layer wraps the CDCL controller so A's cover
//! state can prune the DFS at any level, on top of CDCL's own
//! propagation and conflict-driven prunes.

use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};

use crate::controller::CdclController;
use crate::dual::{
    BasicCoverState, CoverState, DualPathSearchController, PairPool, PathOutcome, SearchMode,
};
use crate::dual::wrapper::{StateQueryWrapper, run_dfs_with_restarts};
use crate::matrix::{NNF, PathParams, PathsClass, ProdPath};

pub struct CdclDualPathController<S: CoverState = BasicCoverState> {
    _state: std::marker::PhantomData<S>,
}

impl<S: CoverState> Default for CdclDualPathController<S> {
    fn default() -> Self { Self::new() }
}

impl<S: CoverState> CdclDualPathController<S> {
    pub fn new() -> Self {
        Self { _state: std::marker::PhantomData }
    }
}

impl<S: CoverState + 'static> DualPathSearchController for CdclDualPathController<S> {
    type State = S;

    fn run(
        self,
        nnf: &NNF,
        _mode: SearchMode,
        pool: Arc<PairPool>,
        state: Arc<Mutex<Self::State>>,
        cancel: Arc<AtomicBool>,
    ) -> PathOutcome {
        let uncovered: Arc<Mutex<Option<ProdPath>>> = Arc::new(Mutex::new(None));

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

        let params = PathParams {
            uncovered_path_limit: 1,
            paths_class_limit:    usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover:             false,
        };

        let inner = CdclController::for_nnf_with_cover(nnf, Some(params), on_class);
        let mut composite = StateQueryWrapper::new(inner, state, cancel);
        run_dfs_with_restarts(&mut composite, nnf, &*uncovered)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dual::{BasicCoverController, GreedyMaxCoverController, Outcome, solve_dual, SearchMode};

    #[test]
    fn cdcl_b_detects_satisfiable() {
        let matrix = crate::matrix::Matrix::try_from("a + b").expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            CdclDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert!(matches!(outcome, Outcome::Sat(_)));
    }

    #[test]
    fn cdcl_b_detects_unsatisfiable() {
        let matrix = crate::matrix::Matrix::try_from("a*a'").expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            CdclDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }

    #[test]
    fn cdcl_b_with_greedy_a() {
        let text = "(a + b)*(a' + b)*(a + b')*(a' + b')";
        let matrix = crate::matrix::Matrix::try_from(text).expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let outcome = solve_dual(
            &nnf,
            GreedyMaxCoverController::default(),
            CdclDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }
}
