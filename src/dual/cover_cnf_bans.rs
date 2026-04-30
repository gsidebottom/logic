//! `CnfBansCoverController` — the cover-search side that uses
//! [`crate::dual::cover_state_cnf::CnfBansCoverState`] and
//! periodically calls CaDiCaL to check whether every path is
//! covered.
//!
//! Pair selection is the same heap-based greedy max-cover scheme
//! [`GreedyMaxCoverController`] uses — largest box first, FIFO on
//! ties.  The controller maintains a counter of pairs registered
//! since the last CaDiCaL invocation; when the counter exceeds the
//! current `check_threshold`, it triggers a check.  After each
//! check the threshold is multiplied by `1.5` (geometric backoff)
//! so the per-check cost amortizes as the search progresses.
//!
//! The first check is gated until at least
//! `min_pairs_before_first_check` pairs have been registered —
//! avoids invoking CaDiCaL on a tiny ban set where it's
//! pointlessly answering "SAT, of course".

use std::collections::BinaryHeap;

use crate::dual::cover_state_cnf::CnfBansCoverState;
use crate::dual::flat::{mine_pairs, pair_box_size};
use crate::dual::{CoverSearchController, PairPool};
use crate::matrix::NNF;

pub struct CnfBansCoverController {
    arities: Vec<usize>,
    heap: BinaryHeap<(u128, usize, usize)>,
    next_scan: usize,
    /// Number of pairs registered since the last CaDiCaL check (or
    /// since the start, before the first check).
    pairs_since_check: usize,
    /// Threshold for the next CaDiCaL invocation.  Grows
    /// geometrically after each check.
    check_threshold: usize,
    /// Don't run CaDiCaL until at least this many pairs have been
    /// registered total.
    min_pairs_before_first_check: usize,
    /// Total pairs registered (cumulative).
    registered: usize,
    /// How many CaDiCaL checks have been performed (diagnostics).
    checks_performed: usize,
    /// Was the last check's outcome `true`?  Cached for a single
    /// short-circuit: once we've decided "complete", subsequent
    /// `is_complete` calls skip the SAT solver.
    cached_complete: bool,
}

impl CnfBansCoverController {
    pub fn new() -> Self {
        Self {
            arities: Vec::new(),
            heap: BinaryHeap::new(),
            next_scan: 0,
            pairs_since_check: 0,
            check_threshold: 1024,
            min_pairs_before_first_check: 256,
            registered: 0,
            checks_performed: 0,
            cached_complete: false,
        }
    }

    /// Override the initial CaDiCaL check threshold.  Default 1024
    /// pairs.  Smaller thresholds invoke CaDiCaL more often; larger
    /// thresholds amortize better.
    pub fn with_check_threshold(mut self, t: usize) -> Self {
        self.check_threshold = t.max(1);
        self
    }

    /// Override the minimum pair count before the first CaDiCaL
    /// check.  Default 256.  Useful for tests that want to exercise
    /// the check path on small inputs.
    pub fn with_min_pairs_before_first_check(mut self, n: usize) -> Self {
        self.min_pairs_before_first_check = n;
        self
    }

    pub fn registered_count(&self) -> usize { self.registered }
    pub fn checks_performed(&self) -> usize { self.checks_performed }
}

impl Default for CnfBansCoverController {
    fn default() -> Self { Self::new() }
}

impl CoverSearchController for CnfBansCoverController {
    type State = CnfBansCoverState;

    fn create_state(&self, nnf: &NNF) -> Self::State {
        CnfBansCoverState::new(nnf)
    }

    fn seed_pool(&self, nnf: &NNF, pool: &PairPool) {
        // Same static mining as Greedy: every cross-clause
        // complementary pair goes into the pool at startup.
        for pair in mine_pairs(nnf) {
            pool.push(pair);
        }
    }

    fn next_pair_index(&mut self, pool: &PairPool, state: &Self::State) -> Option<usize> {
        if self.arities.is_empty() && !state.arities().is_empty() {
            self.arities = state.arities().to_vec();
        }
        let pool_len = pool.len();
        while self.next_scan < pool_len {
            let i = self.next_scan;
            self.next_scan += 1;
            let Some(pair) = pool.get(i) else { continue; };
            let size = match pair_to_triggers(&pair) {
                Some(t) if !self.arities.is_empty() => pair_box_size(&t, &self.arities),
                _ => 0,
            };
            let tiebreak = usize::MAX - i;
            self.heap.push((size, tiebreak, i));
        }
        self.heap.pop().map(|(_, _, i)| i)
    }

    fn register_pair(&mut self, idx: usize, pool: &PairPool, state: &mut Self::State) -> bool {
        if let Some(pair) = pool.get(idx) {
            state.add_pair(pair);
            self.registered += 1;
            self.pairs_since_check += 1;
            if self.arities.is_empty() && !state.arities().is_empty() {
                self.arities = state.arities().to_vec();
            }
            true
        } else {
            false
        }
    }

    fn is_complete(&mut self, state: &mut Self::State) -> bool {
        // If we've already decided "complete", stay there — no
        // need to invoke CaDiCaL again.
        if self.cached_complete { return true; }
        // Don't bother checking until there are enough bans for
        // CaDiCaL to plausibly say UNSAT.
        if self.registered < self.min_pairs_before_first_check {
            return false;
        }
        // Backoff: only check every `check_threshold` registrations.
        if self.pairs_since_check < self.check_threshold {
            return false;
        }
        self.pairs_since_check = 0;
        // Geometric backoff so checks get rarer as the search runs.
        // Cap at 4× the original to avoid waiting too long.
        let new_threshold = (self.check_threshold * 3) / 2;
        self.check_threshold = new_threshold.max(self.check_threshold + 1);

        self.checks_performed += 1;
        let complete = state.check_complete_with_cadical();
        if complete {
            self.cached_complete = true;
        }
        complete
    }
}

fn pair_to_triggers(pair: &crate::matrix::Pair) -> Option<[(usize, usize); 2]> {
    let extract = |pos: &crate::matrix::Position| -> Option<(usize, usize)> {
        match pos.len() {
            1 => Some((pos[0], 0)),
            2 => Some((pos[0], pos[1])),
            _ => None,
        }
    };
    Some([extract(&pair.0)?, extract(&pair.1)?])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dual::{
        BasicDualPathController, CnfBansCoverController as _,
        CoverSearchController, Outcome, SearchMode, solve_dual,
    };
    use crate::matrix::{Lit, NNF};

    fn lit_p(v: u32) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> NNF { NNF::Lit(Lit::neg(v)) }

    /// End-to-end: solve a small UNSAT formula via dual with the
    /// CNF-bans cover controller; confirm A's CaDiCaL declares
    /// UNSAT (the framework's first non-trivial use of A's
    /// completeness signal).
    #[test]
    fn cnf_bans_solves_simple_unsat() {
        let nnf = NNF::Sum(vec![lit_n(0), lit_p(0)]);
        let outcome = solve_dual(
            &nnf,
            CnfBansCoverController::new()
                .with_min_pairs_before_first_check(1)
                .with_check_threshold(1),
            BasicDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }

    /// SAT formulas: A's CaDiCaL should NEVER declare UNSAT, B
    /// finds the uncovered path.
    #[test]
    fn cnf_bans_doesnt_falsely_claim_unsat_on_sat() {
        let nnf = NNF::Sum(vec![NNF::Prod(vec![lit_p(0), lit_n(1)])]);
        let outcome = solve_dual(
            &nnf,
            CnfBansCoverController::new()
                .with_min_pairs_before_first_check(0)
                .with_check_threshold(1),
            BasicDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert!(matches!(outcome, Outcome::Sat(_)));
    }

    /// Larger UNSAT with multi-alt clauses.
    #[test]
    fn cnf_bans_solves_multiclause_unsat() {
        // (a + b) ∧ (¬a) ∧ (¬b)  — UNSAT.
        // Complement: Sum(Prod(¬a,¬b), a, b)
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
            lit_p(0),
            lit_p(1),
        ]);
        let outcome = solve_dual(
            &nnf,
            CnfBansCoverController::new()
                .with_min_pairs_before_first_check(1)
                .with_check_threshold(1),
            BasicDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }
}
