//! `BddBansCoverController` — cover-search side using a BDD
//! representation of the uncovered set.
//!
//! Same heap-based greedy max-cover selection as
//! [`crate::dual::GreedyMaxCoverController`].  Differs in
//! `is_complete`: the controller calls
//! [`crate::dual::cover_state_bdd::BddBansCoverState::check_complete_with_bdd`]
//! periodically; that method merges any unmerged pairs into the
//! `valid_bdd` and returns `valid_bdd.is_false()`.
//!
//! Compared to [`crate::dual::CnfBansCoverController`] (the
//! CaDiCaL variant), this controller's per-check cost is the BDD
//! merge time (linear in the new pairs) — there's no separate
//! solve-from-scratch pass.  The trade-off is BDD memory: bad
//! variable orderings can blow the BDD up.

use std::collections::BinaryHeap;

use crate::dual::cover_state_bdd::BddBansCoverState;
use crate::dual::flat::{mine_pairs, pair_box_size};
use crate::dual::{CoverSearchController, PairPool};
use crate::matrix::NNF;

pub struct BddBansCoverController {
    arities: Vec<usize>,
    heap: BinaryHeap<(u128, usize, usize)>,
    next_scan: usize,
    pairs_since_check: usize,
    check_threshold: usize,
    min_pairs_before_first_check: usize,
    registered: usize,
    checks_performed: usize,
    cached_complete: bool,
}

impl BddBansCoverController {
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

    pub fn with_check_threshold(mut self, t: usize) -> Self {
        self.check_threshold = t.max(1);
        self
    }
    pub fn with_min_pairs_before_first_check(mut self, n: usize) -> Self {
        self.min_pairs_before_first_check = n;
        self
    }

    pub fn registered_count(&self) -> usize { self.registered }
    pub fn checks_performed(&self) -> usize { self.checks_performed }
}

impl Default for BddBansCoverController {
    fn default() -> Self { Self::new() }
}

impl CoverSearchController for BddBansCoverController {
    type State = BddBansCoverState;

    fn create_state(&self, nnf: &NNF) -> Self::State {
        BddBansCoverState::new(nnf)
    }

    fn seed_pool(&self, nnf: &NNF, pool: &PairPool) {
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
        if self.cached_complete { return true; }
        if self.registered < self.min_pairs_before_first_check {
            return false;
        }
        if self.pairs_since_check < self.check_threshold {
            return false;
        }
        self.pairs_since_check = 0;
        let new_threshold = (self.check_threshold * 3) / 2;
        self.check_threshold = new_threshold.max(self.check_threshold + 1);

        self.checks_performed += 1;
        let complete = state.check_complete_with_bdd();
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
        BasicDualPathController, Outcome, SearchMode, solve_dual,
    };
    use crate::matrix::{Lit, NNF};

    fn lit_p(v: u32) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> NNF { NNF::Lit(Lit::neg(v)) }

    #[test]
    fn bdd_bans_solves_simple_unsat() {
        let nnf = NNF::Sum(vec![lit_n(0), lit_p(0)]);
        let outcome = solve_dual(
            &nnf,
            BddBansCoverController::new()
                .with_min_pairs_before_first_check(1)
                .with_check_threshold(1),
            BasicDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }

    #[test]
    fn bdd_bans_doesnt_falsely_claim_unsat_on_sat() {
        let nnf = NNF::Sum(vec![NNF::Prod(vec![lit_p(0), lit_n(1)])]);
        let outcome = solve_dual(
            &nnf,
            BddBansCoverController::new()
                .with_min_pairs_before_first_check(0)
                .with_check_threshold(1),
            BasicDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert!(matches!(outcome, Outcome::Sat(_)));
    }

    #[test]
    fn bdd_bans_solves_multiclause_unsat() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
            lit_p(0),
            lit_p(1),
        ]);
        let outcome = solve_dual(
            &nnf,
            BddBansCoverController::new()
                .with_min_pairs_before_first_check(1)
                .with_check_threshold(1),
            BasicDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }
}
