//! `BasicCoverController` — Phase 1 cover-search controller.
//!
//! Pulls pairs from the pool in arrival order, registers each one
//! against [`crate::dual::BasicCoverState`].  Doesn't claim
//! completeness — termination is the path-search side's job in
//! Phase 1.  This exists to validate the framework's plumbing:
//! every pair B emits travels through the pool and lands in A's
//! state, so future heuristics have a state to consult.

use crate::dual::{BasicCoverState, CoverSearchController, PairPool};
use crate::matrix::NNF;

/// Phase 1 baseline.  Processes pairs in FIFO order and never claims
/// the cover is complete.
pub struct BasicCoverController {
    /// Next index to pull from the pool.
    cursor: usize,
}

impl Default for BasicCoverController {
    fn default() -> Self { Self::new() }
}

impl BasicCoverController {
    pub fn new() -> Self {
        Self { cursor: 0 }
    }

    /// Index of the next pair this controller will request.  Useful
    /// for tests to confirm A has caught up.
    pub fn cursor(&self) -> usize { self.cursor }
}

impl CoverSearchController for BasicCoverController {
    type State = BasicCoverState;

    fn create_state(&self, nnf: &NNF) -> Self::State {
        BasicCoverState::new(nnf)
    }

    fn next_pair_index(&mut self, pool: &PairPool, _state: &Self::State) -> Option<usize> {
        if self.cursor < pool.len() {
            let idx = self.cursor;
            self.cursor += 1;
            Some(idx)
        } else {
            None
        }
    }

    fn register_pair(&mut self, idx: usize, pool: &PairPool, state: &mut Self::State) -> bool {
        if let Some(pair) = pool.get(idx) {
            state.add_pair(pair);
            true
        } else {
            false
        }
    }

    fn is_complete(&mut self, _state: &mut Self::State) -> bool {
        // Phase 1: never claim UNSAT from the cover side.  B's
        // exhaustion is the termination authority.
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dual::{BasicCoverState, CoverState, PairPool};

    #[test]
    fn cursor_advances_and_pairs_land_in_state() {
        // Use a tiny flat-Sum-of-Prods NNF so BasicCoverState
        // accepts pairs without complaint.
        use crate::matrix::{Lit, NNF};
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![NNF::Lit(Lit::pos(0)), NNF::Lit(Lit::pos(1))]),
            NNF::Prod(vec![NNF::Lit(Lit::neg(0)), NNF::Lit(Lit::neg(1))]),
        ]);
        let pool = PairPool::new();
        let mut state = BasicCoverState::new(&nnf);
        let mut ctrl = BasicCoverController::new();

        // Empty pool → no pair to process.
        assert_eq!(ctrl.next_pair_index(&pool, &state), None);

        // Push two pairs; controller picks them up in order.
        let p1 = pool.push((vec![0, 0], vec![1, 0]));
        let p2 = pool.push((vec![0, 1], vec![1, 1]));
        assert_eq!(p1, 0);
        assert_eq!(p2, 1);

        let next = ctrl.next_pair_index(&pool, &state).unwrap();
        assert_eq!(next, 0);
        assert!(ctrl.register_pair(next, &pool, &mut state));

        let next = ctrl.next_pair_index(&pool, &state).unwrap();
        assert_eq!(next, 1);
        assert!(ctrl.register_pair(next, &pool, &mut state));

        // Cursor caught up.
        assert_eq!(ctrl.next_pair_index(&pool, &state), None);
        assert_eq!(state.registered_pair_count(), 2);
    }
}
