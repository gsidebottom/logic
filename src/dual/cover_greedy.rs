//! `GreedyMaxCoverController` — picks the unprocessed pair with
//! the largest cover-box first.
//!
//! ## Heuristic
//!
//! For a flat Sum-of-Prods matrix with clause arities
//! `[k_0, ..., k_{n-1}]`, a pair `((i, a), (j, b))` covers exactly
//! the box `{ x : x_i = a ∧ x_j = b }` of size
//! `Π_{c ≠ i, j} k_c`.  Picking pairs with the largest boxes first
//! is the simplest greedy approximation to set-cover.  It's an
//! approximation: the true max-cover-step picks the pair whose box
//! has the largest *intersection with the still-uncovered region*,
//! which requires reasoning about overlap with previously-registered
//! boxes.  The straight box-size score is cheap and well-behaved in
//! practice for greedy covers.
//!
//! ## Phase 4: heap-based selection
//!
//! Selection uses a [`std::collections::BinaryHeap`] keyed by
//! `(box_size, FIFO-tiebreaker, pair_idx)`.  Each pool entry is
//! pushed onto the heap exactly once (lazily, at the next
//! `next_pair_index` call after it appeared in the pool); `pop`
//! returns the highest-size entry in `O(log N)`.  Total selection
//! cost across an entire run is `O(N log N)` instead of the
//! Phase 2 baseline's `O(N²)`.
//!
//! Tie-breaker: we use `usize::MAX - pool_idx` as the secondary
//! key so equal-size pairs are popped in pool-arrival order
//! (preserving the FIFO behaviour Phase 2 had on non-flat
//! matrices, where every pair has size 0).
//!
//! ## Pool seeding
//!
//! `seed_pool` mines every cross-clause complementary pair via
//! [`flat::mine_pairs`], pushing them into the pool at startup.
//! On non-flat matrices `mine_pairs` returns empty and Greedy
//! degrades to FIFO over B's emitted pairs.

use std::collections::BinaryHeap;

use crate::dual::{
    flat::{mine_pairs, pair_box_size},
    BasicCoverState, CoverSearchController, PairPool,
};
use crate::matrix::NNF;

pub struct GreedyMaxCoverController {
    /// Clause arities of the source matrix; empty for non-flat
    /// (where Greedy degrades to FIFO).
    arities: Vec<usize>,
    /// Max-heap of `(box_size, fifo_tiebreaker, pair_idx)`.  Sorts
    /// largest-box-first; on ties, lowest pool-index first.
    heap: BinaryHeap<(u128, usize, usize)>,
    /// Next pool index to scan for newly-arrived pairs.  Lazy
    /// drain — `next_pair_index` walks `pool[next_scan..pool.len()]`
    /// and pushes each onto the heap before popping the top.
    next_scan: usize,
    /// Number of pairs registered (for tests / observers).
    registered: usize,
}

impl GreedyMaxCoverController {
    pub fn new() -> Self {
        Self {
            arities: Vec::new(),
            heap: BinaryHeap::new(),
            next_scan: 0,
            registered: 0,
        }
    }

    pub fn registered_count(&self) -> usize { self.registered }
}

impl Default for GreedyMaxCoverController {
    fn default() -> Self { Self::new() }
}

impl CoverSearchController for GreedyMaxCoverController {
    type State = BasicCoverState;

    fn create_state(&self, nnf: &NNF) -> Self::State {
        BasicCoverState::new(nnf)
    }

    fn seed_pool(&self, nnf: &NNF, pool: &PairPool) {
        // Mine all cross-clause complementary pairs.  These are the
        // candidates Greedy ranks by box size.  Empty Vec on non-flat.
        for pair in mine_pairs(nnf) {
            pool.push(pair);
        }
    }

    fn next_pair_index(&mut self, pool: &PairPool, state: &Self::State) -> Option<usize> {
        // Late-bind arities from state.  First call only.
        if self.arities.is_empty() && !state.arities().is_empty() {
            self.arities = state.arities().to_vec();
        }
        // Drain new pool entries into the heap.  Each pair is
        // pushed at most once — the `next_scan` cursor advances
        // monotonically.
        let pool_len = pool.len();
        while self.next_scan < pool_len {
            let i = self.next_scan;
            self.next_scan += 1;
            let Some(pair) = pool.get(i) else { continue; };
            let size = match pair_to_triggers(&pair) {
                Some(t) if !self.arities.is_empty() => pair_box_size(&t, &self.arities),
                _ => 0,
            };
            // FIFO tiebreaker: lower pool-index → higher tiebreaker
            // value → wins under max-heap.
            let tiebreak = usize::MAX - i;
            self.heap.push((size, tiebreak, i));
        }
        self.heap.pop().map(|(_, _, i)| i)
    }

    fn register_pair(&mut self, idx: usize, pool: &PairPool, state: &mut Self::State) -> bool {
        if let Some(pair) = pool.get(idx) {
            state.add_pair(pair);
            self.registered += 1;
            // Also late-bind here in case `register_pair` is called
            // before `next_pair_index` (test path).
            if self.arities.is_empty() && !state.arities().is_empty() {
                self.arities = state.arities().to_vec();
            }
            true
        } else {
            false
        }
    }

    fn is_complete(&mut self, _state: &mut Self::State) -> bool {
        // Computing "every path covered" exactly is co-NP-hard with
        // the basic state representation; defer to B's exhaustion
        // for termination.  A future BDD- or CaDiCaL-bans-backed
        // state could implement this cheaply.
        false
    }
}

/// Re-extract triggers from a pair on demand.  Mirrors the logic in
/// [`crate::dual::flat_pair_triggers`].
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
    use crate::dual::{BasicCoverState, CoverState, PairPool};
    use crate::matrix::{Lit, NNF};

    fn lit_p(v: u32) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> NNF { NNF::Lit(Lit::neg(v)) }

    /// Greedy with heap should still pick the largest-box pair
    /// first, exactly like the linear-scan version.
    #[test]
    fn greedy_picks_largest_box_first() {
        // 4 clauses with non-uniform arities so the choice is
        // non-trivial.
        let nnf = NNF::Sum(vec![
            // Clause 0: arity 3 (a, b, c)
            NNF::Prod(vec![lit_p(0), lit_p(1), lit_p(2)]),
            // Clause 1: arity 2 (¬a, d)
            NNF::Prod(vec![lit_n(0), lit_p(3)]),
            // Clause 2: arity 2 (e, ¬b)
            NNF::Prod(vec![lit_p(4), lit_n(1)]),
            // Clause 3: arity 4 (¬c, ¬d, ¬e, f)
            NNF::Prod(vec![lit_n(2), lit_n(3), lit_n(4), lit_p(5)]),
        ]);

        let pool = PairPool::new();
        GreedyMaxCoverController::new().seed_pool(&nnf, &pool);

        let mut ctrl = GreedyMaxCoverController::new();
        let mut state = BasicCoverState::new(&nnf);

        // Compute the pair-with-max-box-size from the seeded pool
        // by iterating manually.
        let pairs = pool.snapshot();
        let arities = state.arities().to_vec();
        let mut max_size: u128 = 0;
        let mut max_idx: usize = 0;
        for (i, p) in pairs.iter().enumerate() {
            let t = pair_to_triggers(p).unwrap();
            let s = pair_box_size(&t, &arities);
            if s > max_size { max_size = s; max_idx = i; }
        }

        let chosen = ctrl.next_pair_index(&pool, &state).expect("non-empty");
        assert_eq!(chosen, max_idx,
            "greedy should pick the pair with the largest box first; \
             chose {} but max is at index {} with size {}",
            chosen, max_idx, max_size);
        assert!(ctrl.register_pair(chosen, &pool, &mut state));
        assert_eq!(state.registered_pair_count(), 1);
    }

    #[test]
    fn greedy_seeds_pool_with_static_pairs() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
        ]);
        let pool = PairPool::new();
        GreedyMaxCoverController::new().seed_pool(&nnf, &pool);
        assert_eq!(pool.len(), 2);
    }

    /// On non-flat matrices the heap becomes a FIFO queue (every
    /// pair has size 0 and the tiebreaker resolves to pool-index
    /// order).
    #[test]
    fn greedy_falls_back_to_fifo_on_non_flat() {
        let nnf = NNF::Prod(vec![lit_p(0)]);   // top is Prod, not Sum
        let pool = PairPool::new();
        let mut ctrl = GreedyMaxCoverController::new();
        ctrl.seed_pool(&nnf, &pool);
        assert!(pool.is_empty());

        pool.push((vec![0], vec![1]));
        pool.push((vec![2], vec![3]));
        let state = BasicCoverState::new(&nnf);
        assert_eq!(ctrl.next_pair_index(&pool, &state), Some(0));
        assert_eq!(ctrl.next_pair_index(&pool, &state), Some(1));
        assert_eq!(ctrl.next_pair_index(&pool, &state), None);
    }

    /// New: confirm heap-based selection returns pairs in the right
    /// order across multiple selections (largest boxes first).
    #[test]
    fn greedy_heap_orders_multiple_selections_by_box_size() {
        // Same matrix as `greedy_picks_largest_box_first`; arities
        // [3, 2, 2, 4] → max distinct sub-products are
        //   (1,2): 3*4 = 12   ← but no complementary pair between them
        //   (0,3): 2*2 =  4
        //   (1,3): 3*2 =  6
        //   (2,3): 3*2 =  6
        //   (0,1): 2*4 =  8
        //   (0,2): 2*4 =  8
        // Mining yields the cross-clause complements only.  We
        // confirm the popped order is non-increasing in size.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1), lit_p(2)]),
            NNF::Prod(vec![lit_n(0), lit_p(3)]),
            NNF::Prod(vec![lit_p(4), lit_n(1)]),
            NNF::Prod(vec![lit_n(2), lit_n(3), lit_n(4), lit_p(5)]),
        ]);
        let pool = PairPool::new();
        GreedyMaxCoverController::new().seed_pool(&nnf, &pool);

        let mut ctrl = GreedyMaxCoverController::new();
        let mut state = BasicCoverState::new(&nnf);
        let arities = state.arities().to_vec();
        let mut last_size: u128 = u128::MAX;
        let mut count = 0;
        while let Some(idx) = ctrl.next_pair_index(&pool, &state) {
            let pair = pool.get(idx).unwrap();
            let t = pair_to_triggers(&pair).unwrap();
            let size = pair_box_size(&t, &arities);
            assert!(size <= last_size,
                "non-monotone: pair at idx {} has size {} but previous had {}",
                idx, size, last_size);
            last_size = size;
            ctrl.register_pair(idx, &pool, &mut state);
            count += 1;
        }
        assert!(count > 0, "should have processed at least one pair");
    }
}
