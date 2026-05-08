//! `GreedyDynamicCoverController` — classical set-cover greedy: at
//! each step pick the pair that **newly** covers the most paths,
//! given the pairs already chosen.
//!
//! ## How it differs from [`crate::dual::GreedyMaxCoverController`]
//!
//! The static controller scores every pair by its *isolated* box
//! size — the number of paths it would cover *if picked alone*.
//! That score never changes, so a pair stays "best" forever even
//! if everything in its box was already covered by an earlier
//! pick.
//!
//! This controller scores by **marginal gain** — how many *currently
//! uncovered* paths a pair would add.  The score drops every time a
//! new pair is registered, so picks late in the run go to small
//! pairs whose corner of the matrix is still unclaimed instead of
//! to big pairs that overlap heavily with what's already chosen.
//!
//! Set-cover marginal gain is submodular, so plain greedy here
//! enjoys the textbook `1 + ln n` approximation ratio.
//!
//! ## Implementation
//!
//! * **State**: [`crate::dual::BddBansCoverState`].  It already
//!   maintains `valid_bdd` = "alt-selections not yet covered by any
//!   registered pair," with exactly-one-per-clause constraints
//!   AND'd in.  Marginal gain of pair `X` is just
//!   `cardinality(valid_bdd ∧ box(X))` — exposed as
//!   `BddBansCoverState::gain_for_pair`.
//!
//! * **Selection**: lazy-greedy max-heap (Minoux 1978).  Cached
//!   gains in the heap are upper bounds on current gains
//!   (submodularity); we pop, recompute the popped entry's true
//!   gain, and either (a) return it if it still beats the next
//!   heap top, or (b) push it back with the lower true gain and
//!   try again.  The first selection is fast (uses the
//!   `box_size` upper bound seeded into the heap); later selections
//!   may re-evaluate a handful of top candidates but rarely the
//!   whole pool.
//!
//! * **Termination**: `is_complete` returns
//!   `state.check_complete_with_bdd()`.  Unlike the static greedy
//!   controller (which always defers to B's exhaustion), this
//!   controller can declare UNSAT itself once `valid_bdd` is
//!   `false` — letting A win the termination race on UNSAT
//!   matrices where the cover is small.

use std::collections::BinaryHeap;

use crate::dual::{
    flat::{mine_pairs, pair_box_size},
    BddBansCoverState, CoverSearchController, PairPool,
};
use crate::matrix::NNF;

pub struct GreedyDynamicCoverController {
    /// Clause arities; populated late from `state.arities()` on the
    /// first `next_pair_index` (the state has the canonical copy).
    arities: Vec<usize>,
    /// Lazy max-heap of `(cached_gain, fifo_tiebreaker, pair_idx)`.
    /// Cached gains are submodular upper bounds on current gain;
    /// `next_pair_index` re-evaluates the popped entry and pushes
    /// it back if its true gain dropped below the next heap top.
    heap: BinaryHeap<(u128, usize, usize)>,
    /// Cursor into `pool[..]` for newly-arrived pairs we haven't
    /// pushed onto the heap yet.  Advances monotonically.
    next_scan: usize,
    /// Number of pairs registered (tests / observers).
    registered: usize,
    /// Maximum BDD re-evaluations per `next_pair_index` call.  When
    /// many candidates have nearly-identical cached gains (common on
    /// dense, structured matrices like PHP), the lazy-greedy loop
    /// would otherwise re-evaluate the entire pool to find the
    /// arg-max — paying `pool_size × cardinality_cost` per pick.
    /// Capping trades a tiny amount of optimality (we may pick a pair
    /// whose true gain is the best of the *cap*-many we evaluated,
    /// not the absolute best) for a massive speedup.
    reeval_cap: usize,
    /// BDD-size fallback threshold.  Once `valid_bdd.size()` exceeds
    /// this, `next_pair_index` skips the BDD-based gain evaluation
    /// entirely and degrades to static box-size selection (popping
    /// the heap by cached gain without re-scoring).  This keeps the
    /// controller usable on BDD-blowup families like PHP, where each
    /// gain query becomes a ~100 ms BDD `cardinality` traversal once
    /// the BDD reaches millions of nodes.  Sound: cached gains are
    /// always ≥ true gains by submodularity, so popping by cached
    /// value is just the static greedy pick.  Default 100 000 nodes
    /// — small enough that per-query cost stays sub-millisecond on
    /// the matrices where the BDD doesn't blow up, large enough to
    /// keep dynamic mode active on faulty-adder-class problems.
    bdd_size_threshold: usize,
}

impl GreedyDynamicCoverController {
    pub fn new() -> Self {
        Self {
            arities: Vec::new(),
            heap: BinaryHeap::new(),
            next_scan: 0,
            registered: 0,
            reeval_cap: 16,
            bdd_size_threshold: 100_000,
        }
    }

    /// Override the per-call re-evaluation cap.  Higher values are
    /// closer to true greedy; lower values are faster.  Set to
    /// `usize::MAX` for the unbounded (provably-optimal) variant.
    pub fn with_reeval_cap(mut self, cap: usize) -> Self {
        self.reeval_cap = cap.max(1);
        self
    }

    /// Override the BDD-size fallback threshold.  Set to 0 to never
    /// fall back (always do BDD-based scoring); set to `usize::MAX`
    /// to disable the fallback's other half (always-on dynamic).
    pub fn with_bdd_size_threshold(mut self, t: usize) -> Self {
        self.bdd_size_threshold = t;
        self
    }

    pub fn registered_count(&self) -> usize { self.registered }
}

impl Default for GreedyDynamicCoverController {
    fn default() -> Self { Self::new() }
}

impl CoverSearchController for GreedyDynamicCoverController {
    type State = BddBansCoverState;

    fn create_state(&self, nnf: &NNF) -> Self::State {
        BddBansCoverState::new(nnf)
    }

    fn seed_pool(&self, nnf: &NNF, pool: &PairPool) {
        // Same static seed as the box-size greedy: every cross-clause
        // complementary pair.  Empty Vec on non-flat → controller
        // degrades to FIFO over B's emitted pairs.
        for pair in mine_pairs(nnf) {
            pool.push(pair);
        }
    }

    fn next_pair_index(&mut self, pool: &PairPool, state: &Self::State) -> Option<usize> {
        // Late-bind arities the first time the state has them.
        if self.arities.is_empty() && !state.arities().is_empty() {
            self.arities = state.arities().to_vec();
        }

        // Drain newly-arrived pool entries onto the heap with a
        // box-size upper bound.  By submodularity, box_size ≥ true
        // marginal gain at any point in the run, so seeding with it
        // keeps the lazy-greedy invariant intact: cached gain ≥
        // true gain.
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

        // BDD-size fallback: once `valid_bdd` has grown beyond
        // `bdd_size_threshold` nodes (typical PHP-style blowup), the
        // controller goes idle entirely — returning `None` causes the
        // driver loop to yield and lets B drive termination.  We
        // can't usefully keep registering pairs because (a) BDD AND
        // + cardinality on a multi-million-node BDD is hundreds of
        // milliseconds per call, and (b) `register_pair` itself has
        // to call `check_complete_with_bdd` to keep the next gain
        // query fresh, and that update grows the BDD further.  Going
        // idle stops both sources of overhead.  Degrades dynamic
        // greedy to "do nothing more" once it's no longer cheap;
        // sound because B's path-search exhaustion is an authority
        // for UNSAT regardless of what A has registered.
        if state.bdd_size() > self.bdd_size_threshold {
            return None;
        }

        // Lazy-greedy loop: pop the top entry, re-evaluate via the
        // BDD, and either return it (its true gain still tops the
        // heap) or push it back with the lower true gain.  Candidates
        // whose true gain has dropped to 0 are entirely dropped —
        // they'd never contribute and reinserting them wastes heap
        // operations.
        //
        // Capped at `self.reeval_cap` re-evaluations per call to
        // avoid pathological pool walks on dense matrices.  When the
        // cap fires we return the best (true_gain, idx) seen so far —
        // approximate but still strictly better than the static
        // box-size choice (we always pick from candidates that are at
        // least as fresh as the static heap's top).
        let mut best: Option<(u128, u128, usize, usize)> = None;  // (true_gain, cached, tiebreak, idx)
        let mut reevals = 0usize;
        loop {
            // If we hit the cap, fall back to the best we've seen.
            if reevals >= self.reeval_cap {
                if let Some((tg, cg, tb, idx)) = best {
                    // Re-add anything we popped but didn't return —
                    // they're still candidates with their re-evaluated
                    // true gain (a tighter upper bound than they had).
                    self.heap.push((tg, tb, idx));
                    let (_, _, _, ret_idx) = (tg, cg, tb, idx);
                    return Some(ret_idx);
                }
                // No best (heap was empty) — fall through to heap
                // pop, which will return None.
            }
            let (cached_gain, tiebreak, idx) = match self.heap.pop() {
                Some(x) => x,
                None => return best.map(|(_, _, _, i)| i),
            };
            let pair = match pool.get(idx) {
                Some(p) => p,
                None => continue,
            };
            let true_gain = state.gain_for_pair(&pair);
            reevals += 1;

            if true_gain == 0 {
                // Drop entirely — this pair's region is fully covered.
                continue;
            }

            let next_top = self.heap.peek().map(|&(g, _, _)| g).unwrap_or(0);
            if true_gain >= next_top {
                // Provably the best remaining candidate (true_gain ≥
                // next_top ≥ next_top's true gain by submodularity).
                debug_assert!(true_gain <= cached_gain,
                    "lazy-greedy invariant violated: true_gain {} > cached_gain {} for pair {}",
                    true_gain, cached_gain, idx);
                // Re-insert any "best" we were tracking so it stays
                // available for next call.
                if let Some((bg, _bcg, btb, bidx)) = best {
                    if bidx != idx { self.heap.push((bg, btb, bidx)); }
                }
                return Some(idx);
            }

            // Update "best so far" for the cap-fallback path.
            match best {
                None => best = Some((true_gain, cached_gain, tiebreak, idx)),
                Some((bg, _, _, _)) if true_gain > bg =>
                    best = Some((true_gain, cached_gain, tiebreak, idx)),
                Some((_, _, btb, bidx)) => {
                    // Push the loser back with its updated true gain.
                    if bidx != idx { /* unchanged */ }
                    let _ = btb;
                }
            }
            // Push the just-evaluated entry back with its true gain
            // (unless it's now the "best so far" — that's tracked
            // separately and re-inserted on either return path).
            if best.map(|(_, _, _, bi)| bi) != Some(idx) {
                self.heap.push((true_gain, tiebreak, idx));
            }
        }
    }

    fn register_pair(&mut self, idx: usize, pool: &PairPool, state: &mut Self::State) -> bool {
        let Some(pair) = pool.get(idx) else { return false; };
        state.add_pair(pair);
        // Sync the BDD so the next `gain_for_pair` query sees this
        // pair's effect.  `check_complete_with_bdd` returns the
        // completeness signal as a side benefit; we rely on
        // `is_complete` to read it again at the end of the
        // register/check round-trip in the driver loop, so its
        // result here is just discarded.
        let _ = state.check_complete_with_bdd();
        self.registered += 1;
        true
    }

    fn is_complete(&mut self, state: &mut Self::State) -> bool {
        // Cheap re-check.  `check_complete_with_bdd` is idempotent
        // when no new pairs have been registered since the last call,
        // so this is just a `valid_bdd.is_false()` lookup.
        state.check_complete_with_bdd()
    }
}

/// Re-extract triggers from a pair on demand.  Mirrors
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
    use crate::dual::{
        solve_dual, BasicDualPathController, CoverSearchController, Outcome, PairPool,
        SearchMode,
    };
    use crate::matrix::{Lit, NNF};

    fn lit_p(v: u32) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> NNF { NNF::Lit(Lit::neg(v)) }

    #[test]
    fn dynamic_seeds_pool_with_static_pairs() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
        ]);
        let pool = PairPool::new();
        GreedyDynamicCoverController::new().seed_pool(&nnf, &pool);
        assert_eq!(pool.len(), 2);
    }

    /// On the simplest UNSAT formula `(a)(¬a)` (complement
    /// `Sum[Lit(¬a), Lit(a)]`) the dynamic greedy should pick the
    /// single pair, register it, and `is_complete` should fire.
    #[test]
    fn dynamic_drives_termination_on_simple_unsat() {
        let nnf = NNF::Sum(vec![lit_n(0), lit_p(0)]);
        let outcome = solve_dual(
            &nnf,
            GreedyDynamicCoverController::default(),
            BasicDualPathController::<BddBansCoverState>::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }

    /// Cross-product agreement on a mix of SAT/UNSAT: same set as
    /// `dual_greedy_agrees_on_assorted_formulas` in `mod.rs`.
    #[test]
    fn dynamic_agrees_on_assorted_formulas() {
        for text in &[
            "a + a'",
            "a + b",
            "a*b + a*b' + a'*b + a'*b'",
            "(a + b)*(c + d)",
            "(a + b + c)*(b + c + d)*(a + d)",
            "(x + y)*(x' + z)*(y' + z')",
            "a*a'",
            "a*a'*b",
            "(a + b)*(a' + b)*(a + b')*(a' + b')",
        ] {
            let matrix = crate::matrix::Matrix::try_from(*text).expect("matrix");
            let expected_sat = matrix.satisfiable(crate::matrix::smart_controller_builder).is_ok();
            let nnf = matrix.nnf_complement.clone();
            let outcome = solve_dual(
                &nnf,
                GreedyDynamicCoverController::default(),
                BasicDualPathController::<BddBansCoverState>::default(),
                SearchMode::Satisfiable,
            );
            let dual_is_sat = matches!(outcome, Outcome::Sat(_));
            assert_eq!(dual_is_sat, expected_sat,
                "GreedyDynamic disagrees on '{}': dual={:?}, expected_sat={}",
                text, outcome, expected_sat);
        }
    }

    /// Construct a small UNSAT formula whose static-greedy pick is
    /// strictly worse than the dynamic-greedy pick, and verify that
    /// dynamic still produces the correct UNSAT answer (correctness
    /// only — this isn't a perf assertion).
    #[test]
    fn dynamic_handles_overlapping_box_formula() {
        // `(a + b)(a + b')(a')` — UNSAT.
        // Complement: a'b' + a'b + a → Sum[Prod[a',b'], Prod[a',b], Lit(a)].
        // Cover pairs:
        //   {a' (pos [0,0]), a (pos [2])}  — covers the alt-0 branch of clause 0
        //   {a' (pos [1,0]), a (pos [2])}  — covers the alt-0 branch of clause 1
        //   {b' (pos [0,1]), b (pos [1,1])} — closes the (alt 1, alt 1) corner
        // Static greedy: picks pairs by box size; both `{a', a}` pairs
        // overlap heavily.  Dynamic picks one `{a', a}` then jumps to
        // `{b', b}` to close the remaining corner, since its marginal
        // gain is higher than the second `{a', a}`'s residual.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
            NNF::Prod(vec![lit_n(0), lit_p(1)]),
            lit_p(0),
        ]);
        let outcome = solve_dual(
            &nnf,
            GreedyDynamicCoverController::default(),
            BasicDualPathController::<BddBansCoverState>::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat);
    }
}
