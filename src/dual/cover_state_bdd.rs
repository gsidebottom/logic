//! `BddBansCoverState` — cover state that maintains the *uncovered*
//! set as a [BDD](https://en.wikipedia.org/wiki/Binary_decision_diagram).
//!
//! For a flat Sum-of-Prods matrix with clause arities
//! `[k_0, ..., k_{n-1}]`:
//!
//! * Allocate one boolean BDD variable per `(clause, alt)`:
//!   `var[c][a]` is true iff clause `c`'s alt `a` is selected on the
//!   path the encoding represents.
//! * `valid_bdd` is initialized as the AND of per-clause
//!   exactly-one constraints — it represents every legal
//!   alt-selection.
//! * For each registered complementary pair `((i, a), (j, b))`,
//!   AND `valid_bdd` with `NOT (var[i][a] ∧ var[j][b])` — the
//!   selection that produces a complementary literal pair.
//!
//! The BDD is `false` iff every path has been covered.
//! `check_complete_with_bdd()` is `valid_bdd.is_false()` —
//! constant-time on the BDD's root pointer.
//!
//! Compared to [`crate::dual::cover_state_cnf::CnfBansCoverState`],
//! the BDD representation:
//!
//! * Trades incremental SAT-solver invocations for incremental BDD
//!   `and_not` operations.  Each `add_pair` updates the BDD.
//! * Has O(1) completeness check (BDD is_false on root).
//! * Pays for variable ordering: bad orderings can blow up BDD size.
//!   We use the natural `clause-then-alt` ordering and rely on the
//!   default compaction in `biodivine-lib-bdd`.
//!
//! Non-flat NNFs short-circuit the same way as the other cover
//! states: `is_prefix_covered` returns `false`,
//! `check_complete_with_bdd` returns `false`.

use biodivine_lib_bdd::{Bdd, BddVariable, BddVariableSet, BddVariableSetBuilder};

use crate::dual::{flat, is_flat_sum_of_prods, CoverState, flat_pair_triggers};
use crate::matrix::{NNF, Pair, ProdPath};

pub struct BddBansCoverState {
    pairs: Vec<Pair>,
    triggers: Vec<Option<[(usize, usize); 2]>>,
    is_flat: bool,
    arities: Vec<usize>,
    /// Phase 4 bucket index for fast `is_prefix_covered`.
    index: Vec<Vec<Vec<usize>>>,
    /// BDD variable set (None for non-flat).
    bdd_vars: Option<BddVariableSet>,
    /// `var_map[c][a]` = BDD variable for "clause c picks alt a".
    var_map: Vec<Vec<BddVariable>>,
    /// Current `valid_bdd` — the BDD representing alt-selections
    /// that satisfy every per-clause exactly-one constraint *and*
    /// every registered pair-ban.  `is_false()` ⇒ cover complete.
    valid_bdd: Option<Bdd>,
    /// How many pairs have been merged into `valid_bdd` so far.
    pairs_merged: usize,
}

impl BddBansCoverState {
    pub fn new(nnf: &NNF) -> Self {
        let is_flat = is_flat_sum_of_prods(nnf);
        let arities = if is_flat {
            flat::flat_arities(nnf).unwrap_or_default()
        } else {
            Vec::new()
        };
        let index: Vec<Vec<Vec<usize>>> = arities.iter()
            .map(|&k| (0..k).map(|_| Vec::new()).collect())
            .collect();

        // Build BDD machinery.
        let (bdd_vars, var_map, valid_bdd) = if is_flat && !arities.is_empty() {
            let mut builder = BddVariableSetBuilder::new();
            let mut var_map: Vec<Vec<BddVariable>> = Vec::with_capacity(arities.len());
            for (c, &k) in arities.iter().enumerate() {
                let mut row: Vec<BddVariable> = Vec::with_capacity(k);
                for a in 0..k {
                    let name = format!("c{}_a{}", c, a);
                    row.push(builder.make_variable(&name));
                }
                var_map.push(row);
            }
            let vars = builder.build();

            // Build the initial valid_bdd: AND of (exactly-one per
            // clause).  Eager construction — for matrices with very
            // many clauses this can take a few ms.
            let mut valid = vars.mk_true();
            for (c, k) in arities.iter().enumerate() {
                let clause_eo = build_exactly_one(&vars, &var_map[c][..*k]);
                valid = valid.and(&clause_eo);
            }
            (Some(vars), var_map, Some(valid))
        } else {
            (None, Vec::new(), None)
        };

        Self {
            pairs: Vec::new(),
            triggers: Vec::new(),
            is_flat,
            arities,
            index,
            bdd_vars,
            var_map,
            valid_bdd,
            pairs_merged: 0,
        }
    }

    pub fn arities(&self) -> &[usize] { &self.arities }
    pub fn pairs(&self)   -> &[Pair]  { &self.pairs }
    pub fn is_flat(&self) -> bool     { self.is_flat }

    /// Register a pair.  Indexes the pair the same way as
    /// `BasicCoverState`; BDD is updated lazily on the next
    /// `check_complete_with_bdd` call.
    pub fn add_pair(&mut self, pair: Pair) {
        let triggers = if self.is_flat { flat_pair_triggers(&pair) } else { None };
        let pair_idx = self.pairs.len();
        if let Some([(i, a), (j, b)]) = triggers {
            if i < self.index.len() && a < self.index[i].len() {
                self.index[i][a].push(pair_idx);
            }
            if (j, b) != (i, a) && j < self.index.len() && b < self.index[j].len() {
                self.index[j][b].push(pair_idx);
            }
        }
        self.pairs.push(pair);
        self.triggers.push(triggers);
    }

    /// Sync any unmerged pairs into the `valid_bdd` and return
    /// `valid_bdd.is_false()`.
    ///
    /// Returns `false` for non-flat matrices (no encoding).
    pub fn check_complete_with_bdd(&mut self) -> bool {
        let Some(vars) = self.bdd_vars.as_ref() else { return false; };
        let Some(valid) = self.valid_bdd.as_mut() else { return false; };
        // Merge any new pairs.
        for i in self.pairs_merged..self.triggers.len() {
            let Some([(ci, ai), (cj, aj)]) = self.triggers[i] else { continue; };
            if ci >= self.var_map.len() || ai >= self.var_map[ci].len() { continue; }
            if cj >= self.var_map.len() || aj >= self.var_map[cj].len() { continue; }
            let bdd_a = vars.mk_var(self.var_map[ci][ai]);
            let bdd_b = vars.mk_var(self.var_map[cj][aj]);
            let conflict = bdd_a.and(&bdd_b);
            // valid := valid AND NOT conflict
            *valid = valid.and_not(&conflict);
            // Early exit: if the BDD became false, every alt-
            // selection is now banned — cover complete.  Still
            // increment the cursor so a later call doesn't re-merge.
            if valid.is_false() {
                self.pairs_merged = i + 1;
                return true;
            }
        }
        self.pairs_merged = self.triggers.len();
        valid.is_false()
    }

    /// Diagnostic: BDD node count after the last `check_complete_with_bdd`.
    /// Returns 0 for non-flat or before the first check.
    pub fn bdd_size(&self) -> usize {
        self.valid_bdd.as_ref().map(|b| b.size()).unwrap_or(0)
    }

    /// How many pairs have been merged into the BDD.
    pub fn bdd_pair_count(&self) -> usize { self.pairs_merged }
}

impl CoverState for BddBansCoverState {
    fn is_prefix_covered(&self, prefix: &ProdPath) -> bool {
        if !self.is_flat { return false; }
        for (i, &a) in prefix.iter().enumerate() {
            if i >= self.index.len() { continue; }
            if a >= self.index[i].len() { continue; }
            for &pair_idx in &self.index[i][a] {
                let Some([t1, t2]) = self.triggers[pair_idx] else { continue; };
                let (oi, oa) = if t1 == (i, a) { t2 } else { t1 };
                if oi == i { continue; }
                if prefix.len() > oi && prefix[oi] == oa {
                    return true;
                }
            }
        }
        false
    }

    fn registered_pair_count(&self) -> usize { self.pairs.len() }
}

/// Build the BDD for "exactly-one of `vs` is true": (∨ vs) ∧
/// pairwise(¬vs[a] ∨ ¬vs[b]).
fn build_exactly_one(vars: &BddVariableSet, vs: &[BddVariable]) -> Bdd {
    if vs.is_empty() {
        return vars.mk_false();
    }
    // At-least-one: x_0 ∨ x_1 ∨ ...
    let mut alo = vars.mk_var(vs[0]);
    for &v in &vs[1..] {
        alo = alo.or(&vars.mk_var(v));
    }
    // At-most-one: pairwise (¬x_a ∨ ¬x_b).
    let mut amo = vars.mk_true();
    for i in 0..vs.len() {
        for j in (i + 1)..vs.len() {
            let pair_amo = vars.mk_not_var(vs[i]).or(&vars.mk_not_var(vs[j]));
            amo = amo.and(&pair_amo);
        }
    }
    alo.and(&amo)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::matrix::Lit;

    fn lit_p(v: u32) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> NNF { NNF::Lit(Lit::neg(v)) }

    #[test]
    fn check_complete_returns_false_when_no_bans() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
        ]);
        let mut state = BddBansCoverState::new(&nnf);
        assert!(!state.check_complete_with_bdd());
    }

    #[test]
    fn check_complete_returns_true_for_simple_unsat() {
        // (a) ∧ (¬a) — UNSAT.  Complement: Sum(Lit(¬a), Lit(a)).
        let nnf = NNF::Sum(vec![lit_n(0), lit_p(0)]);
        let mut state = BddBansCoverState::new(&nnf);
        state.add_pair((vec![0], vec![1]));
        assert!(state.check_complete_with_bdd(),
            "after registering the cross-clause pair, every path is covered");
    }

    #[test]
    fn check_complete_returns_true_for_three_clause_unsat() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
            lit_p(0),
            lit_p(1),
        ]);
        let mut state = BddBansCoverState::new(&nnf);
        state.add_pair((vec![0, 0], vec![1]));
        state.add_pair((vec![0, 1], vec![2]));
        assert!(state.check_complete_with_bdd());
    }

    #[test]
    fn check_complete_returns_false_when_paths_remain_uncovered() {
        // SAT formula complement.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
        ]);
        let mut state = BddBansCoverState::new(&nnf);
        state.add_pair((vec![0, 0], vec![1, 0]));
        state.add_pair((vec![0, 1], vec![1, 1]));
        assert!(!state.check_complete_with_bdd(),
            "two paths remain uncovered → BDD must remain non-false");
    }

    #[test]
    fn is_prefix_covered_uses_index() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
        ]);
        let mut state = BddBansCoverState::new(&nnf);
        state.add_pair((vec![0, 0], vec![1, 0]));
        assert!(state.is_prefix_covered(&vec![0, 0]));
        assert!(!state.is_prefix_covered(&vec![0, 1]));
    }

    #[test]
    fn non_flat_short_circuits() {
        let nnf = NNF::Prod(vec![lit_p(0)]);
        let mut state = BddBansCoverState::new(&nnf);
        state.add_pair((vec![0], vec![1]));
        assert!(!state.is_prefix_covered(&vec![0]));
        assert!(!state.check_complete_with_bdd());
    }

    /// BDD size grows with pairs but remains bounded by the
    /// per-clause exactly-one constraints.  Sanity check: for a
    /// small matrix the BDD doesn't explode.
    #[test]
    fn bdd_size_is_reasonable_for_small_matrix() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1), lit_p(2)]),
            NNF::Prod(vec![lit_n(0), lit_n(1), lit_n(2)]),
        ]);
        let mut state = BddBansCoverState::new(&nnf);
        // Register all 3 cross-clause complementary pairs.
        state.add_pair((vec![0, 0], vec![1, 0]));
        state.add_pair((vec![0, 1], vec![1, 1]));
        state.add_pair((vec![0, 2], vec![1, 2]));
        let _ = state.check_complete_with_bdd();
        // 6 BDD vars, exactly-one over 3 + 3 vars + 3 bans → small.
        assert!(state.bdd_size() < 100,
            "BDD blew up unexpectedly: {} nodes", state.bdd_size());
    }
}
