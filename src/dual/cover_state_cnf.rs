//! `CnfBansCoverState` — cover state that mirrors
//! [`crate::dual::BasicCoverState`] but additionally maintains an
//! incremental CaDiCaL solver encoding the *uncovered* set as a
//! boolean CNF.  Lets the cover-search side declare UNSAT
//! independently of the path-search side.
//!
//! ## The encoding
//!
//! For a flat Sum-of-Prod-of-Lits matrix with clause arities
//! `[k_0, ..., k_{n-1}]`:
//!
//! * Allocate one boolean variable per `(clause, alt)`:
//!   `var[c][a]` is true iff clause `c`'s alt `a` is "selected"
//!   on the path the encoding represents.
//! * Constrain each clause to pick exactly one alt: at-least-one
//!   `(var[c][0] ∨ var[c][1] ∨ ...)` plus pairwise at-most-one
//!   `(¬var[c][a] ∨ ¬var[c][b])` for `a < b`.
//! * For each registered complementary pair `((i, a), (j, b))`,
//!   add the *ban* clause `(¬var[i][a] ∨ ¬var[j][b])` — the
//!   selection that produces a complementary literal pair.
//!
//! The CNF is satisfiable iff some path is uncovered (i.e. some
//! alt-selection avoids every ban).  When CaDiCaL reports UNSAT,
//! every path is covered → the original formula is unsatisfiable
//! and the cover-search side reports
//! [`crate::dual::Outcome::Unsat`].
//!
//! ## Incremental usage
//!
//! The CaDiCaL solver is created once at state construction, with
//! the per-clause exactly-one constraints already added.  Each
//! `add_pair` call appends one ban clause to the solver.
//! `check_complete_with_cadical` calls `solver.solve()` and
//! returns `true` on UNSAT.
//!
//! Calling `solve()` per pair is too expensive — even on flat
//! Sum-of-Prods the bans CNF can have thousands of clauses and
//! solving takes milliseconds.  The accompanying
//! [`crate::dual::CnfBansCoverController`] schedules checks on a
//! geometric backoff (every 1024, then 2048, ...) so the cost
//! amortizes.

use crate::dual::{flat, is_flat_sum_of_prods, CoverState, flat_pair_triggers};
use crate::matrix::{NNF, Pair, ProdPath};

pub struct CnfBansCoverState {
    pairs: Vec<Pair>,
    triggers: Vec<Option<[(usize, usize); 2]>>,
    is_flat: bool,
    arities: Vec<usize>,
    /// Per-(clause, alt) bucket index for fast `is_prefix_covered`,
    /// same as `BasicCoverState`.
    index: Vec<Vec<Vec<usize>>>,
    /// `var_map[c][a]` = CaDiCaL variable ID (1-indexed) for the
    /// "clause `c` picks alt `a`" boolean.  Empty for non-flat.
    var_map: Vec<Vec<i32>>,
    /// CaDiCaL solver, lazily initialized.  Holds the per-clause
    /// exactly-one constraints + ban clauses for every registered
    /// pair so far.
    cadical: Option<cadical::Solver>,
    /// How many pairs have been pushed to the CaDiCaL solver as
    /// ban clauses.  Lets `add_pair` and `check_complete` push
    /// only the new ones since last sync.
    pairs_pushed_to_solver: usize,
}

impl CnfBansCoverState {
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
        // Allocate one CaDiCaL var per (clause, alt) — IDs start at 1.
        let mut next_var: i32 = 1;
        let var_map: Vec<Vec<i32>> = arities.iter().map(|&k| {
            (0..k).map(|_| { let v = next_var; next_var += 1; v }).collect()
        }).collect();
        Self {
            pairs: Vec::new(),
            triggers: Vec::new(),
            is_flat,
            arities,
            index,
            var_map,
            cadical: None,
            pairs_pushed_to_solver: 0,
        }
    }

    pub fn arities(&self) -> &[usize] { &self.arities }
    pub fn pairs(&self)   -> &[Pair]  { &self.pairs }
    pub fn is_flat(&self) -> bool     { self.is_flat }

    /// Register a pair.  Indexes the pair the same way as
    /// `BasicCoverState`; CaDiCaL solver state is updated lazily on
    /// the next `check_complete_with_cadical` call.
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

    /// Lazily build the CaDiCaL solver: allocate it on first call,
    /// add the per-clause exactly-one constraints.  Idempotent.
    fn ensure_cadical(&mut self) {
        if self.cadical.is_some() { return; }
        if !self.is_flat || self.arities.is_empty() {
            // Without flat structure we can't encode the bans.
            // Leave `cadical` None and `check_complete` will return
            // false.
            return;
        }
        let mut solver: cadical::Solver = cadical::Solver::new();
        // Per-clause exactly-one constraints.
        for c in 0..self.arities.len() {
            let k = self.arities[c];
            // at-least-one: (var[c][0] ∨ var[c][1] ∨ ...)
            let alo: Vec<i32> = self.var_map[c].iter().copied().collect();
            solver.add_clause(alo);
            // at-most-one: pairwise (¬var[c][a] ∨ ¬var[c][b]) for a < b.
            for a in 0..k {
                for b in (a + 1)..k {
                    solver.add_clause([
                        -self.var_map[c][a],
                        -self.var_map[c][b],
                    ]);
                }
            }
        }
        self.cadical = Some(solver);
    }

    /// Push any new ban clauses to the CaDiCaL solver.  Cheap if
    /// no new pairs since last sync.
    fn sync_pairs_to_cadical(&mut self) {
        let Some(solver) = self.cadical.as_mut() else { return; };
        for i in self.pairs_pushed_to_solver..self.pairs.len() {
            let Some([(ci, ai), (cj, aj)]) = self.triggers[i] else { continue; };
            if ci >= self.var_map.len() || ai >= self.var_map[ci].len() { continue; }
            if cj >= self.var_map.len() || aj >= self.var_map[cj].len() { continue; }
            solver.add_clause([-self.var_map[ci][ai], -self.var_map[cj][aj]]);
        }
        self.pairs_pushed_to_solver = self.pairs.len();
    }

    /// Run CaDiCaL on the bans CNF.  Returns `true` iff CaDiCaL
    /// proves the CNF UNSAT, meaning every alt-selection
    /// contradicts some ban → cover complete → original formula
    /// is unsatisfiable.
    ///
    /// Returns `false` for SAT or non-flat matrices (where we
    /// can't build the encoding).
    pub fn check_complete_with_cadical(&mut self) -> bool {
        if !self.is_flat { return false; }
        self.ensure_cadical();
        if self.cadical.is_none() { return false; }
        self.sync_pairs_to_cadical();
        let solver = self.cadical.as_mut().expect("ensured above");
        match solver.solve() {
            Some(false) => true,    // UNSAT → cover complete
            Some(true)  => false,   // SAT → not yet complete
            None        => false,   // unknown / interrupted
        }
    }

    /// How many ban clauses have been pushed to the CaDiCaL
    /// solver.  Used by tests / observers.
    pub fn cadical_clause_count(&self) -> usize { self.pairs_pushed_to_solver }
}

impl CoverState for CnfBansCoverState {
    fn is_prefix_covered(&self, prefix: &ProdPath) -> bool {
        // Same indexed lookup as `BasicCoverState`.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::matrix::Lit;

    fn lit_p(v: u32) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> NNF { NNF::Lit(Lit::neg(v)) }

    /// Construct a state for a 2-clause matrix and confirm CaDiCaL
    /// reports SAT before any pairs are registered.
    #[test]
    fn check_complete_returns_false_when_no_bans() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
        ]);
        let mut state = CnfBansCoverState::new(&nnf);
        // No pairs registered → exactly-one constraints alone are
        // SAT (e.g. clause 0 picks var 0, clause 1 picks var 0).
        assert!(!state.check_complete_with_cadical());
    }

    /// Genuinely-UNSAT formula whose complement has every path
    /// covered.  Original: `a ∧ ¬a` (UNSAT).  Complement:
    /// `Sum(Lit(¬a), Lit(a))`.  Path semantics: Sum visits both
    /// children → path lits = {¬a, a} → always covered.  After
    /// registering the one cross-clause complementary pair,
    /// CaDiCaL should prove the bans CNF UNSAT.
    #[test]
    fn check_complete_returns_true_for_simple_unsat() {
        let nnf = NNF::Sum(vec![lit_n(0), lit_p(0)]);
        let mut state = CnfBansCoverState::new(&nnf);
        // Singleton sum-children get flat_pair_triggers Position [c]
        // mapped to (c, 0).
        state.add_pair((vec![0], vec![1]));
        assert!(state.check_complete_with_cadical(),
            "after registering the one cross-clause pair, every \
             path should be covered (formula is UNSAT)");
    }

    /// Slightly larger UNSAT case to exercise multi-alt clauses.
    /// Original: `(a ∨ b) ∧ ¬a ∧ ¬b` (UNSAT — every clause covers
    /// what the others ban).  Complement (Sum-of-Prods):
    ///   cube 0 = ¬a ∧ ¬b
    ///   cube 1 = a       (singleton)
    ///   cube 2 = b       (singleton)
    /// Cross-clause complements:
    ///   (cube 0 alt 0 = ¬a) ↔ (cube 1 alt 0 = a)
    ///   (cube 0 alt 1 = ¬b) ↔ (cube 2 alt 0 = b)
    #[test]
    fn check_complete_returns_true_for_three_clause_unsat() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
            lit_p(0),
            lit_p(1),
        ]);
        let mut state = CnfBansCoverState::new(&nnf);
        state.add_pair((vec![0, 0], vec![1]));   // ¬a vs a
        state.add_pair((vec![0, 1], vec![2]));   // ¬b vs b
        assert!(state.check_complete_with_cadical(),
            "after registering all cross-clause pairs, the bans \
             CNF should prove UNSAT");
    }

    /// SAT case: only some pairs registered → CaDiCaL reports SAT
    /// (not enough bans to rule out every path).  This is the
    /// correctness invariant: A only declares UNSAT when truly so.
    #[test]
    fn check_complete_returns_false_when_paths_remain_uncovered() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
        ]);
        // Original (¬a∨¬b) ∧ (a∨b) — SAT (a=t,b=f).  Complement
        // has 2 covered + 2 uncovered paths.  Even after we
        // register the 2 cross-clause complementary pairs,
        // 2 paths remain uncovered.
        let mut state = CnfBansCoverState::new(&nnf);
        state.add_pair((vec![0, 0], vec![1, 0]));
        state.add_pair((vec![0, 1], vec![1, 1]));
        assert!(!state.check_complete_with_cadical(),
            "complement is SAT (the original formula is SAT), so \
             the bans CNF must remain SAT — A should not declare UNSAT");
    }

    /// `is_prefix_covered` mirrors `BasicCoverState`'s indexed
    /// lookup — confirm it works the same way on this state too.
    #[test]
    fn is_prefix_covered_uses_index() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
        ]);
        let mut state = CnfBansCoverState::new(&nnf);
        state.add_pair((vec![0, 0], vec![1, 0]));   // ban (alt 0, alt 0)
        // Prefix [0, 0] should be covered by this pair.
        assert!(state.is_prefix_covered(&vec![0, 0]));
        // Prefix [0, 1] doesn't match: not covered.
        assert!(!state.is_prefix_covered(&vec![0, 1]));
    }

    /// Non-flat matrices: `is_prefix_covered` is conservatively
    /// false and `check_complete_with_cadical` returns false.
    #[test]
    fn non_flat_short_circuits() {
        let nnf = NNF::Prod(vec![lit_p(0)]);
        let mut state = CnfBansCoverState::new(&nnf);
        state.add_pair((vec![0], vec![1]));
        assert!(!state.is_prefix_covered(&vec![0]));
        assert!(!state.check_complete_with_cadical());
    }
}
