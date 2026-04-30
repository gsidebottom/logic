//! Helpers for the flat Sum-of-Prod-of-Lits matrix shape (the
//! CNF-complement / SAT-search common case).
//!
//! Two services:
//!
//! 1. **`flat_clauses`** — extract a `Vec<Vec<Lit>>` clause structure
//!    from a flat NNF.  The outer Vec is the Sum-children (clause
//!    cubes); the inner Vec is each clause's alternative literals.
//!    Returns `None` when the NNF isn't flat.
//! 2. **`mine_pairs`** — enumerate every cross-clause complementary
//!    pair from the clause structure.  Useful for seeding A's pair
//!    pool at startup so it has work to do before B begins emitting.
//!
//! Both are `O(n_clauses · max_arity)` plus, for `mine_pairs`, an
//! O(n_lits²) cross-product to find complements — fine for the
//! formula sizes we benchmark.

use crate::matrix::{Lit, NNF, Pair, Position};

/// Extract clause-of-lits structure from a flat Sum-of-Prod-of-Lits
/// NNF.  Each clause is the alts of the corresponding `Prod` child
/// (or a single-element `Vec<Lit>` if the Sum-child is a bare
/// `Lit`).  Returns `None` if `nnf` doesn't have flat shape.
pub fn flat_clauses(nnf: &NNF) -> Option<Vec<Vec<Lit>>> {
    let NNF::Sum(children) = nnf else { return None; };
    let mut out = Vec::with_capacity(children.len());
    for c in children {
        match c {
            NNF::Lit(l) => out.push(vec![l.clone()]),
            NNF::Prod(alts) => {
                let mut v = Vec::with_capacity(alts.len());
                for a in alts {
                    match a {
                        NNF::Lit(l) => v.push(l.clone()),
                        _ => return None,
                    }
                }
                out.push(v);
            }
            NNF::Sum(_) => return None,
        }
    }
    Some(out)
}

/// Mine every cross-clause complementary pair from a flat
/// Sum-of-Prod-of-Lits NNF.  For each pair of clauses `(i, j)`
/// with `i < j`, find every `(a, b)` where `clauses[i][a]` is the
/// complement of `clauses[j][b]`, and emit a `Pair` with
/// `Position`s `[i, a]` / `[j, b]`.
///
/// Returns an empty Vec when the NNF isn't flat.  Caller is
/// responsible for not registering duplicate pairs (the cover
/// state's append-only design tolerates duplicates but they're
/// wasted work).
pub fn mine_pairs(nnf: &NNF) -> Vec<Pair> {
    let Some(clauses) = flat_clauses(nnf) else { return Vec::new(); };
    let mut out = Vec::new();
    let n = clauses.len();
    for i in 0..n {
        // Singleton-Lit Sum-children encode Position [i]; multi-alt
        // Prod children encode [i, a].  Build the right Position
        // shape per clause.
        let pos_for = |clause_idx: usize, alt_idx: usize| -> Position {
            if clauses[clause_idx].len() == 1 {
                vec![clause_idx]
            } else {
                vec![clause_idx, alt_idx]
            }
        };
        for j in (i + 1)..n {
            for (a, lit_a) in clauses[i].iter().enumerate() {
                for (b, lit_b) in clauses[j].iter().enumerate() {
                    if lit_a.var == lit_b.var && lit_a.neg != lit_b.neg {
                        out.push((pos_for(i, a), pos_for(j, b)));
                    }
                }
            }
        }
    }
    out
}

/// Box size = the number of paths a pair covers.  For a pair with
/// triggers `(i, a)` and `(j, b)` and clause arities
/// `[k_0, k_1, ..., k_{n-1}]`, the pair fixes clauses `i, j` and
/// leaves the rest free, so the box size is `Π_{c ≠ i, j} k_c`.
///
/// Returns `0` if the trigger indices are out of range, or if the
/// pair targets the same clause twice (a same-clause pair is
/// physically impossible and shouldn't happen, but be defensive).
pub fn pair_box_size(triggers: &[(usize, usize); 2], arities: &[usize]) -> u128 {
    let (i, _) = triggers[0];
    let (j, _) = triggers[1];
    if i >= arities.len() || j >= arities.len() || i == j {
        return 0;
    }
    let mut prod: u128 = 1;
    for (c, k) in arities.iter().enumerate() {
        if c == i || c == j { continue; }
        prod = prod.saturating_mul(*k as u128);
    }
    prod
}

/// Convenience: clause arities for a flat NNF.
pub fn flat_arities(nnf: &NNF) -> Option<Vec<usize>> {
    flat_clauses(nnf).map(|cs| cs.into_iter().map(|c| c.len()).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit_p(v: u32) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> NNF { NNF::Lit(Lit::neg(v)) }

    #[test]
    fn flat_clauses_extracts_cube_structure() {
        // (a + b)*(a' + c) → complement = a'b' + ac' which in NNF
        // is Sum(Prod(¬a, ¬b), Prod(a, ¬c)).
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
            NNF::Prod(vec![lit_p(0), lit_n(2)]),
        ]);
        let clauses = flat_clauses(&nnf).expect("flat");
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0].len(), 2);
        assert_eq!(clauses[1].len(), 2);
    }

    #[test]
    fn flat_clauses_handles_singleton_sum_children() {
        // Sum(Prod(a, b), c) — second child is a bare Lit.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            lit_p(2),
        ]);
        let clauses = flat_clauses(&nnf).expect("flat");
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[1].len(), 1);
    }

    #[test]
    fn flat_clauses_rejects_nested() {
        // Prod-inside-Prod → not flat.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![NNF::Prod(vec![lit_p(0)])]),
        ]);
        assert!(flat_clauses(&nnf).is_none());
    }

    #[test]
    fn mine_pairs_finds_complementary_cross_clause() {
        // Sum(Prod(¬a, ¬b), Prod(a, ¬c))
        // Complementary: ¬a in clause 0 alt 0 vs a in clause 1 alt 0.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
            NNF::Prod(vec![lit_p(0), lit_n(2)]),
        ]);
        let pairs = mine_pairs(&nnf);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0], (vec![0, 0], vec![1, 0]));
    }

    #[test]
    fn mine_pairs_finds_multiple_complements() {
        // Sum(Prod(a, b), Prod(¬a, ¬b)): a/¬a and b/¬b both pairs.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_n(0), lit_n(1)]),
        ]);
        let pairs = mine_pairs(&nnf);
        assert_eq!(pairs.len(), 2);
    }

    #[test]
    fn pair_box_size_computes_product_excluding_pair_clauses() {
        // 4 clauses with arities [2, 3, 2, 4].  Pair fixes clauses 0
        // and 2; box size = arities[1] * arities[3] = 3 * 4 = 12.
        let arities = [2usize, 3, 2, 4];
        let size = pair_box_size(&[(0, 0), (2, 0)], &arities);
        assert_eq!(size, 12);
    }

    #[test]
    fn pair_box_size_zero_when_same_clause() {
        let arities = [2usize, 3];
        assert_eq!(pair_box_size(&[(0, 0), (0, 1)], &arities), 0);
    }
}
