//! XOR-recovery + GF(2) Gaussian-elimination preprocessing.
//!
//! Many "hard for resolution" instances are, underneath, pure systems
//! of XOR (parity) constraints: random mod-2 systems, Urquhart/Tseitin
//! formulas, the `x1`/`x2` family.  A k-XOR  `x1 ⊕ … ⊕ xk = b`  expands
//! to `2^(k-1)` clauses of length k in CNF, and *resolution* — hence
//! both plain CDCL and this matrix method — provably needs exponential
//! time to refute them (Urquhart 1987).  But the system is LINEAR over
//! GF(2): recover the XORs and Gaussian-eliminate, and the formula is
//! decided in polynomial time.  This is the CryptoMiniSat trick.
//!
//! Pipeline:
//!   1. [`recover_xors`] — find clause groups that encode an XOR.  A
//!      genuine k-XOR appears as exactly `2^(k-1)` length-k clauses over
//!      one variable set, all with the same negation parity.  Instances
//!      are shuffled, so we group by variable SET, not clause order.
//!   2. [`solve_xor_system`] — build the GF(2) matrix, row-reduce, and:
//!        * `Unsat` — a `0 = 1` row.  Each recovered XOR is *equivalent*
//!          to the clauses it consumed, so an inconsistent XOR subset
//!          ⇒ the whole formula is UNSAT.  Sound by recovery-exactness.
//!        * `Sat(model)` — every clause was consumed (a PURE-XOR
//!          formula) and the system is consistent; back-substitution
//!          yields a model, which is re-checked against the original
//!          clauses before returning (a recovery bug can then only
//!          degrade to `Indeterminate`, never an unsound SAT).
//!        * `Indeterminate` — non-XOR clauses remain (a mixed formula);
//!          the caller falls through to the matrix search.  Forcing the
//!          GE-derived units into the residual is a future extension.

use std::collections::HashMap;

/// An XOR constraint `vars[0] ⊕ vars[1] ⊕ … = rhs` (vars 1-indexed).
#[derive(Debug, Clone, PartialEq)]
pub struct XorConstraint {
    pub vars: Vec<u32>,
    pub rhs: bool,
}

/// Outcome of the XOR/GE pre-pass.
#[derive(Debug)]
pub enum XorGaussResult {
    /// The XOR subsystem is inconsistent ⇒ the formula is UNSAT.
    Unsat,
    /// Pure-XOR formula, satisfiable; `model[i]` is the value of var i+1.
    Sat(Vec<bool>),
    /// Couldn't decide (no XORs, or non-XOR clauses remain).
    Indeterminate { recovered: usize, consumed: usize, total: usize },
}

/// Largest XOR arity we try to recover.  `2^(k-1)` clauses per XOR, so
/// k=20 already implies 0.5M clauses; bigger groups are left as CNF.
const MAX_XOR_ARITY: usize = 20;

/// Recover XOR constraints from `clauses`.  Returns the constraints and
/// a per-clause flag marking whether it was consumed by some XOR.
pub fn recover_xors(clauses: &[Vec<i32>]) -> (Vec<XorConstraint>, Vec<bool>) {
    // Group clause indices by their variable SET (sorted abs lits).
    // Only "clean" clauses qualify: arity within cap, no repeated
    // variable (which also rejects a tautological `x ∨ ¬x`).
    let mut groups: HashMap<Vec<u32>, Vec<usize>> = HashMap::new();
    for (ci, cl) in clauses.iter().enumerate() {
        if cl.is_empty() || cl.len() > MAX_XOR_ARITY {
            continue;
        }
        let mut vars: Vec<u32> = cl.iter().map(|&l| l.unsigned_abs()).collect();
        vars.sort_unstable();
        if vars.windows(2).any(|w| w[0] == w[1]) {
            continue;
        }
        groups.entry(vars).or_default().push(ci);
    }

    let mut xors = Vec::new();
    let mut consumed = vec![false; clauses.len()];

    for (vars, idxs) in &groups {
        let k = vars.len();
        let need = 1usize << (k - 1); // 2^(k-1) clauses for a complete k-XOR
        if idxs.len() < need {
            continue; // not enough clauses to complete even one XOR
        }
        let pos: HashMap<u32, usize> =
            vars.iter().enumerate().map(|(i, &v)| (v, i)).collect();
        // Bucket DISTINCT clauses by negation parity.  Each clause is
        // identified by the bitmask of which vars it negates.
        let mut by_parity: [HashMap<u32, usize>; 2] = [HashMap::new(), HashMap::new()];
        for &ci in idxs {
            let mut mask: u32 = 0;
            let mut negs = 0usize;
            for &l in &clauses[ci] {
                let p = pos[&l.unsigned_abs()];
                if l < 0 {
                    mask |= 1u32 << p;
                    negs += 1;
                }
            }
            by_parity[negs & 1].entry(mask).or_insert(ci);
        }
        // A parity bucket with exactly 2^(k-1) DISTINCT clauses contains
        // every violating assignment of that parity ⇒ a complete k-XOR.
        // Negation-parity p ⇒ rhs b = 1 ⊕ p.  (Both buckets full ⇒ two
        // contradictory XORs over the same vars ⇒ GE finds UNSAT.)
        for p in 0..2 {
            if by_parity[p].len() == need {
                xors.push(XorConstraint {
                    vars: vars.clone(),
                    rhs: (1 ^ p) != 0,
                });
                for &ci in by_parity[p].values() {
                    consumed[ci] = true;
                }
            }
        }
    }
    (xors, consumed)
}

enum GaussOutcome {
    Unsat,
    Consistent(Vec<bool>),
}

/// Gaussian-eliminate the XOR system over GF(2).  On consistency,
/// returns a model (free variables set false, pivots back-substituted).
fn gauss(nvars: usize, xors: &[XorConstraint]) -> GaussOutcome {
    let words = nvars / 64 + 1;
    // Each row = (coefficient bitset over vars, rhs bit).  Bit v-1 ↔ var v.
    let mut rows: Vec<(Vec<u64>, bool)> = xors
        .iter()
        .map(|x| {
            let mut c = vec![0u64; words];
            for &v in &x.vars {
                let b = (v - 1) as usize;
                c[b / 64] |= 1u64 << (b % 64);
            }
            (c, x.rhs)
        })
        .collect();

    let mut pivot_row_of_col: Vec<Option<usize>> = vec![None; nvars];
    let mut pr = 0usize; // next free pivot row
    for col in 0..nvars {
        if pr >= rows.len() {
            break;
        }
        let w = col / 64;
        let bit = 1u64 << (col % 64);
        // Find a row at/below pr with this column set.
        let Some(sel) = (pr..rows.len()).find(|&r| rows[r].0[w] & bit != 0) else {
            continue;
        };
        rows.swap(pr, sel);
        // Reduced row-echelon: clear this column from every OTHER row.
        let pivot = rows[pr].clone();
        for r in 0..rows.len() {
            if r != pr && rows[r].0[w] & bit != 0 {
                for i in 0..words {
                    rows[r].0[i] ^= pivot.0[i];
                }
                rows[r].1 ^= pivot.1;
            }
        }
        pivot_row_of_col[col] = Some(pr);
        pr += 1;
    }

    // Inconsistency: a row with no coefficients but rhs = 1 (0 = 1).
    for (c, rhs) in &rows {
        if *rhs && c.iter().all(|&w| w == 0) {
            return GaussOutcome::Unsat;
        }
    }
    // Model: free variables false; each pivot variable takes its row's
    // rhs (after RREF a pivot row has only the pivot + free vars, and
    // free vars are false).
    let mut model = vec![false; nvars];
    for col in 0..nvars {
        if let Some(r) = pivot_row_of_col[col] {
            model[col] = rows[r].1;
        }
    }
    GaussOutcome::Consistent(model)
}

fn model_satisfies(model: &[bool], clauses: &[Vec<i32>]) -> bool {
    clauses.iter().all(|cl| {
        cl.iter().any(|&l| {
            let v = l.unsigned_abs() as usize;
            v >= 1 && v <= model.len() && model[v - 1] == (l > 0)
        })
    })
}

/// Run the full XOR-recovery + Gaussian-elimination pre-pass.
pub fn solve_xor_system(nvars: usize, clauses: &[Vec<i32>]) -> XorGaussResult {
    let (xors, consumed) = recover_xors(clauses);
    let n_consumed = consumed.iter().filter(|&&c| c).count();
    if xors.is_empty() {
        return XorGaussResult::Indeterminate {
            recovered: 0,
            consumed: 0,
            total: clauses.len(),
        };
    }
    match gauss(nvars, &xors) {
        GaussOutcome::Unsat => XorGaussResult::Unsat,
        GaussOutcome::Consistent(model) => {
            // Decide SAT only for a PURE-XOR formula (every clause
            // consumed) AND only after re-checking the model — so a
            // recovery bug degrades to Indeterminate, never unsound SAT.
            if n_consumed == clauses.len() && model_satisfies(&model, clauses) {
                XorGaussResult::Sat(model)
            } else {
                XorGaussResult::Indeterminate {
                    recovered: xors.len(),
                    consumed: n_consumed,
                    total: clauses.len(),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// CNF for `a ⊕ b ⊕ c = 1`: the 4 clauses with even negation count.
    fn xor3_eq1() -> Vec<Vec<i32>> {
        vec![
            vec![1, 2, 3],     // 0 negs
            vec![1, -2, -3],   // 2 negs
            vec![-1, 2, -3],   // 2 negs
            vec![-1, -2, 3],   // 2 negs
        ]
    }

    #[test]
    fn recovers_a_single_3xor() {
        let (xors, consumed) = recover_xors(&xor3_eq1());
        assert_eq!(xors.len(), 1);
        assert_eq!(xors[0].vars, vec![1, 2, 3]);
        assert!(xors[0].rhs, "a⊕b⊕c=1 → rhs true");
        assert!(consumed.iter().all(|&c| c), "all 4 clauses consumed");
    }

    #[test]
    fn pure_xor_sat_model_checks_out() {
        // a⊕b⊕c=1 alone is satisfiable.
        match solve_xor_system(3, &xor3_eq1()) {
            XorGaussResult::Sat(m) => assert!(model_satisfies(&m, &xor3_eq1())),
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn contradictory_xors_are_unsat() {
        // a⊕b⊕c=1 AND a⊕b⊕c=0 over the same vars → UNSAT.  Supply all
        // 8 clauses (both parity buckets full).
        let mut cl = xor3_eq1();
        cl.extend(vec![
            vec![-1, -2, -3], // 3 negs (odd) → part of =0
            vec![-1, 2, 3],
            vec![1, -2, 3],
            vec![1, 2, -3],
        ]);
        assert!(matches!(solve_xor_system(3, &cl), XorGaussResult::Unsat));
    }

    #[test]
    fn linear_system_unsat() {
        // x=1 (1-XOR), y=1 (1-XOR), and x⊕y=1 (2-XOR, CNF {(x∨y),(¬x∨¬y)}).
        // x=1,y=1 force x⊕y=0, contradicting x⊕y=1 → GE finds UNSAT.
        let cl = vec![vec![1], vec![2], vec![1, 2], vec![-1, -2]];
        assert!(matches!(solve_xor_system(2, &cl), XorGaussResult::Unsat));
    }

    #[test]
    fn mixed_formula_is_indeterminate() {
        // One real XOR plus a stray non-XOR clause → not pure XOR.
        let mut cl = xor3_eq1();
        cl.push(vec![4, 5]); // length-2 over fresh vars, lone clause (not a full 2-XOR)
        assert!(matches!(
            solve_xor_system(5, &cl),
            XorGaussResult::Indeterminate { .. }
        ));
    }
}
