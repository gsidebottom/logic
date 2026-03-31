use std::collections::BTreeSet;

// ─── Literal ──────────────────────────────────────────────────────────────────

/// A propositional variable index.
pub type Var = u32;

/// A literal: a variable with a polarity (positive or negative).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit {
    pub var: Var,
    pub neg: bool,
}

impl Lit {
    pub fn pos(var: Var) -> Self { Lit { var, neg: false } }
    pub fn neg(var: Var) -> Self { Lit { var, neg: true  } }

    pub fn complement(&self) -> Self { Lit { var: self.var, neg: !self.neg } }
    pub fn is_complement_of(&self, other: &Lit) -> bool {
        self.var == other.var && self.neg != other.neg
    }
}

// ─── Matrix ───────────────────────────────────────────────────────────────────

/// A formula in negation normal form (NNF / Matrix).
///
/// `∑` (Sum)  = disjunction (OR)
/// `∏` (Prod) = conjunction (AND)
#[derive(Clone, Debug)]
pub enum Matrix {
    Lit(Lit),
    Sum(Vec<Matrix>),
    Prod(Vec<Matrix>),
}

impl Matrix {
    /// Push negation inward (De Morgan) to produce the complement in NNF.
    pub fn complement(&self) -> Self {
        match self {
            Matrix::Lit(l)      => Matrix::Lit(l.complement()),
            Matrix::Sum(ch)     => Matrix::Prod(ch.iter().map(|c| c.complement()).collect()),
            Matrix::Prod(ch)    => Matrix::Sum(ch.iter().map(|c| c.complement()).collect()),
        }
    }
}

// ─── Paths ────────────────────────────────────────────────────────────────────

/// A path through a matrix: a set of literals, one drawn from each disjunct at
/// every Sum node encountered on the way down.
pub type Path = BTreeSet<Lit>;

/// Compute every path through `m`.
///
/// - `Sum`  (OR):  cross-product — a path merges one sub-path from **each** child.
/// - `Prod` (AND): union         — a path passes through **any one** child.
/// - `Lit`:        a single singleton path.
pub fn paths(m: &Matrix) -> Vec<Path> {
    match m {
        Matrix::Lit(l) => vec![std::iter::once(l.clone()).collect()],

        Matrix::Sum(children) => {
            // Start with one empty path; extend it by cross-producting each child.
            children.iter().fold(vec![Path::new()], |acc, child| {
                let cp = paths(child);
                acc.into_iter()
                    .flat_map(|p| cp.iter().map(move |q| p.iter().chain(q).cloned().collect()))
                    .collect()
            })
        }

        Matrix::Prod(children) => {
            children.iter().flat_map(|child| paths(child)).collect()
        }
    }
}

/// A path is *complementary* if it contains at least one complementary literal pair `{l, l'}`.
pub fn is_complementary(path: &Path) -> bool {
    path.iter().any(|l| path.contains(&l.complement()))
}

/// A matrix is *valid* (tautology) iff every path is complementary.
pub fn is_valid(m: &Matrix) -> bool {
    paths(m).iter().all(is_complementary)
}

/// A matrix is *satisfiable* iff its complement has at least one non-complementary path
/// (i.e. the complement is not a tautology).
pub fn is_satisfiable(m: &Matrix) -> bool {
    paths(&m.complement()).iter().any(|p| !is_complementary(p))
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── Helpers ───────────────────────────────────────────────────────────────

    fn v(n: Var) -> Matrix { Matrix::Lit(Lit::pos(n)) }
    fn vn(n: Var) -> Matrix { Matrix::Lit(Lit::neg(n)) }
    fn sum(ch: Vec<Matrix>) -> Matrix { Matrix::Sum(ch) }
    fn prod(ch: Vec<Matrix>) -> Matrix { Matrix::Prod(ch) }

    // Sort paths for deterministic comparison.
    fn sorted_paths(m: &Matrix) -> Vec<Vec<(Var, bool)>> {
        let mut ps: Vec<Vec<(Var, bool)>> = paths(m)
            .into_iter()
            .map(|p| p.into_iter().map(|l| (l.var, l.neg)).collect())
            .collect();
        ps.iter_mut().for_each(|p| p.sort());
        ps.sort();
        ps
    }

    // ── Literal paths ─────────────────────────────────────────────────────────

    #[test]
    fn test_lit_pos_path() {
        assert_eq!(sorted_paths(&v(0)), vec![vec![(0, false)]]);
    }

    #[test]
    fn test_lit_neg_path() {
        assert_eq!(sorted_paths(&vn(0)), vec![vec![(0, true)]]);
    }

    // ── Prod paths ────────────────────────────────────────────────────────────

    #[test]
    fn test_prod_two_lits() {
        // a · b  →  two paths: {a}, {b}
        let m = prod(vec![v(0), v(1)]);
        assert_eq!(sorted_paths(&m), vec![vec![(0, false)], vec![(1, false)]]);
    }

    #[test]
    fn test_prod_three_lits() {
        // a · b · c  →  three paths
        let m = prod(vec![v(0), v(1), v(2)]);
        assert_eq!(sorted_paths(&m), vec![
            vec![(0, false)],
            vec![(1, false)],
            vec![(2, false)],
        ]);
    }

    // ── Sum paths ─────────────────────────────────────────────────────────────

    #[test]
    fn test_sum_two_lits() {
        // a + b  →  one path: {a, b}
        let m = sum(vec![v(0), v(1)]);
        assert_eq!(sorted_paths(&m), vec![vec![(0, false), (1, false)]]);
    }

    #[test]
    fn test_sum_of_prods() {
        // (a · b) + (c · d)  →  four paths: {a,c}, {a,d}, {b,c}, {b,d}
        let m = sum(vec![prod(vec![v(0), v(1)]), prod(vec![v(2), v(3)])]);
        let mut got = sorted_paths(&m);
        got.sort();
        let mut exp = vec![
            vec![(0,false),(2,false)],
            vec![(0,false),(3,false)],
            vec![(1,false),(2,false)],
            vec![(1,false),(3,false)],
        ];
        exp.sort();
        assert_eq!(got, exp);
    }

    // ── Complement ────────────────────────────────────────────────────────────

    #[test]
    fn test_complement_lit() {
        assert!(matches!(v(0).complement(), Matrix::Lit(l) if l == Lit::neg(0)));
        assert!(matches!(vn(0).complement(), Matrix::Lit(l) if l == Lit::pos(0)));
    }

    #[test]
    fn test_complement_sum_becomes_prod() {
        // (a + b)' = a' · b'
        let m = sum(vec![v(0), v(1)]).complement();
        assert!(matches!(m, Matrix::Prod(_)));
    }

    #[test]
    fn test_complement_prod_becomes_sum() {
        // (a · b)' = a' + b'
        let m = prod(vec![v(0), v(1)]).complement();
        assert!(matches!(m, Matrix::Sum(_)));
    }

    // ── Validity ──────────────────────────────────────────────────────────────

    #[test]
    fn test_valid_tautology_a_or_not_a() {
        // a + a'  is a tautology
        let m = sum(vec![v(0), vn(0)]);
        assert!(is_valid(&m));
    }

    #[test]
    fn test_not_valid_simple_var() {
        // a alone is not a tautology
        assert!(!is_valid(&v(0)));
    }

    #[test]
    fn test_not_valid_a_or_b() {
        // a + b is not a tautology (a=0, b=0 falsifies it)
        assert!(!is_valid(&sum(vec![v(0), v(1)])));
    }

    #[test]
    fn test_valid_document_example() {
        // ((a·b) + (a'+b')) · ((a'+b') + (a·b))  is a tautology
        let ab   = prod(vec![v(0), v(1)]);
        let nanb = sum(vec![vn(0), vn(1)]);
        let left  = sum(vec![ab.clone(), nanb.clone()]);
        let right = sum(vec![nanb, ab]);
        let m = prod(vec![left, right]);
        assert!(is_valid(&m));
    }

    // ── Satisfiability ────────────────────────────────────────────────────────

    #[test]
    fn test_satisfiable_simple_var() {
        assert!(is_satisfiable(&v(0)));
    }

    #[test]
    fn test_satisfiable_tautology() {
        // a + a'  is satisfiable (any assignment works)
        assert!(is_satisfiable(&sum(vec![v(0), vn(0)])));
    }

    #[test]
    fn test_unsatisfiable_contradiction() {
        // a · a'  is unsatisfiable
        assert!(!is_satisfiable(&prod(vec![v(0), vn(0)])));
    }

    #[test]
    fn test_satisfiable_a_or_b() {
        assert!(is_satisfiable(&sum(vec![v(0), v(1)])));
    }

    #[test]
    fn test_unsatisfiable_cnf() {
        // (a + b) · (a + b') · (a' + b) · (a' + b')  is unsatisfiable
        let m = prod(vec![
            sum(vec![v(0), v(1)]),
            sum(vec![v(0), vn(1)]),
            sum(vec![vn(0), v(1)]),
            sum(vec![vn(0), vn(1)]),
        ]);
        assert!(!is_satisfiable(&m));
    }
}
