use std::collections::HashMap;
use crate::formula::{count_primes, extract_vars, get_base_name, parse, Node};

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

// ─── Position ─────────────────────────────────────────────────────────────────

/// A position of a literal within a matrix: a sequence of child indices,
/// each indexing into the `Vec` of a `Sum` or `Prod` node encountered on the
/// way down, terminating at a `Lit`.
///
/// For example, in `Sum([Prod([Lit(a), Lit(b)]), Lit(c)])`:
/// - `Lit(a)` is at `[0, 0]`
/// - `Lit(b)` is at `[0, 1]`
/// - `Lit(c)` is at `[1]`
pub type Position = Vec<usize>;

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

/// A path through a matrix: a sequence of `Position`s, one drawn from each
/// disjunct at every `Sum` node encountered on the way down.
pub type Path = Vec<Position>;

/// Compute every path through `m`, where each path is a sequence of positions
/// identifying the literals selected during the cross-product traversal.
///
/// - `Sum`  (OR):  cross-product — each path picks one position from **each** child.
/// - `Prod` (AND): union         — each path picks positions from **any one** child.
/// - `Lit`:        a single-element path containing the literal's own position.
pub fn paths(m: &Matrix) -> Vec<Path> {
    paths_from(m, vec![])
}

fn paths_from(m: &Matrix, pos: Position) -> Vec<Path> {
    match m {
        Matrix::Lit(_) => vec![vec![pos]],

        Matrix::Sum(children) => {
            children.iter().enumerate().fold(vec![vec![]], |acc, (i, child)| {
                let mut child_pos = pos.clone();
                child_pos.push(i);
                let cp = paths_from(child, child_pos);
                acc.into_iter()
                    .flat_map(|p| cp.iter().map(move |q| {
                        let mut combined = p.clone();
                        combined.extend_from_slice(q);
                        combined
                    }))
                    .collect()
            })
        }

        Matrix::Prod(children) => {
            children.iter().enumerate().flat_map(|(i, child)| {
                let mut child_pos = pos.clone();
                child_pos.push(i);
                paths_from(child, child_pos)
            }).collect()
        }
    }
}

/// Resolve a position to the `Lit` it points to in `m`, or `None` if the
/// position is out of bounds or does not end at a `Lit`.
pub fn lit_at<'a>(m: &'a Matrix, pos: &[usize]) -> Option<&'a Lit> {
    let mut node = m;
    for &i in pos {
        match node {
            Matrix::Lit(_) => return None,
            Matrix::Sum(ch) | Matrix::Prod(ch) => node = ch.get(i)?,
        }
    }
    match node {
        Matrix::Lit(l) => Some(l),
        _ => None,
    }
}

/// A path is *complementary* if it contains at least one complementary literal
/// pair `{l, l'}` (resolved via `m`).
pub fn is_complementary(path: &Path, m: &Matrix) -> bool {
    let lits: Vec<&Lit> = path.iter().filter_map(|pos| lit_at(m, pos)).collect();
    lits.iter().any(|l| lits.iter().any(|l2| l.is_complement_of(l2)))
}

/// A matrix is *valid* (tautology) iff every path is complementary.
pub fn is_valid(m: &Matrix) -> bool {
    paths(m).iter().all(|p| is_complementary(p, m))
}

/// A matrix is *satisfiable* iff its complement has at least one non-complementary path
/// (i.e. the complement is not a tautology).
pub fn is_satisfiable(m: &Matrix) -> bool {
    let comp = m.complement();
    paths(&comp).iter().any(|p| !is_complementary(p, &comp))
}

// ─── Literal positions ────────────────────────────────────────────────────────

/// Return every `Position` in `m` at which `target` appears.
pub fn literal_positions(m: &Matrix, target: &Lit) -> Vec<Position> {
    let mut result = Vec::new();
    collect_positions(m, target, &mut Vec::new(), &mut result);
    result
}

fn collect_positions(m: &Matrix, target: &Lit, prefix: &mut Position, out: &mut Vec<Position>) {
    match m {
        Matrix::Lit(l) => if l == target { out.push(prefix.clone()); }
        Matrix::Sum(ch) | Matrix::Prod(ch) => {
            for (i, child) in ch.iter().enumerate() {
                prefix.push(i);
                collect_positions(child, target, prefix, out);
                prefix.pop();
            }
        }
    }
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

    // Resolve each path's positions to (var, neg) pairs, sort for deterministic comparison.
    fn sorted_paths(m: &Matrix) -> Vec<Vec<(Var, bool)>> {
        let mut ps: Vec<Vec<(Var, bool)>> = paths(m)
            .into_iter()
            .map(|path| {
                let mut lits: Vec<(Var, bool)> = path.iter()
                    .filter_map(|pos| lit_at(m, pos))
                    .map(|l| (l.var, l.neg))
                    .collect();
                lits.sort();
                lits
            })
            .collect();
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

// ─── Formula → Matrix conversion ──────────────────────────────────────────────

pub fn node_to_matrix(node: &Node, var_index: &HashMap<String, u32>) -> Matrix {
    match node {
        Node::Var(name) => {
            let base = get_base_name(name);
            let neg  = count_primes(name) % 2 == 1;
            match base {
                "0" => if neg { Matrix::Prod(vec![]) } else { Matrix::Sum(vec![]) },
                "1" => if neg { Matrix::Sum(vec![]) } else { Matrix::Prod(vec![]) },
                _   => Matrix::Lit(Lit { var: *var_index.get(base).unwrap(), neg }),
            }
        }
        Node::And(ch) => Matrix::Prod(ch.iter().map(|c| node_to_matrix(c, var_index)).collect()),
        Node::Or(ch)  => Matrix::Sum(ch.iter().map(|c| node_to_matrix(c, var_index)).collect()),
    }
}

pub fn format_path(path: &Path, m: &Matrix, var_names: &[String]) -> String {
    if path.is_empty() { return "∅".to_string(); }
    let mut lits: Vec<String> = path.iter()
        .filter_map(|pos| lit_at(m, pos))
        .map(|l| {
            let name = &var_names[l.var as usize];
            if l.neg { format!("{}'", name) } else { name.clone() }
        })
        .collect();
    lits.sort();
    format!("{{{}}}", lits.join(", "))
}

pub fn parse_to_matrix(formula: &str) -> Result<(Matrix, Vec<String>), String> {
    let ast  = parse(formula)?;
    let vars: Vec<String> = extract_vars(&ast).into_iter().collect();
    if vars.len() > 20 {
        return Err("Too many variables for matrix analysis (max 20)".to_string());
    }
    let idx: HashMap<String, u32> = vars.iter().enumerate().map(|(i, v)| (v.clone(), i as u32)).collect();
    Ok((node_to_matrix(&ast, &idx), vars))
}

