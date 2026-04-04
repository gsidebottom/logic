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

/// A path through a matrix: a sequence of `Prod` member selections, one for
/// each `Prod` node encountered during depth-first traversal.
///
/// For example, in `Sum([Prod([A, Sum([B, C'])]), Prod([E, F', Sum([G, Prod([H, I])])])])`:
/// - `[0, 0]` = `{A, E}` (Prod0→A, Prod1→E)
/// - `[1, 0]` = `{B, C', E}` (Prod0→Sum[B,C'], Prod1→E)
/// - `[1, 2, 0]` = `{B, C', G, H}` (Prod0→Sum, Prod1→Sum→Prod[H,I]→H)
pub type Path = Vec<usize>;

/// Compute every path through `m`, where each path is a sequence of `Prod`
/// member selections identifying which child was chosen at each `Prod` node.
///
/// - `Sum`  (OR):  cross-product — each path picks one sub-path from **each** child.
/// - `Prod` (AND): union         — each path picks one child, prepending its index.
/// - `Lit`:        an empty path (no `Prod` selection needed).
pub fn paths(m: &Matrix) -> Vec<Path> {
    paths_from(m)
}

fn paths_from(m: &Matrix) -> Vec<Path> {
    match m {
        Matrix::Lit(_) => vec![vec![]],

        Matrix::Sum(children) => {
            children.iter().fold(vec![vec![]], |acc, child| {
                let cp = paths_from(child);
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
                paths_from(child).into_iter().map(move |mut p| {
                    p.insert(0, i);
                    p
                })
            }).collect()
        }
    }
}

/// Resolve a path to the literals it collects.
///
/// Follows the path's `Prod` member selections depth-first, collecting every
/// `Lit` encountered (including those reached via `Sum` cross-products).
pub fn lits_on_path<'a>(m: &'a Matrix, path: &[usize]) -> Vec<&'a Lit> {
    lits_on_path_inner(m, path).0
}

fn lits_on_path_inner<'a>(m: &'a Matrix, path: &[usize]) -> (Vec<&'a Lit>, usize) {
    match m {
        Matrix::Lit(l) => (vec![l], 0),
        Matrix::Prod(children) => {
            let sel = path[0];
            let (lits, consumed) = lits_on_path_inner(&children[sel], &path[1..]);
            (lits, 1 + consumed)
        }
        Matrix::Sum(children) => {
            let mut all_lits = Vec::new();
            let mut total = 0;
            for child in children {
                let (lits, consumed) = lits_on_path_inner(child, &path[total..]);
                all_lits.extend(lits);
                total += consumed;
            }
            (all_lits, total)
        }
    }
}

/// Resolve a path to the `Position`s (absolute tree addresses) of its literals.
pub fn positions_on_path(m: &Matrix, path: &[usize]) -> Vec<Position> {
    let mut result = Vec::new();
    positions_on_path_inner(m, path, &mut Vec::new(), &mut result);
    result
}

fn positions_on_path_inner(
    m: &Matrix,
    path: &[usize],
    pos: &mut Vec<usize>,
    out: &mut Vec<Position>,
) -> usize {
    match m {
        Matrix::Lit(_) => {
            out.push(pos.clone());
            0
        }
        Matrix::Prod(children) => {
            let sel = path[0];
            pos.push(sel);
            let consumed = positions_on_path_inner(&children[sel], &path[1..], pos, out);
            pos.pop();
            1 + consumed
        }
        Matrix::Sum(children) => {
            let mut total = 0;
            for (i, child) in children.iter().enumerate() {
                pos.push(i);
                let consumed = positions_on_path_inner(child, &path[total..], pos, out);
                pos.pop();
                total += consumed;
            }
            total
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
    let lits = lits_on_path(m, path);
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

    // Resolve each path's literals to (var, neg) pairs, sort for deterministic comparison.
    fn sorted_paths(m: &Matrix) -> Vec<Vec<(Var, bool)>> {
        let mut ps: Vec<Vec<(Var, bool)>> = paths(m)
            .into_iter()
            .map(|path| {
                let mut lits: Vec<(Var, bool)> = lits_on_path(m, &path)
                    .into_iter()
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

    // ── Path encoding ─────────────────────────────────────────────────────────

    #[test]
    fn test_path_encoding() {
        // A (B + C') + E F' (G + H I)
        // = Sum([Prod([A, Sum([B, C'])]), Prod([E, F', Sum([G, Prod([H, I])])])])
        let a = v(0); let b = v(1); let cn = vn(2); let e = v(3);
        let fn_ = vn(4); let g = v(5); let h = v(6); let i = v(7);
        let m = sum(vec![
            prod(vec![a, sum(vec![b, cn])]),
            prod(vec![e, fn_, sum(vec![g, prod(vec![h, i])])]),
        ]);

        // [0, 0] = {A, E}
        assert_eq!(lits_on_path(&m, &[0, 0]).iter().map(|l| l.var).collect::<Vec<_>>(),
                   vec![0, 3]);
        // [0, 1] = {A, F'}
        assert_eq!(lits_on_path(&m, &[0, 1]).iter().map(|l| (l.var, l.neg)).collect::<Vec<_>>(),
                   vec![(0, false), (4, true)]);
        // [1, 0] = {B, C', E}
        assert_eq!(lits_on_path(&m, &[1, 0]).iter().map(|l| l.var).collect::<Vec<_>>(),
                   vec![1, 2, 3]);
        // [1, 2, 0] = {B, C', G, H}
        assert_eq!(lits_on_path(&m, &[1, 2, 0]).iter().map(|l| l.var).collect::<Vec<_>>(),
                   vec![1, 2, 5, 6]);
        // [1, 2, 1] = {B, C', G, I}
        assert_eq!(lits_on_path(&m, &[1, 2, 1]).iter().map(|l| l.var).collect::<Vec<_>>(),
                   vec![1, 2, 5, 7]);
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
    let resolved = lits_on_path(m, path);
    if resolved.is_empty() { return "∅".to_string(); }
    let mut lits: Vec<String> = resolved.iter()
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

