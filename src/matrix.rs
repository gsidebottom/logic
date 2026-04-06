use std::collections::HashMap;
use serde::{Deserialize, Serialize};
use crate::formula::{count_primes, get_base_name, Ast, Node};

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

// ─── Path / Cover / Paths ────────────────────────────────────────────────────

/// A path through a matrix: a sequence of `Prod` member selections, one for
/// each `Prod` node encountered during depth-first traversal.
///
/// For example, in `Sum([Prod([A, Sum([B, C'])]), Prod([E, F', Sum([G, Prod([H, I])])])])`:
/// - `[0, 0]` = `{A, E}` (Prod0→A, Prod1→E)
/// - `[1, 0]` = `{B, C', E}` (Prod0→Sum[B,C'], Prod1→E)
/// - `[1, 2, 0]` = `{B, C', G, H}` (Prod0→Sum, Prod1→Sum→Prod[H,I]→H)
pub type ProdPath = Vec<usize>;

/// A set of complementary literal pairs identified by their `Position`s.
pub type Cover = Vec<(Position, Position)>;

/// Parameters controlling proof search.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PathParams {
    #[serde(default = "PathParams::default_paths_limit")]
    pub paths_limit: usize,
    #[serde(default)]
    pub collect_covered_paths: bool,
}

impl PathParams {
    fn default_paths_limit() -> usize { 1 }
}

impl Default for PathParams {
    fn default() -> Self {
        PathParams {
            paths_limit: Self::default_paths_limit(),
            collect_covered_paths: false,
        }
    }
}

/// Result of checking validity of a matrix.
///
/// The matrix is valid (a tautology) iff `uncovered_paths` is empty.
/// `cover` and `covered_path_prefixes` are always populated.
/// `covered_paths` is populated only when `PathParams::collect_covered_paths` is true.
pub struct Paths {
    pub cover: Cover,
    pub covered_path_prefixes: Vec<Vec<Position>>,
    pub covered_paths: Vec<ProdPath>,
    pub uncovered_paths: Vec<ProdPath>,
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

    /// Resolve a path to the literals it collects.
    ///
    /// Follows the path's `Prod` member selections depth-first, collecting every
    /// `Lit` encountered (including those reached via `Sum` cross-products).
    pub fn lits_on_path(&self, path: &[usize]) -> Vec<&Lit> {
        fn inner<'a>(m: &'a Matrix, path: &[usize]) -> (Vec<&'a Lit>, usize) {
            match m {
                Matrix::Lit(l) => (vec![l], 0),
                Matrix::Prod(children) => {
                    let sel = path[0];
                    let (lits, consumed) = inner(&children[sel], &path[1..]);
                    (lits, 1 + consumed)
                }
                Matrix::Sum(children) => {
                    let mut all_lits = Vec::new();
                    let mut total = 0;
                    for child in children {
                        let (lits, consumed) = inner(child, &path[total..]);
                        all_lits.extend(lits);
                        total += consumed;
                    }
                    (all_lits, total)
                }
            }
        }
        inner(self, path).0
    }

    /// Compute every path through this matrix, where each path is a sequence
    /// of `Prod` member selections identifying which child was chosen at each
    /// `Prod` node.
    ///
    /// - `Sum`  (OR):  cross-product — each path picks one sub-path from **each** child.
    /// - `Prod` (AND): union         — each path picks one child, prepending its index.
    /// - `Lit`:        an empty path (no `Prod` selection needed).
    pub fn paths_iter(&self) -> impl Iterator<Item = ProdPath> {
        fn collect(m: &Matrix) -> Vec<ProdPath> {
            match m {
                Matrix::Lit(_) => vec![vec![]],
                Matrix::Sum(children) => {
                    children.iter().fold(vec![vec![]], |acc, child| {
                        let cp = collect(child);
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
                        collect(child).into_iter().map(move |mut p| {
                            p.insert(0, i);
                            p
                        })
                    }).collect()
                }
            }
        }
        collect(self).into_iter()
    }

    /// Resolve a path to the `Position`s (absolute tree addresses) of its literals.
    pub fn positions_on_path(&self, path: &[usize]) -> Vec<Position> {
        fn inner(m: &Matrix, path: &[usize], pos: &mut Vec<usize>, out: &mut Vec<Position>) -> usize {
            match m {
                Matrix::Lit(_) => {
                    out.push(pos.clone());
                    0
                }
                Matrix::Prod(children) => {
                    let sel = path[0];
                    pos.push(sel);
                    let consumed = inner(&children[sel], &path[1..], pos, out);
                    pos.pop();
                    1 + consumed
                }
                Matrix::Sum(children) => {
                    let mut total = 0;
                    for (i, child) in children.iter().enumerate() {
                        pos.push(i);
                        let consumed = inner(child, &path[total..], pos, out);
                        pos.pop();
                        total += consumed;
                    }
                    total
                }
            }
        }
        let mut result = Vec::new();
        inner(self, path, &mut Vec::new(), &mut result);
        result
    }

    /// Return every `Position` at which `target` appears.
    pub fn literal_positions(&self, target: &Lit) -> Vec<Position> {
        fn inner(m: &Matrix, target: &Lit, prefix: &mut Position, out: &mut Vec<Position>) {
            match m {
                Matrix::Lit(l) => if l == target { out.push(prefix.clone()); }
                Matrix::Sum(ch) | Matrix::Prod(ch) => {
                    for (i, child) in ch.iter().enumerate() {
                        prefix.push(i);
                        inner(child, target, prefix, out);
                        prefix.pop();
                    }
                }
            }
        }
        let mut result = Vec::new();
        inner(self, target, &mut Vec::new(), &mut result);
        result
    }

    /// Resolve a position to the `Lit` it points to, or `None` if the
    /// position is out of bounds or does not end at a `Lit`.
    pub fn lit_at(&self, pos: &[usize]) -> Option<&Lit> {
        let mut node = self;
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

    /// A path is *complementary* if it contains at least one complementary
    /// literal pair `{l, l'}`.
    pub fn is_complementary(&self, path: &ProdPath) -> bool {
        let lits = self.lits_on_path(path);
        lits.iter().any(|l| lits.iter().any(|l2| l.is_complement_of(l2)))
    }

    /// A matrix is *valid* (tautology) iff every path is complementary.
    pub fn is_valid(&self) -> bool {
        self.paths_iter().all(|p| self.is_complementary(&p))
    }

    /// A matrix is *satisfiable* iff its complement has at least one
    /// non-complementary path (i.e. the complement is not a tautology).
    pub fn is_satisfiable(&self) -> bool {
        let comp = self.complement();
        comp.paths_iter().any(|p| !comp.is_complementary(&p))
    }

    /// Covering pairs for all paths.
    ///
    /// Iterates through each path. If any pair already in the cover has both
    /// its positions in the path, the path is already covered. Otherwise,
    /// finds the first complementary literal pair within the path and adds it
    /// to the cover.
    pub fn cover(&self, paths: &[ProdPath]) -> Cover {
        let resolved: Vec<Vec<Position>> = paths.iter()
            .map(|p| self.positions_on_path(p))
            .collect();

        let mut result: Cover = Vec::new();

        'path: for positions in &resolved {
            for (pa, pb) in &result {
                if positions.contains(pa) && positions.contains(pb) {
                    continue 'path;
                }
            }
            'found: for pos_a in positions {
                if let Some(lit_a) = self.lit_at(pos_a) {
                    for pos_b in positions {
                        if let Some(lit_b) = self.lit_at(pos_b) {
                            if lit_a.is_complement_of(lit_b) {
                                result.push((pos_a.clone(), pos_b.clone()));
                                break 'found;
                            }
                        }
                    }
                }
            }
        }

        result
    }

    /// Check validity using prefix-pruned depth-first search.
    ///
    /// Uses `for_each_path_prefix` to prune paths whose prefix already
    /// contains a complementary pair. For invalid matrices this finds
    /// non-complementary paths (up to `paths_limit`) without
    /// enumerating all paths.
    pub fn paths(&self, params: Option<PathParams>) -> Paths {
        let params = params.unwrap_or_default();
        let mut uncovered_paths = Vec::new();
        let mut covered_paths = Vec::new();
        let mut cover = Cover::new();
        let mut covered_path_prefixes = Vec::new();
        let mut covered_at_depth: Option<usize> = None;
        let mut path_count: usize = 0;

        self.for_each_path_prefix(|lits, positions, prod_path| {
            if path_count >= params.paths_limit {
                return false;
            }
            // Detect backtrack: if we shrunk past the depth where we found
            // a complementary pair, we're no longer in a covered subtree.
            if let Some(d) = covered_at_depth {
                if lits.len() < d {
                    covered_at_depth = None;
                }
            }
            if let Some(path) = prod_path {
                if covered_at_depth.is_some() {
                    if params.collect_covered_paths {
                        covered_paths.push(path.clone());
                        path_count += 1;
                    }
                } else {
                    uncovered_paths.push(path.clone());
                    path_count += 1;
                }
                return path_count < params.paths_limit;
            }
            // Check if the newest literal has a complement among prior ones.
            if covered_at_depth.is_none() {
                if let Some(new_lit) = lits.last() {
                    let new_pos = positions.last().unwrap();
                    for (j, prior) in lits[..lits.len() - 1].iter().enumerate() {
                        if prior.is_complement_of(new_lit) {
                            cover.push((positions[j].clone(), new_pos.clone()));
                            covered_path_prefixes.push(positions.clone());
                            covered_at_depth = Some(lits.len());
                            if !params.collect_covered_paths {
                                return false; // prune
                            }
                            return true;
                        }
                    }
                }
            }
            true
        });

        Paths { cover, covered_path_prefixes, covered_paths, uncovered_paths }
    }

    /// Reference implementation: check validity by examining all paths.
    ///
    /// Reference implementation: check validity by examining all paths.
    pub fn paths_reference(&self) -> Paths {
        let all_paths: Vec<ProdPath> = self.paths_iter().collect();
        let uncovered_paths: Vec<ProdPath> = all_paths.iter()
            .filter(|p| !self.is_complementary(p))
            .cloned()
            .collect();
        if uncovered_paths.is_empty() {
            Paths { cover: self.cover(&all_paths), covered_path_prefixes: vec![], covered_paths: vec![], uncovered_paths }
        } else {
            Paths { cover: vec![], covered_path_prefixes: vec![], covered_paths: vec![], uncovered_paths }
        }
    }

    /// Depth-first traversal of all path prefixes, with pruning.
    ///
    /// Calls `f(lits, positions, prod_path)` at each step of the traversal:
    /// - When a `Prod` member is selected or a `Lit` is reached: `prod_path` is `None`
    /// - When a full path is completed: `prod_path` is `Some(&path)`
    ///
    /// `lits` and `positions` are parallel vectors: `positions[i]` is the
    /// absolute tree address of `lits[i]`.
    ///
    /// If `f` returns `true`, traversal continues forward; if `false`, it
    /// backtracks to the last `Prod` member choice.
    pub fn for_each_path_prefix(
        &self,
        mut f: impl FnMut(&Vec<&Lit>, &Vec<Position>, Option<&ProdPath>) -> bool,
    ) {
        type Lits<'a> = Vec<&'a Lit>;
        type Positions = Vec<Position>;

        fn traverse<'a, F: FnMut(&Lits<'a>, &Positions, Option<&ProdPath>) -> bool>(
            m: &'a Matrix,
            path: &mut ProdPath,
            lits: &mut Lits<'a>,
            positions: &mut Positions,
            pos: &mut Position,
            f: &mut F,
            then: &mut dyn FnMut(&mut ProdPath, &mut Lits<'a>, &mut Positions, &mut Position, &mut F),
        ) {
            match m {
                Matrix::Lit(l) => {
                    lits.push(l);
                    positions.push(pos.clone());
                    if f(lits, positions, None) {
                        then(path, lits, positions, pos, f);
                    }
                    positions.pop();
                    lits.pop();
                }
                Matrix::Prod(children) => {
                    for (i, child) in children.iter().enumerate() {
                        path.push(i);
                        pos.push(i);
                        if f(lits, positions, None) {
                            traverse(child, path, lits, positions, pos, f, then);
                        }
                        pos.pop();
                        path.pop();
                    }
                }
                Matrix::Sum(children) => {
                    traverse_sum(children, 0, path, lits, positions, pos, f, then);
                }
            }
        }

        #[allow(clippy::too_many_arguments)]
        fn traverse_sum<'a, F: FnMut(&Lits<'a>, &Positions, Option<&ProdPath>) -> bool>(
            children: &'a [Matrix],
            idx: usize,
            path: &mut ProdPath,
            lits: &mut Lits<'a>,
            positions: &mut Positions,
            pos: &mut Position,
            f: &mut F,
            then: &mut dyn FnMut(&mut ProdPath, &mut Lits<'a>, &mut Positions, &mut Position, &mut F),
        ) {
            if idx >= children.len() {
                then(path, lits, positions, pos, f);
            } else {
                let pos_len = pos.len();
                pos.push(idx);
                traverse(&children[idx], path, lits, positions, pos, f,
                    &mut |path, lits, positions, pos, f| {
                        let saved_pos = pos.clone();
                        pos.truncate(pos_len);
                        traverse_sum(children, idx + 1, path, lits, positions, pos, f, then);
                        *pos = saved_pos;
                    },
                );
                pos.truncate(pos_len);
            }
        }

        let mut path = ProdPath::new();
        let mut lits = Vec::new();
        let mut positions = Vec::new();
        let mut pos = Vec::new();
        traverse(self, &mut path, &mut lits, &mut positions, &mut pos, &mut f,
            &mut |path, lits, positions, _pos, f| {
                f(lits, positions, Some(path));
            },
        );
    }
}

// ─── Formula → Matrix conversion ──────────────────────────────────────────────

impl From<&Ast> for Matrix {
    fn from(ast: &Ast) -> Self {
        fn convert(node: &Node, var_index: &HashMap<String, u32>) -> Matrix {
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
                Node::And(ch) => {
                    let mut members = Vec::new();
                    for c in ch {
                        match convert(c, var_index) {
                            Matrix::Prod(inner) => members.extend(inner),
                            other => members.push(other),
                        }
                    }
                    Matrix::Prod(members)
                }
                Node::Or(ch) => {
                    let mut members = Vec::new();
                    for c in ch {
                        match convert(c, var_index) {
                            Matrix::Sum(inner) => members.extend(inner),
                            other => members.push(other),
                        }
                    }
                    Matrix::Sum(members)
                }
            }
        }
        convert(&ast.root, &ast.var_index)
    }
}

pub fn format_path(path: &ProdPath, m: &Matrix, var_names: &[String]) -> String {
    let resolved = m.lits_on_path(path);
    if resolved.is_empty() { return "∅".to_string(); }
    let lits: Vec<String> = resolved.iter()
        .map(|l| {
            let name = &var_names[l.var as usize];
            if l.neg { format!("{}'", name) } else { name.clone() }
        })
        .collect();
    format!("{{{}}}", lits.join(", "))
}

pub fn parse_to_matrix(formula: &str) -> Result<(Matrix, Vec<String>), String> {
    let ast = Ast::try_from(formula)?;
    Ok((Matrix::from(&ast), ast.vars))
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
        let mut ps: Vec<Vec<(Var, bool)>> = m.paths_iter()
            .map(|path| {
                let mut lits: Vec<(Var, bool)> = m.lits_on_path(&path)
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

    // ── Formula-to-matrix flattening ────────────────────────────────────────

    #[test]
    fn test_parse_prod_flattening() {
        // (A B) (C D) should produce Prod(A, B, C, D), not Prod(A, B, Prod(C, D))
        let (m, _) = parse_to_matrix("(A B) (C D)").unwrap();
        match &m {
            Matrix::Prod(children) => {
                assert_eq!(children.len(), 4, "expected 4 children, got {:?}", m);
                assert!(children.iter().all(|c| matches!(c, Matrix::Lit(_))));
            }
            _ => panic!("expected Prod, got {:?}", m),
        }
    }

    #[test]
    fn test_parse_sum_flattening() {
        // (A + B) + (C + D) should produce Sum(A, B, C, D), not Sum(A, B, Sum(C, D))
        let (m, _) = parse_to_matrix("(A + B) + (C + D)").unwrap();
        match &m {
            Matrix::Sum(children) => {
                assert_eq!(children.len(), 4, "expected 4 children, got {:?}", m);
                assert!(children.iter().all(|c| matches!(c, Matrix::Lit(_))));
            }
            _ => panic!("expected Sum, got {:?}", m),
        }
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
        assert_eq!(m.lits_on_path(&[0, 0]).iter().map(|l| l.var).collect::<Vec<_>>(),
                   vec![0, 3]);
        // [0, 1] = {A, F'}
        assert_eq!(m.lits_on_path(&[0, 1]).iter().map(|l| (l.var, l.neg)).collect::<Vec<_>>(),
                   vec![(0, false), (4, true)]);
        // [1, 0] = {B, C', E}
        assert_eq!(m.lits_on_path(&[1, 0]).iter().map(|l| l.var).collect::<Vec<_>>(),
                   vec![1, 2, 3]);
        // [1, 2, 0] = {B, C', G, H}
        assert_eq!(m.lits_on_path(&[1, 2, 0]).iter().map(|l| l.var).collect::<Vec<_>>(),
                   vec![1, 2, 5, 6]);
        // [1, 2, 1] = {B, C', G, I}
        assert_eq!(m.lits_on_path(&[1, 2, 1]).iter().map(|l| l.var).collect::<Vec<_>>(),
                   vec![1, 2, 5, 7]);
    }

    // ── for_each_path_prefix ─────────────────────────────────────────────────

    #[test]
    fn test_for_each_path_prefix_collects_all_paths() {
        // (a · b) + (c · d) — full paths have 2 literals
        let m = sum(vec![prod(vec![v(0), v(1)]), prod(vec![v(2), v(3)])]);
        let mut full_paths = Vec::new();
        let expected: Vec<ProdPath> = m.paths_iter().collect();
        m.for_each_path_prefix(|_lits, _pos, prod_path| {
            if let Some(path) = prod_path {
                full_paths.push(path.clone());
            }
            true
        });
        assert_eq!(full_paths, expected);
    }

    #[test]
    fn test_for_each_path_prefix_includes_lits() {
        // A (B + C') + E F' (G + H I)
        let m = sum(vec![
            prod(vec![v(0), sum(vec![v(1), vn(2)])]),
            prod(vec![v(3), vn(4), sum(vec![v(5), prod(vec![v(6), v(7)])])]),
        ]);
        let mut all_lit_counts = Vec::new();
        m.for_each_path_prefix(|lits, _pos, _prod_path| {
            all_lit_counts.push(lits.len());
            true
        });
        // Should see various prefix literal counts including 0 (Prod selections)
        assert!(all_lit_counts.contains(&0));
        assert!(all_lit_counts.contains(&1));
    }

    #[test]
    fn test_for_each_path_prefix_pruning() {
        // (a · b) + (c · d) — prune when first literal is var 1 (b)
        let m = sum(vec![prod(vec![v(0), v(1)]), prod(vec![v(2), v(3)])]);
        let mut completed_paths = Vec::new();
        m.for_each_path_prefix(|lits, _pos, prod_path| {
            if let Some(path) = prod_path {
                completed_paths.push(path.clone());
            }
            // Prune: don't continue if latest literal is var 1 (b)
            !lits.last().is_some_and(|l| l.var == 1)
        });
        // Path [1] selects b, which gets pruned. Only paths selecting a (var 0) complete.
        assert_eq!(completed_paths.len(), 2); // [0,0] and [0,1]
        assert!(completed_paths.iter().all(|p| p[0] == 0));
    }

    // ── paths vs paths_reference ─────────────────────────────────

    fn assert_paths_matches(m: &Matrix) {
        let fast = m.paths(None);
        let reference = m.paths_reference();
        assert_eq!(fast.uncovered_paths, reference.uncovered_paths);
        // Covers may differ in structure but must both be valid: every path
        // must contain at least one pair from the cover.
        if reference.uncovered_paths.is_empty() {
            let all_paths: Vec<ProdPath> = m.paths_iter().collect();
            for path in &all_paths {
                let positions = m.positions_on_path(path);
                assert!(fast.cover.iter().any(|(pa, pb)|
                    positions.contains(pa) && positions.contains(pb)),
                    "fast cover misses path {:?}", path);
            }
        }
    }

    #[test]
    fn test_paths_tautology_a_or_not_a() {
        assert_paths_matches(&sum(vec![v(0), vn(0)]));
    }

    #[test]
    fn test_paths_not_valid_simple_var() {
        assert_paths_matches(&v(0));
    }

    #[test]
    fn test_paths_not_valid_a_or_b() {
        assert_paths_matches(&sum(vec![v(0), v(1)]));
    }

    #[test]
    fn test_paths_document_example() {
        // ((a·b) + (a'+b')) · ((a'+b') + (a·b))
        let ab   = prod(vec![v(0), v(1)]);
        let nanb = sum(vec![vn(0), vn(1)]);
        let left  = sum(vec![ab.clone(), nanb.clone()]);
        let right = sum(vec![nanb, ab]);
        assert_paths_matches(&prod(vec![left, right]));
    }

    #[test]
    fn test_paths_complement_tautology() {
        // check on complement (used by check_satisfiable)
        let m = prod(vec![v(0), vn(0)]); // a · a' — unsatisfiable
        let comp = m.complement();        // a' + a — tautology
        assert_paths_matches(&comp);
    }

    #[test]
    fn test_paths_cnf_unsatisfiable_complement() {
        // (a+b)·(a+b')·(a'+b)·(a'+b') — unsatisfiable
        let m = prod(vec![
            sum(vec![v(0), v(1)]),
            sum(vec![v(0), vn(1)]),
            sum(vec![vn(0), v(1)]),
            sum(vec![vn(0), vn(1)]),
        ]);
        let comp = m.complement();
        assert_paths_matches(&comp);
    }

    #[test]
    fn test_paths_larger_tautology() {
        // R'H' + L H R' + L' + R
        let (m, _) = parse_to_matrix("R'H' + L H R' + L' + R").unwrap();
        assert_paths_matches(&m);
    }

    #[test]
    fn test_paths_four_var() {
        let (m, _) = parse_to_matrix(
            "a'·b'·c + b'·c'·d + c'·d'·a' + d'·a·b' + a·b·c' + b·c·d' + c·d·a + d·a'·b"
        ).unwrap();
        assert_paths_matches(&m);
    }

    #[test]
    fn test_paths_paths_limit() {
        // (A·B) + (C·D) has 4 non-complementary paths: {A,C}, {A,D}, {B,C}, {B,D}
        let m = sum(vec![prod(vec![v(0), v(1)]), prod(vec![v(2), v(3)])]);

        // Limit 3: should return exactly 3 uncovered paths
        let p3 = m.paths(Some(PathParams { paths_limit: 3, ..Default::default() }));
        assert_eq!(p3.uncovered_paths.len(), 3);

        // Limit 5 (more than total): should return all 4 uncovered paths
        let p5 = m.paths(Some(PathParams { paths_limit: 5, ..Default::default() }));
        assert_eq!(p5.uncovered_paths.len(), 4);

        // Default limit (1): should return exactly 1 uncovered path
        let p1 = m.paths(None);
        assert_eq!(p1.uncovered_paths.len(), 1);
    }

    #[test]
    fn test_paths_collect_covered() {
        // a + a' is a tautology — all paths are covered
        let m = sum(vec![v(0), vn(0)]);

        // Without collect_covered_paths: covered_paths is empty
        let p = m.paths(None);
        assert!(p.uncovered_paths.is_empty());
        assert!(p.covered_paths.is_empty());

        // With collect_covered_paths: covered_paths has all paths
        let p = m.paths(Some(PathParams {
            paths_limit: usize::MAX,
            collect_covered_paths: true,
        }));
        assert!(p.uncovered_paths.is_empty());
        assert!(!p.covered_paths.is_empty());
        // All paths from paths_iter should appear in covered_paths
        let all: Vec<ProdPath> = m.paths_iter().collect();
        assert_eq!(p.covered_paths.len(), all.len());
    }

    #[test]
    fn test_paths_collect_covered_mixed() {
        // (A·B) + (C·D) — all 4 paths are uncovered (no complementary pairs)
        let m = sum(vec![prod(vec![v(0), v(1)]), prod(vec![v(2), v(3)])]);
        let p = m.paths(Some(PathParams {
            paths_limit: 10,
            collect_covered_paths: true,
        }));
        assert_eq!(p.uncovered_paths.len(), 4);
        assert_eq!(p.covered_paths.len(), 0);
    }

    #[test]
    fn test_paths_covered_and_uncovered() {
        // a + a' b + c b' + a b + a a' b b'
        let (m, _) = parse_to_matrix("a + a' b + c b' + a b + a a' b b'").unwrap();
        let p = m.paths(Some(PathParams {
            paths_limit: 20,
            collect_covered_paths: true,
        }));
        assert_eq!(p.covered_paths.len(), 18);
        assert_eq!(p.uncovered_paths.len(), 2);
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
        assert!(m.is_valid());
    }

    #[test]
    fn test_not_valid_simple_var() {
        // a alone is not a tautology
        assert!(!v(0).is_valid());
    }

    #[test]
    fn test_not_valid_a_or_b() {
        // a + b is not a tautology (a=0, b=0 falsifies it)
        assert!(!sum(vec![v(0), v(1)]).is_valid());
    }

    #[test]
    fn test_valid_document_example() {
        // ((a·b) + (a'+b')) · ((a'+b') + (a·b))  is a tautology
        let ab   = prod(vec![v(0), v(1)]);
        let nanb = sum(vec![vn(0), vn(1)]);
        let left  = sum(vec![ab.clone(), nanb.clone()]);
        let right = sum(vec![nanb, ab]);
        let m = prod(vec![left, right]);
        assert!(m.is_valid());
    }

    // ── Satisfiability ────────────────────────────────────────────────────────

    #[test]
    fn test_satisfiable_simple_var() {
        assert!(v(0).is_satisfiable());
    }

    #[test]
    fn test_satisfiable_tautology() {
        // a + a'  is satisfiable (any assignment works)
        assert!(sum(vec![v(0), vn(0)]).is_satisfiable());
    }

    #[test]
    fn test_unsatisfiable_contradiction() {
        // a · a'  is unsatisfiable
        assert!(!prod(vec![v(0), vn(0)]).is_satisfiable());
    }

    #[test]
    fn test_satisfiable_a_or_b() {
        assert!(sum(vec![v(0), v(1)]).is_satisfiable());
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
        assert!(!m.is_satisfiable());
    }
}
