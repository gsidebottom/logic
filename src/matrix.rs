use std::collections::HashMap;
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

// ─── Path / Cover / Proof ────────────────────────────────────────────────────

/// A path through a matrix: a sequence of `Prod` member selections, one for
/// each `Prod` node encountered during depth-first traversal.
///
/// For example, in `Sum([Prod([A, Sum([B, C'])]), Prod([E, F', Sum([G, Prod([H, I])])])])`:
/// - `[0, 0]` = `{A, E}` (Prod0→A, Prod1→E)
/// - `[1, 0]` = `{B, C', E}` (Prod0→Sum[B,C'], Prod1→E)
/// - `[1, 2, 0]` = `{B, C', G, H}` (Prod0→Sum, Prod1→Sum→Prod[H,I]→H)
pub type Path = Vec<usize>;

/// A set of complementary literal pairs identified by their `Position`s.
pub type Cover = Vec<(Position, Position)>;

/// Result of checking validity of a matrix.
///
/// If `first_uncovered_path` is `None`, every path is complementary and `cover`
/// contains a greedy set of covering pairs. Otherwise `first_uncovered_path`
/// holds the first non-complementary path and `cover` is empty.
pub struct Proof {
    pub cover: Cover,
    pub first_uncovered_path: Option<Path>,
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
    pub fn paths_iter(&self) -> impl Iterator<Item = Path> {
        fn collect(m: &Matrix) -> Vec<Path> {
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
    pub fn is_complementary(&self, path: &Path) -> bool {
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
    pub fn cover(&self, paths: &[Path]) -> Cover {
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
    /// contains a complementary pair. For invalid matrices this finds the
    /// first non-complementary path without enumerating all paths.
    pub fn check_valid(&self) -> Proof {
        let mut first_uncovered: Option<Path> = None;
        let mut cover = Cover::new();

        self.for_each_path_prefix(|prefix, lits, positions, complete| {
            if first_uncovered.is_some() {
                return false;
            }
            if complete {
                first_uncovered = Some(prefix.to_vec());
                return false;
            }
            // Check if the newest literal has a complement among prior ones.
            if let Some(new_lit) = lits.last() {
                let new_pos = positions.last().unwrap();
                for (j, prior) in lits[..lits.len() - 1].iter().enumerate() {
                    if prior.is_complement_of(new_lit) {
                        cover.push((positions[j].clone(), new_pos.clone()));
                        return false; // prune
                    }
                }
            }
            true
        });

        match first_uncovered {
            Some(path) => Proof { cover: vec![], first_uncovered_path: Some(path) },
            None       => Proof { cover, first_uncovered_path: None },
        }
    }

    /// Reference implementation: check validity by examining all paths.
    ///
    /// Returns a `Proof` whose `first_uncovered_path` is `None` when every
    /// path is complementary (valid / tautology), with `cover` holding the
    /// greedy covering pairs.  Otherwise `first_uncovered_path` is the first
    /// non-complementary path and `cover` is empty.
    pub fn check_valid_reference(&self) -> Proof {
        let all_paths: Vec<Path> = self.paths_iter().collect();
        match all_paths.iter().find(|p| !self.is_complementary(p)) {
            Some(path) => Proof { cover: vec![], first_uncovered_path: Some(path.clone()) },
            None       => Proof { cover: self.cover(&all_paths), first_uncovered_path: None },
        }
    }

    /// Depth-first traversal of all path prefixes, with pruning.
    ///
    /// Calls `f(path, lits, positions, complete)` at each step of the traversal:
    /// - When a `Prod` member is selected (new path element, `complete = false`)
    /// - When a `Lit` is reached (new literal + position in `lits`/`positions`, `complete = false`)
    /// - When a full path is completed (`complete = true`)
    ///
    /// `lits` and `positions` are parallel vectors: `positions[i]` is the
    /// absolute tree address of `lits[i]`.
    ///
    /// If `f` returns `true`, traversal continues forward; if `false`, it
    /// backtracks to the last `Prod` member choice.
    pub fn for_each_path_prefix(
        &self,
        mut f: impl FnMut(&Path, &Vec<&Lit>, &Vec<Position>, bool) -> bool,
    ) {
        type Lits<'a> = Vec<&'a Lit>;
        type Positions = Vec<Position>;

        fn traverse<'a, F: FnMut(&Path, &Lits<'a>, &Positions, bool) -> bool>(
            m: &'a Matrix,
            path: &mut Path,
            lits: &mut Lits<'a>,
            positions: &mut Positions,
            pos: &mut Position,
            f: &mut F,
            then: &mut dyn FnMut(&mut Path, &mut Lits<'a>, &mut Positions, &mut Position, &mut F),
        ) {
            match m {
                Matrix::Lit(l) => {
                    lits.push(l);
                    positions.push(pos.clone());
                    if f(path, lits, positions, false) {
                        then(path, lits, positions, pos, f);
                    }
                    positions.pop();
                    lits.pop();
                }
                Matrix::Prod(children) => {
                    for (i, child) in children.iter().enumerate() {
                        path.push(i);
                        pos.push(i);
                        if f(path, lits, positions, false) {
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
        fn traverse_sum<'a, F: FnMut(&Path, &Lits<'a>, &Positions, bool) -> bool>(
            children: &'a [Matrix],
            idx: usize,
            path: &mut Path,
            lits: &mut Lits<'a>,
            positions: &mut Positions,
            pos: &mut Position,
            f: &mut F,
            then: &mut dyn FnMut(&mut Path, &mut Lits<'a>, &mut Positions, &mut Position, &mut F),
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

        let mut path = Path::new();
        let mut lits = Vec::new();
        let mut positions = Vec::new();
        let mut pos = Vec::new();
        traverse(self, &mut path, &mut lits, &mut positions, &mut pos, &mut f,
            &mut |path, lits, positions, _pos, f| {
                f(path, lits, positions, true);
            },
        );
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
        let expected: Vec<Path> = m.paths_iter().collect();
        m.for_each_path_prefix(|prefix, _lits, _pos, complete| {
            if complete {
                full_paths.push(prefix.to_vec());
            }
            true
        });
        assert_eq!(full_paths, expected);
    }

    #[test]
    fn test_for_each_path_prefix_includes_prefixes() {
        // A (B + C') + E F' (G + H I)
        let m = sum(vec![
            prod(vec![v(0), sum(vec![v(1), vn(2)])]),
            prod(vec![v(3), vn(4), sum(vec![v(5), prod(vec![v(6), v(7)])])]),
        ]);
        let mut all_prefixes = Vec::new();
        m.for_each_path_prefix(|prefix, _lits, _pos, _complete| {
            all_prefixes.push(prefix.to_vec());
            true
        });
        // Should include intermediate prefixes like [0], [1], [0,0], etc.
        assert!(all_prefixes.contains(&vec![0]));
        assert!(all_prefixes.contains(&vec![1]));
        assert!(all_prefixes.contains(&vec![0, 0]));
        assert!(all_prefixes.contains(&vec![0, 1]));
        assert!(all_prefixes.contains(&vec![1, 2, 0]));
    }

    #[test]
    fn test_for_each_path_prefix_pruning() {
        // (a · b) + (c · d) — prune when prefix starts with [1]
        let m = sum(vec![prod(vec![v(0), v(1)]), prod(vec![v(2), v(3)])]);
        let mut visited = Vec::new();
        m.for_each_path_prefix(|prefix, _lits, _pos, _complete| {
            visited.push(prefix.to_vec());
            // Prune: don't continue if first Prod selected member 1
            prefix[0] != 1
        });
        // Should see [0] (continue), [0,0], [0,1], [1] (pruned — no [1,*])
        assert!(visited.contains(&vec![0]));
        assert!(visited.contains(&vec![0, 0]));
        assert!(visited.contains(&vec![0, 1]));
        assert!(visited.contains(&vec![1]));
        assert!(!visited.contains(&vec![1, 0]));
        assert!(!visited.contains(&vec![1, 1]));
    }

    // ── check_valid vs check_valid_reference ─────────────────────────────────

    fn assert_check_valid_matches(m: &Matrix) {
        let fast = m.check_valid();
        let reference = m.check_valid_reference();
        assert_eq!(fast.first_uncovered_path, reference.first_uncovered_path);
        // Covers may differ in structure but must both be valid: every path
        // must contain at least one pair from the cover.
        if reference.first_uncovered_path.is_none() {
            let all_paths: Vec<Path> = m.paths_iter().collect();
            for path in &all_paths {
                let positions = m.positions_on_path(path);
                assert!(fast.cover.iter().any(|(pa, pb)|
                    positions.contains(pa) && positions.contains(pb)),
                    "fast cover misses path {:?}", path);
            }
        }
    }

    #[test]
    fn test_check_valid_tautology_a_or_not_a() {
        assert_check_valid_matches(&sum(vec![v(0), vn(0)]));
    }

    #[test]
    fn test_check_valid_not_valid_simple_var() {
        assert_check_valid_matches(&v(0));
    }

    #[test]
    fn test_check_valid_not_valid_a_or_b() {
        assert_check_valid_matches(&sum(vec![v(0), v(1)]));
    }

    #[test]
    fn test_check_valid_document_example() {
        // ((a·b) + (a'+b')) · ((a'+b') + (a·b))
        let ab   = prod(vec![v(0), v(1)]);
        let nanb = sum(vec![vn(0), vn(1)]);
        let left  = sum(vec![ab.clone(), nanb.clone()]);
        let right = sum(vec![nanb, ab]);
        assert_check_valid_matches(&prod(vec![left, right]));
    }

    #[test]
    fn test_check_valid_complement_tautology() {
        // check on complement (used by check_satisfiable)
        let m = prod(vec![v(0), vn(0)]); // a · a' — unsatisfiable
        let comp = m.complement();        // a' + a — tautology
        assert_check_valid_matches(&comp);
    }

    #[test]
    fn test_check_valid_cnf_unsatisfiable_complement() {
        // (a+b)·(a+b')·(a'+b)·(a'+b') — unsatisfiable
        let m = prod(vec![
            sum(vec![v(0), v(1)]),
            sum(vec![v(0), vn(1)]),
            sum(vec![vn(0), v(1)]),
            sum(vec![vn(0), vn(1)]),
        ]);
        let comp = m.complement();
        assert_check_valid_matches(&comp);
    }

    #[test]
    fn test_check_valid_larger_tautology() {
        // R'H' + L H R' + L' + R
        let (m, _) = parse_to_matrix("R'H' + L H R' + L' + R").unwrap();
        assert_check_valid_matches(&m);
    }

    #[test]
    fn test_check_valid_four_var() {
        let (m, _) = parse_to_matrix(
            "a'·b'·c + b'·c'·d + c'·d'·a' + d'·a·b' + a·b·c' + b·c·d' + c·d·a + d·a'·b"
        ).unwrap();
        assert_check_valid_matches(&m);
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

pub fn format_path(path: &Path, m: &Matrix, var_names: &[String]) -> String {
    let resolved = m.lits_on_path(path);
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
    let ast = Ast::try_from(formula)?;
    Ok((Matrix::from(&ast), ast.vars))
}

