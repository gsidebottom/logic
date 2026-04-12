use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use serde::{Deserialize, Serialize};
use crate::formula::{count_primes, get_base_name, Ast, Node};

/// Handle for cooperatively cancelling a running async traversal.
#[derive(Clone, Default, Debug)]
pub struct CancelHandle(Arc<AtomicBool>);

impl CancelHandle {
    pub fn new() -> Self { Self::default() }
    pub fn cancel(&self) { self.0.store(true, Ordering::Relaxed); }
    pub fn is_cancelled(&self) -> bool { self.0.load(Ordering::Relaxed) }
}

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

/// A sequence of literal `Position`s — the literals collected on a path or path prefix.
pub type PathPrefix = Vec<Position>;

// ─── Path / Cover / Paths ────────────────────────────────────────────────────

/// A path through a matrix: a sequence of `Prod` member selections, one for
/// each `Prod` node encountered during depth-first traversal.
///
/// For example, in `Sum([Prod([A, Sum([B, C'])]), Prod([E, F', Sum([G, Prod([H, I])])])])`:
/// - `[0, 0]` = `{A, E}` (Prod0→A, Prod1→E)
/// - `[1, 0]` = `{B, C', E}` (Prod0→Sum[B,C'], Prod1→E)
/// - `[1, 2, 0]` = `{B, C', G, H}` (Prod0→Sum, Prod1→Sum→Prod[H,I]→H)
pub type ProdPath = Vec<usize>;

/// A complementary literal pair identified by their `Position`s.
pub type Pair = (Position, Position);

/// A set of complementary literal pairs identified by their `Position`s.
pub type Cover = Vec<Pair>;

/// Parameters controlling proof search.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PathParams {
    #[serde(default = "PathParams::default_paths_limit")]
    pub paths_limit: usize,
}

impl PathParams {
    fn default_paths_limit() -> usize { 1 }
}

impl Default for PathParams {
    fn default() -> Self {
        PathParams { paths_limit: Self::default_paths_limit() }
    }
}

/// A complementary pair together with the path prefix it covers.
pub struct CoveredPathPrefix {
    pub cover: Pair,
    pub prefix: PathPrefix,
}

/// Classification of a single path encountered during matrix path enumeration.
pub enum PathsClass {
    Covered(CoveredPathPrefix),
    Uncovered(ProdPath),
}

/// An owned snapshot of a single `for_each_path_prefix` callback invocation,
/// suitable for sending across a channel.
#[derive(Clone, Debug)]
pub struct PathPrefixEvent {
    pub lits: Vec<Lit>,
    pub positions: PathPrefix,
    pub prod_path: Option<ProdPath>,
}

/// Result of checking validity of a matrix.
///
/// The matrix is valid (a tautology) iff every class is `Covered`.
/// `paths_limit` limits `classes.len()`.
pub struct Paths {
    pub classes: Vec<PathsClass>,
    pub hit_limit: bool,
}

impl Paths {
    /// Extract the cover (list of complementary pairs) from the covered classes.
    pub fn cover(&self) -> Cover {
        self.classes.iter().filter_map(|c| match c {
            PathsClass::Covered(cp) => Some(cp.cover.clone()),
            PathsClass::Uncovered(_) => None,
        }).collect()
    }

    /// Iterate over the covered path prefixes.
    pub fn covered_path_prefixes(&self) -> impl Iterator<Item = &CoveredPathPrefix> {
        self.classes.iter().filter_map(|c| match c {
            PathsClass::Covered(cp) => Some(cp),
            PathsClass::Uncovered(_) => None,
        })
    }

    /// Iterate over the uncovered paths.
    pub fn uncovered_paths(&self) -> impl Iterator<Item = &ProdPath> {
        self.classes.iter().filter_map(|c| match c {
            PathsClass::Uncovered(p) => Some(p),
            PathsClass::Covered(_) => None,
        })
    }
}

// ─── PathSearchController ─────────────────────────────────────────────────────

/// A `PathSearchController` that prunes paths whose prefix already contains a
/// complementary literal pair, classifying each completed path as
/// `Covered` or `Uncovered`. Classified items are delivered via
/// `should_continue_on_paths_class`. Set `on_class` to receive them via a callback.
pub struct BacktrackWhenCoveredController<F: FnMut(PathsClass, bool) -> bool = fn(PathsClass, bool) -> bool> {
    paths_limit: usize,
    covered_at_depth: Option<usize>,
    path_count: usize,
    last_lits_len: usize,
    on_class: Option<F>,
}

impl From<Option<PathParams>> for BacktrackWhenCoveredController {
    fn from(params: Option<PathParams>) -> Self {
        let params = params.unwrap_or_default();
        Self {
            paths_limit: params.paths_limit,
            covered_at_depth: None,
            path_count: 0,
            last_lits_len: 0,
            on_class: None,
        }
    }
}

impl<F: FnMut(PathsClass, bool) -> bool> BacktrackWhenCoveredController<F> {
    pub fn with_on_class(params: Option<PathParams>, on_class: F) -> Self {
        let params = params.unwrap_or_default();
        Self {
            paths_limit: params.paths_limit,
            covered_at_depth: None,
            path_count: 0,
            last_lits_len: 0,
            on_class: Some(on_class),
        }
    }

    pub fn hit_limit(&self) -> bool { self.path_count >= self.paths_limit }
}

impl<F: FnMut(PathsClass, bool) -> bool> PathSearchController for BacktrackWhenCoveredController<F> {
    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        complete_prod_path: Option<&ProdPath>,
    ) -> bool {
        if self.path_count >= self.paths_limit {
            return false;
        }
        // Detect backtrack: if lits shrunk past the depth where we found
        // a complementary pair, we're no longer in a covered subtree.
        if let Some(d) = self.covered_at_depth {
            if prefix_literals.len() < d {
                self.covered_at_depth = None;
            }
        }
        // Check new literals for complementary pairs.
        if self.covered_at_depth.is_none() && prefix_literals.len() > self.last_lits_len {
            'outer: for new_idx in self.last_lits_len..prefix_literals.len() {
                let new_lit = prefix_literals[new_idx];
                for (j, prior) in prefix_literals[..new_idx].iter().enumerate() {
                    if prior.is_complement_of(new_lit) {
                        let cpp = CoveredPathPrefix {
                            cover: (prefix_positions[j].clone(), prefix_positions[new_idx].clone()),
                            prefix: prefix_positions.clone(),
                        };
                        self.path_count += 1;
                        let hit_limit = self.path_count >= self.paths_limit;
                        if !self.should_continue_on_paths_class(PathsClass::Covered(cpp), hit_limit) {
                            self.last_lits_len = prefix_literals.len();
                            return false;
                        }
                        self.covered_at_depth = Some(prefix_literals.len());
                        break 'outer;
                    }
                }
            }
        }
        if let Some(path) = complete_prod_path {
            if self.covered_at_depth.is_none() {
                self.path_count += 1;
                let hit_limit = self.path_count >= self.paths_limit;
                if !self.should_continue_on_paths_class(PathsClass::Uncovered(path.clone()), hit_limit) {
                    self.last_lits_len = prefix_literals.len();
                    return false;
                }
            }
            self.last_lits_len = prefix_literals.len();
            return self.path_count < self.paths_limit;
        }
        // Prod selection — prune if covered.
        if self.covered_at_depth.is_some() {
            self.last_lits_len = prefix_literals.len();
            return false;
        }
        self.last_lits_len = prefix_literals.len();
        true
    }

    fn should_continue_on_paths_class(&mut self, paths_class: PathsClass, hit_limit: bool) -> bool {
        match &mut self.on_class {
            Some(f) => f(paths_class, hit_limit),
            None => true,
        }
    }
}

/// Controls depth-first path-prefix traversal.
pub trait PathSearchController {
    /// Called at each step of the traversal. Return `true` to continue
    /// forward, `false` to backtrack.
    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        complete_prod_path: Option<&ProdPath>,
    ) -> bool;

    /// Called on each classified path. Return `true` to continue
    /// classifying paths, `false` to stop the traversal.
    fn should_continue_on_paths_class(&mut self, _paths_class: PathsClass, _hit_limit: bool) -> bool {
        true
    }
}

/// Blanket impl: any matching `FnMut` is a `PathSearchController`.
impl<F> PathSearchController for F
where
    F: FnMut(&Vec<&Lit>, &PathPrefix, Option<&ProdPath>) -> bool,
{
    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        complete_prod_path: Option<&ProdPath>,
    ) -> bool {
        self(prefix_literals, prefix_positions, complete_prod_path)
    }
}

// ─── NNF ───────────────────────────────────────────────────────────────────

/// A formula in negation normal form (NNF).
///
/// `∑` (Sum)  = disjunction (OR)
/// `∏` (Prod) = conjunction (AND)
#[derive(Clone, Debug)]
pub enum NNF {
    Lit(Lit),
    Sum(Vec<NNF>),
    Prod(Vec<NNF>),
}

impl NNF {
    /// Push negation inward (De Morgan) to produce the complement in NNF.
    pub fn complement(&self) -> Self {
        match self {
            NNF::Lit(l)      => NNF::Lit(l.complement()),
            NNF::Sum(ch)     => NNF::Prod(ch.iter().map(|c| c.complement()).collect()),
            NNF::Prod(ch)    => NNF::Sum(ch.iter().map(|c| c.complement()).collect()),
        }
    }

    /// Resolve a path to the literals it collects.
    ///
    /// Follows the path's `Prod` member selections depth-first, collecting every
    /// `Lit` encountered (including those reached via `Sum` cross-products).
    pub fn lits_on_path(&self, path: &[usize]) -> Vec<&Lit> {
        fn inner<'a>(m: &'a NNF, path: &[usize]) -> (Vec<&'a Lit>, usize) {
            match m {
                NNF::Lit(l) => (vec![l], 0),
                NNF::Prod(children) => {
                    let sel = path[0];
                    let (lits, consumed) = inner(&children[sel], &path[1..]);
                    (lits, 1 + consumed)
                }
                NNF::Sum(children) => {
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
        fn collect(m: &NNF) -> Vec<ProdPath> {
            match m {
                NNF::Lit(_) => vec![vec![]],
                NNF::Sum(children) => {
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
                NNF::Prod(children) => {
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
    pub fn positions_on_path(&self, path: &[usize]) -> PathPrefix {
        fn inner(m: &NNF, path: &[usize], pos: &mut Vec<usize>, out: &mut PathPrefix) -> usize {
            match m {
                NNF::Lit(_) => {
                    out.push(pos.clone());
                    0
                }
                NNF::Prod(children) => {
                    let sel = path[0];
                    pos.push(sel);
                    let consumed = inner(&children[sel], &path[1..], pos, out);
                    pos.pop();
                    1 + consumed
                }
                NNF::Sum(children) => {
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
    pub fn literal_positions(&self, target: &Lit) -> PathPrefix {
        fn inner(m: &NNF, target: &Lit, prefix: &mut Position, out: &mut PathPrefix) {
            match m {
                NNF::Lit(l) => if l == target { out.push(prefix.clone()); }
                NNF::Sum(ch) | NNF::Prod(ch) => {
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
                NNF::Lit(_) => return None,
                NNF::Sum(ch) | NNF::Prod(ch) => node = ch.get(i)?,
            }
        }
        match node {
            NNF::Lit(l) => Some(l),
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
        let resolved: Vec<PathPrefix> = paths.iter()
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
    pub fn paths<F: FnMut(PathsClass, bool) -> bool>(&self, ctrl: &mut BacktrackWhenCoveredController<F>) {
        self.for_each_path_prefix(|lits, positions, prod_path| {
            ctrl.should_continue_on_prefix(lits, positions, prod_path)
        });
    }

    /// Async streaming variant of `paths`: spawns a blocking thread that runs
    /// the depth-first traversal and sends each `PathsClass` as it is
    /// discovered, paired with a `bool` that is `true` if this item caused
    /// the `paths_limit` to be reached.
    pub fn paths_async<F: FnMut(PathsClass, bool) -> bool + Send + 'static>(
        &self,
        mut ctrl: BacktrackWhenCoveredController<F>,
    ) -> (tokio::task::JoinHandle<()>, CancelHandle) {
        let m = self.clone();
        let cancel = CancelHandle::new();
        let cancel_for_thread = cancel.clone();
        let handle = tokio::task::spawn_blocking(move || {
            m.for_each_path_prefix(|lits, positions, prod_path| {
                if cancel_for_thread.is_cancelled() { return false; }
                ctrl.should_continue_on_prefix(lits, positions, prod_path)
            });
        });
        (handle, cancel)
    }

    /// Reference implementation: check validity by examining all paths.
    ///
    /// Reference implementation: check validity by examining all paths.
    pub fn paths_reference(&self) -> Paths {
        let all_paths: Vec<ProdPath> = self.paths_iter().collect();
        let uncovered: Vec<ProdPath> = all_paths.iter()
            .filter(|p| !self.is_complementary(p))
            .cloned()
            .collect();
        let classes: Vec<PathsClass> = if uncovered.is_empty() {
            self.cover(&all_paths).into_iter()
                .map(|cover| PathsClass::Covered(CoveredPathPrefix { cover, prefix: vec![] }))
                .collect()
        } else {
            uncovered.into_iter().map(PathsClass::Uncovered).collect()
        };
        Paths { classes, hit_limit: false }
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
        mut f: impl FnMut(&Vec<&Lit>, &PathPrefix, Option<&ProdPath>) -> bool,
    ) {
        type Lits<'a> = Vec<&'a Lit>;
        type Positions = PathPrefix;

        fn traverse<'a, F: FnMut(&Lits<'a>, &Positions, Option<&ProdPath>) -> bool>(
            m: &'a NNF,
            path: &mut ProdPath,
            lits: &mut Lits<'a>,
            positions: &mut Positions,
            pos: &mut Position,
            f: &mut F,
            then: &mut dyn FnMut(&mut ProdPath, &mut Lits<'a>, &mut Positions, &mut Position, &mut F),
        ) {
            match m {
                NNF::Lit(l) => {
                    lits.push(l);
                    positions.push(pos.clone());
                    then(path, lits, positions, pos, f);
                    positions.pop();
                    lits.pop();
                }
                NNF::Prod(children) => {
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
                NNF::Sum(children) => {
                    traverse_sum(children, 0, path, lits, positions, pos, f, then);
                }
            }
        }

        #[allow(clippy::too_many_arguments)]
        fn traverse_sum<'a, F: FnMut(&Lits<'a>, &Positions, Option<&ProdPath>) -> bool>(
            children: &'a [NNF],
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

    /// Async variant of `for_each_path_prefix`: spawns a blocking thread that
    /// runs the depth-first traversal, sends each event as an owned
    /// `PathPrefixEvent` over the returned channel, and consults
    /// `should_continue_on_prefix` at each step to decide whether to continue forward
    /// or backtrack. The traversal also stops when the receiver is dropped
    /// (the next send fails).
    ///
    /// Returns a `(JoinHandle, Receiver)` pair so the caller can observe both
    /// the streamed events and any panic from the worker thread.
    pub fn for_each_path_prefix_async(
        &self,
        buffer_size: usize,
        mut path_prefix_controller: impl FnMut(&Vec<&Lit>, &PathPrefix, Option<&ProdPath>) -> bool + Send + 'static,
    ) -> (
        tokio::task::JoinHandle<Result<(), tokio::sync::mpsc::error::SendError<PathPrefixEvent>>>,
        tokio::sync::mpsc::Receiver<PathPrefixEvent>,
        CancelHandle,
    ) {
        let m = self.clone();
        let (tx, rx) = tokio::sync::mpsc::channel::<PathPrefixEvent>(buffer_size);
        let cancel = CancelHandle::new();
        let cancel_for_thread = cancel.clone();
        let handle = tokio::task::spawn_blocking(move || {
            let mut send_err = None;
            m.for_each_path_prefix(|lits, positions, prod_path| {
                if send_err.is_some() || cancel_for_thread.is_cancelled() { return false; }
                let event = PathPrefixEvent {
                    lits: lits.iter().map(|&l| l.clone()).collect(),
                    positions: positions.clone(),
                    prod_path: prod_path.cloned(),
                };
                if let Err(e) = tx.blocking_send(event) {
                    send_err = Some(e);
                    return false;
                }
                path_prefix_controller(lits, positions, prod_path)
            });
            send_err.map(Err).unwrap_or(Ok(()))
        });
        (handle, rx, cancel)
    }
}

// ─── Formula → NNF conversion ──────────────────────────────────────────────

impl From<&Ast> for NNF {
    fn from(ast: &Ast) -> Self {
        fn convert(node: &Node, var_index: &HashMap<String, u32>) -> NNF {
            match node {
                Node::Var(name) => {
                    let base = get_base_name(name);
                    let neg  = count_primes(name) % 2 == 1;
                    match base {
                        "0" => if neg { NNF::Prod(vec![]) } else { NNF::Sum(vec![]) },
                        "1" => if neg { NNF::Sum(vec![]) } else { NNF::Prod(vec![]) },
                        _   => NNF::Lit(Lit { var: *var_index.get(base).unwrap(), neg }),
                    }
                }
                Node::And(ch) => {
                    let mut members = Vec::new();
                    for c in ch {
                        match convert(c, var_index) {
                            NNF::Prod(inner) => members.extend(inner),
                            other => members.push(other),
                        }
                    }
                    NNF::Prod(members)
                }
                Node::Or(ch) => {
                    let mut members = Vec::new();
                    for c in ch {
                        match convert(c, var_index) {
                            NNF::Sum(inner) => members.extend(inner),
                            other => members.push(other),
                        }
                    }
                    NNF::Sum(members)
                }
            }
        }
        convert(&ast.root, &ast.var_index)
    }
}

pub fn format_path(path: &ProdPath, m: &NNF, var_names: &[String]) -> String {
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

/// A parsed formula with its AST and NNF (negation normal form) matrix.
pub struct Matrix {
    pub formula: String,
    pub ast: Ast,
    pub nnf: NNF,
    pub nnf_complement: NNF,
}

impl TryFrom<&str> for Matrix {
    type Error = String;
    fn try_from(formula: &str) -> Result<Self, String> {
        let ast = Ast::try_from(formula)?;
        let nnf = NNF::from(&ast);
        let nnf_complement = nnf.complement();
        Ok(Matrix {
            formula: formula.to_string(),
            ast,
            nnf,
            nnf_complement,
        })
    }
}

impl Matrix {
    pub fn for_each_path_prefix(
        &self,
        complement: bool,
        buffer_size: usize,
        mut path_prefix_controller: impl PathSearchController + Send + 'static,
    ) -> (
        tokio::task::JoinHandle<Result<(), tokio::sync::mpsc::error::SendError<PathPrefixEvent>>>,
        tokio::sync::mpsc::Receiver<PathPrefixEvent>,
        CancelHandle,
    ) {
        let target = if complement { &self.nnf_complement } else { &self.nnf };
        target.for_each_path_prefix_async(buffer_size, move |lits, positions, prod_path| {
            path_prefix_controller.should_continue_on_prefix(lits, positions, prod_path)
        })
    }
}

pub fn parse_to_matrix(formula: &str) -> Result<(NNF, Vec<String>), String> {
    let m = Matrix::try_from(formula)?;
    Ok((m.nnf, m.ast.vars))
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── Helpers ───────────────────────────────────────────────────────────────

    fn v(n: Var) -> NNF { NNF::Lit(Lit::pos(n)) }
    fn vn(n: Var) -> NNF { NNF::Lit(Lit::neg(n)) }
    fn sum(ch: Vec<NNF>) -> NNF { NNF::Sum(ch) }
    fn prod(ch: Vec<NNF>) -> NNF { NNF::Prod(ch) }

    // Resolve each path's literals to (var, neg) pairs, sort for deterministic comparison.
    fn sorted_paths(m: &NNF) -> Vec<Vec<(Var, bool)>> {
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
            NNF::Prod(children) => {
                assert_eq!(children.len(), 4, "expected 4 children, got {:?}", m);
                assert!(children.iter().all(|c| matches!(c, NNF::Lit(_))));
            }
            _ => panic!("expected Prod, got {:?}", m),
        }
    }

    #[test]
    fn test_parse_sum_flattening() {
        // (A + B) + (C + D) should produce Sum(A, B, C, D), not Sum(A, B, Sum(C, D))
        let (m, _) = parse_to_matrix("(A + B) + (C + D)").unwrap();
        match &m {
            NNF::Sum(children) => {
                assert_eq!(children.len(), 4, "expected 4 children, got {:?}", m);
                assert!(children.iter().all(|c| matches!(c, NNF::Lit(_))));
            }
            _ => panic!("expected Sum, got {:?}", m),
        }
    }

    // ── Path encoding ─────────────────────────────────────────────────────────

    /// Test helper: run `paths()` with the given params, collect classes into a `Paths`.
    fn collect_paths(m: &NNF, params: Option<PathParams>) -> Paths {
        let mut classes = Vec::new();
        let hit_limit = {
            let mut ctrl = BacktrackWhenCoveredController::with_on_class(params, |class, _| {
                classes.push(class);
                true
            });
            m.paths(&mut ctrl);
            ctrl.hit_limit()
        };
        Paths { classes, hit_limit }
    }

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

    #[test]
    fn test_for_each_path_prefix_full_trace() {
        // a + b + b' c' + c d + e
        // NNF: Sum([a, b, Prod([b', c']), Prod([c, d]), e])
        // Variables alphabetically: a=0, b=1, c=2, d=3, e=4
        let (m, _) = parse_to_matrix("a + b + b' c' + c d + e").unwrap();
        let mut trace: Vec<(Vec<(Var, bool)>, Option<ProdPath>)> = Vec::new();
        m.for_each_path_prefix(|lits, _positions, prod_path| {
            trace.push((
                lits.iter().map(|l| (l.var, l.neg)).collect(),
                prod_path.cloned(),
            ));
            true
        });

        let a  = (0, false);
        let b  = (1, false);
        let bn = (1, true);
        let c  = (2, false);
        let cn = (2, true);
        let d  = (3, false);
        let e  = (4, false);

        assert_eq!(trace, vec![
            // Prod2 select member 0 (b'), lits has [a, b] from Sum children 0,1
            (vec![a, b],             None),
            // Prod3 select member 0 (c), lits has [a, b, b'] from Lit(b')
            (vec![a, b, bn],         None),
            // Complete path [0, 0]: lits = [a, b, b', c, e]
            (vec![a, b, bn, c, e],   Some(vec![0, 0])),
            // Prod3 select member 1 (d)
            (vec![a, b, bn],         None),
            // Complete path [0, 1]: lits = [a, b, b', d, e]
            (vec![a, b, bn, d, e],   Some(vec![0, 1])),
            // Prod2 select member 1 (c')
            (vec![a, b],             None),
            // Prod3 select member 0 (c)
            (vec![a, b, cn],         None),
            // Complete path [1, 0]: lits = [a, b, c', c, e]
            (vec![a, b, cn, c, e],   Some(vec![1, 0])),
            // Prod3 select member 1 (d)
            (vec![a, b, cn],         None),
            // Complete path [1, 1]: lits = [a, b, c', d, e]
            (vec![a, b, cn, d, e],   Some(vec![1, 1])),
        ]);
    }

    // ── paths vs paths_reference ─────────────────────────────────

    fn assert_paths_matches(m: &NNF) {
        let fast = collect_paths(&m, Some(PathParams { paths_limit: usize::MAX }));
        let reference = m.paths_reference();
        let fast_uncovered: Vec<&ProdPath> = fast.uncovered_paths().collect();
        let ref_uncovered: Vec<&ProdPath> = reference.uncovered_paths().collect();
        assert_eq!(fast_uncovered, ref_uncovered);
        // Covers may differ in structure but must both be valid: every path
        // must contain at least one pair from the cover.
        if ref_uncovered.is_empty() {
            let all_paths: Vec<ProdPath> = m.paths_iter().collect();
            for path in &all_paths {
                let positions = m.positions_on_path(path);
                assert!(fast.cover().iter().any(|(pa, pb)|
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
        let p3 = collect_paths(&m, Some(PathParams { paths_limit: 3 }));
        assert_eq!(p3.uncovered_paths().count(), 3);

        // Limit 5 (more than total): should return all 4 uncovered paths
        let p5 = collect_paths(&m, Some(PathParams { paths_limit: 5 }));
        assert_eq!(p5.uncovered_paths().count(), 4);

        // Default limit (1): should return exactly 1 uncovered path
        let p1 = collect_paths(&m, None);
        assert_eq!(p1.uncovered_paths().count(), 1);
    }

    #[test]
    fn test_paths_covered_and_uncovered() {
        // a + a' b + c b' + a b + a a' b b'
        // 6 covered path prefixes + 4 uncovered paths = 10
        let (m, _) = parse_to_matrix("a + a' b + c b' + a b + a a' b b'").unwrap();
        let p = collect_paths(&m, Some(PathParams { paths_limit: 20 }));
        assert_eq!(p.covered_path_prefixes().count(), 6);
        assert_eq!(p.uncovered_paths().count(), 4);
        assert_eq!(p.cover().len(), 6);
    }

    #[tokio::test]
    async fn test_paths_async_cancel() {
        // Large enumeration; cancel after the first item.
        let m = sum((0..6).map(|_| prod(vec![v(0), v(1), v(2), v(3)])).collect());
        let (tx, mut rx) = tokio::sync::mpsc::channel::<(PathsClass, bool)>(1);
        let ctrl = BacktrackWhenCoveredController::with_on_class(
            Some(PathParams { paths_limit: usize::MAX }),
            move |class, hit_limit| { tx.blocking_send((class, hit_limit)).is_ok() },
        );
        let (handle, cancel) = m.paths_async(ctrl);
        let _first = rx.recv().await.expect("at least one item");
        cancel.cancel();
        while rx.recv().await.is_some() {}
        handle.await.expect("worker panicked");
    }

    #[tokio::test]
    async fn test_paths_async_matches_paths() {
        let (m, _) = parse_to_matrix("a + a' b + c b' + a b + a a' b b'").unwrap();
        let sync_paths = collect_paths(&m, Some(PathParams { paths_limit: 20 }));

        let (tx, mut rx) = tokio::sync::mpsc::channel::<(PathsClass, bool)>(8);
        let ctrl = BacktrackWhenCoveredController::with_on_class(
            Some(PathParams { paths_limit: 20 }),
            move |class, hit_limit| { tx.blocking_send((class, hit_limit)).is_ok() },
        );
        let (handle, _cancel) = m.paths_async(ctrl);
        let mut items: Vec<(PathsClass, bool)> = Vec::new();
        while let Some(it) = rx.recv().await {
            items.push(it);
        }
        handle.await.expect("worker panicked");

        assert_eq!(items.len(), sync_paths.classes.len());
        for (a, b) in items.iter().zip(sync_paths.classes.iter()) {
            match (&a.0, b) {
                (PathsClass::Covered(x), PathsClass::Covered(y)) => {
                    assert_eq!(x.cover, y.cover);
                    assert_eq!(x.prefix, y.prefix);
                }
                (PathsClass::Uncovered(x), PathsClass::Uncovered(y)) => {
                    assert_eq!(x, y);
                }
                _ => panic!("class mismatch"),
            }
        }
        assert!(items[..items.len() - 1].iter().all(|(_, hit)| !hit));
    }

    #[tokio::test]
    async fn test_for_each_path_prefix_async() {
        // Compare the events streamed from the async variant against
        // the synchronous closure-based version.
        let (m, _) = parse_to_matrix("a b + c d").unwrap();

        let mut sync_events: Vec<(Vec<Lit>, PathPrefix, Option<ProdPath>)> = Vec::new();
        m.for_each_path_prefix(|lits, positions, prod_path| {
            sync_events.push((
                lits.iter().map(|&l| l.clone()).collect(),
                positions.clone(),
                prod_path.cloned(),
            ));
            true
        });

        let (handle, mut rx, _cancel) = m.for_each_path_prefix_async(64, |_, _, _| true);
        let mut async_events: Vec<(Vec<Lit>, PathPrefix, Option<ProdPath>)> = Vec::new();
        while let Some(ev) = rx.recv().await {
            async_events.push((ev.lits, ev.positions, ev.prod_path));
        }
        handle.await.expect("worker thread panicked").expect("send error");

        assert_eq!(sync_events, async_events);
        assert!(!async_events.is_empty());
    }

    // ── Complement ────────────────────────────────────────────────────────────

    #[test]
    fn test_complement_lit() {
        assert!(matches!(v(0).complement(), NNF::Lit(l) if l == Lit::neg(0)));
        assert!(matches!(vn(0).complement(), NNF::Lit(l) if l == Lit::pos(0)));
    }

    #[test]
    fn test_complement_sum_becomes_prod() {
        // (a + b)' = a' · b'
        let m = sum(vec![v(0), v(1)]).complement();
        assert!(matches!(m, NNF::Prod(_)));
    }

    #[test]
    fn test_complement_prod_becomes_sum() {
        // (a · b)' = a' + b'
        let m = prod(vec![v(0), v(1)]).complement();
        assert!(matches!(m, NNF::Sum(_)));
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
