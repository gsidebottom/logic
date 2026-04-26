use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;
use serde::{Deserialize, Serialize};
use crate::formula::{count_primes, get_base_name, Ast, Node};

/// Process-wide tokio runtime used by synchronous wrappers (like
/// `Matrix::valid` / `Matrix::satisfiable`) that need to `block_on` an async
/// `classify_paths` call.  Building a fresh multi-threaded runtime costs
/// roughly a millisecond; reusing one amortises that across calls.  The
/// runtime has a single worker thread, which is plenty for the blocking-task
/// pool that `classify_paths` dispatches work onto.
pub fn shared_runtime() -> &'static tokio::runtime::Runtime {
    static RT: OnceLock<tokio::runtime::Runtime> = OnceLock::new();
    RT.get_or_init(|| {
        tokio::runtime::Builder::new_multi_thread()
            .worker_threads(1)
            .enable_all()
            .build()
            .expect("failed to build shared tokio runtime")
    })
}

/// Two-way handle on a running path-classification job: callers use it to
/// cooperatively cancel the worker, and the worker uses it to publish a
/// best-effort live progress count of *paths classified so far* (covered
/// + uncovered, weighted by each covered prefix's cover count) so readers
/// see something tick even when the result channel is silent — e.g. an
/// UNSAT formula in `no_cover` mode classifies many paths but emits no
/// class events.
///
/// The progress value is an `f64` because cover counts can vastly exceed
/// `u64`'s range for large NNFs; we store it as `f64::to_bits` inside an
/// `AtomicU64` so loads and stores stay lock-free.
#[derive(Clone, Default, Debug)]
pub struct PathClassificationHandle {
    cancelled: Arc<AtomicBool>,
    paths:     Arc<std::sync::atomic::AtomicU64>,
}

impl PathClassificationHandle {
    pub fn new() -> Self { Self::default() }
    pub fn cancel(&self) { self.cancelled.store(true, Ordering::Relaxed); }
    pub fn is_cancelled(&self) -> bool { self.cancelled.load(Ordering::Relaxed) }
    /// Worker-side: publish the current count of paths classified so far
    /// (sum of cover counts of covered prefixes plus the number of uncovered
    /// paths reached).  Monotonically non-decreasing during a single run.
    pub fn record_paths(&self, n: f64) {
        self.paths.store(n.to_bits(), Ordering::Relaxed);
    }
    pub fn paths_so_far(&self) -> f64 {
        f64::from_bits(self.paths.load(Ordering::Relaxed))
    }
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
    /// Limited number of paths classes reported.
    #[serde(default = "PathParams::default_paths_class_limit")]
    pub paths_class_limit: usize,
    /// Limited number of uncovered paths reported.
    #[serde(default = "PathParams::default_uncovered_path_limit")]
    pub uncovered_path_limit: usize,
    /// Limited number of covered prefixes reported.
    #[serde(default = "PathParams::default_covered_prefix_limit")]
    pub covered_prefix_limit: usize,
    /// If true, run with a controller whose `needs_cover()` is `false` — no
    /// `CoveredPathPrefix` events are built or emitted, and position tracking
    /// is skipped inside the traversal.  Intended for "I just want yes/no
    /// with a witness" queries like validity / satisfiability.
    #[serde(default)]
    pub no_cover: bool,
}

impl PathParams {
    fn default_paths_class_limit() -> usize { 100 }
    fn default_uncovered_path_limit() -> usize { usize::MAX }
    fn default_covered_prefix_limit() -> usize { usize::MAX }
}

impl Default for PathParams {
    fn default() -> Self {
        PathParams {
            paths_class_limit: Self::default_paths_class_limit(),
            uncovered_path_limit: Self::default_uncovered_path_limit(),
            covered_prefix_limit: Self::default_covered_prefix_limit(),
            no_cover: false,
        }
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
/// `paths_class_limit` limits `classes.len()`.
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

// ─── PathSearchController re-exports ──────────────────────────────────────────
//
// The trait, the workhorse cover-aware controller, and the propagation-aware
// SAT controller all live in the [`crate::controller`] module.  We re-export
// the names here so existing call-sites that wrote
// `use crate::matrix::PathSearchController` keep compiling.

pub use crate::controller::{
    BacktrackWhenCoveredController, PathSearchController, SmartController,
};


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

    /// Evaluate this NNF under a partial assignment.
    /// Returns `Ok(true)` if the formula is determined true, `Ok(false)` if
    /// determined false, and `Err(())` if the assignment is insufficient.
    /// A `Lit::pos(x)` in the assignment means `x=1`, `Lit::neg(x)` means `x=0`.
    pub fn evaluate(&self, assignment: &[Lit]) -> Result<bool, ()> {
        match self {
            NNF::Lit(l) => {
                // Find this variable in the assignment
                match assignment.iter().find(|a| a.var == l.var) {
                    None => Err(()),
                    Some(a) => Ok(a.neg == l.neg), // both neg or both pos → literal is true
                }
            }
            NNF::Sum(ch) => {
                // OR: true if any child true, false if all false, undetermined otherwise
                let mut all_false = true;
                for c in ch {
                    match c.evaluate(assignment) {
                        Ok(true) => return Ok(true),
                        Ok(false) => {}
                        Err(()) => { all_false = false; }
                    }
                }
                if all_false { Ok(false) } else { Err(()) }
            }
            NNF::Prod(ch) => {
                // AND: false if any child false, true if all true, undetermined otherwise
                let mut all_true = true;
                for c in ch {
                    match c.evaluate(assignment) {
                        Ok(false) => return Ok(false),
                        Ok(true) => {}
                        Err(()) => { all_true = false; }
                    }
                }
                if all_true { Ok(true) } else { Err(()) }
            }
        }
    }

    /// Total number of paths through this NNF.
    /// A path selects one member from each Prod and visits all children of each Sum.
    pub fn path_count(&self) -> f64 {
        match self {
            NNF::Lit(_)   => 1.0,
            NNF::Sum(ch)  => ch.iter().map(|c| c.path_count()).product(),
            NNF::Prod(ch) => ch.iter().map(|c| c.path_count()).sum(),
        }
    }

    /// Number of complete paths to the right of the last position in `prefix`.
    /// When a covered prefix is found during DFS, only the remaining Sum
    /// children (not yet crossed) are pruned. Prod siblings are visited
    /// independently because `covered_at_depth` clears when `lits` shrinks.
    pub fn prefix_cover_count(&self, prefix: &PathPrefix) -> f64 {
        let Some(last_pos) = prefix.last() else { return self.path_count() };
        fn walk(node: &NNF, pos: &[usize], multiplier: f64) -> f64 {
            if pos.is_empty() {
                return multiplier;
            }
            match node {
                NNF::Lit(_) => multiplier,
                NNF::Sum(ch) => {
                    let idx = pos[0];
                    // Remaining Sum children idx+1..n-1 haven't been crossed yet;
                    // they are skipped when we backtrack.
                    let remaining: f64 = ch[idx + 1..].iter()
                        .map(|c| c.path_count())
                        .product();
                    walk(&ch[idx], &pos[1..], multiplier * remaining)
                }
                NNF::Prod(ch) => {
                    // Prod siblings are NOT pruned — covered_at_depth clears
                    // when lits shrinks back after each Prod child.
                    walk(&ch[pos[0]], &pos[1..], multiplier)
                }
            }
        }
        walk(self, last_pos, 1.0)
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
    /// non-complementary paths (up to `paths_class_limit`) without
    /// enumerating all paths.
    pub fn paths<C: PathSearchController + ?Sized>(&self, ctrl: &mut C) {
        self.for_each_path_prefix_with_controller(ctrl);
    }

    /// Run [`Self::for_each_path_prefix`] driven by a [`PathSearchController`].
    /// Bridges the trait's `sum_ord` / `prod_ord` / `should_continue_on_prefix`
    /// methods into the three closures the function expects.  A `RefCell`
    /// gives the closures shared access to the controller — calls are
    /// strictly sequential within the DFS so the runtime borrow check never
    /// trips.
    ///
    /// Generic on the concrete `C` rather than `&mut dyn ...` because
    /// `PathSearchController` carries an associated type (`OnClass`) that
    /// can't be left unspecified in a trait object.  Static dispatch
    /// works for all callers and lets the compiler inline the bridge
    /// closures.
    pub fn for_each_path_prefix_with_controller<C: PathSearchController + ?Sized>(&self, ctrl: &mut C) {
        let cell = std::cell::RefCell::new(ctrl);
        self.for_each_path_prefix_ord(
            |children| cell.borrow_mut().sum_ord(children),
            |children| cell.borrow_mut().prod_ord(children),
            |lits, positions, prod_path| {
                cell.borrow_mut().should_continue_on_prefix(lits, positions, prod_path)
            },
        );
    }

    /// Same as [`Self::for_each_path_prefix_with_controller`] but for the
    /// positions-off traversal.  The controller must declare
    /// `needs_cover() == false` so the empty `prefix_positions` slice it
    /// receives is contractually valid.
    pub fn for_each_path_prefix_no_positions_with_controller<C: PathSearchController + ?Sized>(
        &self,
        ctrl: &mut C,
    ) {
        debug_assert!(!ctrl.needs_cover(),
            "no-positions traversal requires needs_cover() == false");
        let cell = std::cell::RefCell::new(ctrl);
        self.for_each_path_prefix_no_positions_ord(
            |children| cell.borrow_mut().sum_ord(children),
            |children| cell.borrow_mut().prod_ord(children),
            |lits, prod_path, _cover_mult| {
                let empty = PathPrefix::new();
                // No-positions traversal still uses simple bool semantics: any
                // non-None unwind request collapses to "backtrack one level."
                cell.borrow_mut().should_continue_on_prefix(lits, &empty, prod_path).is_none()
            },
        );
    }

    /// Async streaming path classification.  Spawns a blocking thread that
    /// runs the DFS via [`Self::for_each_path_prefix_with_controller`],
    /// wrapping the caller-supplied inner controller in a [`CancelController`]
    /// for cooperative cancellation and progress publishing.  Each
    /// `(PathsClass, hit_limit)` event the inner controller emits flows
    /// through the channel returned in the second tuple slot.
    ///
    /// `controller_builder` is a one-shot factory that receives the
    /// channel `Sender` and returns a `PathSearchController`; it lets
    /// callers pick any controller (typically
    /// [`BacktrackWhenCoveredController`] or a [`SmartController`]) and
    /// decide how class events should be plumbed onto the channel.  The
    /// traversal stops cleanly if the receiver is dropped — the next
    /// `blocking_send` fails, the closure returns `false`, and the inner
    /// controller honours that on its next `should_continue_on_paths_class`
    /// call.
    pub fn classify_paths<C, B>(
        &self,
        buffer_size: usize,
        controller_builder: B,
    ) -> (
        tokio::task::JoinHandle<Result<(), Box<dyn std::error::Error + Send>>>,
        tokio::sync::mpsc::Receiver<(PathsClass, bool)>,
        PathClassificationHandle,
    )
    where
        C: PathSearchController + Send + 'static,
        B: FnOnce(tokio::sync::mpsc::Sender<(PathsClass, bool)>) -> C + Send + 'static,
    {
        let m = self.clone();
        let (tx, rx) = tokio::sync::mpsc::channel::<(PathsClass, bool)>(buffer_size);
        let cancel = PathClassificationHandle::new();
        let cancel_for_thread = cancel.clone();
        let handle = tokio::task::spawn_blocking(move || {
            let inner = controller_builder(tx);
            let mut ctrl = crate::controller::CancelController::new(inner, cancel_for_thread);
            m.for_each_path_prefix_with_controller(&mut ctrl);
            ctrl.publish_progress();
            Ok::<(), Box<dyn std::error::Error + Send>>(())
        });
        (handle, rx, cancel)
    }

    /// Uncovered-only streaming variant of [`Self::classify_paths`].  Runs
    /// the caller-supplied controller via the positions-off traversal
    /// ([`Self::for_each_path_prefix_no_positions`]) so no
    /// `CoveredPathPrefix` is built and no `pos.clone()` happens at Lit
    /// visits.  The controller must report `needs_cover() == false` (this
    /// is debug-asserted on first traversal step).
    ///
    /// Progress reporting is cover-multiplier-weighted: when the
    /// controller's `covered_prefix_count()` ticks up, the
    /// classified-paths counter advances by `cover_mult` (the number of
    /// complete paths the just-detected cover stands for); when
    /// `uncovered_path_count()` ticks up, it advances by 1.  This keeps
    /// the rate display meaningful even on enormous formulas where each
    /// covered-prefix event prunes billions of paths.
    pub fn classify_paths_uncovered_only<C, B>(
        &self,
        buffer_size: usize,
        controller_builder: B,
    ) -> (
        tokio::task::JoinHandle<Result<(), Box<dyn std::error::Error + Send>>>,
        tokio::sync::mpsc::Receiver<(PathsClass, bool)>,
        PathClassificationHandle,
    )
    where
        C: PathSearchController + Send + 'static,
        B: FnOnce(tokio::sync::mpsc::Sender<(PathsClass, bool)>) -> C + Send + 'static,
    {
        let m = self.clone();
        let (tx, rx) = tokio::sync::mpsc::channel::<(PathsClass, bool)>(buffer_size);
        let cancel = PathClassificationHandle::new();
        let cancel_for_step = cancel.clone();
        let handle = tokio::task::spawn_blocking(move || {
            let mut ctrl = controller_builder(tx);
            debug_assert!(!ctrl.needs_cover(),
                "classify_paths_uncovered_only requires a controller with needs_cover() == false");
            let mut step: u64 = 0;
            let mut paths_classified: f64 = 0.0;
            let mut prev_cov: usize = 0;
            let mut prev_unc: usize = 0;
            m.for_each_path_prefix_no_positions(
                |lits, prod_path, cover_mult| {
                    if cancel_for_step.is_cancelled() { return false; }
                    let empty: PathPrefix = Vec::new();
                    let cont = ctrl.should_continue_on_prefix(lits, &empty, prod_path).is_none();
                    let cov = ctrl.covered_prefix_count();
                    let unc = ctrl.uncovered_path_count();
                    if cov > prev_cov {
                        paths_classified += cover_mult;
                        prev_cov = cov;
                    }
                    if unc > prev_unc {
                        paths_classified += 1.0;
                        prev_unc = unc;
                    }
                    step = step.wrapping_add(1);
                    if step & 0xFFF == 0 {
                        cancel_for_step.record_paths(paths_classified);
                    }
                    cont
                },
            );
            cancel_for_step.record_paths(paths_classified);
            Ok::<(), Box<dyn std::error::Error + Send>>(())
        });
        (handle, rx, cancel)
    }

    /// Depth-first traversal of all path prefixes, with generalized pruning
    /// and caller-controlled child order at Sum and Prod nodes.
    ///
    /// `sum_ord` and `prod_ord` are called once per Sum / Prod node the
    /// traversal enters and return `Option<Vec<(usize, &NNF)>>`:
    /// - `None` — visit the children in declaration order (no allocation).
    /// - `Some(order)` — visit the listed `(index, child)` pairs in the
    ///   given order, allowing permutation, filtering, or skipping.
    /// Indices identify the absolute child position used to record the
    /// path.
    ///
    /// `report_prefix(lits, positions, prod_path)` is called at each step:
    /// - When a `Prod` member is selected or a `Lit` is reached: `prod_path` is `None`
    /// - When a full path is completed: `prod_path` is `Some(&path)`
    ///
    /// `lits` and `positions` are parallel vectors: `positions[i]` is the
    /// absolute tree address of `lits[i]`.
    ///
    /// `report_prefix` returns `Option<usize>`:
    /// - `None` — continue forward.
    /// - `Some(0)` — backtrack one level: pop the last item from `pos` and
    ///   `path` and continue with the next sibling at this level.
    /// - `Some(i)` for `i > 0` — backtrack `i + 1` levels: pop the last
    ///   `i + 1` items from `pos` (and from `path` for those that were
    ///   `Prod` choices), then continue with the next sibling at the level
    ///   we land on.  Lets a caller skip up multiple recursion frames in
    ///   one shot — useful when a lit-set discovers that an ancestor's
    ///   choice has become impossible.
    pub fn for_each_path_prefix_ord<SO, PO>(
        &self,
        mut sum_ord:  SO,
        mut prod_ord: PO,
        mut report_prefix: impl FnMut(&Vec<&Lit>, &PathPrefix, Option<&ProdPath>) -> Option<usize>,
    )
    where
        SO: for<'a> FnMut(&'a [NNF]) -> Option<Vec<(usize, &'a NNF)>>,
        PO: for<'a> FnMut(&'a [NNF]) -> Option<Vec<(usize, &'a NNF)>>,
    {
        type Lits<'a> = Vec<&'a Lit>;
        type Positions = PathPrefix;

        #[allow(clippy::too_many_arguments)]
        fn traverse<'a, F, SO, PO>(
            m: &'a NNF,
            path: &mut ProdPath,
            lits: &mut Lits<'a>,
            positions: &mut Positions,
            pos: &mut Position,
            f: &mut F,
            sum_ord:  &mut SO,
            prod_ord: &mut PO,
            then: &mut dyn FnMut(&mut ProdPath, &mut Lits<'a>, &mut Positions, &mut Position, &mut F, &mut SO, &mut PO) -> Option<usize>,
        ) -> Option<usize>
        where
            F: FnMut(&Lits<'a>, &Positions, Option<&ProdPath>) -> Option<usize>,
            SO: for<'b> FnMut(&'b [NNF]) -> Option<Vec<(usize, &'b NNF)>>,
            PO: for<'b> FnMut(&'b [NNF]) -> Option<Vec<(usize, &'b NNF)>>,
        {
            match m {
                NNF::Lit(l) => {
                    lits.push(l);
                    positions.push(pos.clone());
                    let r = match f(lits, positions, None) {
                        None    => then(path, lits, positions, pos, f, sum_ord, prod_ord),
                        Some(k) => Some(k),
                    };
                    positions.pop();
                    lits.pop();
                    r
                }
                NNF::Prod(children) => {
                    let order_opt = prod_ord(children);
                    let len = order_opt.as_ref().map_or(children.len(), |o| o.len());
                    for ord_idx in 0..len {
                        let (i, child) = match &order_opt {
                            Some(o) => o[ord_idx],
                            None    => (ord_idx, &children[ord_idx]),
                        };
                        path.push(i);
                        pos.push(i);
                        let r = match f(lits, positions, None) {
                            None    => traverse(child, path, lits, positions, pos, f, sum_ord, prod_ord, then),
                            Some(k) => Some(k),
                        };
                        pos.pop();
                        path.pop();
                        match r {
                            // None: child completed normally; try next sibling.
                            // Some(0): unwind requested at this level only —
                            //          natural pop above already removed the
                            //          one item asked for; continue with next
                            //          sibling.
                            None | Some(0) => continue,
                            // Some(k>0): unwind further — propagate decremented.
                            Some(k)        => return Some(k - 1),
                        }
                    }
                    None
                }
                NNF::Sum(children) => {
                    let order_opt = sum_ord(children);
                    traverse_sum(children, order_opt.as_deref(), 0, path, lits, positions, pos, f, sum_ord, prod_ord, then)
                }
            }
        }

        #[allow(clippy::too_many_arguments)]
        fn traverse_sum<'a, F, SO, PO>(
            children: &'a [NNF],
            order:    Option<&[(usize, &'a NNF)]>,
            ord_idx:  usize,
            path: &mut ProdPath,
            lits: &mut Lits<'a>,
            positions: &mut Positions,
            pos: &mut Position,
            f: &mut F,
            sum_ord:  &mut SO,
            prod_ord: &mut PO,
            then: &mut dyn FnMut(&mut ProdPath, &mut Lits<'a>, &mut Positions, &mut Position, &mut F, &mut SO, &mut PO) -> Option<usize>,
        ) -> Option<usize>
        where
            F: FnMut(&Lits<'a>, &Positions, Option<&ProdPath>) -> Option<usize>,
            SO: for<'b> FnMut(&'b [NNF]) -> Option<Vec<(usize, &'b NNF)>>,
            PO: for<'b> FnMut(&'b [NNF]) -> Option<Vec<(usize, &'b NNF)>>,
        {
            let len = order.map_or(children.len(), |o| o.len());
            if ord_idx >= len {
                return then(path, lits, positions, pos, f, sum_ord, prod_ord);
            }
            let (child_idx, child) = match order {
                Some(o) => o[ord_idx],
                None    => (ord_idx, &children[ord_idx]),
            };
            let pos_len = pos.len();
            pos.push(child_idx);
            let r = traverse(child, path, lits, positions, pos, f, sum_ord, prod_ord,
                &mut |path, lits, positions, pos, f, sum_ord, prod_ord| {
                    let saved_pos = pos.clone();
                    pos.truncate(pos_len);
                    let r = traverse_sum(children, order, ord_idx + 1, path, lits, positions, pos, f, sum_ord, prod_ord, then);
                    if r.is_none() { *pos = saved_pos; }
                    r
                },
            );
            pos.truncate(pos_len);
            match r {
                None | Some(0) => None,
                Some(k)        => Some(k - 1),
            }
        }

        let mut path = ProdPath::new();
        let mut lits = Vec::new();
        let mut positions = Vec::new();
        let mut pos = Vec::new();
        traverse(self, &mut path, &mut lits, &mut positions, &mut pos, &mut report_prefix, &mut sum_ord, &mut prod_ord,
            &mut |path, lits, positions, _pos, f, _so, _po| {
                f(lits, positions, Some(path))
            },
        );
    }

    /// Positions-off variant of [`Self::for_each_path_prefix`].  Skips the
    /// per-Lit `pos.clone()` and doesn't maintain a parallel `positions` vec.
    /// Use when the controller's `needs_cover()` is `false` (e.g. for
    /// first-uncovered queries where cover certificates aren't consumed).
    ///
    /// The callback receives an additional `cover_mult: f64` argument: the
    /// number of complete paths through the NNF that share the *current*
    /// prefix.  When the controller detects a covered pair and returns
    /// false, this multiplier is the cover count of the covered prefix.
    /// At a path completion (`prod_path = Some(_)`) the multiplier is 1.
    pub fn for_each_path_prefix_no_positions(
        &self,
        f: impl FnMut(&Vec<&Lit>, Option<&ProdPath>, f64) -> bool,
    ) {
        // Thin wrapper over the `_ord` version with declaration-order Sum /
        // Prod traversal — same rationale as [`Self::for_each_path_prefix`].
        self.for_each_path_prefix_no_positions_ord(|_| None, |_| None, f);
    }

    /// Like [`Self::for_each_path_prefix_no_positions`] but with custom
    /// Sum/Prod child ordering — see [`Self::for_each_path_prefix_ord`].
    pub fn for_each_path_prefix_no_positions_ord<SO, PO>(
        &self,
        mut sum_ord:  SO,
        mut prod_ord: PO,
        mut f: impl FnMut(&Vec<&Lit>, Option<&ProdPath>, f64) -> bool,
    )
    where
        SO: for<'a> FnMut(&'a [NNF]) -> Option<Vec<(usize, &'a NNF)>>,
        PO: for<'a> FnMut(&'a [NNF]) -> Option<Vec<(usize, &'a NNF)>>,
    {
        type Lits<'a> = Vec<&'a Lit>;
        type Counts = HashMap<*const NNF, f64>;

        // Memoise path_count for every reachable subtree once.  Without this
        // the per-Sum sibling-product computations would call path_count
        // recursively and turn an O(N) traversal into O(N²) or worse.
        fn build_counts(n: &NNF, c: &mut Counts) -> f64 {
            let k = n as *const NNF;
            if let Some(&v) = c.get(&k) { return v; }
            let v = match n {
                NNF::Lit(_)   => 1.0,
                NNF::Sum(ch)  => ch.iter().map(|x| build_counts(x, c)).product(),
                NNF::Prod(ch) => ch.iter().map(|x| build_counts(x, c)).sum(),
            };
            c.insert(k, v);
            v
        }
        let mut counts: Counts = HashMap::new();
        build_counts(self, &mut counts);

        #[allow(clippy::too_many_arguments)]
        fn traverse<'a, F, SO, PO>(
            m: &'a NNF,
            mult: f64,
            path: &mut ProdPath,
            lits: &mut Lits<'a>,
            counts: &Counts,
            f: &mut F,
            sum_ord:  &mut SO,
            prod_ord: &mut PO,
            then: &mut dyn FnMut(f64, &mut ProdPath, &mut Lits<'a>, &Counts, &mut F, &mut SO, &mut PO),
        )
        where
            F: FnMut(&Lits<'a>, Option<&ProdPath>, f64) -> bool,
            SO: for<'b> FnMut(&'b [NNF]) -> Option<Vec<(usize, &'b NNF)>>,
            PO: for<'b> FnMut(&'b [NNF]) -> Option<Vec<(usize, &'b NNF)>>,
        {
            match m {
                NNF::Lit(l) => {
                    lits.push(l);
                    if f(lits, None, mult) {
                        then(mult, path, lits, counts, f, sum_ord, prod_ord);
                    }
                    lits.pop();
                }
                NNF::Prod(children) => {
                    let order_opt = prod_ord(children);
                    let len = order_opt.as_ref().map_or(children.len(), |o| o.len());
                    for ord_idx in 0..len {
                        let (i, child) = match &order_opt {
                            Some(o) => o[ord_idx],
                            None    => (ord_idx, &children[ord_idx]),
                        };
                        path.push(i);
                        if f(lits, None, mult) {
                            traverse(child, mult, path, lits, counts, f, sum_ord, prod_ord, then);
                        }
                        path.pop();
                    }
                }
                NNF::Sum(children) => {
                    let order_opt = sum_ord(children);
                    traverse_sum(children, order_opt.as_deref(), 0, mult, path, lits, counts, f, sum_ord, prod_ord, then);
                }
            }
        }

        #[allow(clippy::too_many_arguments)]
        fn traverse_sum<'a, F, SO, PO>(
            children: &'a [NNF],
            order:    Option<&[(usize, &'a NNF)]>,
            ord_idx:  usize,
            base_mult: f64,
            path: &mut ProdPath,
            lits: &mut Lits<'a>,
            counts: &Counts,
            f: &mut F,
            sum_ord:  &mut SO,
            prod_ord: &mut PO,
            then: &mut dyn FnMut(f64, &mut ProdPath, &mut Lits<'a>, &Counts, &mut F, &mut SO, &mut PO),
        )
        where
            F: FnMut(&Lits<'a>, Option<&ProdPath>, f64) -> bool,
            SO: for<'b> FnMut(&'b [NNF]) -> Option<Vec<(usize, &'b NNF)>>,
            PO: for<'b> FnMut(&'b [NNF]) -> Option<Vec<(usize, &'b NNF)>>,
        {
            let len = order.map_or(children.len(), |o| o.len());
            if ord_idx >= len {
                then(base_mult, path, lits, counts, f, sum_ord, prod_ord);
            } else {
                let child = match order {
                    Some(o) => o[ord_idx].1,
                    None    => &children[ord_idx],
                };
                // While inside the chosen child the *unvisited* Sum siblings —
                // those at order positions > ord_idx — contribute a product
                // factor; their path counts come from the memo.
                let after_mult: f64 = match order {
                    Some(o) => o[ord_idx+1..].iter()
                        .map(|(_, c)| counts[&(*c as *const NNF)])
                        .product(),
                    None => children[ord_idx+1..].iter()
                        .map(|c| counts[&(c as *const NNF)])
                        .product(),
                };
                let inner = base_mult * after_mult;
                traverse(child, inner, path, lits, counts, f, sum_ord, prod_ord,
                    &mut |_m, path, lits, counts, f, sum_ord, prod_ord| {
                        traverse_sum(children, order, ord_idx + 1, base_mult, path, lits, counts, f, sum_ord, prod_ord, then);
                    },
                );
            }
        }

        let mut path = ProdPath::new();
        let mut lits = Vec::new();
        traverse(self, 1.0, &mut path, &mut lits, &counts, &mut f, &mut sum_ord, &mut prod_ord,
            &mut |mult, path, lits, _counts, f, _so, _po| {
                f(lits, Some(path), mult);
            },
        );
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
                    NNF::Prod(ch.iter().map(|c| convert(c, var_index)).collect())
                }
                Node::Or(ch) => {
                    NNF::Sum(ch.iter().map(|c| convert(c, var_index)).collect())
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
    /// Async streaming path classification of either the matrix's NNF
    /// (`complement == false`) or its complement (`complement == true`).
    ///
    /// `params.no_cover` selects the traversal flavour: the default
    /// (`false`) builds full cover certificates via
    /// [`NNF::classify_paths`]; `true` switches to
    /// [`NNF::classify_paths_uncovered_only`], which uses the positions-off
    /// DFS and cover-multiplier-weighted progress.  In both cases the
    /// caller-supplied `controller_builder` constructs the inner controller
    /// — typically [`BacktrackWhenCoveredController`] in the appropriate
    /// mode (cover or uncovered_only), but any
    /// [`PathSearchController`] is accepted.
    pub fn classify_paths<C, B>(
        &self,
        complement: bool,
        buffer_size: usize,
        params: Option<PathParams>,
        controller_builder: B,
    ) -> (
        tokio::task::JoinHandle<Result<(), Box<dyn std::error::Error + Send>>>,
        tokio::sync::mpsc::Receiver<(PathsClass, bool)>,
        PathClassificationHandle,
    )
    where
        C: PathSearchController + Send + 'static,
        B: FnOnce(tokio::sync::mpsc::Sender<(PathsClass, bool)>) -> C + Send + 'static,
    {
        let target = if complement { &self.nnf_complement } else { &self.nnf };
        if params.as_ref().is_some_and(|p| p.no_cover) {
            target.classify_paths_uncovered_only(buffer_size, controller_builder)
        } else {
            target.classify_paths(buffer_size, controller_builder)
        }
    }

}

pub fn parse_to_nnf(formula: &str) -> Result<(NNF, Vec<String>), String> {
    let m = Matrix::try_from(formula)?;
    Ok((m.nnf, m.ast.vars))
}

/// Default `controller_builder` for [`Matrix::classify_paths`] and
/// [`NNF::classify_paths`] / [`NNF::classify_paths_uncovered_only`]:
/// builds a [`BacktrackWhenCoveredController`] in cover or uncovered-only
/// mode based on `params.no_cover`, plumbing each `(PathsClass, hit_limit)`
/// onto the supplied channel `Sender`.  When the receiver is dropped the
/// `blocking_send` fails and the controller stops classifying.
pub fn default_classify_controller(
    params: Option<PathParams>,
    tx: tokio::sync::mpsc::Sender<(PathsClass, bool)>,
) -> BacktrackWhenCoveredController<impl FnMut(PathsClass, bool) -> bool + Send> {
    let no_cover = params.as_ref().is_some_and(|p| p.no_cover);
    let on_class = move |class, hit_limit| tx.blocking_send((class, hit_limit)).is_ok();
    if no_cover {
        BacktrackWhenCoveredController::with_on_class_uncovered_only(params, on_class)
    } else {
        BacktrackWhenCoveredController::with_on_class(params, on_class)
    }
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── Test-only NNF helpers ─────────────────────────────────────────────────
    //
    // These methods used to live in the production `impl NNF` block but
    // weren't called from anywhere except tests.  Moving them under
    // `#[cfg(test)]` keeps the production surface lean and makes it
    // immediately obvious which APIs the rest of the crate (and downstream
    // consumers) actually depend on.

    impl NNF {
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

        /// Reference implementation: classify every path through a complete
        /// enumeration, then either build a cover (when all paths are
        /// complementary) or list the uncovered paths.  The fast streaming
        /// `classify_paths` path is cross-checked against this.
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

        /// Convenience wrapper over `for_each_path_prefix_ord` with natural
        /// child ordering.  Production code drives the traversal via
        /// `for_each_path_prefix_with_controller` which already supplies
        /// natural-order closures by default; this closure-style entry
        /// point exists only to keep the suite of small DFS unit tests
        /// readable.
        pub fn for_each_path_prefix(
            &self,
            report_prefix: impl FnMut(&Vec<&Lit>, &PathPrefix, Option<&ProdPath>) -> Option<usize>,
        ) {
            self.for_each_path_prefix_ord(|_| None, |_| None, report_prefix);
        }

        /// Async streaming variant of `paths`: spawns a blocking thread that
        /// runs the depth-first traversal and sends each `PathsClass` as it
        /// is discovered, paired with a `bool` that is `true` if this item
        /// caused the `paths_class_limit` to be reached.
        pub fn paths_async(
            &self,
            ctrl: impl PathSearchController + Send + 'static,
        ) -> (tokio::task::JoinHandle<()>, PathClassificationHandle) {
            let m = self.clone();
            let cancel = PathClassificationHandle::new();
            let mut wrapped = crate::controller::CancelController::new(ctrl, cancel.clone());
            let handle = tokio::task::spawn_blocking(move || {
                m.for_each_path_prefix_with_controller(&mut wrapped);
            });
            (handle, cancel)
        }

        /// Async variant of `for_each_path_prefix`: spawns a blocking thread
        /// that runs the depth-first traversal and sends each event as an
        /// owned `PathPrefixEvent` over the returned channel.  Used by the
        /// streaming-traversal unit test; production paths use
        /// `classify_paths` (class events) instead of streaming every step.
        pub fn for_each_path_prefix_async(
            &self,
            buffer_size: usize,
            mut path_prefix_controller: impl FnMut(&Vec<&Lit>, &PathPrefix, Option<&ProdPath>) -> bool + Send + 'static,
        ) -> (
            tokio::task::JoinHandle<Result<(), tokio::sync::mpsc::error::SendError<PathPrefixEvent>>>,
            tokio::sync::mpsc::Receiver<PathPrefixEvent>,
            PathClassificationHandle,
        ) {
            let m = self.clone();
            let (tx, rx) = tokio::sync::mpsc::channel::<PathPrefixEvent>(buffer_size);
            let cancel = PathClassificationHandle::new();
            let cancel_for_thread = cancel.clone();
            let handle = tokio::task::spawn_blocking(move || {
                let mut send_err = None;
                m.for_each_path_prefix(|lits, positions, prod_path| {
                    if send_err.is_some() || cancel_for_thread.is_cancelled() { return Some(0); }
                    let event = PathPrefixEvent {
                        lits: lits.iter().map(|&l| l.clone()).collect(),
                        positions: positions.clone(),
                        prod_path: prod_path.cloned(),
                    };
                    if let Err(e) = tx.blocking_send(event) {
                        send_err = Some(e);
                        return Some(0);
                    }
                    if path_prefix_controller(lits, positions, prod_path) { None } else { Some(0) }
                });
                send_err.map(Err).unwrap_or(Ok(()))
            });
            (handle, rx, cancel)
        }
    }

    // ── Test-only Matrix helpers ─────────────────────────────────────────────
    //
    // Sync convenience wrappers around `classify_paths` /
    // `classify_paths_uncovered_only`.  Production callers (web_app) drive
    // those streaming APIs directly so they can show progress, cancel, and
    // surface incremental results; the tests just want a one-shot answer
    // ("is this valid?", "give me a satisfying assignment") and these
    // wrappers keep the assertions readable.

    impl Matrix {
        /// Evaluate the formula under a partial assignment.  Forwards to
        /// `NNF::evaluate` on the matrix's NNF.
        pub fn evaluate(&self, assignment: &[Lit]) -> Result<bool, ()> {
            self.nnf.evaluate(assignment)
        }

        /// Check if the formula is valid (a tautology).  Returns `Ok(())` if
        /// valid, `Err(falsifying_assignment)` otherwise.
        pub fn valid(&self) -> Result<(), Vec<Lit>> {
            let params = Some(PathParams {
                uncovered_path_limit: 1,
                paths_class_limit: usize::MAX,
                covered_prefix_limit: usize::MAX,
                no_cover: true,
            });
            let p = params.clone();
            let uncovered = self.first_uncovered(false, params, |tx| {
                default_classify_controller(p, tx)
            });
            match uncovered {
                None => Ok(()),
                Some(path) => {
                    let assignment = self.path_to_assignment(&self.nnf, &path);
                    Err(assignment)
                }
            }
        }

        /// Check if the formula is satisfiable.  Returns
        /// `Ok(satisfying_assignment)` or `Err(())`.
        ///
        /// Uses the same `classify_paths`-based pipeline as `valid()`: a
        /// [`BacktrackWhenCoveredController`] does cover-pair detection, the
        /// `_uncovered_only` traversal skips position tracking, and the
        /// natural-order DFS finds the first non-conflicting path.  For
        /// structured formulas where a real SAT solver would shine
        /// (adders, large encoders), prefer
        /// [`Matrix::cadical_satisfiable`] — see `bench_faulty_add_at_most`
        /// for the gap.
        pub fn satisfiable(&self) -> Result<Vec<Lit>, ()> {
            let params = Some(PathParams {
                uncovered_path_limit: 1,
                paths_class_limit: usize::MAX,
                covered_prefix_limit: usize::MAX,
                no_cover: true,
            });
            let p = params.clone();
            let uncovered = self.first_uncovered(true, params, |tx| {
                default_classify_controller(p, tx)
            });
            match uncovered {
                None => Err(()),
                Some(path) => Ok(self.path_to_assignment(&self.nnf_complement, &path)),
            }
        }

        /// Smart-controller variant of [`Self::satisfiable`].  Drives the
        /// search through [`SmartController`], which preprocesses every
        /// Prod-of-Lits ("clause complement") into a watch-list index for
        /// cross-clause unit propagation.  Used by `smart_satisfiable_*`
        /// tests and the `bench_faulty_add_at_most` micro-benchmark.
        pub fn satisfiable_with_smart_controller(&self) -> Result<Vec<Lit>, ()> {
            let params = Some(PathParams {
                uncovered_path_limit: 1,
                paths_class_limit: usize::MAX,
                covered_prefix_limit: usize::MAX,
                no_cover: true,
            });
            let nnf = &self.nnf_complement;
            let mut uncovered: Option<ProdPath> = None;
            {
                let mut ctrl = SmartController::for_nnf(nnf, params, |class, _| {
                    if let PathsClass::Uncovered(p) = class {
                        uncovered = Some(p);
                        false
                    } else {
                        true
                    }
                });
                nnf.for_each_path_prefix_no_positions_with_controller(&mut ctrl);
            }
            match uncovered {
                None => Err(()),
                Some(path) => Ok(self.path_to_assignment(&self.nnf_complement, &path)),
            }
        }

        fn first_uncovered<C, B>(
            &self,
            complement: bool,
            params: Option<PathParams>,
            controller_builder: B,
        ) -> Option<ProdPath>
        where
            C: PathSearchController + Send + 'static,
            B: FnOnce(tokio::sync::mpsc::Sender<(PathsClass, bool)>) -> C + Send + 'static,
        {
            // Runs `classify_paths` (or its uncovered-only flavour when
            // `params.no_cover` is set) on the process-wide shared runtime
            // and returns the first `Uncovered` class emitted.  Dropping
            // the receiver signals the worker to stop; we still await the
            // handle for panic visibility.
            let nnf = if complement { &self.nnf_complement } else { &self.nnf };
            let no_cover = params.as_ref().is_some_and(|p| p.no_cover);
            shared_runtime().block_on(async {
                let (handle, mut rx, _cancel) = if no_cover {
                    nnf.classify_paths_uncovered_only(64, controller_builder)
                } else {
                    nnf.classify_paths(64, controller_builder)
                };
                let mut uncovered = None;
                while let Some((class, _)) = rx.recv().await {
                    if let PathsClass::Uncovered(p) = class {
                        uncovered = Some(p);
                        break;
                    }
                }
                drop(rx);
                let _ = handle.await;
                uncovered
            })
        }

        fn path_to_assignment(&self, nnf: &NNF, path: &ProdPath) -> Vec<Lit> {
            let lits = nnf.lits_on_path(path);
            let mut seen = std::collections::HashSet::new();
            lits.into_iter()
                .filter(|l| seen.insert(l.var))
                .map(|l| Lit { var: l.var, neg: !l.neg })
                .collect()
        }
    }

    // ── Helpers ───────────────────────────────────────────────────────────────

    fn v(n: Var) -> NNF { NNF::Lit(Lit::pos(n)) }
    fn vn(n: Var) -> NNF { NNF::Lit(Lit::neg(n)) }
    fn sum(ch: Vec<NNF>) -> NNF { NNF::Sum(ch) }
    fn prod(ch: Vec<NNF>) -> NNF { NNF::Prod(ch) }

    // ── CaDiCaL cross-check ────────────────────────────────────────────────────

    /// Check validity and satisfiability with CaDiCaL and compare to Matrix results.
    fn cadical_cross_check(
        formula: &str,
        matrix_valid: &Result<(), Vec<Lit>>,
        matrix_sat: &Result<Vec<Lit>, ()>,
        verbose: bool,
    ) {
        let m = Matrix::try_from(formula).unwrap();
        let vars = m.ast.vars.clone();
        let rt = tokio::runtime::Runtime::new().expect("failed to create runtime");

        let (valid_r, sat_r) = rt.block_on(async {
            if verbose { eprintln!("cadical sat solving '{}'", formula); }
            let t_sat = std::time::Instant::now();
            let (sat_handle, _cancel2) = m.cadical_satisfiable();
            let sr = sat_handle.await.expect("sat task panicked").expect("cadical sat failed");
            let sat_elapsed = t_sat.elapsed();
            if verbose || sat_elapsed.as_secs_f64() > 1.0 {
                eprintln!("cadical {:.2}ms to sat solve '{}'", sat_elapsed.as_secs_f64() * 1000.0, formula);
            }

            if verbose { eprintln!("cadical valid solving '{}'", formula); }
            let t_valid = std::time::Instant::now();
            let (valid_handle, _cancel) = m.cadical_valid();
            let vr = valid_handle.await.expect("valid task panicked").expect("cadical valid failed");
            let valid_elapsed = t_valid.elapsed();
            if verbose || valid_elapsed.as_secs_f64() > 1.0 {
                eprintln!("cadical {:.2}ms to valid solve '{}'", valid_elapsed.as_secs_f64() * 1000.0, formula);
            }

            (vr, sr)
        });

        let valid_result = &valid_r.result;
        let sat_result = &sat_r.result;

        // --- Format and print assignments ---
        let fmt_asgn = |asgn: &[Lit]| -> String {
            asgn.iter().map(|l| {
                let name = &vars[l.var as usize];
                if l.neg { format!("{}=0", name) } else { format!("{}=1", name) }
            }).collect::<Vec<_>>().join(", ")
        };
        let fmt_clause = |clause: &[i32]| -> String {
            clause.iter().map(|&lit| {
                let var_idx = lit.unsigned_abs() as usize - 1;
                let negated = lit < 0;
                if var_idx < vars.len() {
                    if negated { format!("{}'", vars[var_idx]) } else { vars[var_idx].clone() }
                } else {
                    if negated { format!("t{}'", var_idx + 1) } else { format!("t{}", var_idx + 1) }
                }
            }).collect::<Vec<_>>().join(" + ")
        };
        if verbose {
            if !valid_r.learned_clauses.is_empty() {
                eprintln!("cadical valid learned {} clauses:", valid_r.learned_clauses.len());
                for c in &valid_r.learned_clauses { eprintln!("  {}", fmt_clause(c)); }
            }
            if !sat_r.learned_clauses.is_empty() {
                eprintln!("cadical sat learned {} clauses:", sat_r.learned_clauses.len());
                for c in &sat_r.learned_clauses { eprintln!("  {}", fmt_clause(c)); }
            }
            match valid_result {
                Ok(()) => eprintln!("cadical: valid (complement unsatisfiable)"),
                Err(asgn) => eprintln!("cadical: not valid, falsifying: {}", fmt_asgn(asgn)),
            }
            match sat_result {
                Ok(asgn) => eprintln!("cadical: satisfiable, satisfying: {}", fmt_asgn(asgn)),
                Err(()) => eprintln!("cadical: unsatisfiable"),
            }
            match matrix_valid {
                Ok(()) => eprintln!("matrix: valid"),
                Err(asgn) => eprintln!("matrix: not valid, falsifying: {}", fmt_asgn(asgn)),
            }
            match matrix_sat {
                Ok(asgn) => eprintln!("matrix: satisfiable, satisfying: {}", fmt_asgn(asgn)),
                Err(()) => eprintln!("matrix: unsatisfiable"),
            }
        }

        // --- Compare Matrix results with CaDiCaL ---
        assert_eq!(matrix_valid.is_ok(), valid_result.is_ok(),
            "cadical and matrix disagree on validity of '{}'", formula);
        assert_eq!(matrix_sat.is_ok(), sat_result.is_ok(),
            "cadical and matrix disagree on satisfiability of '{}'", formula);

        if let Err(matrix_asgn) = matrix_valid {
            assert_eq!(m.evaluate(matrix_asgn), Ok(false),
                "matrix falsifying assignment doesn't evaluate to false");
        }
        if let Err(cadical_asgn) = valid_result {
            assert_eq!(m.evaluate(cadical_asgn), Ok(false),
                "cadical falsifying assignment doesn't evaluate to false");
        }
        if let Ok(matrix_asgn) = matrix_sat {
            assert_eq!(m.evaluate(matrix_asgn), Ok(true),
                "matrix satisfying assignment doesn't evaluate to true");
        }
        if let Ok(cadical_asgn) = sat_result {
            assert_eq!(m.evaluate(cadical_asgn), Ok(true),
                "cadical satisfying assignment doesn't evaluate to true");
        }
    }

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
        let (m, _) = parse_to_nnf("(A B) (C D)").unwrap();
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
        let (m, _) = parse_to_nnf("(A + B) + (C + D)").unwrap();
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
            None
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
            None
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
            if lits.last().is_some_and(|l| l.var == 1) { Some(0) } else { None }
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
        let (m, _) = parse_to_nnf("a + b + b' c' + c d + e").unwrap();
        let mut trace: Vec<(Vec<(Var, bool)>, Option<ProdPath>)> = Vec::new();
        m.for_each_path_prefix(|lits, _positions, prod_path| {
            trace.push((
                lits.iter().map(|l| (l.var, l.neg)).collect(),
                prod_path.cloned(),
            ));
            None
        });

        let a  = (0, false);
        let b  = (1, false);
        let bn = (1, true);
        let c  = (2, false);
        let cn = (2, true);
        let d  = (3, false);
        let e  = (4, false);

        // f is now also called at every Lit push (in addition to Prod
        // selects and complete-path leaves), so the trace records every
        // intermediate state as the lits stack grows.
        assert_eq!(trace, vec![
            // Sum children 0, 1: Lit a, Lit b pushes
            (vec![a],                None),
            (vec![a, b],             None),
            // Sum child 2: Prod2 select member 0 (b')
            (vec![a, b],             None),
            // Lit b' push inside Prod2
            (vec![a, b, bn],         None),
            // Sum child 3: Prod3 select member 0 (c)
            (vec![a, b, bn],         None),
            // Lit c push inside Prod3
            (vec![a, b, bn, c],      None),
            // Sum child 4: Lit e push
            (vec![a, b, bn, c, e],   None),
            // Complete path [0, 0]
            (vec![a, b, bn, c, e],   Some(vec![0, 0])),
            // Prod3 select member 1 (d)
            (vec![a, b, bn],         None),
            // Lit d push
            (vec![a, b, bn, d],      None),
            // Lit e push
            (vec![a, b, bn, d, e],   None),
            // Complete path [0, 1]
            (vec![a, b, bn, d, e],   Some(vec![0, 1])),
            // Prod2 select member 1 (c')
            (vec![a, b],             None),
            // Lit c' push
            (vec![a, b, cn],         None),
            // Prod3 select member 0 (c)
            (vec![a, b, cn],         None),
            // Lit c push
            (vec![a, b, cn, c],      None),
            // Lit e push
            (vec![a, b, cn, c, e],   None),
            // Complete path [1, 0]
            (vec![a, b, cn, c, e],   Some(vec![1, 0])),
            // Prod3 select member 1 (d)
            (vec![a, b, cn],         None),
            // Lit d push
            (vec![a, b, cn, d],      None),
            // Lit e push
            (vec![a, b, cn, d, e],   None),
            // Complete path [1, 1]
            (vec![a, b, cn, d, e],   Some(vec![1, 1])),
        ]);
    }

    // ── paths vs paths_reference ─────────────────────────────────

    fn assert_paths_matches(m: &NNF) {
        let fast = collect_paths(&m, Some(PathParams { paths_class_limit: usize::MAX, uncovered_path_limit: usize::MAX, covered_prefix_limit: usize::MAX, no_cover: false }));
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
        let (m, _) = parse_to_nnf("R'H' + L H R' + L' + R").unwrap();
        assert_paths_matches(&m);
    }

    #[test]
    fn test_paths_four_var() {
        let (m, _) = parse_to_nnf(
            "a'·b'·c + b'·c'·d + c'·d'·a' + d'·a·b' + a·b·c' + b·c·d' + c·d·a + d·a'·b"
        ).unwrap();
        assert_paths_matches(&m);
    }

    #[test]
    fn test_paths_paths_class_limit() {
        // (A·B) + (C·D) has 4 non-complementary paths: {A,C}, {A,D}, {B,C}, {B,D}
        let m = sum(vec![prod(vec![v(0), v(1)]), prod(vec![v(2), v(3)])]);

        // Limit 3: should return exactly 3 uncovered paths
        let p3 = collect_paths(&m, Some(PathParams { paths_class_limit: 3, uncovered_path_limit: usize::MAX, ..Default::default() }));
        assert_eq!(p3.uncovered_paths().count(), 3);

        // Limit 5 (more than total): should return all 4 uncovered paths
        let p5 = collect_paths(&m, Some(PathParams { paths_class_limit: 5, uncovered_path_limit: usize::MAX, ..Default::default() }));
        assert_eq!(p5.uncovered_paths().count(), 4);

        // Default limit (paths_class_limit=100): should return all 4 uncovered paths
        let p_default = collect_paths(&m, None);
        assert_eq!(p_default.uncovered_paths().count(), 4);
    }

    #[test]
    fn test_paths_covered_and_uncovered() {
        // a + a' b + c b' + a b + a a' b b'
        // 6 covered path prefixes + 4 uncovered paths = 10
        let (m, _) = parse_to_nnf("a + a' b + c b' + a b + a a' b b'").unwrap();
        let p = collect_paths(&m, Some(PathParams { paths_class_limit: 20, uncovered_path_limit: usize::MAX, ..Default::default() }));
        assert_eq!(p.covered_path_prefixes().count(), 6);
        assert_eq!(p.uncovered_paths().count(), 4);
        assert_eq!(p.cover().len(), 6);
    }

    // ── Matrix::classify_paths limits ──────────────────────────────────────

    // A (R' + S') + A' (R S) + B T + B' T' + A X'
    // has 10 uncovered paths and 11 covered prefixes (21 path classes total).
    const CLASSIFY_FORMULA: &str = "A (R' + S') + A' (R S) + B T + B' T' + A X'";

    /// Helper: collect all (PathsClass, hit_limit) from Matrix::classify_paths.
    async fn collect_classify(formula: &str, complement: bool, params: PathParams) -> Vec<(PathsClass, bool)> {
        let m = Matrix::try_from(formula).unwrap();
        let p = Some(params.clone());
        let (handle, mut rx, _cancel) = m.classify_paths(complement, 64, Some(params),
            move |tx| default_classify_controller(p, tx));
        let mut items = Vec::new();
        while let Some(item) = rx.recv().await {
            items.push(item);
        }
        handle.await.expect("worker panicked").expect("classify error");
        items
    }

    fn count_covered(items: &[(PathsClass, bool)]) -> usize {
        items.iter().filter(|(c, _)| matches!(c, PathsClass::Covered(_))).count()
    }
    fn count_uncovered(items: &[(PathsClass, bool)]) -> usize {
        items.iter().filter(|(c, _)| matches!(c, PathsClass::Uncovered(_))).count()
    }

    #[tokio::test]
    async fn test_classify_paths_no_limits() {
        let items = collect_classify(CLASSIFY_FORMULA, false, PathParams {
            paths_class_limit: usize::MAX,
            uncovered_path_limit: usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover: false,
        }).await;
        assert_eq!(count_covered(&items), 11);
        assert_eq!(count_uncovered(&items), 10);
        assert_eq!(items.len(), 21);
        // Only the last item should have hit_limit=true? No — no limit was hit.
        assert!(items.iter().all(|(_, hit)| !hit));
    }

    #[tokio::test]
    async fn test_classify_paths_class_limit() {
        // paths_class_limit=8: should get exactly 8 classes total
        let items = collect_classify(CLASSIFY_FORMULA, false, PathParams {
            paths_class_limit: 8,
            uncovered_path_limit: usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover: false,
        }).await;
        assert_eq!(items.len(), 8);
        assert!(items.last().unwrap().1); // last item has hit_limit=true
    }

    #[tokio::test]
    async fn test_classify_paths_uncovered_limit() {
        // uncovered_path_limit=3: should stop after 3 uncovered paths
        let items = collect_classify(CLASSIFY_FORMULA, false, PathParams {
            paths_class_limit: usize::MAX,
            uncovered_path_limit: 3,
            covered_prefix_limit: usize::MAX,
            no_cover: false,
        }).await;
        assert_eq!(count_uncovered(&items), 3);
        // May have some covered prefixes found before/between uncovered paths
        assert!(count_covered(&items) <= 6);
        assert!(items.last().unwrap().1);
    }

    #[tokio::test]
    async fn test_classify_paths_covered_limit() {
        // covered_prefix_limit=2: should stop after 2 covered prefixes
        let items = collect_classify(CLASSIFY_FORMULA, false, PathParams {
            paths_class_limit: usize::MAX,
            uncovered_path_limit: usize::MAX,
            covered_prefix_limit: 2,
            no_cover: false,
        }).await;
        assert_eq!(count_covered(&items), 2);
        // May have some uncovered paths found before/between covered prefixes
        assert!(count_uncovered(&items) <= 10);
        assert!(items.last().unwrap().1);
    }

    #[tokio::test]
    async fn test_classify_paths_uncovered_1() {
        // uncovered_path_limit=1: default-like, should get exactly 1 uncovered
        let items = collect_classify(CLASSIFY_FORMULA, false, PathParams {
            paths_class_limit: usize::MAX,
            uncovered_path_limit: 1,
            covered_prefix_limit: usize::MAX,
            no_cover: false,
        }).await;
        assert_eq!(count_uncovered(&items), 1);
        assert!(items.last().unwrap().1);
    }

    #[tokio::test]
    async fn test_classify_paths_all_limits_tight() {
        // All limits set to 1: whichever fires first stops
        let items = collect_classify(CLASSIFY_FORMULA, false, PathParams {
            paths_class_limit: 1,
            uncovered_path_limit: 1,
            covered_prefix_limit: 1,
            no_cover: false,
        }).await;
        assert_eq!(items.len(), 1);
        assert!(items[0].1); // hit_limit=true
    }

    #[tokio::test]
    async fn test_classify_paths_complement() {
        // Complement should have different path structure
        let items = collect_classify(CLASSIFY_FORMULA, true, PathParams {
            paths_class_limit: usize::MAX,
            uncovered_path_limit: usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover: false,
        }).await;
        // Just verify it runs and produces some classes
        assert!(!items.is_empty());
        assert!(items.iter().all(|(_, hit)| !hit));
    }

    // ── Matrix::valid / Matrix::satisfiable ────────────────────────────────

    #[test]
    fn test_valid_tautology() {
        let m = Matrix::try_from("A + A'").unwrap();
        assert!(m.valid().is_ok());
    }

    #[test]
    fn test_valid_not_tautology() {
        let m = Matrix::try_from("A").unwrap();
        let err = m.valid().unwrap_err();
        // A is not a tautology; falsifying assignment should set A=0
        assert_eq!(err.len(), 1);
        assert_eq!(err[0], Lit::neg(0)); // A=0
    }

    #[test]
    fn test_valid_equiv() {
        // a = b is not a tautology
        let m = Matrix::try_from("a = b").unwrap();
        assert!(m.valid().is_err());
    }

    #[test]
    fn test_satisfiable_simple() {
        let m = Matrix::try_from("A").unwrap();
        let asgn = m.satisfiable().unwrap();
        // A is satisfiable; satisfying assignment should set A=1
        assert_eq!(asgn.len(), 1);
        assert_eq!(asgn[0], Lit::pos(0)); // A=1
    }

    #[test]
    fn test_satisfiable_contradiction() {
        let m = Matrix::try_from("A A'").unwrap();
        assert!(m.satisfiable().is_err());
    }

    #[test]
    fn test_satisfiable_equiv() {
        // a = b is satisfiable (e.g. a=0, b=0)
        let m = Matrix::try_from("a = b").unwrap();
        let asgn = m.satisfiable().unwrap();
        // Both should have the same value
        let a_val = asgn.iter().find(|l| l.var == 0).unwrap();
        let b_val = asgn.iter().find(|l| l.var == 1).unwrap();
        assert_eq!(a_val.neg, b_val.neg, "a and b should have the same truth value");
    }

    #[test]
    fn test_evaluate() {
        let m = Matrix::try_from("A B + C").unwrap();
        // A=1, B=1 → A·B=true → true (short-circuit)
        assert_eq!(m.evaluate(&[Lit::pos(0), Lit::pos(1)]), Ok(true));
        // A=1, B=0, C=0 → A·B=false, C=false → false
        assert_eq!(m.evaluate(&[Lit::pos(0), Lit::neg(1), Lit::neg(2)]), Ok(false));
        // C=1 → C=true → true (short-circuit)
        assert_eq!(m.evaluate(&[Lit::pos(2)]), Ok(true));
        // A=0, C=0 → A·B=false, C=false → false regardless of B
        assert_eq!(m.evaluate(&[Lit::neg(0), Lit::neg(2)]), Ok(false));
        // A=1, B=0 → A·B=false, C=? → undetermined
        assert_eq!(m.evaluate(&[Lit::pos(0), Lit::neg(1)]), Err(()));
        // Empty assignment → undetermined
        assert_eq!(m.evaluate(&[]), Err(()));
    }

    #[test]
    fn test_valid_falsifying_evaluates_false() {
        let m = Matrix::try_from("A + A'B").unwrap();
        if let Err(asgn) = m.valid() {
            assert_eq!(m.evaluate(&asgn), Ok(false));
        }
    }

    #[test]
    fn test_satisfiable_assignment_evaluates_true() {
        let m = Matrix::try_from("A B + C").unwrap();
        let asgn = m.satisfiable().unwrap();
        assert_eq!(m.evaluate(&asgn), Ok(true));
    }

    #[test]
    fn test_valid_and_satisfiable_formula_r() {
        let f = "(a+b+c')(b+c+d')(c+d+a)(d+a'+b)(a'+b'+c)(b'+c'+d)(c'+d'+a')(d'+a+b')";
        let m = Matrix::try_from(f).unwrap();
        let valid = m.valid();
        assert_eq!(m.evaluate(valid.as_ref().unwrap_err()), Ok(false));
        let sat = m.satisfiable();
        assert!(sat.is_err());
        cadical_cross_check(f, &valid, &sat, false);
    }

    #[test]
    fn test_valid_and_satisfiable_formula_r_prime() {
        let f = "a'·b'·c + b'·c'·d + c'·d'·a' + d'·a·b' + a·b·c' + b·c·d' + c·d·a + d·a'·b";
        let m = Matrix::try_from(f).unwrap();
        let valid = m.valid();
        assert!(valid.is_ok());
        let sat = m.satisfiable();
        assert_eq!(m.evaluate(sat.as_ref().unwrap()), Ok(true));
        cadical_cross_check(f, &valid, &sat, false);
    }

    #[test]
    fn test_valid_and_satisfiable_formula_clpb_2() {
        let f = "A (R' + S') + A' (R S) + B T + B' T' + A X'";
        let m = Matrix::try_from(f).unwrap();
        let valid = m.valid();
        assert_eq!(m.evaluate(valid.as_ref().unwrap_err()), Ok(false));
        let sat = m.satisfiable();
        assert_eq!(m.evaluate(sat.as_ref().unwrap()), Ok(true));
        cadical_cross_check(f, &valid, &sat, false);
    }

    #[test]
    fn test_valid_and_satisfiable_formula_w338() {
        let f = "\
            (x_1 + x_2 + x_3) (x_1' + x_2' + x_3') \
            (x_2 + x_3 + x_4) (x_2' + x_3' + x_4') \
            (x_3 + x_4 + x_5) (x_3' + x_4' + x_5') \
            (x_4 + x_5 + x_6) (x_4' + x_5' + x_6') \
            (x_5 + x_6 + x_7) (x_5' + x_6' + x_7') \
            (x_6 + x_7 + x_8) (x_6' + x_7' + x_8') \
            (x_1 + x_3 + x_5) (x_1' + x_3' + x_5') \
            (x_2 + x_4 + x_6) (x_2' + x_4' + x_6') \
            (x_3 + x_5 + x_7) (x_3' + x_5' + x_7') \
            (x_4 + x_6 + x_8) (x_4' + x_6' + x_8') \
            (x_1 + x_4 + x_7) (x_1' + x_4' + x_7') \
            (x_2 + x_5 + x_8) (x_2' + x_5' + x_8')";
        let m = Matrix::try_from(f).unwrap();
        let valid = m.valid();
        assert_eq!(m.evaluate(valid.as_ref().unwrap_err()), Ok(false));
        let sat = m.satisfiable();
        assert_eq!(m.evaluate(sat.as_ref().unwrap()), Ok(true));
        cadical_cross_check(f, &valid, &sat, true);
    }

    #[test]
    #[ignore]
    fn test_valid_and_satisfiable_formula_w339() {
        let f = "\
            (x_1 + x_2 + x_3) (x_1' + x_2' + x_3') \
            (x_2 + x_3 + x_4) (x_2' + x_3' + x_4') \
            (x_3 + x_4 + x_5) (x_3' + x_4' + x_5') \
            (x_4 + x_5 + x_6) (x_4' + x_5' + x_6') \
            (x_5 + x_6 + x_7) (x_5' + x_6' + x_7') \
            (x_6 + x_7 + x_8) (x_6' + x_7' + x_8') \
            (x_7 + x_8 + x_9) (x_7' + x_8' + x_9') \
            (x_1 + x_3 + x_5) (x_1' + x_3' + x_5') \
            (x_2 + x_4 + x_6) (x_2' + x_4' + x_6') \
            (x_3 + x_5 + x_7) (x_3' + x_5' + x_7') \
            (x_4 + x_6 + x_8) (x_4' + x_6' + x_8') \
            (x_5 + x_7 + x_9) (x_5' + x_7' + x_9') \
            (x_1 + x_4 + x_7) (x_1' + x_4' + x_7') \
            (x_2 + x_5 + x_8) (x_2' + x_5' + x_8') \
            (x_3 + x_6 + x_9) (x_3' + x_6' + x_9') \
            (x_1 + x_5 + x_9) (x_1' + x_5' + x_9')";
        let m = Matrix::try_from(f).unwrap();
        let valid = m.valid();
        assert_eq!(m.evaluate(valid.as_ref().unwrap_err()), Ok(false));
        let sat = m.satisfiable();
        assert!(sat.is_err());
        cadical_cross_check(f, &valid, &sat, true);
    }

    #[test]
    fn test_valid_and_satisfiable_formula_equal_not_equal() {
        let f = "(a = b = c = d)' = (a ≠ b ≠ c ≠ d)";
        let m = Matrix::try_from(f).unwrap();
        let valid = m.valid();
        assert!(valid.is_ok());
        let sat = m.satisfiable();
        assert_eq!(m.evaluate(sat.as_ref().unwrap()), Ok(true));
        cadical_cross_check(f, &valid, &sat, false);
    }

    #[test]
    fn test_valid_larger_tautology() {
        let m = Matrix::try_from("R'H' + L H R' + L' + R").unwrap();
        assert!(m.valid().is_ok());
    }

    #[test]
    fn test_prefix_cover_count() {
        // Sum([A, B, Prod([C, D])])
        // path_count = 1 * 1 * (1+1) = 2
        // Paths: {A, B, C}, {A, B, D}
        let m = sum(vec![v(0), v(1), prod(vec![v(2), v(3)])]);
        assert_eq!(m.path_count(), 2.0);

        // DFS order: A, B, [Prod: C, D]
        // At A (pos [0]): remaining Sum siblings B, Prod → 1*2 = 2 paths to the right
        assert_eq!(m.prefix_cover_count(&vec![vec![0]]), 2.0);
        // At B (pos [1]): remaining Sum sibling Prod → 2 paths to the right
        assert_eq!(m.prefix_cover_count(&vec![vec![1]]), 2.0);
        // At C (pos [2,0]): no remaining Sum siblings; Prod sibling D is NOT pruned → 1
        assert_eq!(m.prefix_cover_count(&vec![vec![2, 0]]), 1.0);
        // At D (pos [2,1]): no remaining Sum siblings; no Prod siblings right of D → 1
        assert_eq!(m.prefix_cover_count(&vec![vec![2, 1]]), 1.0);

        // Prod([Sum([A, B]), Sum([C, D])])
        // path_count = 1 + 1 = 2. Paths: {A,B}, {C,D}.
        let m2 = prod(vec![sum(vec![v(0), v(1)]), sum(vec![v(2), v(3)])]);
        assert_eq!(m2.path_count(), 2.0);
        // At A (pos [0,0]): remaining Sum sibling B → multiplier 1; Prod sibling ignored → 1
        assert_eq!(m2.prefix_cover_count(&vec![vec![0, 0]]), 1.0);
        // At C (pos [1,0]): remaining Sum sibling D → multiplier 1 → 1
        assert_eq!(m2.prefix_cover_count(&vec![vec![1, 0]]), 1.0);

        // prefix_cover_count uses last position only
        assert_eq!(m.prefix_cover_count(&vec![vec![0], vec![2, 0]]), 1.0);

        // Empty prefix → full path_count
        assert_eq!(m.prefix_cover_count(&vec![]), 2.0);

        // Verify invariant: sum of prefix_cover_counts for covered prefixes
        // + uncovered path count == total path_count. This holds because the
        // DFS partitions the path space: each covered prefix accounts for its
        // pruned subtree, and uncovered paths each account for 1 path.
        let (nnf, _) = parse_to_nnf(CLASSIFY_FORMULA).unwrap();
        let total = nnf.path_count();
        let p = collect_paths(&nnf, Some(PathParams {
            paths_class_limit: usize::MAX,
            uncovered_path_limit: usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover: false,
        }));
        let covered_sum: f64 = p.covered_path_prefixes()
            .map(|cp| nnf.prefix_cover_count(&cp.prefix))
            .sum();
        let uncovered_count = p.uncovered_paths().count() as f64;
        assert_eq!(covered_sum + uncovered_count, total,
            "covered paths ({}) + uncovered paths ({}) should equal total ({})",
            covered_sum, uncovered_count, total);
    }

    #[tokio::test]
    async fn test_paths_async_cancel() {
        // Large enumeration; cancel after the first item.
        let m = sum((0..6).map(|_| prod(vec![v(0), v(1), v(2), v(3)])).collect());
        let (tx, mut rx) = tokio::sync::mpsc::channel::<(PathsClass, bool)>(1);
        let ctrl = BacktrackWhenCoveredController::with_on_class(
            Some(PathParams { paths_class_limit: usize::MAX, uncovered_path_limit: usize::MAX, covered_prefix_limit: usize::MAX, no_cover: false }),
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
        let (m, _) = parse_to_nnf("a + a' b + c b' + a b + a a' b b'").unwrap();
        let params = Some(PathParams { paths_class_limit: 20, uncovered_path_limit: usize::MAX, ..Default::default() });
        let sync_paths = collect_paths(&m, params.clone());

        let (tx, mut rx) = tokio::sync::mpsc::channel::<(PathsClass, bool)>(8);
        let ctrl = BacktrackWhenCoveredController::with_on_class(
            params,
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
        let (m, _) = parse_to_nnf("a b + c d").unwrap();

        let mut sync_events: Vec<(Vec<Lit>, PathPrefix, Option<ProdPath>)> = Vec::new();
        m.for_each_path_prefix(|lits, positions, prod_path| {
            sync_events.push((
                lits.iter().map(|&l| l.clone()).collect(),
                positions.clone(),
                prod_path.cloned(),
            ));
            None
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

    /// Load the expr and adder jq libraries, generate the formula for
    /// `add(16;371;226;0;empty;empty)` (a 16-bit ripple adder with a=371,
    /// b=226, c_in=0 and free outputs) and verify that both Matrix and CaDiCaL
    /// report it satisfiable with assignments that agree on every shared var.
    #[test]
    fn sat_adder_jq_371_plus_226() {
        use xq::{module_loader::PreludeLoader, run_query, Value as XqValue};

        // Strip any `# === tests ===` / `# === deps ===` sections that may have
        // been saved via the web editor — those are structural markers that
        // aren't valid here where we concatenate the libraries ourselves.
        let strip_sections = |s: &str| -> String {
            let cut = s.find("\n# === tests ===").unwrap_or(s.len());
            let head = &s[..cut];
            let mut out = String::new();
            let mut lines = head.lines();
            // Drop a leading `# === deps === … # === end deps ===` block if present.
            let peek: Vec<&str> = lines.clone().take_while(|l| l.trim().is_empty()).collect();
            for _ in 0..peek.len() { lines.next(); }
            let mut rest = lines.clone();
            if let Some(first) = rest.next() {
                if first.trim_end() == "# === deps ===" {
                    // advance original iterator past the block
                    for _ in 0..peek.len() { /* already skipped */ }
                    lines.next(); // consume the deps marker
                    while let Some(l) = lines.next() {
                        if l.trim_end() == "# === end deps ===" { break; }
                    }
                }
            }
            for l in lines { out.push_str(l); out.push('\n'); }
            out
        };
        // Concatenate every dep adder.jq has accumulated.  Order matters —
        // dependencies must precede the libs that use them; we rely on the
        // current set of files in lib/ here rather than parsing the deps
        // marker so the test stays self-contained.
        let load = |name: &str| -> String {
            strip_sections(&std::fs::read_to_string(format!("lib/{}", name))
                .unwrap_or_else(|e| panic!("read lib/{}: {}", name, e)))
        };
        let expr     = load("expr.jq");
        let math     = load("math.jq");
        let at_most  = load("at_most.jq");
        let adder    = load("adder.jq");
        let combined = format!(
            "{}\n{}\n{}\n{}\nadd(16;371;226;0;empty;empty)",
            expr, math, at_most, adder,
        );

        let loader  = PreludeLoader();
        let context = std::iter::once(Ok::<XqValue, xq::InputError>(XqValue::Null));
        let input   = std::iter::empty::<Result<XqValue, xq::InputError>>();

        let iter = run_query(&combined, context, input, &loader)
            .expect("jq query failed to compile");
        let json_vals: Vec<String> = iter
            .map(|r| r.expect("jq emitted error").to_string())
            .collect();
        assert_eq!(json_vals.len(), 1, "expected a single formula output, got {}", json_vals.len());
        // xq's to_string() returns a JSON encoding; the value is a JSON string, so unquote.
        let formula: String = serde_json::from_str(&json_vals[0])
            .expect("formula result was not a JSON string");

        let matrix = Matrix::try_from(formula.as_str()).expect("parse adder formula");

        // Matrix.satisfiable — time for benchmarking.  Best of 21 runs (warm cache).
        let mut best = std::time::Duration::MAX;
        let mut matrix_asgn = None;
        for _ in 0..21 {
            let t = std::time::Instant::now();
            let a = matrix.satisfiable().expect("matrix: formula should be satisfiable");
            let dt = t.elapsed();
            if dt < best { best = dt; }
            matrix_asgn = Some(a);
        }
        let matrix_asgn = matrix_asgn.unwrap();
        eprintln!("Matrix::satisfiable best-of-21 took {:.3}µs", best.as_secs_f64() * 1_000_000.0);

        // CaDiCaL.satisfiable.
        let rt = tokio::runtime::Runtime::new().expect("tokio runtime");
        let cadical_asgn = rt.block_on(async {
            let (handle, _cancel) = matrix.cadical_satisfiable();
            handle.await.expect("cadical task panicked")
                .expect("cadical sat call failed")
                .result.expect("cadical: formula should be satisfiable")
        });

        // Build var -> value maps and require agreement wherever both solvers assigned
        // the same variable. (CaDiCaL usually returns a total assignment; Matrix may omit
        // variables not forced along the satisfying path.)
        let to_map = |lits: &[Lit]| -> HashMap<Var, bool> {
            lits.iter().map(|l| (l.var, !l.neg)).collect()
        };
        let m_map = to_map(&matrix_asgn);
        let c_map = to_map(&cadical_asgn);

        let mut overlap = 0;
        for (&var, &mval) in &m_map {
            if let Some(&cval) = c_map.get(&var) {
                overlap += 1;
                assert_eq!(
                    mval, cval,
                    "mismatch on {}: matrix={} cadical={}",
                    matrix.ast.vars[var as usize], mval as u8, cval as u8,
                );
            }
        }
        assert!(overlap > 0, "matrix and cadical assignments had no overlapping variables");

        // The output sum variables s_0..s_15 (s_0 is the LSB) must encode 371 + 226 = 597.
        // Check both solvers' assignments. CaDiCaL returns a total assignment so we
        // decode and compare the full 16-bit sum; Matrix's assignment may be partial,
        // so we verify every s_i it *does* contain matches the expected bit.
        const W: u32 = 16;
        const EXPECTED: u32 = 371 + 226;

        // CaDiCaL — full decode.
        let mut cadical_decoded: u32 = 0;
        for i in 0..W {
            let name = format!("s_{}", i);
            let idx = matrix.ast.vars.iter().position(|v| v == &name)
                .unwrap_or_else(|| panic!("variable {} not found in formula", name));
            let lit = cadical_asgn.iter().find(|l| l.var as usize == idx)
                .unwrap_or_else(|| panic!("no cadical assignment for {}", name));
            if !lit.neg { cadical_decoded |= 1 << i; }
        }
        assert_eq!(
            cadical_decoded, EXPECTED,
            "cadical s variables encode {} but 371 + 226 = {}", cadical_decoded, EXPECTED,
        );

        // Matrix — per-bit check on whatever s_i are present.
        let mut matrix_bits_checked = 0;
        for i in 0..W {
            let name = format!("s_{}", i);
            let idx = matrix.ast.vars.iter().position(|v| v == &name).unwrap() as Var;
            if let Some(&val) = m_map.get(&idx) {
                let expected_bit = ((EXPECTED >> i) & 1) == 1;
                assert_eq!(
                    val, expected_bit,
                    "matrix s_{} = {} but bit {} of {} is {}",
                    i, val as u8, i, EXPECTED, expected_bit as u8,
                );
                matrix_bits_checked += 1;
            }
        }
        assert!(matrix_bits_checked > 0, "matrix assignment contained no s_i variables");
    }

    /// Sanity check that the smart-controller path produces a valid
    /// satisfying assignment on a few small/medium formulas where the
    /// natural-order path is known to work.
    #[test]
    fn smart_satisfiable_matches_natural() {
        let cases = [
            "a",
            "a + b",
            "(a + b)(a' + c)(b' + c')",
            "(a_10' a_9' a_8' a_7' a_6 a_5 a_4 a_3' a_2 a_1 a_0)",
            // (a + b)(¬a + b)(a + ¬b) — only b=true(=1, a anything)? No: b=1 satisfies all; a=1,b=0 contradicts (¬a + b).
            // Actually (a+b)(¬a+b)(a+¬b): from clause 2: a=1 → b=1.  From clause 3: a=1 ∨ b=0; with b=1 → a=1.  So a=1,b=1 works.
            "(a + b)(a' + b)(a + b')",
            // Equation a · b = u expanded to CNF.
            "(a' + b' + u)(a + u')(b + u')",
            // 3-bit adder for 1+1=2 (no fault, exact arithmetic).
            "(a_2' a_1' a_0) (b_2' b_1' b_0) c_0' (s_2' s_1 s_0') c_3' \
             ((a_2 b_2 = u_2) (w_2 c_2 = v_2) (u_2 + v_2 = c_3) (a_2 \u{2295} b_2 = w_2) (w_2 \u{2295} c_2 = s_2)) \
             ((a_1 b_1 = u_1) (w_1 c_1 = v_1) (u_1 + v_1 = c_2) (a_1 \u{2295} b_1 = w_1) (w_1 \u{2295} c_1 = s_1)) \
             ((a_0 b_0 = u_0) (w_0 c_0 = v_0) (u_0 + v_0 = c_1) (a_0 \u{2295} b_0 = w_0) (w_0 \u{2295} c_0 = s_0))",
            // Simulate one bit-adder with a fault flag wrapping each equation.
            "(d_0' \u{21d2} (a b = u)) (d_1' \u{21d2} (w c = v)) (d_2' \u{21d2} (u + v = c_x)) (d_3' \u{21d2} (a \u{2295} b = w)) (d_4' \u{21d2} (w \u{2295} c = s))",
        ];
        for f in &cases {
            let m = match Matrix::try_from(*f) {
                Ok(m) => m,
                Err(e) => panic!("parse {}: {}", f, e),
            };
            let nat = m.satisfiable();
            let smart = m.satisfiable_with_smart_controller();
            assert_eq!(nat.is_ok(), smart.is_ok(),
                       "{}: natural={:?} smart={:?}", f, nat.is_ok(), smart.is_ok());
            if let Ok(asgn) = smart {
                let r = m.evaluate(&asgn);
                assert_eq!(r, Ok(true),
                    "{}: smart's assignment {:?} doesn't satisfy formula", f, asgn);
            }
        }
    }

    /// Run smart on `faulty_add(3;1;1;0;3;0)` (no at_most layer).  Bisects
    /// the bench failure to figure out which sub-formula confuses the
    /// propagation.
    #[test]
    #[ignore]
    fn smart_satisfiable_on_faulty_add_3() {
        use xq::{module_loader::PreludeLoader, run_query, Value as XqValue};
        let strip_sections = |s: &str| -> String {
            let cut = s.find("\n# === tests ===").unwrap_or(s.len());
            let head = &s[..cut];
            let mut out = String::new();
            let mut lines = head.lines();
            let peek: Vec<&str> = lines.clone().take_while(|l| l.trim().is_empty()).collect();
            for _ in 0..peek.len() { lines.next(); }
            let mut rest = lines.clone();
            if let Some(first) = rest.next() {
                if first.trim_end() == "# === deps ===" {
                    lines.next();
                    while let Some(l) = lines.next() {
                        if l.trim_end() == "# === end deps ===" { break; }
                    }
                }
            }
            for l in lines { out.push_str(l); out.push('\n'); }
            out
        };
        let load = |name: &str| -> String {
            strip_sections(&std::fs::read_to_string(format!("lib/{}", name))
                .unwrap_or_else(|e| panic!("read lib/{}: {}", name, e)))
        };
        let expr  = load("expr.jq");
        let math  = load("math.jq");
        let at_m  = load("at_most.jq");
        let adder = load("adder.jq");
        let combined = format!("{}\n{}\n{}\n{}\nfaulty_add(3;1;1;0;3;0)", expr, math, at_m, adder);

        let loader  = PreludeLoader();
        let context = std::iter::once(Ok::<XqValue, xq::InputError>(XqValue::Null));
        let input   = std::iter::empty::<Result<XqValue, xq::InputError>>();
        let iter    = run_query(&combined, context, input, &loader)
            .expect("jq compile");
        let json_vals: Vec<String> = iter.map(|r| r.expect("jq err").to_string()).collect();
        let formula: String = serde_json::from_str(&json_vals[0]).unwrap();

        let m = Matrix::try_from(formula.as_str()).unwrap();
        let nat   = m.satisfiable();
        let smart = m.satisfiable_with_smart_controller();
        assert_eq!(nat.is_ok(), smart.is_ok(),
                   "faulty_add(3): natural={:?} smart={:?}", nat.is_ok(), smart.is_ok());
        if let Ok(asgn) = smart {
            assert_eq!(m.evaluate(&asgn), Ok(true), "smart's assignment doesn't satisfy");
        }
    }

    /// Performance regression check.  Generates the formula for
    /// `faulty_add_at_most(3;1;1;0;3;0;1)` from the jq libraries and times
    /// both `Matrix::satisfiable()` and `Matrix::cadical_satisfiable()` on it.
    /// Use `cargo test --release --lib bench_faulty_add_at_most -- --nocapture
    /// --ignored` to run; ignored by default so it doesn't slow down regular
    /// CI but can be invoked deliberately.
    #[test]
    #[ignore]
    fn bench_faulty_add_at_most() {
        use xq::{module_loader::PreludeLoader, run_query, Value as XqValue};

        let strip_sections = |s: &str| -> String {
            let cut = s.find("\n# === tests ===").unwrap_or(s.len());
            let head = &s[..cut];
            let mut out = String::new();
            let mut lines = head.lines();
            let peek: Vec<&str> = lines.clone().take_while(|l| l.trim().is_empty()).collect();
            for _ in 0..peek.len() { lines.next(); }
            let mut rest = lines.clone();
            if let Some(first) = rest.next() {
                if first.trim_end() == "# === deps ===" {
                    lines.next();
                    while let Some(l) = lines.next() {
                        if l.trim_end() == "# === end deps ===" { break; }
                    }
                }
            }
            for l in lines { out.push_str(l); out.push('\n'); }
            out
        };
        let load = |name: &str| -> String {
            strip_sections(&std::fs::read_to_string(format!("lib/{}", name))
                .unwrap_or_else(|e| panic!("read lib/{}: {}", name, e)))
        };
        let expr    = load("expr.jq");
        let math    = load("math.jq");
        let at_most = load("at_most.jq");
        let adder   = load("adder.jq");
        let combined = format!(
            "{}\n{}\n{}\n{}\nfaulty_add_at_most(3;1;1;0;3;0;1)",
            expr, math, at_most, adder,
        );

        let loader  = PreludeLoader();
        let context = std::iter::once(Ok::<XqValue, xq::InputError>(XqValue::Null));
        let input   = std::iter::empty::<Result<XqValue, xq::InputError>>();
        let iter    = run_query(&combined, context, input, &loader)
            .expect("jq query failed to compile");
        let json_vals: Vec<String> = iter.map(|r| r.expect("jq emitted error").to_string()).collect();
        assert_eq!(json_vals.len(), 1);
        let formula: String = serde_json::from_str(&json_vals[0]).expect("formula not a JSON string");

        eprintln!("formula length: {} chars", formula.len());
        let matrix = Matrix::try_from(formula.as_str()).expect("parse formula");
        eprintln!("variables: {}", matrix.ast.vars.len());

        // ── Matrix::satisfiable (natural-order path) ──
        let t = std::time::Instant::now();
        let matrix_asgn = matrix.satisfiable().expect("matrix: should be satisfiable");
        let matrix_ms = t.elapsed().as_secs_f64() * 1000.0;
        eprintln!("Matrix::satisfiable        took {:>10.3} ms ({} lits)",
                  matrix_ms, matrix_asgn.len());

        // ── Matrix::satisfiable_with_smart_controller (heuristic path) ──
        let t = std::time::Instant::now();
        let smart_asgn = matrix.satisfiable_with_smart_controller()
            .expect("matrix smart: should be satisfiable");
        let smart_ms = t.elapsed().as_secs_f64() * 1000.0;
        eprintln!("Matrix::satisfiable_smart  took {:>10.3} ms ({} lits)",
                  smart_ms, smart_asgn.len());

        // ── Matrix::cadical_satisfiable ──
        let rt = tokio::runtime::Runtime::new().unwrap();
        let t = std::time::Instant::now();
        let cadical_asgn = rt.block_on(async {
            let (handle, _cancel) = matrix.cadical_satisfiable();
            handle.await.unwrap().unwrap().result.expect("cadical: should be satisfiable")
        });
        let cadical_ms = t.elapsed().as_secs_f64() * 1000.0;
        eprintln!("Matrix::cadical_satisfiable took {:>10.3} ms ({} lits)",
                  cadical_ms, cadical_asgn.len());

        eprintln!("ratio matrix/cadical:       {:.1}×", matrix_ms / cadical_ms.max(0.001));
        eprintln!("ratio smart/cadical:        {:.1}×", smart_ms  / cadical_ms.max(0.001));
    }
}
