//! Dual-process matrix search framework — Phase 1 plumbing.
//!
//! Two cooperating search processes (see `doc/dual-search-design.md`):
//!
//! * **Process A — cover search.**  Maintains the pool of complementary
//!   pairs and an evolving notion of "what's covered so far".  Picks
//!   pairs to *register* against the cover state using whatever
//!   heuristic.
//! * **Process B — uncovered-path search.**  Walks the NNF looking for
//!   an uncovered path, emitting pairs into the pool as it discovers
//!   them and (later) consulting A's cover state to prune.
//!
//! Phase 1 scope: minimal driver, simplest A and B controllers, an
//! append-only `Vec<Pair>` cover state.  B is the termination
//! authority — A is observational.  This validates the plumbing
//! without committing to any heuristic design.

pub mod cover_basic;
pub mod cover_bdd_bans;
pub mod cover_cnf_bans;
pub mod cover_greedy;
pub mod cover_greedy_dynamic;
pub mod cover_state_bdd;
pub mod cover_state_cnf;
pub mod effective_count;
pub mod flat;
pub mod path_basic;
pub mod path_cdcl;
pub mod path_effective;
pub mod path_smart;
pub mod wrapper;

#[cfg(test)]
mod bench;

pub use cover_basic::BasicCoverController;
pub use cover_bdd_bans::BddBansCoverController;
pub use cover_cnf_bans::CnfBansCoverController;
pub use cover_greedy::GreedyMaxCoverController;
pub use cover_greedy_dynamic::GreedyDynamicCoverController;
pub use cover_state_bdd::BddBansCoverState;
pub use cover_state_cnf::CnfBansCoverState;
pub use path_basic::BasicDualPathController;
pub use path_cdcl::CdclDualPathController;
pub use path_effective::EffectivePathController;
pub use path_smart::SmartDualPathController;

use crate::matrix::{NNF, Pair, PathPrefix, ProdPath};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};

/// Stack size for the A/B search threads spawned by [`solve_dual`] /
/// [`solve_dual_with_cancel`].  The matrix-method DFS in
/// `for_each_path_prefix_ord` recurses through Sum siblings via
/// continuation closures — on a CNF complement with N clauses the
/// nesting is `O(N)`, so industrial inputs (≥ 30k clauses) blow the
/// OS default 2 MB stack and abort with a fatal-runtime stack
/// overflow.
///
/// 256 MB matches the figure `sat.rs` configures on its tokio
/// runtime builder.  The dual backends call `solve_dual_with_cancel`
/// from a `spawn_blocking` task — that task itself runs on a tokio
/// blocking-pool thread with the configured big stack, but A and B
/// are spawned via `std::thread::spawn` *inside* that task and
/// inherit the OS default unless we override it explicitly.
const SEARCH_THREAD_STACK_SIZE: usize = 256 * 1024 * 1024;

/// Spawn a search thread with [`SEARCH_THREAD_STACK_SIZE`] bytes of
/// stack.  Use this in place of `std::thread::spawn` for any thread
/// that drives a matrix-method DFS — see the constant's docs for
/// why the OS default isn't enough.
fn spawn_search_thread<F, T>(name: &str, f: F) -> std::thread::JoinHandle<T>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    std::thread::Builder::new()
        .name(name.into())
        .stack_size(SEARCH_THREAD_STACK_SIZE)
        .spawn(f)
        .expect("failed to spawn search thread")
}

/// Outcome of a dual-process search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// An uncovered path was found — for SAT-mode this means the
    /// formula is satisfiable; for VALID-mode it means the formula is
    /// not valid.  The `ProdPath` identifies the path in the NNF.
    Sat(ProdPath),
    /// Every path was covered — for SAT-mode this means the formula
    /// is unsatisfiable; for VALID-mode it means the formula is valid.
    Unsat,
}

/// Result of process B (the path-search side) running to completion.
#[derive(Debug, Clone)]
pub enum PathOutcome {
    /// B found an uncovered path.  Path-search wins.
    Uncovered(ProdPath),
    /// B exhausted the search space without finding any uncovered
    /// path.  Implies all paths are covered (since B's controller
    /// detects covers itself, in Phase 1).
    Exhausted,
    /// B was cancelled (e.g. A reached UNSAT first).
    Cancelled,
}

/// Which side of the matrix-method theorem we're using.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchMode {
    /// Search the formula's complement, looking for a satisfying
    /// assignment.  An uncovered path = SAT.
    Satisfiable,
    /// Search the formula directly, looking for a falsifying
    /// assignment.  An uncovered path = not valid.
    Validity,
}

/// Append-only log of complementary pairs known to the search.  Both
/// processes share this through an `Arc`.
///
/// Phase 1 representation: a `Mutex<Vec<Pair>>`.  This is fine for
/// proving the plumbing; later phases can replace it with a
/// lock-free structure if contention shows up.
pub struct PairPool {
    pairs: Mutex<Vec<Pair>>,
}

impl PairPool {
    pub fn new() -> Arc<Self> {
        Arc::new(Self { pairs: Mutex::new(Vec::new()) })
    }

    /// Append a pair.  Returns its index in the pool.  Idempotent on
    /// the index sense: pushing the same pair twice yields two
    /// indices (Phase 1 doesn't dedup; the cover state can be the
    /// dedupping authority if it cares).
    pub fn push(&self, pair: Pair) -> usize {
        let mut p = self.pairs.lock().unwrap();
        let idx = p.len();
        p.push(pair);
        idx
    }

    pub fn len(&self) -> usize {
        self.pairs.lock().unwrap().len()
    }

    pub fn is_empty(&self) -> bool {
        self.pairs.lock().unwrap().is_empty()
    }

    pub fn get(&self, idx: usize) -> Option<Pair> {
        self.pairs.lock().unwrap().get(idx).cloned()
    }

    /// Snapshot for diagnostics / testing.
    pub fn snapshot(&self) -> Vec<Pair> {
        self.pairs.lock().unwrap().clone()
    }
}

/// Cover state — A's accumulated knowledge of which paths are
/// covered.  The trait is a query interface; concrete representations
/// can be append-only logs, BDDs, bitmaps, etc.
///
/// `Send + 'static` is required because the dual driver hands the
/// state to A and B threads via `Arc<Mutex<...>>`.  `Sync` is
/// *not* required: serialization is the Mutex's job, and some
/// representations (e.g. the [`crate::dual::cover_state_cnf::CnfBansCoverState`]'s
/// embedded CaDiCaL solver) are `Send` but not `Sync`.
pub trait CoverState: Send + 'static {
    /// Is the path identified by these prefix positions already
    /// covered by some pair we've registered?  Phase 1's basic
    /// state can return `false` always (it leaves cover detection
    /// to B's local controller); future phases use this to prune
    /// B early.
    ///
    /// **Coordinate system: absolute tree positions, not prod-path
    /// indices.**  `prefix_positions[k]` is the full path from
    /// the NNF root to the k-th lit on the prefix (e.g. `[c, a]`
    /// for "Sum-child c, Prod-alt a", or `[c]` for a singleton-Lit
    /// Sum-child).  Positions stay in the original declaration-order
    /// coordinate system regardless of any `sum_ord` re-ordering the
    /// engine's controller stack applied — they record which
    /// physical tree node the lit lives at, not which slot in
    /// `prod_path` accumulated it.
    ///
    /// Why this matters: `prod_path` indices track *DFS-visit
    /// order*.  When wrappers like
    /// `EffectiveCountWrapper::sum_ord` permute Sum-children for
    /// branch-ordering heuristics, `prod_path[k]` no longer
    /// corresponds to the k-th clause; matching pair triggers
    /// against `prod_path` indices produces both false negatives
    /// (missed prunes) and false positives (spurious "covered"
    /// verdicts, the soundness bug behind `greedy_eff` returning
    /// wrong `UNSAT` on SAT problems).
    fn is_prefix_covered(&self, prefix_positions: &PathPrefix) -> bool;

    /// Statistical summary used by some cover-search controllers.
    /// `None` if the representation can't answer cheaply.
    fn uncovered_estimate(&self) -> Option<f64> { None }

    /// Number of pairs that have been registered against this state.
    /// Used by tests and observers; not a soundness signal.
    fn registered_pair_count(&self) -> usize { 0 }
}

/// Cover-state representation for the dual framework.
///
/// **Flat-mode triggers.**  For a flat Sum-of-Prod-of-Lits matrix,
/// every Lit's `Position` is `[i, j]` meaning "Sum-child `i`,
/// Prod-alt `j`" — and the DFS visits Sum-children in order, so
/// `ProdPath[i]` is the alt picked for clause `i`.  A pair
/// `((i, a), (j, b))` therefore "fires" on a path iff
/// `prefix[i] == a ∧ prefix[j] == b`.  We pre-extract these
/// `(clause_idx, alt_idx)` triggers when registering a pair.
///
/// **Phase 4 indexed lookup.**  In addition to the trigger list,
/// the state maintains a per-`(clause_idx, alt_idx)` *bucket index*
/// of pair-IDs whose triggers fire on that bucket.  This turns
/// `is_prefix_covered` from O(|registered pairs|) into
/// O(|prefix| × avg pairs per bucket) — typically a 10-20× speedup
/// on PHP-sized formulas.
///
/// **Non-flat fallback.**  If the matrix isn't flat, no triggers
/// are extracted and `is_prefix_covered` returns `false` — sound
/// and conservative, leaves cover detection to B's local logic.
pub struct BasicCoverState {
    /// Raw registered pairs in arrival order.
    pairs: Vec<Pair>,
    /// Per-pair trigger conditions when the matrix is flat.  Each
    /// entry `[(i, a), (j, b)]` says "pair fires when path picks
    /// alt `a` for clause `i` and alt `b` for clause `j`".
    /// `None` means triggers couldn't be derived (non-flat NNF or
    /// malformed pair).
    ///
    /// **Coordinate system: clause-index, not prod-path-index.**
    /// `mine_pairs` and the absolute `prefix_positions` carried by
    /// `Covered` events both use clause indices (the 0..n_clauses
    /// range over Sum-children).  The matrix-method DFS, by
    /// contrast, emits its `prod_path` in prod-encounter-order:
    /// singleton-Lit Sum-children don't push to `prod_path` at all.
    /// The two coordinate systems differ whenever the NNF has any
    /// singleton-Lit child.  See [`Self::is_prefix_covered`] for
    /// the translation.
    triggers: Vec<Option<[(usize, usize); 2]>>,
    /// Whether the source NNF is flat Sum-of-Prods.  When false,
    /// `is_prefix_covered` short-circuits to `false`.
    is_flat: bool,
    /// Clause arities for the source NNF when flat; empty
    /// otherwise.  `arities[c] == 1` ⇔ clause `c` is a singleton-Lit
    /// (no `Prod` wrapper, no `prod_path` slot).
    arities: Vec<usize>,
    /// **Phase 4 bucket index.**  `index[clause_idx][alt_idx]` is
    /// the list of pair-IDs whose triggers include
    /// `(clause_idx, alt_idx)`.  Built lazily as pairs are
    /// registered.  Empty in non-flat mode.
    index: Vec<Vec<Vec<usize>>>,
    /// **All-singletons cover flag.**  Set true if any registered
    /// pair has triggers where both clauses are singletons (which
    /// would mean their lits are *always* on every complete path,
    /// so the pair covers the empty prefix — really every prefix).
    /// In a well-formed CNF input two complementary unit clauses
    /// imply trivial UNSAT, so this is set defensively but rarely
    /// fires in practice.
    has_always_covering_pair: bool,
}

impl BasicCoverState {
    pub fn new(nnf: &NNF) -> Self {
        let is_flat = is_flat_sum_of_prods(nnf);
        let arities = if is_flat {
            flat::flat_arities(nnf).unwrap_or_default()
        } else {
            Vec::new()
        };
        // Pre-allocate the bucket index with the right shape so
        // `add_pair` doesn't have to reshape per call.
        let index: Vec<Vec<Vec<usize>>> = arities.iter()
            .map(|&k| (0..k).map(|_| Vec::new()).collect())
            .collect();
        Self {
            pairs: Vec::new(),
            triggers: Vec::new(),
            is_flat,
            arities,
            index,
            has_always_covering_pair: false,
        }
    }

    /// Per-clause arity of the source matrix (empty for non-flat).
    pub fn arities(&self) -> &[usize] { &self.arities }

    /// Register a pair against the state.  Pre-extracts triggers
    /// for flat-mode matrices and indexes them by (clause, alt).
    pub fn add_pair(&mut self, pair: Pair) {
        let triggers = if self.is_flat {
            flat_pair_triggers(&pair)
        } else {
            None
        };
        let pair_idx = self.pairs.len();
        if let Some([(i, a), (j, b)]) = triggers {
            // Add this pair-ID to both buckets so a query can
            // discover it via either trigger.
            if i < self.index.len() && a < self.index[i].len() {
                self.index[i][a].push(pair_idx);
            }
            // Skip the second push if both triggers happen to land
            // in the same bucket — defensive against malformed
            // self-pairs.
            if (j, b) != (i, a) && j < self.index.len() && b < self.index[j].len() {
                self.index[j][b].push(pair_idx);
            }
            // If BOTH triggers point at singleton clauses, both lits
            // are on every complete path automatically — the pair
            // covers every prefix, including the empty one.  Flag it
            // so `is_prefix_covered` returns true without needing to
            // see either clause in the walked prefix.
            let i_is_singleton = i < self.arities.len() && self.arities[i] <= 1;
            let j_is_singleton = j < self.arities.len() && self.arities[j] <= 1;
            if i_is_singleton && j_is_singleton {
                self.has_always_covering_pair = true;
            }
        }
        self.pairs.push(pair);
        self.triggers.push(triggers);
    }

    pub fn pairs(&self) -> &[Pair] { &self.pairs }

    pub fn is_flat(&self) -> bool { self.is_flat }
}

impl CoverState for BasicCoverState {
    /// Phase 4 indexed lookup using absolute tree positions.  For
    /// every position on the prefix, decode `(clause_idx, alt_idx)`
    /// from the position vector and consult the bucket index for
    /// pairs whose triggers fire on that `(clause_idx, alt_idx)`;
    /// for each candidate pair, check whether its *other* trigger
    /// is also satisfied by some position on the prefix.
    ///
    /// **Why we walk `prefix_positions`, not `prefix_prod_path`.**
    /// Pair triggers are stored in clause-index coordinates — both
    /// `mine_pairs` and the `CoveredPathPrefix.cover` field of
    /// `Covered` events use absolute tree positions over the NNF's
    /// Sum-children.  The engine's `prod_path` is in DFS-visit
    /// order, which a wrapper like `EffectiveCountWrapper::sum_ord`
    /// can permute for branch-ordering — making `prod_path[k]`
    /// correspond to whatever clause the wrapper happened to visit
    /// k-th, not the k-th clause overall.  Indexing pair triggers
    /// by `prod_path` indices therefore mis-matches them against
    /// the wrong clauses on every reordered run, producing
    /// spurious "covered" verdicts that prune satisfiable subtrees.
    /// This was the soundness bug behind `greedy_eff` returning
    /// wrong `UNSAT` on SAT problems.
    ///
    /// `prefix_positions` doesn't have this problem: positions are
    /// recorded as the literal's tree-address (Sum-child index, then
    /// Prod-alt index for multi-alt clauses, or just the Sum-child
    /// index for singletons), and `traverse_sum` pushes the
    /// *original* child index even when consulting a re-ordered
    /// child list.  So `prefix_positions` is always in declaration-
    /// order coordinates and matches the pair triggers' coordinate
    /// system directly.
    ///
    /// Work O(|prefix| × avg pairs per bucket × |prefix|) — the
    /// "other trigger satisfied" check is O(|prefix|) because it
    /// scans the position list.  Per-query allocation of a small
    /// `clause_assignment` lookup table eliminates the inner scan
    /// in the common case where the same clause appears at most
    /// once on the prefix (always true for the flat
    /// Sum-of-Prod-of-Lits shape this matters for).
    fn is_prefix_covered(&self, prefix_positions: &PathPrefix) -> bool {
        if !self.is_flat { return false; }
        // Edge case: a pair whose both triggers point at singleton
        // clauses covers every prefix.  Short-circuit.
        if self.has_always_covering_pair { return true; }

        // Build a per-clause "assigned alt" lookup from the prefix
        // positions.  Sized by `self.arities.len()` because that's
        // the maximum clause index we'd ever want to index.  Vec
        // of `Option<usize>` is fine — `arities.len()` is bounded
        // by the matrix's clause count.
        let mut clause_assignment: Vec<Option<usize>> = vec![None; self.arities.len()];
        for pos in prefix_positions {
            let (c, a) = match pos.len() {
                1 => (pos[0], 0),
                2 => (pos[0], pos[1]),
                _ => continue,
            };
            if c < clause_assignment.len() {
                clause_assignment[c] = Some(a);
            }
        }

        // Walk positions, consult buckets, check the other trigger
        // via the precomputed assignment.
        for pos in prefix_positions {
            let (c, a) = match pos.len() {
                1 => (pos[0], 0),
                2 => (pos[0], pos[1]),
                _ => continue,
            };
            if c >= self.index.len() { continue; }
            if a >= self.index[c].len() { continue; }
            for &pair_idx in &self.index[c][a] {
                let Some([t1, t2]) = self.triggers[pair_idx] else { continue; };
                let (oc, oa) = if t1 == (c, a) { t2 } else { t1 };
                if oc == c { continue; }   // self-pair guard
                if clause_assignment.get(oc).copied().flatten() == Some(oa) {
                    return true;
                }
            }
        }
        false
    }

    fn registered_pair_count(&self) -> usize { self.pairs.len() }
}

/// Detect a flat Sum-of-Prod-of-Lits matrix (the CNF-complement
/// shape).  The top is `Sum`, each child is either a singleton
/// `Lit` or a `Prod` whose every alt is a `Lit`.
pub fn is_flat_sum_of_prods(nnf: &NNF) -> bool {
    matches!(nnf,
        NNF::Sum(children) if children.iter().all(|c| match c {
            NNF::Lit(_)  => true,
            NNF::Prod(alts) => alts.iter().all(|a| matches!(a, NNF::Lit(_))),
            NNF::Sum(_)  => false,
        })
    )
}

/// Extract `[(i, a), (j, b)]` triggers from a `Pair` whose two
/// `Position`s have flat Sum-of-Prods shape.
///
/// Position `[i, a]` (Lit nested in Sum-child `i`'s Prod alt `a`)
/// → trigger `(i, a)`.  A Lit directly under the Sum (not wrapped
/// in a Prod) has Position `[i]` only — we encode that as alt `0`,
/// matching the DFS engine's behaviour where a singleton Lit
/// occupies the same Prod-path slot.
///
/// Returns `None` for malformed or non-flat positions.
pub(crate) fn flat_pair_triggers(pair: &Pair) -> Option<[(usize, usize); 2]> {
    let extract = |pos: &crate::matrix::Position| -> Option<(usize, usize)> {
        match pos.len() {
            1 => Some((pos[0], 0)),
            2 => Some((pos[0], pos[1])),
            _ => None,
        }
    };
    Some([extract(&pair.0)?, extract(&pair.1)?])
}

/// Cover-search controller — process A's logic.  Owns a heuristic
/// for picking which pair to process next and what "process" means.
pub trait CoverSearchController: Send + 'static {
    type State: CoverState;

    /// Construct the initial cover state.  Phase 2 needs the NNF
    /// here so the state can index pair-positions against the
    /// matrix structure (e.g. flat Sum-of-Prods clause arities).
    fn create_state(&self, nnf: &NNF) -> Self::State;

    /// Index of the next pair the controller wants to register.
    /// Returns `None` to yield (e.g. waiting for B to feed in more
    /// pairs).  The driver re-polls after a short delay or after
    /// new-pair notifications.
    fn next_pair_index(&mut self, pool: &PairPool, state: &Self::State) -> Option<usize>;

    /// Apply pair `pool[idx]` to `state`.  Returns `true` if this
    /// pair contributed coverage (some controllers may discard
    /// redundant pairs).
    fn register_pair(&mut self, idx: usize, pool: &PairPool, state: &mut Self::State) -> bool;

    /// Completeness check.  Returning `true` means the cover state
    /// proves every path is covered → UNSAT.  The driver halts B
    /// when this fires and returns [`Outcome::Unsat`].
    ///
    /// Takes `&mut self` and `&mut state` because expensive checks
    /// (e.g. invoking a SAT solver against a CNF-of-bans encoding)
    /// often need to mutate cached state.  Cheap controllers
    /// (Phase 1-2) just return `false` and rely on B's exhaustion
    /// for termination.
    fn is_complete(&mut self, _state: &mut Self::State) -> bool { false }

    /// Optional: pre-populate the pool with statically-derivable
    /// pairs at startup, before B begins emitting.  Default is
    /// no-op.  The greedy controller overrides to seed the pool
    /// with every cross-clause complementary pair.
    fn seed_pool(&self, _nnf: &NNF, _pool: &PairPool) {}
}

/// Path-search controller — process B's logic.  Phase 1 wraps the
/// existing matrix DFS.  The trait is intentionally minimal: a
/// single `run` that does the search and reports its outcome,
/// emitting pairs into the pool as it goes.
pub trait DualPathSearchController: Send + 'static {
    type State: CoverState;

    /// Run the path search to completion (or cancellation).  Pushes
    /// every covered-pair detection into `pool`.  May consult `state`
    /// for early pruning (Phase 1 implementations don't yet).
    fn run(
        self,
        nnf: &NNF,
        mode: SearchMode,
        pool: Arc<PairPool>,
        state: Arc<Mutex<Self::State>>,
        cancel: Arc<AtomicBool>,
    ) -> PathOutcome;
}

/// Phase 1 driver: spawn A and B on threads, await the first
/// terminating signal, cancel the other.  Sound by construction
/// because B alone is the termination authority in Phase 1 (it
/// detects covers locally and exhausts when every path is closed).
pub fn solve_dual<A, B>(
    nnf: &NNF,
    cover_ctrl: A,
    path_ctrl:  B,
    mode: SearchMode,
) -> Outcome
where
    A: CoverSearchController,
    B: DualPathSearchController<State = A::State>,
{
    let pool   = PairPool::new();
    cover_ctrl.seed_pool(nnf, &pool);
    let state  = Arc::new(Mutex::new(cover_ctrl.create_state(nnf)));
    let cancel_a = Arc::new(AtomicBool::new(false));
    let cancel_b = Arc::new(AtomicBool::new(false));

    // Either side may signal completion via this channel; the
    // driver takes the first message and cancels the other thread.
    let (term_tx, term_rx) = std::sync::mpsc::sync_channel::<TermSignal>(2);

    // Process A: pulls pairs from the pool, registers them, and
    // may signal `CoverComplete` if its `is_complete` check fires.
    let a_handle = {
        let pool   = pool.clone();
        let state  = state.clone();
        let cancel = cancel_a.clone();
        let tx     = term_tx.clone();
        spawn_search_thread("dual.a", move || {
            let outcome = cover_loop(cover_ctrl, &pool, &state, &cancel);
            // Only `CoverComplete` is a useful signal — `Cancelled`
            // means the driver is already shutting us down.
            if matches!(outcome, CoverOutcome::CoverComplete) {
                let _ = tx.send(TermSignal::CoverComplete);
            }
            outcome
        })
    };

    // Process B: walks paths, emits pairs.  Signals via the
    // terminator channel either way (Uncovered → Sat,
    // Exhausted → Unsat).
    let b_handle = {
        let pool    = pool.clone();
        let state   = state.clone();
        let cancel  = cancel_b.clone();
        let nnf     = nnf.clone();
        let tx      = term_tx.clone();
        spawn_search_thread("dual.b", move || {
            let outcome = path_ctrl.run(&nnf, mode, pool, state, cancel);
            // Don't signal on `Cancelled` — that means A already won.
            match &outcome {
                PathOutcome::Uncovered(pp) => {
                    let _ = tx.send(TermSignal::PathUncovered(pp.clone()));
                }
                PathOutcome::Exhausted => {
                    let _ = tx.send(TermSignal::PathExhausted);
                }
                PathOutcome::Cancelled => {}
            }
            outcome
        })
    };

    // Drop the driver's local sender so the channel can close
    // naturally if both threads exit without signalling (shouldn't
    // happen in well-formed runs but be defensive).
    drop(term_tx);

    // Wait for the first signal from either side.
    let signal = term_rx.recv().expect(
        "both cover-search and path-search threads exited without signalling",
    );

    // Tell both sides to wind down.
    cancel_a.store(true, Ordering::SeqCst);
    cancel_b.store(true, Ordering::SeqCst);

    // Reap threads — important so panics propagate and resources free.
    let _a_outcome = a_handle.join().expect("cover-search thread panicked");
    let _b_outcome = b_handle.join().expect("path-search thread panicked");

    match signal {
        TermSignal::PathUncovered(pp) => Outcome::Sat(pp),
        TermSignal::PathExhausted     => Outcome::Unsat,
        TermSignal::CoverComplete     => Outcome::Unsat,
    }
}

/// Like [`solve_dual`] but accepts an external cancellation signal.
/// When `external_cancel` becomes `true`, both A and B are signalled
/// to wind down and `Outcome::Unsat` is returned (caller is
/// expected to consult its own state to distinguish cancel from
/// genuine UNSAT).  Polls `external_cancel` every 5 ms while waiting
/// for one of A/B to signal termination — fast enough that
/// back-to-back UI re-runs (e.g. flipping the backend selector)
/// don't accumulate concurrent in-flight searches, slow enough that
/// the wake cost is negligible.
pub fn solve_dual_with_cancel<A, B>(
    nnf: &NNF,
    cover_ctrl: A,
    path_ctrl:  B,
    mode: SearchMode,
    external_cancel: Arc<AtomicBool>,
) -> Outcome
where
    A: CoverSearchController,
    B: DualPathSearchController<State = A::State>,
{
    let pool   = PairPool::new();
    cover_ctrl.seed_pool(nnf, &pool);
    let state  = Arc::new(Mutex::new(cover_ctrl.create_state(nnf)));
    let cancel_a = Arc::new(AtomicBool::new(false));
    let cancel_b = Arc::new(AtomicBool::new(false));
    let (term_tx, term_rx) = std::sync::mpsc::sync_channel::<TermSignal>(2);

    let a_handle = {
        let pool   = pool.clone();
        let state  = state.clone();
        let cancel = cancel_a.clone();
        let tx     = term_tx.clone();
        spawn_search_thread("dual.a", move || {
            let outcome = cover_loop(cover_ctrl, &pool, &state, &cancel);
            if matches!(outcome, CoverOutcome::CoverComplete) {
                let _ = tx.send(TermSignal::CoverComplete);
            }
            outcome
        })
    };
    let b_handle = {
        let pool    = pool.clone();
        let state   = state.clone();
        let cancel  = cancel_b.clone();
        let nnf     = nnf.clone();
        let tx      = term_tx.clone();
        spawn_search_thread("dual.b", move || {
            let outcome = path_ctrl.run(&nnf, mode, pool, state, cancel);
            match &outcome {
                PathOutcome::Uncovered(pp) => {
                    let _ = tx.send(TermSignal::PathUncovered(pp.clone()));
                }
                PathOutcome::Exhausted => {
                    let _ = tx.send(TermSignal::PathExhausted);
                }
                PathOutcome::Cancelled => {}
            }
            outcome
        })
    };
    drop(term_tx);

    // Poll for a terminator signal while watching the external
    // cancel flag.  recv_timeout returns Err(Disconnected) if all
    // senders dropped without sending — that shouldn't happen in
    // well-formed runs (both threads send on termination) but be
    // defensive.
    use std::sync::mpsc::RecvTimeoutError;
    let mut cancelled = false;
    let signal_opt = loop {
        if external_cancel.load(Ordering::SeqCst) {
            cancelled = true;
            break None;
        }
        match term_rx.recv_timeout(std::time::Duration::from_millis(5)) {
            Ok(sig) => break Some(sig),
            Err(RecvTimeoutError::Timeout) => continue,
            Err(RecvTimeoutError::Disconnected) => break None,
        }
    };
    cancel_a.store(true, Ordering::SeqCst);
    cancel_b.store(true, Ordering::SeqCst);
    let _a_outcome = a_handle.join().expect("cover-search thread panicked");
    let _b_outcome = b_handle.join().expect("path-search thread panicked");

    if cancelled {
        // External cancel — caller decides what to do; we report as
        // Unsat by convention (the cancel handler in the UI sets
        // `running = false` and the snapshot's uncovered_paths is
        // checked separately to decide the verdict).
        return Outcome::Unsat;
    }
    match signal_opt {
        Some(TermSignal::PathUncovered(pp)) => Outcome::Sat(pp),
        Some(TermSignal::PathExhausted)     => Outcome::Unsat,
        Some(TermSignal::CoverComplete)     => Outcome::Unsat,
        None                                => Outcome::Unsat,
    }
}

/// Internal: which side terminated and how.
enum TermSignal {
    /// B found an uncovered path → SAT.
    PathUncovered(ProdPath),
    /// B exhausted without an uncovered path → UNSAT (B's cover
    /// detection did the work).
    PathExhausted,
    /// A's `is_complete` check returned true → UNSAT (A's
    /// cover-state representation proved every path is covered).
    CoverComplete,
}

/// A's main loop: poll for new pairs, register them, check
/// completeness.  Yields briefly when the pool is dry to give B time
/// to produce more.
fn cover_loop<A: CoverSearchController>(
    mut ctrl:  A,
    pool:      &Arc<PairPool>,
    state:     &Arc<Mutex<A::State>>,
    cancel:    &Arc<AtomicBool>,
) -> CoverOutcome {
    loop {
        if cancel.load(Ordering::SeqCst) {
            return CoverOutcome::Cancelled;
        }
        let next = {
            let s = state.lock().unwrap();
            ctrl.next_pair_index(pool, &*s)
        };
        match next {
            Some(idx) => {
                let mut s = state.lock().unwrap();
                ctrl.register_pair(idx, pool, &mut *s);
                if ctrl.is_complete(&mut *s) {
                    return CoverOutcome::CoverComplete;
                }
            }
            None => {
                // No pair to process right now.  Sleep briefly so we
                // don't spin while B is still feeding pairs.  Phase 2
                // can replace this with a condvar / channel signal.
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CoverOutcome {
    /// A determined the cover is complete (UNSAT signal).  Phase 1's
    /// `BasicCoverController` never produces this.
    CoverComplete,
    /// A was cancelled by the driver.  Normal end-of-search in
    /// Phase 1.
    Cancelled,
}

#[cfg(test)]
mod cover_state_positions_tests {
    //! Tests that pin down `BasicCoverState::is_prefix_covered`'s
    //! use of `prefix_positions` (absolute tree addresses) rather
    //! than `prefix_prod_path` (DFS-visit order).  The pre-fix code
    //! indexed `prod_path` directly with clause indices, which was
    //! wrong when (a) the NNF had singleton-Lit Sum-children
    //! (singletons don't push to `prod_path`), or (b) any wrapper
    //! permuted Sum-children via `sum_ord`.  Both produced
    //! spurious "covered" verdicts that pruned satisfiable
    //! subtrees — the soundness bug behind `greedy_eff` returning
    //! wrong UNSAT on SAT problems.
    //!
    //! Tests construct `PathPrefix` (= `Vec<Position>`) values
    //! directly to exercise the query without needing the engine.

    use super::*;
    use crate::matrix::{Lit, NNF, Position};

    fn lit_p(v: u32) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> NNF { NNF::Lit(Lit::neg(v)) }

    /// Position for clause `c`'s alt `a` (multi-alt Prod clause).
    fn pos_alt(c: usize, a: usize) -> Position { vec![c, a] }
    /// Position for a singleton-Lit Sum-child at clause `c`.
    fn pos_single(c: usize) -> Position { vec![c] }

    /// A pair across two multi-alt clauses fires when the prefix
    /// positions show both clauses committed to the trigger alts.
    /// Crucially, this works regardless of the *order* the
    /// positions appear in `prefix_positions` (the engine may have
    /// reordered Sum-children).
    #[test]
    fn cover_query_position_based_lookup() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),     // clause 0
            NNF::Prod(vec![lit_p(2), lit_p(3)]),     // clause 1
            NNF::Prod(vec![lit_p(4), lit_p(5)]),     // clause 2
        ]);
        let mut st = BasicCoverState::new(&nnf);
        // Pair: clause 0 alt 1 + clause 2 alt 0.
        st.add_pair((pos_alt(0, 1), pos_alt(2, 0)));
        // Prefix in declaration order: clause 0 alt 1, clause 2 alt 0.
        assert!(st.is_prefix_covered(&vec![pos_alt(0, 1), pos_alt(2, 0)]));
        // Same content, reversed order — still fires.
        assert!(st.is_prefix_covered(&vec![pos_alt(2, 0), pos_alt(0, 1)]));
        // Wrong alts.
        assert!(!st.is_prefix_covered(&vec![pos_alt(0, 0), pos_alt(2, 0)]));
        assert!(!st.is_prefix_covered(&vec![pos_alt(0, 1), pos_alt(2, 1)]));
        // Only one of the two clauses on the prefix.
        assert!(!st.is_prefix_covered(&vec![pos_alt(0, 1)]));
    }

    /// A pair where one trigger is a singleton-Lit Sum-child.
    /// Singleton positions are length-1 vectors (no alt index);
    /// the query must still match them correctly against pair
    /// triggers that encode singletons as alt 0.
    #[test]
    fn cover_query_handles_singleton_position() {
        let nnf = NNF::Sum(vec![
            lit_p(0),                                // clause 0: singleton
            NNF::Prod(vec![lit_p(1), lit_p(2)]),     // clause 1: arity 2
            lit_p(3),                                // clause 2: singleton
        ]);
        let mut st = BasicCoverState::new(&nnf);
        // Pair: singleton clause 0 + clause 1 alt 1.
        st.add_pair((pos_single(0), pos_alt(1, 1)));
        // Prefix: both lits on the path.
        assert!(st.is_prefix_covered(&vec![pos_single(0), pos_alt(1, 1)]));
        // Prefix: only singleton — clause 1 not yet committed.
        assert!(!st.is_prefix_covered(&vec![pos_single(0)]));
        // Prefix: only clause 1, wrong alt.
        assert!(!st.is_prefix_covered(&vec![pos_alt(1, 0)]));
    }

    /// Pin down the wrong-UNSAT regression.  Before the fix,
    /// `is_prefix_covered` indexed `prefix[i]` as if `i` were the
    /// clause index, so a permuted prefix would either miss covers
    /// or report false ones.  The position-based query is immune.
    ///
    /// Construct a minimal scenario: 3 multi-alt clauses, register
    /// a single pair, then verify that a "permuted" prefix
    /// (positions in a different order than declaration) returns
    /// the same verdict.
    #[test]
    fn cover_query_immune_to_prefix_order() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_p(2), lit_p(3)]),
            NNF::Prod(vec![lit_p(4), lit_p(5)]),
        ]);
        let mut st = BasicCoverState::new(&nnf);
        st.add_pair((pos_alt(1, 1), pos_alt(2, 0)));
        // Declaration-order prefix.
        assert!(st.is_prefix_covered(&vec![pos_alt(0, 0), pos_alt(1, 1), pos_alt(2, 0)]));
        // Same positions, visited in a wrapper-reordered order.
        assert!(st.is_prefix_covered(&vec![pos_alt(2, 0), pos_alt(0, 0), pos_alt(1, 1)]));
        assert!(st.is_prefix_covered(&vec![pos_alt(1, 1), pos_alt(2, 0)]));
        assert!(!st.is_prefix_covered(&vec![pos_alt(0, 0), pos_alt(1, 0), pos_alt(2, 0)]));
    }

    /// All-singletons pair fires on the empty prefix (both lits
    /// are automatically on every complete path).
    #[test]
    fn cover_query_handles_all_singleton_pair() {
        let nnf = NNF::Sum(vec![
            lit_p(0),                                // clause 0: singleton
            NNF::Prod(vec![lit_p(1), lit_p(2)]),     // clause 1: arity 2
            lit_n(0),                                // clause 2: singleton (¬a)
        ]);
        let mut st = BasicCoverState::new(&nnf);
        st.add_pair((pos_single(0), pos_single(2)));
        assert!(st.is_prefix_covered(&vec![]));
        assert!(st.is_prefix_covered(&vec![pos_single(0)]));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    /// Helper: parse a formula and run the dual SAT search.
    fn dual_sat(text: &str) -> Outcome {
        let matrix = crate::matrix::Matrix::try_from(text).expect("matrix");
        // SAT search runs on the formula's complement NNF.
        let nnf = matrix.nnf_complement.clone();
        solve_dual(&nnf,
                   BasicCoverController::default(),
                   BasicDualPathController::default(),
                   SearchMode::Satisfiable)
    }

    /// Helper: existing `Matrix::satisfiable` answer for cross-check.
    fn existing_sat(text: &str) -> bool {
        let matrix = crate::matrix::Matrix::try_from(text).expect("matrix");
        matrix.satisfiable(crate::matrix::smart_controller_builder).is_ok()
    }

    /// Helper: existing `Matrix::valid` answer for cross-check.
    fn existing_valid(text: &str) -> bool {
        let matrix = crate::matrix::Matrix::try_from(text).expect("matrix");
        matrix.valid(crate::matrix::smart_controller_builder).is_ok()
    }

    #[test]
    fn dual_agrees_on_simple_sat_formulas() {
        for text in &[
            "a",
            "a + b",
            "a*b",
            "(a + b)*(a' + c)",
            "a*(b + c)*(a' + b')",
            "(a + b + c)*(a' + b)*(a' + c')",
        ] {
            let dual_outcome = dual_sat(text);
            let existing_is_sat = existing_sat(text);
            let dual_is_sat = matches!(dual_outcome, Outcome::Sat(_));
            assert_eq!(dual_is_sat, existing_is_sat,
                       "disagreement on '{}': dual={:?}, existing.sat={}",
                       text, dual_outcome, existing_is_sat);
        }
    }

    #[test]
    fn dual_agrees_on_simple_unsat_formulas() {
        for text in &[
            "a*a'",
            "(a + b)*(a' + b)*(a + b')*(a' + b')",
        ] {
            let dual_outcome = dual_sat(text);
            let existing_is_sat = existing_sat(text);
            let dual_is_sat = matches!(dual_outcome, Outcome::Sat(_));
            assert_eq!(dual_is_sat, existing_is_sat,
                       "disagreement on '{}': dual={:?}, existing.sat={}",
                       text, dual_outcome, existing_is_sat);
        }
    }

    /// Extended cross-check on a wider variety of formulas to give
    /// the framework a real workout.  Mixes SAT and UNSAT cases and
    /// includes a couple of nested-NNF cases that exercise the
    /// covered-prefix path.
    #[test]
    fn dual_agrees_on_assorted_formulas() {
        for text in &[
            // SAT
            "a + a'",
            "a*b + a*b' + a'*b + a'*b'",
            "(a + b)*(c + d)",
            "(a + b + c)*(b + c + d)*(a + d)",
            "(x + y)*(x' + z)*(y' + z')",
            // UNSAT
            "a*a'*b",
            "(a + b)*(a' + b)*(a + b')*(a' + b')",
            "(a + b)*(a + b')*(a' + b)*(a' + b')*(c + d)",
        ] {
            let dual_outcome = dual_sat(text);
            let existing_is_sat = existing_sat(text);
            let dual_is_sat = matches!(dual_outcome, Outcome::Sat(_));
            assert_eq!(dual_is_sat, existing_is_sat,
                       "disagreement on '{}': dual={:?}, existing.sat={}",
                       text, dual_outcome, existing_is_sat);
        }
    }

    /// Greedy A-controller cross-check: same formulas as
    /// `dual_agrees_on_assorted_formulas`, just with Greedy on the
    /// A side.  Asserts the framework produces the same outcomes
    /// regardless of which cover-search heuristic A uses.
    #[test]
    fn dual_greedy_agrees_on_assorted_formulas() {
        for text in &[
            // SAT
            "a + a'",
            "a + b",
            "a*b + a*b' + a'*b + a'*b'",
            "(a + b)*(c + d)",
            "(a + b + c)*(b + c + d)*(a + d)",
            "(x + y)*(x' + z)*(y' + z')",
            // UNSAT
            "a*a'",
            "a*a'*b",
            "(a + b)*(a' + b)*(a + b')*(a' + b')",
        ] {
            let matrix = crate::matrix::Matrix::try_from(*text).expect("matrix");
            let nnf = matrix.nnf_complement.clone();
            let outcome = solve_dual(
                &nnf,
                GreedyMaxCoverController::default(),
                BasicDualPathController::default(),
                SearchMode::Satisfiable,
            );
            let existing_is_sat = existing_sat(text);
            let dual_is_sat = matches!(outcome, Outcome::Sat(_));
            assert_eq!(dual_is_sat, existing_is_sat,
                       "Greedy disagrees with existing on '{}': dual={:?}, existing.sat={}",
                       text, outcome, existing_is_sat);
        }
    }

    /// CnfBans A-controller cross-check: same formulas as
    /// `dual_agrees_on_assorted_formulas` but with the
    /// CaDiCaL-bans-driven controller on the A side.  Validates
    /// that A's CaDiCaL completeness check produces the same
    /// outcomes as the other configurations across a mix of
    /// SAT and UNSAT formulas.
    #[test]
    fn dual_cnf_bans_agrees_on_assorted_formulas() {
        for text in &[
            // SAT
            "a + a'",
            "a + b",
            "a*b + a*b' + a'*b + a'*b'",
            "(a + b)*(c + d)",
            "(a + b + c)*(b + c + d)*(a + d)",
            "(x + y)*(x' + z)*(y' + z')",
            // UNSAT
            "a*a'",
            "a*a'*b",
            "(a + b)*(a' + b)*(a + b')*(a' + b')",
        ] {
            let matrix = crate::matrix::Matrix::try_from(*text).expect("matrix");
            let nnf = matrix.nnf_complement.clone();
            // Aggressive thresholds so the CaDiCaL path actually
            // fires on these tiny test formulas.
            let cover = CnfBansCoverController::new()
                .with_min_pairs_before_first_check(0)
                .with_check_threshold(1);
            let outcome = solve_dual(
                &nnf,
                cover,
                BasicDualPathController::default(),
                SearchMode::Satisfiable,
            );
            let existing_is_sat = existing_sat(text);
            let dual_is_sat = matches!(outcome, Outcome::Sat(_));
            assert_eq!(dual_is_sat, existing_is_sat,
                       "CnfBans disagrees with existing on '{}': dual={:?}, existing.sat={}",
                       text, outcome, existing_is_sat);
        }
    }

    /// EffectivePathController cross-check.  Validates the
    /// effective-path-count B-side controller against the existing
    /// solver on a mix of SAT/UNSAT formulas, including a few that
    /// exercise the non-flat NNF code path (parens forcing nested
    /// AND/OR structure).
    #[test]
    fn dual_effective_agrees_on_assorted_formulas() {
        for text in &[
            // SAT
            "a + a'",
            "a + b",
            "a*b + a*b' + a'*b + a'*b'",
            "(a + b)*(c + d)",
            "(a + b + c)*(b + c + d)*(a + d)",
            "(x + y)*(x' + z)*(y' + z')",
            "(a + b c)(d + e f)",
            // UNSAT
            "a*a'",
            "a*a'*b",
            "(a + b)*(a' + b)*(a + b')*(a' + b')",
        ] {
            let matrix = crate::matrix::Matrix::try_from(*text).expect("matrix");
            let nnf = matrix.nnf_complement.clone();
            let outcome = solve_dual(
                &nnf,
                BasicCoverController::default(),
                EffectivePathController::default(),
                SearchMode::Satisfiable,
            );
            let existing_is_sat = existing_sat(text);
            let dual_is_sat = matches!(outcome, Outcome::Sat(_));
            assert_eq!(dual_is_sat, existing_is_sat,
                       "EffectivePathController disagrees on '{}': dual={:?}, existing.sat={}",
                       text, outcome, existing_is_sat);
        }
    }

    /// BDD A-controller cross-check.  Validates the BDD-bans
    /// completeness path against a mix of SAT and UNSAT formulas.
    #[test]
    fn dual_bdd_bans_agrees_on_assorted_formulas() {
        for text in &[
            // SAT
            "a + a'",
            "a + b",
            "a*b + a*b' + a'*b + a'*b'",
            "(a + b)*(c + d)",
            "(a + b + c)*(b + c + d)*(a + d)",
            "(x + y)*(x' + z)*(y' + z')",
            // UNSAT
            "a*a'",
            "a*a'*b",
            "(a + b)*(a' + b)*(a + b')*(a' + b')",
        ] {
            let matrix = crate::matrix::Matrix::try_from(*text).expect("matrix");
            let nnf = matrix.nnf_complement.clone();
            let cover = BddBansCoverController::new()
                .with_min_pairs_before_first_check(0)
                .with_check_threshold(1);
            let outcome = solve_dual(
                &nnf,
                cover,
                BasicDualPathController::default(),
                SearchMode::Satisfiable,
            );
            let existing_is_sat = existing_sat(text);
            let dual_is_sat = matches!(outcome, Outcome::Sat(_));
            assert_eq!(dual_is_sat, existing_is_sat,
                       "BddBans disagrees with existing on '{}': dual={:?}, existing.sat={}",
                       text, outcome, existing_is_sat);
        }
    }

    /// State-query benefit: if A pre-registers pairs that cover
    /// regions B hasn't yet visited, B should prune those subtrees
    /// without doing the local detection itself.  We test by
    /// pre-populating the cover state with statically-mined pairs
    /// (via Greedy's seed_pool) and confirming the search still
    /// reaches the right answer.
    ///
    /// (A direct prune-count assertion would require exposing the
    /// `StateQueryWrapper`'s instrumentation through the API; for
    /// Phase 2 we rely on the env-gated stderr printout for that.)
    #[test]
    fn state_query_does_not_break_correctness() {
        // UNSAT formula where mining produces many pairs.
        let text = "(a + b + c)*(a + b' + c)*(a + b + c')*(a + b' + c')\
                   *(a' + b + c)*(a' + b' + c)*(a' + b + c')*(a' + b' + c')";
        let matrix = crate::matrix::Matrix::try_from(text).expect("matrix");
        let nnf = matrix.nnf_complement.clone();
        let outcome = solve_dual(
            &nnf,
            GreedyMaxCoverController::default(),
            BasicDualPathController::default(),
            SearchMode::Satisfiable,
        );
        assert_eq!(outcome, Outcome::Unsat,
                   "8-cube UNSAT in 3 vars should be UNSAT under dual+Greedy");
        assert!(!existing_sat(text));
    }

    /// Cross-product correctness: every (A, B) combination agrees
    /// with the existing single-DFS solver on every formula.  This
    /// is the authoritative Phase 3 check that the framework's
    /// plug-in matrix is sound.
    #[test]
    fn dual_cross_product_agrees_on_assorted_formulas() {
        let formulas: &[&str] = &[
            // SAT
            "a",
            "a + b",
            "a + a'",
            "a*b + a*b' + a'*b + a'*b'",
            "(a + b)*(c + d)",
            "(a + b + c)*(b + c + d)*(a + d)",
            "(x + y)*(x' + z)*(y' + z')",
            // UNSAT
            "a*a'",
            "a*a'*b",
            "(a + b)*(a' + b)*(a + b')*(a' + b')",
            "(a + b + c)*(a + b' + c)*(a + b + c')*(a + b' + c')\
            *(a' + b + c)*(a' + b' + c)*(a' + b + c')*(a' + b' + c')",
        ];

        // Helper: run `solve_dual` with the four (A, B) combinations
        // and assert each agrees with the existing single-DFS
        // controller's verdict.
        fn check<S, A, B>(
            text: &str,
            label: &str,
            ctor_a: impl FnOnce() -> A,
            ctor_b: impl FnOnce() -> B,
            expected_sat: bool,
        )
        where
            S: CoverState,
            A: CoverSearchController<State = S>,
            B: DualPathSearchController<State = S>,
        {
            let matrix = crate::matrix::Matrix::try_from(text).expect("matrix");
            let nnf = matrix.nnf_complement.clone();
            let outcome = solve_dual(&nnf, ctor_a(), ctor_b(),
                                     SearchMode::Satisfiable);
            let dual_is_sat = matches!(outcome, Outcome::Sat(_));
            assert_eq!(dual_is_sat, expected_sat,
                "[{}] dual disagrees on '{}': dual={:?}, expected_sat={}",
                label, text, outcome, expected_sat);
        }

        for text in formulas {
            let expected_sat = existing_sat(text);

            check(text, "Basic A × Basic B",
                  BasicCoverController::default,
                  BasicDualPathController::<BasicCoverState>::default,
                  expected_sat);
            check(text, "Basic A × Smart B",
                  BasicCoverController::default,
                  SmartDualPathController::<BasicCoverState>::default,
                  expected_sat);
            check(text, "Basic A × CDCL B",
                  BasicCoverController::default,
                  CdclDualPathController::<BasicCoverState>::default,
                  expected_sat);
            check(text, "Greedy A × Basic B",
                  GreedyMaxCoverController::default,
                  BasicDualPathController::<BasicCoverState>::default,
                  expected_sat);
            check(text, "Greedy A × Smart B",
                  GreedyMaxCoverController::default,
                  SmartDualPathController::<BasicCoverState>::default,
                  expected_sat);
            check(text, "Greedy A × CDCL B",
                  GreedyMaxCoverController::default,
                  CdclDualPathController::<BasicCoverState>::default,
                  expected_sat);
            // Dynamic-greedy uses BddBansCoverState (its gain query
            // reads `valid_bdd`).  Same B-controllers are generic
            // over the state type, so they instantiate fine here.
            check(text, "GreedyDyn A × Basic B",
                  GreedyDynamicCoverController::default,
                  BasicDualPathController::<BddBansCoverState>::default,
                  expected_sat);
            check(text, "GreedyDyn A × Smart B",
                  GreedyDynamicCoverController::default,
                  SmartDualPathController::<BddBansCoverState>::default,
                  expected_sat);
            check(text, "GreedyDyn A × CDCL B",
                  GreedyDynamicCoverController::default,
                  CdclDualPathController::<BddBansCoverState>::default,
                  expected_sat);
        }
    }

    /// Same as `dual_agrees_on_assorted_formulas` but for validity:
    /// run on the original NNF, an Uncovered outcome means
    /// "not-valid", an exhaustion means "valid".
    #[test]
    fn dual_validity_agrees_on_assorted_formulas() {
        let cases: &[(&str, bool)] = &[
            ("a + a'",                       true),
            ("a*a'",                         false),
            ("(a + a')*(b + b')",            true),
            ("a*b",                          false),
            ("a + b",                        false),
        ];
        for (text, expected_valid) in cases {
            let matrix = crate::matrix::Matrix::try_from(*text).expect("matrix");
            let nnf = matrix.nnf.clone();
            let outcome = solve_dual(
                &nnf,
                BasicCoverController::default(),
                BasicDualPathController::default(),
                SearchMode::Validity,
            );
            let dual_says_valid = matches!(outcome, Outcome::Unsat);
            let existing_says_valid = existing_valid(text);
            assert_eq!(dual_says_valid, *expected_valid,
                       "dual disagrees with expectation on '{}': dual.valid={}, expected={}",
                       text, dual_says_valid, expected_valid);
            assert_eq!(dual_says_valid, existing_says_valid,
                       "dual disagrees with existing on '{}': dual.valid={}, existing.valid={}",
                       text, dual_says_valid, existing_says_valid);
        }
    }

    #[test]
    fn pair_pool_threading() {
        // Smoke test: producers + consumers can drive PairPool
        // safely concurrently.
        use crate::matrix::Position;
        let pool = PairPool::new();
        let n_producers = 4;
        let per_producer = 50;
        let mut handles = Vec::new();
        for p in 0..n_producers {
            let pool = pool.clone();
            handles.push(std::thread::spawn(move || {
                for i in 0..per_producer {
                    let p1: Position = vec![p, i];
                    let p2: Position = vec![p, i + 1];
                    pool.push((p1, p2));
                }
            }));
        }
        for h in handles { h.join().unwrap(); }
        assert_eq!(pool.len(), n_producers * per_producer);
    }

    #[test]
    fn validity_mode_smoke() {
        // `a + a'` is valid; dual should report Unsat (no falsifying
        // path) when run in Validity mode.
        let text = "a + a'";
        let matrix = crate::matrix::Matrix::try_from(text).expect("matrix");
        // For VALID mode we search the formula directly.
        let nnf = matrix.nnf.clone();
        let outcome = solve_dual(
            &nnf,
            BasicCoverController::default(),
            BasicDualPathController::default(),
            SearchMode::Validity,
        );
        assert_eq!(outcome, Outcome::Unsat);
        assert!(existing_valid(text));
    }
}
