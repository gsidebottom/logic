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
pub mod cover_state_bdd;
pub mod cover_state_cnf;
pub mod flat;
pub mod path_basic;
pub mod path_smart;
pub mod path_cdcl;
pub mod wrapper;

#[cfg(test)]
mod bench;

pub use cover_basic::BasicCoverController;
pub use cover_bdd_bans::BddBansCoverController;
pub use cover_cnf_bans::CnfBansCoverController;
pub use cover_greedy::GreedyMaxCoverController;
pub use cover_state_bdd::BddBansCoverState;
pub use cover_state_cnf::CnfBansCoverState;
pub use path_basic::BasicDualPathController;
pub use path_cdcl::CdclDualPathController;
pub use path_smart::SmartDualPathController;

use crate::matrix::{NNF, Pair, ProdPath};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};

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
    /// Is the path identified by this `ProdPath` already covered by
    /// some pair we've registered?  Phase 1's basic state can return
    /// `false` always (it leaves cover detection to B's local
    /// controller); future phases will use this to prune B early.
    fn is_prefix_covered(&self, prefix: &ProdPath) -> bool;

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
    /// entry `[(i, a), (j, b)]` says "pair fires when prefix[i]==a
    /// and prefix[j]==b".  `None` means triggers couldn't be
    /// derived (non-flat NNF or malformed pair).
    triggers: Vec<Option<[(usize, usize); 2]>>,
    /// Whether the source NNF is flat Sum-of-Prods.  When false,
    /// `is_prefix_covered` short-circuits to `false`.
    is_flat: bool,
    /// Clause arities for the source NNF when flat; empty
    /// otherwise.
    arities: Vec<usize>,
    /// **Phase 4 bucket index.**  `index[clause_idx][alt_idx]` is
    /// the list of pair-IDs whose triggers include
    /// `(clause_idx, alt_idx)`.  Built lazily as pairs are
    /// registered.  Empty in non-flat mode.
    index: Vec<Vec<Vec<usize>>>,
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
        }
        self.pairs.push(pair);
        self.triggers.push(triggers);
    }

    pub fn pairs(&self) -> &[Pair] { &self.pairs }

    pub fn is_flat(&self) -> bool { self.is_flat }
}

impl CoverState for BasicCoverState {
    /// Phase 4 indexed lookup.  Walks the prefix and, for each
    /// `(clause_idx, alt_idx)` entry, consults the bucket index for
    /// pairs that fire on that trigger; checks whether their *other*
    /// trigger is also satisfied by the prefix.  Total work
    /// O(|prefix| × avg pairs per bucket), vs the naive
    /// O(|registered pairs|) full scan.
    fn is_prefix_covered(&self, prefix: &ProdPath) -> bool {
        if !self.is_flat { return false; }
        for (i, &a) in prefix.iter().enumerate() {
            // Prefix entry may be out of range when the DFS is
            // exploring beyond the matrix's clause count — happens
            // for non-flat sub-NNFs that snuck past the flat check
            // (shouldn't, but be defensive).
            if i >= self.index.len() { continue; }
            if a >= self.index[i].len() { continue; }
            for &pair_idx in &self.index[i][a] {
                let Some([t1, t2]) = self.triggers[pair_idx] else { continue; };
                // We know one trigger matches (i, a); the *other* is
                // whichever isn't (i, a).
                let (oi, oa) = if t1 == (i, a) { t2 } else { t1 };
                if oi == i { continue; }   // self-pair guard
                if prefix.len() > oi && prefix[oi] == oa {
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
        std::thread::spawn(move || {
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
        std::thread::spawn(move || {
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
        fn check<A, B>(
            text: &str,
            label: &str,
            ctor_a: impl FnOnce() -> A,
            ctor_b: impl FnOnce() -> B,
            expected_sat: bool,
        )
        where
            A: CoverSearchController<State = BasicCoverState>,
            B: DualPathSearchController<State = BasicCoverState>,
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
