//! [`CdclController`] — matrix-CDCL search controller.
//!
//! Conflict-Driven Clause Learning controller built on top of the
//! matrix-method DFS.  Built up in steps so each piece is verifiable in
//! isolation.
//!
//! ## Roadmap
//!
//! - **Step 1**: scaffolding + per-pushed-lit trail + conflict counting.
//! - **Step 2**: reason tracking on the trail (Decision / SumForced).
//! - **Step 3** (this commit): cross-clause unit propagation.
//!   Watched-literal scheme ported from
//!   [`crate::controller::SmartController`], plus an `Implied(clause_id)`
//!   reason variant so propagated lits land in the trail with a back-
//!   pointer to the clause that forced them.  This is the foundation
//!   the implication-graph walker in Step 4 builds on.
//! - **Step 4**: 1UIP conflict analysis to derive a *learned clause*.
//! - **Step 5** (this commit): register learned clauses with the
//!   propagation watch lists.  Each derived clause gets a fresh
//!   `clause_id` and is treated identically to original cubes
//!   thereafter — its alts get watch-list entries, its blockings
//!   participate in cascade propagation.  Initial state (every alt's
//!   complement is on the trail by construction at derivation time) is
//!   recorded against the appropriate push-frames so backtrack undoes
//!   the blockings correctly as those trail lits get popped.
//! - **Step 6**: non-chronological backjumping via the existing
//!   `Option<usize>` return value.  After a cascade conflict triggers
//!   1UIP analysis (Step 4) and the learned clause is wired into the
//!   watch lists (Step 5), we return `Some(1)` instead of `Some(0)`
//!   — the matrix-method analog of CDCL's backjump.  In our
//!   Sum-of-Prods CNF-complement structure, `Some(1)` escapes the
//!   current Prod's alt loop entirely and continues with the previous
//!   Prod's next alternative; the newly-active learned clause then
//!   drives propagation as the search re-descends.  Chronological
//!   `Some(0)` is still used for path-level conflicts (where we don't
//!   have a learned clause to justify the more aggressive jump).
//! - **LBD-based learned-clause deletion**: each learned clause is
//!   tagged with its Literal Block Distance — the count of distinct
//!   decision levels among its alts.  At restart time, when the
//!   live-learned-clause count exceeds `learned_clause_limit`, we
//!   mark the high-LBD half of the learned clauses as deleted (a
//!   tombstone bit in `clause_deleted`) and compact watch lists so
//!   subsequent propagation doesn't walk them.  Doing this at
//!   restart time is convenient because the trail is about to be
//!   cleared anyway, so there are no live `Reason::Implied(...)`
//!   references to deleted clauses to worry about.  Original
//!   (preprocessed) clauses are never deleted.
//!
//!   Tuning note: the default limit is 100000.  Lower limits
//!   (2000-50000) regressed PHP-12-11 / PHP-14-13 noticeably —
//!   the matrix-method search loses propagation power that would
//!   otherwise short-circuit the path tree, and the cost of the
//!   reduction itself (watch-list compaction) doesn't pay back.
//!   The current default is effectively a safety bound for
//!   runaway searches; the heuristic infrastructure is in place,
//!   but the policy could use further tuning.
//! - **Phase saving**: when a variable is popped from the trail
//!   (during backtrack or restart) we remember the polarity it had.
//!   In `prod_ord`, after VSIDS sorting, we tiebreak by preferring
//!   alts whose polarity matches the saved phase for their variable
//!   — so when revisiting a Prod the search re-tries the polarity
//!   that was previously productive.  Especially useful after
//!   restarts: the saved phases capture "what worked before" while
//!   the trail is wiped.
//! - **VSIDS**: variable-ordering heuristic.  Each
//!   variable has an *activity* score that's bumped every time it's
//!   in a learned clause's alts, then decayed (relatively) by
//!   inflating the bump value over time.  In `prod_ord`, after the
//!   propagation-driven filter runs, surviving alts are sorted by
//!   descending activity — most-recently-conflicted variables are
//!   tried first.  This focuses search on the active "frontier" the
//!   way mainstream CDCL solvers do.
//! - **Quality-of-life** (later): VSIDS, restarts, LBD-based deletion.

use std::collections::HashMap;

use crate::controller::PathSearchController;
use crate::controller::backtrack::BacktrackWhenCoveredController;
use crate::matrix::{Lit, NNF, PathParams, PathPrefix, PathsClass, ProdPath, Var};

/// CDCL search controller, in development.  Wraps a
/// [`BacktrackWhenCoveredController`] for cover-aware DFS pruning and
/// adds:
///
/// - A *reasoned trail*: every fact known at the current point in the
///   search (decision lits, Sum-forced lits, propagation-implied lits),
///   each annotated with `(reason, decision_level)`.
/// - *Cross-clause unit propagation*: at each Prod-of-Lits "clause
///   complement" we maintain a blocked-alternatives count via watched
///   lists, and when only one alt remains we add the corresponding lit
///   to the trail as `Implied(clause_id)`.
/// - *1UIP conflict analysis* (Step 4): when a conflict fires we walk
///   the implication graph backwards through `Reason::Implied`
///   chains until one lit at the conflict's decision level remains,
///   and produce a [`LearnedClause`] capturing the result.  Storage
///   only at this stage — Step 5 wires learned clauses into the
///   propagation watch lists and Step 6 uses the backjump level.
///
/// Currently behaves identically to a plain `SmartController` in terms
/// of search outcomes — the trail's reason annotations and learned
/// clauses are observational at this stage.
pub struct CdclController<F: FnMut(PathsClass, bool) -> bool = fn(PathsClass, bool) -> bool> {
    inner: BacktrackWhenCoveredController<F>,

    // ── Reasoned trail (the "fact list") ──
    /// Every lit known at the current point in the search, in the order
    /// it was learned.  Includes both DFS-pushed lits (Decision,
    /// SumForced) and propagation-implied lits (Implied(clause_id)).
    trail: Vec<TrailLit>,

    /// Number of complementary-pair detections observed during the
    /// search.  Includes both inner-controller covered-prefix events
    /// and propagation-cascade conflicts.
    conflict_count: usize,

    /// Snapshot of `prefix_prod_path.len()` at the most recent DFS lit
    /// push.  Lets us tell whether the next lit-push was preceded by a
    /// Prod entry (Decision) or just another Sum-child visit
    /// (SumForced).
    last_path_len_at_lit_push: usize,

    // ── Propagation infrastructure (port from SmartController) ──
    //
    // For every Prod-of-Lits "clause complement" with Sum-only
    // ancestors, we store its alternatives, a count of how many are
    // blocked by lits committed to the path, and a per-alt blocked
    // bitmap to dedup.  Watch lists drive the propagation cascade.
    prod_alts:        Vec<Vec<Lit>>,    // per clause_id: clones of Lit children
    prod_total:       Vec<usize>,       // per clause_id: total alternatives
    prod_blocked:     Vec<usize>,       // per clause_id: # blocked alts
    prod_alt_blocked: Vec<Vec<bool>>,   // per clause_id: which alts are blocked
    /// `var*2 + neg` lit_idx → list of `(clause_id, alt_idx)` entries.
    /// Pushing a lit with this lit_idx blocks each listed alternative.
    watches:          Vec<Vec<(usize, usize)>>,
    /// `var*2 + neg` lit_idx → count of times propagation has
    /// implied this lit (multiple clauses can each imply the same lit
    /// in a single cascade).  >0 means the lit is currently implied.
    implied_lit_counter: Vec<u32>,

    /// One frame per DFS lit pushed onto the path; records everything
    /// the cascade did so we can undo on backtrack.
    push_frames:     Vec<PushFrame>,
    /// Mirror of `prefix_literals.len()` from the previous controller
    /// call — lets us notice push/pop diffs cheaply.
    our_counted_len: usize,

    /// Learned clauses derived by 1UIP analysis, in the order they
    /// were derived.  Step 5 will move learned clauses into a
    /// permanent collection registered with the propagation watch
    /// lists; for now we just keep them around for tests / observation.
    learned_clauses: Vec<LearnedClause>,

    // ── VSIDS variable-ordering heuristic ──
    //
    // `var_activity[v]` is the running activity score for variable v.
    // When a learned clause is derived, every variable in its alts
    // gets `bump_value` added to its activity.  The global bump value
    // grows over time (multiplied by `1 / decay_factor` after each
    // conflict), which is mathematically equivalent to multiplying
    // every existing activity by `decay_factor` — but only mutates
    // one number per conflict instead of the whole vector.  When any
    // activity exceeds 1e100 we re-normalize (divide everything by
    // 1e100) to avoid f64 overflow.
    var_activity: Vec<f64>,
    bump_value:   f64,
    decay_factor: f64,

    // ── Phase saving ──
    //
    // `saved_phase[v] = Some(neg)` means variable `v` was last
    // assigned with polarity `neg` — i.e., the literal `Lit { var: v,
    // neg }` was on the trail at some point and got popped.  The next
    // time `prod_ord` has to break ties between alts of equal VSIDS
    // activity, alts whose polarity matches the saved phase win.
    // None means "never assigned".
    saved_phase: Vec<Option<bool>>,

    // ── LBD-based learned-clause deletion ──
    //
    // `clause_deleted[id] = true` means clause `id` has been pruned
    // from the live propagation set.  `process_push` skips deleted
    // clauses' watch entries; the storage stays around (we don't
    // compact `prod_alts` etc.) so existing `clause_id`s and the
    // `Reason::Implied(clause_id)` back-pointers remain valid.
    //
    // Reduction is triggered from `complete_restart()` when
    // `learned_clauses.len() > learned_clause_limit`; we mark the
    // top-LBD half of the live-learned set as deleted.  Original
    // (preprocessed) clauses are never deleted.
    clause_deleted: Vec<bool>,
    /// Above this many live learned clauses, the next restart triggers
    /// LBD-based reduction.  Default 2000 (MiniSAT-style initial cap).
    learned_clause_limit: usize,
    /// Number of original (preprocessed) clauses, recorded after
    /// `preprocess`.  Indexes >= this are learned clauses.
    initial_clause_count: usize,

    // ── Luby restart schedule ──
    //
    // After each cascade conflict we increment
    // `conflicts_since_last_restart`; when it reaches
    // `restart_threshold = restart_unit * luby(restart_count)`, we set
    // `restart_pending = true` and return `Some(usize::MAX)` from the
    // current `should_continue_on_prefix` call, which unwinds the
    // entire DFS.  The driver then calls `complete_restart()` and
    // re-invokes the engine.  The Luby sequence
    //   1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 8, 16, …
    // gives geometric backoff so that after enough restarts even an
    // UNSAT formula's full DFS fits within one allowance, breaking
    // any restart loop.
    restart_pending:               bool,
    conflicts_since_last_restart:  usize,
    restart_threshold:             usize,
    restart_count:                 usize,
    /// Multiplier on the Luby sequence: each restart's threshold is
    /// `restart_unit * luby(restart_count + 1)` conflicts.  Higher
    /// values mean less-frequent restarts; default 100 matches
    /// MiniSAT-style tuning.
    restart_unit:                  usize,
}

/// Luby's restart sequence (1-indexed).
///
/// Returns the i-th term of `1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2,
/// 4, 8, 1, 1, …` — Luby et al.'s provably-optimal-in-expectation
/// restart schedule for non-deterministic search.  Computed
/// iteratively in O(log i) time.
fn luby(mut i: usize) -> usize {
    debug_assert!(i >= 1, "Luby sequence is 1-indexed");
    loop {
        // Find the smallest k where 2^k - 1 >= i.
        let mut k = 1;
        while (1usize << k) - 1 < i {
            k += 1;
        }
        if i == (1usize << k) - 1 {
            return 1usize << (k - 1);
        }
        // Otherwise, recurse on i - 2^(k-1) + 1.
        i = i - (1usize << (k - 1)) + 1;
    }
}

/// Result of 1UIP conflict analysis: the new clause to add, plus the
/// non-chronological backjump level.
///
/// Semantically, the learned clause is a Prod-of-Lits cube to be
/// added to the top-level Sum of the complement NNF.  Its presence
/// forces every future path to include at least one of its lits —
/// which prevents the conflict from recurring.  The `backjump_level`
/// is the second-highest decision level among the cube's lits;
/// after backjumping there, propagation alone will derive the
/// remaining UIP lit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LearnedClause {
    /// The cube's literal alternatives.  A path satisfying the
    /// learned clause must have at least one of these on it.
    pub alts: Vec<Lit>,
    /// Decision level to backjump to.  Always `< conflict_level`,
    /// usually the second-highest level represented in `alts`.
    /// Step 6 uses this to drive non-chronological backjump.
    pub backjump_level: usize,
    /// Literal Block Distance: number of distinct decision levels
    /// among the lits in the original learning set (the lits whose
    /// negations form `alts`).  Lower LBD = the clause crosses fewer
    /// decision frontiers = more likely to fire propagation early =
    /// more valuable to keep.  Used by the periodic reducer to rank
    /// learned clauses for deletion.
    pub lbd: usize,
}

/// Why a lit ended up on the trail.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reason {
    /// Pushed because a `Prod` chose this `Lit` as its alternative.
    /// In a CNF-complement search this is the typical case: each
    /// clause-complement Prod picks one literal.
    Decision,
    /// Pushed as a direct `Lit` child of a `Sum` (visit-all forces it
    /// onto the path with no choice involved).  In a CNF-complement
    /// search this happens for unit-clause complements that appear as
    /// direct top-level Sum children.
    SumForced,
    /// Forced by unit propagation: every other alt of clause
    /// `clause_id` has been blocked by lits already on the path /
    /// already implied, so this lit is the only remaining choice.
    /// The `clause_id` is an index into `CdclController::prod_alts` —
    /// it's the back-pointer Step 4's 1UIP analysis follows when
    /// building the implication graph.
    Implied(usize),
}

#[derive(Clone, Debug)]
struct TrailLit {
    lit: Lit,
    reason: Reason,
    /// Decision level at the time this lit was added to the trail.
    /// = `prefix_prod_path.len()` at the push that triggered it
    /// (Decision/SumForced lits) or the cascade that implied it
    /// (Implied lits).
    decision_level: usize,
}

#[derive(Default)]
struct PushFrame {
    /// Number of `trail` entries this push (DFS push + propagation
    /// cascade) added.  On undo, pop this many from the trail.
    trail_added: usize,
    /// `(clause_id, alt_idx)` pairs marked blocked during this push's
    /// cascade.  Each one decrements `prod_blocked[clause_id]` on
    /// undo.
    blocked: Vec<(usize, usize)>,
    /// `lit_idx` (= `var*2+neg`) values whose `implied_lit_counter`
    /// this push incremented.  Each decrements on undo.
    implied: Vec<usize>,
}

impl<F: FnMut(PathsClass, bool) -> bool> CdclController<F> {
    /// Build a CdclController and pre-process `nnf` so cross-clause
    /// unit propagation is active during the search.  Pass the same
    /// NNF the controller will be driven over (the original for
    /// validity, the complement for satisfiability).
    pub fn for_nnf(nnf: &NNF, params: Option<PathParams>, on_class: F) -> Self {
        let mut s = <Self as PathSearchController>::with_on_class_uncovered_only(params, on_class);
        s.preprocess(nnf);
        s
    }

    /// Number of conflicts observed during this search so far.
    pub fn conflict_count(&self) -> usize { self.conflict_count }

    /// Snapshot of the current trail as `(lit, reason, decision_level)`
    /// triples.  Exposed for tests / introspection.
    pub fn trail_snapshot(&self) -> Vec<(Lit, Reason, usize)> {
        self.trail.iter()
            .map(|t| (t.lit.clone(), t.reason, t.decision_level))
            .collect()
    }

    /// Number of indexed clauses (Prod-of-Lits with Sum-only ancestors)
    /// found during preprocessing.  Useful as a sanity check that the
    /// formula's structure was understood by the controller.
    pub fn clause_count(&self) -> usize { self.prod_alts.len() }

    /// All learned clauses derived during this search so far, in the
    /// order they were derived.
    pub fn learned_clauses(&self) -> &[LearnedClause] { &self.learned_clauses }

    /// Most recent learned clause, if any.  Convenience accessor for
    /// tests.
    pub fn last_learned_clause(&self) -> Option<&LearnedClause> {
        self.learned_clauses.last()
    }

    /// 1UIP conflict analysis.  Given the id of a clause that became
    /// fully blocked (or that tried to imply a lit whose complement
    /// was already true), walk back through the implication graph by
    /// repeatedly resolving the most-recent trail lit in the learning
    /// set against its `Reason::Implied(rid)` clause.  Stop when
    /// exactly one lit at the conflict level remains.  The negations
    /// of the resulting lit set form the learned clause.
    fn analyze_conflict(&self, conflict_clause_id: usize) -> LearnedClause {
        // Initial learning set: lits-on-trail that block every alt of
        // the conflicting clause.  Each blocked alt `a` has its
        // complement `¬a` true on the trail, which is what blocks it.
        // So learning = { ¬a : a is an alt of the conflict clause }.
        let mut learning: HashMap<Lit, usize> = HashMap::new();
        for alt in &self.prod_alts[conflict_clause_id] {
            let lit = alt.complement();
            let level = self.find_level(&lit);
            learning.insert(lit, level);
        }

        let conflict_level = learning.values().copied().max().unwrap_or(0);

        // Resolve while > 1 lit at conflict_level.  Each iteration
        // picks the most-recent trail lit `p` in `learning` at
        // conflict_level; if `p` was Implied by some clause `R`, we
        // remove `p` from learning and add `¬r` for every other alt
        // `r` of `R`.  This is the resolution rule applied at the
        // implication graph level.
        loop {
            let count_at_top = learning.values().filter(|&&l| l == conflict_level).count();
            if count_at_top <= 1 { break; }

            // Find most-recent trail lit in learning at conflict_level.
            let pick: Option<&TrailLit> = self.trail.iter().rev()
                .find(|t| t.decision_level == conflict_level && learning.contains_key(&t.lit));

            let Some(pick) = pick else { break; };

            match pick.reason {
                Reason::Implied(rid) => {
                    let pick_lit = pick.lit.clone();
                    learning.remove(&pick_lit);
                    // Snapshot the alts so we don't borrow self while
                    // mutating learning.
                    let alts: Vec<Lit> = self.prod_alts[rid].clone();
                    for r_alt in alts {
                        if r_alt != pick_lit {
                            let new_lit = r_alt.complement();
                            let level = self.find_level(&new_lit);
                            // Use entry().or_insert: same lit at same
                            // level shouldn't be inserted twice.
                            learning.entry(new_lit).or_insert(level);
                        }
                    }
                }
                _ => {
                    // Hit a Decision or SumForced lit at conflict_level.
                    // It's fixed — we can't resolve through it.  This
                    // is the UIP if it's the only one at conflict_level,
                    // which the loop's break-condition handles, but if
                    // there are still multiple at conflict_level here,
                    // it means the conflict involves multiple
                    // Decisions/SumForceds at the same level (rare in
                    // CNF-complement search; possible with structural
                    // SumForceds).  Stop and accept the current set.
                    break;
                }
            }
        }

        // Negations of the learning-set lits → cube alts of the
        // learned clause.  A future path containing all the
        // *original* learning lits would re-trigger this conflict;
        // by adding a cube whose alts are their negations, we force
        // the path to include at least one negation, breaking the
        // conflict.
        let alts: Vec<Lit> = learning.keys().map(|l| l.complement()).collect();

        // Backjump level: highest level *strictly below* conflict_level
        // among the learning lits.  After backjumping there, the UIP
        // lit becomes the only conflict-level lit blocked → propagation
        // can re-derive it via the learned clause.
        let backjump_level = learning.values()
            .copied()
            .filter(|&l| l < conflict_level)
            .max()
            .unwrap_or(0);

        // LBD = count of distinct decision levels among the learning
        // set's lits.  Note that `learning.values()` collects *every*
        // lit's level (including the UIP at conflict_level), so an LBD
        // of 1 means "all lits at the same decision level" — extreme
        // glue / very valuable.
        let unique_levels: std::collections::HashSet<usize> =
            learning.values().copied().collect();
        let lbd = unique_levels.len();

        LearnedClause { alts, backjump_level, lbd }
    }

    /// VSIDS: bump variable `var`'s activity by the current
    /// `bump_value`.  Re-normalizes activities + bump_value when the
    /// scores get unwieldy.
    fn bump_var_activity(&mut self, var: Var) {
        let idx = var as usize;
        if idx >= self.var_activity.len() {
            self.var_activity.resize(idx + 1, 0.0);
        }
        self.var_activity[idx] += self.bump_value;
        // Re-normalize when any activity gets too large to avoid
        // f64 inf/overflow.  Dividing every activity (and the bump
        // value) by the same factor preserves the relative ordering.
        if self.var_activity[idx] > 1e100 {
            for a in &mut self.var_activity {
                *a *= 1e-100;
            }
            self.bump_value *= 1e-100;
        }
    }

    /// VSIDS: decay all activities by inflating the bump value.
    /// Equivalent to multiplying every existing activity by
    /// `decay_factor`, but cheaper.
    fn decay_var_activities(&mut self) {
        self.bump_value /= self.decay_factor;
    }

    /// VSIDS: variable activity lookup, defaulting to 0.0 if the
    /// variable hasn't been seen yet.
    fn var_activity(&self, var: Var) -> f64 {
        self.var_activity.get(var as usize).copied().unwrap_or(0.0)
    }

    /// Number of learned clauses currently considered live (not
    /// LBD-deleted).  Useful as a sanity check / progress indicator.
    pub fn live_learned_clause_count(&self) -> usize {
        (self.initial_clause_count..self.prod_alts.len())
            .filter(|&id| !self.clause_deleted[id])
            .count()
    }

    /// LBD-based learned-clause reduction.  Mark the high-LBD half of
    /// the live learned clauses as deleted (their watch entries get
    /// skipped in `process_push` going forward).  Original (preprocessed)
    /// clauses are never deleted, only learned ones.
    ///
    /// **Caller invariant**: this is safe to call only when no trail
    /// entry has `Reason::Implied(deleted_id)` for any clause we're
    /// about to delete.  In practice we only call it from
    /// `complete_restart()`, where the trail is about to be cleared
    /// anyway, so the invariant is trivially satisfied.
    fn reduce_learned_clauses(&mut self) {
        // Collect (clause_id, lbd) for live learned clauses.
        let mut live: Vec<(usize, usize)> = (self.initial_clause_count..self.prod_alts.len())
            .filter(|&id| !self.clause_deleted[id])
            .map(|id| {
                let learned_idx = id - self.initial_clause_count;
                let lbd = self.learned_clauses
                    .get(learned_idx)
                    .map(|lc| lc.lbd)
                    .unwrap_or(0);
                (id, lbd)
            })
            .collect();
        if live.is_empty() { return; }

        // Sort by LBD ascending (low first = keep first).
        live.sort_by_key(|&(_, lbd)| lbd);

        // Delete the top-LBD half.  Keep the lower half, which has
        // the highest "glue" / longest expected propagation reach.
        let to_delete = live.len() / 2;
        for &(clause_id, _lbd) in live.iter().rev().take(to_delete) {
            self.clause_deleted[clause_id] = true;
            // Reset blocking state for the deleted clause, in case
            // the search re-uses these slots after some other
            // reduction.  (Not strictly necessary since we'll skip
            // the clause via `clause_deleted`, but tidies up.)
            self.prod_blocked[clause_id] = 0;
            for b in &mut self.prod_alt_blocked[clause_id] {
                *b = false;
            }
        }

        // Compact watch lists: remove entries for deleted clauses so
        // `process_push` doesn't walk through them on every push.
        // Without this compaction the early-skip on `clause_deleted`
        // is fast per-entry but the Luby schedule grows the
        // between-restart window faster than the reducer can halve
        // the count, and watch lists fill up with stale entries —
        // PHP-12-11 timed at ~19s without compaction vs. ~1s with.
        let deleted = &self.clause_deleted;
        for w in &mut self.watches {
            w.retain(|&(clause_id, _)| !deleted[clause_id]);
        }
    }

    /// Phase saving: record the polarity of `lit` against its
    /// variable.  Called from `undo()` and `complete_restart()` —
    /// every trail entry being popped contributes its polarity.
    fn save_lit_phase(&mut self, lit: &Lit) {
        let v = lit.var as usize;
        if v >= self.saved_phase.len() {
            self.saved_phase.resize(v + 1, None);
        }
        self.saved_phase[v] = Some(lit.neg);
    }

    /// Phase saving: does `lit`'s polarity match the saved phase for
    /// its variable?  Returns `false` when the variable has no saved
    /// phase yet — phase saving is only a tiebreaker, so the search's
    /// first descent uses VSIDS / declaration order untouched.
    fn phase_matches(&self, lit: &Lit) -> bool {
        self.saved_phase.get(lit.var as usize)
            .copied()
            .flatten()
            .map_or(false, |saved| saved == lit.neg)
    }

    /// Look up the decision level of `lit` on the trail.  If multiple
    /// trail entries share the same lit (e.g. an Implied lit later
    /// re-pushed as a Decision), return the *earliest* level — that's
    /// the level at which this fact was first established.
    fn find_level(&self, lit: &Lit) -> usize {
        self.trail.iter()
            .find(|t| t.lit == *lit)
            .map(|t| t.decision_level)
            .unwrap_or(0)
    }

    /// Add a 1UIP-derived clause to the controller's propagation
    /// machinery: index it in [`Self::watches`], append it to
    /// [`Self::prod_alts`] / [`Self::prod_total`] /
    /// [`Self::prod_blocked`] / [`Self::prod_alt_blocked`], and record
    /// its initial blockings against the push-frames responsible for
    /// the lits currently blocking each alt.
    ///
    /// Returns the freshly-assigned `clause_id`.
    ///
    /// Initial state: by construction of 1UIP, every alt's complement
    /// is currently true on the trail (the alts are negations of the
    /// learning set, which are precisely the trail lits that drove the
    /// conflict).  So immediately after registration the clause is
    /// fully blocked.  As the DFS backtracks (whether chronological in
    /// Step 5 or non-chronological after Step 6), each frame pop
    /// undoes the blockings it owns, and the learned clause's state
    /// tracks the trail correctly without further bookkeeping.
    ///
    /// `current_frame` is the in-progress frame for the push that
    /// triggered the conflict.  Lits added by *this* push (the DFS
    /// lit + its propagation cascade) live at the trail tail and have
    /// no entry yet in [`Self::push_frames`]; their blockings must
    /// route to `current_frame` rather than to an existing frame.
    fn register_learned_clause(
        &mut self,
        learned: &LearnedClause,
        current_frame: &mut PushFrame,
    ) -> usize {
        let clause_id = self.prod_alts.len();
        let alts: Vec<Lit> = learned.alts.clone();

        // Insert into watches.  An alt being pushed onto the trail
        // is detected via watches[alt.lit_idx ^ 1] (i.e. someone
        // pushed the alt's complement); but we register at
        // watches[alt.lit_idx] so future pushes of the alt's
        // complement find this clause via the standard process_push
        // path.  Wait — let's be precise:
        //
        //   process_push(lit) walks watches[comp_of_lit] looking for
        //   `(clause, alt_idx)` entries to block.  That means
        //   watches[X] holds entries `(clause, alt_idx)` where the
        //   *alt's lit_idx* is X.  So we insert into
        //   watches[alt.lit_idx], and when someone pushes a lit `l`
        //   such that `l.complement().lit_idx == alt.lit_idx` (i.e.
        //   `l == alt.complement()`), the block fires.
        for (alt_idx, lit) in alts.iter().enumerate() {
            let lit_idx = (lit.var as usize) * 2 + (lit.neg as usize);
            if lit_idx >= self.watches.len() {
                self.watches.resize(lit_idx + 1, Vec::new());
                self.implied_lit_counter.resize(lit_idx + 1, 0);
            }
            self.watches[lit_idx].push((clause_id, alt_idx));
        }

        self.prod_total.push(alts.len());
        self.prod_blocked.push(0);
        self.prod_alt_blocked.push(vec![false; alts.len()]);
        self.prod_alts.push(alts.clone());
        // The new clause is live by default — only the LBD reducer
        // turns it off.
        self.clause_deleted.push(false);

        // Walk the trail to find which entry blocks each alt and
        // attribute the blocking to the correct frame.  This is
        // O(trail × alts) but typically alts is small (often <10) so
        // it's fine.
        //
        // Build a parallel array `frame_of_trail[i]` = index into
        // `push_frames` for trail entry `i`.  Trail entries beyond
        // `frame_of_trail.len()` belong to `current_frame` (which
        // hasn't been moved into `push_frames` yet).
        let mut frame_of_trail: Vec<usize> = Vec::with_capacity(self.trail.len());
        for (frame_idx, frame) in self.push_frames.iter().enumerate() {
            for _ in 0..frame.trail_added {
                frame_of_trail.push(frame_idx);
            }
        }
        let len_in_frames = frame_of_trail.len();

        // Snapshot trail lit_idx values to dodge the
        // `&self.trail` + `&mut self.prod_alt_blocked` borrow conflict.
        let trail_lit_idx: Vec<usize> = self.trail.iter()
            .map(|t| (t.lit.var as usize) * 2 + (t.lit.neg as usize))
            .collect();

        for (alt_idx, alt) in alts.iter().enumerate() {
            let comp_idx = (alt.var as usize) * 2 + ((!alt.neg) as usize);
            // Find the FIRST trail entry whose lit is the alt's
            // complement.  That's the entry "responsible" for the
            // alt being blocked; when its frame pops, the blocking
            // gets undone in lockstep.
            for (trail_idx, &t_idx) in trail_lit_idx.iter().enumerate() {
                if t_idx == comp_idx {
                    self.prod_alt_blocked[clause_id][alt_idx] = true;
                    self.prod_blocked[clause_id] += 1;
                    if trail_idx < len_in_frames {
                        let fi = frame_of_trail[trail_idx];
                        self.push_frames[fi].blocked.push((clause_id, alt_idx));
                    } else {
                        // Trail entry was added by the in-progress
                        // current frame.
                        current_frame.blocked.push((clause_id, alt_idx));
                    }
                    break;
                }
            }
        }

        clause_id
    }

    /// Walk `nnf` once and index every `Prod` whose children are all
    /// `Lit`s **and whose ancestors are all `Sum` nodes**.  Same
    /// soundness rationale as in [`crate::controller::SmartController`]:
    /// a Prod nested inside another Prod is on an alternative branch
    /// the DFS may not visit, so we can't safely propagate over it.
    fn preprocess(&mut self, nnf: &NNF) {
        fn walk<G: FnMut(PathsClass, bool) -> bool>(
            n: &NNF,
            s: &mut CdclController<G>,
            inside_prod: bool,
        ) {
            match n {
                NNF::Lit(_) => {}
                NNF::Sum(ch) => for c in ch { walk(c, s, inside_prod); }
                NNF::Prod(ch) => {
                    if !inside_prod && !ch.is_empty() && ch.iter().all(|c| matches!(c, NNF::Lit(_))) {
                        let clause_id = s.prod_alts.len();
                        let alts: Vec<Lit> = ch.iter().map(|c| match c {
                            NNF::Lit(l) => l.clone(),
                            _ => unreachable!(),
                        }).collect();
                        for (alt_idx, lit) in alts.iter().enumerate() {
                            let lit_idx = (lit.var as usize) * 2 + (lit.neg as usize);
                            if lit_idx >= s.watches.len() {
                                s.watches.resize(lit_idx + 1, Vec::new());
                            }
                            s.watches[lit_idx].push((clause_id, alt_idx));
                        }
                        s.prod_total.push(alts.len());
                        s.prod_blocked.push(0);
                        s.prod_alt_blocked.push(vec![false; alts.len()]);
                        s.prod_alts.push(alts);
                    }
                    for c in ch { walk(c, s, true); }
                }
            }
        }
        walk(nnf, self, false);
        if !self.watches.is_empty() {
            self.implied_lit_counter.resize(self.watches.len(), 0);
        }
        // Record how many clauses came from preprocess; anything added
        // later is a learned clause and may be considered for deletion.
        self.initial_clause_count = self.prod_alts.len();
        // Initialize `clause_deleted` to all false for original clauses.
        self.clause_deleted = vec![false; self.prod_alts.len()];
    }

    /// Returns whether `lit_idx` is currently "true" on the path —
    /// either an actual DFS-pushed lit or a propagation-implied lit.
    /// O(1).
    #[inline]
    fn lit_or_implied(&self, lit_idx: usize) -> bool {
        if self.implied_lit_counter.get(lit_idx).copied().unwrap_or(0) > 0 {
            return true;
        }
        let var = (lit_idx >> 1) as Var;
        let neg = (lit_idx & 1) == 1;
        self.inner.has_lit(&Lit { var, neg })
    }

    /// Linear scan over a clause's alternatives — returns the unique
    /// non-blocked one, or `None` if there's zero or more than one.
    /// Called only when the blocked count says exactly one should
    /// remain, so the linear cost is bounded by the clause's arity.
    fn find_remaining_alt(&self, clause_id: usize) -> Option<usize> {
        let alts = &self.prod_alts[clause_id];
        let mut found: Option<usize> = None;
        for (i, lit) in alts.iter().enumerate() {
            let comp_idx = (lit.var as usize) * 2 + ((!lit.neg) as usize);
            if self.lit_or_implied(comp_idx) { continue; }
            if found.is_some() { return None; }
            found = Some(i);
        }
        found
    }

    /// Run the propagation cascade triggered by pushing `lit` onto the
    /// trail at `level`.  Mutates clause-blocked counts and the
    /// implied-lit counter, and appends one `Reason::Implied(clause_id)`
    /// trail entry per implied lit.  All changes are recorded in
    /// `frame` for undo on backtrack.
    ///
    /// Returns `Err(clause_id)` on cascade conflict — `clause_id` is
    /// the clause that became fully blocked (or that tried to imply
    /// a lit whose complement was already true).  1UIP analysis
    /// builds its initial learning set from this clause's alts.
    fn process_push(&mut self, lit: &Lit, level: usize, frame: &mut PushFrame) -> Result<(), usize> {
        let mut queue: Vec<usize> = Vec::new();
        queue.push((lit.var as usize) * 2 + (lit.neg as usize));
        while let Some(l_idx) = queue.pop() {
            let comp_idx = l_idx ^ 1;
            if comp_idx >= self.watches.len() { continue; }
            // Snapshot the watch list — we're about to mutate clause
            // state and may extend the queue, so we can't hold the borrow.
            let touches: Vec<(usize, usize)> = self.watches[comp_idx].clone();
            for (clause_id, alt_idx) in touches {
                // Skip clauses pruned by LBD reduction — their watch
                // entries are still in `self.watches` (we don't compact
                // for ID-stability reasons) but they shouldn't fire.
                if self.clause_deleted[clause_id] { continue; }
                if self.prod_alt_blocked[clause_id][alt_idx] { continue; }
                self.prod_alt_blocked[clause_id][alt_idx] = true;
                self.prod_blocked[clause_id] += 1;
                frame.blocked.push((clause_id, alt_idx));
                let total   = self.prod_total[clause_id];
                let blocked = self.prod_blocked[clause_id];
                if blocked >= total {
                    // Every alt of this clause is blocked — conflict.
                    return Err(clause_id);
                }
                if blocked == total - 1 {
                    if let Some(rem_alt) = self.find_remaining_alt(clause_id) {
                        let rl = self.prod_alts[clause_id][rem_alt].clone();
                        let r_idx      = (rl.var as usize) * 2 + (rl.neg as usize);
                        let r_comp_idx = r_idx ^ 1;
                        if self.lit_or_implied(r_comp_idx) {
                            return Err(clause_id);
                        }
                        if !self.lit_or_implied(r_idx) {
                            self.implied_lit_counter[r_idx] += 1;
                            frame.implied.push(r_idx);
                            // Add to the reasoned trail with the
                            // back-pointer to the clause that forced
                            // this lit.  1UIP analysis uses this
                            // back-pointer to traverse the implication
                            // graph.
                            self.trail.push(TrailLit {
                                lit: rl.clone(),
                                reason: Reason::Implied(clause_id),
                                decision_level: level,
                            });
                            frame.trail_added += 1;
                            queue.push(r_idx);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Undo every blocking / implication recorded in `frame`, plus
    /// truncate the reasoned trail by the number of entries this push
    /// added.
    fn undo(&mut self, frame: &PushFrame) {
        for &(clause_id, alt_idx) in &frame.blocked {
            self.prod_alt_blocked[clause_id][alt_idx] = false;
            self.prod_blocked[clause_id] -= 1;
        }
        for &lit_idx in &frame.implied {
            self.implied_lit_counter[lit_idx] -= 1;
        }
        // Phase saving: every lit being popped here contributes its
        // polarity to `saved_phase` so the next decision involving
        // that variable can re-prefer the recently-tried polarity.
        // We snapshot the lits first to avoid an aliasing borrow with
        // the `&mut self.saved_phase` we'd need otherwise.
        let new_len = self.trail.len() - frame.trail_added;
        let popped: Vec<Lit> = self.trail[new_len..]
            .iter()
            .map(|t| t.lit.clone())
            .collect();
        for lit in &popped {
            self.save_lit_phase(lit);
        }
        self.trail.truncate(new_len);
    }
}

impl<F: FnMut(PathsClass, bool) -> bool> PathSearchController for CdclController<F> {
    type OnClass = F;

    fn with_on_class(params: Option<PathParams>, on_class: F) -> Self {
        Self {
            inner: <BacktrackWhenCoveredController<F> as PathSearchController>::with_on_class(params, on_class),
            trail: Vec::new(),
            conflict_count: 0,
            last_path_len_at_lit_push: 0,
            prod_alts:        Vec::new(),
            prod_total:       Vec::new(),
            prod_blocked:     Vec::new(),
            prod_alt_blocked: Vec::new(),
            watches:          Vec::new(),
            implied_lit_counter: Vec::new(),
            push_frames:      Vec::new(),
            our_counted_len:  0,
            learned_clauses:  Vec::new(),
            // VSIDS defaults: standard MiniSAT-style 0.95 decay.
            // bump_value starts at 1.0 and grows over time as
            // `bump_value /= decay_factor` runs after each conflict.
            var_activity:     Vec::new(),
            bump_value:       1.0,
            decay_factor:     0.95,
            saved_phase:      Vec::new(),
            clause_deleted:   Vec::new(),
            // Reduction fires when live learned-clause count exceeds
            // this.  Tuned conservatively: low values (2000-50000)
            // regressed PHP-12-11 and PHP-14-13 by 4-6× because the
            // matrix-method search loses propagation power that
            // would otherwise short-circuit the path tree.
            // 100000 is a safety bound for runaway searches without
            // disturbing typical short ones.
            learned_clause_limit: 100000,
            initial_clause_count: 0,    // set at end of preprocess()
            // Luby restart defaults: unit=100 conflicts × luby(1)=1
            // → 100 conflicts before first restart.  Subsequent
            // thresholds follow the Luby sequence.
            restart_pending:              false,
            conflicts_since_last_restart: 0,
            restart_threshold:            100,
            restart_count:                0,
            restart_unit:                 100,
        }
    }

    fn with_on_class_uncovered_only(params: Option<PathParams>, on_class: F) -> Self {
        Self {
            inner: <BacktrackWhenCoveredController<F> as PathSearchController>::with_on_class_uncovered_only(params, on_class),
            trail: Vec::new(),
            conflict_count: 0,
            last_path_len_at_lit_push: 0,
            prod_alts:        Vec::new(),
            prod_total:       Vec::new(),
            prod_blocked:     Vec::new(),
            prod_alt_blocked: Vec::new(),
            watches:          Vec::new(),
            implied_lit_counter: Vec::new(),
            push_frames:      Vec::new(),
            our_counted_len:  0,
            learned_clauses:  Vec::new(),
            // VSIDS defaults: standard MiniSAT-style 0.95 decay.
            // bump_value starts at 1.0 and grows over time as
            // `bump_value /= decay_factor` runs after each conflict.
            var_activity:     Vec::new(),
            bump_value:       1.0,
            decay_factor:     0.95,
            saved_phase:      Vec::new(),
            clause_deleted:   Vec::new(),
            // Reduction fires when live learned-clause count exceeds
            // this.  Tuned conservatively: low values (2000-50000)
            // regressed PHP-12-11 and PHP-14-13 by 4-6× because the
            // matrix-method search loses propagation power that
            // would otherwise short-circuit the path tree.
            // 100000 is a safety bound for runaway searches without
            // disturbing typical short ones.
            learned_clause_limit: 100000,
            initial_clause_count: 0,    // set at end of preprocess()
            // Luby restart defaults: unit=100 conflicts × luby(1)=1
            // → 100 conflicts before first restart.  Subsequent
            // thresholds follow the Luby sequence.
            restart_pending:              false,
            conflicts_since_last_restart: 0,
            restart_threshold:            100,
            restart_count:                0,
            restart_unit:                 100,
        }
    }

    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        prefix_prod_path: &ProdPath,
        is_complete: bool,
    ) -> Option<usize> {
        // ── Phase 1: backtrack ──
        // Pop push_frames whose lits have been popped from the DFS path.
        // Each frame undoes its cascade (block / implied) and trims the
        // matching number of entries from the reasoned trail.
        while self.our_counted_len > prefix_literals.len() {
            let frame = self.push_frames.pop().expect("push_frames underflow");
            self.undo(&frame);
            self.our_counted_len -= 1;
        }
        // After backtrack, snap last_path_len_at_lit_push to the most
        // recently retained DFS lit's level (or 0 if no DFS lits left).
        if self.our_counted_len < prefix_literals.len() {
            self.last_path_len_at_lit_push = self.trail.iter().rev()
                .find(|t| !matches!(t.reason, Reason::Implied(_)))
                .map(|t| t.decision_level)
                .unwrap_or(0);
        }

        // ── Phase 2: delegate to the inner controller FIRST ──
        // The inner updates its lit_counter to reflect the current
        // prefix_literals, which our `lit_or_implied` checks rely on.
        // Calling inner before our forward-propagation phase ensures
        // process_push's "is the complement on path?" queries see the
        // up-to-date path state.  (Same ordering SmartController uses
        // and for the same reason.)
        let inner_r = self.inner.should_continue_on_prefix(
            prefix_literals, prefix_positions, prefix_prod_path, is_complete,
        );

        // ── Phase 3: forward — process newly-pushed DFS lits ──
        let mut want_backtrack = false;
        // Step 6: track whether the conflict was cascade-derived
        // (i.e., produced a learned clause).  If so, return `Some(1)`
        // instead of `Some(0)` — a 1-Prod backjump in our flat
        // Sum-of-Prods CNF-complement search.  Path-level conflicts
        // (no learned clause) still use chronological `Some(0)` to
        // avoid skipping potentially-valid paths.
        let mut want_backjump = false;
        while self.our_counted_len < prefix_literals.len() {
            let i = self.our_counted_len;
            let new_lit: Lit = prefix_literals[i].clone();
            let level = prefix_prod_path.len();

            // Reason for the DFS-pushed lit: Decision if path grew
            // since the last DFS push, SumForced otherwise.
            let reason = if level > self.last_path_len_at_lit_push {
                Reason::Decision
            } else {
                Reason::SumForced
            };

            let lit_idx  = (new_lit.var as usize) * 2 + (new_lit.neg as usize);
            let comp_idx = lit_idx ^ 1;

            // Add the DFS lit to the reasoned trail.  Even if it was
            // previously Implied, we keep the new record — Step 4's
            // 1UIP analysis treats trail entries as events and
            // resolves duplicates by their reason chains.
            let mut frame = PushFrame::default();
            self.trail.push(TrailLit {
                lit: new_lit.clone(),
                reason,
                decision_level: level,
            });
            frame.trail_added = 1;

            // Conflict detection at push time: is the complement
            // already known true?  At this point the inner has
            // processed `prefix_literals` so its lit_counter reflects
            // the new lit's presence; lit_or_implied(comp_idx) is
            // therefore accurate.
            let pushing_conflict = self.lit_or_implied(comp_idx);
            if pushing_conflict {
                self.conflict_count += 1;
                want_backtrack = true;
                // No useful 1UIP analysis for path-level conflicts
                // (they aren't tied to a specific clause's all-alts-
                // blocked event).  Step 6 may revisit this — for now
                // we just count it.
            } else {
                // Run the propagation cascade unless this lit was
                // already implied (in which case its consequences are
                // already applied to clause-blocked state).
                let already_implied = self.implied_lit_counter
                    .get(lit_idx).copied().unwrap_or(0) > 0;
                if !already_implied {
                    match self.process_push(&new_lit, level, &mut frame) {
                        Ok(()) => {}
                        Err(conflict_clause_id) => {
                            self.conflict_count += 1;
                            want_backtrack = true;
                            // Run 1UIP analysis and register the
                            // learned clause with the propagation
                            // machinery.  Initial blockings (every alt
                            // is blocked by construction) get routed
                            // to the appropriate push-frame's
                            // `blocked` list so they're undone as
                            // their owning frames pop on backtrack.
                            //
                            // Step 6 will turn `want_backtrack=true`
                            // into a non-chronological backjump using
                            // `learned.backjump_level`.
                            let learned = self.analyze_conflict(conflict_clause_id);
                            let _learned_id = self.register_learned_clause(&learned, &mut frame);
                            // VSIDS: bump every variable in the
                            // learned clause's alts.  These are the
                            // variables most directly involved in
                            // the conflict — focusing future
                            // decisions on them tends to compact the
                            // search.
                            for alt in &learned.alts {
                                self.bump_var_activity(alt.var);
                            }
                            self.decay_var_activities();
                            self.learned_clauses.push(learned);
                            // Step 6: cascade conflict + learned
                            // clause → 1-Prod backjump.  See module
                            // docstring for why `Some(1)` is the
                            // right K for Sum-of-Prods.
                            want_backjump = true;
                            // Luby restart: count this cascade
                            // conflict; trigger restart when the
                            // current threshold is reached.
                            self.conflicts_since_last_restart += 1;
                            if self.conflicts_since_last_restart >= self.restart_threshold {
                                self.restart_pending = true;
                            }
                        }
                    }
                }
            }

            self.push_frames.push(frame);
            self.our_counted_len += 1;
            self.last_path_len_at_lit_push = level;
        }

        // Restart takes precedence: returning `Some(usize::MAX)`
        // unwinds the entire DFS.  The driver
        // ([`crate::matrix::NNF::classify_paths_uncovered_only`]) sees
        // `is_restart_pending()` after the engine exits, calls
        // `complete_restart()`, and re-invokes the engine — which
        // then re-descends with the same learned clauses + variable
        // activities but a fresh trail.
        if self.restart_pending {
            return Some(usize::MAX);
        }
        // Step 6: cascade conflicts (with learned clauses) escape the
        // current Prod's alt loop via `Some(1)`; path-level conflicts
        // fall back to chronological `Some(0)`.  The inner controller
        // may also have asked for backtrack (covered-prefix detection),
        // in which case its return value already encodes the request.
        if want_backjump {
            return Some(1);
        }
        if want_backtrack {
            return Some(0);
        }
        inner_r
    }

    fn should_continue_on_paths_class(&mut self, paths_class: PathsClass, hit_limit: bool) -> bool {
        self.inner.should_continue_on_paths_class(paths_class, hit_limit)
    }

    fn needs_cover(&self) -> bool { self.inner.needs_cover() }

    fn sum_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.sum_ord(children)
    }

    /// Propagation-driven `prod_ord` filter (same as
    /// [`crate::controller::SmartController`]) plus a VSIDS sort:
    ///
    /// 1. Skip Prod alternatives whose lits already appear false on
    ///    the path (the Prod choice would create a covered prefix
    ///    immediately).
    /// 2. Short-circuit to a single alt whose lit is already true
    ///    (the Prod is already satisfied).
    /// 3. Sort the surviving alts by descending variable activity
    ///    (VSIDS) — most-recently-conflicted variables are tried
    ///    first.  Ties keep declaration order (stable sort).  Non-
    ///    Lit children get activity 0.0 so they sort last.
    fn prod_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        let mut filtered: Vec<(usize, &'a NNF)> = Vec::with_capacity(children.len());
        for (i, c) in children.iter().enumerate() {
            match c {
                NNF::Lit(l) => {
                    let lit_idx  = (l.var as usize) * 2 + (l.neg as usize);
                    let comp_idx = lit_idx ^ 1;
                    if self.lit_or_implied(lit_idx) {
                        return Some(vec![(i, c)]);
                    }
                    if self.lit_or_implied(comp_idx) {
                        continue;
                    }
                    filtered.push((i, c));
                }
                _ => filtered.push((i, c)),
            }
        }

        // VSIDS + phase saving sort:
        //   1. Primary: descending variable activity.
        //   2. Tiebreaker: alts whose polarity matches the saved
        //      phase for their variable come first.
        // Stable sort, so further ties keep declaration order.
        filtered.sort_by(|(_, a), (_, b)| {
            let act_a = match a { NNF::Lit(l) => self.var_activity(l.var), _ => 0.0 };
            let act_b = match b { NNF::Lit(l) => self.var_activity(l.var), _ => 0.0 };
            act_b.partial_cmp(&act_a).unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| {
                    let p_a = match a { NNF::Lit(l) => self.phase_matches(l), _ => false };
                    let p_b = match b { NNF::Lit(l) => self.phase_matches(l), _ => false };
                    // Reverse compare so true (match) sorts before false.
                    p_b.cmp(&p_a)
                })
        });

        Some(filtered)
    }

    fn path_count(&self) -> usize { self.inner.path_count() }
    fn covered_prefix_count(&self) -> usize { self.inner.covered_prefix_count() }
    fn uncovered_path_count(&self) -> usize { self.inner.uncovered_path_count() }

    fn is_restart_pending(&self) -> bool { self.restart_pending }

    /// Reset trail / propagation state but keep accumulated knowledge.
    /// After this returns, the controller is ready to drive a fresh
    /// DFS with empty trail; the next call to
    /// `should_continue_on_prefix` will re-derive any forcing chains
    /// from scratch using the persistent watch lists, which now
    /// include all learned clauses and reflect the current VSIDS
    /// scores.
    fn complete_restart(&mut self) {
        // LBD reduction: prune the high-LBD half of learned clauses
        // when there are too many.  Done first (before the trail is
        // cleared) for symmetry with mainstream CDCL solvers; in our
        // case the reducer doesn't actually care about trail content
        // because only learned clauses are eligible and they're not
        // referenced by `Reason` *via the trail being cleared next*.
        if self.live_learned_clause_count() > self.learned_clause_limit {
            self.reduce_learned_clauses();
        }

        // Phase saving: every trail lit's polarity is preserved
        // across the restart so the next descent can re-prefer
        // recently-productive polarities.  Clone first to dodge the
        // borrow conflict with `save_lit_phase`'s `&mut self`.
        let popped: Vec<Lit> = self.trail.iter().map(|t| t.lit.clone()).collect();
        for lit in &popped {
            self.save_lit_phase(lit);
        }

        // Reset trail and per-search bookkeeping.
        self.trail.clear();
        self.push_frames.clear();
        self.our_counted_len = 0;
        self.last_path_len_at_lit_push = 0;
        self.restart_pending = false;
        self.conflicts_since_last_restart = 0;

        // Reset clause-blocking state.  Empty trail → nothing
        // currently true → no alts blocked, no implied lits.  This
        // is correct because every blocking we've recorded was
        // attributed to a push_frame, all of which are now cleared;
        // the on-trail lits that justified those blockings are gone.
        for blocked in &mut self.prod_blocked {
            *blocked = 0;
        }
        for ab in &mut self.prod_alt_blocked {
            for b in ab.iter_mut() {
                *b = false;
            }
        }
        for c in &mut self.implied_lit_counter {
            *c = 0;
        }

        // Advance the Luby schedule for the next restart's threshold.
        self.restart_count += 1;
        // 1-indexed Luby; first call here goes from initial threshold
        // (luby(1)*unit) to luby(2)*unit, etc.
        self.restart_threshold = self.restart_unit * luby(self.restart_count + 1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: drive a CdclController over `nnf` to completion and
    /// return the trail snapshot at every step.
    fn record_trail_evolution(nnf: &NNF) -> Vec<Vec<(Lit, Reason, usize)>> {
        let snapshots = std::cell::RefCell::new(Vec::new());
        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(nnf, None, |_class, _hl| true);
        nnf.for_each_path_prefix_ord(
            |_| None,
            |_| None,
            |lits, positions, prod_path, is_complete| {
                let r = ctrl.should_continue_on_prefix(lits, positions, prod_path, is_complete);
                snapshots.borrow_mut().push(ctrl.trail_snapshot());
                r
            },
        );
        snapshots.into_inner()
    }

    /// Build an NNF mirroring the complement of a 2-clause CNF:
    /// `(a + b)(¬c + d)` complement = `(¬a ∧ ¬b) + (c ∧ ¬d)`.
    /// Each Prod's alt is a Decision; the second Prod's alts at level 2.
    #[test]
    fn step2_decision_lits_from_prod_alts() {
        let na = NNF::Lit(Lit::neg(0));     // ¬a
        let nb = NNF::Lit(Lit::neg(1));     // ¬b
        let c  = NNF::Lit(Lit::pos(2));     // c
        let nd = NNF::Lit(Lit::neg(3));     // ¬d
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![na.clone(), nb.clone()]),
            NNF::Prod(vec![c.clone(),  nd.clone()]),
        ]);

        let snapshots = record_trail_evolution(&nnf);
        let mut decisions = std::collections::HashSet::new();
        for snap in &snapshots {
            for (lit, reason, level) in snap {
                if *reason == Reason::Decision {
                    decisions.insert((lit.var, lit.neg, *level));
                }
            }
        }
        assert!(decisions.contains(&(0, true, 1)),  "¬a should appear as Decision at level 1");
        assert!(decisions.contains(&(1, true, 1)),  "¬b should appear as Decision at level 1");
        assert!(decisions.contains(&(2, false, 2)), "c should appear as Decision at level 2");
        assert!(decisions.contains(&(3, true, 2)),  "¬d should appear as Decision at level 2");
    }

    /// `Sum(¬a, Prod(¬b, ¬c))` has `¬a` at level 0 SumForced; `¬b`/`¬c`
    /// as Decision at level 1.
    #[test]
    fn step2_sum_forced_vs_decision() {
        let na = NNF::Lit(Lit::neg(0));
        let nb = NNF::Lit(Lit::neg(1));
        let nc = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            na.clone(),
            NNF::Prod(vec![nb.clone(), nc.clone()]),
        ]);

        let snapshots = record_trail_evolution(&nnf);

        let mut saw_sum_forced_a    = false;
        let mut saw_decision_b_or_c = false;
        for snap in &snapshots {
            for (lit, reason, level) in snap {
                if lit.var == 0 && lit.neg && *reason == Reason::SumForced {
                    assert_eq!(*level, 0, "¬a is at top-level Sum, level 0");
                    saw_sum_forced_a = true;
                }
                if (lit.var == 1 || lit.var == 2) && lit.neg && *reason == Reason::Decision {
                    assert_eq!(*level, 1, "¬b/¬c are Prod alts, level 1");
                    saw_decision_b_or_c = true;
                }
            }
        }
        assert!(saw_sum_forced_a,    "expected SumForced ¬a in trail");
        assert!(saw_decision_b_or_c, "expected Decision ¬b or ¬c in trail");
    }

    /// Conflict counter rises when a complementary pair lands on the
    /// same path.
    #[test]
    fn step2_conflict_count_rises_on_complementary_pair() {
        let a  = NNF::Lit(Lit::pos(0));
        let na = NNF::Lit(Lit::neg(0));
        let nnf = NNF::Sum(vec![a.clone(), na.clone()]);

        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, |_, _| true);
        nnf.for_each_path_prefix_ord(
            |_| None,
            |_| None,
            |lits, positions, prod_path, is_complete| {
                ctrl.should_continue_on_prefix(lits, positions, prod_path, is_complete)
            },
        );
        assert!(ctrl.conflict_count() >= 1,
            "expected at least one conflict; got {}",
            ctrl.conflict_count());
    }

    // ── Step 3: propagation tests ────────────────────────────────────────

    /// Two clauses that share a variable in opposite polarities form a
    /// classic unit-propagation chain:
    ///    (a)         — unit clause, complement is `¬a`
    ///    (¬a + b)    — complement is `(a ∧ ¬b)`
    /// Once `¬a` lands on the path (from clause 1), clause 2's `a` alt
    /// gets blocked (its complement is on the path), leaving `¬b` as
    /// the sole remaining alt — which propagation should imply.
    ///
    /// In CNF complement form: `Sum(¬a, Prod(a, ¬b))` — the second
    /// cube `(a ∧ ¬b)` is the indexed clause.  Visiting `¬a` blocks
    /// that cube's `a` alt; `¬b` is then implied.
    #[test]
    fn step3_propagation_implies_lits() {
        let na = NNF::Lit(Lit::neg(0));
        let a  = NNF::Lit(Lit::pos(0));
        let nb = NNF::Lit(Lit::neg(1));
        let nnf = NNF::Sum(vec![
            na.clone(),                              // ¬a   (forces a=false)
            NNF::Prod(vec![a.clone(), nb.clone()]),  // a ∧ ¬b — clause_id 0
        ]);

        let snapshots = record_trail_evolution(&nnf);

        // We should observe at least one trail entry where ¬b appears
        // with reason Implied — propagation forced it once ¬a was
        // on the path.
        let mut saw_implied_nb = false;
        for snap in &snapshots {
            for (lit, reason, _level) in snap {
                if lit.var == 1 && lit.neg {
                    if let Reason::Implied(clause_id) = reason {
                        assert_eq!(*clause_id, 0, "expected clause_id=0 (the only indexed cube)");
                        saw_implied_nb = true;
                    }
                }
            }
        }
        assert!(saw_implied_nb,
            "expected ¬b to appear as Reason::Implied(clause_id) in some trail snapshot");
    }

    /// Preprocessing should index the cube as a single clause.
    #[test]
    fn step3_preprocess_indexes_clauses() {
        // Two cubes → two indexed clauses.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![NNF::Lit(Lit::pos(0)), NNF::Lit(Lit::neg(1))]),
            NNF::Prod(vec![NNF::Lit(Lit::neg(0)), NNF::Lit(Lit::pos(2))]),
        ]);
        let ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, |_, _| true);
        assert_eq!(ctrl.clause_count(), 2);
    }

    /// Sanity: a CNF complement where no propagation fires
    /// (only one cube, no shared vars) should preprocess but emit no
    /// Implied entries.
    #[test]
    fn step3_no_propagation_when_independent() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![NNF::Lit(Lit::pos(0)), NNF::Lit(Lit::pos(1))]),
        ]);
        let snapshots = record_trail_evolution(&nnf);
        for snap in &snapshots {
            for (_lit, reason, _level) in snap {
                if let Reason::Implied(_) = reason {
                    panic!("unexpected Implied entry in independent-clauses NNF: {:?}", snap);
                }
            }
        }
    }

    // ── Step 4: 1UIP conflict analysis tests ────────────────────────────

    /// On-class callback used by tests: ignore everything, keep
    /// classifying.  An `fn` (not a closure) so the controller's `F`
    /// type parameter is concrete and the controller is `Sized` /
    /// returnable.
    fn noop_on_class(_class: PathsClass, _hl: bool) -> bool { true }

    /// Helper: drive a CdclController over `nnf` and return the
    /// controller after the search completes (so tests can inspect
    /// `learned_clauses()` etc.).
    fn run_to_completion(nnf: &NNF) -> CdclController<fn(PathsClass, bool) -> bool> {
        let ctrl_cell = std::cell::RefCell::new(
            CdclController::for_nnf(nnf, None, noop_on_class as fn(PathsClass, bool) -> bool)
        );
        nnf.for_each_path_prefix_ord(
            |_| None,
            |_| None,
            |lits, positions, prod_path, is_complete| {
                ctrl_cell.borrow_mut().should_continue_on_prefix(lits, positions, prod_path, is_complete)
            },
        );
        ctrl_cell.into_inner()
    }

    /// Smallest cascade conflict: a unit literal triggers a cascade
    /// that fully blocks a downstream clause.
    ///
    /// Original CNF: (a ∨ b) ∧ (¬a ∨ ¬c) ∧ (¬b ∨ ¬c) ∧ (c)
    ///   — one of the cleaner ways to construct a structurally-UNSAT
    ///   instance whose UNSAT proof flows through propagation.
    ///   complement = (¬a ∧ ¬b) + (a ∧ c) + (b ∧ c) + (¬c)
    ///
    /// We put the unit ¬c **first** so the Sum visits it before any
    /// Prod, putting ¬c on the trail at level 0:
    ///   Sum(¬c, Prod(a, c), Prod(b, c), Prod(¬a, ¬b))
    ///
    /// Cascade after ¬c (SumForced, level 0) is on path:
    ///   - clause 0 (Prod a, c): alt `c` blocked (comp `¬c` on path).
    ///     Remaining alt `a` → implied via clause 0.
    ///   - clause 1 (Prod b, c): alt `c` blocked.  Remaining alt `b`
    ///     → implied via clause 1.
    ///   - clause 2 (Prod ¬a, ¬b): alt `¬a` blocked (comp `a` now
    ///     implied), alt `¬b` blocked (comp `b` now implied).  Both
    ///     blocked → CONFLICT, conflict clause = clause 2.
    ///
    /// 1UIP analysis on clause 2:
    ///   initial learning = { a, b }   (negations of clause 2's alts;
    ///                                  both lits currently on trail
    ///                                  as `Implied(0)` and `Implied(1)`)
    ///   Resolve b (Implied(1) = Prod(b, c)): replace b with ¬c
    ///     (negation of the other alt `c`).  learning = { a, ¬c }.
    ///   Resolve a (Implied(0) = Prod(a, c)): replace a with ¬c.
    ///     learning = { ¬c }.
    ///   Exactly one lit at conflict level 0 → done.
    ///   Learned cube alts = { c } (negation of ¬c).
    #[test]
    fn step4_simple_cascade_yields_learned_clause() {
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let ctrl = run_to_completion(&nnf);
        let learned = ctrl.learned_clauses();
        assert!(!learned.is_empty(),
            "expected at least one learned clause from cascade conflict, got none");

        let lc = &learned[0];
        let alts_set: std::collections::HashSet<Lit> = lc.alts.iter().cloned().collect();
        let expected: std::collections::HashSet<Lit> = [Lit::pos(2)].into_iter().collect();
        assert_eq!(alts_set, expected,
            "expected learned alts = {{ c }}, got {:?}", lc.alts);
        // All learning-set lits at level 0 → no higher UIP, backjump_level 0.
        assert_eq!(lc.backjump_level, 0);
    }

    /// 1UIP resolution actually fires when the implication chain has
    /// depth.
    ///
    /// Setup so we get cascading implications:
    ///   Sum( (¬a ∨ b) → cube ¬b ∧ a   becomes clause_id 0
    ///        (¬b ∨ c) → cube ¬c ∧ b   becomes clause_id 1
    ///        (¬a ∨ ¬c)→ cube c ∧ a    becomes clause_id 2
    ///        a — top-level Sum-Lit (forces a true)
    ///   )
    ///
    /// Once `a` (SumForced, level 0) is on the path:
    ///   - clause 0 (¬b ∧ a): `a`'s alt blocked (its comp `¬a` not on
    ///     path, but `a` itself IS on path so `a`'s alt is blocked
    ///     wait no...
    ///
    /// Actually let me think again.  The cubes are the *complements*
    /// of CNF clauses, so the cube alts are *negated* original lits.
    /// "¬a ∨ b"'s complement is "a ∧ ¬b": cube alts are `a`, `¬b`.
    ///
    /// When `a` is on the trail (from the unit Sum-Lit), the cube `(a
    /// ∧ ¬b)` has its `a` alt blocked? No — an alt is blocked when its
    /// *complement* is on path.  The complement of `a` (the alt) is
    /// `¬a`.  So an alt `a` is blocked when `¬a` is on path.  But we
    /// have `a` on path, not `¬a`.  So that alt is *not* blocked.
    ///
    /// I had this backwards.  Let me re-think the test.
    #[test]
    fn step4_implication_chain_resolves_through_implied() {
        // Goal: have a Decision lit at level 1 trigger a cascade,
        // resulting in conflict, with at least one Implied step in the
        // resolution.
        //
        // Construction:
        //   Sum(
        //     ¬x,                              (top-level: forces x = false)
        //     Prod(x, y),                      clause_id 0: alts {x, y}
        //                                      with ¬x on path, alt x blocked,
        //                                      so y is implied at level 0.
        //     Prod(x, ¬y),                     clause_id 1: alts {x, ¬y}
        //                                      with ¬x on path, alt x blocked.
        //                                      With y implied, ¬y's comp y is
        //                                      true → ¬y blocked too.  Conflict!
        //   )
        let x  = NNF::Lit(Lit::pos(0));
        let nx = NNF::Lit(Lit::neg(0));
        let y  = NNF::Lit(Lit::pos(1));
        let ny = NNF::Lit(Lit::neg(1));
        let nnf = NNF::Sum(vec![
            nx.clone(),
            NNF::Prod(vec![x.clone(), y.clone()]),    // clause_id 0
            NNF::Prod(vec![x.clone(), ny.clone()]),   // clause_id 1
        ]);

        let ctrl = run_to_completion(&nnf);
        let learned = ctrl.learned_clauses();
        assert!(!learned.is_empty(),
            "expected a learned clause from cascade conflict");

        // The conflict's initial learning set: { ¬x, ¬y } (negations
        // of clause 1's alts {x, ¬y}).  ¬y is on the trail with reason
        // Implied(0) — so 1UIP resolves it: replace ¬y with the
        // negations of clause 0's *other* alts (i.e. negations of {x}
        // since y was the implied alt) = { ¬x }.  Final learning set:
        // { ¬x } — already there.  Learned clause alts = { x }.
        let lc = &learned[0];
        let alts_set: std::collections::HashSet<Lit> = lc.alts.iter().cloned().collect();
        assert!(alts_set.contains(&Lit::pos(0)),
            "learned clause should contain `x` (negation of ¬x): {:?}", lc.alts);
        // All learning lits at level 0 ⇒ backjump 0.
        assert_eq!(lc.backjump_level, 0);
    }

    // ── Step 5: learned-clause registration tests ─────────────────────

    /// After a conflict, the learned clause should be registered with
    /// `prod_alts` — so `clause_count()` grows by one.
    #[test]
    fn step5_learned_clause_grows_clause_count() {
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let initial_clauses = {
            let ctrl: CdclController<fn(PathsClass, bool) -> bool> =
                CdclController::for_nnf(&nnf, None, noop_on_class);
            ctrl.clause_count()
        };
        assert_eq!(initial_clauses, 3, "preprocess should index the 3 cubes");

        let ctrl = run_to_completion(&nnf);
        assert_eq!(
            ctrl.clause_count(),
            initial_clauses + ctrl.learned_clauses().len(),
            "every learned clause should add 1 to clause_count: \
             initial={}, learned={}, final={}",
            initial_clauses,
            ctrl.learned_clauses().len(),
            ctrl.clause_count(),
        );
    }

    /// Newly-registered learned clauses must have entries in `watches`
    /// for each of their alts, so future pushes propagate through them.
    #[test]
    fn step5_learned_clause_indexed_in_watches() {
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let ctrl = run_to_completion(&nnf);
        let learned = ctrl.learned_clauses();
        assert!(!learned.is_empty(), "expected a learned clause");

        // The learned clause from this NNF has alts = { c }.  Its
        // clause_id is `initial_clauses + 0` = 3.  watches[c.lit_idx]
        // should contain (3, 0).
        let learned_id = 3;     // 3 original cubes + this is the first learned
        let c_lit_idx  = 2 * 2 + 0;     // var=2 (c), neg=false
        let watches_entries = &ctrl.watches[c_lit_idx];
        assert!(
            watches_entries.iter().any(|&(cid, _)| cid == learned_id),
            "expected watches[{}] to contain the learned clause's id ({}); \
             got {:?}",
            c_lit_idx, learned_id, watches_entries,
        );
    }

    // ── Step 6: backjump tests ───────────────────────────────────────

    /// Cascade conflicts should return `Some(1)` (1-Prod backjump),
    /// not `Some(0)` (chronological).  Path-level conflicts should
    /// still return `Some(0)`.
    #[test]
    fn step6_cascade_conflict_returns_backjump_distance_1() {
        // Same NNF as step4_simple_cascade — known cascade conflict.
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        // Capture every return value of should_continue_on_prefix.
        let returns_cell = std::cell::RefCell::new(Vec::new());
        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);
        nnf.for_each_path_prefix_ord(
            |_| None,
            |_| None,
            |lits, positions, prod_path, is_complete| {
                let r = ctrl.should_continue_on_prefix(lits, positions, prod_path, is_complete);
                returns_cell.borrow_mut().push(r);
                r
            },
        );

        let returns = returns_cell.into_inner();
        // The cascade conflict from pushing ¬c happens at the
        // first step.  We expect at least one Some(1) return value
        // (= 1-Prod backjump from the cascade-derived learned
        // clause).  We don't assert there are *no* Some(0) returns
        // because path-level conflicts and the inner controller's
        // covered-prefix detection can also drive backtracks.
        assert!(
            returns.iter().any(|&r| r == Some(1)),
            "expected at least one Some(1) return from cascade conflict; got {:?}",
            returns,
        );
        // Also: the controller registered a learned clause along the way.
        assert!(
            !ctrl.learned_clauses().is_empty(),
            "expected at least one learned clause to accompany the backjump",
        );
    }

    // ── VSIDS tests ──────────────────────────────────────────────────

    /// After conflicts, every variable that appeared in a learned
    /// clause's alts should have positive activity.  Exposed via the
    /// inherent `var_activity()` accessor.
    #[test]
    fn vsids_bump_increases_activity_of_conflict_vars() {
        // Use the same UNSAT NNF that step4 / step5 / step6 use.
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let ctrl = run_to_completion(&nnf);

        // `c` (var=2) is the sole alt of the learned clause derived
        // from this NNF — see step4_simple_cascade_yields_learned_clause.
        // After at least one bump, var 2's activity must be > 0.
        assert!(
            ctrl.var_activity(2) > 0.0,
            "expected var 2 ('c') to have positive activity after conflict; got {}",
            ctrl.var_activity(2),
        );
        // Variables not in any learned clause's alts (in this case,
        // `a`/var=0 and `b`/var=1 don't appear in the resolved {c}
        // learned cube) should have activity 0.
        assert_eq!(ctrl.var_activity(0), 0.0,
            "var 0 ('a') not in any learned clause should have 0 activity");
        assert_eq!(ctrl.var_activity(1), 0.0,
            "var 1 ('b') not in any learned clause should have 0 activity");
    }

    /// Repeated bumps on the same variable accumulate, and the global
    /// `bump_value` grows after each decay so that the same number of
    /// raw bumps gives more weight when applied to recent conflicts.
    #[test]
    fn vsids_bump_value_grows_with_decay() {
        let nnf = NNF::Sum(vec![
            NNF::Lit(Lit::pos(0)),
        ]);
        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);

        let initial_bump = ctrl.bump_value;
        ctrl.decay_var_activities();
        let after_one = ctrl.bump_value;
        ctrl.decay_var_activities();
        let after_two = ctrl.bump_value;

        // bump_value /= decay_factor each call → strictly increasing.
        assert!(after_one > initial_bump,
            "bump_value should grow after decay: {} -> {}", initial_bump, after_one);
        assert!(after_two > after_one,
            "bump_value should keep growing: {} -> {}", after_one, after_two);

        // Specifically: 0.95 decay means each step multiplies by 1/0.95.
        let expected_one = initial_bump / 0.95;
        assert!((after_one - expected_one).abs() < 1e-12,
            "after one decay: expected {}, got {}", expected_one, after_one);
    }

    /// Re-normalization fires when activity exceeds 1e100, scaling
    /// every activity (and the bump value) down by 1e-100 so the
    /// relative ordering is preserved but f64 doesn't overflow.
    #[test]
    fn vsids_renormalization_keeps_ordering() {
        let nnf = NNF::Sum(vec![
            NNF::Lit(Lit::pos(0)),
            NNF::Lit(Lit::pos(1)),
        ]);
        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);

        // Just under the renormalization threshold so a single bump
        // doesn't trigger renorm.
        ctrl.bump_value = 5e99;

        // Bump var 0 three times.  Each adds 5e99.
        // After bump 1: var_act[0] = 5e99    (<= 1e100, no renorm)
        // After bump 2: var_act[0] = 1e100  (still <= 1e100, no renorm)
        // After bump 3: var_act[0] = 1.5e100 (> 1e100, renorm fires).
        //   Renorm: every activity *= 1e-100, bump_value *= 1e-100.
        //   So var_act[0] = 1.5, bump_value = 0.05.
        ctrl.bump_var_activity(0);
        ctrl.bump_var_activity(0);
        ctrl.bump_var_activity(0);
        let act_0_after_renorm = ctrl.var_activity(0);
        assert!(act_0_after_renorm < 1e10,
            "renormalization should bring activity down: {}", act_0_after_renorm);
        assert!(ctrl.bump_value < 1e10,
            "renormalization should bring bump_value down: {}", ctrl.bump_value);

        // Bump var 1 once with the now-smaller bump.
        ctrl.bump_var_activity(1);

        // Relative ordering preserved: var 0 got 3 bumps' worth of
        // activity (post-renorm), var 1 got 1 bump's worth, so var 0
        // should remain higher.
        assert!(ctrl.var_activity(0) > ctrl.var_activity(1),
            "var 0 should have higher activity than var 1: {} vs {}",
            ctrl.var_activity(0), ctrl.var_activity(1));
    }

    // ── Restart tests ────────────────────────────────────────────────

    /// The Luby sequence must produce its canonical first 15 terms.
    #[test]
    fn luby_sequence_canonical_prefix() {
        let expected = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        for (i, &want) in expected.iter().enumerate() {
            let got = luby(i + 1);
            assert_eq!(got, want, "luby({}) = {}, expected {}", i + 1, got, want);
        }
    }

    /// `luby(2^k - 1) == 2^(k-1)` for all reasonable k — the
    /// "long-run length doubles" invariant.
    #[test]
    fn luby_long_run_lengths_double() {
        for k in 1..16 {
            let i = (1usize << k) - 1;
            assert_eq!(luby(i), 1usize << (k - 1),
                "luby(2^{}-1 = {}) should equal 2^{} = {}", k, i, k-1, 1usize << (k-1));
        }
    }

    /// `complete_restart()` must clear the trail and propagation
    /// blocked-state but keep learned clauses, watches, and VSIDS
    /// activities.
    #[test]
    fn restart_resets_trail_keeps_knowledge() {
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let mut ctrl = run_to_completion(&nnf);

        assert!(!ctrl.learned_clauses().is_empty());
        assert!(ctrl.var_activity(2) > 0.0);

        // Snapshot persistent knowledge before restart.
        let learned_before  = ctrl.learned_clauses().len();
        let activity_before = ctrl.var_activity(2);
        let watches_len     = ctrl.watches.len();
        let prod_alts_len   = ctrl.prod_alts.len();

        // Force-set restart_pending so we can exercise the trigger
        // path even if the run-to-completion call already cleared it.
        ctrl.restart_pending = true;
        ctrl.complete_restart();

        // Trail / propagation state cleared.
        assert!(ctrl.trail.is_empty(), "trail should be empty after restart");
        assert!(ctrl.push_frames.is_empty(), "push_frames should be empty");
        assert_eq!(ctrl.our_counted_len, 0);
        for &b in &ctrl.prod_blocked { assert_eq!(b, 0); }
        for ab in &ctrl.prod_alt_blocked {
            for &b in ab { assert!(!b); }
        }
        for &c in &ctrl.implied_lit_counter { assert_eq!(c, 0); }

        // Persistent knowledge preserved.
        assert_eq!(ctrl.learned_clauses().len(), learned_before,
            "learned clauses should survive restart");
        assert_eq!(ctrl.var_activity(2), activity_before,
            "VSIDS activity should survive restart");
        assert_eq!(ctrl.watches.len(), watches_len,
            "watches shouldn't shrink");
        assert_eq!(ctrl.prod_alts.len(), prod_alts_len,
            "indexed clauses (incl. learned) should persist");

        assert!(!ctrl.is_restart_pending());
        assert_eq!(ctrl.restart_count, 1);
    }

    /// Force-restart-on-every-conflict must still terminate with the
    /// right UNSAT answer — Luby's geometric backoff guarantees that
    /// eventually a single iteration's threshold exceeds the search
    /// cost, allowing clean DFS exhaustion.
    #[test]
    fn restart_preserves_unsat_outcome() {
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);
        // Make every cascade conflict trigger a restart.
        ctrl.restart_unit = 1;
        ctrl.restart_threshold = 1;

        // Drive the search via the same loop pattern as
        // classify_paths_uncovered_only's worker uses.
        let cell = std::cell::RefCell::new(ctrl);
        let mut max_iters = 100;     // safety bound
        loop {
            let prev_unc = cell.borrow().uncovered_path_count();
            nnf.for_each_path_prefix_no_positions_ord(
                |_| None,
                |_| None,
                |lits, prod_path, is_complete, _cover_mult| {
                    let empty: PathPrefix = Vec::new();
                    cell.borrow_mut().should_continue_on_prefix(lits, &empty, prod_path, is_complete).is_none()
                },
            );
            let need_restart = {
                let c = cell.borrow();
                c.is_restart_pending() && c.uncovered_path_count() == prev_unc
            };
            if !need_restart { break; }
            cell.borrow_mut().complete_restart();
            max_iters -= 1;
            assert!(max_iters > 0,
                "restart loop didn't converge — Luby threshold growth broken?");
        }
        assert_eq!(cell.borrow().uncovered_path_count(), 0,
            "expected UNSAT outcome");
        assert!(cell.borrow().restart_count > 0,
            "expected at least one restart to have fired");
    }

    // ── Phase-saving tests ───────────────────────────────────────────

    /// Popping a frame via `undo()` should record the polarity of
    /// each removed trail entry as the saved phase for its variable.
    #[test]
    fn phase_saving_records_polarity_on_pop() {
        let nnf = NNF::Sum(vec![NNF::Lit(Lit::pos(0))]);
        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);

        // Hand-stage a trail entry + matching push frame, then call
        // `undo()` to simulate a backtrack.  This tests the
        // phase-saving path without requiring a particular DFS
        // unwinding sequence.
        ctrl.trail.push(TrailLit {
            lit: Lit::neg(5),
            reason: Reason::Decision,
            decision_level: 1,
        });
        let frame = PushFrame { trail_added: 1, blocked: vec![], implied: vec![] };
        ctrl.undo(&frame);

        assert!(ctrl.trail.is_empty(), "trail should be empty after undo");
        assert_eq!(
            ctrl.saved_phase.get(5).copied().flatten(),
            Some(true),
            "expected var 5's phase saved as neg=true; saved_phase = {:?}",
            ctrl.saved_phase,
        );
    }

    /// Saved phases should survive a `complete_restart()`.
    #[test]
    fn phase_saving_survives_restart() {
        let a  = NNF::Lit(Lit::pos(0));
        let na = NNF::Lit(Lit::neg(0));
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![a.clone(),  na.clone()]),
        ]);

        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);

        // Simulate having a lit on the trail with a particular polarity,
        // then trigger a restart.  After the restart, saved_phase
        // should remember the polarity even though the trail is empty.
        ctrl.trail.push(TrailLit {
            lit: Lit::neg(7),    // var 7, polarity neg=true
            reason: Reason::Decision,
            decision_level: 1,
        });
        ctrl.restart_pending = true;
        ctrl.complete_restart();

        assert!(ctrl.trail.is_empty());
        assert_eq!(
            ctrl.saved_phase.get(7).copied().flatten(),
            Some(true),
            "var 7's saved phase should be `neg=true` after restart; got {:?}",
            ctrl.saved_phase.get(7),
        );
    }

    /// `phase_matches` returns true iff the lit's polarity equals
    /// the saved phase, false when no save exists.
    #[test]
    fn phase_matches_lookup() {
        let nnf = NNF::Sum(vec![NNF::Lit(Lit::pos(0))]);
        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);

        // No save yet → phase_matches false.
        assert!(!ctrl.phase_matches(&Lit::pos(0)));
        assert!(!ctrl.phase_matches(&Lit::neg(0)));

        // Save var 0 with neg=true.
        ctrl.save_lit_phase(&Lit::neg(0));
        assert!(!ctrl.phase_matches(&Lit::pos(0)),
            "Lit::pos(0) (neg=false) shouldn't match saved neg=true");
        assert!(ctrl.phase_matches(&Lit::neg(0)),
            "Lit::neg(0) (neg=true) should match saved neg=true");

        // Re-save with neg=false → flips the saved phase.
        ctrl.save_lit_phase(&Lit::pos(0));
        assert!(ctrl.phase_matches(&Lit::pos(0)));
        assert!(!ctrl.phase_matches(&Lit::neg(0)));
    }

    // ── LBD-deletion tests ──────────────────────────────────────────

    /// LBD of a learned clause whose learning set has all lits at
    /// level 0 should be 1 (one distinct level).
    #[test]
    fn lbd_one_when_all_lits_at_same_level() {
        // Same NNF as step4_simple_cascade — its learned cube has
        // alts = [c] derived from a learning set entirely at level 0.
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let ctrl = run_to_completion(&nnf);
        let learned = ctrl.learned_clauses();
        assert!(!learned.is_empty(), "expected at least one learned clause");
        assert_eq!(learned[0].lbd, 1,
            "LBD should be 1 for a single-level learning set; got {}",
            learned[0].lbd);
    }

    /// `clause_deleted` is initialized correctly during preprocess and
    /// `live_learned_clause_count` reflects the deletion state.
    #[test]
    fn live_learned_count_tracks_clause_deleted() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![NNF::Lit(Lit::pos(0)), NNF::Lit(Lit::pos(1))]),
        ]);
        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);

        // Before any conflict: 0 learned clauses.
        assert_eq!(ctrl.live_learned_clause_count(), 0);
        assert_eq!(ctrl.initial_clause_count, 1);
        assert_eq!(ctrl.clause_deleted.len(), 1);
        assert!(!ctrl.clause_deleted[0]);   // original clause is live

        // Hand-stage a learned clause to test the live-count tracking
        // without driving an actual search.
        let learned = LearnedClause {
            alts: vec![Lit::pos(0)],
            backjump_level: 0,
            lbd: 5,
        };
        let mut frame = PushFrame::default();
        let learned_id = ctrl.register_learned_clause(&learned, &mut frame);
        ctrl.learned_clauses.push(learned);
        assert_eq!(ctrl.live_learned_clause_count(), 1);
        assert_eq!(learned_id, 1);   // initial_count=1, so first learned id is 1

        // Mark the learned clause deleted; live count drops to 0.
        ctrl.clause_deleted[learned_id] = true;
        assert_eq!(ctrl.live_learned_clause_count(), 0);
    }

    /// `reduce_learned_clauses` should mark the high-LBD half of the
    /// learned clauses as deleted, preserving the low-LBD half.
    #[test]
    fn reduce_learned_clauses_marks_high_lbd_half() {
        // Use a Sum-of-Prod-of-Lits NNF so preprocess indexes one
        // initial clause (giving initial_clause_count == 1).  Without
        // a Prod, initial_clause_count would be 0 and the learned
        // clauses below would be at ids 0..=3.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![NNF::Lit(Lit::pos(0)), NNF::Lit(Lit::pos(1))]),
        ]);
        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);
        assert_eq!(ctrl.initial_clause_count, 1);

        // Hand-stage four learned clauses with distinct LBDs.
        let lbds = [1, 7, 3, 5];
        for &lbd in &lbds {
            let learned = LearnedClause {
                alts: vec![Lit::pos(lbd as Var)],
                backjump_level: 0,
                lbd,
            };
            let mut frame = PushFrame::default();
            let _ = ctrl.register_learned_clause(&learned, &mut frame);
            ctrl.learned_clauses.push(learned);
        }

        assert_eq!(ctrl.live_learned_clause_count(), 4);

        ctrl.reduce_learned_clauses();

        // Half (2 of 4) should be marked deleted — specifically the
        // top-LBD half (LBDs 5 and 7).
        assert_eq!(ctrl.live_learned_clause_count(), 2,
            "expected reduction to leave 2 live clauses");

        // Inspect which got deleted.  ids 1..=4 in registration order;
        // lbds at those ids are [1, 7, 3, 5].  Survivors are LBD 1 and 3.
        // initial_clause_count = 1 (original Lit clause), so learned
        // clauses are at ids 1, 2, 3, 4.
        assert!(!ctrl.clause_deleted[1], "LBD 1 (id 1) should survive");
        assert!( ctrl.clause_deleted[2], "LBD 7 (id 2) should be deleted");
        assert!(!ctrl.clause_deleted[3], "LBD 3 (id 3) should survive");
        assert!( ctrl.clause_deleted[4], "LBD 5 (id 4) should be deleted");
    }

    /// `process_push` must skip deleted clauses.  We hand-build a
    /// state where a learned clause would normally fire (its watch
    /// entry would block an alt) and confirm that marking it deleted
    /// makes the cascade ignore it.
    #[test]
    fn deleted_clauses_skipped_during_propagation() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![NNF::Lit(Lit::pos(0)), NNF::Lit(Lit::pos(1))]),
        ]);
        let mut ctrl: CdclController<fn(PathsClass, bool) -> bool> =
            CdclController::for_nnf(&nnf, None, noop_on_class);

        // Stage a learned clause with alts [a, b].  Its watch entries
        // are for var 0 and var 1.  Pushing ¬a (var 0, neg=true)
        // would normally block the `a` alt of this clause.
        let learned = LearnedClause {
            alts: vec![Lit::pos(0), Lit::pos(1)],
            backjump_level: 0,
            lbd: 1,
        };
        let mut frame = PushFrame::default();
        let learned_id = ctrl.register_learned_clause(&learned, &mut frame);
        ctrl.learned_clauses.push(learned);

        // Mark the clause deleted.
        ctrl.clause_deleted[learned_id] = true;

        // Now run process_push for ¬a and observe that the deleted
        // clause's blocked count does NOT change.
        let blocked_before = ctrl.prod_blocked[learned_id];
        let mut frame2 = PushFrame::default();
        let _ = ctrl.process_push(&Lit::neg(0), 0, &mut frame2);
        let blocked_after = ctrl.prod_blocked[learned_id];
        assert_eq!(blocked_before, blocked_after,
            "deleted clause's prod_blocked should not change on cascade");
    }

    /// Backjumping must not break the agreement with SmartController.
    /// (This is a sanity check that complements the cross-controller
    /// test in `src/bin/sat.rs::tests::cdcl_agrees_with_smart_on_all_cases`,
    /// run from inside the controller's own test module so it stays
    /// passing when developing here in isolation.)
    #[test]
    fn step6_backjump_preserves_outcome_on_known_unsat() {
        // Build the same UNSAT NNF as step4 / step5 / step6 above.
        // After all conflicts and backjumps, the search must terminate
        // with no uncovered path found (i.e., the inner controller's
        // uncovered_path_count stays 0).
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let ctrl = run_to_completion(&nnf);
        assert_eq!(
            ctrl.uncovered_path_count(), 0,
            "UNSAT formula should yield no uncovered paths; got {}",
            ctrl.uncovered_path_count(),
        );
    }

    /// Backtracking must undo a learned clause's initial blockings —
    /// the learned cube's `prod_blocked` count should return to 0
    /// once every trail lit responsible for the initial blockings
    /// has been popped.
    #[test]
    fn step5_backtrack_clears_learned_clause_blockings() {
        // Drive the search the same way `run_to_completion` does, but
        // also issue an extra `should_continue_on_prefix` call with
        // an empty prefix at the end — that simulates the trail being
        // fully drained, which is what happens in the production
        // engine after the last conflict triggers backtrack-out.
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let mut ctrl = run_to_completion(&nnf);

        // Empty-prefix call: simulates the DFS having popped every
        // lit off the trail.
        let empty_lits: Vec<&Lit> = Vec::new();
        let empty_positions = Vec::new();
        let empty_path = Vec::new();
        ctrl.should_continue_on_prefix(&empty_lits, &empty_positions, &empty_path, false);

        // After full unwind, every clause's prod_blocked should be 0.
        for (cid, &blocked) in ctrl.prod_blocked.iter().enumerate() {
            assert_eq!(
                blocked, 0,
                "after full backtrack, clause {} (alts={:?}) should have 0 blocked alts; got {}",
                cid, ctrl.prod_alts[cid], blocked,
            );
        }
        // ... and every alt-blocked bit should be false.
        for (cid, alt_block) in ctrl.prod_alt_blocked.iter().enumerate() {
            for (i, &b) in alt_block.iter().enumerate() {
                assert!(!b, "clause {} alt {} should be unblocked; was {}", cid, i, b);
            }
        }
    }

    /// Sanity: each cascade conflict produces exactly one learned
    /// clause (we don't double-count).  Uses the same UNSAT NNF as
    /// `step4_simple_cascade_yields_learned_clause`.
    #[test]
    fn step4_one_learned_clause_per_conflict() {
        let a   = NNF::Lit(Lit::pos(0));
        let na  = NNF::Lit(Lit::neg(0));
        let b   = NNF::Lit(Lit::pos(1));
        let nb  = NNF::Lit(Lit::neg(1));
        let c   = NNF::Lit(Lit::pos(2));
        let nc  = NNF::Lit(Lit::neg(2));
        let nnf = NNF::Sum(vec![
            nc.clone(),
            NNF::Prod(vec![a.clone(),  c.clone()]),
            NNF::Prod(vec![b.clone(),  c.clone()]),
            NNF::Prod(vec![na.clone(), nb.clone()]),
        ]);

        let ctrl = run_to_completion(&nnf);
        let learned = ctrl.learned_clauses();
        assert_eq!(learned.len(), 1, "expected exactly 1 learned clause, got {}", learned.len());
    }
}
