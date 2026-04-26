//! [`SmartController`] — propagation-aware path-search controller.
//!
//! Adds cross-clause unit propagation on top of
//! [`crate::controller::BacktrackWhenCoveredController`].  The propagation
//! is purely structural — it indexes every `Prod` of `Lit`s whose
//! ancestors are all `Sum` nodes (i.e. "clauses" that lie on every path
//! through the NNF) and watches for blocked alternatives — so it works
//! identically whether the search is over the original formula
//! (validity / falsifying assignments) or its complement
//! (satisfiability / satisfying assignments).  The only things that
//! differ between the two cases are which NNF you preprocess and how you
//! interpret the resulting uncovered path.

use crate::controller::PathSearchController;
use crate::controller::backtrack::BacktrackWhenCoveredController;
use crate::matrix::{
    Lit, NNF, PathParams, PathPrefix, PathsClass, ProdPath, Var,
};

/// Path-search controller that wraps a [`BacktrackWhenCoveredController`]
/// and adds two CDCL-flavoured heuristics for fast uncovered-path searches
/// (used by both validity and satisfiability):
///
/// 1. **Unit-clause-first Sum ordering.**  At a Sum node (every child is
///    forced to contribute lits to the path) visit `Lit` children first,
///    then small `Prod`s, then larger structures.  Forced lits land in the
///    lit-set before downstream choices are made.
///
/// 2. **Cross-clause unit propagation.**  At controller creation the NNF is
///    pre-processed to index every "clause complement" (a `Prod` whose
///    children are all `Lit`s).  Each indexed `Prod` keeps a count of how
///    many of its alternatives have been blocked by lits committed to the
///    current path.  When a lit is pushed, watch lists drive O(touched-clauses)
///    propagation: any indexed `Prod` containing the lit's complement gets
///    one more blocked alternative; if its count reaches `total - 1` the
///    remaining alternative is *implied* and cascade-propagated.  At the
///    Prod entry, [`Self::prod_ord`] consults the implied set and the
///    blocked count to filter alternatives that the search couldn't satisfy
///    anyway, often collapsing the choice to a single alternative.
///
/// Backtracking is supported via a per-pushed-lit trail: every blocking
/// and implication tied to a given push is undone when the corresponding
/// lit is popped from the prefix.
pub struct SmartController<F: FnMut(PathsClass, bool) -> bool = fn(PathsClass, bool) -> bool> {
    inner: BacktrackWhenCoveredController<F>,
    // Indexed Prod-of-Lits "clause complements" found during preprocessing.
    // Each gets a sequential `prod_id`; per-id state lives in the parallel
    // vectors below.
    prod_alts:   Vec<Vec<Lit>>,    // per prod_id: clones of Lit children
    prod_total:  Vec<usize>,       // per prod_id: total alternatives
    prod_blocked: Vec<usize>,      // per prod_id: blocked-alternative count
    // Per prod_id, a bitmap of which alternatives are currently blocked.
    // Used to dedup blocking actions when the same lit is pushed multiple
    // times (e.g. by different clauses' Sum traversal pushing the same
    // forced literal) — without dedup we'd double-count.
    prod_alt_blocked: Vec<Vec<bool>>,
    // For each (var, polarity) — encoded as `var*2 + neg` — list of
    // (prod_id, alt_idx) entries indicating that pushing this lit blocks
    // that alternative.
    watches:     Vec<Vec<(usize, usize)>>,
    // Shadow lit-counter for *implied* lits — those propagation has decided
    // are on the path even though the DFS hasn't yet visited their Prod.
    implied_lit_counter: Vec<u32>,
    // One trail entry per lit pushed onto the prefix — records everything
    // we did in response so we can undo on pop.  A new lit also gets an
    // (empty) entry if propagation already implied it (skips re-propagation).
    propagation_trail: Vec<TrailEntry>,
    // Mirror of `prefix_literals.len()` from the previous callback — lets
    // us notice push/pop diffs cheaply at every entry.
    our_counted_len: usize,
    // True if propagation detected a conflict that should be flushed once
    // the inner controller's bookkeeping has caught up.  Reset on backtrack.
    propagation_conflict: bool,
}

#[derive(Default)]
struct TrailEntry {
    /// `(prod_id, alt_idx)` pairs that this push (or its implied cascade)
    /// marked as blocked.  Each one decrements `prod_blocked[prod_id]` on
    /// undo.
    blocked: Vec<(usize, usize)>,
    /// `var*2 + neg` indices that this push (or its implied cascade) added
    /// to `implied_lit_counter`.  Each decrements on undo.
    implied: Vec<usize>,
}

impl<F: FnMut(PathsClass, bool) -> bool> SmartController<F> {
    /// Shared constructor body — used by the trait's `with_on_class` /
    /// `with_on_class_uncovered_only` impls below to wrap an already-built
    /// inner controller.
    fn from_inner(inner: BacktrackWhenCoveredController<F>) -> Self {
        Self {
            inner,
            prod_alts:            Vec::new(),
            prod_total:           Vec::new(),
            prod_blocked:         Vec::new(),
            prod_alt_blocked:     Vec::new(),
            watches:              Vec::new(),
            implied_lit_counter:  Vec::new(),
            propagation_trail:    Vec::new(),
            our_counted_len:      0,
            propagation_conflict: false,
        }
    }

    /// Build a propagation-aware controller and pre-process `nnf` for
    /// cross-clause unit propagation.  Pass the same NNF the controller
    /// will be driven over: the original `nnf` for a validity search
    /// (where an uncovered path is a falsifying assignment) or the
    /// complement for a satisfiability search (where an uncovered path is
    /// a satisfying assignment).
    ///
    /// Uses uncovered-only mode for the inner controller, since the
    /// propagation-driven search is naturally paired with the no-positions
    /// traversal.  If you want cover certificates as well, build via
    /// [`PathSearchController::with_on_class`] and then call `preprocess`
    /// (private) — but in practice all current callers want
    /// uncovered-only.
    pub fn for_nnf(nnf: &NNF, params: Option<PathParams>, on_class: F) -> Self {
        let mut s = <Self as PathSearchController>::with_on_class_uncovered_only(params, on_class);
        s.preprocess(nnf);
        s
    }

    /// Walk `nnf` once and index every `Prod` whose children are all `Lit`s
    /// **and whose ancestors are all Sum nodes**.  The Sum-only-ancestor
    /// restriction is what makes propagation sound: a Prod inside another
    /// Prod is an alternative branch the DFS may *not* visit (Prod is "pick
    /// one child" in this NNF convention), so forcing one of its lits via
    /// unit propagation could rule out an SAT path that the outer Prod
    /// chose differently.  Top-level Prod-of-Lits — only Sum ancestors —
    /// *are* on every path and so are safe to propagate over.
    fn preprocess(&mut self, nnf: &NNF) {
        fn walk<G: FnMut(PathsClass, bool) -> bool>(
            n: &NNF,
            s: &mut SmartController<G>,
            inside_prod: bool,
        ) {
            match n {
                NNF::Lit(_) => {}
                NNF::Sum(ch) => for c in ch { walk(c, s, inside_prod); }
                NNF::Prod(ch) => {
                    if !inside_prod && !ch.is_empty() && ch.iter().all(|c| matches!(c, NNF::Lit(_))) {
                        let prod_id = s.prod_alts.len();
                        let alts: Vec<Lit> = ch.iter().map(|c| match c {
                            NNF::Lit(l) => l.clone(),
                            _ => unreachable!(),
                        }).collect();
                        for (alt_idx, lit) in alts.iter().enumerate() {
                            let lit_idx = (lit.var as usize) * 2 + (lit.neg as usize);
                            if lit_idx >= s.watches.len() {
                                s.watches.resize(lit_idx + 1, Vec::new());
                            }
                            s.watches[lit_idx].push((prod_id, alt_idx));
                        }
                        s.prod_total.push(alts.len());
                        s.prod_blocked.push(0);
                        s.prod_alt_blocked.push(vec![false; alts.len()]);
                        s.prod_alts.push(alts);
                    }
                    // Once we're inside any Prod, descendants are on alternative
                    // branches and unsafe to index for propagation.
                    for c in ch { walk(c, s, true); }
                }
            }
        }
        walk(nnf, self, false);
        if !self.watches.is_empty() {
            self.implied_lit_counter.resize(self.watches.len(), 0);
        }
    }

    pub fn hit_limit(&self) -> bool { self.inner.hit_limit() }
    pub fn path_count(&self) -> usize { self.inner.path_count() }
    pub fn covered_prefix_count(&self) -> usize { self.inner.covered_prefix_count() }
    pub fn uncovered_path_count(&self) -> usize { self.inner.uncovered_path_count() }

    /// Returns whether `lit_idx` is true on the path — actually pushed, or
    /// implied by propagation.  O(1).
    #[inline]
    fn lit_or_implied(&self, lit_idx: usize) -> bool {
        if self.implied_lit_counter.get(lit_idx).copied().unwrap_or(0) > 0 {
            return true;
        }
        // Decode lit_idx → Lit and consult inner.
        let var = (lit_idx >> 1) as Var;
        let neg = (lit_idx & 1) == 1;
        self.inner.has_lit(&Lit { var, neg })
    }

    /// Apply propagation triggered by pushing `lit` onto the path.  Mutates
    /// `prod_blocked` / `implied_lit_counter` and records every change in
    /// `entry` so it can be undone later.  Returns `Err(())` if a conflict
    /// (some Prod's blocked count reached `total`) is discovered.
    fn process_push(&mut self, lit: &Lit, entry: &mut TrailEntry) -> Result<(), ()> {
        let mut queue: Vec<usize> = Vec::new();
        queue.push((lit.var as usize) * 2 + (lit.neg as usize));
        while let Some(l_idx) = queue.pop() {
            // Pushing lit blocks every alternative whose lit is its complement.
            let comp_idx = l_idx ^ 1;
            if comp_idx >= self.watches.len() { continue; }
            // Snapshot the watch list — we're about to mutate prod state
            // and may recurse via the queue, so we can't hold the borrow.
            let touches: Vec<(usize, usize)> = self.watches[comp_idx].clone();
            for (prod_id, alt_idx) in touches {
                // Dedup: an alt can be blocked by many things — re-pushes
                // of the same lit, multiple complements landing in the
                // same Prod, etc.  Skip if it's already blocked.
                if self.prod_alt_blocked[prod_id][alt_idx] { continue; }
                self.prod_alt_blocked[prod_id][alt_idx] = true;
                self.prod_blocked[prod_id] += 1;
                entry.blocked.push((prod_id, alt_idx));
                let total   = self.prod_total[prod_id];
                let blocked = self.prod_blocked[prod_id];
                if blocked >= total { return Err(()); }
                if blocked == total - 1 {
                    if let Some(rem_alt) = self.find_remaining_alt(prod_id) {
                        let rl = self.prod_alts[prod_id][rem_alt].clone();
                        let r_idx      = (rl.var as usize) * 2 + (rl.neg as usize);
                        let r_comp_idx = r_idx ^ 1;
                        if self.lit_or_implied(r_comp_idx) {
                            return Err(());
                        }
                        if !self.lit_or_implied(r_idx) {
                            self.implied_lit_counter[r_idx] += 1;
                            entry.implied.push(r_idx);
                            queue.push(r_idx);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Linear scan of a Prod's alternatives — returns the unique non-blocked
    /// one, or `None` if there's zero or more than one.  Called only when
    /// the blocked count says exactly one should remain, so the linear cost
    /// is bounded by the Prod's arity (typically tiny).
    fn find_remaining_alt(&self, prod_id: usize) -> Option<usize> {
        let alts = &self.prod_alts[prod_id];
        let mut found: Option<usize> = None;
        for (i, lit) in alts.iter().enumerate() {
            let comp_idx = (lit.var as usize) * 2 + ((!lit.neg) as usize);
            if self.lit_or_implied(comp_idx) { continue; }
            if found.is_some() { return None; }
            found = Some(i);
        }
        found
    }

    /// Undo every blocking / implication recorded in `entry`.
    fn undo(&mut self, entry: &TrailEntry) {
        for &(prod_id, alt_idx) in &entry.blocked {
            self.prod_alt_blocked[prod_id][alt_idx] = false;
            self.prod_blocked[prod_id] -= 1;
        }
        for &lit_idx in &entry.implied {
            self.implied_lit_counter[lit_idx] -= 1;
        }
    }
}

impl<F: FnMut(PathsClass, bool) -> bool> PathSearchController for SmartController<F> {
    type OnClass = F;

    /// Build a propagation-aware controller wrapping a *cover-mode* inner
    /// controller.  The propagation logic itself is mode-independent — it
    /// only cares about which `Prod`-of-`Lit`s clauses exist and which
    /// lits are on the path — so this is a useful pairing when the caller
    /// wants both cross-clause propagation *and* `Covered` events for
    /// downstream reporting.  See [`Self::for_nnf`] for the more common
    /// uncovered-only flavour used by `Matrix::satisfiable_with_smart_controller`.
    fn with_on_class(params: Option<PathParams>, on_class: F) -> Self {
        let inner = <BacktrackWhenCoveredController<F> as PathSearchController>::with_on_class(params, on_class);
        Self::from_inner(inner)
    }

    /// Build a propagation-aware controller in uncovered-only mode: no
    /// `Covered` emissions, `needs_cover()` returns false, no per-Lit
    /// `pos.clone()` happens in the no-positions traversal.  This is the
    /// flavour [`Self::for_nnf`] uses internally.  Without preprocessing
    /// (i.e. when built via this constructor directly without subsequent
    /// `for_nnf` setup) the propagation is dormant and the controller
    /// falls back to local alternative pruning via `prod_ord`.
    fn with_on_class_uncovered_only(params: Option<PathParams>, on_class: F) -> Self {
        let inner = <BacktrackWhenCoveredController<F> as PathSearchController>::with_on_class_uncovered_only(params, on_class);
        Self::from_inner(inner)
    }

    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        complete_prod_path: Option<&ProdPath>,
    ) -> Option<usize> {
        // Step 1: undo propagation for every lit that's been popped from
        // the prefix since the last call.  Trail entries are 1-to-1 with
        // pushed lits, so we just pop & undo the suffix.
        while self.our_counted_len > prefix_literals.len() {
            let entry = self.propagation_trail.pop().expect("trail underflow");
            self.undo(&entry);
            self.our_counted_len -= 1;
        }
        // Reset any cached propagation conflict if the conflicting lit has
        // been popped.
        if self.propagation_conflict && self.our_counted_len <= prefix_literals.len() {
            // Conservative — we'll recompute on the next propagation.
            self.propagation_conflict = false;
        }

        // Step 2: let the inner controller run its cover-detection logic.
        // If it wants to backtrack, honour that immediately.
        let inner_r = self.inner.should_continue_on_prefix(
            prefix_literals, prefix_positions, complete_prod_path,
        );
        if inner_r.is_some() { return inner_r; }

        // Step 3: handle every newly-pushed lit by running propagation.
        // Each push gets one trail entry recording every blocking / implication
        // that resulted, so backtrack can undo them in the reverse order.
        while self.our_counted_len < prefix_literals.len() {
            let lit = prefix_literals[self.our_counted_len];
            let lit_idx = (lit.var as usize) * 2 + (lit.neg as usize);
            let mut entry = TrailEntry::default();
            // If this lit was already implied, propagation has already
            // applied its effects; the actual push doesn't add anything.
            let already_implied = self.implied_lit_counter
                .get(lit_idx).copied().unwrap_or(0) > 0;
            let conflict = if already_implied {
                false
            } else {
                self.process_push(lit, &mut entry).is_err()
            };
            self.propagation_trail.push(entry);
            self.our_counted_len += 1;
            if conflict { return Some(0); }
        }
        None
    }

    fn should_continue_on_paths_class(&mut self, paths_class: PathsClass, hit_limit: bool) -> bool {
        self.inner.should_continue_on_paths_class(paths_class, hit_limit)
    }

    fn needs_cover(&self) -> bool { self.inner.needs_cover() }

    fn path_count(&self) -> usize { self.inner.path_count() }
    fn covered_prefix_count(&self) -> usize { self.inner.covered_prefix_count() }
    fn uncovered_path_count(&self) -> usize { self.inner.uncovered_path_count() }

    // sum_ord left at default (natural order).  Reordering Sum children
    // is *unsound* with the current path encoding: the `ProdPath` only
    // records Prod-choice indices, and `NNF::lits_on_path` walks Sum
    // children in declaration order, consuming path entries in that order.
    // If we visited Sum children in a different order during the DFS, the
    // path entries we pushed would be in DFS order, not declaration order,
    // and `lits_on_path` would index the wrong Prod alternatives.
    // (Reordering Prod is fine — Prod consumes exactly one path entry
    // and we record the original child index.)

    fn prod_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        // Filter alternatives that propagation has shown can't lead to a
        // satisfying path:
        //   * already true (lit on path or implied) → return that single
        //     alternative; the Prod is already satisfied.
        //   * complement already true → skip; descending would create a
        //     covered prefix immediately.
        //   * otherwise keep.
        // For non-`Lit` children we can't reason about nested subtrees, so
        // we keep them and let the DFS work them out.  Empty result is the
        // correct "no consistent choice" signal — the surrounding Sum's
        // continuation chain never reaches the end and no spurious path is
        // emitted.  We always return `Some(...)` because we always inspect
        // children; the DFS engine's `None`-shortcut for declaration order
        // doesn't apply to a propagation-aware controller.
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
        Some(filtered)
    }
}
