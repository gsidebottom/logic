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

    /// Like [`Self::for_nnf`] but builds the controller in *cover mode*
    /// (the inner `BacktrackWhenCoveredController` emits `Covered`
    /// events on complementary-pair detection) while still preprocessing
    /// the matrix for cross-clause unit propagation.  Used by the dual
    /// search framework, which needs both: cover events to feed the
    /// shared pair-pool, and propagation to keep B's path-search fast.
    pub fn for_nnf_with_cover(nnf: &NNF, params: Option<PathParams>, on_class: F) -> Self {
        let mut s = <Self as PathSearchController>::with_on_class(params, on_class);
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
    ///
    /// **Cover-mode caveat.**  When the inner controller wants `Covered`
    /// certificates we suppress the `Err` short-circuit and propagate as
    /// far as the queue takes us — never bailing out on a fully-blocked
    /// Prod.  Returning early would skip the DFS visit of that Prod, and
    /// the cover pair that closes its alt-paths would never be emitted
    /// (every alt's complement is on the path; visiting each alt lets
    /// inner detect the cover naturally).  The bookkeeping stays
    /// consistent because `find_remaining_alt` only fires when
    /// `blocked == total - 1`; once we cross `total` no further
    /// implications are attempted on that Prod, just dead-weight blocks
    /// that the trail will undo on backtrack.
    fn process_push(&mut self, lit: &Lit, entry: &mut TrailEntry) -> Result<(), ()> {
        let allow_short_circuit = !self.inner.needs_cover();
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
                if blocked >= total {
                    if allow_short_circuit { return Err(()); }
                    // Cover mode: skip implication step (no remaining alt)
                    // and continue draining the queue.
                    continue;
                }
                if blocked == total - 1 {
                    if let Some(rem_alt) = self.find_remaining_alt(prod_id) {
                        let rl = self.prod_alts[prod_id][rem_alt].clone();
                        let r_idx      = (rl.var as usize) * 2 + (rl.neg as usize);
                        let r_comp_idx = r_idx ^ 1;
                        if self.lit_or_implied(r_comp_idx) {
                            if allow_short_circuit { return Err(()); }
                            // Cover mode: this Prod is unsatisfiable but
                            // we'll let the DFS visit it and rely on
                            // inner to detect the cover.  Don't imply
                            // anything (no consistent remaining alt).
                            continue;
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
        prefix_prod_path: &ProdPath,
        is_complete: bool,
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
            prefix_literals, prefix_positions, prefix_prod_path, is_complete,
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
        //
        // **Cover-mode caveat.**  When the inner controller wants `Covered`
        // certificates (`needs_cover()` is true) we must *not* prune
        // alternatives whose visit would produce a covered subtree — doing
        // so silently drops the very cover pairs the caller asked for.
        // Concrete example: complement of `(a+b)(a+b')(c)(d)(e)(a')` has
        // four paths; one of them is closed *only* by `{b', b}`, but
        // pruning the `b` alternative skips that path entirely and the
        // pair never makes it into the certificate.  Skipping the
        // "lit-already-true" shortcut on the same grounds — the unvisited
        // alternatives in that Prod might also carry pairs we haven't
        // logged yet.  In cover mode we keep every Lit child and let
        // inner detect `Covered` events naturally; sound, just slower.
        let want_cover = self.inner.needs_cover();
        let mut filtered: Vec<(usize, &'a NNF)> = Vec::with_capacity(children.len());
        for (i, c) in children.iter().enumerate() {
            match c {
                NNF::Lit(l) if !want_cover => {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::matrix::{Matrix, PathParams, PathsClass, default_classify_controller, DynOnClass};
    use std::collections::HashSet;

    /// Regression — `(a+b)(a+b')(c)(d)(e)(a')` is UNSAT, but covering the
    /// complement requires *both* `{a',a}` and `{b',b}`: path 4 of the
    /// complement = `[b', b, c', d', e', a]` has no `a'`, so `{a',a}`
    /// alone can't close it.  An earlier `SmartController::prod_ord` in
    /// cover mode pruned the `b` alternative based on propagation
    /// implying `a'`, never visiting path 4 and silently dropping the
    /// `{b',b}` cover certificate.  Cover mode must keep every Lit
    /// alternative so inner emits a Covered event for every path.
    #[tokio::test]
    async fn smart_cover_mode_emits_pair_for_every_path() {
        let formula = "(a + b)(a + b')(c)(d)(e)(a')";
        let m = Matrix::try_from(formula).unwrap();
        let nnf = m.nnf_complement.clone();
        let total_paths = nnf.path_count();
        let params = PathParams {
            uncovered_path_limit: 1,
            paths_class_limit: usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover: false,
        };
        let p = Some(params.clone());
        let nnf_for_builder = nnf.clone();
        let (handle, mut rx, _cancel) = m.classify_paths(true, 64, Some(params), move |tx| {
            let on_class: DynOnClass = Box::new(move |class, hit_limit| {
                tx.blocking_send((class, hit_limit)).is_ok()
            });
            SmartController::for_nnf_with_cover(&nnf_for_builder, p, on_class)
        });
        let mut lit_pairs: HashSet<(String, String)> = HashSet::new();
        let mut total_cover_count = 0.0_f64;
        let mut uncovered = 0usize;
        while let Some((class, _)) = rx.recv().await {
            match class {
                PathsClass::Covered(cp) => {
                    total_cover_count += nnf.prefix_cover_count(&cp.prefix);
                    let l1 = nnf.lit_at(&cp.cover.0).unwrap();
                    let l2 = nnf.lit_at(&cp.cover.1).unwrap();
                    let mut a = format!("{:?}", l1);
                    let mut b = format!("{:?}", l2);
                    if a > b { std::mem::swap(&mut a, &mut b); }
                    lit_pairs.insert((a, b));
                }
                PathsClass::Uncovered(_) => uncovered += 1,
            }
        }
        handle.await.expect("worker panicked").expect("classify error");
        assert_eq!(uncovered, 0, "formula is UNSAT — no uncovered paths expected");
        // Cover certificate must account for every path of the complement.
        // Without the fix this is < total_paths because path 4 (`[b', b, ...]`)
        // is silently pruned by `prod_ord` when `a'` is implied.
        assert_eq!(total_cover_count, total_paths,
                   "covered prefixes account for {} of {} paths",
                   total_cover_count, total_paths);
        // For this specific formula path 4 is closed *only* by `{b, b'}`,
        // so that pair must be present in the literal-level certificate
        // — there's no other way to cover it.
        let var_pair_present = |v: char| {
            lit_pairs.iter().any(|(a, b)| {
                let av = a.contains(&format!("var: {}", v as u32 - 'a' as u32));
                let bv = b.contains(&format!("var: {}", v as u32 - 'a' as u32));
                av && bv && a != b  // one positive, one negative
            })
        };
        assert!(var_pair_present('b'), "missing {{b, b'}} cover pair (got {:?})", lit_pairs);
    }

    /// Stronger regression — propagation can detect a conflict for a Prod
    /// `P` *before* the DFS visits `P`.  In that case my conservative
    /// "don't filter Lit alts in cover mode" fix isn't enough on its own
    /// because smart returns `Some(0)` from `process_push` before reaching
    /// `P`'s alt-loop and no Covered events fire at all.  For
    /// `(a)(b)(a'+b')(c)(d)(c'+d')` the complement is
    /// `Sum[a', b', Prod[a,b], c', d', Prod[c,d]]`; pushing `a'` then `b'`
    /// blocks both alts of `Prod[a,b]`.  Suppressing the propagation
    /// short-circuit lets the DFS visit `Prod[a,b]` and emit `{a,a'}` /
    /// `{b,b'}`, which together cover every complement path (they close
    /// at depth 3 regardless of the later `Prod[c,d]` choice).
    #[tokio::test]
    async fn smart_emits_pair_when_prop_conflict_precedes_dfs_visit() {
        let formula = "(a)(b)(a' + b')(c)(d)(c' + d')";
        let m = Matrix::try_from(formula).unwrap();
        let nnf = m.nnf_complement.clone();
        let total_paths = nnf.path_count();
        let params = PathParams {
            uncovered_path_limit: 1,
            paths_class_limit: usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover: false,
        };
        let p = Some(params.clone());
        let nnf_for_builder = nnf.clone();
        let (handle, mut rx, _cancel) = m.classify_paths(true, 64, Some(params), move |tx| {
            let on_class: DynOnClass = Box::new(move |class, hit_limit| {
                tx.blocking_send((class, hit_limit)).is_ok()
            });
            SmartController::for_nnf_with_cover(&nnf_for_builder, p, on_class)
        });
        let mut total_cover_count = 0.0_f64;
        let mut uncovered = 0usize;
        let mut covered_events = 0usize;
        while let Some((class, _)) = rx.recv().await {
            match class {
                PathsClass::Covered(cp) => {
                    covered_events += 1;
                    total_cover_count += nnf.prefix_cover_count(&cp.prefix);
                }
                PathsClass::Uncovered(_) => uncovered += 1,
            }
        }
        handle.await.expect("worker panicked").expect("classify error");
        assert_eq!(uncovered, 0, "formula is UNSAT");
        assert!(covered_events > 0, "must emit at least one Covered event");
        // Every path through the complement must be covered by some
        // certificate prefix.  Sum of `prefix_cover_count` over emitted
        // covered prefixes is the count of distinct full paths covered.
        // Without this fix the count is 0 (no events at all).
        assert_eq!(total_cover_count, total_paths,
                   "covered prefixes account for {} of {} paths",
                   total_cover_count, total_paths);
    }

    /// Sanity: the equivalent uncovered-only run still terminates fast and
    /// returns no uncovered paths (formula is UNSAT) — proves the
    /// cover-mode change didn't bleed into the propagation-pruning path.
    #[tokio::test]
    async fn smart_uncovered_only_still_prunes() {
        let formula = "(a + b)(a + b')(c)(d)(e)(a')";
        let m = Matrix::try_from(formula).unwrap();
        let params = PathParams {
            uncovered_path_limit: 1,
            paths_class_limit: usize::MAX,
            covered_prefix_limit: usize::MAX,
            no_cover: true,
        };
        let p = Some(params.clone());
        let (handle, mut rx, _cancel) = m.classify_paths(true, 64, Some(params),
            move |tx| default_classify_controller(p, tx));
        let mut uncovered = 0usize;
        while let Some((class, _)) = rx.recv().await {
            if matches!(class, PathsClass::Uncovered(_)) { uncovered += 1; }
        }
        handle.await.expect("worker panicked").expect("classify error");
        assert_eq!(uncovered, 0);
    }
}
