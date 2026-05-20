//! [`BacktrackWhenCoveredController`] — cover-aware DFS pruning controller.

use crate::controller::PathSearchController;
use crate::matrix::{
    CoveredPathPrefix, Lit, PathParams, PathPrefix, PathsClass, ProdPath, UncoveredPath,
};
use crate::nnf_arena::{ArenaPathSearchController, NnfArena, NnfId};

/// A `PathSearchController` that prunes paths whose prefix already contains a
/// complementary literal pair, classifying each completed path as
/// `Covered` or `Uncovered`. Classified items are delivered via
/// `should_continue_on_paths_class`. Set `on_class` to receive them via a callback.
pub struct BacktrackWhenCoveredController<F: FnMut(PathsClass, bool) -> bool = fn(PathsClass, bool) -> bool> {
    paths_class_limit: usize,
    uncovered_path_limit: usize,
    covered_prefix_limit: usize,
    covered_at_depth: Option<usize>,
    path_count: usize,
    uncovered_path_count: usize,
    covered_prefix_count: usize,
    last_lits_len: usize,
    on_class: Option<F>,
    // O(1) complement lookup: for each (var, polarity) encoded as var*2 + neg,
    // `lit_counter` is the number of copies currently on the path, and
    // `lit_first_pos` is the earliest prefix index where that literal still
    // sits.  `counted` is a stack of those encoded indices mirroring the
    // `prefix_literals` vec observed on the previous callback, so we can pop
    // our bookkeeping in lockstep when the DFS backtracks.
    lit_counter: Vec<u32>,
    lit_first_pos: Vec<Option<usize>>,
    counted: Vec<usize>,
    /// When true, the controller never builds or emits `PathsClass::Covered`
    /// events and declares `needs_cover() == false`, letting the driver
    /// skip all per-literal position cloning.  Complementary-pair detection
    /// still runs (for pruning via `covered_at_depth`); only the
    /// `CoveredPathPrefix` construction and `on_class(Covered)` invocation
    /// are suppressed.
    uncovered_only: bool,
}

impl From<Option<PathParams>> for BacktrackWhenCoveredController {
    fn from(params: Option<PathParams>) -> Self {
        let params = params.unwrap_or_default();
        Self {
            paths_class_limit: params.paths_class_limit,
            uncovered_path_limit: params.uncovered_path_limit,
            covered_prefix_limit: params.covered_prefix_limit,
            covered_at_depth: None,
            path_count: 0,
            uncovered_path_count: 0,
            covered_prefix_count: 0,
            last_lits_len: 0,
            on_class: None,
            lit_counter: Vec::new(),
            lit_first_pos: Vec::new(),
            counted: Vec::new(),
            uncovered_only: false,
        }
    }
}

impl<F: FnMut(PathsClass, bool) -> bool> BacktrackWhenCoveredController<F> {
    pub fn hit_limit(&self) -> bool {
        self.path_count >= self.paths_class_limit
            || self.uncovered_path_count >= self.uncovered_path_limit
            || self.covered_prefix_count >= self.covered_prefix_limit
    }

    /// Total classified path prefixes (covered + uncovered) seen so far.
    pub fn path_count(&self) -> usize { self.path_count }

    /// Number of complementary-pair detections so far (covered prefixes).
    /// Each one stands for `cover_count` complete paths that the DFS pruned.
    pub fn covered_prefix_count(&self) -> usize { self.covered_prefix_count }

    /// Number of complete uncovered paths reached so far.  Each contributes
    /// exactly one path to the classified total.
    pub fn uncovered_path_count(&self) -> usize { self.uncovered_path_count }

    /// Whether the literal `lit` is currently present anywhere in the live
    /// path prefix (the same lit may be pushed multiple times — this returns
    /// `true` if the count is positive).  O(1).
    pub fn has_lit(&self, lit: &Lit) -> bool {
        let idx = (lit.var as usize) * 2 + (lit.neg as usize);
        self.lit_counter.get(idx).copied().unwrap_or(0) > 0
    }

    /// Whether the *complement* of `lit` is on the current path — i.e.
    /// pushing `lit` now would create a covered prefix.  O(1).
    pub fn has_complement_of(&self, lit: &Lit) -> bool {
        let comp_idx = (lit.var as usize) * 2 + ((!lit.neg) as usize);
        self.lit_counter.get(comp_idx).copied().unwrap_or(0) > 0
    }

    #[inline]
    fn ensure_capacity(&mut self, idx: usize) {
        if idx >= self.lit_counter.len() {
            self.lit_counter.resize(idx + 1, 0);
            self.lit_first_pos.resize(idx + 1, None);
        }
    }

    /// Sync our counter/first-pos bookkeeping with a prefix length by popping
    /// entries that are no longer present.
    #[inline]
    fn pop_to(&mut self, target_len: usize) {
        while self.counted.len() > target_len {
            let idx = self.counted.pop().unwrap();
            self.lit_counter[idx] -= 1;
            if self.lit_counter[idx] == 0 {
                self.lit_first_pos[idx] = None;
            }
        }
    }

    /// Record a newly-visible literal.
    #[inline]
    fn push_lit(&mut self, lit: &Lit, pos: usize) {
        let idx = (lit.var as usize) * 2 + (lit.neg as usize);
        self.ensure_capacity(idx);
        self.lit_counter[idx] += 1;
        if self.lit_first_pos[idx].is_none() {
            self.lit_first_pos[idx] = Some(pos);
        }
        self.counted.push(idx);
    }
}

/// What an `on_class(Uncovered)` event should carry.  In the
/// NNF-engine world we have `prefix_positions: &PathPrefix` to copy
/// in; in the arena world we don't have positions at all (the arena
/// engine works in uncovered-only mode where the controller has
/// `needs_cover() == false`).  Both impls funnel through
/// [`BacktrackWhenCoveredController::sync_lits_and_check_cover`] and
/// [`BacktrackWhenCoveredController::emit_uncovered_event`], which
/// take an `UncoveredEventPos` so the shared code doesn't know
/// whether the caller has real positions or empty ones.
enum UncoveredEventPos<'a> {
    Nnf(&'a PathPrefix),
    /// Arena mode: no positions exist.  Empty-vec sentinel.
    EmptyArena,
}

impl<F: FnMut(PathsClass, bool) -> bool> BacktrackWhenCoveredController<F> {
    /// Push any new lits (positions `our_counted_len..lits_len`) into
    /// our bookkeeping mirror, checking each one against the
    /// complement table for a cover.  If a cover lit is found, set
    /// `covered_at_depth`, optionally emit a `Covered` event (NNF mode
    /// only — arena mode is uncovered-only by construction), and
    /// return `false` to indicate the on-class callback asked us to
    /// stop.  Otherwise return `true` (continue).
    ///
    /// `lit_at(pos)` is a closure that returns `&Lit` for prefix
    /// position `pos`.  Both engine modes (NNF-pointer-based,
    /// arena-owned) plug into this via different closure bodies; the
    /// rest of the logic is identical.
    fn sync_lits_and_check_cover(
        &mut self,
        lits_len: usize,
        mut lit_at: impl FnMut(usize) -> Lit,
        positions: &UncoveredEventPos<'_>,
    ) -> bool {
        if self.covered_at_depth.is_some() {
            // Already in a covered subtree — just mirror without checking.
            while self.counted.len() < lits_len {
                let pos = self.counted.len();
                let lit = lit_at(pos);
                self.push_lit(&lit, pos);
            }
            return true;
        }
        while self.counted.len() < lits_len {
            let pos = self.counted.len();
            let lit = lit_at(pos);
            let comp_idx = (lit.var as usize) * 2 + ((!lit.neg) as usize);
            if comp_idx < self.lit_counter.len() && self.lit_counter[comp_idx] > 0 {
                self.path_count += 1;
                self.covered_prefix_count += 1;
                self.push_lit(&lit, pos);
                self.covered_at_depth = Some(lits_len);
                if !self.uncovered_only {
                    // Build + emit Covered.  Only valid for NNF mode
                    // since arena mode has no positions.
                    let prefix_positions = match positions {
                        UncoveredEventPos::Nnf(p) => *p,
                        UncoveredEventPos::EmptyArena => {
                            panic!("uncovered_only=false in arena mode would require \
                                    positions which the arena engine does not provide; \
                                    use `with_on_class_uncovered_only` to construct \
                                    arena-mode controllers");
                        }
                    };
                    let j = self.lit_first_pos[comp_idx]
                        .expect("first_pos must be set when counter > 0");
                    let cpp = CoveredPathPrefix {
                        cover: (prefix_positions[j].clone(), prefix_positions[pos].clone()),
                        prefix: prefix_positions.clone(),
                    };
                    if !self.should_continue_on_paths_class(PathsClass::Covered(cpp), self.hit_limit()) {
                        self.last_lits_len = lits_len;
                        return false;
                    }
                }
                break;
            }
            self.push_lit(&lit, pos);
        }
        // If covered detection happened above, mirror remaining lits
        // without rechecking to keep backtrack pop counts sound.
        while self.counted.len() < lits_len {
            let pos = self.counted.len();
            let lit = lit_at(pos);
            self.push_lit(&lit, pos);
        }
        true
    }
}

impl<F: FnMut(PathsClass, bool) -> bool> PathSearchController for BacktrackWhenCoveredController<F> {
    type OnClass = F;

    fn with_on_class(params: Option<PathParams>, on_class: F) -> Self {
        let params = params.unwrap_or_default();
        Self {
            paths_class_limit: params.paths_class_limit,
            uncovered_path_limit: params.uncovered_path_limit,
            covered_prefix_limit: params.covered_prefix_limit,
            covered_at_depth: None,
            path_count: 0,
            uncovered_path_count: 0,
            covered_prefix_count: 0,
            last_lits_len: 0,
            on_class: Some(on_class),
            lit_counter: Vec::new(),
            lit_first_pos: Vec::new(),
            counted: Vec::new(),
            uncovered_only: false,
        }
    }

    /// "Uncovered-only" flavour of [`Self::with_on_class`].  The controller
    /// still detects complementary pairs (and prunes the subtree
    /// accordingly) but never builds a `CoveredPathPrefix` or delivers a
    /// `PathsClass::Covered` event to `on_class`.  It declares
    /// `needs_cover() == false`, so paired with
    /// [`crate::matrix::NNF::for_each_path_prefix_no_positions`] no per-Lit
    /// `pos.clone()` happens.  Intended for callers like `first_uncovered`
    /// that only want to know whether a non-contradictory path exists.
    fn with_on_class_uncovered_only(params: Option<PathParams>, on_class: F) -> Self {
        let mut this = <Self as PathSearchController>::with_on_class(params, on_class);
        this.uncovered_only = true;
        this
    }

    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        prefix_prod_path: &ProdPath,
        is_complete: bool,
    ) -> Option<usize> {
        if self.hit_limit() {
            return Some(0);
        }
        let lits_len = prefix_literals.len();
        self.pop_to(lits_len);
        if let Some(d) = self.covered_at_depth && lits_len < d {
            self.covered_at_depth = None;
        }
        let ok = self.sync_lits_and_check_cover(
            lits_len,
            |pos| prefix_literals[pos].clone(),
            &UncoveredEventPos::Nnf(prefix_positions),
        );
        if !ok {
            self.last_lits_len = lits_len;
            return Some(0);
        }
        if is_complete {
            if self.covered_at_depth.is_none() {
                self.path_count += 1;
                self.uncovered_path_count += 1;
                let uncov = UncoveredPath {
                    prod_path: prefix_prod_path.clone(),
                    positions: prefix_positions.clone(),
                    lits: prefix_literals.iter().map(|&l| l.clone()).collect(),
                };
                if !self.should_continue_on_paths_class(PathsClass::Uncovered(uncov), self.hit_limit()) {
                    self.last_lits_len = lits_len;
                    return Some(0);
                }
            }
            self.last_lits_len = lits_len;
            return if self.hit_limit() { Some(0) } else { None };
        }
        if self.covered_at_depth.is_some() {
            self.last_lits_len = lits_len;
            return Some(0);
        }
        self.last_lits_len = lits_len;
        None
    }

    fn should_continue_on_paths_class(&mut self, paths_class: PathsClass, hit_limit: bool) -> bool {
        match &mut self.on_class {
            Some(f) => f(paths_class, hit_limit),
            None => true,
        }
    }

    fn needs_cover(&self) -> bool {
        !self.uncovered_only
    }

    fn path_count(&self) -> usize { self.path_count }
    fn covered_prefix_count(&self) -> usize { self.covered_prefix_count }
    fn uncovered_path_count(&self) -> usize { self.uncovered_path_count }
}

/// Arena-engine version of the same cover-detecting controller.
/// Hot logic is shared with the NNF impl via
/// [`BacktrackWhenCoveredController::sync_lits_and_check_cover`]; the
/// only differences are:
///
/// * Lits arrive as `&[Lit]` (owned, from the arena's `lit()` calls)
///   instead of `&Vec<&Lit>` (borrowed from a positions-on NNF
///   traversal).
/// * There are no positions — the arena engine doesn't compute them.
///   So the controller must be in `uncovered_only` mode (constructed
///   via `with_on_class_uncovered_only`); the shared helper panics
///   loudly if a Covered event is about to be emitted in arena mode.
/// * The emitted `UncoveredPath` carries an empty `positions` vec
///   and an empty `prod_path` slot for `cover` is N/A (we only emit
///   Uncovered, not Covered).
impl<F: FnMut(PathsClass, bool) -> bool> ArenaPathSearchController for BacktrackWhenCoveredController<F> {
    fn should_continue_on_prefix(
        &mut self,
        _arena: &NnfArena,
        lits: &[Lit],
        prod_path: &ProdPath,
        is_complete: bool,
    ) -> Option<usize> {
        if self.hit_limit() {
            return Some(0);
        }
        let lits_len = lits.len();
        self.pop_to(lits_len);
        if let Some(d) = self.covered_at_depth && lits_len < d {
            self.covered_at_depth = None;
        }
        let ok = self.sync_lits_and_check_cover(
            lits_len,
            |pos| lits[pos].clone(),
            &UncoveredEventPos::EmptyArena,
        );
        if !ok {
            self.last_lits_len = lits_len;
            return Some(0);
        }
        if is_complete {
            if self.covered_at_depth.is_none() {
                self.path_count += 1;
                self.uncovered_path_count += 1;
                // Arena mode: positions are intentionally empty —
                // downstream consumers (matrix.eff in sat.rs) read
                // `lits` directly and don't need positions for
                // anything.
                let uncov = UncoveredPath {
                    prod_path: prod_path.clone(),
                    positions: Vec::new(),
                    lits: lits.to_vec(),
                };
                if !self.should_continue_on_paths_class(PathsClass::Uncovered(uncov), self.hit_limit()) {
                    self.last_lits_len = lits_len;
                    return Some(0);
                }
            }
            self.last_lits_len = lits_len;
            return if self.hit_limit() { Some(0) } else { None };
        }
        if self.covered_at_depth.is_some() {
            self.last_lits_len = lits_len;
            return Some(0);
        }
        self.last_lits_len = lits_len;
        None
    }

    // sum_ord / prod_ord — fall through to trait defaults (`None`,
    // = declaration order).  This controller has never overridden
    // them in the NNF impl either.
    //
    // No `_arena` parameter is used; we just keep the trait
    // signature for delegation chains.
    #[allow(unused_variables)]
    fn sum_ord(&mut self, _arena: &NnfArena, _parent: NnfId, _children: &[NnfId]) -> Option<Vec<NnfId>> { None }
    #[allow(unused_variables)]
    fn prod_ord(&mut self, _arena: &NnfArena, _parent: NnfId, _children: &[NnfId]) -> Option<Vec<NnfId>> { None }
}

#[cfg(test)]
mod arena_tests {
    use super::*;
    use crate::matrix::Lit;
    use crate::nnf_arena::NnfArena;

    fn lit_p(v: u32) -> crate::matrix::NNF { crate::matrix::NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> crate::matrix::NNF { crate::matrix::NNF::Lit(Lit::neg(v)) }

    /// Smoke test: an Uncovered event fires when the arena engine
    /// reaches a complete non-contradictory path.  Mirrors the
    /// "matrix-method finds an uncovered path = SAT" semantics.
    #[test]
    fn arena_backtrack_emits_uncovered_for_satisfiable() {
        // (a) ∨ (b) — one Sum of two single-Lit clauses; the
        // matrix-method search of this NNF has two complete paths
        // (each one a single lit), neither contradictory → 2
        // Uncovered events.
        let nnf = crate::matrix::NNF::Sum(vec![lit_p(0), lit_p(1)]);
        let arena = NnfArena::from_nnf(&nnf);

        let uncovered_count = std::cell::Cell::new(0u32);
        let mut ctrl = <BacktrackWhenCoveredController<_> as PathSearchController>::with_on_class_uncovered_only(
            None,
            |class: PathsClass, _hl| {
                if matches!(class, PathsClass::Uncovered(_)) {
                    uncovered_count.set(uncovered_count.get() + 1);
                }
                true
            },
        );
        arena.for_each_path_prefix(&mut ctrl);
        // Sum cross-product over two Sums-of-Lit → 1 path per arrangement;
        // here we have Sum with 2 single-Lit children, both visited in
        // the cross-product → 1 complete path with both lits.
        assert!(uncovered_count.get() >= 1, "expected ≥1 Uncovered event, got {}", uncovered_count.get());
    }

    /// Cover detection still fires in arena mode.  Formula:
    /// `Sum(a, ¬a)` — a Sum with two complementary Lits.  Sum is
    /// visit-all (matrix-method cross-product), so any complete path
    /// through this Sum includes *both* `a` and `¬a` lits — a
    /// covered (complementary) prefix.  In uncovered-only mode we
    /// should see 0 Uncovered events and at least 1 covered-prefix
    /// detection.
    #[test]
    fn arena_backtrack_prunes_contradictory_path() {
        let nnf = crate::matrix::NNF::Sum(vec![lit_p(0), lit_n(0)]);
        let arena = NnfArena::from_nnf(&nnf);

        let uncovered_count = std::cell::Cell::new(0u32);
        let mut ctrl = <BacktrackWhenCoveredController<_> as PathSearchController>::with_on_class_uncovered_only(
            None,
            |class: PathsClass, _hl| {
                if matches!(class, PathsClass::Uncovered(_)) {
                    uncovered_count.set(uncovered_count.get() + 1);
                }
                true
            },
        );
        arena.for_each_path_prefix(&mut ctrl);
        assert_eq!(uncovered_count.get(), 0, "(a ∧ ¬a) is unsat → no uncovered paths");
        assert!(ctrl.covered_prefix_count() > 0, "should have detected the a/¬a pair");
    }
}
