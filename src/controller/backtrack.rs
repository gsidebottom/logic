//! [`BacktrackWhenCoveredController`] — cover-aware DFS pruning controller.

use crate::controller::PathSearchController;
use crate::matrix::{
    CoveredPathPrefix, Lit, PathParams, PathPrefix, PathsClass, ProdPath,
};

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
        // Sync our counter mirror with the DFS stack: pop any entries that the
        // traversal has since popped.  This must run every call because the DFS
        // only invokes us at certain boundaries; between calls, lits may have
        // grown and shrunk multiple times.
        self.pop_to(prefix_literals.len());

        // If we backtracked past the depth where the current covered pair was
        // first detected, the pair no longer straddles the prefix and we can
        // resume checking.
        if let Some(d) = self.covered_at_depth && prefix_literals.len() < d {
            self.covered_at_depth = None;
        }

        // Process new literals, one at a time, with O(1) complement lookup.
        if self.covered_at_depth.is_none() {
            while self.counted.len() < prefix_literals.len() {
                let pos = self.counted.len();
                let lit = prefix_literals[pos];
                let comp_idx = (lit.var as usize) * 2 + ((!lit.neg) as usize);
                if comp_idx < self.lit_counter.len() && self.lit_counter[comp_idx] > 0 {
                    self.path_count += 1;
                    self.covered_prefix_count += 1;
                    // Keep the bookkeeping in sync — we still push this lit so a
                    // later pop_to() can undo it cleanly when the DFS retreats.
                    self.push_lit(lit, pos);
                    self.covered_at_depth = Some(prefix_literals.len());
                    // Build + emit the covered event only when requested.  The
                    // uncovered-only flavour skips both the allocations and
                    // the callback, which makes this hot path allocation-free.
                    if !self.uncovered_only {
                        let j = self.lit_first_pos[comp_idx]
                            .expect("first_pos must be set when counter > 0");
                        let cpp = CoveredPathPrefix {
                            cover: (prefix_positions[j].clone(), prefix_positions[pos].clone()),
                            prefix: prefix_positions.clone(),
                        };
                        if !self.should_continue_on_paths_class(PathsClass::Covered(cpp), self.hit_limit()) {
                            self.last_lits_len = prefix_literals.len();
                            return Some(0);
                        }
                    }
                    break;
                }
                self.push_lit(lit, pos);
            }
        }
        // If covered detection happened above (or we were already in a covered
        // subtree), there may still be lits in `prefix_literals` that we haven't
        // mirrored — mirror them without rechecking so backtrack stays sound.
        while self.counted.len() < prefix_literals.len() {
            let pos = self.counted.len();
            let lit = prefix_literals[pos];
            self.push_lit(lit, pos);
        }

        if is_complete {
            if self.covered_at_depth.is_none() {
                self.path_count += 1;
                self.uncovered_path_count += 1;
                if !self.should_continue_on_paths_class(PathsClass::Uncovered(prefix_prod_path.clone()), self.hit_limit()) {
                    self.last_lits_len = prefix_literals.len();
                    return Some(0);
                }
            }
            self.last_lits_len = prefix_literals.len();
            return if self.hit_limit() { Some(0) } else { None };
        }
        // Prod selection — prune if covered.
        if self.covered_at_depth.is_some() {
            self.last_lits_len = prefix_literals.len();
            return Some(0);
        }
        self.last_lits_len = prefix_literals.len();
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
