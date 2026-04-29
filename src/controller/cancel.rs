//! [`CancelController`] — wraps any [`PathSearchController`] with cooperative
//! cancellation and periodic progress publishing.

use crate::controller::PathSearchController;
use crate::matrix::{Lit, NNF, PathClassificationHandle, PathPrefix, PathsClass, ProdPath};

/// A `PathSearchController` adapter that:
///
/// 1. Polls a [`PathClassificationHandle`] at every traversal step and asks
///    the DFS to backtrack out completely (`Some(0)`) when cancelled.
/// 2. Counts steps and, every 4096 of them, publishes
///    `inner.paths_classified()` to the handle so observers see a smooth
///    increase even when the underlying controller is silent for long
///    stretches (e.g. UNSAT runs that never emit a class).
///
/// All other trait methods (`should_continue_on_paths_class`,
/// `needs_cover`, `sum_ord`, `prod_ord`, `path_count`,
/// `paths_classified`) forward to the inner controller.  This means
/// composing `CancelController` with `BacktrackWhenCoveredController`
/// or `SmartController` Just Works.
pub struct CancelController<C: PathSearchController> {
    pub inner: C,
    pub cancel: PathClassificationHandle,
    step: u64,
}

impl<C: PathSearchController> CancelController<C> {
    pub fn new(inner: C, cancel: PathClassificationHandle) -> Self {
        Self { inner, cancel, step: 0 }
    }

    /// Publish the inner controller's current paths-classified count to the
    /// handle.  Call this once after the DFS completes so the final value is
    /// reflected even if the last 4096-step boundary wasn't crossed.
    pub fn publish_progress(&self) {
        self.cancel.record_paths(self.inner.paths_classified());
    }
}

impl<C: PathSearchController> PathSearchController for CancelController<C> {
    /// `CancelController` is a wrapper — it doesn't construct itself from
    /// `(params, F)`.  Use [`CancelController::new`] with an
    /// already-constructed inner controller.  The trait's
    /// `with_on_class` / `with_on_class_uncovered_only` constructors fall
    /// back to their default-panic impls.
    type OnClass = ();

    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        prefix_prod_path: &ProdPath,
        is_complete: bool,
    ) -> Option<usize> {
        if self.cancel.is_cancelled() {
            return Some(0);
        }
        self.step = self.step.wrapping_add(1);
        if self.step & 0xFFF == 0 {
            self.cancel.record_paths(self.inner.paths_classified());
        }
        self.inner.should_continue_on_prefix(prefix_literals, prefix_positions, prefix_prod_path, is_complete)
    }

    fn should_continue_on_paths_class(&mut self, paths_class: PathsClass, hit_limit: bool) -> bool {
        self.inner.should_continue_on_paths_class(paths_class, hit_limit)
    }

    fn needs_cover(&self) -> bool { self.inner.needs_cover() }

    fn sum_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.sum_ord(children)
    }

    fn prod_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.prod_ord(children)
    }

    fn path_count(&self) -> usize { self.inner.path_count() }
    fn covered_prefix_count(&self) -> usize { self.inner.covered_prefix_count() }
    fn uncovered_path_count(&self) -> usize { self.inner.uncovered_path_count() }
    fn paths_classified(&self) -> f64 { self.inner.paths_classified() }
}
