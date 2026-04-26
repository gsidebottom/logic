//! Path-search controllers driving [`crate::matrix::NNF::for_each_path_prefix`].
//!
//! This module hosts the [`PathSearchController`] trait plus a couple of
//! ready-made implementations:
//!
//! * [`backtrack::BacktrackWhenCoveredController`] — the workhorse used by
//!   `Matrix::valid` / `Matrix::satisfiable` for cover-aware DFS pruning.
//! * [`smart::SmartSatController`] — a SAT-search controller layering
//!   cross-clause unit propagation on top of `BacktrackWhenCoveredController`.

pub mod backtrack;
pub mod cancel;
pub mod smart;

pub use backtrack::BacktrackWhenCoveredController;
pub use cancel::CancelController;
pub use smart::SmartSatController;

use crate::matrix::{Lit, NNF, PathPrefix, PathsClass, ProdPath};

/// Controls depth-first path-prefix traversal.
///
/// The DFS calls `should_continue_on_prefix` at every Prod child entry and at
/// every path completion; `sum_ord` / `prod_ord` once per Sum / Prod node to
/// pick the order in which children are visited.  The trait surfaces all of
/// the controls that [`crate::matrix::NNF::for_each_path_prefix`] exposes —
/// including the generalized backtracking via `Option<usize>` and the
/// per-node ordering hooks — so a controller can both decide *what* to
/// backtrack and *how* the search visits Sum/Prod children.
pub trait PathSearchController {
    /// Called at each step of the traversal.
    /// - `None` — continue forward.
    /// - `Some(0)` — backtrack one level (pop the latest item from `pos` and
    ///   `path` and try the next sibling).
    /// - `Some(i)` for `i > 0` — backtrack `i + 1` levels.  Use this for
    ///   non-chronological backjumping when the controller knows that no
    ///   choice in the recent stack frames can resolve the current conflict.
    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        complete_prod_path: Option<&ProdPath>,
    ) -> Option<usize>;

    /// Called on each classified path. Return `true` to continue
    /// classifying paths, `false` to stop the traversal.
    fn should_continue_on_paths_class(&mut self, _paths_class: PathsClass, _hit_limit: bool) -> bool {
        true
    }

    /// Whether this controller consumes cover certificates.  Default is
    /// `true` for back-compat.  Returning `false` is a contract: the
    /// controller promises it won't read `prefix_positions` and won't care
    /// about `PathsClass::Covered` events.  In return the driver may skip
    /// the per-Lit `pos.clone()` bookkeeping and the per-emission
    /// `prefix_positions.clone()` — see
    /// [`crate::matrix::NNF::for_each_path_prefix_no_positions`] and
    /// [`crate::matrix::NNF::classify_paths_uncovered_only`].
    fn needs_cover(&self) -> bool { true }

    /// Order in which to visit a Sum node's children.
    ///
    /// Return `None` to use declaration order (the default — and the
    /// allocation-free fast path inside the DFS engine).  Return
    /// `Some(order)` to permute, filter, or otherwise reshape the
    /// traversal — e.g. visit the most-constrained subtree first to detect
    /// conflicts early.  The `(index, child)` pairs in `order` must
    /// reference the original `children` slice; indices are the absolute
    /// positions used to record the path.
    fn sum_ord<'a>(&mut self, _children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        None
    }

    /// Order in which to visit a Prod node's alternatives.  Same `None` =
    /// declaration order convention as [`Self::sum_ord`].  At Prod the DFS
    /// picks one alternative at a time, so reordering changes which
    /// alternative is tried first (and therefore what the search descends
    /// into eagerly).
    fn prod_ord<'a>(&mut self, _children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        None
    }

    /// Total classified path prefixes (covered + uncovered) seen so far.
    /// Default `0` for controllers that don't track this.  Wrappers like
    /// [`cancel::CancelController`] surface the inner controller's count for
    /// progress publishing.
    fn path_count(&self) -> usize { 0 }

    /// Floating-point count of *paths* classified so far — meaning the
    /// number of complete paths through the matrix that have been resolved,
    /// either by reaching them uncovered or by detecting a cover that
    /// dominates them.  Defaults to `path_count() as f64`; the
    /// uncovered-only flavour can override to weight covered detections by
    /// the count of paths each one stands for.
    fn paths_classified(&self) -> f64 { self.path_count() as f64 }
}
