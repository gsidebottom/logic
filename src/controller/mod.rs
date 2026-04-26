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
pub mod smart;

pub use backtrack::BacktrackWhenCoveredController;
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

    /// Order in which to visit a Sum node's children.  Default: declaration
    /// order.  Returning a permuted, filtered, or reordered vector lets a
    /// controller drive the search — e.g. visit the most-constrained subtree
    /// first to detect conflicts early.
    fn sum_ord<'a>(&mut self, children: &'a [NNF]) -> Vec<(usize, &'a NNF)> {
        NNF::natural_order(children)
    }

    /// Order in which to visit a Prod node's alternatives.  Default:
    /// declaration order.  At Prod the DFS picks one alternative at a time;
    /// reordering changes which alternative is tried first (and therefore
    /// what the search descends into eagerly).
    fn prod_ord<'a>(&mut self, children: &'a [NNF]) -> Vec<(usize, &'a NNF)> {
        NNF::natural_order(children)
    }
}
