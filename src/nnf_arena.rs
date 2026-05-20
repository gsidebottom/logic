//! Memory-compact arena representation of an NNF.
//!
//! The canonical [`crate::matrix::NNF`] type is an enum with three
//! variants: `Lit(Lit)`, `Sum(Vec<NNF>)`, `Prod(Vec<NNF>)`.  Rust
//! enums are sized for their largest variant — `Vec<NNF>` is 24 B —
//! so every node, even a `Lit`, occupies 32 B inline (8 B tag/pad +
//! 24 B max-variant body).  And every Sum/Prod's `Vec<NNF>` is a
//! separate heap allocation with its own 24 B header on the heap.
//! On a 10M-node CNF complement (≈ pj2013_k9 territory) that adds
//! up to ~256 MB just for the NNF tree before any search state.
//!
//! `NnfArena` collapses this to a single flat array of fixed-size
//! `NnfNode` records (12 B each) plus one shared `Vec<NnfId>`
//! holding every node's children edges contiguously.  Same
//! information, ≈ 40 % of the bytes:
//!
//! | scheme                  | per node     | per child edge |
//! |-------------------------|--------------|----------------|
//! | `enum NNF` (status quo) | 32 B inline  | (inline)       |
//! | `NnfArena`              | 12 B         | 4 B            |
//!
//! For a 10M-node / 8M-edge complement that's roughly
//! `(120 MB + 32 MB) = 152 MB` vs `256 MB` — about 100 MB saved per
//! NNF copy.
//!
//! ## Layout
//!
//! Each `NnfNode` is `#[repr(C)]` with a kind discriminant byte
//! followed by two `u32` payload words, interpreted by kind:
//!
//! | kind        | `a`                              | `b`            |
//! |-------------|----------------------------------|----------------|
//! | `Lit`       | packed `var | (neg << 31)`       | unused (0)     |
//! | `Sum`/`Prod`| `children_data` start index      | child count    |
//!
//! Children of a Sum/Prod are stored contiguously in
//! `children_data[a .. a + b]` — same CSR-style layout as
//! [`crate::dual::effective_count::EffectiveCountIndex::children_ids`].
//!
//! ## Variable-width assumption
//!
//! `var` is packed into 31 bits, so the maximum supported variable
//! id is `2^31 - 1` (≈ 2.1 billion).  This is well past any CNF
//! input the matrix-method solver is realistically going to see —
//! competition benchmarks top out around 100M variables.
//! Construction `debug_assert!`s on this; a release build with an
//! oversized `var` would silently lose the top bits.

use crate::matrix::{Lit, NNF, PathClassificationHandle, PathsClass, ProdPath, Var};

/// Identifier for a node within an [`NnfArena`].  `u32` (not
/// `usize`) so the per-node footprint is 12 B on every host —
/// indices are the dominant per-node storage and `u32` lets us
/// address up to 4 billion nodes, more than any reasonable matrix
/// search.
pub type NnfId = u32;

/// Kind of an arena node.  Same three cases as the `NNF` enum, but
/// stored as a 1-byte tag so the per-node footprint is compact.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum NnfKind {
    Lit  = 0,
    Sum  = 1,
    Prod = 2,
}

/// One node in the arena.  Fixed-size 12 B with `#[repr(C)]` for
/// predictable layout regardless of compiler reordering.  Field
/// interpretation depends on `kind`; see the module-level docs.
#[derive(Copy, Clone, Debug)]
#[repr(C)]
pub struct NnfNode {
    pub kind: NnfKind,
    /// Padding to 4-byte boundary.  Explicit so the layout is
    /// portable and stable across builds.
    _pad: [u8; 3],
    /// For `Lit`: `var | (neg << 31)`.
    /// For `Sum`/`Prod`: starting index in `NnfArena::children_data`.
    a: u32,
    /// For `Lit`: unused (zero).
    /// For `Sum`/`Prod`: number of children.
    b: u32,
}

const NEG_BIT: u32 = 1 << 31;
const VAR_MASK: u32 = !NEG_BIT;

/// Memory-compact NNF, stored as a flat node array plus a single
/// shared children-id array.  See the module docs for the layout
/// rationale.
///
/// Built from an existing [`NNF`] via [`Self::from_nnf`].  After
/// construction the original NNF can be dropped — the arena owns
/// every byte it needs to drive a search.
pub struct NnfArena {
    nodes: Vec<NnfNode>,
    children_data: Vec<NnfId>,
}

impl NnfArena {
    /// Build an arena by walking `nnf` in DFS pre-order.  Node IDs
    /// are assigned in visit order; the root is always id 0.
    pub fn from_nnf(nnf: &NNF) -> Self {
        let mut arena = Self {
            nodes: Vec::new(),
            children_data: Vec::new(),
        };
        arena.build(nnf);
        arena
    }

    /// Recursive helper for `from_nnf`.  Pushes the current node as
    /// a placeholder, recurses into children (which fills in their
    /// own subtree), then back-fills the parent's `(a, b)` to point
    /// at its children's IDs in `children_data`.
    ///
    /// Allocates a small temporary `Vec<NnfId>` per Sum/Prod for
    /// the children IDs before flushing to `children_data`.  Peak
    /// scratch is `O(tree depth × max branching)` — for CNF
    /// complements (depth 3: Sum → Prod → Lit) that's negligible.
    fn build(&mut self, nnf: &NNF) -> NnfId {
        let id = self.nodes.len() as NnfId;
        // Push a placeholder so child recursion has a stable parent id.
        let node = match nnf {
            NNF::Lit(l) => NnfNode {
                kind: NnfKind::Lit,
                _pad: [0; 3],
                a: pack_lit(l.var, l.neg),
                b: 0,
            },
            NNF::Sum(_) => NnfNode { kind: NnfKind::Sum,  _pad: [0; 3], a: 0, b: 0 },
            NNF::Prod(_) => NnfNode { kind: NnfKind::Prod, _pad: [0; 3], a: 0, b: 0 },
        };
        self.nodes.push(node);

        match nnf {
            NNF::Lit(_) => { /* no children */ }
            NNF::Sum(ch) | NNF::Prod(ch) => {
                let mut child_ids: Vec<NnfId> = Vec::with_capacity(ch.len());
                for c in ch {
                    let cid = self.build(c);
                    child_ids.push(cid);
                }
                let start = self.children_data.len() as u32;
                let n = child_ids.len() as u32;
                self.children_data.extend_from_slice(&child_ids);
                let entry = &mut self.nodes[id as usize];
                entry.a = start;
                entry.b = n;
            }
        }
        id
    }

    /// Total number of nodes in the arena.
    pub fn n_nodes(&self) -> usize { self.nodes.len() }

    /// The root node id (always 0; the first node pushed during
    /// `from_nnf`).
    pub fn root(&self) -> NnfId { 0 }

    /// Kind of node `id`.
    pub fn kind(&self, id: NnfId) -> NnfKind { self.nodes[id as usize].kind }

    /// Children NodeIds of node `id`, in declaration order.  Empty
    /// slice for `Lit` leaves.
    pub fn children(&self, id: NnfId) -> &[NnfId] {
        let node = &self.nodes[id as usize];
        match node.kind {
            NnfKind::Lit => &[],
            _ => {
                let start = node.a as usize;
                let end = start + node.b as usize;
                &self.children_data[start..end]
            }
        }
    }

    /// The `Lit` payload of node `id`.  Panics in debug builds if
    /// `id` is not a `Lit`.
    pub fn lit(&self, id: NnfId) -> Lit {
        let node = &self.nodes[id as usize];
        debug_assert!(matches!(node.kind, NnfKind::Lit),
            "lit() called on non-Lit node id={}, kind={:?}", id, node.kind);
        let v = node.a;
        Lit { var: (v & VAR_MASK) as Var, neg: (v & NEG_BIT) != 0 }
    }

    /// Approximate memory footprint of the arena, in bytes.  Used
    /// for instrumentation; not exact (excludes Vec spare capacity
    /// beyond `len`, allocator headers, etc.).
    pub fn approx_size_bytes(&self) -> usize {
        self.nodes.len() * std::mem::size_of::<NnfNode>()
            + self.children_data.len() * std::mem::size_of::<NnfId>()
    }
}

/// Arena-native path-search controller — same role as
/// [`crate::controller::PathSearchController`] but with hooks taking
/// `NnfId` instead of `&NNF`.  Used by [`NnfArena::for_each_path_prefix`]
/// to drive the arena's DFS traversal.
///
/// Why a parallel trait instead of reusing [`PathSearchController`]?
/// The status-quo trait's `sum_ord(&NNF, &[NNF])` and
/// `prod_ord(&NNF, &[NNF])` signatures are deeply embedded in the
/// existing engine (`for_each_path_prefix_ord`) and four downstream
/// implementations (`CdclController`, `SmartController`,
/// `BacktrackWhenCoveredController`, `EffectiveCountWrapper`) that
/// pattern-match on `&NNF` for variant cases and lit access.  An
/// arena world has neither — children come as `&[NnfId]` and lit
/// payloads come from the arena.  Forcing the existing trait to be
/// generic over both representations would make every implementation
/// substantially more complex, so for now we keep the two universes
/// separate: the arena trait, engine, and (eventually) arena-native
/// versions of each controller live alongside the NNF-based ones.
pub trait ArenaPathSearchController {
    /// Visit-order hook for the children of a Sum node.  Mirrors
    /// [`PathSearchController::sum_ord`].  `arena` is the arena
    /// being traversed; `parent` and the returned `NnfId`s all
    /// refer to nodes in it.  `children` is `arena.children(parent)`
    /// for convenience (so impls don't have to re-fetch it).  Return
    /// `None` for declaration order (no allocation), `Some(order)`
    /// to permute / re-order.
    ///
    /// Why pass `arena` to every hook instead of having the
    /// controller store an `&NnfArena` field?  Lifetime and
    /// ownership.  The arena is owned by whatever drives the
    /// search; the controllers are wrappers that hold all the
    /// mutable search state.  Passing `arena` as a method argument
    /// keeps both lifetimes independent and lets controllers stack
    /// (wrappers / wrapped) without each layer having to manage
    /// arena ownership explicitly.
    fn sum_ord(&mut self, _arena: &NnfArena, _parent: NnfId, _children: &[NnfId]) -> Option<Vec<NnfId>> {
        None
    }

    /// Visit-order hook for the alternatives of a Prod node.
    /// Mirrors [`PathSearchController::prod_ord`].  See [`Self::sum_ord`]
    /// for the `arena` argument rationale.
    fn prod_ord(&mut self, _arena: &NnfArena, _parent: NnfId, _children: &[NnfId]) -> Option<Vec<NnfId>> {
        None
    }

    /// Called at every prefix step (every Lit visit, plus at the
    /// final empty-tail visit of a complete path).  Same semantics
    /// as [`PathSearchController::should_continue_on_prefix`] —
    /// returning `None` continues, `Some(0)` backs up one level,
    /// `Some(k)` backs up `k+1` levels.  `arena` is passed for the
    /// same reason as in [`Self::sum_ord`].
    fn should_continue_on_prefix(
        &mut self,
        _arena: &NnfArena,
        _lits: &[Lit],
        _prod_path: &ProdPath,
        _is_complete: bool,
    ) -> Option<usize> {
        None
    }
}

impl NnfArena {
    /// DFS the arena, invoking the controller's hooks.  Same
    /// traversal semantics as
    /// [`crate::matrix::NNF::for_each_path_prefix_with_controller`]
    /// — drive the matrix-method search by reporting each lit
    /// prefix and giving the controller a chance to re-order
    /// Sum/Prod children — but built on the arena's `NnfId`
    /// vocabulary and iterating the flat node arrays instead of
    /// pattern-matching on an enum.
    ///
    /// The traversal is recursive (matches the existing NNF-based
    /// engine's structure for ease of validation); converting to
    /// an explicit work stack is a follow-up if recursion-depth
    /// stack budget becomes a concern on giant inputs.
    pub fn for_each_path_prefix<C: ArenaPathSearchController>(&self, ctrl: &mut C) {
        let mut lits: Vec<Lit>      = Vec::new();
        let mut prod_path: ProdPath = ProdPath::new();
        self.traverse(
            self.root(), &mut lits, &mut prod_path, ctrl,
            &mut |arena, lits, path, ctrl| ctrl.should_continue_on_prefix(arena, lits, path, true),
        );
    }

    /// Recursive driver mirroring `traverse` in
    /// [`crate::matrix::NNF::for_each_path_prefix_ord`].  `then` is
    /// the continuation invoked once the subtree at `m` has been
    /// fully visited — for the top-level entry that's the
    /// `is_complete=true` report; nested Sum frames pass their
    /// "visit the next sibling" continuation.
    ///
    /// Returns the same `Option<usize>` backtrack code as the
    /// NNF-based engine: `None` continues forward, `Some(0)` backs
    /// up one level, `Some(k)` decrements and bubbles up.
    ///
    /// `then` takes `&mut`-borrows of the same `lits`/`prod_path`
    /// that the caller owns, so nested Sum frames can keep pushing
    /// into them across the continuation chain.
    fn traverse<C: ArenaPathSearchController>(
        &self,
        m: NnfId,
        lits: &mut Vec<Lit>,
        prod_path: &mut ProdPath,
        ctrl: &mut C,
        then: &mut dyn FnMut(&NnfArena, &mut Vec<Lit>, &mut ProdPath, &mut C) -> Option<usize>,
    ) -> Option<usize> {
        match self.kind(m) {
            NnfKind::Lit => {
                let l = self.lit(m);
                lits.push(l);
                let r = match ctrl.should_continue_on_prefix(self, lits, prod_path, false) {
                    None    => then(self, lits, prod_path, ctrl),
                    Some(k) => Some(k),
                };
                lits.pop();
                r
            }
            NnfKind::Prod => {
                let children = self.children(m);
                let order = ctrl.prod_ord(self, m, children);
                let len = order.as_ref().map_or(children.len(), |o| o.len());
                for ord_idx in 0..len {
                    let (i, child) = match &order {
                        Some(o) => {
                            let c = o[ord_idx];
                            let orig_idx = children.iter().position(|&id| id == c)
                                .expect("prod_ord returned a NodeId not in children");
                            (orig_idx, c)
                        }
                        None => (ord_idx, children[ord_idx]),
                    };
                    prod_path.push(i);
                    let r = match ctrl.should_continue_on_prefix(self, lits, prod_path, false) {
                        None    => self.traverse(child, lits, prod_path, ctrl, then),
                        Some(k) => Some(k),
                    };
                    prod_path.pop();
                    match r {
                        None | Some(0) => continue,
                        Some(k)        => return Some(k - 1),
                    }
                }
                None
            }
            NnfKind::Sum => {
                let children = self.children(m);
                let order = ctrl.sum_ord(self, m, children);
                self.traverse_sum(children, order.as_deref(), 0, lits, prod_path, ctrl, then)
            }
        }
    }

    fn traverse_sum<C: ArenaPathSearchController>(
        &self,
        children: &[NnfId],
        order:    Option<&[NnfId]>,
        ord_idx:  usize,
        lits: &mut Vec<Lit>,
        prod_path: &mut ProdPath,
        ctrl: &mut C,
        then: &mut dyn FnMut(&NnfArena, &mut Vec<Lit>, &mut ProdPath, &mut C) -> Option<usize>,
    ) -> Option<usize> {
        let len = order.map_or(children.len(), |o| o.len());
        if ord_idx >= len {
            return then(self, lits, prod_path, ctrl);
        }
        let child = match order {
            Some(o) => o[ord_idx],
            None    => children[ord_idx],
        };
        let r = self.traverse(child, lits, prod_path, ctrl, &mut |arena, lits, path, ctrl| {
            arena.traverse_sum(children, order, ord_idx + 1, lits, path, ctrl, then)
        });
        match r {
            None | Some(0) => None,
            Some(k)        => Some(k - 1),
        }
    }
}

impl NnfArena {
    /// Arena counterpart of
    /// [`crate::matrix::NNF::classify_paths_with_nnf`].  Takes the
    /// arena by value, moves it into a `spawn_blocking` task that
    /// runs the arena DFS via the restart-loop driver.  Returns the
    /// same `(JoinHandle, Receiver, PathClassificationHandle)`
    /// triple the NNF engine returns, so callers can use a single
    /// uniform pattern regardless of which engine fronts the search.
    ///
    /// `controller_builder(&NnfArena, tx) -> Controller` is the
    /// hook for callers to construct their controller stack with
    /// the same arena the engine will walk — same role as in the
    /// NNF version, gives callers the arena reference they need to
    /// build their `EffectiveCountIndex` (or similar) keyed by
    /// `NnfId`.
    pub fn classify_paths_with_arena<C, B>(
        self,
        buffer_size: usize,
        controller_builder: B,
    ) -> (
        tokio::task::JoinHandle<Result<(), Box<dyn std::error::Error + Send>>>,
        tokio::sync::mpsc::Receiver<(PathsClass, bool)>,
        PathClassificationHandle,
    )
    where
        C: ArenaPathSearchController + crate::controller::PathSearchController + Send + 'static,
        B: FnOnce(&NnfArena, tokio::sync::mpsc::Sender<(PathsClass, bool)>) -> C + Send + 'static,
    {
        let (tx, rx) = tokio::sync::mpsc::channel::<(PathsClass, bool)>(buffer_size);
        let cancel = PathClassificationHandle::new();
        let cancel_for_thread = cancel.clone();
        let handle = tokio::task::spawn_blocking(move || {
            let inner = controller_builder(&self, tx);
            let cancel_check = cancel_for_thread.clone();
            let mut ctrl = crate::controller::CancelController::new(inner, cancel_for_thread);
            // Restart loop — same as the NNF engine's restart loop
            // in `classify_paths_with_nnf`.  Re-invokes the DFS
            // when the controller asks for a Luby restart;
            // otherwise exits after a single full traversal.
            loop {
                if cancel_check.is_cancelled() { break; }
                self.for_each_path_prefix(&mut ctrl);
                if cancel_check.is_cancelled() { break; }
                if !<crate::controller::CancelController<C> as crate::controller::PathSearchController>::is_restart_pending(&ctrl) {
                    break;
                }
                <crate::controller::CancelController<C> as crate::controller::PathSearchController>::complete_restart(&mut ctrl);
            }
            crate::controller::CancelController::<C>::publish_progress(&ctrl);
            Ok::<(), Box<dyn std::error::Error + Send>>(())
        });
        (handle, rx, cancel)
    }
}

/// Pack a `(var, neg)` pair into a single `u32`.  Top bit is `neg`,
/// low 31 bits are `var`.  Debug-asserts that `var` fits.
fn pack_lit(var: Var, neg: bool) -> u32 {
    debug_assert!(var <= VAR_MASK,
        "var={} exceeds 31-bit arena packing limit (max {})",
        var, VAR_MASK);
    (var & VAR_MASK) | if neg { NEG_BIT } else { 0 }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::matrix::Lit;

    fn lit_p(v: Var) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: Var) -> NNF { NNF::Lit(Lit::neg(v)) }

    /// Round-trip a tiny NNF → arena and verify every node's kind,
    /// children, and Lit payload matches.
    #[test]
    fn arena_round_trip_basic() {
        let nnf = NNF::Sum(vec![
            lit_p(0),
            NNF::Prod(vec![lit_p(1), lit_n(2)]),
            NNF::Prod(vec![lit_n(3), lit_p(4), lit_n(5)]),
        ]);
        let a = NnfArena::from_nnf(&nnf);

        // 1 Sum + 1 Lit + 1 Prod + 2 Lit + 1 Prod + 3 Lit = 9 nodes.
        assert_eq!(a.n_nodes(), 9);
        assert_eq!(a.kind(a.root()), NnfKind::Sum);

        // Root's three children correspond to the three Sum members
        // in DFS-preorder order.
        let root_children = a.children(a.root());
        assert_eq!(root_children.len(), 3);

        // First child is the lone Lit(0).
        assert_eq!(a.kind(root_children[0]), NnfKind::Lit);
        assert_eq!(a.lit(root_children[0]), Lit::pos(0));

        // Second child is a Prod with two Lit children.
        let c1 = root_children[1];
        assert_eq!(a.kind(c1), NnfKind::Prod);
        let c1_ch = a.children(c1);
        assert_eq!(c1_ch.len(), 2);
        assert_eq!(a.lit(c1_ch[0]), Lit::pos(1));
        assert_eq!(a.lit(c1_ch[1]), Lit::neg(2));

        // Third child is a Prod with three Lit children.
        let c2 = root_children[2];
        assert_eq!(a.kind(c2), NnfKind::Prod);
        let c2_ch = a.children(c2);
        assert_eq!(c2_ch.len(), 3);
        assert_eq!(a.lit(c2_ch[0]), Lit::neg(3));
        assert_eq!(a.lit(c2_ch[1]), Lit::pos(4));
        assert_eq!(a.lit(c2_ch[2]), Lit::neg(5));
    }

    /// A single Lit is a degenerate but valid NNF.  The arena
    /// should have exactly one node and the root should be that Lit.
    #[test]
    fn arena_single_lit() {
        let nnf = lit_n(42);
        let a = NnfArena::from_nnf(&nnf);
        assert_eq!(a.n_nodes(), 1);
        assert_eq!(a.kind(a.root()), NnfKind::Lit);
        assert_eq!(a.lit(a.root()), Lit::neg(42));
        assert!(a.children(a.root()).is_empty());
    }

    /// Empty Sum / Prod are also valid NNF shapes (degenerate but
    /// the engine handles them).  Arena should preserve them.
    #[test]
    fn arena_empty_sum_and_prod() {
        let nnf = NNF::Sum(vec![NNF::Prod(vec![]), NNF::Sum(vec![])]);
        let a = NnfArena::from_nnf(&nnf);
        assert_eq!(a.n_nodes(), 3);
        assert_eq!(a.kind(a.root()), NnfKind::Sum);
        let ch = a.children(a.root());
        assert_eq!(ch.len(), 2);
        assert_eq!(a.kind(ch[0]), NnfKind::Prod);
        assert!(a.children(ch[0]).is_empty());
        assert_eq!(a.kind(ch[1]), NnfKind::Sum);
        assert!(a.children(ch[1]).is_empty());
    }

    /// Verify the bit-packing roundtrips for `Lit` polarity and a
    /// large-but-valid `var`.
    #[test]
    fn arena_lit_packing_roundtrip() {
        for &var in &[0u32, 1, 100, 65535, 1 << 20, (1u32 << 31) - 1] {
            for &neg in &[false, true] {
                let nnf = NNF::Lit(Lit { var, neg });
                let a = NnfArena::from_nnf(&nnf);
                let l = a.lit(a.root());
                assert_eq!(l.var, var, "var mismatch for ({}, {})", var, neg);
                assert_eq!(l.neg, neg, "neg mismatch for ({}, {})", var, neg);
            }
        }
    }

    /// Node size sanity: the whole point of the arena is the
    /// compact per-node footprint.  Fail loudly if a layout change
    /// silently regresses this.
    #[test]
    fn arena_node_size_is_compact() {
        let sz = std::mem::size_of::<NnfNode>();
        assert!(sz <= 12,
            "NnfNode should be ≤ 12 bytes (got {}); regression in the \
             arena's per-node footprint",
            sz);
    }

    // ─── Engine smoke tests ────────────────────────────────────────────

    /// Trivial collector: records the lits at every `is_complete`
    /// callback (i.e. every complete path through the NNF).  Used
    /// to verify that the arena engine produces the same enumeration
    /// of complete paths as the existing NNF engine.
    struct PathCollector {
        complete_paths: Vec<Vec<Lit>>,
    }
    impl PathCollector {
        fn new() -> Self { Self { complete_paths: Vec::new() } }
    }
    impl ArenaPathSearchController for PathCollector {
        fn should_continue_on_prefix(
            &mut self,
            _arena: &NnfArena,
            lits: &[Lit],
            _prod_path: &ProdPath,
            is_complete: bool,
        ) -> Option<usize> {
            if is_complete {
                self.complete_paths.push(lits.to_vec());
            }
            None
        }
    }

    /// Drive the NNF-based engine with a controller that does the
    /// same path-collection job — gives us a ground-truth list of
    /// paths to compare the arena engine against.
    fn collect_nnf_paths(nnf: &NNF) -> Vec<Vec<Lit>> {
        let collected = std::cell::RefCell::new(Vec::<Vec<Lit>>::new());
        nnf.for_each_path_prefix_ord(
            |_, _| None,
            |_, _| None,
            |lits, _positions, _path, is_complete| {
                if is_complete {
                    let owned: Vec<Lit> = lits.iter().map(|l| (*l).clone()).collect();
                    collected.borrow_mut().push(owned);
                }
                None
            },
        );
        collected.into_inner()
    }

    /// Same paths whether walked via NNF or arena, on a flat
    /// Sum-of-Prods shape (the matrix-method workhorse).
    #[test]
    fn arena_engine_matches_nnf_engine_flat() {
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_n(1)]),
            NNF::Prod(vec![lit_n(0), lit_p(2), lit_n(3)]),
            lit_p(4),
        ]);
        let nnf_paths = collect_nnf_paths(&nnf);
        let arena = NnfArena::from_nnf(&nnf);
        let mut c = PathCollector::new();
        arena.for_each_path_prefix(&mut c);
        assert_eq!(c.complete_paths, nnf_paths);
        assert!(!c.complete_paths.is_empty(), "should have found at least one path");
    }

    /// Nested-Sum case: the arena engine's Sum-cross-product
    /// logic should produce the same multi-Sum cross-product
    /// enumeration as the NNF engine.
    #[test]
    fn arena_engine_matches_nnf_engine_nested() {
        let nnf = NNF::Sum(vec![
            NNF::Sum(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_p(2), lit_p(3)]),
        ]);
        let nnf_paths = collect_nnf_paths(&nnf);
        let arena = NnfArena::from_nnf(&nnf);
        let mut c = PathCollector::new();
        arena.for_each_path_prefix(&mut c);
        assert_eq!(c.complete_paths, nnf_paths);
    }

    /// Sum-of-Prod cross-product semantics: Sum visits every
    /// child, each Prod picks one alt, so the complete-path count
    /// for `Sum[ Prod[a,b], Prod[c,d] ]` is `2 × 2 = 4`.
    #[test]
    fn arena_engine_sum_cross_product() {
        struct Counter { complete: usize }
        impl ArenaPathSearchController for Counter {
            fn should_continue_on_prefix(
                &mut self, _arena: &NnfArena, _lits: &[Lit], _prod_path: &ProdPath, is_complete: bool,
            ) -> Option<usize> {
                if is_complete { self.complete += 1; }
                None
            }
        }
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),
            NNF::Prod(vec![lit_p(2), lit_p(3)]),
        ]);
        let arena = NnfArena::from_nnf(&nnf);
        let mut c = Counter { complete: 0 };
        arena.for_each_path_prefix(&mut c);
        assert_eq!(c.complete, 4, "Sum cross-product over 2 Prods of 2 alts");
    }

    /// Backtrack signal actually prunes: a controller that returns
    /// `Some(0)` the moment it sees lit_p(2) on the prefix should
    /// cut every path that descends into the second Prod's alts
    /// after picking `c`.  Specifically the cross-product has 4
    /// paths: (a,c), (a,d), (b,c), (b,d); pruning at `c` kills (a,c)
    /// and (b,c) → 2 complete paths instead of 4.
    #[test]
    fn arena_engine_honours_backtrack_signal() {
        struct PruneAfterC { complete: usize }
        impl ArenaPathSearchController for PruneAfterC {
            fn should_continue_on_prefix(
                &mut self, _arena: &NnfArena, lits: &[Lit], _prod_path: &ProdPath, is_complete: bool,
            ) -> Option<usize> {
                if lits.iter().any(|l| l.var == 2 && !l.neg) {
                    return Some(0);   // back up one level
                }
                if is_complete { self.complete += 1; }
                None
            }
        }
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_p(0), lit_p(1)]),    // a, b
            NNF::Prod(vec![lit_p(2), lit_p(3)]),    // c, d
        ]);
        let arena = NnfArena::from_nnf(&nnf);
        let mut c = PruneAfterC { complete: 0 };
        arena.for_each_path_prefix(&mut c);
        assert_eq!(c.complete, 2, "pruning at c should leave (*, d) only");
    }
}
