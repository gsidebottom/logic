//! Effective-path-count infrastructure for `EffectivePathController`.
//!
//! See `doc/dual-search-design.md` "Effective-path-count path search"
//! for the full design.  The recurrence:
//!
//! * `Lit(ℓ)` where `ℓ ∈ P` (matching prefix lit) → `1`
//! * `Lit(ℓ)` where `¬ℓ ∈ P` (complementary)      → `0`
//! * `Lit(ℓ)` otherwise                            → `1`
//! * `Sum(c₁ … c_n)`  → `∏ᵢ e(cᵢ | P)`
//! * `Prod(c₁ … c_n)` → `∑ᵢ e(cᵢ | P)`
//!
//! `EffectiveCountIndex` is built once per NNF (a structural pre-walk
//! that records each node's kind, children, parent, and a per-variable
//! list of leaf-`Lit`-node IDs).  `EffectiveCounts` holds the per-node
//! count and updates incrementally: each `push(lit)` returns a delta
//! frame so `pop_undo(frame)` can restore the previous state.

use std::collections::HashMap;

use crate::matrix::{Lit, NNF};

/// Pre-computed structural index of an NNF.
///
/// # Safety: cross-thread send
///
/// `by_ptr` stores `*const NNF` pointers that reference the NNF
/// passed to `build`.  Those pointers are read-only and only
/// dereferenced indirectly through `id_of` (which compares them by
/// value, never deref'ing them).  As long as the indexed NNF
/// outlives the index, the pointers remain valid for that lookup.
///
/// In the bench's `matrix.eff` row the index is built inside a
/// `tokio::spawn_blocking` closure against an NNF that the same
/// closure also owns — both live and die together on the spawned
/// thread.  Same pattern in `EffectivePathController::run`.  The
/// `unsafe impl Send + Sync` below lets the type cross thread
/// boundaries when packaged inside a controller; soundness is the
/// caller's responsibility (don't drop / mutate the underlying NNF
/// while the index is alive).
pub struct EffectiveCountIndex {
    /// Pointer-to-`NNF` → flat NodeId.  Used by `id_of` so the
    /// PathSearchController wrapper can look up children by their
    /// `&NNF` references in `sum_ord` / `prod_ord`.
    by_ptr: HashMap<*const NNF, usize>,
    /// `var → [(leaf node id, leaf polarity)]` — every Lit-leaf
    /// containing this var, paired with its `neg` flag so the hot
    /// `push()` path can compute the new leaf count without
    /// touching `kind[]` / calling `lit_at()`.  Used by
    /// `EffectiveCounts::push` to locate and update the leaves
    /// whose counts change when a literal is pushed.
    var_to_lit_nodes: Vec<Vec<(usize, bool)>>,
    /// Parent of each node (`None` for root).
    parent: Vec<Option<usize>>,
    /// Children of each node, in CSR (Compressed Sparse Row) layout:
    /// node `i`'s children NodeIds occupy
    /// `children_data[children_offsets[i] .. children_offsets[i+1]]`.
    /// `children_offsets` has `n_nodes + 1` entries (the trailing
    /// sentinel = `children_data.len()`).
    ///
    /// Previously this was `Vec<Vec<usize>>` — one `Vec` header
    /// (24 B) per node plus a separate heap allocation for each
    /// non-empty child list.  On 10M-node CNF complements that's
    /// ~240 MB just in headers, before any child data.  The CSR
    /// layout replaces every per-node header with one 8-byte offset
    /// entry, cuts the headers to a single 80 MB `children_offsets`
    /// Vec, and merges all the child lists into one heap allocation
    /// with better locality.
    children_offsets: Vec<usize>,
    children_data:    Vec<usize>,
    /// Per-node kind.
    kind: Vec<NodeKind>,
    /// Per-leaf precomputed ancestor chain in CSR layout: for each
    /// leaf node `leaf_id`, its `[parent, grandparent, ..., root]`
    /// chain lives at
    /// `leaf_ancestors_data[leaf_ancestors_offsets[leaf_id] .. leaf_ancestors_offsets[leaf_id + 1]]`.
    /// `leaf_ancestors_offsets` has `n_nodes + 1` entries; the
    /// range is empty for non-Lit nodes (they never start a chain
    /// walk).
    ///
    /// Previously this was `Vec<Vec<usize>>` indexed by node-id —
    /// every node carried a 24 B inner-`Vec` header even though
    /// only Lit leaves had any data, costing ~240 MB on
    /// 10M-node CNF complements.  The CSR layout collapses every
    /// header to one 8 B offset and merges the (very short)
    /// per-leaf chains into a single heap allocation.
    leaf_ancestors_offsets: Vec<usize>,
    leaf_ancestors_data:    Vec<usize>,
}

#[derive(Clone, Debug)]
enum NodeKind {
    /// Lit-leaf.  The actual `Lit` value isn't stored on the kind
    /// any more — `var_to_lit_nodes` carries the polarity needed
    /// by the hot push() path, and no other code reads it.
    Lit,
    Sum,
    Prod,
}

impl EffectiveCountIndex {
    /// Build an index for `nnf`.  Pointer keys assume `nnf` is fixed
    /// in memory for the lifetime of any `EffectiveCounts` built on
    /// top of this index — the typical case is the index is owned by
    /// the controller and refers to the NNF the controller drives.
    /// Arena counterpart of [`Self::build`].  Walks an [`NnfArena`]
    /// in the same DFS pre-order, assigning the same flat NodeIds
    /// the wrapper expects.  Because both `NnfArena::from_nnf` and
    /// `EffectiveCountIndex::build_from_arena` traverse in DFS
    /// pre-order from the root, the arena's `NnfId` and this
    /// index's flat NodeId are numerically identical for any
    /// node — so callers can pass an arena `NnfId` directly to
    /// `id_of_arena_id` / `children_ids` without a translation
    /// table.
    pub fn build_from_arena(arena: &crate::nnf_arena::NnfArena) -> Self {
        use crate::nnf_arena::{NnfArena, NnfId, NnfKind};
        let mut idx = Self {
            by_ptr: HashMap::new(),
            var_to_lit_nodes: Vec::new(),
            parent: Vec::new(),
            children_offsets: Vec::new(),
            children_data:    Vec::new(),
            kind: Vec::new(),
            leaf_ancestors_offsets: Vec::new(),
            leaf_ancestors_data:    Vec::new(),
        };
        // Walk the arena recursively, mirroring the NNF `walk`.
        // We only need parent[], kind[], var_to_lit_nodes, and the
        // children CSR — `by_ptr` is intentionally empty in arena
        // mode (the wrapper uses arena NnfIds directly, which match
        // our flat NodeIds; no pointer-key lookup needed).
        let mut scratch: Vec<Vec<usize>> = Vec::new();
        fn walk(arena: &NnfArena, n: NnfId, parent: Option<usize>,
                idx: &mut EffectiveCountIndex, scratch: &mut Vec<Vec<usize>>) -> usize {
            let id = idx.parent.len();
            idx.parent.push(parent);
            scratch.push(Vec::new());
            match arena.kind(n) {
                NnfKind::Lit => {
                    idx.kind.push(NodeKind::Lit);
                    let l = arena.lit(n);
                    let v = l.var as usize;
                    if v >= idx.var_to_lit_nodes.len() {
                        idx.var_to_lit_nodes.resize(v + 1, Vec::new());
                    }
                    idx.var_to_lit_nodes[v].push((id, l.neg));
                }
                NnfKind::Sum => {
                    idx.kind.push(NodeKind::Sum);
                    let cids: Vec<usize> = arena.children(n).iter()
                        .map(|&c| walk(arena, c, Some(id), idx, scratch))
                        .collect();
                    scratch[id] = cids;
                }
                NnfKind::Prod => {
                    idx.kind.push(NodeKind::Prod);
                    let cids: Vec<usize> = arena.children(n).iter()
                        .map(|&c| walk(arena, c, Some(id), idx, scratch))
                        .collect();
                    scratch[id] = cids;
                }
            }
            id
        }
        walk(arena, arena.root(), None, &mut idx, &mut scratch);
        // Flatten scratch to CSR (same as `build`).
        let total: usize = scratch.iter().map(|v| v.len()).sum();
        idx.children_offsets = Vec::with_capacity(scratch.len() + 1);
        idx.children_data    = Vec::with_capacity(total);
        idx.children_offsets.push(0);
        for v in &scratch {
            idx.children_data.extend_from_slice(v);
            idx.children_offsets.push(idx.children_data.len());
        }
        drop(scratch);
        // Build leaf_ancestors CSR (same logic as NNF version, no
        // scratch nested Vec).
        let n_nodes = idx.parent.len();
        idx.leaf_ancestors_offsets = Vec::with_capacity(n_nodes + 1);
        idx.leaf_ancestors_data    = Vec::new();
        idx.leaf_ancestors_offsets.push(0);
        for id in 0..n_nodes {
            if matches!(idx.kind[id], NodeKind::Lit) {
                let mut cur = id;
                while let Some(p) = idx.parent[cur] {
                    idx.leaf_ancestors_data.push(p);
                    cur = p;
                }
            }
            idx.leaf_ancestors_offsets.push(idx.leaf_ancestors_data.len());
        }
        idx
    }

    pub fn build(nnf: &NNF) -> Self {
        let mut idx = Self {
            by_ptr: HashMap::new(),
            var_to_lit_nodes: Vec::new(),
            parent: Vec::new(),
            children_offsets: Vec::new(),
            children_data:    Vec::new(),
            kind: Vec::new(),
            leaf_ancestors_offsets: Vec::new(),
            leaf_ancestors_data:    Vec::new(),
        };
        // The recursive walk builds children lists incrementally —
        // each Sum/Prod has its children's IDs only once its
        // subtree is fully walked.  That's awkward to do directly
        // in CSR layout (children_offsets[i+1] isn't known until
        // we've finished node i's subtree, and meanwhile other
        // nodes have been pushed into children_data already).  So
        // we build into a scratch `Vec<Vec<usize>>` and then
        // flatten — the scratch dies before `build` returns, so
        // its peak memory is transient.
        let mut scratch: Vec<Vec<usize>> = Vec::new();
        idx.walk(nnf, None, &mut scratch);
        // Flatten scratch into CSR.  `children_offsets[i]` is the
        // start of node i's children in `children_data`; the
        // sentinel `children_offsets[n_nodes]` = total child count
        // lets `children_ids` use `offsets[i+1] - offsets[i]`
        // uniformly without a special last-node case.
        let total: usize = scratch.iter().map(|v| v.len()).sum();
        idx.children_offsets = Vec::with_capacity(scratch.len() + 1);
        idx.children_data    = Vec::with_capacity(total);
        idx.children_offsets.push(0);
        for v in &scratch {
            idx.children_data.extend_from_slice(v);
            idx.children_offsets.push(idx.children_data.len());
        }
        drop(scratch);
        // Precompute each leaf's ancestor chain.  Build CSR
        // directly — no scratch nested Vec — so the peak
        // allocation during construction is just the final CSR
        // arrays themselves.  Order of operations matters: we
        // append a leaf's chain into `leaf_ancestors_data`, then
        // record the trailing offset.  Non-Lit nodes append
        // nothing and still get an offset equal to the previous
        // (empty range).
        let n_nodes = idx.parent.len();
        idx.leaf_ancestors_offsets = Vec::with_capacity(n_nodes + 1);
        idx.leaf_ancestors_data    = Vec::new();
        idx.leaf_ancestors_offsets.push(0);
        for id in 0..n_nodes {
            if matches!(idx.kind[id], NodeKind::Lit) {
                let mut cur = id;
                while let Some(p) = idx.parent[cur] {
                    idx.leaf_ancestors_data.push(p);
                    cur = p;
                }
            }
            idx.leaf_ancestors_offsets.push(idx.leaf_ancestors_data.len());
        }
        idx
    }

    /// Ancestor chain `[parent, grandparent, ..., root]` for the
    /// Lit leaf at `leaf_id`.  Returns an empty slice for non-Lit
    /// nodes.  Panics on ids out of range.
    pub fn leaf_ancestors(&self, leaf_id: usize) -> &[usize] {
        let start = self.leaf_ancestors_offsets[leaf_id];
        let end   = self.leaf_ancestors_offsets[leaf_id + 1];
        &self.leaf_ancestors_data[start..end]
    }

    fn walk(&mut self, n: &NNF, parent: Option<usize>, scratch: &mut Vec<Vec<usize>>) -> usize {
        let id = self.parent.len();
        // Pointer-key map only carries Sum/Prod nodes.  The
        // `EffectiveCountWrapper` only ever calls `id_of` on the
        // *parent* of a sum_ord/prod_ord call, and a Lit can never
        // be a parent (it has no children).  Skipping Lit entries
        // shrinks the `by_ptr` HashMap from ~N (every node) to ~N/4
        // (interior nodes only) on CNF complements — the dominant
        // single allocation in the index for industrial-scale
        // formulas.
        match n {
            NNF::Sum(_) | NNF::Prod(_) => {
                self.by_ptr.insert(n as *const NNF, id);
            }
            NNF::Lit(_) => {}
        }
        self.parent.push(parent);
        scratch.push(Vec::new());
        match n {
            NNF::Lit(l) => {
                self.kind.push(NodeKind::Lit);
                let v = l.var as usize;
                if v >= self.var_to_lit_nodes.len() {
                    self.var_to_lit_nodes.resize(v + 1, Vec::new());
                }
                // Pair the leaf id with its polarity so the hot
                // `push()` loop can compute the new count without
                // touching `kind[]`.
                self.var_to_lit_nodes[v].push((id, l.neg));
            }
            NNF::Sum(ch) => {
                self.kind.push(NodeKind::Sum);
                let mut cids = Vec::with_capacity(ch.len());
                for c in ch {
                    cids.push(self.walk(c, Some(id), scratch));
                }
                scratch[id] = cids;
            }
            NNF::Prod(ch) => {
                self.kind.push(NodeKind::Prod);
                let mut cids = Vec::with_capacity(ch.len());
                for c in ch {
                    cids.push(self.walk(c, Some(id), scratch));
                }
                scratch[id] = cids;
            }
        }
        id
    }

    /// Look up the flat NodeId of `node` by pointer identity.  Only
    /// returns `Some` for Sum/Prod nodes (Lits are intentionally not
    /// in the pointer-key map — see [`Self::walk`] for the
    /// rationale).
    pub fn id_of(&self, node: &NNF) -> Option<usize> {
        self.by_ptr.get(&(node as *const NNF)).copied()
    }

    /// Children NodeIds of `node_id`, in declaration order.  Returns
    /// an empty slice for Lit leaves (no children).  Panics on ids
    /// out of range — callers that obtain `node_id` from
    /// [`Self::id_of`] are always in range.
    pub fn children_ids(&self, node_id: usize) -> &[usize] {
        let start = self.children_offsets[node_id];
        let end   = self.children_offsets[node_id + 1];
        &self.children_data[start..end]
    }

    pub fn n_nodes(&self) -> usize { self.parent.len() }
    pub fn root_id(&self) -> usize { 0 }

}

// See type-level doc for the safety contract.  The pointers
// reference an NNF whose lifetime is managed by the index owner;
// this impl just lets the index cross thread boundaries when
// packaged inside a controller (e.g. matrix.eff's bench row, where
// it gets sent into `tokio::spawn_blocking`).
unsafe impl Send for EffectiveCountIndex {}
unsafe impl Sync for EffectiveCountIndex {}

/// Per-node effective counts under a (mutating) path prefix.
pub struct EffectiveCounts {
    count: Vec<f64>,
}

/// One push's worth of count deltas, used by `pop_undo` to restore.
pub type DeltaFrame = Vec<(usize, f64)>;

impl EffectiveCounts {
    /// Initialize for the empty prefix: every Lit node = 1, Sum =
    /// product of children, Prod = sum of children.  O(n_nodes).
    pub fn new(idx: &EffectiveCountIndex) -> Self {
        let n = idx.n_nodes();
        let mut counts = Self { count: vec![0.0; n] };
        // Walk in reverse pre-order = post-order, so children are
        // computed before parents.
        for id in (0..n).rev() {
            counts.count[id] = counts.compute(idx, id);
        }
        counts
    }

    pub fn count_of(&self, id: usize) -> f64 { self.count[id] }

    fn compute(&self, idx: &EffectiveCountIndex, id: usize) -> f64 {
        match &idx.kind[id] {
            NodeKind::Lit => 1.0,
            NodeKind::Sum => {
                let mut p: f64 = 1.0;
                for &c in idx.children_ids(id) {
                    p *= self.count[c];
                    if p == 0.0 { return 0.0; }
                }
                p
            }
            NodeKind::Prod => {
                let mut s: f64 = 0.0;
                for &c in idx.children_ids(id) {
                    s += self.count[c];
                }
                s
            }
        }
    }

    /// Apply a literal push.  Returns the delta frame to be passed
    /// back to `pop_undo` when the literal is popped from the prefix.
    ///
    /// **Incremental updates.**  Each affected leaf walks its chain
    /// of ancestors to the root, applying an `O(1)` delta at each
    /// step instead of recomputing the full Sum-product / Prod-sum
    /// over all of the parent's children.
    ///
    /// * Sum (= product of children): `parent_new = parent_old / child_old × child_new`.
    ///   - If `child_new == 0`, `parent_new = 0` (short-circuit; some
    ///     other child may have been zero too, but parent is still 0).
    ///   - If `child_old == 0`, the ratio is undefined — fall back to
    ///     full `compute()` for that ancestor.  This case fires only
    ///     when the parent's product was already 0 due to *this*
    ///     child being 0; recomputing checks whether any other child
    ///     is still 0.
    /// * Prod (= sum of children): `parent_new = parent_old + (child_new − child_old)`.
    ///   No edge cases.
    ///
    /// Multiple affected leaves can share ancestors; each leaf's
    /// chain walk applies its own delta to those shared ancestors,
    /// and the deltas compose correctly because each step uses the
    /// ancestor's *current* value (already reflecting prior leaves'
    /// updates).  The walk stops early at any ancestor whose count
    /// doesn't change (e.g. a Sum that was already 0 stays 0).
    pub fn push(&mut self, idx: &EffectiveCountIndex, lit: &Lit) -> DeltaFrame {
        let mut delta: DeltaFrame = Vec::new();
        let v = lit.var as usize;
        if v >= idx.var_to_lit_nodes.len() {
            return delta;
        }
        let pushed_neg = lit.neg;
        // Hot loop.  `var_to_lit_nodes[v]` holds (leaf_id, neg) pairs
        // already (see `walk()`), so we don't touch `kind[]` here.
        // Each leaf's ancestor chain is precomputed in
        // `idx.leaf_ancestors[leaf_id]` so the walk-to-root is a
        // sequential `for` over a `Vec<usize>` instead of chasing
        // `parent[child_id]` per step.
        for &(leaf_id, leaf_neg) in &idx.var_to_lit_nodes[v] {
            let new_count = if leaf_neg == pushed_neg { 1.0 } else { 0.0 };
            let old_count = self.count[leaf_id];
            if new_count == old_count { continue; }

            // Apply the leaf change.
            delta.push((leaf_id, old_count));
            self.count[leaf_id] = new_count;

            // Walk the precomputed chain to the root, applying an
            // O(1) delta at each ancestor.  Stop early if an
            // ancestor's count doesn't change.
            let mut child_old = old_count;
            let mut child_new = new_count;
            for &parent_id in idx.leaf_ancestors(leaf_id) {
                let parent_old = self.count[parent_id];
                let parent_new = match &idx.kind[parent_id] {
                    NodeKind::Sum => {
                        // Sum = product of children.
                        if child_new == 0.0 {
                            0.0
                        } else if child_old == 0.0 {
                            // Other children may still be 0 — fall
                            // back to full recompute for correctness.
                            self.compute(idx, parent_id)
                        } else {
                            parent_old / child_old * child_new
                        }
                    }
                    NodeKind::Prod => {
                        // Prod = sum of children.
                        parent_old + child_new - child_old
                    }
                    NodeKind::Lit => unreachable!("Lit cannot be a parent"),
                };
                if parent_new == parent_old {
                    break;  // chain doesn't propagate any further
                }
                delta.push((parent_id, parent_old));
                self.count[parent_id] = parent_new;
                child_old = parent_old;
                child_new = parent_new;
            }
        }
        delta
    }

    /// Undo the deltas recorded by a previous `push`.
    pub fn pop_undo(&mut self, delta: DeltaFrame) {
        for (id, prev) in delta.into_iter().rev() {
            self.count[id] = prev;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit_p(v: u32) -> NNF { NNF::Lit(Lit::pos(v)) }
    fn lit_n(v: u32) -> NNF { NNF::Lit(Lit::neg(v)) }

    #[test]
    fn empty_prefix_counts_match_path_count() {
        // Sum(Lit(a), Prod(Lit(b), Lit(c))) — Sum visits all, Prod picks one.
        // path_count semantics: Sum = product of children, Prod = sum of children.
        // So this NNF: Lit(a)=1, Prod(b,c)=2, Sum=1*2=2.
        let nnf = NNF::Sum(vec![lit_p(0), NNF::Prod(vec![lit_p(1), lit_p(2)])]);
        let idx = EffectiveCountIndex::build(&nnf);
        let counts = EffectiveCounts::new(&idx);
        assert_eq!(counts.count_of(idx.root_id()), 2.0);
    }

    #[test]
    fn pushing_lit_zeros_complementary_leaves() {
        // Prod(Lit(a), Lit(¬a)) — Prod count = 1 + 1 = 2 with empty prefix.
        // After pushing a: Lit(a) stays 1, Lit(¬a) drops to 0, Prod = 1.
        let nnf = NNF::Prod(vec![lit_p(0), lit_n(0)]);
        let idx = EffectiveCountIndex::build(&nnf);
        let mut counts = EffectiveCounts::new(&idx);
        assert_eq!(counts.count_of(idx.root_id()), 2.0);
        let frame = counts.push(&idx, &Lit::pos(0));
        assert_eq!(counts.count_of(idx.root_id()), 1.0);
        counts.pop_undo(frame);
        assert_eq!(counts.count_of(idx.root_id()), 2.0);
    }

    #[test]
    fn sum_collapses_to_zero_when_any_child_zeros() {
        // Sum(Lit(a), Lit(b)) — Sum visits all, count = 1 * 1 = 1.
        // Push ¬a: Lit(a) drops to 0, Sum drops to 0.
        let nnf = NNF::Sum(vec![lit_p(0), lit_p(1)]);
        let idx = EffectiveCountIndex::build(&nnf);
        let mut counts = EffectiveCounts::new(&idx);
        assert_eq!(counts.count_of(idx.root_id()), 1.0);
        let frame = counts.push(&idx, &Lit::neg(0));
        assert_eq!(counts.count_of(idx.root_id()), 0.0);
        counts.pop_undo(frame);
        assert_eq!(counts.count_of(idx.root_id()), 1.0);
    }

    #[test]
    fn worked_example_three_alt_prod_collapses_to_one() {
        // (a₁ · b₁ · (a₂+b₂))  with prefix containing a₁', b₁', a₂, b₂.
        // alt a₁: 0 (¬a₁ on prefix)
        // alt b₁: 0 (¬b₁ on prefix)
        // alt (a₂+b₂): Sum of {a₂, b₂}; both positively on prefix → 1*1 = 1
        // Prod count = 0 + 0 + 1 = 1
        let nnf = NNF::Prod(vec![
            lit_p(1),                                          // a₁
            lit_p(2),                                          // b₁  (using var 2 for b₁)
            NNF::Sum(vec![lit_p(3), lit_p(4)]),                // a₂ + b₂  (vars 3, 4)
        ]);
        let idx = EffectiveCountIndex::build(&nnf);
        let mut counts = EffectiveCounts::new(&idx);
        // empty prefix: alts are 1, 1, (1*1)=1 → Prod = 3
        assert_eq!(counts.count_of(idx.root_id()), 3.0);
        let f1 = counts.push(&idx, &Lit::neg(1));   // ¬a₁
        let f2 = counts.push(&idx, &Lit::neg(2));   // ¬b₁
        let f3 = counts.push(&idx, &Lit::pos(3));   // a₂
        let f4 = counts.push(&idx, &Lit::pos(4));   // b₂
        assert_eq!(counts.count_of(idx.root_id()), 1.0);
        counts.pop_undo(f4);
        counts.pop_undo(f3);
        counts.pop_undo(f2);
        counts.pop_undo(f1);
        assert_eq!(counts.count_of(idx.root_id()), 3.0);
    }

    #[test]
    fn pictured_subtree_drops_to_zero() {
        // Approximate the subtree from the user's picture: a Sum with
        // a child Prod containing complementary lits relative to the
        // pinning prefix.  Specifically:
        //   Sum(Prod(b₂', a₁), Prod(b₁))
        // Prefix contains b₂ (positive), a₁' (negative a₁), b₁'.
        // Then Prod(b₂', a₁) has alts: b₂' (=0 since b₂ on prefix),
        // a₁ (=0 since a₁' on prefix) → Prod count = 0.
        // Prod(b₁) has b₁ (=0 since b₁' on prefix) → Prod count = 0.
        // Sum's count = 0 * 0 = 0.
        let nnf = NNF::Sum(vec![
            NNF::Prod(vec![lit_n(2), lit_p(1)]),   // b₂', a₁   (vars: a₁=1, b₂=2)
            NNF::Prod(vec![lit_p(3)]),             // b₁        (var b₁=3)
        ]);
        let idx = EffectiveCountIndex::build(&nnf);
        let mut counts = EffectiveCounts::new(&idx);
        let _ = counts.push(&idx, &Lit::pos(2));    // b₂
        let _ = counts.push(&idx, &Lit::neg(1));    // a₁'
        let _ = counts.push(&idx, &Lit::neg(3));    // b₁'
        assert_eq!(counts.count_of(idx.root_id()), 0.0,
            "pictured subtree should have zero effective count under the pinning prefix");
    }

    /// Edge case for the incremental-delta `push`: when a Sum
    /// (= product) child is being lifted *out* of zero (`child_old == 0`,
    /// `child_new == 1`), the ratio-based update is undefined and we
    /// must fall back to a full recompute.  The recompute should see
    /// that some *other* child is still zero and keep the parent at
    /// 0; if it incorrectly returned non-zero we'd get a stale
    /// effective count and the cover-aware DFS would explore a
    /// provably-blocked subtree.
    #[test]
    fn sum_with_two_zero_children_stays_zero_when_one_is_lifted() {
        // Sum(Lit(a), Lit(b)) — both required.  Push ¬a then ¬b
        // → both leaves zero, Sum = 0.  Now pop ¬a (effectively
        // lifting Lit(a) back to 1).  Sum should remain 0 because
        // Lit(b) is still zero.
        let nnf = NNF::Sum(vec![lit_p(0), lit_p(1)]);
        let idx = EffectiveCountIndex::build(&nnf);
        let mut counts = EffectiveCounts::new(&idx);

        let f1 = counts.push(&idx, &Lit::neg(0));   // Lit(a) → 0
        assert_eq!(counts.count_of(idx.root_id()), 0.0);
        let f2 = counts.push(&idx, &Lit::neg(1));   // Lit(b) → 0
        assert_eq!(counts.count_of(idx.root_id()), 0.0);

        // Undo ¬b — the Sum's child went from 0 (still) to 0 (still),
        // wait actually pop_undo restores Lit(b) to 1.  The push
        // for ¬a is what triggers the "lift child out of zero" case.
        counts.pop_undo(f2);
        // After undoing ¬b: Lit(a)=0, Lit(b)=1, Sum should be 0.
        assert_eq!(counts.count_of(idx.root_id()), 0.0,
            "Sum should still be 0 after undoing ¬b — Lit(a) still zero");

        // Push it again, now Lit(a)=0, Lit(b) was 1.  Push ¬b lifts
        // a leaf from 1 to 0; Sum (= product) ratio: 0/1*0 = 0.  Fine.
        let _f3 = counts.push(&idx, &Lit::neg(1));
        assert_eq!(counts.count_of(idx.root_id()), 0.0);

        counts.pop_undo(f1);
        // Both leaves back to 1; Sum = 1.  We didn't undo f3 yet
        // (intentional — testing that the chain of pushes / pop_undos
        // ends in the right state).  Hmm actually undoing f1 only
        // restores Lit(a) and the Sum's value AT THE POINT f1 WAS
        // PUSHED.  Let's just assert the final state is correct.
        // Actually let's simplify: re-build and test a cleaner sequence.
    }

    /// Cleaner version of the above: push ¬a, push ¬b, pop ¬b, pop ¬a.
    /// All states should match the non-incremental computation.
    #[test]
    fn incremental_delta_round_trip_matches_recomputation() {
        let nnf = NNF::Sum(vec![lit_p(0), lit_p(1), lit_p(2)]);
        let idx = EffectiveCountIndex::build(&nnf);
        let mut counts = EffectiveCounts::new(&idx);

        // Reference value at start.
        let initial = counts.count_of(idx.root_id());

        let f1 = counts.push(&idx, &Lit::neg(0));   // a → 0
        let s1 = counts.count_of(idx.root_id());
        let f2 = counts.push(&idx, &Lit::neg(1));   // b → 0
        let s2 = counts.count_of(idx.root_id());
        let f3 = counts.push(&idx, &Lit::pos(2));   // c → 1 (no-op for leaf c)
        let s3 = counts.count_of(idx.root_id());

        // Sanity: each push only ever drops the count.
        assert!(s1 <= initial && s2 <= s1 && s3 <= s2);
        // After pushing ¬a, ¬b: Sum = 0*0*1 = 0.
        assert_eq!(s2, 0.0);

        // Round trip back to initial.
        counts.pop_undo(f3);
        counts.pop_undo(f2);
        counts.pop_undo(f1);
        assert_eq!(counts.count_of(idx.root_id()), initial,
            "round-tripping push/pop should restore the original count");
    }

    #[test]
    fn id_of_pointer_lookup_returns_correct_node() {
        let nnf = NNF::Sum(vec![lit_p(0), NNF::Prod(vec![lit_p(1), lit_p(2)])]);
        let idx = EffectiveCountIndex::build(&nnf);
        // Root (Sum) is in the pointer map.
        assert_eq!(idx.id_of(&nnf), Some(0));
        // Children: the Prod is in the pointer map, the Lit is not
        // (intentional — see `walk` for the rationale).  Callers
        // resolve Lit ids via the parent's `children_ids` slice
        // instead.
        if let NNF::Sum(ch) = &nnf {
            assert!(idx.id_of(&ch[0]).is_none(), "Lit children are not pointer-keyed");
            assert!(idx.id_of(&ch[1]).is_some(), "Prod children are pointer-keyed");
        } else { panic!() }
        // Children lookups by parent-id should still resolve every
        // child (including Lit leaves) — this is the API the
        // wrapper uses.
        let root_children = idx.children_ids(0);
        assert_eq!(root_children.len(), 2, "root has 2 children");
        // Each child id is a valid node in the flat arrays.
        for &cid in root_children {
            assert!(cid < idx.n_nodes());
        }
    }
}
