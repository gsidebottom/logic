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

use std::collections::{BTreeSet, HashMap};

use crate::matrix::{Lit, NNF};

/// Pre-computed structural index of an NNF.
pub struct EffectiveCountIndex {
    /// Pointer-to-`NNF` → flat NodeId.  Used by `id_of` so the
    /// PathSearchController wrapper can look up children by their
    /// `&NNF` references in `sum_ord` / `prod_ord`.
    by_ptr: HashMap<*const NNF, usize>,
    /// `var → [leaf node id]` — every Lit-leaf containing this var.
    /// Used by `EffectiveCounts::push` to locate the leaves whose
    /// counts change when a literal is pushed.
    var_to_lit_nodes: Vec<Vec<usize>>,
    /// Parent of each node (`None` for root).
    parent: Vec<Option<usize>>,
    /// Children of each node (empty for `Lit`).
    children: Vec<Vec<usize>>,
    /// Per-node kind.
    kind: Vec<NodeKind>,
}

#[derive(Clone, Debug)]
enum NodeKind {
    Lit(Lit),
    Sum,
    Prod,
}

impl EffectiveCountIndex {
    /// Build an index for `nnf`.  Pointer keys assume `nnf` is fixed
    /// in memory for the lifetime of any `EffectiveCounts` built on
    /// top of this index — the typical case is the index is owned by
    /// the controller and refers to the NNF the controller drives.
    pub fn build(nnf: &NNF) -> Self {
        let mut idx = Self {
            by_ptr: HashMap::new(),
            var_to_lit_nodes: Vec::new(),
            parent: Vec::new(),
            children: Vec::new(),
            kind: Vec::new(),
        };
        idx.walk(nnf, None);
        idx
    }

    fn walk(&mut self, n: &NNF, parent: Option<usize>) -> usize {
        let id = self.parent.len();
        self.by_ptr.insert(n as *const NNF, id);
        self.parent.push(parent);
        self.children.push(Vec::new());
        match n {
            NNF::Lit(l) => {
                self.kind.push(NodeKind::Lit(l.clone()));
                let v = l.var as usize;
                if v >= self.var_to_lit_nodes.len() {
                    self.var_to_lit_nodes.resize(v + 1, Vec::new());
                }
                self.var_to_lit_nodes[v].push(id);
            }
            NNF::Sum(ch) => {
                self.kind.push(NodeKind::Sum);
                let mut cids = Vec::with_capacity(ch.len());
                for c in ch {
                    cids.push(self.walk(c, Some(id)));
                }
                self.children[id] = cids;
            }
            NNF::Prod(ch) => {
                self.kind.push(NodeKind::Prod);
                let mut cids = Vec::with_capacity(ch.len());
                for c in ch {
                    cids.push(self.walk(c, Some(id)));
                }
                self.children[id] = cids;
            }
        }
        id
    }

    pub fn id_of(&self, node: &NNF) -> Option<usize> {
        self.by_ptr.get(&(node as *const NNF)).copied()
    }
    pub fn n_nodes(&self) -> usize { self.parent.len() }
    pub fn root_id(&self) -> usize { 0 }

    fn lit_at(&self, id: usize) -> Option<&Lit> {
        match &self.kind[id] {
            NodeKind::Lit(l) => Some(l),
            _ => None,
        }
    }
}

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
            NodeKind::Lit(_) => 1.0,
            NodeKind::Sum => {
                let mut p: f64 = 1.0;
                for &c in &idx.children[id] {
                    p *= self.count[c];
                    if p == 0.0 { return 0.0; }
                }
                p
            }
            NodeKind::Prod => {
                let mut s: f64 = 0.0;
                for &c in &idx.children[id] {
                    s += self.count[c];
                }
                s
            }
        }
    }

    /// Apply a literal push.  Returns the delta frame to be passed
    /// back to `pop_undo` when the literal is popped from the prefix.
    pub fn push(&mut self, idx: &EffectiveCountIndex, lit: &Lit) -> DeltaFrame {
        let mut delta: DeltaFrame = Vec::new();
        let v = lit.var as usize;
        if v >= idx.var_to_lit_nodes.len() {
            return delta;
        }
        // Update affected Lit leaves.  Matching lits keep count=1
        // (no change); complementary lits drop to 0.
        let mut to_process: BTreeSet<usize> = BTreeSet::new();
        for &leaf_id in &idx.var_to_lit_nodes[v] {
            let leaf_lit = idx.lit_at(leaf_id).expect("var_to_lit_nodes points to non-Lit");
            if leaf_lit.var != lit.var { continue; }
            let new_count = if leaf_lit.neg == lit.neg { 1.0 } else { 0.0 };
            if new_count != self.count[leaf_id] {
                delta.push((leaf_id, self.count[leaf_id]));
                self.count[leaf_id] = new_count;
                if let Some(p) = idx.parent[leaf_id] { to_process.insert(p); }
            }
        }
        // Propagate upward, deepest first (largest id in pre-order
        // = deepest), recomputing each dirty ancestor.  Stop at an
        // ancestor whose count doesn't change.
        while let Some(id) = to_process.pop_last() {
            let new_count = self.compute(idx, id);
            if new_count != self.count[id] {
                delta.push((id, self.count[id]));
                self.count[id] = new_count;
                if let Some(p) = idx.parent[id] { to_process.insert(p); }
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

    #[test]
    fn id_of_pointer_lookup_returns_correct_node() {
        let nnf = NNF::Sum(vec![lit_p(0), NNF::Prod(vec![lit_p(1), lit_p(2)])]);
        let idx = EffectiveCountIndex::build(&nnf);
        // Root.
        assert_eq!(idx.id_of(&nnf), Some(0));
        // First child (lit_p(0)).
        if let NNF::Sum(ch) = &nnf {
            assert!(idx.id_of(&ch[0]).is_some());
            assert!(idx.id_of(&ch[1]).is_some());
        } else { panic!() }
    }
}
