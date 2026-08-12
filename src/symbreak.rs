//! symbreak — a Rust port of satsuma-style structure-based symmetry
//! breaking for SAT, staged as a *certified* hydra pre-CaDiCaL stage.
//!
//! Many hard SAT instances are hard only because they are highly
//! symmetric: the pigeonhole family, clique-coloring, and most
//! combinatorial-design formulas admit large automorphism groups, and
//! a CDCL solver re-derives the same conflict once per symmetric copy.
//! Symmetry breaking detects those automorphisms and adds
//! *symmetry-breaking predicates* (SBPs) that keep one representative
//! per orbit, collapsing the search. satsuma (Anders et al.) is the
//! current state of the art; it detects symmetries with the practical
//! graph-automorphism solver `dejavu` and emits structure-based
//! breaking constraints (lex-leader or fixing), optionally with SR /
//! VeriPB proofs so the result stays certifiable.
//!
//! ## Soundness (why this can live inside hydra)
//! SBP clauses are **satisfiability-preserving but not
//! equivalence-preserving**: they remove some models while keeping at
//! least one per orbit. Consequences for hydra's certified-everything
//! design:
//!   * A model of the augmented formula is still a genuine model of the
//!     original, so **SAT verdicts stay sound and witness-certifiable**.
//!   * "augmented formula is UNSAT" does **not** by itself certify the
//!     *original* is UNSAT — that needs the symmetry proof (SR/VeriPB).
//!     Phase 6 emits it; until then a symmetry-broken UNSAT is sound
//!     but flagged uncertified (as hydra's XOR-UNSAT path already is).
//!
//! ## Build plan (gated per layer)
//!   * **Phase 1 (this file, now):** colored-graph encoding of a CNF +
//!     color refinement (coarsest equitable partition / 1-dimensional
//!     Weisfeiler-Leman). This equitable-partition core is the inner
//!     primitive of individualization-refinement, so everything below
//!     builds on it.
//!   * Phase 2: individualization-refinement tree + deterministic
//!     backtracking automorphism search (nauty/Traces style).
//!   * Phase 3: dejavu's random IR-walk Monte-Carlo paradigm +
//!     Schreier-Sims (membership, orbits, strong generating set).
//!   * Phase 4: CNF symmetry extraction + SBP generation (lex-leader,
//!     fixing).
//!   * Phase 5: hydra stage integration before the CaDiCaL handoff.
//!   * Phase 6: SR + VeriPB proof emission for symmetry-broken UNSAT.

/// A vertex-colored undirected graph (simple; parallel edges allowed
/// but the CNF encoding never creates them on clean input).
#[derive(Clone)]
pub struct Graph {
    pub n: usize,
    pub adj: Vec<Vec<u32>>,
    /// Initial coloring; `refine` returns the equitable partition
    /// refining it.
    pub color: Vec<u32>,
}

impl Graph {
    pub fn new(n: usize) -> Self {
        Graph {
            n,
            adj: vec![Vec::new(); n],
            color: vec![0; n],
        }
    }

    pub fn add_edge(&mut self, u: u32, v: u32) {
        self.adj[u as usize].push(v);
        self.adj[v as usize].push(u);
    }
}

/// Number of distinct colors in a coloring.
pub fn num_colors(color: &[u32]) -> usize {
    let mut c: Vec<u32> = color.to_vec();
    c.sort_unstable();
    c.dedup();
    c.len()
}

/// The CNF literal graph plus the metadata needed to map graph
/// automorphisms back to formula symmetries (Phase 4).
pub struct CnfGraph {
    pub graph: Graph,
    pub nvars: usize,
    pub nclauses: usize,
}

/// Graph node index of a DIMACS literal.
///   positive literal of var v  -> 2*(v-1)
///   negative literal of var v  -> 2*(v-1) + 1
#[inline]
pub fn lit_node(lit: i32) -> u32 {
    let v = lit.unsigned_abs() - 1;
    if lit > 0 { 2 * v } else { 2 * v + 1 }
}

/// Encode a CNF as a 2-colored literal graph (the standard
/// saucy/BreakID encoding):
///   * `2*nvars` literal nodes, colored 0;
///   * `nclauses` clause nodes, colored 1 (so no automorphism ever
///     maps a literal onto a clause);
///   * a *negation edge* between the two literal nodes of each variable
///     (forces automorphisms to respect the polarity pairing);
///   * an *occurrence edge* from each literal node to every clause node
///     it appears in.
///
/// A graph automorphism of this encoding is exactly a symmetry of the
/// formula: a permutation of literals that respects negation and maps
/// the clause set to itself.
pub fn cnf_to_graph(nvars: usize, clauses: &[Vec<i32>]) -> CnfGraph {
    let m = clauses.len();
    let n = 2 * nvars + m;
    let mut g = Graph::new(n);
    for u in 2 * nvars..n {
        g.color[u] = 1;
    }
    for v in 0..nvars {
        g.add_edge((2 * v) as u32, (2 * v + 1) as u32);
    }
    for (ci, clause) in clauses.iter().enumerate() {
        let cnode = (2 * nvars + ci) as u32;
        for &lit in clause {
            g.add_edge(lit_node(lit), cnode);
        }
    }
    CnfGraph { graph: g, nvars, nclauses: m }
}

/// Color refinement: the coarsest equitable partition refining
/// `g.color`. Two nodes keep the same color iff they had the same color
/// *and* the same multiset of neighbor colors; iterate to fixpoint.
///
/// Colors are canonically relabeled `0..k` each round (signatures
/// sorted), so the output is deterministic and comparable across runs
/// — the invariant every downstream layer relies on. The partition is
/// monotonically non-decreasing in cell count (each node's own color is
/// folded into its signature), so a round that fails to increase the
/// count has reached the fixpoint.
pub fn refine(g: &Graph) -> Vec<u32> {
    let mut color = g.color.clone();
    let mut ncolors = num_colors(&color);
    loop {
        // Per-node signature: (own color, sorted neighbor colors).
        let mut sigs: Vec<(u32, Vec<u32>)> = Vec::with_capacity(g.n);
        for u in 0..g.n {
            let mut nb: Vec<u32> = g.adj[u].iter().map(|&w| color[w as usize]).collect();
            nb.sort_unstable();
            sigs.push((color[u], nb));
        }
        // Canonical relabel: sort distinct signatures, id = rank.
        let mut order: Vec<(u32, Vec<u32>)> = sigs.clone();
        order.sort();
        order.dedup();
        let nnew = order.len();
        let map: std::collections::HashMap<&(u32, Vec<u32>), u32> = order
            .iter()
            .enumerate()
            .map(|(i, s)| (s, i as u32))
            .collect();
        let new: Vec<u32> = sigs.iter().map(|s| map[s]).collect();
        if nnew == ncolors {
            return new;
        }
        color = new;
        ncolors = nnew;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(n: usize) -> Graph {
        let mut g = Graph::new(n);
        for i in 0..n.saturating_sub(1) {
            g.add_edge(i as u32, (i + 1) as u32);
        }
        g
    }

    /// PHP with `p` pigeons and `h` holes: var(pp,hh) = pp*h + hh + 1.
    fn php(p: usize, h: usize) -> (usize, Vec<Vec<i32>>) {
        let v = |pp: usize, hh: usize| (pp * h + hh + 1) as i32;
        let mut cl = Vec::new();
        for pp in 0..p {
            cl.push((0..h).map(|hh| v(pp, hh)).collect());
        }
        for hh in 0..h {
            for pp in 0..p {
                for qq in (pp + 1)..p {
                    cl.push(vec![-v(pp, hh), -v(qq, hh)]);
                }
            }
        }
        (p * h, cl)
    }

    #[test]
    fn path_reflection_classes() {
        // A path's equitable partition is "distance to nearest end", so
        // node i and node (n-1-i) share a color (the reflection), and
        // the partition is coarser than discrete.
        let g = path(7);
        let c = refine(&g);
        for i in 0..7 {
            assert_eq!(c[i], c[6 - i], "reflection i<->6-i must preserve color");
        }
        assert!(num_colors(&c) < 7, "path must not refine to discrete");
        assert_eq!(num_colors(&c), 4, "P7 has 4 distance-to-end classes");
    }

    #[test]
    fn refinement_is_idempotent() {
        let g = path(9);
        let c1 = refine(&g);
        let g2 = Graph { n: g.n, adj: g.adj.clone(), color: c1.clone() };
        let c2 = refine(&g2);
        assert_eq!(num_colors(&c1), num_colors(&c2));
        for i in 0..g.n {
            for j in 0..g.n {
                assert_eq!(
                    c1[i] == c1[j],
                    c2[i] == c2[j],
                    "refining an equitable partition must not split it further"
                );
            }
        }
    }

    #[test]
    fn cnf_encoding_shape() {
        // 2 vars, clauses [1,2] and [-1,-2].
        let clauses = vec![vec![1, 2], vec![-1, -2]];
        let cg = cnf_to_graph(2, &clauses);
        assert_eq!(cg.graph.n, 2 * 2 + 2);
        let degsum: usize = cg.graph.adj.iter().map(|a| a.len()).sum();
        // 2 negation edges + 4 occurrence edges = 6 undirected -> degree sum 12
        assert_eq!(degsum, 12);
        // literal nodes color 0, clause nodes color 1
        assert_eq!(&cg.graph.color[0..4], &[0, 0, 0, 0]);
        assert_eq!(&cg.graph.color[4..6], &[1, 1]);
    }

    #[test]
    fn php_symmetry_is_four_colors() {
        // PHP_{4,3}: full pigeon x hole symmetry (S_4 x S_3 on the
        // variables) must collapse the refined coloring to exactly four
        // orbit classes — positive literals, negative literals, pigeon
        // clauses, conflict clauses. A wrong encoding or a wrong
        // refinement breaks this.
        let (nvars, clauses) = php(4, 3);
        let cg = cnf_to_graph(nvars, &clauses);
        let c = refine(&cg.graph);
        assert_eq!(num_colors(&c), 4, "PHP_4,3 collapses to 4 orbit colors");
        // All positive-literal nodes share one color.
        let pos0 = c[lit_node(1) as usize];
        for v in 1..=nvars as i32 {
            assert_eq!(c[lit_node(v) as usize], pos0, "all pos literals one color");
        }
        // Positive and negative literals differ (their degrees do).
        assert_ne!(c[lit_node(1) as usize], c[lit_node(-1) as usize]);
    }
}
