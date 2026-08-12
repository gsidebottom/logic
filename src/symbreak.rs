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
    refine_coloring(g, &g.color)
}

/// Color refinement seeded from an arbitrary starting coloring (the
/// individualization step of Phase 2 feeds a coloring here). Semantics
/// identical to [`refine`]; see its doc.
pub fn refine_coloring(g: &Graph, start: &[u32]) -> Vec<u32> {
    let mut color = start.to_vec();
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

// ===========================================================================
// Phase 2/3: individualization-refinement automorphism search + the group
// engine (Schreier-Sims) needed to gate it. The IR search finds a generating
// set of Aut(G); Schreier-Sims turns generators into |Aut| and membership.
// dejavu's randomized IR-walk competitiveness on adversarial graphs is a
// deliberate later-perf gap; this layer is correct, not yet dejavu-fast.
// ===========================================================================

/// Permutations on `0..n` are `Vec<usize>` (images). `compose(a,b)`
/// applies `b` then `a`: `(a∘b)(x) = a[b[x]]`.
fn perm_compose(a: &[usize], b: &[usize]) -> Vec<usize> {
    b.iter().map(|&x| a[x]).collect()
}
fn perm_inverse(a: &[usize]) -> Vec<usize> {
    let mut r = vec![0usize; a.len()];
    for (x, &ax) in a.iter().enumerate() {
        r[ax] = x;
    }
    r
}
fn perm_is_identity(a: &[usize]) -> bool {
    a.iter().enumerate().all(|(x, &ax)| x == ax)
}

/// Orbit of `p` under `gens` with a transversal: `map[y]` is a
/// permutation sending `p` to `y` (a coset representative).
fn orbit_transversal(p: usize, gens: &[Vec<usize>]) -> std::collections::HashMap<usize, Vec<usize>> {
    let n = if gens.is_empty() { p + 1 } else { gens[0].len() };
    let mut trans = std::collections::HashMap::new();
    trans.insert(p, (0..n).collect::<Vec<usize>>());
    let mut queue = vec![p];
    while let Some(x) = queue.pop() {
        let rep_x = trans[&x].clone();
        for g in gens {
            let y = g[x];
            if !trans.contains_key(&y) {
                trans.insert(y, perm_compose(g, &rep_x));
                queue.push(y);
            }
        }
    }
    trans
}

/// Order of the group generated by `generators` (permutations on
/// `0..n`), via a plain deterministic Schreier-Sims stabilizer chain.
/// Correct for the small groups this port gates on; not tuned for
/// large-degree performance.
pub fn group_order(n: usize, generators: &[Vec<usize>]) -> u128 {
    let mut levels: Vec<Vec<Vec<usize>>> =
        vec![generators.iter().filter(|g| !perm_is_identity(g)).cloned().collect()];
    let mut order: u128 = 1;
    let mut i = 0;
    while i < levels.len() {
        let gens = levels[i].clone();
        if gens.is_empty() {
            break;
        }
        // Base point: something moved by a generator at this level.
        let bp = (0..n)
            .find(|&p| gens.iter().any(|g| g[p] != p))
            .expect("nonempty gens must move a point");
        let trans = orbit_transversal(bp, &gens);
        order *= trans.len() as u128;
        // Schreier generators of the stabilizer of `bp`.
        let mut seen = std::collections::HashSet::new();
        let mut stab = Vec::new();
        for (&x, rep_x) in &trans {
            for g in &gens {
                let gx = g[x];
                let s = perm_compose(&perm_inverse(&trans[&gx]), &perm_compose(g, rep_x));
                if !perm_is_identity(&s) && seen.insert(s.clone()) {
                    stab.push(s);
                }
            }
        }
        levels.push(stab);
        i += 1;
    }
    order
}

/// Individualization-refinement automorphism search. Returns a
/// generating set of the color-respecting automorphism group of `g`
/// (each generator is verified to be a true automorphism, so the set is
/// never wrong — at worst incomplete, which the |Aut| gates catch).
///
/// Method (nauty/Traces lineage): descend the IR tree to a first
/// discrete leaf as the reference labeling; every other leaf yields a
/// candidate automorphism `first_leaf⁻¹ ∘ leaf`, verified before it is
/// kept. Branches are pruned by orbits of the discovered generators
/// that fix the current individualization path pointwise (the pointwise
/// stabilizer) — sound, and what keeps K_n's n! leaves down to a few
/// generators. A node budget bounds the search.
pub fn find_generators(g: &Graph) -> Vec<Vec<usize>> {
    let n = g.n;
    // adjacency as a set of ordered pairs (u<w) packed into u64
    let key = |u: usize, w: usize| -> u64 {
        let (a, b) = if u < w { (u, w) } else { (w, u) };
        (a as u64) << 32 | b as u64
    };
    let mut edges = std::collections::HashSet::new();
    let mut edge_list = Vec::new();
    for u in 0..n {
        for &w in &g.adj[u] {
            let w = w as usize;
            if u < w && edges.insert(key(u, w)) {
                edge_list.push((u, w));
            }
        }
    }
    let init = &g.color;
    let is_auto = |gamma: &[usize]| -> bool {
        for v in 0..n {
            if init[gamma[v]] != init[v] {
                return false;
            }
        }
        edge_list.iter().all(|&(u, w)| edges.contains(&key(gamma[u], gamma[w])))
    };

    struct Search<'a> {
        g: &'a Graph,
        n: usize,
        first_inv: Option<Vec<usize>>,
        gens: Vec<Vec<usize>>,
        nodes: usize,
        budget: usize,
    }
    let mut s = Search { g, n, first_inv: None, gens: Vec::new(), nodes: 0, budget: 2_000_000 };

    // Recursive DFS over the IR tree. `path` = individualized vertices.
    fn dfs<F: Fn(&[usize]) -> bool>(
        s: &mut Search,
        color: &[u32],
        path: &[usize],
        is_auto: &F,
    ) {
        if s.nodes >= s.budget {
            return;
        }
        s.nodes += 1;
        if num_colors(color) == s.n {
            // discrete: color[v] is v's position; ℓ = color.
            if s.first_inv.is_none() {
                let mut inv = vec![0usize; s.n];
                for v in 0..s.n {
                    inv[color[v] as usize] = v;
                }
                s.first_inv = Some(inv);
                return;
            }
            let inv0 = s.first_inv.as_ref().unwrap();
            let gamma: Vec<usize> = (0..s.n).map(|v| inv0[color[v] as usize]).collect();
            if !perm_is_identity(&gamma) && is_auto(&gamma) && !s.gens.contains(&gamma) {
                s.gens.push(gamma);
            }
            return;
        }
        // target cell: smallest color that is not a singleton
        let mut counts = std::collections::HashMap::new();
        for &c in color {
            *counts.entry(c).or_insert(0usize) += 1;
        }
        let target = (0..)
            .map(|c| c as u32)
            .find(|c| counts.get(c).copied().unwrap_or(0) > 1)
            .unwrap();
        let cell: Vec<usize> = (0..s.n).filter(|&v| color[v] == target).collect();
        // pointwise-stabilizer orbit pruning: only branch one vertex per
        // orbit under generators that fix `path`.
        let stab: Vec<Vec<usize>> =
            s.gens.iter().filter(|gm| path.iter().all(|&p| gm[p] == p)).cloned().collect();
        let mut explored: Vec<usize> = Vec::new();
        for &v in &cell {
            // recompute orbit membership against the growing generator set
            let stab_now: Vec<Vec<usize>> = if stab.len() == s.gens.len() {
                stab.clone()
            } else {
                s.gens.iter().filter(|gm| path.iter().all(|&p| gm[p] == p)).cloned().collect()
            };
            let orb = if stab_now.is_empty() {
                None
            } else {
                Some(orbit_transversal(v, &stab_now))
            };
            let skip = explored.iter().any(|&e| match &orb {
                Some(o) => o.contains_key(&e),
                None => false,
            });
            if skip {
                continue;
            }
            explored.push(v);
            let mut c2 = color.to_vec();
            let m = *c2.iter().max().unwrap();
            c2[v] = m + 1;
            let refined = refine_coloring(s.g, &c2);
            let mut new_path = path.to_vec();
            new_path.push(v);
            dfs(s, &refined, &new_path, is_auto);
        }
    }

    let root = refine(g);
    dfs(&mut s, &root, &[], &is_auto);
    s.gens
}

// ===========================================================================
// Phase 4: CNF symmetry extraction + symmetry-breaking-predicate generation.
// A graph automorphism becomes a literal permutation; the sign-preserving
// ones (all of PHP's, since the encoding colors pos/neg literals apart) give
// variable permutations, and each gets a lex-leader SBP. Sat-preserving:
// every orbit keeps its lex-minimal assignment, so a model survives.
// ===========================================================================

/// Extract the variable permutation induced by a graph automorphism, if
/// it is sign-preserving (maps every positive-literal node to a
/// positive-literal node). Returns `None` for polarity-flipping
/// generators (handled by signed lex-leader in a later extension).
pub fn to_variable_perm(gamma: &[usize], nvars: usize) -> Option<Vec<usize>> {
    let mut pi = vec![0usize; nvars];
    for v in 0..nvars {
        let img = gamma[2 * v];
        if img % 2 != 0 {
            return None; // positive literal maps to a negative literal
        }
        let w = img / 2;
        if w >= nvars || gamma[2 * v + 1] != 2 * w + 1 {
            return None;
        }
        pi[v] = w;
    }
    Some(pi)
}

/// Lex-leader symmetry-breaking clauses for a variable permutation `pi`
/// under the identity variable order: enforce the assignment is
/// lexicographically ≤ its `pi`-image. Uses the standard equal-prefix
/// aux-variable chain (`y_{i+1} ↔ y_i ∧ (a_i = b_i)`); fixed points of
/// `pi` are skipped. Fresh aux-variable ids are drawn from `next_fresh`.
pub fn lex_leader(pi: &[usize], nvars: usize, next_fresh: &mut i32) -> Vec<Vec<i32>> {
    let mut cl = Vec::new();
    let mut bound: Option<i32> = None; // None ⇒ prefix still all-equal
    for oi in 0..nvars {
        let wi = pi[oi];
        if oi == wi {
            continue; // pi fixes this variable: no constraint, bound unchanged
        }
        let a = oi as i32 + 1;
        let b = wi as i32 + 1;
        // bound ⇒ a ≤ b   (i.e. ¬a ∨ b)
        match bound {
            None => cl.push(vec![-a, b]),
            Some(y) => cl.push(vec![-y, -a, b]),
        }
        // define y2 ↔ bound ∧ (a = b)
        let y2 = *next_fresh;
        *next_fresh += 1;
        if let Some(y) = bound {
            cl.push(vec![-y2, y]); // y2 ⇒ bound
        }
        cl.push(vec![-y2, -a, b]); // y2 ⇒ (a ⇒ b)
        cl.push(vec![-y2, a, -b]); // y2 ⇒ (b ⇒ a)
        match bound {
            None => {
                cl.push(vec![a, b, y2]); // a=b=0 ⇒ y2
                cl.push(vec![-a, -b, y2]); // a=b=1 ⇒ y2
            }
            Some(y) => {
                cl.push(vec![-y, a, b, y2]);
                cl.push(vec![-y, -a, -b, y2]);
            }
        }
        bound = Some(y2);
    }
    cl
}

/// End-to-end Phase 4: detect the formula's symmetries and return the
/// lex-leader SBP clauses plus the new variable count (originals +
/// aux). Sound: the augmented formula is equisatisfiable with the
/// original (SAT-preserving), so a SAT verdict + its witness stay valid.
pub fn break_symmetries(nvars: usize, clauses: &[Vec<i32>]) -> (Vec<Vec<i32>>, usize) {
    let cg = cnf_to_graph(nvars, clauses);
    let gens = find_generators(&cg.graph);
    let mut next_fresh = nvars as i32 + 1;
    let mut added = Vec::new();
    for g in &gens {
        if let Some(pi) = to_variable_perm(g, nvars) {
            added.extend(lex_leader(&pi, nvars, &mut next_fresh));
        }
    }
    (added, (next_fresh - 1) as usize)
}

#[cfg(test)]
mod phase4_tests {
    use super::*;

    /// Assignments (as bitmasks over vars 0..nvars) satisfying `clauses`.
    fn models(nvars: usize, clauses: &[Vec<i32>]) -> Vec<u64> {
        let mut out = Vec::new();
        for mask in 0u64..(1u64 << nvars) {
            let sat = clauses.iter().all(|cl| {
                cl.iter().any(|&l| {
                    let bit = (mask >> (l.unsigned_abs() - 1)) & 1 == 1;
                    (l > 0) == bit
                })
            });
            if sat {
                out.push(mask);
            }
        }
        out
    }

    #[test]
    fn single_generator_is_exact_lex_leader() {
        // F = (x1 ∨ x2), symmetry swap(x1,x2). Models {01,10,11} fall in
        // two ⟨swap⟩ orbits; a correct lex-leader keeps exactly one per
        // orbit → 2 surviving.
        let clauses = vec![vec![1, 2]];
        let (added, newn) = break_symmetries(2, &clauses);
        assert!(!added.is_empty(), "swap symmetry must be found");
        let mut all = clauses.clone();
        all.extend(added);
        // count surviving ORIGINAL assignments (aux vars are determined)
        let aug = models(newn, &all);
        let orig_surviving: std::collections::HashSet<u64> =
            aug.iter().map(|m| m & 0b11).collect();
        assert_eq!(orig_surviving.len(), 2, "one representative per orbit");
    }

    #[test]
    fn multi_generator_is_sat_preserving() {
        // F = (x1 ∨ x2 ∨ x3), full S_3 symmetry. 7 models in 3 orbits by
        // weight. Per-generator lex-leader is sound (≥1 per orbit) though
        // not necessarily exact.
        let clauses = vec![vec![1, 2, 3]];
        let orig = models(3, &clauses);
        assert_eq!(orig.len(), 7);
        let (added, newn) = break_symmetries(3, &clauses);
        let mut all = clauses.clone();
        all.extend(added);
        let surviving: std::collections::HashSet<u64> =
            models(newn, &all).iter().map(|m| m & 0b111).collect();
        assert!(!surviving.is_empty(), "SAT must be preserved");
        assert!(surviving.len() >= 3, "at least one per S_3 orbit (sound)");
        assert!(surviving.len() < orig.len(), "must actually break some symmetry");
    }

    #[test]
    fn php_symmetries_are_sign_preserving_and_break() {
        // Every PHP generator is sign-preserving (pos/neg literals are
        // different colors), so all yield variable permutations, and the
        // stage adds real clauses. UNSAT is preserved trivially.
        let v = |p: usize, h: usize| (p * 2 + h + 1) as i32;
        let mut clauses = Vec::new();
        for p in 0..3 {
            clauses.push(vec![v(p, 0), v(p, 1)]);
        }
        for h in 0..2 {
            for p in 0..3 {
                for q in p + 1..3 {
                    clauses.push(vec![-v(p, h), -v(q, h)]);
                }
            }
        }
        let cg = cnf_to_graph(6, &clauses);
        let gens = find_generators(&cg.graph);
        assert!(!gens.is_empty());
        for g in &gens {
            assert!(to_variable_perm(g, 6).is_some(), "PHP gens are sign-preserving");
        }
        let (added, _) = break_symmetries(6, &clauses);
        assert!(!added.is_empty(), "PHP symmetry must produce SBP clauses");
        // PHP_3,2 is UNSAT; adding clauses keeps it UNSAT.
        let mut all = clauses.clone();
        all.extend(added);
        assert!(models(6, &clauses).is_empty());
        // (augmented over aux vars also unsat, but the original projection
        // is already empty — soundness is trivial here.)
    }
}

#[cfg(test)]
mod group_tests {
    use super::*;

    #[test]
    fn schreier_sims_known_orders() {
        // S_5 from adjacent transpositions -> 120
        let n = 5;
        let mut gens = Vec::new();
        for i in 0..n - 1 {
            let mut p: Vec<usize> = (0..n).collect();
            p.swap(i, i + 1);
            gens.push(p);
        }
        assert_eq!(group_order(n, &gens), 120);
        // 5-cycle -> order 5
        let cyc: Vec<usize> = (0..n).map(|x| (x + 1) % n).collect();
        assert_eq!(group_order(n, &[cyc.clone()]), 5);
        // dihedral: 5-cycle + reflection -> 10
        let refl: Vec<usize> = (0..n).map(|x| (n - x) % n).collect();
        assert_eq!(group_order(n, &[cyc, refl]), 10);
    }

    fn cycle_graph(n: usize) -> Graph {
        let mut g = Graph::new(n);
        for i in 0..n {
            g.add_edge(i as u32, ((i + 1) % n) as u32);
        }
        g
    }
    fn complete_graph(n: usize) -> Graph {
        let mut g = Graph::new(n);
        for i in 0..n {
            for j in i + 1..n {
                g.add_edge(i as u32, j as u32);
            }
        }
        g
    }
    fn path_graph(n: usize) -> Graph {
        let mut g = Graph::new(n);
        for i in 0..n.saturating_sub(1) {
            g.add_edge(i as u32, (i + 1) as u32);
        }
        g
    }
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

    fn aut_order(g: &Graph) -> u128 {
        group_order(g.n, &find_generators(g))
    }

    #[test]
    fn cycle_is_dihedral() {
        assert_eq!(aut_order(&cycle_graph(6)), 12); // D_6, order 2n
        assert_eq!(aut_order(&cycle_graph(7)), 14);
    }

    #[test]
    fn complete_is_symmetric() {
        assert_eq!(aut_order(&complete_graph(5)), 120); // S_5
        assert_eq!(aut_order(&complete_graph(4)), 24);
    }

    #[test]
    fn path_reflection_only() {
        assert_eq!(aut_order(&path_graph(5)), 2); // just the flip
        assert_eq!(aut_order(&path_graph(6)), 2);
    }

    #[test]
    fn php_symmetry_group() {
        // PHP_{p,h} formula symmetry group is S_p x S_h, order p! * h!.
        let (nv, cl) = php(3, 2);
        let cg = cnf_to_graph(nv, &cl);
        assert_eq!(aut_order(&cg.graph), 12); // 3! * 2!
        let (nv, cl) = php(4, 3);
        let cg = cnf_to_graph(nv, &cl);
        assert_eq!(aut_order(&cg.graph), 144); // 4! * 3!
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
