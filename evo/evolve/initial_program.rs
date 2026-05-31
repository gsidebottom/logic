// =====================================================================
// EVOLVE-BLOCK-START
// =====================================================================
//
// **Eff-layer ordering policy — pure functions on effective counts.**
//
// These three functions are the entire algorithmic surface that
// OpenEvolve / the `evo/evolve/` rig is allowed to mutate.  The
// surrounding `EffectiveCountWrapper` glue (count maintenance,
// prefix tracking, CDCL integration) is load-bearing for correctness
// and stays fixed.
//
// CONTRACTS — DO NOT BREAK (the evaluator will reject candidates
// that violate these, via cross-checking against CaDiCaL verdicts on
// the evo/ benchmark set):
//
//   `should_reorder_sum(counts, tau) -> bool`
//      Pure, no side effects.  When `false`, the caller skips the
//      reorder and uses identity order — that's a sound shortcut
//      (Sum semantics are visit-all in any order).
//
//   `sum_visit_order(counts, tau) -> Vec<usize>`
//      MUST return a PERMUTATION of `0..counts.len()` — every index
//      EXACTLY once, no duplicates, no drops.  Sum semantics
//      require visiting every child to gather lits; dropping any
//      breaks soundness.  The "no reorder" answer is the identity
//      permutation.
//
//   `prod_visit_order(counts) -> Vec<usize>`
//      Returns a subset of `0..counts.len()` in visit order.  MAY
//      drop indices whose `counts[i] == 0.0` (those are provably
//      unreachable through this Prod given the current prefix; the
//      whole point of the eff layer is to prune them).  MUST NOT
//      drop any index with `counts[i] > 0.0` and MUST NOT duplicate
//      any index.  Order of the kept indices is free.
//
// INPUTS:
//   `counts[i]` = the static "effective count" for the i-th
//   child/alt — a non-negative f64 (or `f64::INFINITY` when the
//   parent isn't in the precomputed index; treat infinities as
//   "very large, unknown precisely").  Could be 0 (provably
//   blocked) up to the total path count below this node.
//
//   `tau` = variance-gate threshold from the wrapper config.
//   `tau == 0.0` is "always reorder" (legacy behavior).
//   `tau == f64::INFINITY` is "never reorder Sums" (gate trips false).
//   Intermediate values gate by log10(max/min) >= tau.

/// Variance gate: should `sum_visit_order` actually re-sort, or is
/// the spread of sibling counts small enough to leave them alone?
fn should_reorder_sum(counts: &[f64], tau: f64) -> bool {
    if counts.len() < 2 { return false; }
    if tau == 0.0 { return true; }
    let mut min_nz: f64 = f64::INFINITY;
    let mut max_nz: f64 = 0.0;
    let mut any_zero = false;
    let mut any_nonzero = false;
    for &c in counts {
        if !c.is_finite() {
            // `inf` here means "no precomputed count" (parent not in
            // the index).  Treat as max — always reorder when one
            // sibling has unknown count.
            return true;
        }
        if c == 0.0 {
            any_zero = true;
        } else {
            any_nonzero = true;
            if c < min_nz { min_nz = c; }
            if c > max_nz { max_nz = c; }
        }
    }
    if any_zero && any_nonzero { return true; }
    if !any_nonzero { return false; }      // all zero — order doesn't matter
    if min_nz <= 0.0 || max_nz <= 0.0 { return false; }
    (max_nz / min_nz).log10() >= tau
}

/// Sum-child visit order: descending by count (high-leverage first).
/// Visiting high-count children early feeds CDCL better decision
/// variables and produces tighter proofs (matches the best-scoring
/// baseline).  Soundness is order-independent: Sum visits all children.
fn sum_visit_order(counts: &[f64], tau: f64) -> Vec<usize> {
    let n = counts.len();
    if !should_reorder_sum(counts, tau) {
        return (0..n).collect();
    }
    let mut idx: Vec<usize> = (0..n).collect();
    // Order among equal-count children is soundness-irrelevant (Sum is
    // visit-all), so use the cheaper unstable sort to save CPU.
    idx.sort_unstable_by(|&a, &b|
        counts[b].partial_cmp(&counts[a]).unwrap_or(std::cmp::Ordering::Equal));
    idx
}

/// Prod-alt visit order from a slice of per-alt effective counts.
/// Filters zero-count alts (provably blocked) then sorts descending
/// by count so the "richest" surviving alts (most satisfying paths)
/// get tried first — finds SAT witnesses faster in DFS.
/// Infinite counts (unknown) are placed after finite ones.
fn prod_visit_order(counts: &[f64]) -> Vec<usize> {
    let mut keep: Vec<(usize, f64)> = counts.iter().enumerate()
        .filter_map(|(i, &c)| if c > 0.0 { Some((i, c)) } else { None })
        .collect();
    // Prod order among equal-count alts is free, so use unstable sort.
    keep.sort_unstable_by(|a, b| {
        let (af, bf) = (a.1.is_finite(), b.1.is_finite());
        if af && bf {
            b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal)
        } else if af {
            std::cmp::Ordering::Less    // finite before infinite
        } else if bf {
            std::cmp::Ordering::Greater
        } else {
            std::cmp::Ordering::Equal
        }
    });
    keep.into_iter().map(|(i, _)| i).collect()
}

// =====================================================================
// EVOLVE-BLOCK-END
// =====================================================================
