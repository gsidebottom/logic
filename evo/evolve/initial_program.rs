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
// CONTRACTS — these depend on the build mode:
//
//   * NARROW / sound-by-construction (default, or `--features
//     evolve_guard`): the two ordering fns MUST preserve every branch
//     (permutation for Sum; keep-every-positive-count for Prod), so the
//     policy can only change *order*, never the verdict.
//   * WIDE / open evolution (`--features evolve_wide`): a policy MAY
//     DROP branches for aggressive pruning (sum_visit_order may return a
//     subsequence; prod_visit_order may drop reachable alts).  This can
//     make the search UNSOUND — that's allowed.  Soundness is enforced
//     DOWNSTREAM by the evaluator (matrix cover proof where available +
//     SAT-witness check + ground-truth drat-verified labels), NOT by
//     construction.  A wrong UNSAT/SAT on the benchmark scores 0; a
//     correct-but-unprovable UNSAT still counts as a solve.
//
// HARD RULES (both modes — never relaxed, enforced by an always-on
// sanitizer so a violation can't crash, only get cleaned):
//   * indices MUST be in range `0..counts.len()` and MUST NOT be
//     duplicated (out-of-range / dup indices are silently dropped).
//   * all three fns MUST be pure (no I/O, no panic on empty/NaN/Inf).
//
//   `should_reorder_sum(counts, tau) -> bool`
//      When `false`, the caller uses identity order (sound: Sum is
//      visit-all in any order).
//   `sum_visit_order(counts, tau) -> Vec<usize>`
//      Visit order for Sum children.  NARROW: a permutation of
//      `0..counts.len()`.  WIDE: MAY drop indices (prune children).
//   `prod_visit_order(counts) -> Vec<usize>`
//      Visit order for Prod alts (subset).  Both modes MAY drop
//      zero-count alts (provably blocked).  WIDE: MAY also drop
//      positive-count alts (aggressive pruning).
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

/// Sum-child visit order: **descending** by count (high-leverage
/// first).  Soundness is order-independent — Sum is visit-all, so any
/// permutation gives identical verdicts; only search *speed* changes.
///
/// **Why descending (counterintuitive).**  The original heuristic
/// sorted *ascending* — visit low-count, tightly-constrained children
/// first to "fail fast."  Good DFS instinct, but the eff layer sits on
/// a full CDCL engine that finds contradictions via propagation +
/// conflict analysis, not by walking to complementary leaves.  What
/// CDCL benefits from is good *decision variables*: a high-count child
/// carries the high-leverage variables (in the most paths/clauses), so
/// deciding them first triggers larger propagation cascades and yields
/// conflicts higher in the tree → shorter, more general learned
/// clauses.  Ascending fought VSIDS; descending reinforces it.  The
/// same principle applies to `prod_visit_order` below.
///
/// Empirically established on the `evo/` struct-eff set: the
/// ascending→descending flip (sum, then prod) gains +2 solved at both
/// 30s and 60s budgets.  The prod flip was found by the
/// `evo/evolve/` OpenEvolve rig; the sum flip by hand.  See its README.
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

/// Prod-alt visit order: filter zero-count alts (provably blocked),
/// then sort **descending** by count so the "richest" surviving alts
/// (the branches with the most satisfying paths beneath them) are
/// tried first — reaches SAT witnesses faster in the DFS, and feeds
/// CDCL better decisions on UNSAT (same "high-leverage first"
/// principle as `sum_visit_order`).  Infinite counts ("unknown", parent
/// not indexed) sort *after* finite ones — defer the unknowns.
/// Soundness: every positive-count alt is kept (only zero-count,
/// provably-blocked alts are dropped); reordering the kept set can't
/// change the verdict.
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
