// =====================================================================
// EVOLVE-BLOCK-START
// =====================================================================
//
// **CDCL search-control policy — restart schedule + VSIDS decay.**
//
// These two pure functions are the entire evolvable surface of the
// CDCL engine.  Everything else (watched-literal BCP, 1UIP conflict
// analysis, the trail, clause learning) is load-bearing for
// correctness and stays fixed.
//
// SOUND BY CONSTRUCTION: both are pure EFFICIENCY knobs.  CDCL reaches
// the same verdict for ANY decision order, restart schedule, or
// activity-decay rate (only learned clauses are ever dropped; original
// clauses never are) — so no value these return can make a wrong
// SAT/UNSAT, only change how fast the search converges.  The caller
// also CLAMPS the outputs (restart interval >= 1 so it can't hang;
// decay into the open interval (0,1) so VSIDS stays stable), so a
// degenerate/NaN return is harmless.
//
// INPUTS:
//   `restart_count` — how many restarts have already happened (0 during
//     the first interval).  Use it to make the schedule / decay
//     ADAPTIVE (e.g. explore broadly early, dive deep later).
//   `restart_unit`  — the configured base restart interval (100 in
//     production); the seed scales the Luby sequence by it.
// You may call the module-level `luby(i)` helper (1-indexed Luby
// sequence 1,1,2,1,1,2,4,…) or compute any other schedule.

/// Conflicts to allow before the next restart, given the restart index.
/// Seed: Luby(restart_count+1) × unit — the classic Luby policy.
/// Ideas worth trying: a larger effective unit (fewer restarts, deeper
/// dives on hard UNSAT), geometric/linear schedules, or a unit that
/// grows with `restart_count`.
fn restart_interval(restart_count: usize, restart_unit: usize) -> usize {
    restart_unit * luby(restart_count + 1)
}

/// VSIDS activity decay applied per conflict (`bump_value /= decay`),
/// given the restart index.  Seed: constant 0.95 (MiniSAT-style).
/// Lower = forget faster (more reactive to recent conflicts); higher =
/// longer memory.  May vary with `restart_count` to anneal over time.
fn vsids_decay(_restart_count: usize) -> f64 {
    0.95
}

// =====================================================================
// EVOLVE-BLOCK-END
// =====================================================================
