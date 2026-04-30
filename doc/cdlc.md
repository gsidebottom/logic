# Adding CDCL to the Matrix Method

This document records the work done to bolt a CDCL-style search controller
onto the matrix-method DFS in this crate.  The implementation lives in
[`src/controller/cdcl.rs`](../src/controller/cdcl.rs) as `CdclController`.

## Motivation

The matrix-method search with `SmartController` already handles cross-clause
unit propagation (watched-literal scheme) and turns out to be surprisingly
competitive on PHP-style problems — faster than CaDiCaL on `php-12-11`.
But on instances like `benchmarks/rast-p11.k20.cnf`, where CaDiCaL finishes
in milliseconds, matrix takes effectively forever.  The hypothesis was that
CDCL — conflict-driven *clause learning*, plus VSIDS, restarts, phase
saving, and LBD-based clause deletion — would close the gap.

## Why this is non-obvious in the matrix setting

CDCL is normally described against a CNF + assignment + watched-literal
solver.  We have:

* An **NNF tree** (Sum / Prod / Lit) being traversed depth-first.
* `Sum` = visit every child; `Prod` = pick one alternative.
* A "path" through the matrix is a complete sequence of choices, recorded
  as `(prefix_literals, prefix_positions, prefix_prod_path)`.
* Pruning happens when a path's literal sequence contains a complementary
  pair — what CDCL would call a *conflict on the assignment*.

So the matrix-method analog of "decision level" is the length of
`prefix_prod_path` (the chain of `Prod`-alternative choices the DFS has made),
and "the assignment" is the current `prefix_literals`.  Every CDCL feature
needed an analog in this geometry.

## The controller protocol

The DFS engine drives traversal through a trait, [`PathSearchController`]
(`src/controller/mod.rs`).  The key method is

```rust
fn should_continue_on_prefix(
    &mut self,
    prefix_literals:  &Vec<&Lit>,
    prefix_positions: &PathPrefix,
    prefix_prod_path: &ProdPath,
    is_complete:      bool,
) -> Option<usize>;
```

Return value:

* `None` — continue forward.
* `Some(0)` — backtrack one level (chronological).
* `Some(K)` for `K ≥ 1` — backtrack `K + 1` levels (non-chronological
  backjumping; matrix-CDCL uses `Some(1)` after a learned-clause-driven
  cascade conflict).
* `Some(usize::MAX)` — unwind the entire DFS (used by restarts).

Two more controller hooks were added during this work to support restarts:

```rust
fn is_restart_pending(&self) -> bool { false }
fn complete_restart(&mut self) {}
```

The driver `NNF::classify_paths_uncovered_only` checks `is_restart_pending`
after each DFS run and re-invokes the engine after `complete_restart()`,
keeping accumulated knowledge (learned clauses, VSIDS scores) across the
restart.

## Stepwise build-up

CDCL was built in named steps so each piece could be tested in isolation
against the existing `SmartController`.  Two key invariants held throughout:

1. `cdcl_agrees_with_smart_on_all_cases` (in `src/bin/sat.rs`) — every
   formula in the test suite must be classified the same way by both
   controllers.
2. The full lib + sat-bin test suite (currently 141 + 23 = **164 tests**)
   must stay green.

### Step 1 — scaffolding + reasoned trail

* Added `CdclController<F>` wrapping a `BacktrackWhenCoveredController`.
* Per-pushed-lit `trail: Vec<TrailLit>` — every fact known on the current
  path, in push order.
* Conflict counting (`conflict_count: usize`).

At this stage the controller is observational — it behaves identically to
`SmartController` outwardly.

### Step 2 — reason tracking on the trail

Trait method gained `prefix_prod_path: &ProdPath` and `is_complete: bool`,
so a controller can attach decision-level information to each trail entry.

```rust
enum Reason {
    Decision,             // Pushed because a Prod chose this alt
    SumForced,            // Direct Lit child of a Sum (no choice)
    Implied(usize),       // Step 3+: clause_id that forced it
}

struct TrailLit {
    lit: Lit,
    reason: Reason,
    decision_level: usize,
}
```

Decision level = `prefix_prod_path.len()` at push time.

### Step 3 — cross-clause unit propagation

Ported the `SmartController` watched-literal scheme into the CDCL
controller, adding an `Implied(clause_id)` reason variant so the
implication graph is reconstructable.  Per Prod-of-Lits "clause"
(with Sum-only ancestors) we maintain:

* `prod_alts[clause_id]: Vec<Lit>` — the alternatives.
* `prod_total / prod_blocked / prod_alt_blocked` — blocked-alt counts.
* `watches[lit_idx]: Vec<(clause_id, alt_idx)>` — the watch lists.
* `implied_lit_counter[lit_idx]` — many clauses can imply the same lit.

When a push leaves only one unblocked alt, that alt's lit is added to the
trail with `Reason::Implied(clause_id)` and propagation cascades.

`push_frames: Vec<PushFrame>` record every blocking / implied-lit
mutation per DFS lit push so that backtrack can undo them precisely.

### Step 4 — 1UIP conflict analysis

When a cascade conflict fires (every alt of some `clause_id` is blocked)
we walk the implication graph backwards starting from the lits that block
the conflict clause's alts.  Repeatedly:

1. Find the most-recent trail lit `p` in the learning set at
   `conflict_level`.
2. If `p`'s reason is `Implied(R)`: remove `p`, add `¬r` for every
   other alt `r` of `R`.  This is resolution at the implication-graph
   level.
3. If `p`'s reason is `Decision` or `SumForced`: stop.

Stopping when only one lit remains at `conflict_level` gives the **1UIP**
(First Unique Implication Point).

The result is a `LearnedClause`:

```rust
pub struct LearnedClause {
    pub alts: Vec<Lit>,            // negations of the learning set
    pub backjump_level: usize,     // 2nd-highest level among alts
    pub lbd: usize,                // (added by LBD step)
}
```

At Step 4 the learned clause is observational — stored, not yet wired.

### Step 5 — register learned clauses with the watch lists

Each derived `LearnedClause` gets a fresh `clause_id` (`prod_alts.len()`)
and is treated identically to original cubes thereafter:

* `watches[alt.lit_idx]` gets a `(clause_id, alt_idx)` entry per alt.
* `prod_total`, `prod_blocked`, `prod_alt_blocked` extended.
* The clause is registered *while* its complement lits are on the trail —
  so we walk the trail to attribute each blocking to the correct
  push-frame.  Trail entries beyond the in-progress frame route to
  `current_frame` rather than to an existing `push_frames[i]`.

This means the next time the DFS approaches the same configuration, the
learned clause fires propagation early.

### Step 6 — non-chronological backjumping

After Step 5, the natural follow-up: instead of returning `Some(0)` on a
cascade conflict, return `Some(1)` to escape the current `Prod`'s alt
loop entirely.  In our flat Sum-of-Prods CNF-complement structure this
is the right backjump distance — the newly-active learned clause then
drives propagation as the search re-descends from the previous Prod's
next alternative.

`Some(0)` is still used for path-level conflicts (where we have no
learned clause justifying the more aggressive jump).

### VSIDS

Variable-ordering heuristic.  Each variable has an *activity* score that's
bumped every time it appears in a learned clause's alts.  Decay is
implemented the lazy way (multiply the global `bump_value` by
`1 / decay_factor` per conflict, normalize when scores exceed `1e100`).

In `prod_ord`, after the propagation-driven filter runs, surviving
alternatives are sorted by descending activity — the
most-recently-conflicted variables are tried first.

Defaults: `bump_value = 1.0`, `decay_factor = 0.95`.

### Restarts (Luby schedule)

After each cascade conflict, `conflicts_since_last_restart` is
incremented.  When it reaches `restart_threshold = restart_unit *
luby(restart_count + 1)`, `restart_pending` is set; the next
`should_continue_on_prefix` call returns `Some(usize::MAX)` to unwind
the entire DFS.  The driver then calls `complete_restart()` and
re-invokes the engine.

```
luby: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, …
```

Defaults: `restart_unit = 100` conflicts; first restart after 100
conflicts.

### Phase saving

When a variable is popped from the trail (during backtrack or restart)
we record its polarity in `saved_phase[var]`.  In `prod_ord`, after the
VSIDS sort, alts whose polarity matches their variable's saved phase
win ties — so revisiting a Prod re-tries the polarity that was
previously productive.  Especially valuable across restarts: the saved
phases capture "what worked before" while the trail is wiped.

### LBD-based learned-clause deletion

Each learned clause is tagged with its **Literal Block Distance** —
the count of distinct decision levels among the lits in the original
learning set:

```rust
let unique_levels: HashSet<usize> = learning.values().copied().collect();
let lbd = unique_levels.len();
```

Low LBD = the clause crosses fewer decision frontiers = more likely to
fire propagation early = more valuable to keep.

At restart time, when `live_learned_clause_count() > learned_clause_limit`,
`reduce_learned_clauses()` runs:

1. Collect `(clause_id, lbd)` for every live learned clause.
2. Sort by LBD ascending.
3. Mark the top-LBD half as deleted (`clause_deleted[clause_id] = true`).
4. **Compact the watch lists** — remove entries pointing to deleted
   clauses, so `process_push` doesn't walk through them.

`process_push` early-skips deleted clauses:

```rust
if self.clause_deleted[clause_id] { continue; }
```

Doing the reduction at restart time is convenient because the trail is
about to be cleared anyway — there can be no live `Reason::Implied(...)`
references to clauses we're about to delete.  Original (preprocessed)
clauses are never deleted.

#### LBD tuning — the surprise

The default `learned_clause_limit` was set conservatively to **100000**
after discovering that low limits regress the matrix-method search
significantly.

| Limit | PHP-12-11 | PHP-14-13 |
|------:|----------:|----------:|
| 2 000 | 19.0 s | (timeout) |
| 20 000 | 1.27 s | 210 s |
| 50 000 | — | 38.6 s |
| 100 000 | 1.27 s | 35.6 s |
| 200 000 | 1.27 s | 35.6 s |
| baseline (no LBD) | 1.14 s | 33.5 s |

Diagnosis: with low limits, the reducer fires repeatedly during search.
Each reduction throws away learned clauses that were still providing
*propagation* — short-circuiting the path tree.  The matrix-method
search loses propagation power faster than it gains via the smaller
watch lists, and the fixed cost of the reduction itself doesn't pay
back.  Even `limit=20000` (where the reducer fires only a few times on
PHP-12-11) had 6× regressions on PHP-14-13.

The **watch-list compaction** discovery is worth calling out separately.
Without compaction (just early-skip via `clause_deleted`), PHP-12-11 at
limit=2000 timed at 19 s.  Adding `watches[i].retain(|&(c,_)| !deleted[c])`
inside the reducer brought that down to ~6 s — but still much worse
than baseline.  The bottleneck before compaction wasn't the per-entry
skip cost; it was that the Luby schedule's growing windows let learned
clauses pile up to 8000+ between restarts (observed via instrumentation).

The current default is effectively a safety bound for runaway searches.
The infrastructure is in place; the policy could use further tuning,
or could be replaced with a different deletion heuristic (LBD-locking,
age-based scoring, or hybrid schemes used in modern solvers).

## Cumulative results

| Stage | Random 3-SAT n=100 | PHP-12-11 | Notes |
|-------|-------------------:|----------:|-------|
| Baseline `SmartController` | — | — | starting point |
| Steps 1–6 (CDCL core) | — | 1.14 s | learned clauses + 1UIP + backjump |
| + VSIDS | 23.3 s | — | variable activity ordering |
| + Restarts (Luby) | 7.85 s | — | restart_unit = 100 |
| + Phase saving | 5.15 s | 1.14 s | tiebreaker after VSIDS |
| + LBD (limit=100 000) | 0.63 s¹ | 1.27 s | conservative; reducer rarely fires |

¹ The random 3-SAT timing here used a different generator (Python with
`random.seed(42)`, n=100, m=425) than the cumulative summary's number,
so it's not directly comparable; treat it as an order-of-magnitude
sanity check.

CaDiCaL on the same `php-12-11` takes **>2 minutes** — so the matrix
method with this CDCL stack is faster than CaDiCaL by a wide margin on
PHP, but `rast-p11.k20.cnf` still times out (CaDiCaL solves it in
milliseconds).  The remaining gap is structural: see "Open questions".

## Test coverage

The CDCL controller has dedicated unit tests for each step plus
integration coverage:

* **Step-1/2 trail tests** — pushes/pops produce the expected reason
  chain.
* **Step-3 propagation tests** — cascade conflicts fire, blocked-counts
  and implied-lit counters stay consistent across backtrack.
* **Step-4 1UIP tests** — learned clauses match worked examples.
* **Step-5 watch-registration tests** — initial blockings attribute to
  the correct push-frames; backtrack undoes them.
* **Step-6 backjump tests** — the search returns `Some(1)` on cascade
  conflicts.
* **VSIDS tests** — bumps + decay + normalization.
* **Restart tests** — `complete_restart()` clears trail/blocked-counts,
  preserves watches and activities.
* **Phase-saving tests** — pop records polarity; survives restart.
* **LBD tests**:
  * `lbd_one_when_all_lits_at_same_level`
  * `live_learned_count_tracks_clause_deleted`
  * `reduce_learned_clauses_marks_high_lbd_half`
  * `deleted_clauses_skipped_during_propagation`
* **Cross-controller agreement** — `cdcl_agrees_with_smart_on_all_cases`
  validates that the CDCL controller classifies every test formula the
  same as `SmartController`.

All 164 tests pass with the LBD step landed.

## Open questions / next steps

* **`rast-p11.k20.cnf` is still out of reach.**  The CDCL stack helps
  on PHP and random 3-SAT, but the rast benchmarks resist all current
  heuristics.  Possible directions:
  * Better variable-ordering at preprocess time (look at clause
    structure, not just dynamic activity).
  * On-the-fly clause minimization (drop redundant lits from learned
    clauses before they're registered).
  * A different deletion heuristic — current LBD-deletion hurts even
    when tuned generously.
* **LBD policy.**  The implementation works but the default limit is
  high enough that the reducer rarely fires.  A growing-cap scheme
  (`limit *= 1.05` per reduction) or LBD-locking (don't delete a clause
  that's currently a `Reason::Implied`) might allow lower defaults
  without regression.
* **Mid-search reduction.**  All deletion happens at restart time
  because the trail-clearing makes safety trivial.  A scheme that
  triggers reduction during search (e.g. after backjump, when only the
  surviving prefix is on the trail) could let us use tighter caps.
* **Decision-level granularity.**  Our "decision level" is
  `prefix_prod_path.len()` — the count of Prod choices.  But Sum
  visit-all forks are also branching points.  Whether the LBD heuristic
  would work better with a finer-grained level concept is open.
* **Why are there no cascade conflicts on faulty-adder formulas?**
  The instrumentation in `doc/lazy-dfs.md` shows `learned = 0` on
  every faulty-adder bench, including the 27-bit cases where the
  matrix DFS runs for 220 ms (UNSAT) or 56 s (SAT) and accumulates
  hundreds of thousands to millions of conflicts.  All conflicts
  are *path-level* — the new lit's complement is already on the
  trail at push time.  Cascade conflicts (a clause whose every alt
  becomes blocked by propagation) never fire on these formulas, so
  1UIP analysis never runs and learned clauses never get
  registered.  This means CDCL's defining feature is inert on
  hardware-verification workloads, and only the watched-literal
  propagation infrastructure earns its keep.  Worth understanding
  whether this is a property of the formulas, the matrix
  representation, or the order in which alts get blocked — and
  whether structuring the search differently (e.g. eager decision
  at every Prod) would surface cascade conflicts.
* **Try a serious benchmark suite** (SATLIB random 3-SAT, HWMCC small
  instances) systematically and characterize where matrix-CDCL is
  competitive vs. not.  The current measurements (PHP, one random
  3-SAT, the rast-p11 family) are too narrow to draw conclusions about
  which problem classes the matrix-CDCL stack is well-suited to.
* **Lazy matrix-DFS — investigated, conditionally deferred.**  The
  hypothesis was that restructuring the search to commit decisions
  only when propagation forces them (skipping the structural
  enumeration of already-determined Sum-children) would yield a
  meaningful per-step speedup.  Instrumentation showed it depends
  heavily on the workload: already-implied pushes are **<0.01% on
  PHP, ~10% on random 3-SAT, ~5% on small faulty-adder SAT
  instances — but ~62% on both the 27-bit UNSAT (220 ms) and 27-bit
  SAT (56.6 s) faulty-adder cases**.  The 62% pattern isn't
  UNSAT-specific; it shows up on any hardware-verification-style
  formula where the matrix DFS has to explore a combinatorial
  space under heavy propagation.  Lazy DFS could plausibly save
  7-18% on those workloads but offers no win on SAT-search or PHP.
  Even a successful lazy-DFS implementation wouldn't close the gap
  to CaDiCaL on the 27-bit cases (currently 166× / 37 800× slower).
  Full write-up: [`lazy-dfs.md`](./lazy-dfs.md).  Recommendation:
  scope a partial fast-path hook as a smaller experiment before
  committing to a full lazy driver.

## File map

* `src/controller/cdcl.rs` — `CdclController`, `LearnedClause`,
  `Reason`, `TrailLit`, `PushFrame`, all CDCL state and logic.
* `src/controller/mod.rs` — `PathSearchController` trait, including
  the `is_restart_pending` / `complete_restart` hooks added for
  restart support.
* `src/matrix.rs` — `classify_paths_uncovered_only` has the outer
  restart loop wrapping the DFS engine.
* `src/bin/sat.rs` — `--cdcl` CLI flag, `cdcl_agrees_with_smart_on_all_cases`
  cross-controller test.
