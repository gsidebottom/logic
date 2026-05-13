# Strategic Cover — Design

A demand-driven cover-search controller for the dual framework: A
(cover search) watches B (path search)'s current prefix and the
effective path counts on subtrees B is about to explore, and
prioritizes complementary pairs whose endpoints fall inside the
smallest-count subtrees at B's frontier.  The bet: those pairs are
the highest-leverage covers — covering them collapses a tractable
subtree completely, which immediately prunes B's DFS.

## Why

Today every cover controller (`Basic`, `Greedy`,
`GreedyDynamic`, `CnfBans`, `BddBans`) makes its pair-selection
decisions on **static, global** properties of the NNF:

- `Basic`: pool order
- `Greedy`: box-size (paths a pair covers across the *whole* matrix)
- `GreedyDynamic`: submodular marginal gain across the whole matrix
- `Cnf/BddBans`: completeness check, not prioritization

None of them know what B is currently exploring.  This means A
spends time on pairs that:

- Cover paths through subtrees B will never reach (because some
  ancestor literal of B's prefix already forces a different branch)
- Cover huge swaths of "average" paths when a tiny, easy-to-clear
  subtree at B's frontier would have given B a much faster prune

The Effective layer (`src/dual/path_effective.rs`) already maintains
per-NNF-node effective path counts `e(X | P)` as B descends — paths
through `X`'s subtree that are *not* already foreclosed by B's
current prefix `P`.  That information is the answer to "what is B
about to do."  It's right there in shared mutable state on B's
thread.  A just doesn't see it.

**Strategic Cover plugs A into that signal** so A's priorities
follow B's actual exploration in real time.

## The mechanic

1. **Snapshot.**  Add a `PathFrontier` shared structure
   (`Arc<Mutex<PathFrontier>>`) updated by `EffectiveCountWrapper`
   on every push/pop and read by A's `next_pair_index`.  Carries:
   - `prefix_len: usize` — to detect staleness
   - `counts: Vec<(NodePtr, f64)>` — per-NNF-node effective count
     under the current prefix, only for nodes with `e > 0`

2. **A's selection.**  In `StrategicCoverController::next_pair_index`:
   - For each candidate pair `(p1, p2)` in the pool, look up the
     deepest common NNF ancestor `lca(p1, p2)` (cached, since pairs
     don't change).
   - Score the pair by `e(lca | P)` from the snapshot — i.e. the
     effective path count of the smallest subtree both endpoints
     live in, under B's current prefix.
   - Smallest non-zero `e` first.  Ties broken by FIFO.

3. **Adaptation.**  As B's prefix changes, the per-node `e` values
   shift.  A re-ranks lazily: a min-heap keyed on the *last
   observed* `e(lca | P)`.  On every `next_pair_index` call, A
   peeks the top, re-evaluates its current `e`; if stale, sift
   down; repeat.  Amortized cheap on prefix changes that don't
   reorder much.

4. **Seeding.**  Same as Greedy: `seed_pool` mines all
   cross-clause complementary pairs up front.  Strategic isn't
   about which pairs exist — it's about *order*.

5. **Termination.**  Unchanged.  Same `is_complete` story, same
   B-exhaustion path.

## Why this should help

The Effective layer's structural pruning already turns "huge
subtree" into "ignore it" when `e(X | P) = 0`.  What it can't do is
*make* `e(X | P) = 0` for a subtree that's currently small but
nonzero.  That's a job for A: emit pairs that cover the few
remaining paths in `X`, after which the Effective layer prunes `X`
on the next visit.

Concretely the predicted wins are on rows where:

- B's exploration has **uneven branching**: some Sum-children at the
  frontier carry tens of paths, others carry 1 or 2
- A **could** clear the 1-or-2 subtree with one or two well-chosen
  pairs, *if* it knew which subtree mattered
- Without coupling, A is just as likely to be working on covering
  paths in the larger sibling — wasted work

BMC count-zeros is the textbook case: each bit position is a small
local subtree.  27-bit faulty-adder is mixed — each fault-bit gate
is a small block but they're interlinked.  random-3sat has no
structure so we expect Strategic ≈ Basic there.

## Why this should not regress

- Soundness is unaffected.  All emitted pairs are still mined from
  the NNF (`mine_pairs`); priority changes don't change which
  pairs are valid.
- Completeness is unaffected.  Strategic eventually emits every
  pair (not just frontier ones) because its priority key never
  permanently demotes a pair — once B advances, the `lca` of an
  old-frontier pair becomes ancestral and its `e` re-evaluates.
- The base layer (`Basic`/`Greedy`/`Dynamic`) does not have a
  fundamentally different *set* of pairs than Strategic — only
  ordering differs.
- The Effective layer is still hard-wiring CDCL as B's inner (the
  May-2026 experiment confirmed CDCL is essential there; see
  `dual-search-design.md`).  Strategic plugs in alongside that, not
  instead.

## Architecture sketch

### New shared snapshot
```rust
// src/dual/path_frontier.rs (new)

use std::sync::atomic::AtomicUsize;

/// Snapshot of B's current effective-count state, written by the
/// Effective layer and read by Strategic cover search.
///
/// Lock-light: B updates this on every push/pop (rare-ish — only
/// when prefix changes); A reads it on every `next_pair_index`
/// (frequent).  A `Mutex` is fine but a seqlock-style snapshot
/// would also work if contention shows up.
pub struct PathFrontier {
    /// Monotonic version counter — A can short-circuit re-ranking
    /// if version hasn't changed since last poll.
    pub version: AtomicUsize,
    /// Effective counts under B's current prefix, keyed by raw NNF
    /// pointer (same key space as `EffectiveCountIndex`).  Empty
    /// HashMap → no information yet (B hasn't started).
    pub counts: Mutex<HashMap<*const NNF, f64>>,
}

unsafe impl Send for PathFrontier {}
unsafe impl Sync for PathFrontier {}
```

### B-side hook
`EffectiveCountWrapper::sync_to_prefix` already maintains the
per-node count map (`self.counts: EffectiveCounts`).  Add an
optional `frontier: Option<Arc<PathFrontier>>` field; on every
`sync_to_prefix` (i.e. every push/pop), update the shared map:

```rust
if let Some(ref f) = self.frontier {
    let mut guard = f.counts.lock().unwrap();
    self.counts.snapshot_into(&mut *guard);  // (new helper)
    f.version.fetch_add(1, Ordering::Release);
}
```

`snapshot_into` is one new method on `EffectiveCounts` — iterate
nonzero entries, copy into the target map.  Cost: proportional to
the count of nonzero nodes, amortizing across many path steps.

### A-side
`StrategicCoverController` holds:
- `Arc<PathFrontier>` (shared with B)
- A min-heap of `(e_score, fifo, pair_idx)`
- A cache: `pair_idx → (lca_node, last_seen_version)`

Plumbed through `solve_dual` by introducing it as a parameter
(currently the driver only owns A, B, pool, state).  Need a small
change to `solve_dual` to construct the `Arc<PathFrontier>`, hand it
to A's controller, and ensure B's `EffectivePathController` picks
it up (a new constructor:
`EffectivePathController::with_frontier_publisher(frontier)`).

### LCA precomputation
For every pair `(p1, p2)` in the pool, the LCA is a function of
NNF positions and never changes during a run.  Strategic computes
it once, on pair arrival, using the same position-resolution
machinery `flat_pair_triggers` already relies on.  Cost: per-pair
O(min(|p1|, |p2|)) which is small for flat clauses.

### Re-rank strategy
On `next_pair_index`:
1. `let v = frontier.version.load(Acquire);`
2. If `v == last_version`, just pop the heap (no changes).
3. Otherwise, drain the heap into a Vec, re-score each entry from
   the current snapshot, rebuild the heap, set `last_version = v`.
4. Pop the top.

Worst-case rebuild is O(N log N) in pool size, paid only when B's
prefix changed since A last polled.  In practice B's prefix is far
slower than A's polling cadence so most polls are cache-hits.

## Comparison

| Controller       | Pair selection key             | B-coupled? |
|------------------|--------------------------------|------------|
| Basic            | pool order                     | no         |
| Greedy           | static box size                | no         |
| GreedyDynamic    | submodular marginal gain       | no         |
| **Strategic**    | `e(lca(p1,p2) \| P)`, asc       | **yes**    |

Strategic is the first controller that adapts to B's runtime
exploration state.  It's small but novel within the framework.

## Expected impact

Predictions (to be checked against the focused 27-bit bench):

| row                                | greedy×eff | strategic×eff prediction |
|------------------------------------|------------|--------------------------|
| random-3sat n=30 (SAT)             | ~1.5 ms    | tie (no structural locality) |
| faulty_add 27/1 UNSAT              | ~10 ms     | maybe 20% faster (each fault-bit block is small) |
| faulty_add 27/2 SAT                | ~22 ms     | unclear (SAT path may find an early uncovered before Strategic helps) |
| BMC count-zeros n=8 w=16 UNSAT     | ~6 ms      | 1.5–3× faster (per-bit blocks are textbook small subtrees) |

If Strategic is *worse* anywhere it'll be because the LCA lookup
and heap re-ranking overhead exceeded the savings on small inputs.
The fallback: keep Greedy×eff as the default and ship Strategic as
an opt-in for structured/big formulas where the coupling pays off.

## Implementation plan

1. **`src/dual/path_frontier.rs`** (new): `PathFrontier` shared
   snapshot, ~30 lines.
2. **`src/dual/effective_count.rs`**: `snapshot_into` method on
   `EffectiveCounts`, ~10 lines.
3. **`src/dual/path_effective.rs`**:
   - `EffectivePathController::with_frontier_publisher(frontier: Arc<PathFrontier>)`
     constructor.
   - `EffectiveCountWrapper` gains optional frontier field; updates
     on each `sync_to_prefix`.
4. **`src/dual/cover_strategic.rs`** (new): `StrategicCoverController`,
   ~200 lines.
   - Heap + LCA cache + version-keyed re-rank logic.
   - `seed_pool` reuses `mine_pairs` like Greedy does.
5. **`src/dual/mod.rs`**: re-export, `pub use`.
6. **`src/dual/bench.rs`**: add `run_dual_strategic_effective`, plug
   into both bench tables as a new column `strategic×eff` (or
   replace `greedy×eff_b` slot — we removed that column, the
   header is 6 columns again).
7. **Tests**:
   - One unit test covering the cross-check pattern other cover
     controllers have (`bench_focused_top_config`'s cross-check
     style — same verdict as Basic on every formula).
   - One that confirms Strategic's ordering actually responds to
     prefix changes (drive B for k steps, snapshot, verify the
     heap top changed).

## Open questions

1. **LCA representation.**  Cleanest is a `*const NNF` pointer
   (same as `EffectiveCountIndex` uses).  Need to make sure the NNF
   outlives the controller — `solve_dual` already holds the NNF by
   reference for the duration of both threads, so this is fine.
2. **Re-rank cadence.**  On every poll vs every N polls vs only
   when version changes?  Start with "only on version change" and
   measure.
3. **Frontier write granularity.**  Updating on every push/pop is
   probably too fine — B can push/pop hundreds of times per
   millisecond.  Throttle to "every K pushes" or "every X
   microseconds" via a coarser version-bump policy.
4. **Cold start.**  Until B has done a prefix step, the frontier is
   empty.  Strategic should fall back to FIFO (or Greedy ordering)
   for the first few pairs.
5. **Pairs whose LCA is the root.**  Their `e` is just the global
   path count — the same for every such pair.  These degrade to
   FIFO automatically.  Acceptable.
6. **Pairs straddling two Sum branches.**  Their LCA's effective
   count drops to zero on B's first Sum-branch commit (one of the
   two branches has been picked, the other is foreclosed).  Such
   pairs should be deprioritized to `+∞` or dropped from the heap
   entirely on the next re-rank — they cover no live paths.

## Risks

1. **Polling overhead exceeds savings on small inputs.** Likely on
   random-3sat.  Mitigation: profile, then either skip Strategic
   when path count < threshold, or simplify the re-rank to be free
   when version unchanged.
2. **Race on frontier snapshot.**  B writes, A reads.  Worst case:
   A acts on a slightly stale snapshot — pair priorities are
   suboptimal but still correct.  No soundness risk.
3. **LCA correctness for pairs with Sum-sibling endpoints.**  If
   handled wrong, the priority is wrong; soundness is still fine.
   Mitigation: unit test.
4. **Memory: the count map duplicates state.**  ~hundreds of
   nonzero nodes typical; copying on every snapshot is cheap but
   adds allocator pressure.  Mitigation: use a `Vec<(*const NNF,
   f64)>` instead of `HashMap` and reuse the buffer.
5. **Effective layer becomes a hard dependency for Strategic.**
   Strategic only makes sense paired with `EffectivePathController`
   (other B-side controllers don't track per-node counts).
   Document this constraint at the controller's doc-comment level;
   `strategic × cdcl` is not a meaningful combination and shouldn't
   be wired into the bench.

## Recommendation

Worth implementing.  The infrastructure (per-node effective
counts) is already there, the trait shape doesn't need invasive
changes, and the experiment falsifies cleanly: if `strategic×eff`
isn't better than `greedy×eff` on at least BMC and 27-bit
faulty-adder, the idea was wrong and we revert.  If it is, this
becomes the new default A side for structured formulas, and the
matrix-method's "Process A" finally pulls its weight at the
problem's actual frontier rather than its abstract global shape.
