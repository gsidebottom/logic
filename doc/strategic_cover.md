# Strategic Cover — Design + Null Result

A demand-driven cover-search controller for the dual framework: A
(cover search) watches B (path search)'s current prefix and the
effective path counts on subtrees B is exploring, and prioritizes
complementary pairs in *small live subtrees* — pairs whose LCA in
the NNF tree has a small `e(lca | P)`.  The bet was: those pairs
are the highest-leverage covers — closing out a small subtree fully
makes the Effective layer's zero-count prune kick in on B's next
visit, which immediately prunes that whole subtree.

**Result: implemented twice (global pre-mining and frontier-driven
mining), benchmarked thoroughly, doesn't help.  Reverted.  This
doc records the design + null result so the next person tempted
by this idea can skip the dead end.**

---

## The idea

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
per-NNF-node effective path counts `e(X | P)` as B descends.  That
information is the answer to "what is B about to do."  It's right
there in shared mutable state on B's thread.  A just doesn't see it.

**Strategic Cover plugs A into that signal** so A's priorities
follow B's actual exploration in real time.

## What was built

### Shared snapshot
`PathFrontier`: an `Arc<{version: AtomicUsize, counts_by_id:
Mutex<Vec<f64>>}>` written by `EffectiveCountWrapper::sync_to_prefix`
on B's thread and read by `StrategicCoverController::next_pair_index`
on A's thread.

Counts are keyed by `EffectiveCountIndex` node ID — assigned in
preorder during a pre-walk of the NNF.  Because preorder is a
structural property of the tree, two indices built on two separate
clones of the same NNF agree on every node's ID; A and B can use
their own NNF clones and still share the count keyspace.

`EffectiveCountIndex` got `unsafe impl Send + Sync` (the `*const
NNF` pointers reference NNFs owned by `Box<NNF>` fields on the
controllers — stable heap addresses across thread moves).

### Scoring
`pair_score(p1, p2) = e(lca(p1, p2) | P)`.  Pairs with smaller
LCA-subtree counts go first.  Pairs whose LCA is a Sum (= path
picks one branch, pair covers zero paths) get `u64::MAX` and sink
to the heap bottom.  Cold start (no published counts yet) → FIFO.

### Two mining strategies tried

**Variant 1: Global pre-mining.**  At `seed_pool`, enumerate all
complementary pairs in the NNF — including non-flat NNFs (added a
`mine_pairs_general` helper that walks the tree, groups leaves by
variable, cross-products positive/negative within each variable,
filters by LCA-is-Prod).  Pool starts with hundreds-to-thousands
of pairs; A re-ranks lazily as B publishes new counts.

**Variant 2: Frontier-driven mining.**  At `seed_pool`, do only the
cheap flat miner (returns empty on non-flat NNFs, same as Greedy).
Inside `next_pair_index`, on every observed frontier version bump,
walk the count snapshot and mine pairs *within* each subtree whose
`e(X|P)` is in `(0, MINE_THRESHOLD]` and that hasn't been mined
before.  Each subtree is mined at most once.  Internal subtrees
only (Lit-leaves skipped — single-literal subtrees can't form pairs).

## Bench results (focused 27-bit suite, with Phase 1+3+4 preprocessing)

All times in ms; matrix-method columns include pp + search totals.

| Variant | random-3sat | 27/1 UNSAT | 27/2 SAT | BMC count-zeros |
|---------|-------------|------------|----------|-----------------|
| greedy×eff (baseline) | 1.76 | 9.87 | 20.47 | **5.76** |
| strat×eff Variant 1 (global pre-mining) | 2.12 | 10.21 | 21.99 | **10.24** (–78%) |
| strat×eff (B-emissions-only, no mining) | 2.06 | 10.18 | 20.78 | 5.73 |
| strat×eff Variant 2 (frontier mining, T=64) | 1.81 | 10.23 | 20.78 | 7.88 (–37%) |
| strat×eff Variant 2 (frontier mining, T=8, skip leaves) | 1.82 | 10.18 | 20.71 | **7.15** (–24%) |

No variant wins on any row.

## Diagnostic — why it doesn't work

Instrumentation (`STRATEGIC_INSTR=1`) printed `registered`,
`mined_subtrees`, `mined_pairs` per run.  Pattern:

| Row | Mined subtrees | Mined pairs | Search verdict |
|-----|----------------|-------------|----------------|
| random-3sat | 0 | 0 | SAT (fast) |
| 27/1 UNSAT | 0 | 0 | UNSAT (fast) |
| 27/2 SAT | 0 | 0 | SAT (fast) |
| BMC | 1097 | 1124 | UNSAT (slower than greedy) |

**Three of four rows: zero mining activity.**  The search terminates
before A's frontier-driven mining triggers — B finds an uncovered
path or exhausts the matrix in 1-20 ms while A's mining loop is
still waiting for B's first published frontier snapshot.  Strategic
on those rows degenerates to "Greedy plus extra setup cost" — the
1-3% overhead is purely from the extra `Box<NNF>` clone, the index
build, and the publishing-side mutex traffic on B.

**BMC, where mining does fire, still loses.**  Strategic mines 1097
internal subtrees and registers 1124 pairs, all of which get added
to `BasicCoverState`'s bucket index — making `is_prefix_covered`
queries on B's side more expensive.  Whatever pruning value these
pre-mined pairs provide is outweighed by:

1. A's mining cost (walking ~1000 subtrees, grouping leaves by var,
   cross-products, LCA-Sum checks)
2. B's increased cover-state query cost (more pairs to scan)
3. The extra `register_pair` calls into `BasicCoverState::add_pair`

## The structural reason

The "pair in a small live subtree closes the subtree" intuition
fits flat CNF-like shapes better than circuit-encoded shapes:

- **Flat Sum-of-Prods** (random-3sat post-preprocessing): every
  complementary pair has its LCA at the *root Sum*.  No
  small-subtree structure for Strategic to discriminate on.  Score
  is uniform across pairs.  Strategic degenerates to FIFO; Greedy's
  box-size scoring is strictly more informative.

- **Circuit-encoded NNFs** (faulty-adder, BMC): each variable
  typically appears with one polarity in any given subtree of the
  circuit.  Mining *within* a subtree finds zero complementary
  pairs locally (or only pairs whose LCA is the subtree's root —
  same as mining the parent).  The pairs that actually block paths
  **span subtrees** — one literal in subtree X, the complement in a
  sibling subtree Y, with LCA at a Prod ancestor of both.
  Mining-within-X never finds these.

So the score function `e(lca | P)` is degenerate on flat formulas
(uniform across pairs) and the mining-within-subtree strategy is
structurally blind on non-flat formulas (the pairs aren't where
we're looking).

## What it would take to actually work

Three orthogonal angles, each with substantial complexity:

1. **Cross-subtree mining.**  For each frontier subtree X with
   small `e(X | P)`, enumerate pairs (l1, l2) where l1 is in X and
   l2 is in any *sibling* subtree under a Prod ancestor of X.  This
   finds the spanning pairs.  But the search space explodes — every
   leaf in X × every leaf in every sibling — so it'd need much
   tighter selection (e.g. only mine variables that appear in X with
   one polarity, restrict the sibling search to leaves of that var
   with opposite polarity).  Doable but ~10× more code than what
   was attempted here, and the win is still speculative.

2. **A different score.**  `e(lca | P)` is degenerate on flat
   formulas.  An alternative: score by "fraction of B's currently
   live paths this pair blocks", roughly `pair_box_size × (e(lca|P)
   / e(lca|∅))`.  This is Greedy's box-size scaled by liveness — a
   per-prefix-adjusted box size.  Would degenerate gracefully to
   Greedy on flat formulas (where liveness ratios are uniform
   across pairs) and would differentiate on nested ones.  Worth
   trying but only after #1 to avoid the structural blindness.

3. **Lock-free publishing.**  Replace `Mutex<Vec<f64>>` with
   `Vec<AtomicU64>` (each `f64` stored as bits).  B's publishing
   becomes free; A's reads become lock-free.  Removes the
   ~1-3% baseline overhead seen on the no-mining rows.  Useful
   independent of whether the selection logic ever pays off.

## What was removed

Variant 2 was the cleanest implementation and the closest match to
the user's original "pairs in low path count matrices on extensions
of the search prefix" phrasing.  When it still didn't win, we
reverted the whole experiment rather than keep dead code in the
dual module.  All of the following came out:

- `src/dual/cover_strategic.rs` (deleted)
- `src/dual/path_frontier.rs` (deleted)
- Modifications to `src/dual/effective_count.rs` (position-of-id
  tracking, leaf_lit inverted view, subtree-leaves walker,
  `unsafe impl Send + Sync`)
- Modifications to `src/dual/path_effective.rs`
  (`with_frontier_publisher` constructor, `EffectiveCountWrapper`
  frontier field, throttled publishing in `sync_to_prefix`)
- Additions to `src/dual/flat.rs` (`mine_pairs_general` for
  non-flat NNFs)
- `strat×eff` bench column in `src/dual/bench.rs`

Restored cleanly via `git restore` + `rm`; build green, 237/237
tests pass.

## What survives

- This doc, as a record so the dead end doesn't get rediscovered.
- The lessons:
  - Demand-driven A is conceptually right but the leverage point
    is wrong for circuit-encoded formulas where blocking pairs
    span subtrees, not cluster within them.
  - "Add another knob to A" is a tempting move that this codebase
    has resisted for a reason — the existing controllers (`Greedy`,
    `GreedyDynamic`, `Effective` B-side) are already in a fairly
    optimal spot for this benchmark; pushing further means a
    different problem class or a different score function entirely.
