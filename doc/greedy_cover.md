# Greedy cover-search controllers

Process A in the dual-search framework picks complementary pairs from a shared pool to register against a "cover state." The choice of *which* pair to register next is the **greedy heuristic**, and there are at least two distinct meanings of "greedy" worth distinguishing.

## What we ship today: static box-size greedy

`src/dual/cover_greedy.rs` (`GreedyMaxCoverController`).

For each pair `((i, a), (j, b))` it scores

$$\text{box\_size}(X) = \prod_{c \neq i, j} k_c$$

— the number of paths that would be covered if `X` were picked **alone** (the others are free; this pair fixes alts at clauses `i` and `j`). The pair with the largest static box wins.

Pros:
- Each score is independent of every other pick. Compute once at pool-arrival, push into a max-heap, pop in O(log N) per selection.
- Total selection cost over a run: `O(N log N)`.
- No bookkeeping about overlaps.

Cons:
- It's the **wrong objective** when boxes overlap. Two big-box pairs can cover almost the same paths; picking both wastes cover budget.
- The docstring already calls this out:
  > *It's an approximation: the true max-cover-step picks the pair whose box has the largest intersection with the still-uncovered region.*

## The classical alternative: dynamic marginal-gain greedy

Pick the pair with the largest **newly covered** region given the pairs already chosen `C`:

$$X_t = \arg\max_X\; \bigl|\,\text{box}(X) \setminus \textstyle\bigcup_{Y \in C_{t-1}} \text{box}(Y)\,\bigr|$$

Stop when the marginal gain of every pool entry is 0 — equivalently, when the union of chosen boxes covers every path.

This is the textbook greedy for set-cover. Set-cover marginal gain is **submodular** (`f(C ∪ {X}) − f(C)` is non-increasing in `C`), and submodular greedy gives the well-known `1 + ln n` approximation ratio. The static box-size variant has no such guarantee.

### Where they diverge

Three pairs `X, Y, Z` with box sizes `100, 90, 50`. Suppose `X` and `Y` cover almost the same paths and `Z` is disjoint from both.

| pick # | static greedy   | dynamic greedy  |
|--------|-----------------|-----------------|
| 1      | `X` (100)       | `X` (100)       |
| 2      | `Y` (90)        | `Z` (gain 50, since `Y`'s gain dropped to ~10) |
| coverage after 2 | ~110 | 150 |

The dynamic version goes for the *uncovered* region instead of the *largest static box*. On any matrix where pairs overlap meaningfully, the cover it produces is smaller and (more importantly) it can prove UNSAT *earlier* — which matters for our framework because A's `is_complete` returning true is one of our two termination signals.

## Implementation challenge: marginal gain isn't free

Computing `|box(X) \ ⋃_C box(Y)|` exactly each step is the expensive part.

- For two boxes the count is the bivariate path-counter we sketched in the conversation — `O(depth)` per evaluation.
- For multivariate intersection of *k* boxes: same idea, but inclusion-exclusion over subsets of `C` blows up as `2^|C|`.
- For a candidate `X`, the natural formula is
  $$\text{newly}(X \mid C) = |\text{box}(X)| - \bigl|\text{box}(X) \cap \textstyle\bigcup_{Y \in C} \text{box}(Y)\bigr|$$
  and the second term needs symbolic-union machinery to stay cheap.

## Three implementation options

### Option 1 — exact inclusion-exclusion, capped `|C|`

For each candidate `X`:

$$\bigl|\text{box}(X) \cap \bigcup_{Y \in C} \text{box}(Y)\bigr| = \sum_{\emptyset \neq T \subseteq C} (-1)^{|T|+1} \cdot M(\text{root}, X \cup T)$$

where each `M(root, S)` is the multivariate path-count from the design conversation: walk the Steiner subtree of `S`, multiply Sum siblings' path counts, kill the term at the first conflicting Prod. Each `M` is `O(|S| · depth)`; the inclusion-exclusion sum is `O(2^|C|)`.

**Verdict:** fine for `|C| ≤ 20` (≤ 1M I/E terms, fast `M`). Cliffs hard once `|C|` reaches the dozens, which is exactly when the cover is interesting. Skip.

### Option 2 — symbolic union via BDD

Represent the union of chosen boxes as a BDD over `(clause, alt)` boolean variables (one var per `(c, a)` pair, with exactly-one-per-clause constraints). `box(Y)` for a single pair is the trivial conjunction `var[i][a] ∧ var[j][b]`.

Maintain `valid_bdd = exactly_one_per_clause AND ⋂_Y NOT(box(Y))` — the **uncovered** set as a BDD. (This is exactly what `BddBansCoverState` already maintains.) Then for any candidate `X`:

$$\text{newly}(X \mid C) = \bigl|\,\text{valid\_bdd} \wedge \text{box}(X)\,\bigr|$$

evaluated as a `Bdd::and` plus `Bdd::cardinality` — both are routine in `biodivine-lib-bdd`. Each candidate evaluation is `O(\text{|valid\_bdd|} · \text{|box BDD|})`; the box BDD for a pair is two literals so it's tiny.

After each pick we don't need a costly rebuild — `BddBansCoverState::add_pair` already incrementally `and_not`'s the new ban into `valid_bdd`.

**Verdict:** the right baseline. Soundness is automatic, the BDD machinery is already in the codebase, and the per-candidate cost is bounded by the BDD size (which stays small for typical formulas because of the exactly-one structure).

### Option 3 — lazy heap with stale-marker

Standard "lazy greedy" trick (Minoux 1978). By submodularity, every cached gain in the heap is an **upper bound** on the true current gain. So:

```
loop:
    pop (cached_gain, X) from max-heap
    true_gain = recompute(X)   # using whatever exact method
    next_top = heap.peek().cached_gain   # 0 if heap empty
    if true_gain >= next_top:
        return X                # provably the max
    else:
        push (true_gain, X) back into heap
```

This avoids re-evaluating every pool entry every step — only the few "promising" candidates near the top get re-scored. Average-case behaviour is dramatically better than full re-scan.

**Verdict:** strictly an optimization on top of either Option 1 or 2. Plays beautifully with Option 2: pop top, recompute via BDD, push back if dropped. Adopt it together.

## Recommendation

**Option 2 + Option 3 combined.** Concretely:

1. **State**: reuse `BddBansCoverState` (already maintains `valid_bdd`).
2. **Gain query**: add `BddBansCoverState::gain_for_pair(pair) → u128` returning `cardinality(valid_bdd ∧ box(pair))`.
3. **Controller `GreedyDynamicCoverController`**:
   - Same heap structure as the static `GreedyMaxCoverController`, seeded with `box_size` (an upper bound on the very first gain).
   - In `next_pair_index`, lazy-greedy loop: pop, re-eval via `gain_for_pair`, push back if dropped, return when `true_gain >= next_top.cached_gain`.
   - In `register_pair`, sync the BDD via `state.check_complete_with_bdd()` so the next gain query sees the latest.
   - In `is_complete`, return `state.check_complete_with_bdd()`.

Termination: the dynamic version can declare UNSAT itself (BDD becomes `false`), unlike the static greedy which always defers to B's exhaustion.

## What we expected vs what we measured

| benchmark | static `greedy × cdcl` | dynamic `greedy⁺ × cdcl` | other reference |
|---|---|---|---|
| random 3-SAT n=30 (SAT) | 1.33 ms | 2.07 ms (slower) | basic 1.30 ms |
| faulty-add 3-bit (SAT) | 8.94 ms | **6.43 ms** (28 % faster) | basic 7.91 ms, bdd-bans 8.91 ms |
| faulty-add 4-bit (SAT) | 29.4 ms | **26.6 ms** (10 % faster) | basic 23.8 ms, bdd-bans 35.2 ms |
| PHP-10-9 (UNSAT) | 22.2 ms | 196 ms (slower) | bdd-bans 43 ms |

(Final numbers — with the BDD-size fallback active. PHP-10-9 went from `TIMEOUT` to `196 ms`; the fallback short-circuits before the BDD reaches multi-million-node territory.)

The PHP failure mode is intrinsic to the BDD representation, not the dynamic-greedy algorithm. Tracing on PHP-10-9:

```
greedy⁺: registered=50,  BDD nodes=4 451,    sync took   88 µs
greedy⁺: registered=100, BDD nodes=14 798,   sync took  567 µs
greedy⁺: registered=200, BDD nodes=152 826,  sync took  3.6 ms
greedy⁺: registered=300, BDD nodes=1 186 028, sync took  40 ms
greedy⁺: registered=400, BDD nodes=6 310 231, sync took 462 ms
```

Pigeonhole is the textbook BDD-blowup family — adding bans rapidly grows `valid_bdd` from thousands of nodes to millions. Each gain query is O(BDD size), so per-pick cost crosses 100 ms by ~350 picks and the run never terminates.

`bdd-bans × cdcl` on the same matrix finishes in 33 ms because its `BddBansCoverController` uses *static* box-size selection and only triggers a BDD `check_complete_with_bdd` every 1024 pairs — by then B's CDCL has usually exhausted and the framework returns before A's BDD work matters. My dynamic controller, by contrast, is forced to keep `valid_bdd` synchronized after **every** registered pair to make `gain_for_pair` accurate.

### Lessons

- **Lazy greedy works as advertised.** With `reeval_cap = 16`, the bench trace shows ≤ 1 re-eval per pick on PHP — the seeded box-size upper bounds were tight enough that the very first pop wins almost every time. Picking the right pair isn't the bottleneck.
- **BDD `cardinality` is the bottleneck on hard formulas.** Per-pick cost is dominated by the `valid_bdd ∧ box(X)` AND plus a `cardinality()` traversal — both linear in the (worst-case exponential) BDD size.
- **Marginal-gain wins where they happen are modest.** ~10 % on faulty-adder SAT — measurable but not a step change. The static box-size heuristic is already close to optimal on these matrices, so dynamic re-scoring rarely changes the pick order in a way that matters.

### Where to go from here

Direction 1 below is now implemented and shipped (`bdd_size_threshold = 100_000` by default; tunable via `with_bdd_size_threshold`). On BDD-blowup hitting the threshold, `next_pair_index` returns `None` so A goes idle and B drives termination — no more timeouts. Two more productive directions if needed:

1. ~~**Cap the BDD size**~~ — implemented. Once `valid_bdd.size()` crosses 100 000 nodes the controller stops registering further pairs, leaving termination to B. Sound because B's path-search exhaustion is itself an authority for UNSAT.
2. **Switch to symbolic representation that handles PHP** — ZDD or implicit set-cover oracle backed by CaDiCaL `solve_assuming` (count-aware variant). Heavier engineering.
3. **Option 1 hybrid** — exact inclusion-exclusion when `|registered| ≤ K` (say 20), then freeze the cover and stop scoring. PHP's blowup is at hundreds of pairs; if we only score for the first 20 picks the BDD never gets a chance to explode.

## Files added / modified

- **New** `src/dual/cover_greedy_dynamic.rs` — the new controller.
- **Modified** `src/dual/cover_state_bdd.rs` — `gain_for_pair` accessor.
- **Modified** `src/dual/mod.rs` — `pub use GreedyDynamicCoverController`, cross-product test row.
- **Modified** `src/dual/bench.rs` — `run_dual_greedydyn_*` runners + bench rows.

## Future extensions

- **Stochastic submodular maximization** (Mirzasoleiman et al.): subsample candidates per pick; theoretical guarantee of `(1 - 1/e)` in expectation with much less work. Worth trying if BDD evaluation becomes the bottleneck on huge pools.
- **Marginal-gain via projection**: for `valid_bdd` of bounded width, project onto each candidate's two free variables and read off marginal counts directly without computing a fresh AND. Possibly faster than full `cardinality`.
- **Hybrid score**: mix dynamic gain with a tie-breaker that prefers pairs touching previously-uncovered clauses (encourages diverse picks early when many candidates have similar gains).
