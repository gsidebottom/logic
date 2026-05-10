# Dual-Process Matrix Search — Design

A design for a matrix-method validity/satisfiability solver structured as
two cooperating search processes.  This is a **design document** — no
implementation yet.

## Why two processes

The current matrix-method search (`for_each_path_prefix_*` driven by a
`PathSearchController`) does two jobs at once:

1. **Path enumeration** — walking the NNF tree, picking Prod
   alternatives, visiting Sum children.
2. **Cover detection** — at each path completion (or earlier prefix),
   checking whether some complementary pair lies on the current path,
   and using that pair to prune.

These are jobs of fundamentally different shape: enumeration is an
exploration over a discrete combinatorial space; cover detection is a
greedy set-cover problem (each pair "covers" a region of path space).
A single DFS controller has to interleave the two, which is why the
current implementations (`BacktrackWhenCovered`, `Smart`, `Cdcl`)
all bundle cover-aware bookkeeping with their traversal logic.

The proposal is to split them into two specialised processes that
exchange information:

* **Process A — Cover search.**  Maintains the pool of known pairs
  and an evolving notion of "what's covered so far".  Picks a next
  pair to *apply* (i.e. to register its cover region against the
  shared state) using whatever heuristic — "greedy max-cover", "pair
  with most-recent activity", "pair learned from a conflict".
* **Process B — Uncovered-path search.**  Walks the NNF looking for
  a path that isn't covered.  As it goes it discovers new pairs
  (every time it closes a prefix, it has identified the pair that
  did so) and feeds them to A.  A's accumulated cover state lets B
  prune entire subtrees without re-deriving the pairs that closed
  them.

Termination:

* A reports "every path covered" → **UNSAT** (when searching the
  complement, this means the original formula is unsatisfiable; in
  the validity-mode dual it means the formula is valid).
* B reports "found an uncovered path" → **SAT** (or, in the dual,
  "found a falsifying assignment" → **not valid**).

The two processes can run concurrently, on different threads or on
the same thread interleaved.  The framework should be agnostic to
that scheduling decision so we can experiment.

## Set-cover view (the math)

For SAT search the NNF is the formula's complement (a Sum-of-Prod-of-
Lits when the formula is CNF).  Index the Prod nodes 0..n−1.  A path
through the matrix is a tuple `(a_0, ..., a_{n−1})` where `a_i` is
the alternative chosen from Prod `i`.  The path's literal-set is
fixed by the tuple: `{ lit(i, a_i) : 0 ≤ i < n }`.

A complementary pair `((i, a, p1), (j, b, p2))` means: `lit(i, a) =
L`, `lit(j, b) = ¬L`.  The pair "covers" exactly the set of paths
where `a_i = a ∧ a_j = b`.  This is a 2-dimensional axis-aligned box
in the product space.

Reformulating:

* Every uncovered path = a point in the product space avoiding every
  pair-box = a solution to the boolean CNF "for every pair-box,
  *not* in that box".  Each pair contributes a 2-clause "x_i ≠ a ∨
  x_j ≠ b".
* The formula is UNSAT iff the union of pair-boxes covers the whole
  product space.

The two-process search is then:

* A is solving a **greedy set-cover** problem: pick pairs so that
  their boxes cover everything.
* B is solving the **dual** SAT problem: find a point not in any box
  — exactly the "uncovered path" question.

Both processes operate on the same shared **cover state**.  A grows it
(adds boxes); B queries it (asks "is this prefix in any box?") and
contributes (every closed prefix yields a new pair).

For non-flat NNFs the structure is richer (a path is not a flat
tuple) but the same set-cover framing applies — boxes become more
complex regions of path space.

## The framework

### Shared substrate

```rust
/// Append-only log of pairs known to the search.  Both A (the cover
/// process) and B (the path process) write into this — A from
/// learned-clause derivation, B from the prefix it just closed.
struct PairPool {
    pairs: RwLock<Vec<Pair>>,
    new_pair_tx: broadcast::Sender<usize>,   // index into pairs
}

/// Cover state — A's accumulated knowledge of which paths are
/// covered.  Concrete representation is controller-dependent: it
/// could be a list of (pair, prefix) records (today's
/// `CoveredPathPrefix` log), a BDD, a coverage bitmap, or a
/// CNF-with-2-clauses representation.  Both processes need a
/// query interface.
trait CoverState: Send + Sync {
    /// Is the path with this Prod-choice prefix already covered by
    /// some pair we've registered?
    fn is_prefix_covered(&self, prefix: &ProdPath) -> bool;

    /// Statistical summary for the cover-search controller.
    /// Cardinality of "uncovered paths so far" if computable;
    /// `None` if the representation can't answer cheaply.
    fn uncovered_estimate(&self) -> Option<f64>;
}
```

### Cover-search controller (process A)

```rust
trait CoverSearchController: Send {
    type State: CoverState;

    /// Pick the next pair to *register* against the cover state.
    /// Return `None` to yield (e.g. waiting for B to feed in
    /// more pairs).
    fn next_pair(&mut self, pool: &PairPool, state: &Self::State) -> Option<usize>;

    /// Register pair `i` from the pool against the cover state,
    /// growing the state.  Returns whether this pair contributed
    /// any newly-covered paths (some pairs are redundant).
    fn register_pair(&mut self, pair_idx: usize, pool: &PairPool, state: &mut Self::State) -> bool;

    /// Check whether the cover is complete (UNSAT signal).  May be
    /// expensive — controllers can short-circuit by returning
    /// `false` until a heuristic threshold says "now check".
    fn is_complete(&self, state: &Self::State) -> bool;

    /// Hand-off when B reports a new pair.  Lets the controller
    /// update its priorities (e.g. promote pairs whose vars are
    /// recently-active).
    fn on_pair_added(&mut self, pair_idx: usize, pool: &PairPool) {}

    /// Hand-off when B reports it found an uncovered path — search
    /// is over, the controller can drop bookkeeping.
    fn on_path_found(&mut self) {}
}
```

### Path-search controller (process B)

The existing [`PathSearchController`] trait is a starting point.  In
the dual framework it gains hooks to read A's cover state and to emit
discovered pairs:

```rust
trait DualPathSearchController: Send {
    type CoverStateView: CoverState;

    /// Existing: backtrack/continue decisions.
    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        prefix_prod_path: &ProdPath,
        is_complete: bool,
    ) -> Option<usize>;

    /// New: query A's cover state.  When this returns `true` for the
    /// current prefix, the controller can short-circuit without
    /// having to find the pair itself.
    fn external_cover(&self, prod_path: &ProdPath, state: &Self::CoverStateView) -> bool {
        state.is_prefix_covered(prod_path)
    }

    /// New: emit a pair when one is closed on the current prefix.
    /// The driver wires this into `PairPool` so A sees it.
    fn on_pair_closed(&mut self, pair: Pair, pool: &PairPool);

    /// Existing: ordering hooks.
    fn sum_ord<'a>(&mut self, _children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> { None }
    fn prod_ord<'a>(&mut self, _children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> { None }
}
```

### Driver

```rust
fn solve_dual<A, B>(
    nnf: &NNF,
    cover_ctrl: A,
    path_ctrl:  B,
    params: PathParams,
) -> Outcome
where
    A: CoverSearchController,
    B: DualPathSearchController<CoverStateView = A::State>,
{
    let pool = Arc::new(PairPool::new());
    let state = Arc::new(<A::State>::new(nnf, &params));
    let (term_tx, term_rx) = oneshot::channel();

    // Process A: loop picking pairs and registering them.
    let task_a = spawn({
        let pool  = pool.clone();
        let state = state.clone();
        let term_tx = term_tx.clone();
        async move {
            while let Some(idx) = cover_ctrl.next_pair(&pool, &state) {
                cover_ctrl.register_pair(idx, &pool, &mut state.write());
                if cover_ctrl.is_complete(&state) {
                    let _ = term_tx.send(Outcome::Unsat);
                    return;
                }
            }
        }
    });

    // Process B: traverse paths, query A's state, emit new pairs.
    let task_b = spawn({
        let pool  = pool.clone();
        let state = state.clone();
        let term_tx = term_tx.clone();
        async move {
            let r = drive_path_search(nnf, path_ctrl, pool, state);
            match r {
                PathOutcome::Uncovered(pp) => { let _ = term_tx.send(Outcome::Sat(pp)); }
                PathOutcome::Exhausted     => { /* A is the authority for UNSAT */ }
            }
        }
    });

    // Driver awaits whichever finishes first; cancels the other.
    let outcome = block_on(term_rx);
    task_a.cancel();
    task_b.cancel();
    outcome
}
```

The driver is intentionally thin.  Whether tasks run on threads, on
an async runtime, or interleave on a single thread is an
implementation detail that doesn't change the contract.

## How existing controllers fit

The existing controllers map naturally onto B (the path-search side).
For A there's no existing analogue — that's the new work.

### B-side (path-search) controllers

* **`BacktrackWhenCoveredController` → `BasicDualPathController`.**
  Today it scans the prefix on each call to detect a complementary
  pair.  In the dual framework it does the same scan, *plus* checks
  A's cover state first.  When it finds a pair, it emits via
  `on_pair_closed`.
* **`SmartController` → `SmartDualPathController`.**  Same as above,
  with cross-clause unit propagation.  The propagation watch lists
  are kept B-local.
* **`CdclController` → `CdclDualPathController`.**  Same as above,
  with 1UIP analysis.  Each learned clause is a pair (or a
  generalized k-pair if the learned clause has more than 2 lits —
  see open question below).  Learned clauses get emitted as pairs.

### A-side (cover-search) controllers

These are new.  Three obvious candidates:

* **`BasicCoverController`** — process pairs in arrival order, no
  prioritisation.  A baseline.
* **`GreedyMaxCoverController`** — at each step, pick the
  unprocessed pair whose cover region intersects the most still-
  uncovered paths.  Requires the cover state to support `count
  intersection size for box`.  A natural fit when the path space
  is a flat product (CNF complement), where each pair-box's size
  is `Π_{k ≠ i, j} arity_k` and intersections with already-
  processed pairs can be inclusion-excluded.
* **`LearnedActivityController`** — track which pairs led to fast
  cover growth in the recent past, bias future picks toward
  variables in those pairs.  CDCL's VSIDS, applied to A.

### Cross-product

Any A controller × any B controller works — they communicate only
via the `PairPool` and `CoverState`, neither of which depends on
which controllers produced them.  This is what makes the framework
*plug-in*: experimentation is `for a in [Basic, Greedy, Learned]:
for b in [Basic, Smart, Cdcl]: run(a, b)`.

## Effective-path-count path search

A B-side strategy that addresses the "matrix walks through
irrelevant subtrees" pathology observed on circuit-shaped formulas
where unit-pinning constraints force a unique model.  Concrete
example: `plus(a;b;c;w) ∧ a=max ∧ b=max ∧ c=2·max` has a single SAT
model, CaDiCaL solves it via gate-propagation in ~0.3 ms regardless
of `w`, but the existing matrix.cdcl runtime grows ~5× per added bit
(0.6 ms at w=4, 2.5 ms at w=5, 14 ms at w=6, …) because the DFS
re-derives the pinning via blind alt-selection in every nested
XOR sub-tree.

### The idea

Annotate every NNF node with an **effective path count** — the
number of distinct *potentially-satisfying assignments* its
subtree can still contribute given the literals on the current
path prefix.  The DFS then orders Sum traversal and Prod selection
by *increasing* effective count: smallest first.

The order is **not pre-determined** at search start — counts get
updated as literals join (or leave) the path prefix, so the
ordering at any depth reflects the *current* prefix's constraints.
This is the core difference from `sum_ord` / `prod_ord` returning
a fixed permutation: here the ordering at one depth depends on
what was committed at shallower depths.

### The recurrence

For a path prefix `P` (a set of literals committed so far), the
effective count `e(N | P)` of a node `N` is:

| Node                         | Definition                          |
|------------------------------|-------------------------------------|
| `Lit(ℓ)` where `ℓ ∈ P`       | `1` (already satisfied; contributes no new constraint) |
| `Lit(ℓ)` where `¬ℓ ∈ P`      | `0` (closed; subtree can't extend the prefix) |
| `Lit(ℓ)` otherwise           | `1` (a fresh literal commitment is one option) |
| `Sum(c₁ … c_n)` (visit-all)  | `∏ᵢ e(cᵢ \| P)` (every child must be live) |
| `Prod(c₁ … c_n)` (pick-one)  | `∑ᵢ e(cᵢ \| P)` (we'll pick one alt) |

Three observations worth calling out:

1. **`Lit(ℓ)` for `ℓ ∈ P` returns 1, not 0.**  A `Lit` node where
   the literal is already on the prefix is "trivially satisfied" —
   re-committing to it via the matrix DFS adds nothing new but
   doesn't fail either.  Distinct from "I have to add a *new*
   literal here", which is also count 1; the difference is the
   re-commitment doesn't enlarge the assignment.
2. **A Sum's count goes to 0 if any child is 0.**  Sum is
   visit-all; if any descendant cannot be satisfied under the
   current prefix, the entire Sum fails.  This is the early-prune
   signal.
3. **Prod's count is the sum of viable alts.**  A Prod with an
   alt of count 0 just removes that alt from consideration; the
   Prod stays alive as long as some alt is non-zero, and collapses
   to a forced choice when exactly one alt survives.

### Worked example — `plus(a;b;c;3) ∧ a=3 ∧ b=3 ∧ c=6`

The complement of this formula has a top-level `Sum` whose
children include:

* **9 single-literal Sum-children**: the negations of each pinning
  literal — `a₂, a₁', a₀', b₂, b₁', b₀', c₂', c₁', c₀`.  Each has
  effective count `1`.
* **4 multi-alt sub-trees** from the negated bit-equality and
  no-overflow constraints, each with effective count > 1
  initially (often 3 or more).

**Smallest-first** picks the 9 single-literal children first —
committing them to the path prefix until the prefix is
`{a₂, a₁', a₀', b₂, b₁', b₀', c₂', c₁', c₀}`.

Now the four big sub-trees are *re-evaluated* against this
prefix.  Take the Prod node `(a₁ · b₁ · (a₂+b₂))` (one inner
node of one sub-tree):

* alt `a₁` is a `Lit(a₁)`; `a₁'` is on the prefix → count `0`.
* alt `b₁` is a `Lit(b₁)`; `b₁'` is on the prefix → count `0`.
* alt `(a₂+b₂)` is a `Sum(Lit(a₂), Lit(b₂))`.  Both `a₂` and `b₂`
  are *positively* on the prefix → both children count `1` →
  Sum's count is `1 × 1 = 1`.
* Prod count = `0 + 0 + 1 = 1`.  The Prod is alive but constrained
  to its single viable alt.

Propagating up: any sub-tree containing a `Lit` whose complement
is on the prefix gets its count zeroed out.  In the visualised
case the entire sub-tree containing `b₂', a₁, b₁` (all of which
are complementary with the prefix) collapses to count `0`,
and the DFS prunes it without descending.

**The key efficiency**: the matrix DFS *never visits* the alt
`a₁` once we know it's complementary with `a₁'`; the count update
detected this *while we were committing the pinning literals*.
CDCL's unit-propagation gives the same effect via watched
literals on the Tseitin CNF — the effective-count strategy gives
matrix-DFS the structural-NNF analog.

### Incremental maintenance

Naively recomputing every node's count after each push/pop is
`O(|NNF|)` per step.  The tractable approach:

1. **Pre-compute, per variable, the list of NNF nodes whose
   subtree contains that variable**: `var_to_nodes[v] = Vec<NodeId>`.
   One linear walk at construction time.
2. **When literal `ℓ` is pushed**, only nodes in
   `var_to_nodes[var(ℓ)]` need recomputation.  Walk those nodes
   bottom-up; cascade to ancestors only when a count actually
   changes.  For circuits like `plus(a;b;c;w)` each variable
   occurs in `O(w)` places, so the per-step update is `O(w)`.
3. **On pop**, restore previous counts.  Either by recomputing
   again, or by stashing the prior counts on a stack as part of
   the push frame.

This is comparable to CDCL's watched-literal cost — linear in the
local fan-out of the popped variable, not the whole NNF.

#### Incremental delta updates per ancestor (the critical win)

Step 2 above ("walk bottom-up, cascade") leaves a tempting
inefficiency on the table.  When a child's count changes from
`x` to `y`, the parent's new count is computable from its old
count *without re-iterating every other child* — and that's
where the implementation actually pays off:

* **Sum (= product of children)**: `parent_new = parent_old / x · y`.
  - `y == 0` short-circuits to `parent_new = 0`.
  - `x == 0` is the awkward case (the parent's product was already
    0 because *this* child was 0; some sibling might still be 0
    too).  Fall back to the full `compute()` for that one ancestor.
    Rare in practice — only fires when a sibling was already zero.
* **Prod (= sum of children)**: `parent_new = parent_old + (y − x)`.
  No edge cases.

This makes each propagation step **O(1)** instead of O(arity).
Multiple affected leaves can share ancestors; their delta walks
compose correctly because each step uses the ancestor's *current*
value (already reflecting earlier leaves' updates), and the
chain stops early at any ancestor whose count doesn't change.

For BMC's wide Sum/Prod nodes (XOR encodings have 4-way Sums,
the `neq` disjunction has 3-way, the conjunction at the root has
hundreds of children), this is the difference between "count
maintenance is the bottleneck" and "count maintenance is free."

#### Measured impact

Before incremental delta updates, the `EffectivePathController`
recomputed each dirty ancestor with the full `compute()` —
iterating every child of the ancestor, multiplying or summing.
After the switch (single function: `EffectiveCounts::push` in
`src/dual/effective_count.rs`):

| benchmark / config             | full `compute()` | incremental delta | speedup |
|--------------------------------|------------------|-------------------|---------|
| random-3sat n=30 (SAT)         | 1.42 ms          | 1.71 ms           | within noise |
| faulty-add 16-bit / 1f UNSAT   | 16.46 ms         | **7.60 ms**       | **2.2×** |
| faulty-add 16-bit / 2f SAT     | 1882 ms          | **857 ms**        | **2.2×** |
| BMC count-zeros n=8 w=16 UNSAT | **TIMEOUT (>60 s)** | **3.74 ms**    | **>16 000×** |

(All numbers are `dual greedy × eff` from
`bench_focused_top_config`; numbers around the same as before for
the small / random rows where count-maintenance overhead wasn't
the bottleneck anyway.)

The BMC line is the headline result: it went from "the
controller's worst case — never finishes" to "the fastest cell on
that row," beating CaDiCaL (3.93 ms) and `matrix.cdcl` (5.96 ms).
The 2-fault SAT case at 857 ms is now 4.6× faster than
`greedy × cdcl` (3931 ms) and 8× faster than `matrix.cdcl`
(7060 ms).

Why BMC dramatizes this: BMC's NNF is built from bit-vector
arithmetic with thousands of leaves, deep nesting, and wide
Sum/Prod nodes.  The pre-incremental algorithm spent its time
re-multiplying children of dirty Sum nodes — each ancestor visit
was O(arity), and most of the children's counts hadn't changed.
Once each ancestor visit became O(1), the count layer's
overhead drops out of the critical path entirely; the controller
gets to use its narrowing intelligence (effective-count = 0 ⇒
prune) on a per-step cost competitive with raw CDCL propagation.

### Trait changes — wrapper approach

The current `DualPathSearchController` is a thin run-it harness;
its B-side controllers compose an inner cover-aware
`PathSearchController` with a `StateQueryWrapper` (Phase 2/3).
The cleanest place to add effective-count search is **as another
wrapper on the inner stack**, not by extending
`DualPathSearchController` itself:

```rust
// src/dual/path_effective_count.rs (new)
pub struct EffectivePathController<S: CoverState = BasicCoverState> {
    _state: PhantomData<S>,
}

impl<S: CoverState + 'static> DualPathSearchController for EffectivePathController<S> {
    type State = S;

    fn run(self, nnf: &NNF, mode: SearchMode, …) -> PathOutcome {
        // 1. Pre-walk: build var → [node_id] index.
        let counts = EffectiveCountIndex::build(nnf);

        // 2. Construct inner cover-aware controller (cover-mode
        //    so pairs are emitted into the pool as before).
        let inner = SmartController::for_nnf_with_cover(…);

        // 3. Wrap with the count-maintaining adapter, which
        //    wraps `inner` and intercepts sum_ord / prod_ord
        //    plus updates counts on every push/pop in
        //    should_continue_on_prefix.
        let counted = EffectiveCountWrapper::new(inner, counts);

        // 4. Wrap with the cover-state query layer (Phase 2).
        let composite = StateQueryWrapper::new(counted, state, cancel);

        // 5. Drive with restart loop.
        run_dfs_with_restarts(&mut composite, nnf, &uncovered)
    }
}
```

The `EffectiveCountWrapper` is itself a `PathSearchController`:

```rust
struct EffectiveCountWrapper<Inner: PathSearchController> {
    inner: Inner,
    counts: EffectiveCountIndex,
    /// Per-push-frame snapshot of count deltas, for undo on pop.
    frames: Vec<CountDeltaFrame>,
}

impl<Inner: PathSearchController> PathSearchController for EffectiveCountWrapper<Inner> {
    fn should_continue_on_prefix(&mut self, lits, …) -> Option<usize> {
        // Sync frames against `lits` len: pop frames for popped
        // lits, restoring counts; push frames for new lits,
        // updating counts.  Each new push that drives the active
        // subtree's count to 0 returns `Some(0)` for early prune.
        …
        self.inner.should_continue_on_prefix(lits, …)
    }

    fn sum_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        // Sort children by ascending current effective count;
        // exclude zero-count children entirely (they'd zero the
        // Sum, which is detected at should_continue_on_prefix).
        // For the Sum-visit-all case, ordering doesn't change
        // *which* children are visited, just the order — this
        // gets the most-constrained subtree visited first so
        // failures surface early.
        Some(sorted_non_zero(children, &self.counts))
    }

    fn prod_ord<'a>(&mut self, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        // Sort by ascending count, exclude zero-count alts —
        // a zero-count alt is provably blocked, equivalent to
        // CDCL's "blocked by complement on trail".  When only
        // one alt remains, the DFS commits to it forced-choice.
        Some(sorted_non_zero(children, &self.counts))
    }
}
```

The trait `DualPathSearchController` itself **doesn't need to
change** — the strategy lives entirely inside the wrapper, which
plugs into the existing `PathSearchController` slot (the same
trait `BacktrackWhenCovered`, `Smart`, `Cdcl` all implement).
That's the same composition pattern Phase 2/3 already established
with `StateQueryWrapper` — effective counting is just a second
wrapper layer.

The cross-product expands cleanly:

```
{Basic, Greedy, CnfBans, BddBans}      A controllers
×
{Basic, Smart, Cdcl}                   B inner controllers
×
{plain, EffectiveCount}                wrapper option
```

= 24 compositions, all cross-checkable against the existing
`dual_cross_product_agrees_on_assorted_formulas` test.

### Why this hasn't been the natural strategy

The matrix-DFS literature treats "Sum visits all, Prod picks one"
as a fixed traversal protocol.  This proposal **adds a counting
layer** that re-orders both Sum traversal and Prod selection
based on dynamic constraints — essentially making the path-search
look more like CDCL's decision-heuristic-driven search, but
operating on the structural NNF rather than a flat CNF.

The closest analog in CDCL: when the variable being pinned has
only one non-blocked alt remaining in some clause, CDCL forces
it via unit propagation.  The effective-count strategy
generalises that to the NNF: when an inner Prod's alt counts
collapse to one non-zero alt, the DFS commits to it as a forced
choice; when a sub-tree's count drops to zero, the DFS skips it
entirely.

### Expected impact

Cases where this should pay off:

* `plus(a;b;c;w) ∧ pinning` benchmark series (the cleanest
  illustrator).  Predicted: matrix.cdcl + EffectiveCount runtime
  flat as `w` grows, vs the current ~5× per bit.
* Faulty-adder with tight expected-output and fault-count
  pinning — same shape, larger scale.
* Any circuit-encoded formula where pinning input bits should
  propagate through gate equalities to fix output bits.

Cases where it won't help meaningfully:

* PHP family — already flat Sum-of-Prods; the matrix-CDCL stack's
  watched-literal cross-clause propagation already does the
  equivalent work.  Effective counts mostly mirror what
  propagation provides.
* Faulty-adder UNSAT cases where the bottleneck is exhausting a
  structurally-rich NNF — effective counts don't shrink the
  search space, just reorder it.
* Cases where the matrix DFS already finds an uncovered path
  quickly (random-3sat at the easy ratio, small SAT formulas).

The strategy's home is **circuit-like formulas with tight pinning
constraints**, where the unique satisfying assignment can be
derived from the pinning by structural propagation through XOR
and AND gates.

### Implementation plan

1. **Phase 1**: `EffectiveCountIndex` — build the
   `var → [NodeId]` index plus the per-node effective-count
   storage.  Static recurrence: given a prefix, compute every
   count from leaves up.  Validate by enumerating small NNFs
   manually.
2. **Phase 2**: `EffectiveCountWrapper` PathSearchController.
   Maintains counts incrementally on push/pop via per-frame
   delta lists.  Implements `sum_ord` / `prod_ord` to filter
   zero-count children and order ascending.
   Returns `Some(0)` from `should_continue_on_prefix` when the
   active subtree's count is 0.
   Validate: every dual `cross_product` test still passes.
3. **Phase 3**: `EffectivePathController` DualPathSearchController
   — composes inner cover-aware controller with the count
   wrapper and the existing `StateQueryWrapper`.  Bench the
   `plus`-with-pinning sweep at `w ∈ {3, 4, 5, 6, 8, 12}`,
   compare against `matrix.cdcl`.
4. **Phase 4**: extend the bench harness with a 4th column
   (`{plain, EffectiveCount}`) and re-run all faulty-adder
   variants and PHP cases.  Document where it helps and where
   it doesn't.

Estimated effort: ~600 LoC for Phase 1-2 + tests, another ~200
for Phase 3 wiring, ~100 for bench integration.

## Termination and soundness

### Soundness

* A reports UNSAT only when its cover state contains every path.
  Each pair-registration must preserve the invariant: a path is in
  the cover state iff some registered pair's region contains it.
* B reports SAT with an uncovered path.  The path's literal-set is
  consistent (no pair on it, by definition) — so it's a valid
  partial assignment, extendable to a model.

### Completeness

* For every path either (a) some pair lies on it (closed), or (b)
  it's uncovered (a model).
* Every closed path's pair eventually enters `PairPool` — either
  because B traversed it and emitted, or because A processed it
  before B got there (A can derive pairs from the matrix
  statically).
* A's cover state grows monotonically.  If the formula is UNSAT,
  the cover eventually completes; A signals.
* If the formula is SAT, B is guaranteed to traverse the
  uncovered path eventually (provided B's traversal is fair).

### Race conditions

Both processes signal termination via an `oneshot` channel; the
driver takes the first signal.  An A-UNSAT and a B-SAT signal
*shouldn't* both be possible — that would mean the cover state
contained a path that B has just walked uncovered, which violates
A's soundness invariant.  In implementation we should debug-assert
this never happens.

## Open design questions

1. **Cover-state representation.**  The right data structure is the
   biggest open question.
   - **`Vec<CoveredPathPrefix>`** (today's representation) is
     append-only and simple, but `is_prefix_covered` is O(|state|).
   - **Coverage bitmap** is O(1) query but exponential memory in the
     number of clauses.
   - **BDD / ZDD over the Prod-choice variables** is a sweet spot —
     compact, supports both query and "uncovered count" cheaply, but
     adds a substantial dependency.
   - **CNF representation of bans** ("the uncovered set as a CNF
     where each pair contributes one 2-clause") puts us back in
     standard CDCL territory — at which point we might just feed it
     to CaDiCaL.  That's not absurd: it would be an interesting
     experiment to compare matrix-CDCL vs. CaDiCaL-on-the-bans.

2. **Pair generalisation.**  Today a "pair" is two complementary
   lit positions.  CDCL's learned clauses can have arbitrary arity
   (k lits).  Should the framework generalise to "k-tuples whose
   joint occurrence on a path is impossible"?  That would let CDCL
   contribute its full learned-clause inventory to A.  Concretely:
   `Pair = (Position, Position)` becomes `Constraint =
   Vec<Position>` and a constraint's box is the intersection of
   per-coordinate conditions.

3. **A's pair source.**  Where does A get its pairs?
   - From B's emitting (already discussed).
   - From static analysis of the matrix at startup — every two
     lits that are negations of each other and lie on some
     common path are candidate pairs.  Pre-populating the pool
     gives A something to chew on while B starts up.
   - From a third process that does pair-mining unrelated to
     either A or B.

4. **Communication granularity.**  How often does A push cover-state
   updates to B?  Always-visible via shared `Arc<RwLock<…>>` is
   simplest but has lock contention.  Periodic snapshot (B reads a
   stale view between snapshots) is faster but needs careful design
   so B doesn't miss prunings.

5. **Scheduling.**  Threads vs. async tasks vs. interleaved-on-one-
   thread.  Each has implications for fairness (B must keep up;
   starving B means the SAT case never terminates).

6. **The dual (validity).**  All of the above applies to validity
   search by running on the original NNF instead of its complement.
   The framework should be parameterized on which NNF (the
   distinction is just "is `nnf` the formula or its complement?").
   Both processes' soundness/completeness arguments transfer
   verbatim.

7. **Comparison with the existing `classify_paths` machinery.**  The
   existing code already has a `Cover = Vec<Pair>` and emits
   `PathsClass::Covered(CoveredPathPrefix)` events as B's analogue
   produces them.  The dual framework can re-use that infrastructure
   for B — and for A's input — wholesale.

## What this would replace / coexist with

The dual framework is **architecturally different** from
`PathSearchController` but doesn't have to displace it.  A reasonable
roadmap:

1. **Phase 1 — wrap the existing path-search.**  Implement
   `BasicDualPathController` and `BasicCoverController` with the
   simplest cover-state representation (`Vec<CoveredPathPrefix>`).
   Run on the same benchmarks, confirm it gets the same answers.
   Get the framework's plumbing right.
2. **Phase 2 — A-side experimentation.**  Implement
   `GreedyMaxCoverController`, then `LearnedActivityController`.
   Measure where they help.
3. **Phase 3 — B-side reuse.**  Wire up `Smart` and `Cdcl` as B
   controllers in the dual framework.
4. **Phase 4 — cover-state representations.**  Try BDD-based and
   CNF-based representations.  Compare against the simple
   append-only version.

If all phases turn up ho-hum results, the dual framework is a
research artifact and the existing single-DFS approach stays.  If
any phase produces a clear win on the benchmarks where matrix-CDCL
struggles (faulty-adder family, rast-p11.k20), it's the entry
point for the next architectural rebuild.

## What this is *not*

* **Not a faster propagation algorithm.**  Both A and B can use the
  same propagation infrastructure.  This is about how the search is
  structured, not how individual steps run.
* **Not magic on hard instances.**  The 27-bit faulty adder takes
  56 seconds in matrix-CDCL because the matrix DFS explores ~30 M
  pushes; the dual framework would explore the same space in B,
  with A doing extra work in parallel.  At best the parallelism
  gives a constant-factor speedup (≤2× on a 2-core machine).  The
  asymptotic gap to mainstream CDCL solvers remains.
* **Not a guarantee of correctness for free.**  The cross-process
  invariants ("A's cover state never claims a path that's
  reachable") need careful proof, especially with concurrency.

## Testing strategy

* **Round-trip on every existing test formula.**  Both processes
  agree with the existing controllers' answers.
* **Concurrency stress tests.**  Repeat each benchmark with
  randomised scheduling to surface race conditions.
* **A/B latency** — measure how often B's prunes come from A's
  cover state vs. B's own scan.  Above ~50 % suggests the framework
  is paying off; below ~10 % suggests A is too slow to keep up.
* **A's queue depth** — how many pairs does A get ahead of (or
  behind) B?  Sustained large queues mean B is generating faster
  than A consumes.

## Files this would add

A reasonable layout:

```
src/dual/
    mod.rs            — driver, traits, types
    pair_pool.rs      — shared pair log
    cover_state.rs    — CoverState trait + impls
    cover_basic.rs    — BasicCoverController
    cover_greedy.rs   — GreedyMaxCoverController
    cover_learned.rs  — LearnedActivityController
    path_basic.rs     — BasicDualPathController
    path_smart.rs     — SmartDualPathController
    path_cdcl.rs      — CdclDualPathController
```

The existing `src/controller/*.rs` modules stay; the dual framework
is a parallel architecture.

## Recommendation

Start with **Phase 1 only**: a minimal driver, the simplest A and B
controllers, the same `Vec<CoveredPathPrefix>` cover state the
existing code already produces.  Get correctness on the test suite.
That's a 1-2 week implementation that establishes whether the
plumbing works without committing to any of the harder design
decisions (BDDs, k-pair generalization, sophisticated
heuristics).

Defer phases 2-4 until phase 1 either reveals a problem with the
architecture or completes cleanly enough to justify investing in
the harder pieces.
