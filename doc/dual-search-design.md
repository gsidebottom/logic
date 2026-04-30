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
