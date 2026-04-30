# Lazy Matrix-DFS — Investigation

This is a design investigation, not a finished feature.  The motivating
hypothesis was: the matrix-DFS visits every Sum child structurally, so
even when CDCL propagation has already determined what's in those
subtrees, the engine pays per-step overhead (recursion, frame
allocation, controller dispatch) to walk through them.  A lazy DFS —
modeled on how CNF-CDCL solvers operate on a flat assignment, picking
decisions only when propagation gets stuck — should be able to skip
that work.

The investigation found the hypothesis is **mostly wrong on the
benchmarks I have**, for an instructive reason.  The design is still
sound as architecture, but the expected speedup doesn't materialize,
so this writes up the findings rather than proposing a build.

## The current DFS

The engine ([`NNF::for_each_path_prefix_ord`](../src/matrix.rs)) is a
closure-based recursive DFS over the NNF tree:

```
traverse(NNF)
  Lit(l):    push l, call controller, recurse via continuation, pop
  Prod(ch):  for each alt (filtered+sorted by prod_ord)
               push path index, call controller, recurse, pop
  Sum(ch):   visit children one-at-a-time; the "after this child"
             continuation visits the next; deepest level fires
             is_complete=true on the controller
```

The CDCL controller ([`CdclController::should_continue_on_prefix`](../src/controller/cdcl.rs))
is reactive — it gets invoked at every Lit push, every Prod alt entry,
and every path completion.  Its job per call is:

1. Backtrack: pop push-frames whose lits the DFS has popped.
2. Delegate to the inner cover-aware controller.
3. Forward: for each newly-pushed lit, append to trail, run
   `process_push` to cascade propagation (unless the lit was already
   implied), conflict-analyze on cascade conflict, and learn a clause.

For CNF-via-complement search, the NNF is shaped as
`Sum(Prod(Lit, Lit, ...) | Prod(Lit, ...) | ...)` — flat
Sum-of-Prod-of-Lits.  A "path" picks one lit per Prod (one per
clause-cube); a complete path corresponds to a candidate assignment.

### Where the engine is structural rather than driven

* **Sum traversal is in declaration (or `sum_ord`) order, irrespective of
  trail state.**  The same Sum-child gets visited even when its only
  unblocked alt has already been propagated as implied.
* **Prod traversal still descends into the chosen alt's `NNF::Lit`
  recursion** even when CDCL's `prod_ord` has already returned a
  single-alt list (i.e. the alt is fully forced).  The push-frame
  allocation, the `should_continue_on_prefix` call, and the trail.push
  all happen — they just no-op on `process_push` because the lit was
  already implied.

The hypothesis was that this last item — descending into already-implied
alts — was a substantial cost.  CDCL solvers traditionally don't visit
nodes for forced variables; they propagate, then make decisions only
when stuck.  Restructuring our DFS the same way ought to skip the
"engine descent for forced choices" overhead.

## Instrumentation

I added counters to the CDCL controller (visible behind `CDCL_INSTR=1`)
to characterize where work goes.  The relevant fields:

| field | meaning |
|-------|---------|
| `instr_calls` | total `should_continue_on_prefix` calls |
| `instr_calls_with_push` | calls where the DFS pushed at least one new lit |
| `instr_pushes_already_implied` | pushes where the lit was already on the trail as `Implied(...)` (process_push skipped) |
| `instr_pushes_propagated` | pushes that ran the cascade |
| `instr_pushes_conflict` | pushes that immediately conflicted (complement was on the trail) |
| `instr_implied_emitted` | total implied-lit trail entries added by cascades |

Run with `CDCL_INSTR=1 ./target/release/sat --cdcl < formula.cnf`; the
counters print on controller drop.

## Numbers

Single-run, release build, after the LBD step landed:

| Benchmark | time | calls | calls w/ push | already-implied | propagated | implied emitted | conflicts | restarts |
|-----------|-----:|------:|--------------:|----------------:|-----------:|----------------:|----------:|---------:|
| PHP-10-9  | 0.06 s | 5 940 | 2 832 | **1** | 2 831 | 43 468 | 2 142 | 13 |
| PHP-11-10 | 0.24 s | 13 130 | 6 244 | **2** | 6 242 | 107 459 | 4 840 | 25 |
| PHP-12-11 | 1.19 s | 28 552 | 13 531 | **2** | 13 529 | 257 877 | 10 699 | 45 |
| PHP-14-13 | 32.7 s | 132 776 | 62 651 | **5** | 62 646 | 1 421 184 | 51 196 | 156 |
| Random 3-SAT n=100 | 0.58 s | 48 502 | 23 788 | **2 514** | 21 274 | 379 987 | 11 275 | 46 |
| `faulty_add_at_most(3;1;1;0;3;0;1)` SAT | 1.0 ms | 13 668 | 7 035 | **435** | 4 794 | 200 | 1 806 | 0 |
| `faulty_add_at_most(4;1;1;0;3;0;1)` SAT | 5.1 ms | 43 698 | 22 325 | **990** | 15 358 | 450 | 5 977 | 0 |
| `faulty_add_at_most(27;0;134217727;1;134217727;1;1)` UNSAT | 220 ms | 222 525 | 127 945 | **79 801** | 44 604 | 35 645 | 3 540 | 0 |
| `faulty_add_at_most(27;0;134217727;1;134217727;1;2)` SAT | 56 633 ms | 52 249 729 | 29 718 334 | **18 689 664** | 10 088 614 | 4 896 392 | 940 056 | 0 |

### What this says

* On PHP, **already-implied pushes are below 0.01%** of pushes.  PHP's
  structure means propagation rarely surfaces a lit that later happens to
  be the canonical choice for a still-to-visit clause.  The engine
  descends into a Prod, `prod_ord` returns one alt (the unblocked one),
  and that alt's lit is *new* on the trail — `process_push` fires and
  does real work.
* On random 3-SAT, **about 10% of pushes are already-implied** — denser
  variable overlap means propagation more often pre-fills future Prod
  choices.
* On the 3-bit `faulty_add_at_most` (a structured arithmetic-circuit
  SAT instance), **6.2% of pushes are already-implied** — between PHP
  and random 3-SAT.  But the total search is tiny (7 035 pushes
  finishing in ~1 ms), so the 6 % saving would be ≈60 µs absolute —
  the CDCL controller is already running at ~140 ns/push on this
  formula.  CDCL is actually marginally *slower* than `SmartController`
  here (1.00 ms vs 0.84 ms) because the conflict/learning machinery is
  pure overhead when no learned clauses are produced (this run had
  `learned=0` despite 1 806 conflicts — every conflict was a path-level
  conflict, not a cascade conflict).
* On the 4-bit `faulty_add_at_most` the same pattern holds: 4.4 %
  already-implied, `learned=0` despite 5 977 conflicts, CDCL ~1.36×
  slower than Smart (5.05 ms vs 3.71 ms).  Lazy DFS arithmetic: 4.4 %
  of 22 325 pushes at ~225 ns/call ≈ 220 µs absolute savings —
  doesn't even cover the CDCL/Smart gap, let alone close the
  ~6.9× gap to CaDiCaL.  The matrix search on faulty-adder formulas
  finds a SAT model fast enough via plain backtracking that *all* the
  CDCL machinery is overhead.
* **The 27-bit faulty adder breaks this pattern.**  With 459 variables
  and an UNSAT outcome (1 fault is insufficient to reconcile the
  expected 0 + (2²⁷-1) + 1 = 2²⁷-1 with the actual 2²⁷), the search
  has to exhaust an exponential space rather than find a model.
  Result: **62.4 % of pushes are already-implied** — an order of
  magnitude jump from the smaller SAT cases.  Propagation cascades
  extensively (35 645 implied lits over 44 604 propagated pushes).
  CDCL takes 220 ms vs CaDiCaL's 1.3 ms (166×).  Lazy DFS arithmetic:
  79 801 already-implied pushes — if lazy mode shaves 200-500 ns
  off each via skipping the recursion / inner-controller call,
  that's 16-40 ms absolute savings — **a 7-18 % speedup on this
  benchmark**, the first time the data has supported any meaningful
  win.
* **The 27-bit / 2-fault case (SAT) confirms the pattern isn't
  UNSAT-specific.**  Same circuit, same expected mismatch, but with
  2 faults permitted the formula is satisfiable.  Yet the matrix
  DFS still grinds for **56.6 seconds** (vs CaDiCaL's 1.5 ms — a
  37 800× gap).  Already-implied pushes: **18 689 664 / 29 718 334
  = 62.9 %** — essentially identical to the UNSAT case's 62.4 %.
  The matrix-method's failure mode here is exploring the
  combinatorial space of fault-variable assignments before stumbling
  on a model that satisfies all the gate equations; it explores
  ~30 M push points to find a 593-lit assignment.  Lazy DFS
  arithmetic: 18.7 M already-implied pushes × 200-500 ns ≈
  **3.7-9.3 s absolute savings** out of 56.6 s — same 6.5-16.5 %
  proportional speedup as the UNSAT case.

  And `learned=0` *still*, even after 940 K conflicts on a 593-var
  formula taking 56 seconds — the matrix DFS on faulty-adder
  formulas produces zero cascade conflicts, so the CDCL learning
  machinery never engages.  Every byte of trail / 1UIP / clause-
  registration code is dead weight for this problem class.

### What the 27-bit data points mean

The earlier conclusion ("don't build lazy DFS, the savings are too
small") was drawn from PHP and small SAT instances where the search
finds a model fast.  The 27-bit faulty adder shows that on
hardware-verification-style formulas — whether SAT or UNSAT —
where the matrix has to explore a combinatorial space under heavy
propagation, the already-implied push fraction sits at ~62 %, and
lazy DFS would shave a 7-18 % slice off wall time.

The 1-fault and 2-fault numbers together are also a striking
demonstration that **CDCL's defining feature — clause learning — is
inert** on this problem family.  The matrix DFS on faulty-adder
formulas finds path-level conflicts (complement-on-trail at push
time) but never the cascade conflicts that produce learned clauses.
This is worth understanding in its own right and is now logged as
an open question in `doc/cdlc.md`.

That said, 7-18 % is not the right shape of speedup to close a
gap measured in 4-5 orders of magnitude.  CaDiCaL solves the
27-bit 2-fault case in 1.5 ms; matrix-CDCL takes 56.6 s.  Lazy
DFS would be 48-52 s vs 1.5 ms — still 32 000-35 000× slower.
The real fix for this problem class is a different algorithm,
not a different DFS shape.

The recommendation below remains "deferred" — building it requires
real engineering — but the *evidence base* has shifted:
unconditional "no" → conditional "yes for hardware-verification
workloads where you'd accept a 10-15 % speedup, no for SAT/PHP/
find-a-model cases."
* The dominant work is **cascade propagation**: 19 implied lits per
  propagated push on PHP-12-11, 23 on PHP-14-13, 18 on random 3-SAT.
  All of this happens *inside* `process_push`, which is a tight
  watched-literal loop — not a recursive descent.

So the per-step overhead the hypothesis was about (engine recursion +
controller dispatch for already-determined choices) is a small fraction
of total work — order **1% on PHP, 10% on random 3-SAT**.  Eliminating
it entirely wouldn't get a meaningful speedup.

## Where the hypothesis went wrong

The mental model "the engine wastes work descending into forced
choices" was right at the topology level: yes, the engine recurses
into single-alt Prods.  But the *cost of each such descent* is small —
roughly the inner controller's lit-counter update plus a frame
allocation.  The expensive operation per controller call is
`process_push` itself, and it skips the work for already-implied lits
(the `if !already_implied` gate at the top).

In CNF-CDCL solvers, the analog optimization is meaningful because
*decisions are expensive* (they're the search tree's branching points
and trigger BCP, conflict analysis, etc.).  Skipping a forced
"decision" saves a real chunk of work.  In matrix-CDCL, the equivalent
work has already been front-loaded into `process_push` — by the time
the engine reaches the corresponding Prod, the structural descent is
mostly bookkeeping.

## Design sketch (preserved for future reference)

If a future need does justify the restructuring — e.g. a heuristic that
needs clause-level decision flexibility the current `prod_ord` trait
can't express — here's the rough shape.

### State

```rust
struct LazySearch<'a, F: FnMut(PathsClass, bool) -> bool> {
    clauses: Vec<Vec<Lit>>,                  // flat Sum-of-Prod-of-Lits
    committed: Vec<Option<usize>>,           // committed[clause_id] = Some(alt_idx)
    decision_stack: Vec<DecisionFrame>,      // for backtrack
    ctrl: &'a mut CdclController<F>,         // reuse trail / propagation / 1UIP
}

struct DecisionFrame {
    clause_id: usize,
    alt_idx: usize,
    trail_len_before: usize,                 // for undo
    push_frame: PushFrame,                   // existing CDCL frame
}
```

### Main loop

```text
loop {
    # 1. Implication sweep (no decisions yet)
    for each undecided clause i:
        b = ctrl.prod_blocked[i]
        n = clauses[i].len()
        if b == n: conflict on clause i → analyze + backjump
        if b == n - 1:
            alt = ctrl.find_remaining_alt(i)
            committed[i] = Some(alt)         # bookkeeping only — lit already on trail

    # 2. Termination
    if every clause committed:
        emit complete path; return SAT (or continue if classify-all)

    # 3. Decision
    cid = pick_undecided_clause()            # most-constrained first
    alt = pick_best_alt(clauses[cid])        # VSIDS + phase saving
    lit = clauses[cid][alt]
    level = decision_stack.len() + 1
    ctrl.trail.push(TrailLit { lit, reason: Decision, decision_level: level })
    let mut frame = PushFrame::default();
    frame.trail_added = 1;
    match ctrl.process_push(lit, level, &mut frame):
        Ok: committed[cid] = Some(alt); decision_stack.push(...)
        Err(conflict_id):
            learned = ctrl.analyze_conflict(conflict_id)
            ctrl.register_learned_clause(&learned, &mut frame)
            target = learned.backjump_level
            while decision_stack.len() > target:
                f = decision_stack.pop()
                committed[f.clause_id] = None
                ctrl.undo(&f.push_frame)
}
```

### What changes vs. the current setup

* `NNF::for_each_path_prefix_ord` is bypassed — the lazy driver iterates
  clauses directly.
* `should_continue_on_prefix` is bypassed too — its phase 1 (backtrack
  via push-frames) and phase 3 (forward) are inlined into the loop.
* `prod_ord` and `sum_ord` aren't called.  The lazy driver picks
  decisions itself, and the picker can use any heuristic — clause-level
  ("clause with smallest unblocked-alt count"), variable-level ("var in
  most learned clauses"), or hybrid.
* Restart is trivially clean: clear `committed`, undo every frame in
  `decision_stack`, save phases as you go, then re-loop.
* `process_push` / `analyze_conflict` / `register_learned_clause` /
  `undo` are reused unchanged.

### Open design questions

1. **How to share the CDCL controller's state without contortions?**
   The lazy driver needs intimate access (`prod_blocked`, `find_remaining_alt`,
   `trail`, `process_push`, etc.) — these are currently `pub(crate)` /
   private.  Either expose more surface, or make the lazy driver a
   *method* of `CdclController` rather than a separate type.
2. **Cover certificates (validity-mode use).**  The lazy driver only
   makes sense for SAT-search via complement (`Sum(Prod(Lit*)*)`).  For
   validity, the structural DFS is needed to produce
   `prefix_positions` for cover certificates.  This is a clean split.
3. **Cancellation / progress.**  The current path goes through
   `CancelController` which polls a handle every step.  Lazy mode would
   need an equivalent — easy: poll once per loop iteration.
4. **Test parity.**  `cdcl_agrees_with_smart_on_all_cases` would need
   a lazy-mode equivalent (`cdcl_lazy_agrees_with_cdcl_on_sat_only`).
5. **Path enumeration vs. first-uncovered.**  Today the engine enumerates
   paths until the first uncovered one (for SAT) or all paths
   (for cover counting).  The lazy driver naturally fits "find first
   uncovered" — it stops at the first complete commitment.  For
   "enumerate all" it would need to backtrack from the SAT-completion
   and explore alternatives, which is more work to design.

### Where lazy DFS would actually pay off

Honest list, given the data:

* **Code architecture** — flatter loop, easier to reason about restart,
  easier to add new heuristics that don't fit the `prod_ord` shape.
* **More flexible decision heuristics** — clause-of-the-day picks
  (most-constrained, learned-rich, etc.) the trait can't currently
  express.
* **Cleaner CDCL pedagogy** — the resulting code reads like a textbook
  CNF-CDCL solver.
* **UNSAT / exhaustive-search workloads with heavy propagation** —
  the 27-bit faulty adder shows 62 % of pushes are already-implied
  in this regime; lazy DFS could plausibly save 10-20 % of wall
  time.  This is the first benchmark class where the data supports
  a measurable performance win.

What it does **not** buy:

* Material speedup on PHP — already-implied descents are <0.01% of
  pushes.
* Material speedup on random 3-SAT — even at 10% already-implied,
  the recursion work being skipped is a small fraction of per-call
  cost.
* Material speedup on small SAT instances (3-bit / 4-bit faulty
  adder) — the search finds a model fast and CDCL machinery is pure
  overhead.
* Smaller search tree — both designs visit the same paths.
* Faster `process_push` or conflict analysis — those are reused as-is.
* Closing the gap to mainstream CDCL solvers — even an optimistic
  20 % lazy-DFS speedup on the 27-bit case (220 ms → 175 ms) is
  still 130× slower than CaDiCaL's 1.3 ms.

## Recommendation

**Building lazy matrix-DFS as a pure performance optimization is
defensible only for UNSAT-heavy workloads** like hardware
verification (faulty-adder family, HWMCC).  On SAT-search and
random formulas the predicted savings are too small to recover the
engineering cost.

A pragmatic middle ground might be a *partial* refactor: keep the
structural DFS engine but add a "fast-path" hook so the controller
can short-circuit out of an entire Prod descent when its `prod_ord`
returns a single already-implied alt.  That captures the bulk of
the 27-bit case's potential savings without restructuring the
engine.  Worth scoping as a smaller experiment before committing
to a full lazy driver.

Reconsider the full lazy DFS if either:

* the partial fast-path hook turns out to deliver ≥10 % on the
  27-bit case, suggesting the architecture is the right next step; or
* a future heuristic needs decision flexibility the current trait
  can't express (likely candidates: clause-locking schemes, restart
  with partial state preservation, structure-aware variable
  selection); or
* an experimentally-motivated reason emerges to share more state
  between the inner cover-aware controller and the CDCL layer (the
  lazy form makes the boundary cleaner).

For now, the instrumentation counters stay in place behind the
`CDCL_INSTR` env var — they're cheap (~6 increments per
`should_continue_on_prefix` call) and useful for any future
investigation.

## Files touched by this investigation

* [`src/controller/cdcl.rs`](../src/controller/cdcl.rs) — added
  `instr_*` counter fields to `CdclController` and a `Drop` impl
  that prints them when `CDCL_INSTR` is set in the environment.
* No changes to the engine, the trait, or the matrix driver — by
  design, the investigation is observational.
