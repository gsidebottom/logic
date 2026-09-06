# Box-matrix SAT (Boolean satisfiability) backend — compiled nested boxes, parallel + distributed

*Design document — no implementation yet.  Companion to
[dual-search-design.md](dual-search-design.md) (the current matrix engine) and
[cover_certify.md](cover_certify.md) (the certificate format this must keep
honouring).*

## 0. The idea in one paragraph

Today every matrix backend (`smart`, `cdcl`, `eff`, …) walks the negation normal form (NNF) of the
complement literal by literal, discovering complementary pairs at proof time.
For a structured sub-formula that is wasteful: a full adder's complement has
**972 matrix paths, only 13 of which are uncovered, and only 8 distinct once
canonicalized** — and those 8 are just its truth table.  This backend makes the
matrix a tree of **boxes**.  The built-in `and`/`or` boxes behave as now; a
**compiled box** (e.g. `FullAdder(X,Y,C1,Z,C,U1,U2,U3)`) contributes its
precomputed canonical uncovered paths directly, so the search never re-derives the
959 internally covered paths, and coverage is tested per *box row* with a couple
of bitset ops instead of per literal.  Rows are bitsets, so canonical form is the
native representation, propagation is table-constraint propagation, and the
search parallelizes by splitting on box rows — locally over cores, and over
machines with a coordinator/worker layout.  Proofs stay in the existing
primitive cover-certificate format (compiled boxes are *search accelerators*,
never a trust boundary), so `sat-cover-verify` keeps working unchanged.

## 1. Motivation — the adder, measured

Formula (five definitional equivalences):

```
(U1 = X·Y) · (U2 = U3·C1) · (C = U1+U2) · (U3 = X ⊕ Y) · (Z = U3 ⊕ C1)
```

Run through the current engine on the complement (`/paths`, `complement:true`):
**972 paths, 13 uncovered, 8 canonical.**  The 8 canonical uncovered
paths, decoded to assignments (see §2.2 for the polarity convention), are the
adder's truth table — the internal signals come along for free:

| X Y C1 | Z C | U1 U2 U3 | trace paths |
|:------:|:---:|:--------:|:-----------:|
| 0 0 0 | 0 0 | 0 0 0 | 4 |
| 0 0 1 | 1 0 | 0 0 0 | 2 |
| 0 1 0 | 1 0 | 0 0 1 | 1 |
| 0 1 1 | 0 1 | 0 1 1 | 1 |
| 1 0 0 | 1 0 | 0 0 1 | 1 |
| 1 0 1 | 0 1 | 0 1 1 | 1 |
| 1 1 0 | 0 1 | 1 0 0 | 2 |
| 1 1 1 | 1 1 | 1 0 0 | 1 |

Three things to take from this:

- **972 → 8.**  Of the complement's paths, 98.7 % are covered *internally* —
  work that a compiled box does once, at compile time, instead of on every
  instance in every problem.
- **13 → 8.**  The uncovered paths are not even distinct; the same model is reached
  by up to 4 different traversals.  Canonical form (sorted literals, duplicates
  dropped — exactly the new `canonical` view in the web user interface (UI)) removes that redundancy.
- **It composes multiplicatively.**  A ripple-carry adder of `k` full adders
  has `972^k` primitive complement paths but `8^k` row combinations — and with
  propagation on shared carries, far fewer are ever visited.  Multipliers, the
  circuit family classically hard for conflict-driven clause learning (CDCL) solvers, are grids of exactly these boxes.

## 2. Semantics

### 2.1 Matrix method, restated for boxes

The engine walks the NNF of the complement `G = ¬F`.  A path picks **one**
child at each `Prod` (AND) and traverses **all** children at each `Sum` (OR)
— the `EffectiveCountIndex` recurrence `Sum → ∏, Prod → ∑` in
`src/dual/effective_count.rs`.  A path is *covered* if it contains a
complementary pair `ℓ, ¬ℓ` (the pair *covers* it), *uncovered* otherwise.  `F` is UNSAT (unsatisfiable) iff every path of `G` is covered; an
uncovered path is a consistent way to falsify `G`, i.e. a model of `F` (so `F` is SAT, satisfiable).

A **box** is any sub-tree of the matrix that can answer "what are your uncovered
paths, given what is already on the path?"  `Sum`/`Prod` boxes answer this
structurally (that *is* the current search).  A **table box** answers it from
a precomputed list of canonical rows.

### 2.2 Polarity convention (the trap)

Path literals are the literals of the *complement's* NNF.  An uncovered path is
made consistent by making every literal on it **false** (this is what
[cover_certify.md](cover_certify.md) means by "each visited lit is the negation
of the original CNF lit" — CNF being conjunctive normal form).  So a compiled box's canonical uncovered path
`{C, C1, U1, U2, U3', X', Y, Z'}` is the model `X=1 Y=0 C1=0 → Z=1 C=0,
U1=0 U2=0 U3=1`.  The table above is shown decoded; the engine stores rows in
path-literal form, because that is what complementarity is tested against.

### 2.3 Two tables per box

A box `B` occurs in `F` either positively (walked as `¬B` inside `G`) or
negatively (walked as `B`).  Each needs its own compiled table:

- **`¬B` table** — uncovered paths of `¬B`'s matrix = models of `B`.  For the adder,
  8 total rows.  This is the common case (a constraint used positively).
- **`B` table** — uncovered paths of `B`'s matrix = falsifications of `B`.  For the
  adder these are the assignments violating some equation; larger, but still
  finite and precomputable, and usually *partial* rows.

Rows are in general **partial** assignments (don't-cares are simply absent
from both masks); the adder's happen to be total.

### 2.4 Interface vs internal variables

`FullAdder(X,Y,C1,Z,C,U1,U2,U3)` exposes the internals `U1..U3`.  Keep both
options:

- **Exposed** (as written): rows carry the internal literals; correct whenever
  an internal name is also referenced elsewhere (observation, sharing).
- **Projected**: drop the internal columns and dedup rows → the table of
  `∃U1 U2 U3. B`.  Sound only if the internals are local to the box (fresh
  names).  For the adder this is a no-op on row count (8 rows either way) but
  for hierarchical boxes it is what keeps tables small (§5.3).

## 3. Core engine

### 3.1 Representation

- **Variables** are dense indices; a literal set is a pair of bitsets
  `(pos, neg)` over variables.  `w = ⌈nvars/64⌉` words.
- **Row** = `(pos, neg)`.  A row *is* its canonical form: no order, no
  duplicates.
- **Assignment** (current path prefix) = `(pos, neg)` plus a trail for undo.
- **Is a row covered against the prefix?**
  `row.pos & pre.neg == 0 && row.neg & pre.pos == 0` — 2 ANDs, 2 compares per
  word, and vectorizable with SIMD (single instruction, multiple data).  This *is* the complementary-pair test, hoisted from
  "per literal" to "per row".
- **Box** (compiled): `rows: Vec<Row>`, plus per-literal row indexes
  (`rows_with[lit]: RowBitset`) so that "rows still consistent" after adding a
  literal is a bitset AND, not a scan.
- **Box** (structural `Sum`/`Prod`): the existing NNF/arena walk, exposed
  behind the same trait so mixed matrices (compiled boxes inside ordinary
  formula) work from day one.

```rust
pub trait Box_ {
    fn vars(&self) -> &VarSet;
    /// Rows of this box still uncovered under `prefix` (the `live` set); iterated lazily.
    fn uncovered_rows<'a>(&'a self, prefix: &Assignment, live: &RowBitset)
        -> impl Iterator<Item = RowId> + 'a;
    /// Literals every uncovered row agrees on (forced), or None if no row is uncovered.
    fn implied(&self, live: &RowBitset) -> Option<LitSet>;
}
```

### 3.2 Search = DPLL (Davis–Putnam–Logemann–Loveland) over box rows, with table propagation

```
solve(prefix):
    propagate(prefix)                       # §3.3; may close the path
    if some box has 0 uncovered rows: return COVERED (record reason)
    if every box is decided (1 uncovered row each): return UNCOVERED (model = prefix)
    b := choose_box(prefix)                 # §3.4
    for r in b.uncovered_rows(prefix):
        push(r); if solve(prefix) == UNCOVERED: return UNCOVERED; pop()
    return COVERED
```

Choosing a row appends its literals to the prefix.  A path through the whole
matrix is one row per compiled box plus the structural choices — but note that
compiled boxes are examined *once* each, whereas the literal-level walk
revisits a box's sub-tree for every prefix that reaches it.

### 3.3 Propagation (what makes it a solver, not an enumerator)

After each push, for every box that shares a variable with the new literals,
narrow `live &= rows_with[¬lit]`-complement.  Then:

- **Box with 0 live rows** → every completion is covered → backtrack.  This is
  the cover test at box granularity: for a `FullAdder` it kills 959
  paths' worth of exploration in one bitset op.
- **Box with 1 live row** → that row is forced; push its literals (unit
  propagation over the table).
- **Literal common to all live rows** → forced (generalized arc consistency on
  a table constraint).  For an adder with `X,Y` fixed this immediately fixes
  `U1, U3`; with `C1` also fixed, everything.

Cascade to fixpoint.  This is exactly table-constraint generalized arc consistency (GAC) as in constraint programming (CP) solvers,
and it is far stronger than clause-level Boolean constraint propagation (BCP) on the Tseitin encoding of the
same gates — the reason CP and satisfiability-modulo-theories (SMT) solvers beat plain CDCL on word-level
arithmetic.

### 3.4 Branching heuristic — EFF (effective path count), lifted

`EffectiveCountWrapper` orders `Sum`/`Prod` children by the effective path
count under the current prefix.  The lifted version is immediate: a compiled
box's effective count *is* `popcount(live rows)`.  Branch on the box with the
fewest live rows (most constrained first), tie-break by shared-variable degree.
Structural boxes keep the existing EFF ordering, so the heuristic is uniform.

### 3.5 Learning (phase 2, measured)

A dead box (0 live rows) has an explanation: for each row, one prefix literal
that killed it; the set of those literals is a **nogood** — a learned clause
over the prefix, exactly as in lazy clause generation (CP-with-learning).  Add
first-unique-implication-point (1UIP) analysis and restarts by reusing `CdclController`'s machinery over
these nogoods.  This makes the backend a CDCL solver whose propagators are
compiled boxes.  Off by default until the A/B in §9 shows it pays — the
`phase4_cubes` result (learned-cube sharing: "overhead with no benefit") is the
cautionary precedent for assuming learned information helps the cover search.

## 4. Certification — compiled boxes are accelerators, not a trust boundary

Every UNSAT verdict must still certify, and the checker must not have to trust
the compiler.  Two layers:

### 4.1 Compilation soundness (per box, once)

A compiled table is accepted only with a **certificate that it equals the
box's uncovered paths**.  For boxes of ≤ ~20 variables, exhaustive enumeration by
the *existing* engine (which is how the table above was produced) plus a
cross-check that the row set equals the canonicalized enumeration is itself
the certificate; the compiler records, per row, the primitive **trace paths**
(the `uncovered_path_positions` the engine already emits) and the box's
**static internal cover** — the complementary pairs closing its other paths
(the same construction as `emit_static_cover` in `controller/cdcl.rs`, which
enumerates every complementary pair over positions independent of search
order).  Both are stored with the box in the library.

### 4.2 Proof soundness (per problem)

Phase 1 emits proofs at the **primitive level**, unchanged in format:

- the certificate is the union of every box instance's static internal cover
  (positions re-based to the instance's location in the NNF) and the cross-box
  pairs the search found;
- `sat-cover-verify` checks it exactly as today, with no knowledge that boxes
  existed.

This is the honest baseline: whatever the compiled search did, the proof it
hands over is a plain complementary cover of the primitive matrix.  A later
**box-aware certificate** (`v4`: `box <name> <instance-positions>` entries
whose rows are checked against the shipped per-box certificate) buys
compactness — a `k`-adder proof shrinks by roughly the internal-cover size per
instance — but it is an optimization, gated on the primitive path being green.

Gate for either: reproduce known values first (the adder examples in the UI —
"Full Adder", "123+47=170", "Adder Unsat" — and the pigeonhole-principle (PHP)/RoundRobin corpus).
A checker re-encodes the rule it checks, so a new proof system is validated
on instances whose answer is independently known — never on the checker's
say-so alone.

## 5. Compilation and the box library

### 5.1 Compiler

`box-compile <definition> → <table + certificate>`: parse the definition (the
existing formula language), build both complements' matrices, enumerate uncovered
paths with the existing engine, canonicalize (sorted, deduped — the UI's
canonical view is the interactive front end of this), record trace paths and
the static cover, write a library entry.  Embarrassingly parallel across boxes.

### 5.2 Parametric boxes

A library entry is over **formal** parameters; an instance is a renaming
(`FullAdder(a3, b3, c3, s3, c4, u1_3, u2_3, u3_3)`), which is a bitset
column permutation — no re-compilation.  Row masks are stored over the formal
index space and mapped at instantiation.

### 5.3 Hierarchical boxes

A box may be defined in terms of boxes (`RippleAdder4 = FullAdder × 4` with
internal carries).  Compile by running *this* engine on the definition (boxes
inside), then **project** the local internals (§2.4).  Tables grow with the
interface, not the internals — a 4-bit adder projected to its 13 interface
signals has at most 2^9 = 512 rows (one per input combination), independent
of the 20 gate outputs inside.  Where projection would still blow up, keep the
box hierarchical at solve time (the engine handles nested compiled boxes
because a compiled box is just a `Box_`).

### 5.4 Getting boxes into a problem

- **Explicit (first):** box syntax in the formula language and the web UI —
  `FullAdder(X,Y,C1,Z,C,U1,U2,U3)` resolves against a library file; the UI's
  paths view shows compiled rows in the canonical tree (they *are* canonical
  paths) and highlights them in the diagram exactly as now.
- **Detected (later):** for competition CNF, recognise gate clusters
  (Tseitin-encoded XOR/AND/majority, adder and multiplier cells) and replace
  them by library instances.  This plugs into hydra's structure dispatch
  (`cook_pbp::detect_shape` and siblings) as one more detector, routing
  circuit-shaped instances to this backend.

## 6. Multi-core parallelism (out of the box)

- **Unit of work = a sub-tree of the row search** (a prefix of row choices).
  Workers run the §3.2 loop on their own `Assignment`; the compiled tables and
  the arena are shared read-only (`Arc`).  Per-worker state is a few bitsets —
  cheap to fork.
- **Work stealing** via `rayon::scope`/`crossbeam-deque` (rayon is already a
  dependency, 43 `par_iter` sites): a worker that reaches a node with `n` uncovered
  rows on a wide box pushes `n−1` siblings as stealable tasks.  Splitting
  prefers boxes with many live rows near the top of the tree so tasks are
  balanced.
- **Determinism mode**: fixed split depth `k` and a fixed task order, so the
  set of tasks — and therefore the certificate — is reproducible.  Off, the
  scheduler is free-running (faster, non-deterministic).  The `eff` A/B
  history showed how much a nondeterministic engine costs in measurement
  trust, so the deterministic mode is the default for benchmarks.
- **Proof assembly**: each task returns its cover (or a model); the parent
  concatenates.  Because tasks partition the path space by prefix, the union
  is a cover of the whole — no merge logic beyond position re-basing.
- **Nogood sharing** (with §3.5): a lock-free append-only pool, drained in
  batches — the phase-4 write-up's "pool contention / O(N²) drain" risk is
  handled by batching from the start, and sharing stays off until measured.
- Target: saturate all 12 performance cores (P-cores), a project rule; watch for single-threaded tails
  when few tasks remain (re-split the survivors, §7.4).

## 7. Distributed execution — ready for Amazon Web Services (AWS)

The multi-core design already speaks in prefix-partitioned, self-contained
work units with mergeable certificates; distribution is the same protocol over
a queue.

### 7.1 Roles

- **Coordinator** (one small instance, or a Step Functions state machine):
  loads the problem + library, runs the top of the search to depth `k`
  (deterministic split), emits work units, tracks completion, assembles the
  certificate, enforces the budget.
- **Workers** (ECS/Fargate containers or EC2 spot instances — Elastic Container Service, Elastic Compute Cloud; AWS Batch is a natural fit; Lambda for
  units expected < 15 min): stateless.  Pull a unit, solve it with the
  multi-core engine, upload `{UNCOVERED: model | COVERED: cover | SPLIT: children}`.

### 7.2 Plumbing

| concern | choice | why |
|---|---|---|
| work queue | SQS (Simple Queue Service); FIFO — first-in-first-out — ordering not required, units are idempotent | at-least-once is fine: a duplicate solve returns an identical cover |
| artifacts | S3 (Simple Storage Service): problem, library, per-unit certs, assembled proof | workers need no shared state |
| box library | S3 + local cache, content-addressed by definition hash | compile once, everywhere |
| coordination | DynamoDB unit table (`pending/running/done`, attempt count) | visibility timeout + retries give fault tolerance |
| observability | CloudWatch: units/s, uncovered-row histograms, cover sizes | spot the single-tail unit early |

### 7.3 Certificate assembly

The final proof = the split tree (which prefixes were assigned to which
units) + each unit's cover.  A checker verifies (a) the prefixes at depth `k`
partition the row space of the split boxes and (b) each unit cover closes
every path under its prefix.  Both are local checks; the checker itself
parallelizes per unit.  The whole proof remains a primitive cover after
re-basing, so `sat-cover-verify` can check the assembled file end to end.

### 7.4 Hard units and budget

A worker that exceeds its per-unit budget returns `SPLIT` with its own
children (deeper prefixes) rather than failing — the tree deepens where the
problem is hard.  The coordinator enforces a global wall-clock and dollar cap
(spot pricing, max instances), and reports *what was proved* on timeout: the
covered units are a partial cover, exactly the "partial cover" the current
`Paths` UI already visualizes.

### 7.5 What this is *not*

Not a shared-memory CDCL portfolio.  Learned nogoods are not exchanged across
machines in v1 (workers are stateless by design); the parallelism is search-
space partitioning, which is what a prefix-partitioned proof format supports
cleanly.  Cross-machine sharing is a measured extension, same rule as §3.5.

## 8. Integration with the existing code

| seam | change |
|---|---|
| `src/bin/sat.rs` `MatrixBackend` | new variant `Boxes` (`matrix.boxes`), same `-b`/`--emit-cover` plumbing as `eff_cover` |
| `src/controller/mod.rs` `PathSearchController` | the box engine is a controller for structural sub-trees, so mixed matrices reuse `classify_paths_with_arena` unchanged |
| `src/dual/effective_count.rs` | lifted count = live-row popcount; one new arm |
| `src/controller/cdcl.rs` `emit_static_cover` | reused per box at compile time (§4.1) |
| `src/bin/sat_cover_verify.rs` | unchanged in phase 1; `v4` box entries later |
| `src/bin/web_app.rs` `/paths` | serve compiled rows as canonical paths with trace positions, so the UI's canonical tree + diagram highlighting work as-is |
| `tools/gbd/run_benchmark.py` | `-b boxes`, existing soundness gates (witness + cover verify) |
| hydra dispatch (`cook_pbp::detect_shape` family) | circuit detector → route to `boxes` |
| new `src/boxes/` | `row.rs` (bitsets), `table.rs`, `engine.rs`, `compile.rs`, `library.rs`, `par.rs`, `dist/` |

## 9. Phased plan, with gates

Cheap de-risks first; every phase has a measurable gate and nothing is
believed without an equal-budget comparison.

| phase | build | gate |
|---|---|---|
| **M0** (done, this doc) | verify 972/13/8 and extract the table on the real engine | ✓ table matches the adder truth table row for row |
| **M1** core | bitset rows, table + structural boxes, depth-first search (DFS) + propagation, single core; explicit box syntax | same verdicts as `eff`/`cdcl` on the UI adder examples and the test corpus; **every UNSAT certifies** via the primitive cover |
| **M2** compiler + library | `box-compile`, parametric instances, per-box certificate, static internal cover | a `k`-bit ripple adder assembled from `FullAdder` instances certifies for `k` up to the largest the current engine can do, and beyond |
| **M3** multi-core | work stealing, deterministic mode, cover merge | ≥ 8× on 12 cores on a multiplier-verification instance; certificate byte-identical in deterministic mode |
| **M4** measure | `run_benchmark` A/B vs `eff`, `cdcl`, `cadical`, `hydra` on an arithmetic-circuit set (adders, multipliers, the CLP(B) — constraint logic programming over Booleans — examples), **equal wall-clock**, sound gates on | the honest question: does it beat cadical on the circuit slice? |
| **M5** learning | nogoods + 1UIP + restarts (§3.5), on/off | only kept if M4's numbers improve |
| **M6** detection | gate/adder/multiplier detector into hydra | competition CNF instances routed and solved+certified |
| **M7** distributed | coordinator/worker on AWS, split-tree certificates | a multi-hour instance solved across N spot workers with an assembled, checked proof; cost within cap |

M4 is the gate that decides whether M5–M7 are worth building.  Its framing
follows the project's hydra lesson: we do not expect to beat CDCL at general
search; the claim is a **certified win on the circuit slice**, where CDCL's
clause-level view of arithmetic is its known weakness.

## 10. Risks

1. **The win is family-specific.**  Boxes help where the formula *has* boxes.
   Random/industrial CNF without recoverable structure gains nothing — that
   is the hydra premise, and M4 must say so if true.
2. **Negative-occurrence tables can be large** (§2.3).  Mitigation: keep the
   structural definition for that polarity, or compile lazily on first use.
3. **Projection blow-up** for wide interfaces (§5.3).  Mitigation: stay
   hierarchical; measure row counts at compile time and refuse to flatten past
   a threshold.
4. **Certificate size** in phase 1 scales with static internal covers per
   instance.  Acceptable for correctness; `v4` fixes it if it matters.
5. **Position re-basing bugs** when expanding box covers into primitive
   positions.  Mitigation: the checker catches them — that is the point of
   not trusting the compiler — and the gate reproduces known values first.
6. **Parallel measurement trust.**  Deterministic mode for all benchmarks.

## 11. Questions for Greg

1. Box syntax: `FullAdder(X,Y,C1,Z,C,U1,U2,U3)` with a library file, or
   `let FullAdder(...) = …` definitions inline in the formula?
2. Should internals default to *projected* (fresh, local) or *exposed*?  The
   adder example exposes them; hierarchical boxes want projection.
3. Priority of M6 (CNF detection) vs M7 (distributed): detection is what
   makes competition instances reachable; distribution is what makes the
   big ones finish.
4. Is AWS Batch acceptable as the first worker substrate (simplest), or do
   you want Lambda-first for cost granularity?
