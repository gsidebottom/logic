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
matrix a tree of **boxes**, and the boxes are **designed by the user for the
problem at hand** — as jq definitions, the way `lib/adder.jq` already builds
adders — then **compiled to Rust code** (a per-problem specialized solver, or
dynamically loaded plug-ins), not interpreted from tables at run time.  The
built-in `and`/`or` boxes behave as now; a
**compiled box** (e.g. `FullAdder(X,Y,C1,Z,C,U1,U2,U3)`) contributes its
precomputed canonical uncovered paths directly, so the search never re-derives the
959 internally covered paths, and coverage is tested per *box row* with a couple
of bitset ops instead of per literal.  Rows are bitsets, so canonical form is the
native representation, propagation is table-constraint propagation, and the
search parallelizes by splitting on box rows — locally over cores, and over
machines with a Mallob-style malleable, clause-sharing layout.  Proofs never
trust box code: each box ships an ordinary UNSAT certificate that its table is
complete, a small **formally verified** checker composes those with the
box-level cover (compiled boxes are *search accelerators*, never a trust
boundary), and phase 1 can still expand everything into today's primitive
cover format so `sat-cover-verify` keeps working unchanged.

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

*(The M1 engine.  Since 2026-09-13 the engine is conflict-driven — §3.5,
§10.1 — with the propagation below unchanged; decisions are single literals
chosen by activity rather than rows.)*

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

### 3.5 Learning (phase 2, measured — delivered 2026-09-13, see §10.1)

A dead box (0 live rows) has an explanation: for each row, one prefix literal
that killed it; the set of those literals is a **nogood** — a learned clause
over the prefix, exactly as in lazy clause generation (CP-with-learning).  Add
first-unique-implication-point (1UIP) analysis and restarts by reusing `CdclController`'s machinery over
these nogoods.  This makes the backend a CDCL solver whose propagators are
compiled boxes.  Learning matters more than in the first draft of this design: Mallob's
evidence (§8) is that *sharing* learned clauses is what makes distributed
solving scale, so nogoods and their sharing are first-class components — but
still gated by the A/B in §10; the `phase4_cubes` result (learned-cube
sharing: "overhead with no benefit") is the cautionary precedent for assuming
learned information helps the *cover* search.

**Which explanation.**  The kill masks give, for every dead row, the set
of assigned literals that killed it; any hitting set of those sets is a
valid explanation, and the obvious one — trail order, every literal that
kills a row not yet covered — is not minimal: a literal picked early is
often redundant given the later picks.  The engine chooses among three
(`BOXES_EXPLAIN`, 2026-09-15): `greedy`, that baseline; `minimal`, the
same pass preferring literals that cost the learned clause nothing (level
0, or already seen by the analysis) and then made inclusion-minimal,
newest pick first; and `cover`, largest remaining coverage first (the
set-cover greedy, ties by the same preference) and then made
inclusion-minimal — the default.  On the adder cones of §10.1 `cover`
halves the explanation (2.2 literals against greedy's 4.9) and with it
the conflicts; the measurement is in §10.1.

**Which clause.**  The 1-UIP clause is minimised the MiniSat way before
it is learned: a literal whose reason consists of literals already in the
clause, or at level 0, or themselves redundant by the same test, is
dropped — the recursive test with the abstract-level filter, run over the
same lazy explanations.  Those are cached per assignment, so an analysis
and its minimisation explain a table-propagated variable once and later
conflicts reuse it until the variable is unassigned (`BOXES_MINIMIZE`,
on by default; measured in §10.1).

**When to restart.**  Two policies (`BOXES_RESTART`): Luby restarts
with a 64-conflict unit, and — the default — Glucose's dynamic rule — restart when the
last 50 learned clauses' LBD average exceeds 0.8× the running average,
blocked while the trail is 40 % longer than usual — alternating with
stable phases of Luby restarts (unit 512) whose length doubles from
1,000 conflicts, the SAT-side half of CaDiCaL's stable/unstable
scheme without its target phases; a restart reuses the trail down to
the first decision the heap would now make differently.  Measured in
§10.1.

**Which phase.**  Saved phases, and (`BOXES_PHASES=1`, 2026-09-15, off
by default — §10.1) CaDiCaL's target and best phases: after every conflict-free propagation
a trail longer than any since the last restart stores its assignment as
the *target* phases, longer than any ever as the *best*; stable-mode
decisions take the target phase, and every 1,000·k conflicts the saved
phases are rephased — best, original, best, inverted, best, random, in
turn.

**Inprocessing (`BOXES_INPROCESS=1`, 2026-09-15, off by default —
§10.1).**  Every 10,000
conflicts (the interval growing by 10,000), at a restart and at level 0:
the elimination below is run again over the original clauses under the
current level-0 assignment (learned clauses that mention an eliminated
variable are dropped, the rest survive), then the kept learned clauses
of LBD ≤ 6 are *vivified* (Luo et al. 2017) — the negations of a
clause's literals are assigned one by one with the engine's own
propagation, tables included; a literal found true is implied by those
before it and the clause shrinks to them, one found false is dropped,
a conflict ends the clause early — within 2 M propagations a round,
the saved phases restored afterwards.  Elimination during the search
needs the engine's variables never to be assumed, so it runs only where
`simplify` ran (the CLI); vivification runs in the path search's
completion engine too.

**Preprocessing (2026-09-15).**  `Engine::simplify` is SatELite's
bounded variable elimination on the clauses: after level-0 propagation,
a variable in no table and still unassigned is resolved away when its
resolvents (tautologies dropped, at most 20 literals) are no more than
the clauses they replace, two passes cheapest first; the removed
clauses are kept and a model is extended over the eliminated variables
last-eliminated first.  Table variables are frozen, so it is a pure
clause-side pass — and a variable that will be assumed must not be
eliminated, so the completion engine of the path search does not run
it; `sat -b boxes` does (`BOXES_PREPROCESS=0` to skip).  On the plain
ISCAS circuits it removes 65–70 % of the variables in milliseconds
(§10.1).

## 4. Certification and formal verification — the UNSAT decision must be trustworthy

The requirement is the project's standing one, sharpened: an UNSAT answer
must be checkable **without trusting the solver, the box compiler, the
generated box code, or the cluster**.  The plan has three layers, and only the
smallest is in the trusted computing base (TCB — the code whose bugs could
make us accept a false UNSAT).

### 4.1 The obligation on a box table

Let box `B` have definition `φ_B` and table `T_B` (rows = canonical uncovered
paths of `¬B`, i.e. models, §2.2).  For UNSAT soundness the table must be
**complete**:

```
Complete(B, T_B)  :=  ∀ m ⊨ φ_B,  ∃ r ∈ T_B,  r ⊆ m        (rows in model polarity)
```

Every model of the box must contain some row.  Extra rows (`T_B ⊋ models`)
only make the search slower, never unsound; **missing** rows are what would
let a real model slip past the cover.  So the obligation is one-directional,
and it is the *only* thing that needs to be true about a table for UNSAT.
(The other direction — every row really is a model — matters only for SAT
answers, which are certified anyway by evaluating the model against `F`.)

For a **projected** table (§5.3) the statement is unchanged with rows over the
interface variables: `∀ m ⊨ φ_B, ∃ r, r ⊆ m|_I`.  The internals are
existentially absorbed by quantifying over all models of `φ_B`.

### 4.2 The box certificate is an ordinary UNSAT proof

`Complete(B, T_B)` is equivalent to unsatisfiability of

```
φ_B  ∧  ⋀_{r ∈ T_B} ¬(⋀ r)          ("a model of B that contains no row")
```

which is a plain propositional formula.  So a box's certificate is a
**standard UNSAT proof** of that formula — LRAT (the hint-carrying clausal
proof format checked by `cake_lpr`) or VeriPB — produced once at compile time
by any trusted-checkable solver, and checked by the **same verified checkers
hydra already uses** (`cake_lpr` is itself a CakeML-verified LRAT checker).
No new proof system is needed for boxes, and the box's Rust code never enters
the argument.  For the adder this proof is trivial (256 assignments); for a
projected 4-bit adder it is a small SAT instance.

### 4.3 The composition theorem (to be stated and proved in Lean)

```
Theorem box_cover_sound (F : Formula) (boxes : List Box) (T : Box → Table)
  (h_complete : ∀ B ∈ boxes, Complete B (T B))
  (h_cover    : ∀ p : BoxPath F T, Covered p) :
  ¬ ∃ m, m ⊨ F
```

where a `BoxPath` chooses one row per box instance plus one child at each
structural `Prod` (§2.1), `Covered p := ∃ ℓ, ℓ ∈ p ∧ ¬ℓ ∈ p`, and the row
literals are taken in path polarity.  Proof sketch: a model `m` of `F`
restricts to a model of every `φ_B`, hence (by completeness) contains a row of
every table; those rows together with `m`'s structural choices form a
`BoxPath` all of whose literals are consistent with `m` — an uncovered box
path, contradicting `h_cover`.  This is a short Lean development over finite
literal sets (Mathlib `Finset`), and it is the *entire* meta-theory: the
composed UNSAT proof for a formula with plugged-in boxes is exactly
`{ per-box UNSAT proofs of §4.2 } + { a cover of the box paths }`.

`h_cover` is discharged by a **box-level cover certificate**: the existing
`v3` idea (per-variable position lists whose cross products are the pairs,
[cover_certify.md](cover_certify.md)) with positions extended to
`(instance, row)` for compiled boxes.  Phase 1 may instead **expand** each
box cover to primitive positions (per-box trace paths + static internal cover,
§6.1) and hand today's `sat-cover-verify` a plain primitive cover — a valid,
if larger, instance of the same theorem.

### 4.4 What gets formally verified, and with what

| artifact | tool | why this tool |
|---|---|---|
| `box_cover_sound` and the definitions above | **Lean 4 + Mathlib** | the meta-theorem is finite combinatorics; Lean's kernel is the smallest trust anchor available |
| the executable **box-cover checker** (Rust) | **Verus** | Verus verifies performant, idiomatic Rust (`exec` code against `spec`/`proof` functions) with SMT automation — right for a checker that must scan large covers fast |
| the link between them | **Aeneas** (optional) | translate the Rust checker to Lean and prove it decides exactly the `h_cover` premise, so the whole chain lives in one logic; if Aeneas's Rust subset proves limiting, Verus's own spec, stated to mirror the Lean definitions, is the fallback |
| per-box completeness proofs | `cake_lpr` / VeriPB | already verified / already trusted in hydra |

**Decided (2026-09-06): Verus for the checker, Lean for the theorem, Aeneas as the
optional bridge.**

TCB after this: Lean's kernel, Verus's checker (Z3) or the Aeneas translation,
`cake_lpr`/VeriPB, the certificate and formula parsers, and the operating-system (OS) / application-binary-interface (ABI) glue.
**Untrusted**: the search engine, the jq → formula step, the box compiler,
`rustc`, and every generated plug-in.  That is the de Bruijn discipline the
project already follows with hydra, extended to boxes.

### 4.5 Optional stronger layer: verified propagators

The generated box code (§6) can additionally be verified with Verus against
the table semantics — `propagate` returns only literals implied by every live
row, reports `covered` only when no row is live, and `uncovered_rows`
enumerates exactly the live rows.  This does not shrink the TCB for UNSAT
(certificates already cover that) but it makes the engine's *SAT-side* and
nogood-sharing behaviour trustworthy without per-instance checking, which
matters for the distributed on-the-fly scheme in §8.4.

## 5. The box specifier language — jq

### 5.1 A box is a jq definition

The repository already generates its adder problems from jq: `lib/adder.jq`
defines

```jq
def adder(a;b;c_in;s;c_out;u1;u2;u3):
    prod(
        br(eq(prod(a, b), u1)),
        br(eq(prod(u3, c_in), u2)),
        br(eq(sum(u1, u2), c_out)),
        br(eq(xor(a, b), u3)),
        br(eq(xor(u3, c_in), s))
    );
```

over the `expr.jq` constructors (`prod`, `sum`, `eq`, `xor`, `imp`, `br`,
`vi`), and `/jq` evaluates any filter against a transitively resolved
preamble (`resolve_preamble` over the `# === deps ===` sections) with the
`xq` engine.  A **box is such a `def`**: its **parameters are the interface**,
and any other variable it introduces is **internal**.  The two-equation form
of the same adder, in the same idiom:

```jq
def full_adder(x;y;c_in;s;c_out):
    prod(
        br(eq(sum(prod(x, y), prod(br(xor(x, y)), c_in)), c_out)),
        br(eq(xor(x, y, c_in), s))
    );
# → "(x y + (x ⊕ y) c_in = c_out) (x ⊕ y ⊕ c_in = s)"
```

A `.jq` file exports boxes through one more section, alongside the existing
`deps`/`tests` blocks:

```
# === boxes ===
# full_adder(x;y;c_in;s;c_out)
# adder(a;b;c_in;s;c_out;u1;u2;u3)   expose u1,u2,u3
# === end boxes ===
```

`expose` keeps internals as table columns (§2.4); the default is to project
them out.  **Decided (2026-09-06): both as sketched.**  The `# === tests ===` block gains table-level assertions
(`full_adder | table | length == 8`), and the compiler adds its own check
that the compiled table equals the definition's projection — the check that
produced the result below.

**Generalized declarations** (2026-09-12).  `name(p1;…;pn) [:= <jq expression>]
[negation <jq expression>] [expose f1,f2] [budget cubes=N ms=M]`:

* **Right-hand side.**  With `:=`, the box is the formula produced by the jq
  expression; each parameter is bound to its own name as a zero-arity
  definition while it is evaluated (`def a: "a"; def b: "b"; eq(a;b;4)`), so
  generators take parameters next to literals: `eq4(a;b) := eq(a;b;4)`.
  Without `:=`, the definition is the jq function `name(p1;…;pn)` as before.
* **Parameters are families.**  A parameter `p` binds the variable `p` and
  every `p_<subscript>` the definition generates (`expand::family_of`, longest
  prefix wins, so `c_in` is not a member of `c`).  Table columns are the
  members of each family in subscript order; a call `eq4(x, y)` binds by
  prefix, `a_i → x_i`, a primed argument primes every member, a constant
  applies to every member.  A plain variable is a family of one, which is the
  old behaviour.
* **Hidden by construction.**  Every generated variable that belongs to no
  family is hidden (∃-projected); `expose c` adds the family `c` to the
  interface as a further call parameter after the declared ones.
* **Negation clause** (2026-09-14).  `negation <jq expression>` defines the
  box's negative table directly — evaluated like the definition, over the
  same parameters, and compiled like a positive table (its columns must be
  the definition's).  For a definition whose falsifying branches are too
  many paths to enumerate but whose negation has a definition of its own:
  `le_9(a;b) := le(a; b; 9) negation lt(b; a; 9)` (the definition's own NNF
  has over 3·10⁷ uncovered paths for 511 rows; the complement over 2¹⁸
  assignments gives 130 816 raw rows; the clause gives 511 rows at once).
* **Minimization budget** (2026-09-13).  `budget cubes=N ms=M` overrides,
  per box, the cube budget of the Quine–McCluskey prime enumeration (default
  2,000,000) and the wall-clock budget of the exact cover search (default
  1500 ms); over either, the irredundant heuristic cover is kept.  The box
  popup shows the effective values, the time spent and whether the tables are
  proven minima, and its Recompute button rewrites the clause and recompiles.

**Minimized tables** (2026-09-13).  After canonicalization, rows are minimized
(`compile::minimize_rows`).  Up to 14 columns the result is the true minimum:
Quine–McCluskey prime implicants and an exact cover of the prime-implicant
chart: essential primes and prime dominance at every node, minterm dominance
at the root, component decomposition, a greedy prime cover as the initial
bound, an independent-set lower bound, and branch-and-bound on the least-
covered minterm of the cyclic core, under work budgets (over budget, the best
cover found is kept and reported as irredundant, per table).  Beyond that, or over budget, an irredundant cover by
prime implicants (EXPAND + IRREDUNDANT over the 2^k assignments, k ≤ 20 — the
same cap as the negative table).  Coverage is unchanged; row counts stop
depending on how a definition is spelled (`le` as `lt + eq` and `¬lt(b;a)`
both give the 23-row minimum for 4-bit `a ≤ b`), and fewer, wider rows
propagate faster.

**Compile by composition** (2026-09-13, `compile::compile_box_by_join`).  A
definition that is a conjunction of box calls (and literals) is compiled by
joining the callees' tables — each instantiated over the definition's
variables — one call at a time, projecting every hidden variable as soon as
no later conjunct mentions it, then minimizing the interface columns.  The
expanded matrix is never enumerated, so an n-step unrolling compiles in
milliseconds to a table over its interface only.  That table carries what
per-step propagation cannot: for the 4-bit counter `bmc8_w4(a;c8) :=
bmc_chain_w4(a; "c"; 8)` (bmc.jq) the 256 reachable `(a, c8)` rows make
`c8 ≤ 8` a propagation fact, and `bmc_w4_n8_box` — one call plus `c8 > 8` — is
refuted with zero decisions in ~0.3 ms on the boxes backend, faster than
CaDiCaL's ~0.4 ms on the same formula; the original 17-call form takes
1.4 ms because table propagation is per step and the row engine, having no
learning, enumerates the 2^8 `a`-vectors on every completed path.  Negated or
disjoined calls are not composable and fall back to path enumeration; the
negation table of a composed box comes from the complement.

### 5.2 Compilation pipeline

```
jq def  ──/jq──►  formula text  ──parse──►  abstract syntax tree (AST) with box-call nodes
        ──resolve──►  nested boxes compiled first (deps; cycles reported)
        ──enumerate (existing engine)──►  canonical uncovered paths of ¬B
        ──project internals──►  table T_B      ──§4.2──►  certificate
        ──§6 codegen──►  Rust source  ──rustc──►  plug-in / linked module
```

The formula language gains a **box-call form**, `full_adder(a_0, b_0, c_0,
s_0, c_1)`, parsed as a `Box` node and resolved against the library.  That is
what lets a jq definition **emit box calls in its output** instead of
expanding them:

```jq
def add4(a;b;c_in;s;c_out):
    prod([range(4) | br("full_adder(\(a(.)), \(b(.)), \(carry(.)), \(s(.)), \(carry(.+1)))")]),
    ...  # with carry(0) = c_in, carry(4) = c_out
```

so hierarchy is expressed in jq, resolved by the same dependency machinery,
and compiled bottom-up.

### 5.3 Projection — verified on the engine

Projection drops internal columns and dedups rows, yielding the table of
`∃U1 U2 U3. adder`.  Measured: the 8-row `adder(...)` table projected onto
`{X,Y,C1,Z,C}` is **set-equal** to the canonical table of
`(C = X·Y + (X ⊕ Y)·C1)·(Z = X ⊕ Y ⊕ C1)` — the two-equation adder — as
computed independently by the engine.  (The two-equation complement also has
only 208 paths to the five-equation form's 972, with the same 8 uncovered
canonical rows: a more compact definition is cheaper to *compile*, and the
compiled box is identical either way.)  Projection is sound exactly when the
internals are fresh to the box, which the jq convention guarantees unless
`expose` says otherwise; and the §4.2 certificate covers projected tables
without change.

**What projection does *not* claim.**  `adder ⇔ full_adder` — the
five-equation form *equivalent to* the two-equation form over all eight
variables — is **not** valid, and a SAT solver correctly rejects it: the
two-equation form says nothing about `U1,U2,U3`, so it has 64 models to the
five-equation form's 8 (every interface row × 2³ free internals), and the
engine finds 86 uncovered (falsifying) paths, e.g. `X=Y=C1=1, Z=C=1, U1=0`,
where the two-equation form holds but `U1 = X·Y` fails.  The statement that
*is* true is the quantified one, `(∃U1 U2 U3. adder) ⇔ full_adder`, and it is
checked propositionally as two valid implications:

- **completeness** — `adder ⇒ full_adder`: every model of the box, restricted
  to the interface, is a row (0 uncovered paths);
- **soundness** — `full_adder ⇒ adder[U1 := X·Y, U3 := X ⊕ Y, U2 := U3·C1]`:
  every row extends to a model, with the definitions as the witnesses.  The substitution is done by unfolding each internal's defining
  equation in dependency order (`U1`, `U3`, then `U2 := U3·C1` becomes
  `(X ⊕ Y)·C1`), which turns the three definitional equations into
  tautologies and leaves `full_adder`.  In jq it is just a **call with the
  definitions as the internal parameters** —
  `adder("X";"Y";"C1";"Z";"C"; "(X Y)"; "((X ⊕ Y) C1)"; "(X ⊕ Y)")` —
  the payoff of internals-as-parameters (verified: the generated formula
  makes the implication valid, and the combined
  `(adder ⇒ full_adder) (full_adder ⇒ adder[U := defs])` is valid with
  0 uncovered paths).

The first is exactly the §4.1 obligation a projected table must certify; the
second is what the compiler's self-check (set equality of the interface
tables) adds on top.  Neither direction is the bare equivalence, and the
converse `full_adder ⇒ adder` is not valid.

**When the checks are trivial, and when they are not.**  For a *purely
definitional* box — every equation defines one variable, acyclically, as the
adder's five do — `B[U := defs]` minus its tautologies *is* the projected
formula by construction (`FA` is literally "the output definitions with the
internals unfolded"), so both implications are rewrites up to `a = b` ↔
`b = a` and associative regrouping, and `∃U. B ≡ P` is a **syntactic** fact
the compiler can take as a fast path (unfold, drop tautologies, normalize
orientation and associativity, compare).  The implications carry real
content only when `P` is *not* the literal unfolding: a hand-written
interface specification, a formula recovered from a projected *table*, or a
box with a constraint that is not a definition — e.g. `adder ∧ (Z ⇒ C)`, for
which `full_adder ⇒ B[U := defs]` fails (the constraint is missing from
`P`) and the right projection is `full_adder ∧ (Z ⇒ C)`.  `faulty_adder`'s
`d_i ⇒ (equation)` guards are the same situation in the library today.

## 6. Boxes compile to Rust — not tables interpreted at run time

### 6.1 What the generator emits

For a box over `n` interface variables the compiler emits a Rust module
implementing the `Box_` trait (§3.1) with everything specialized:

- **Propagation as a lookup table (LUT).**  The current partial assignment
  restricted to the box is a 3-valued vector (unassigned/true/false) — `3^n`
  states.  For `n ≤ 10` the generator precomputes, per state, the
  forced-literal mask and the covered flag: 243 entries for the 5-variable
  adder, 6 561 for the 8-variable one.  Propagation is one table lookup.
- **Otherwise, per-literal row masks as constants** (`const ROWS_WITH_X_POS:
  u64 = 0b…`): live rows = AND of the masks of the prefix's literals;
  forced literals = literals present in every live row (AND over rows, or a
  second small table); all branchless, all `#[inline]`.
- **`uncovered_rows`** iterates the live mask; **`explain`** (for nogoods,
  §3.5) returns, per dead row, the prefix literal that killed it — also a
  constant table.
- **Per-box static data** used by certificates: trace paths and the static
  internal cover, emitted as data next to the code.

This is the classic specialization step: the table interpreter of §3
partially evaluated on a fixed table *is* this generated code.

### 6.2 Two delivery modes

**Decided (2026-09-06): plug-ins first; the specialized-solver build follows once
the plug-in path is proven.**

| mode | mechanism | when |
|---|---|---|
| **plug-in** | each box (or box family) is a generated crate built as a `cdylib` behind a versioned C ABI (a vtable of `extern "C"` function pointers — Rust-to-Rust ABI is not stable) and loaded with `libloading` | the core solver stays fixed; boxes arrive per problem; interactive use |
| **specialized solver** | the generated modules are linked into a per-problem binary; bitset width fixed by `const W: usize` from the problem's variable count; full inlining and link-time optimization (LTO) | batch/cloud runs where a per-problem build is amortized over hours of solving |

Both key their artifacts by a content hash of the definition, so a box is
compiled once and reused across problems and machines (the library lives in
object storage for the cluster, §8).  Because compile latency is seconds, the
interactive path is **two-tier**: the §3 table interpreter runs immediately
while the compiled box builds in the background and is hot-swapped in.

### 6.3 Safety at the boundary

A dynamically loaded plug-in is native code; the engine treats it as
untrusted for correctness (§4) and as trusted only for memory safety, the way
any `cdylib` is.  Mitigations: the plug-in is generated by *our* compiler from
a checked table (no hand-written unsafe code crosses the boundary), the ABI is
versioned and validated at load, and the specialized-solver mode has no
boundary at all.

## 7. Multi-core parallelism

Unchanged in structure from the first draft — prefix-partitioned work units
over the row search, work stealing via rayon/`crossbeam-deque`, shared
read-only tables and arena, a **deterministic mode** for benchmarks, and
mergeable covers — with one promotion: **nogood sharing between workers is
built in from the start** (a batched, append-only pool, imported at decision
boundaries), because §8's evidence says sharing is where scale comes from.
It remains switchable, and §10's A/B decides whether it stays on.

## 8. Distributed execution — informed by Mallob

### 8.1 What Mallob established

Mallob (Schreiber & Sanders, Karlsruhe Institute of Technology — KIT) is the repeated winner of the SAT
Competition's cloud track.  Its design points that matter here:

- **Malleable scheduling.**  Many jobs share a cluster; each job's worker
  allocation grows and shrinks at run time, and cores are rebalanced in
  milliseconds.  Utilization, not per-job speed, is what makes cloud SAT
  affordable.
- **Job trees.**  A job's processes form a binary tree; clause exchange is a
  periodic aggregate-up / broadcast-down over that tree with bounded buffers,
  so communication scales logarithmically.
- **Diversified portfolio + clause sharing**, not pure partitioning.  Every
  process searches the whole problem (differently seeded/configured CDCL
  solvers) and they exchange filtered learned clauses (by size, literal block
  distance (LBD), and deduplication).  Their measurements show this scales
  better than cube-and-conquer partitioning on most instances: partitioning
  suffers load imbalance and throws away learning at the cut.
- **Certification.**  First (Michaelson, Schreiber, Heule, Kiesl-Reiter,
  Whalen, TACAS 2023 — Tools and Algorithms for the Construction and Analysis of Systems) by tracking clause identifiers (IDs) across solvers and reconstructing
  a single LRAT proof — correct but heavy.  Then (Schreiber, SAT 2024)
  **on-the-fly trusted checking**: every solver process is paired with a
  small trusted checker that validates each learned clause from hints as it
  is produced; clauses that cross process boundaries carry a message
  authentication code (MAC) from the producing checker, so the importing
  checker accepts them without re-derivation; UNSAT is trusted the moment a
  checker validates the empty clause.  No monolithic proof is ever written.

### 8.2 What changes in this design

- **Sharing is the primary scaling mechanism; partitioning is secondary.**
  The default distributed mode is a Mallob-style job tree of engines that each
  search the whole box matrix with diversified branching (different box
  orders, row orders, seeds) and exchange **nogoods** (§3.5) with the same
  filtering discipline.  Prefix partitioning (the first draft's only
  mechanism) is kept for two jobs it does well: giving the *cover*
  certificate a clean tree structure, and spanning high-latency boundaries
  (regions, spot fleets) where sharing would starve.
- **Interconnect.**  Clause sharing at Mallob rates wants a low-latency
  fabric: EC2 (Elastic Compute Cloud) instances in a cluster placement group with EFA (Elastic
  Fabric Adapter) running MPI (Message Passing Interface), or AWS (Amazon Web Services)
  ParallelCluster — not SQS (Simple Queue Service).  The queue-based layer of the first draft
  (SQS/S3 (Simple Storage Service)/DynamoDB) remains the *outer* tier that hands whole prefixes to
  such clusters and collects results.  **Decided (2026-09-06): AWS ParallelCluster with
  EFA is the M7 substrate.**
- **Malleable coordinator.**  The coordinator becomes a scheduler in
  Mallob's sense: it admits many jobs, assigns each a dynamic share of the
  fleet, rebalances on arrivals/completions, and drives spot capacity up and
  down against a dollar cap.  Mallob's JSON (JavaScript Object Notation) job
  API (application programming interface) — submit, incremental, cancel, query
  — is the template for the service surface.

### 8.3 Certification, distributed

Adopt the on-the-fly model rather than assembling a global cover:

- each engine process is paired with a **trusted checker** running the
  Verus-verified cover/nogood checker (§4.4) in incremental mode: every cover
  pair and every learned nogood is validated from its hints as produced;
- a nogood that is shared carries its checker's MAC; the importing checker
  accepts a signed nogood without re-deriving it;
- UNSAT is trusted when some checker validates that the box-path space is
  covered (in nogood terms: derives the empty nogood);
- the per-box completeness certificates (§4.2) are validated once, at
  library load, by every checker.

A monolithic assembled cover (the first draft's assembly scheme) remains available as an
**offline audit artifact** — Mallob's TACAS-2023 route — when a proof must be
archived, at the cost that paper measured.

### 8.4 Budget and failure

Unchanged: per-unit budgets, `SPLIT` on overrun for the partitioned tier,
idempotent units, retries, a global wall-clock/dollar cap, and *what was
proved* reported on timeout.  With sharing, a worker loss loses no proof
state — validated nogoods already imported elsewhere survive — which is the
fault-tolerance argument Mallob makes and we inherit.

## 9. Integration with the existing code

| seam | change |
|---|---|
| `lib/*.jq`, `resolve_preamble`, `/jq` (`web_app.rs`) | box sources; new `# === boxes ===` section; compiler calls `/jq`-equivalent in-process |
| `src/formula.rs` parser | box-call node `name(v1, …)` |
| `src/bin/sat.rs` `MatrixBackend` | new variant `Boxes` (`matrix.boxes`), same `-b`/`--emit-cover` plumbing as `eff_cover` |
| `src/controller/mod.rs` `PathSearchController` | box engine as a controller for structural sub-trees; mixed matrices reuse `classify_paths_with_arena` |
| `src/dual/effective_count.rs` | lifted count = live-row popcount |
| `src/controller/cdcl.rs` `emit_static_cover` | reused per box at compile time |
| new `src/boxes/` | `row.rs`, `table.rs`, `engine.rs`, `compile.rs` (jq→table→cert), `codegen.rs` (Rust emitter), `plugin.rs` (`libloading`, versioned ABI), `library.rs`, `par.rs`, `dist/` |
| new `verify/` | Lean project (`box_cover_sound`), Verus checker crate, Aeneas bridge |
| `Cargo.toml` | `libloading`; generated crates use `crate-type = ["cdylib"]` |
| `src/bin/sat_cover_verify.rs` | unchanged in phase 1; `v4` `(instance,row)` positions later |
| `src/bin/web_app.rs` `/paths` | compiled rows served as canonical paths with trace positions (the UI's canonical tree/highlighting work as-is) |
| `tools/gbd/run_benchmark.py` | `-b boxes`, existing soundness gates |
| hydra dispatch (`cook_pbp::detect_shape` family) | later: circuit detector routing to `boxes` |

## 10. Phased plan, with gates

| phase | build | gate |
|---|---|---|
| **M0** (done) | 972/13/8 verified; table extracted; projection `∃U.adder ≡` two-equation adder verified as set equality | ✓ |
| **M1** core | bitset rows, table + structural boxes, DPLL-over-rows with table propagation, single core; `# === boxes ===` + box-call syntax; interpreted tables | same verdicts as `eff`/`cdcl` on the UI adder examples and the test corpus; every UNSAT certifies via the expanded primitive cover |
| **M2** certificates | per-box completeness proofs via `cake_lpr`/VeriPB; box-level `v4` cover format; unverified checker | known-value gate: pigeonhole-principle (PHP)/RoundRobin corpus and the adder examples all check; a deliberately corrupted table is rejected |
| **M3** formalization | Lean `box_cover_sound`; Verus checker; Aeneas bridge attempted | checker verified; the Lean theorem's premises match the checker's spec by inspection or translation |
| **M4** codegen | LUT/mask propagators, `cdylib` plug-ins via `libloading` **first**, content-hash cache, two-tier hot-swap; specialized-solver mode afterwards | compiled boxes byte-identical in behaviour to interpreted ones on the corpus; measured speedup per propagation |
| **M5** multi-core | work stealing + built-in nogood sharing, deterministic mode | ≥ 8× on 12 cores on a multiplier instance; deterministic certificates byte-identical |
| **M6** measure | equal-wall-clock A/B vs `eff`, `cdcl`, `cadical`, `hydra` on adders, multipliers, the CLP(B) (constraint logic programming over Booleans) examples, with user-supplied boxes | the honest question: a certified win on the circuit slice? |
| **M7** distributed | Mallob-style job tree + sharing on **AWS ParallelCluster with EFA**; malleable coordinator; on-the-fly trusted checkers with MACs; queue tier for prefixes | a multi-hour instance solved across N spot workers, UNSAT trusted by the checkers, cost within cap |
| **M8** detection | gate/adder/multiplier detector into hydra | competition CNF routed and certified — lower priority now that users supply boxes |

M6 decides whether M7–M8 are built.

### 10.1 Status (2026-09-06): M1 delivered

**Built.**  `logic::boxes` — table boxes (canonical rows in model polarity,
per-literal row masks), DPLL over rows with table propagation (dead box →
backtrack, forced literals by subset test), iterative search with a decision
budget; `sat -b boxes [--boxes instances.json]`; `box-compile` (from a bare
formula, or from a jq library's `# === boxes ===` declarations with
`--lib adder.jq --box full_adder | --all`); `logic::jqlib` — the `.jq`
section/preamble machinery extracted from `web_app` (which now uses it) plus
`run_filter`, the box-declaration parser and `box_formula`; `lib/adder.jq`
gained the two-equation `full_adder` and declares both it and `adder` as
boxes; `tools/boxes_verdict_check.py` and `tools/gen_adder_boxes.py`.  **Dynamic boxes in the web app** (2026-09-07): boxes are a section of a jq
library like `deps` and `tests` — the `# === boxes ===` block is split out on
load (`JqLibEntry.boxes`) and re-attached on save — and they **follow the
library lifecycle**: compiled when a library is loaded and whenever it is
saved (`compile_lib_boxes`, replacing that library's entries in the in-memory
store, with per-box statuses returned in the load/save responses), dropped on
unload.  The editor popup has a *Boxes* section: one editable declaration per
line with its status (✓ rows / ✗ error), add/remove; a malformed declaration
is rejected on save before anything is written.  `GET /boxes` lists the
compiled boxes (shown as chips in the jq panel), `GET|DELETE
/boxes/table?name=` fetches or drops one, and `POST /boxes/compile` remains as
the scripted entry point (`save` writes the CLI table format to `boxes/`).
The compiler itself lives in the library (`logic::boxes::compile`, shared
with `box-compile` and `sat --boxes`).

**Gates met.**
- Unit tests: trivial CNFs, pigeonhole, 300 random 3-SAT instances against
  brute force, and the compiled adder box (fixed inputs propagate the whole
  cell with 0 decisions).  Full library suite: 338 passed, 0 failed.
- Corpus (`evo/curated_struct_eff.jsonl`, ≤1000 clauses, 30 s each):
  **26 agree, 0 disagree**, 22 unfinished — pigeonhole, Urquhart/`x1`,`x2`
  parity, `mod2`, 3-colouring, SMT benches — the families a learning-free
  DPLL is expected to lose (that is M5's job).  Soundness held on everything
  that finished.
- Adder problems (`gen_adder_boxes.py`, k = 8/16/32; fixed and free inputs;
  SAT and UNSAT): fully expanded CNF, residual + compiled `full_adder`
  instances, and residual + exposed-internals `adder` instances all agree
  with cadical.  Fixed inputs: 0 decisions either way, but the boxed form
  propagates less (k=32: 129 vs 223 propagations — one step per cell instead
  of per gate); free inputs (k=16, SAT): 15 decisions / 30 propagations
  boxed vs 16 / 97 expanded.
- `box-compile`: `full_adder` 12 uncovered paths → 8 rows over the
  5-variable interface; `adder` 13 → 8 rows over its 8 parameters; the
  library-compiled table equals the formula-compiled one.

**Box calls in the formula language** (2026-09-07): `name(a1, a2, …)` or
`name(a1; a2; …)` refers to a compiled box (`logic::boxes::expand`, mirrored
in `formula.jsx` so the live parser and the server agree).  A call is
recognised whenever the parenthesised text is an argument list — names and
constants separated by `,` or `;`, or empty; `A(B+C)` and `A (B)` keep
meaning AND.  Inside an argument list a comma continues a name only within a
numeric subscript (`d_0,1`).  An **unknown box or a wrong argument count is
an error** — immediately in the UI, and from every formula endpoint
(`/valid`, `/satisfiable`, `/paths`, `/cadical/*`, `/simplify`, plus
`POST /expand`).  This includes the one-argument form `name(x)`: until
2026-09-13 an unknown one-argument name fell back to juxtaposition
(`name · x`), and `v_eq_0_4(c0)` inside a definition compiled with
`math.jq` not loaded silently became two free variables, hidden by
construction — a wrong table (`bmc8_w4` SAT at `c8 = 12`).  The error names
the library that declares the box when the server can tell (declared in a
library on disk that is not loaded / a dependency; declared in a loaded
library whose compile failed, with that error; declared later in the same
boxes block).  A known box expands to its definition with the arguments
substituted (primes compose; `0`/`1` constants allowed) and its projected
internals renamed `<v>__<k>` per call site (the ∃ of §2.4), recursively for
hierarchical boxes, so every existing backend and the diagram work on the
expansion; unloading a library turns its calls back into errors.

**Libraries, dependencies and recompilation** (2026-09-13): a library's
boxes are compiled *after* the boxes of the libraries in its `# === deps ===`
block, transitively (`jqlib::resolve_lib_order`), and a dependency's boxes
are available whether or not it is loaded — read from `lib/` on disk exactly
as its jq definitions are for the preamble — so `bmc.jq` (deps: `math.jq`)
compiles `bmc8_w4` by composition over `v_eq_0_4` in any load order.  The
server keeps, per compiled library, a key over its deps list, jq content,
box declarations and its dependencies' keys (`web_app::lib_key`,
"make"-style): a load, save or unload recompiles exactly the libraries whose
key changed — the edited one and every loaded library that depends on it,
in dependency order — and leaves the rest (the exact-minimisation budgets
make `math.jq` ~1.6 s).  Before compiling, it drops the boxes of every
library outside the loaded libraries' dependency closure, so a dependency's
boxes come and go with its dependants (unload `bmc.jq` and `math.jq`'s
boxes go too, unless `math.jq` is loaded itself or another loaded library
needs it; drop `math.jq` from `bmc.jq`'s deps and its boxes go before
`bmc.jq` recompiles — no definition compiles against a table that is about
to disappear).  A box's right-hand side may use any loaded library's jq
definitions, but a definition can only *call* boxes of its library's
dependency closure (and earlier declarations of its own block) — the error
names the library and says to list it in the deps block — because only
declared deps trigger recompilation.  `GET /boxes`
also lists the declarations that failed (`failed: [{name, lib, error}]`),
and the UI keeps those statuses across page reloads.

**`boxes` backend in the web app** (2026-09-07): the default backend-selector
option for Valid? / Satisfiable? (a formula without box calls runs greedy×eff
as before), *matrix-native*: the ordinary path search
(`SmartController`) runs on the collapsed NNF where every box call is an atom
(`BOXCALL_k`, `expand::atomize_box_calls`), wrapped in
`boxes::controller::BoxAwareController`, which adds table propagation to any
`PathSearchController` through `should_continue_on_prefix`: at every prefix
step each call whose atom is fixed on the prefix must keep a row consistent
with the prefix (bit-parallel row masks — the "dead box → backtrack" rule of
§3), and when a path completes the rows of all fixed calls must be jointly
consistent with it (row engine over the path's literals as units), so an
uncovered path is always a genuine model and the run stops at the first one.
No CNF, no Tseitin, no auxiliary variables — only the CaDiCaL backend
Tseitin-encodes; positions, covers and certificates keep their meaning.  The
polarity rule: a path literal is FALSE in the model it stands for, so `atom'`
on a prefix means the call holds (rows of B) and `atom` that it fails (rows of
¬B).  These runs skip preprocessing (unit propagation could fix an atom before
the search sees it).  The drainer appends to each reported path the values of
the call arguments that are not on the path, from the tables' witness.

Both polarities of every box are compiled at library load: the negative table
from the definition's own NNF when nothing is projected
(`compile_box_polarity`), else the complement of the projected table
(¬∃U.B = ∀U.¬B — compiling ¬B and projecting would be wrong).  Definitions may
call boxes declared earlier (expanded before compiling).

**Box aware** (checkbox after the backend selector, on by default, active
with the `boxes` backend): each call is one unit for Valid?, Satisfiable?
and Paths, drawn as one rectangle labelled `name(args)`; Paths enumerates
the paths of the collapsed matrix with the same `BoxAwareController` around the paths
controller (the client parses the same atomized text, so path positions line
up): prefixes the tables refute are pruned during the search, so only paths
that extend to real models are reported.  Example:
`full_adder(x,y,c_in,s,c_out) (s = c_out)` — 2 collapsed uncovered paths of
the complement vs 5 expanded.

**Learning (M5, 2026-09-13)** — the completion engine
(`boxes::Engine`) is conflict-driven: a box with no live row, or a literal a
box forces, is *explained* lazily from the kill masks (the assigned literals
of the box, oldest levels first, whose kill masks cover the rows that had to
die — the lazy-clause-generation explanation of §3.5), then 1-UIP analysis,
backjumping, learned clauses propagated with two watched literals, VSIDS over a
binary heap of the unassigned variables (ties to the lower variable),
phase saving and restarts (Luby, or Glucose's dynamic ones with stable
phases and trail reuse, §3.5) are the textbook ones, and the learned
clause is minimised (§3.5); the CLI runs bounded variable elimination
first (§3.5).  Inprocessing rounds and target phases exist behind
switches and are off (§3.5, §10.1).  A call whose
tables are tiny (≤ 8 rows, negation ≤ 4 rows) goes into the engine in
**clause form** — `atom ⇒ B` is one clause per row of ¬B, `¬atom ⇒ ¬B` one
per row of B — the same constraint, but propagated by watched literals
(visited only when a watched literal is falsified) instead of live-row masks
(visited at every assignment of any of its variables); larger tables keep
the mask form, whose propagation is stronger.  `solve_under` takes its units
as assumptions, one decision level each, so the clauses learned during one
path's check hold for the next.  One invariant the explanations rest on:
the live-row masks reflect the *whole* trail, so a table added after
level-0 units (the CLI and the witness check build the engine from the
clauses first) is narrowed by the current assignment as it is added — a
table that looks alive with all its rows dead surfaces its conflict
levels later with no literal of the current level, which once meant a
panic in the trail walk or a model violating the table; `search` also
starts analysis at the conflict's own level when that is below the
current one.  Also: the path search's prefix check is
incremental (only the calls touched by literals beyond the common prefix
with the previous one — "some row survives" is monotone), and the witness
reuses the completion engine's model instead of solving again.

**Explanation minimisation (2026-09-15).**  The three explanation modes
of §3.5 on the instances where the engine terminates — the ISCAS cones
and the two competition instances of `doc/box_candidates_satcomp.md`,
and the box-native benchmarks below — same machine, one core each, the
three modes run concurrently (conflicts are deterministic, times
indicative):

| instance | greedy (trail order) | minimal | cover (default) |
|---|---|---|---|
| belpyramid c3540, cones K = 8 (UNSAT) | 247 K conflicts, 6.0 s | 150 K, 3.0 s | 151 K, 3.1 s |
| c3540, K = 12 | 250 K, 6.2 s | 149 K, 3.6 s | 153 K, 3.1 s |
| c5315, K = 8 | 59 K, 1.5 s | 56 K, 1.2 s | 44 K, 0.96 s |
| c5315, K = 12 | 54 K, 1.5 s | 55 K, 1.1 s | 56 K, 1.2 s |
| toughsat_factoring_895s, K = 12 (SAT; CaDiCaL 205 s) | 1.32 M, 146 s | > 300 s | 301 K, 32 s |
| pyhala-braun-sat, K = 8 (SAT; CaDiCaL 5.8 s) | 634 K, 191 s | 1.17 M, 314 s | 182 K, 49 s |
| — literals per explanation there | 4.93 | 3.99 | 2.19 |
| SLP sun56[0,5,7] k = 7 (UNSAT) | 6.7 s | 1.5 s | 1.2 s |
| SLP sun56[0,5,7] k = 8 (SAT) | 50.9 s | 0.02 s | 0.03 s |
| SLP cn120[0,6,8] k = 8 (SAT) | 50.0 s | 5.3 s | 0.48 s |
| matmul rank 6 + symmetry (UNSAT) | 3.5 s | 1.9 s | 1.7 s |
| matmul rank 7 (SAT) | 23.7 s | 22.8 s | 4.6 s |
| waerden w4_ap(35), w5_ap(177), w5_ap(178) | unchanged | unchanged | unchanged |

Two effects.  Minimality alone (`minimal`) removes the redundant old
literals the trail order keeps — the ISCAS conflicts fall by 40 % on
c3540 and the K = 8 cones now beat the plain CNF in time — but on wide
tables (K = 12 cones, the half-adder cells of pyhala-braun, the
9-column `orb` boxes of SLP) the trail order still lands on long covers,
and there choosing by coverage (`cover`) is what finds the 2–3-literal
explanations: toughsat K = 12 goes from 146 s to 32 s (the first
competition instance the engine solves faster than CaDiCaL), pyhala-braun
from 191 s to 49 s, the SLP SAT rows from tens of seconds to well under
one.  Explanations cost more each (every pick scans the candidates) but
there are fewer of them per conflict, and the count of conflicts is what
moves.  Waerden is unchanged: a progression box's explanation is its
three assigned literals whichever way it is chosen.  Not tried: the
exact minimum-cardinality hitting set (a subset search per explanation is
too much at 10⁷ explanations a minute) and explanation-only gate clauses.
Rerun one process at a time with `cover` as the default: c3540 cones
K = 8 3.3 s (plain CNF 2.9 s), c5315 1.0 s (plain 2.2 s), toughsat
K = 12 26 s (model verified; CaDiCaL 205 s), pyhala-braun-sat K = 8
42 s, w5_ap(178) 283 s against 300 s with the trail order (today's
engine; the 186 s of 2026-09-14 was the engine before the live-row fix),
and the SLP window table of `doc/matmul_cxlb_satcomp.md` is re-measured
there: the box engine is now at or below CaDiCaL on every satisfiable
row it finishes.

**Decision heap and learned-clause minimisation (2026-09-15).**  The
VSIDS decision was a scan of every variable; it is a binary heap now
with the same tie order, so with minimisation off the searches are the
runs above, only faster (c3540 K = 8 cones 3.3 → 2.9 s, plain 2.9 →
2.7 s; the 366 K-variable sum-of-3-cubes instance from a crawl to 16 K
decisions a second).  The 1-UIP clause is then minimised (§3.5) over the
lazy explanations, cached per assignment — without the cache the
redundancy probes quadrupled the explanation computations and halved the
conflict rate on the toughsat cones.  Minimisation off → on, the heap in
both, three processes sharing the machine:

| instance | minimisation off | on |
|---|---|---|
| c3540 plain CNF (UNSAT) | 123 K conflicts, 2.7 s, 107 literals per learned clause | 91 K, 1.9 s, 20 literals |
| c3540 cones K = 8 | 151 K, 2.9 s, 66 | 106 K, 2.0 s, 16 |
| c5315 plain CNF | 87 K, 1.5 s, 68 | 50 K, 0.76 s, 14 |
| c5315 cones K = 8 | 44 K, 0.51 s, 26 | 37 K, 0.45 s, 15 |
| toughsat K = 12 (SAT) | SAT 30 s, 301 K | > 300 s, 2.1 M |
| pyhala-braun-sat K = 8 | SAT 43 s, 182 K, 454 | SAT 70 s, 222 K, 34 |
| pyhala-braun-sat plain CNF | SAT 408 s (before the heap) | SAT 204 s, 1.5 M |
| matmul rank 6 + symmetry (UNSAT), boxes / chain | 1.7 s / 1.6 s | 2.5 s / 1.0 s |
| SLP window refutations (five rows) | 0.47–2.5 s | 0.40–1.3 s |
| w5_ap(177) SAT / w5_ap(178) UNSAT | 2.1 s / 283 s | 0.58 s / 315 s |

Circuit refutations gain 25–45 % (the clauses shrink 2–13×); the
box-native benchmarks move within ±10 % either way, except matmul's
rank-6 refutation (+45 %) and its chain form (−40 %); the satisfiable
competition instances lose their trajectory (toughsat) or 22 % more
conflicts (pyhala-braun).  On by default, `BOXES_MINIMIZE=0` for the
CLI and the server.  On the quiet machine with everything on, the SLP
window table of `doc/matmul_cxlb_satcomp.md`: 2–6× slower than CaDiCaL
on the refutations, 3–28× faster on six satisfiable rows and 7–14×
slower on three, and the weight-7 window sun56[1,2,4] at k = 15 now
solved in 23 s where CaDiCaL takes 58 s.

**Restarts and preprocessing (2026-09-15).**  The three
configurations — the engine above (Luby restarts, no preprocessing),
with bounded variable elimination, and with elimination and Glucose
restarts — on the same rows, two or three processes sharing the
machine; the box-native rows from two servers run concurrently:

| instance | Luby, no preprocessing | + elimination, Luby | + elimination, Glucose |
|---|---|---|---|
| c3540 plain CNF (UNSAT; CaDiCaL 0.50 s) | 91 K conflicts, 1.7 s | 1,483 of 2,163 variables gone, 116 K, 1.3 s | 128 K, 1.4 s |
| c5315 plain CNF (UNSAT; CaDiCaL 0.15 s) | 50 K, 0.67 s | 2,755 of 3,801 gone, 28 K, 0.20 s | 32 K, 0.22 s |
| c3540 cones K = 8 / 12 | 1.8 s / 2.5 s | 2.3 s / 2.6 s (56 gone) | 2.1 s / 2.5 s |
| c5315 cones K = 8 / 12 | 0.40 s / 0.75 s | 0.44 s / 0.46 s (256 / 229 gone) | 0.31 s / 0.27 s |
| toughsat plain CNF (SAT; CaDiCaL 205 s) | > 300 s | SAT 78 s (4 gone) | SAT 132 s |
| toughsat cones K = 12 | > 300 s | > 300 s | SAT 235 s |
| pyhala-braun-sat plain CNF (SAT; CaDiCaL 5.8 s) | SAT 221 s | SAT 250 s (3,262 gone) | SAT 103 s |
| pyhala-braun-sat cones K = 8 | SAT 65 s | SAT 65 s (nothing to eliminate) | SAT 142 s |
| pyhala-braun-unsat cones K = 8 (CaDiCaL 53 s) | > 600 s | > 600 s | > 600 s |
| w5_ap(178) (UNSAT; CaDiCaL 9.6 s) | 394 s | — | **64 s** |
| w5_ap(177) (SAT) | 0.64 s | — | 0.074 s |
| matmul rank 6 + symmetry (UNSAT), boxes / chain | 2.9 s / 1.1 s | — | 5.2 s / 1.6 s |
| matmul rank 7, chain / boxes / boxes + symmetry (SAT) | 0.11 s / 5.0 s / 30 s | — | 0.07 s / > 120 s / 19 s |
| SLP window refutations, five rows | 0.40–1.3 s | — | 0.33–2.2 s |

Elimination is the plain-circuit win it is everywhere: 65–70 % of the
ISCAS variables go in 5 ms, c5315 runs 3.4× faster and lands 30 %
behind CaDiCaL, c3540 2.6× behind; it does nothing on the cones (their
variables are in tables) and little on the multipliers (the adder
variables occur too often; nothing on the pyhala cones, 10 % of the
plain CNF).  Glucose restarts are a structural win on van der Waerden —
6× on the refutation and 9× on the satisfiable side at equal load — and
find the toughsat K = 12 model and halve pyhala-braun-sat on the plain
CNF (103 s), at the price of 1.5–1.8× on the matmul refutations and 2×
on the pyhala-braun cones; the ISCAS refutations move within ±30 %
either way.  Glucose is the default (`BOXES_RESTART=luby`
keeps the other), elimination is on in the CLI.  On the quiet machine
with the defaults: w5_ap(178) refuted in 59 s (283 s under Luby), and
the SLP window table of `doc/matmul_cxlb_satcomp.md` re-measured —
1.4–6× behind CaDiCaL on the refutations, 2–25× ahead on eight
satisfiable rows and 13–17× behind on three, the weight-7 window's
k = 15 solve (23 s under Luby) lost within 60 s.

**Target phases and inprocessing (2026-09-15).**  Both implemented as
§3.5 describes and measured in the four combinations against the
engine above (Glucose restarts, elimination in the CLI), the box-native
rows on four servers running concurrently, the CLI rows two at a time:

| instance | neither | target phases | inprocessing | both |
|---|---|---|---|---|
| w5_ap(178) (UNSAT) | 71 s | 197 s | 95 s | 78 s |
| w5_ap(177) (SAT) | 0.08 s | 2.2 s | 0.08 s | 0.63 s |
| matmul rank 6 + symmetry, boxes / chain (UNSAT) | 5.6 / 1.7 s | 2.8 / 2.4 s | 2.9 / 5.5 s | 5.6 / 5.5 s |
| matmul rank 7, chain / boxes (SAT) | 0.07 s / > 60 s | 0.24 s / > 60 s | 0.07 s / 52 s | 0.24 s / > 60 s |
| the five SLP window refutations together | 5.3 s | 7.0 s | 6.3 s | 6.9 s |
| c3540 plain / cones K = 8 (UNSAT) | 1.6 / 2.4 s | 1.7 / 2.8 s | 1.7 / 2.5 s | 1.6 / 2.8 s |
| c5315 plain / cones K = 8 (UNSAT) | 0.25 / 0.36 s | 0.23 / 0.35 s | 0.32 / 0.49 s | 0.32 / 0.67 s |
| toughsat plain CNF (SAT) | 158 s | 39 s | 17 s | 40 s |
| toughsat cones K = 12 (SAT) | 252 s | 24 s | > 300 s | > 300 s |
| pyhala-braun-sat plain CNF (SAT) | 122 s | 161 s | 217 s | 163 s |
| pyhala-braun-sat cones K = 8 (SAT) | 157 s | 103 s | 310 s | 94 s |

Neither pays on this set.  Target phases cost the refutations — the
waerden one 2.8×, the SLP ones 33 % together — and move the satisfiable
rows both ways (toughsat 4–10× faster, w5_ap(177) 30× slower); without
CaDiCaL's local-search rephasing ("walk") the target/best/random cycle
mostly perturbs.  Inprocessing works as intended — vivification takes
3–4 literals off each of thousands of kept clauses per run (c3540:
7,385 clauses, −27,955 literals in four rounds; re-elimination finds
4–35 more variables) — but the rounds cost more than the shorter
clauses return at these run lengths: refutations 20–30 % slower on the
box-native rows, ±10 % on the circuits, the long satisfiable rows
again both ways (it does raise the conflict rate where nothing is
decided — the 33 K-variable sum-of-3-cubes instance makes 472 K
conflicts in 60 s against 368 K, the vivified clauses propagating
faster).  Both stay behind their switches, off; the paper's window
table and the numbers above stand.

**The w(5;5) family, boxes against CaDiCaL (2026-09-15).**  Through
the web app's `/satisfiable` (boxed form `w5_ap(n)`, one `ap5` box per
progression) and `/cadical/sat` (the same boxed formula, and the plain
clause form `w(5;5;n)`, which CaDiCaL solves in identical time — the
endpoint expands the boxes to the same clauses); the engine's defaults
(cover explanations, heap, minimisation, Glucose restarts):

| n | boxes `w5_ap(n)` | CaDiCaL `w5_ap(n)` | CaDiCaL `w(5;5;n)` |
|---|---|---|---|
| 150–176 (SAT) | 0.010–0.014 s | 0.005–0.008 s | 0.005–0.008 s |
| 177 (SAT, the last satisfiable size) | **0.066 s** | 1.22 s | 1.22 s |
| 178 (UNSAT, w(5;5) = 178) | 56 s | 9.7 s | 9.7 s |

and w(4;4;n) for n = 30–35 in a millisecond on both.  Every satisfiable
size but the boundary is trivial for both engines, so the one hard
satisfiable instance is n = 177, where the box engine is 18× faster
than CaDiCaL on the same clauses — and that is one trajectory, not a
property of the engine: the same formula with its progressions in five
orders (which renumbers the variables and reorders the atoms for both
solvers) gives boxes 0.07 / 0.96 / 0.61 / 1.53 / 2.89 s against CaDiCaL
1.25 / 0.02 / 0.30 / 1.10 / 1.22 s.  Each engine scatters 10–60× with
the ordering and each has an order it is lucky on; over the five the
two are comparable, CaDiCaL a little ahead on the median.  The
satisfiable side of the w(5;5) family is therefore not a box-engine
win to report; the refutation (n = 178, 56 s against 9.7 s) is the
number that means something, and it is 6× behind.

Measured on van der Waerden (`lib/waerden.jq`, `w(4;4;35)` UNSAT and
`w(4;4;34)` SAT, 35 variables, 374 clauses; times as the UI reports them,
best of 5): with one `ap4(x_i;x_{i+d};x_{i+2d};x_{i+3d})` box per
progression (`w4_ap(n)`, 187 calls, examples `w4435 boxes` / `w4434 boxes`)
the boxes backend refutes n = 35 in **1.5 ms** (306 conflicts) and solves
n = 34 in **0.7 ms** (49 conflicts) against CaDiCaL's 1.2–1.4 ms (287
conflicts) and 0.4–0.5 ms.  Before this work the same formulas took 30 ms
and 10 ms (DFS over rows: 1572 decisions / 790 conflicts, ~19 µs per
decision in allocation-heavy masks); the steps were allocation-free flat
masks with per-level snapshots (6.5 / 1.4 ms), the incremental prefix check
(−1.3 ms per job), learning (−2.5× conflicts) and the clause form (−5× per
assignment).  Wider boxes do **not** help here: sliding windows of width 7,
10 or 13 (`win7`…, generalized arc consistency over all progressions inside
the window) plus chain boxes for the longer differences (`norun4_L`,
`w4_win(n; W)`) leave the conflict count unchanged (GAC on a window adds
little over unit propagation on these sparse clauses) and cost more per
assignment (5–9 ms) — the strength of boxes is tables whose GAC beats unit
propagation (adders, counters, the bmc chain), not sparse clause sets.
Colour-flip symmetry breaking (`… x_1`) halves the box engine's conflicts
and leaves CaDiCaL's unchanged.  The bmc benchmarks did not regress
(`bmc_w4_n8_gt8` 1.1 ms, its single-box form 0.5 ms of which 0.25 ms is
building the 647-row tables).

**Deep formulas (2026-09-14).**  The path traversal extends a Sum's path by
all of its children through one nested continuation per child
(`traverse_sum`), so a Sum of 4 000 atoms — `w5_ap(178)`'s collapsed
complement — nested ~4 000 frame sets and overflowed a 2 MB stack (the
server aborted).  A Sum's trailing run of literal children — the whole Sum
for a box formula or a clause — is now extended in a loop (`literal_tail`,
both the uncovered-only and the positions/bubble-up traversals; the level
arithmetic of a prune is applied at once), and the runtime's threads get
256 MB stacks for the shapes that still nest (a Sum of thousands of
products).  With that, w(5;5;n) as `ap5` boxes: n = 177 (SAT) 0.42 s vs
CaDiCaL 1.21 s; n = 178 (UNSAT, 3 872 boxes) CaDiCaL 9.6 s, the box engine
not within 150 s — a plain CDCL without clause deletion or inprocessing is
the gap on hard UNSAT instances, the next engine work if it matters.

**Matrix multiplication, the tractable relative of `rank22_logical_form.tex`
(2026-09-14, `lib/matmul.jq`).**  The 2×2 Brent equations over GF(2) with r
products: 64 equations ⊕_m α^m_{ab} β^m_{cd} γ^m_{pq} = [b=c][a=p][d=q] over
12r variables.  Box forms: `mm_chain` (each equation a chain of
`xstep(p;a;b;c;q) ≡ q = p ⊕ abc` boxes) and `mm_boxes` (each term an `and3`
box — clause form in the engine — and each equation one parity box `xor{r}`
with its right-hand side a constant argument; `xor3…xor8` are chains of
`xor2` with the running parities hidden, compiled by composition); CNF forms
for CaDiCaL: `mm_cnf` (xor2 chain) and `mm_cnf_direct` (one clause per
wrong assignment of the r term variables); `mm_sym_boxes` / `mm_sym`: the
products in non-decreasing order of their α vectors (`le_4`), which keeps
satisfiability.  Rank 7 is Strassen; 7 is the rank, so 6 is UNSAT (and
with it every smaller r, a zero product being allowed).  Times as the UI
reports them, 60 s cap, the engine with learned-clause deletion
(`reduce_start` 4000):

| r | verdict | boxes `mm_chain` | `mm_chain`+sym | `mm_boxes` | `mm_boxes`+sym | CaDiCaL `mm_cnf` | +sym | `mm_cnf_direct` | +sym |
|---|---|---|---|---|---|---|---|---|---|
| 8 | SAT | 0.06 s | 0.12 s | 0.41 s | 6.5 s | 0.07 s | 0.01 s | 0.02 s | 0.07 s |
| 7 | SAT | 4.3 s | 4.4 s | 19.3 s | 30.7 s | 0.13 s | 0.39 s | 0.04 s | 0.06 s |
| 6 | UNSAT | > 60 s | 1.8 s | > 60 s | 3.0 s | 52.8 s | 0.26 s | 55.9 s | 0.37 s |
| 5 | UNSAT | 2.4 s | 0.11 s | 4.1 s | 0.14 s | 0.59 s | 0.04 s | 0.35 s | 0.07 s |

(rank 5 box times from the run before the deletion budget was raised.)  So
rank 8 and 7 SAT and rank 6 UNSAT are all decided within 60 s by both
engines; the UNSAT proof needs the symmetry breaking on both (without it
CaDiCaL takes 53–56 s and the box engine does not finish).  CaDiCaL is
10–100× faster on this family: the parity structure gives the box tables
nothing that unit propagation on the exact CNF does not have, and SAT
times are search luck (the four box variants of rank 7 span 4–31 s).
Two engine defects the benchmark exposed are fixed: cancellation did not
reach the completion engine (a cancelled job kept a core busy, and its
late verdict could be reported under the next job's name — a job
generation now guards the state), and the learned database grew without
bound (propagation fell to a seventh of its speed on long runs; LBD-based
deletion holds it at 2–4M propagations/s).

**XOR straight-line programs — the SAT-competition family
(2026-09-14, `lib/slp.jq`).**  SLP(k) of `doc/matmul_cxlb_satcomp.md`: do
k XOR additions compute the given forms (vectors in GF(2)^n) from the n
unit-vector inputs?  The encoding is `matmul/cxlb.py`'s, as boxes: per
step a `cnt2` chain (exactly two sources among the inputs and the earlier
steps), per value bit a `gx` chain (`q = p ⊕ s x`: the AND-guarded parity
x_t_i = s_t_i ⊕ ⊕_u (s_t_{n+u} ∧ x_u_i)), outputs as `imp` boxes guarded
by o_f_t with an `orb` chain for at-least-one, and the paper's symmetry
breaking (nonzero step values; adjacent independent steps strictly
lex-increasing — a `lexstep` chain).  Instances: Strassen's output side
(`strassen_out`, 4 forms over 7 products: SLP(8) SAT, SLP(7) UNSAT), the
four seed cells' output forms as data (`sun56_cell`, `cn120_cell`,
`i19_cell`, `i12_cell`), and `slp_window(cell; indices)` sub-instances over
the inputs the chosen forms use.  `tools/slp_program.py` decodes a
witness into the program and replays it; `tools/slp_bench.py` descends k
with CaDiCaL to each instance's minimum and times both engines at
min−1, min, min+1 (60 s cap; the same box formula for both engines,
CaDiCaL through the expansion):

| instance (cell[form indices]) | n | weights | k | boxes | CaDiCaL |
|---|---|---|---|---|---|
| strassen_out | 7 | 4,2,2,4 | 7 / 8 / 9 | UNSAT 0.7 s / SAT 0.7 s / SAT 0.2 s | UNSAT 0.2 s / SAT 0.01 s / SAT 0.04 s |
| sun56[0,3,7] | 9 | 3,3,3 | 5 / 6 / 7 | UNSAT 0.01 s / SAT 0.02 s / SAT 0.07 s | UNSAT 0.02 s / SAT 0.01 s / SAT 0.02 s |
| sun56[0,5,7] | 11 | 3,5,3 | 7 / 8 / 9 | UNSAT 5.5 s / SAT 41.5 s / SAT 26.0 s | UNSAT 0.33 s / SAT 0.19 s / SAT 0.11 s |
| i12[0,1,3] | 11 | 3,5,3 | 7 / 8 / 9 | UNSAT 2.2 s / > 60 s / > 60 s | UNSAT 0.31 s / SAT 0.43 s / SAT 0.21 s |
| i19[4,6,7] | 11 | 3,5,3 | 7 / 8 / 9 | UNSAT 1.6 s / SAT 42.8 s / > 60 s | UNSAT 0.30 s / SAT 0.28 s / SAT 0.23 s |
| cn120[0,6,8] | 9 | 5,5,3 | 7 / 8 / 9 | UNSAT 1.7 s / SAT 39.8 s / SAT 11.0 s | UNSAT 0.21 s / SAT 0.48 s / SAT 0.19 s |
| i12[0,3,4] | 12 | 3,3,7 | 9 / 10 / 11 | > 60 s / > 60 s / SAT 26.4 s | UNSAT 10.0 s / SAT 0.43 s / SAT 0.43 s |
| sun56[1,2,4] | 14 | 7,7,7 | 13 / 14 / 15 | > 60 s / > 60 s / > 60 s | > 60 s / SAT 15.7 s / SAT 58.2 s |

Three-form windows with n ≤ 12 and minimum ≤ 10 are the tractable
range: both engines decide them, the box engine within 60 s except the
harder SAT rows.  The box engine refutes the min−1 rows (UNSAT) in
0.7–5.5 s where CaDiCaL takes 0.2–0.3 s, but is 30–150× slower on the
SAT rows and times out on three of them; the n = 12 UNSAT boundary
(CaDiCaL 10 s) and the three-weight-7 window (min 14, its k = 13
undecided by either engine in 60 s) are beyond it.  As on the Brent
equations, the tables give it nothing here that unit propagation on the
same clauses lacks — the family's AND-guarded parities defeat table
propagation exactly as they defeat Gaussian elimination — and the gap is
CDCL maturity (heuristics, restarts, inprocessing) on the SAT side.

**Not yet (M1 remainder).**  A one-command certified boxed run: certifying a
`-b boxes` UNSAT currently means running the existing certified pipeline on
the expanded CNF — sound by construction (§4.3, phase 1), but not yet wired
behind `--emit-cover`.

## 11. Risks

1. **The premise is now "the user supplies the boxes."**  That converts the
   first draft's biggest risk (no recoverable structure) into a modelling
   task — but also means results only apply where a modeller has done that
   work.  M8 keeps the automatic route alive.
2. **Compile latency** for interactive use.  Two-tier hot-swap (§6.2)
   hides it; cache hits make repeats free.
3. **Native plug-ins** cross a memory-safety boundary.  Generated-only code,
   versioned ABI, and the no-boundary specialized mode (§6.3); correctness
   never depends on them (§4).
4. **Verification tooling maturity.**  Aeneas's supported Rust subset may not
   cover the checker; Verus's spec is the fallback (§4.4).  The Lean theorem
   stands regardless.
5. **Low-latency fabric on AWS** costs more than a queue; sharing may not pay
   for small instances.  The two-tier layout (§8.2) lets the queue tier run
   alone.
6. **Negative-occurrence tables** and **projection blow-up** (first-draft
   risks) stand; hierarchical boxes and lazy compilation mitigate.
7. **Parallel measurement trust.**  Deterministic mode for every benchmark.

## 12. Decisions (2026-09-06)

The five questions the first drafts left open, and Greg's answers:

1. **Box export** — the `# === boxes ===` section, as sketched in §5.1.
2. **Internals** — default to *projected* (fresh, local); `expose` is the opt-out.
3. **Verification** — Verus for the executable checker, Lean for
   `box_cover_sound`; Aeneas as the optional bridge (§4.4).
4. **Delivery order** — plug-ins (`libloading`, versioned C ABI) first; the
   specialized-solver build second (§6.2, M4).
5. **Cluster substrate** — AWS ParallelCluster with EFA for the sharing tier
   (§8.2, M7); the queue tier stays outside it.

## 13. References

- Schreiber, D., Sanders, P.  *Scalable SAT Solving in the Cloud.*  SAT 2021
  — Mallob: malleable job scheduling, job trees, clause-sharing portfolio.
- Michaelson, D., Schreiber, D., Heule, M., Kiesl-Reiter, B., Whalen, M.
  *Unsatisfiability Proofs for Distributed Clause-Sharing SAT Solvers.*  TACAS
  2023 — reconstructing one LRAT proof from distributed solving.
- Schreiber, D.  *Trusted Scalable SAT Solving with On-the-fly LRAT
  Checking.*  SAT 2024 — per-process trusted checkers, signed shared clauses.
- Mallob project page: https://satres.kikit.kit.edu/research/mallob/
- Verus — SMT-based verification of Rust (`exec`/`spec`/`proof`).
- Aeneas — Rust verification by translation to Lean/Coq/F*.
- `cake_lpr` — CakeML-verified LRAT checker (already hydra's UNSAT checker).
- Lazy clause generation (CP with learning) — the propagator-plus-learning
  architecture §3.5 mirrors.
- [dual-search-design.md](dual-search-design.md), [cover_certify.md](cover_certify.md),
  and the `phase4_cubes` branch write-up for this repository's own precedents.
