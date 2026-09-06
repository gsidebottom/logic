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
compiled boxes.  Learning matters more than in the first draft of this design: Mallob's
evidence (§8) is that *sharing* learned clauses is what makes distributed
solving scale, so nogoods and their sharing are first-class components — but
still gated by the A/B in §10; the `phase4_cubes` result (learned-cube
sharing: "overhead with no benefit") is the cautionary precedent for assuming
learned information helps the *cover* search.

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
boxes; `tools/boxes_verdict_check.py` and `tools/gen_adder_boxes.py`.

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

**Not yet (M1 remainder).**  The box-call form in the formula language / UI
(boxes enter through `--boxes` instance files today), and a one-command
certified boxed run: certifying a `-b boxes` UNSAT currently means running the
existing certified pipeline on the expanded CNF — sound by construction
(§4.3, phase 1), but not yet wired behind `--emit-cover`.

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
