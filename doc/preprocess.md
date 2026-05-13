# NNF preprocessing with witness reconstruction

## Goal

Run a sequence of cheap, semantics-preserving simplifications on the NNF
*before* the matrix-method search begins, while preserving every
externally-visible certificate the search currently produces.  All four
outcomes work through paths of the matrix the search runs on:

- **SAT outcome** (satisfiability search runs on the *complement* NNF
  matrix):  a satisfying assignment over the **original** variables,
  derived from a non-complementary path of the complement NNF matrix.
- **UNSAT outcome** (also via the complement NNF matrix): a
  *complementary cover* of the complement NNF matrix — a set of
  complementary literal pairs at **original**-complement-NNF positions
  that together dominate every path through the complement matrix.
- **VALID outcome** (validity = UNSAT of the complement): a
  complementary cover of the NNF matrix, witnessing that
  every path through the NNF matrix has a complementary pair.
- **INVALID outcome** (validity = SAT of the complement): a falsifying
  assignment over the original variables, derived from a
  non-complementary path of there NNF matrix.

In the existing code (`Matrix::valid` / `Matrix::satisfiable`) the
validity-direction search runs on `self.nnf` (the original F)
directly, but the certificates produced are interchangeable with the
complement-side view because the matrix-method theorem applies to any
NNF: a complementary cover of F's matrix and a complementary cover of
comp(F)'s matrix are dual proofs of the same fact.  This doc speaks
in terms of the complement matrix throughout because that's the side
where SAT preprocessing (unit propagation) is sound.

The four transformations under consideration:

1. Unit propagation
2. Failed-literal probing
3. At-most-1 counter recognition / collapse
4. Bounded variable elimination (BVE) on Tseitin auxiliaries

Each is implementable while preserving witnesses, but each requires its
own reconstruction story. The text-book SAT preprocessor records an
"assignment reconstruction stack"; we additionally need a **cover
position-translation table** because our UNSAT certificate is positional
rather than clause-based.

## Architecture overview

```
build NNF
↓
preprocess (run passes to fixpoint, build reconstruction)
  ├─ unit propagate (cheap, fixed-point with FLP)
  ├─ failed-literal probe
  ├─ at-most-1 collapse
  └─ BVE (selective: single-definition auxiliaries only, size-guarded)
↓
classify_paths(preprocessed_nnf, mode)
↓
on SAT:
  partial assignment (over surviving vars) ← path
  Reconstruction::extend_assignment(&mut partial)
  return Sat(partial)                      // in ORIGINAL vars
on UNSAT:
  covers_simp ← cover pairs from search
  covers_orig ← PositionMap::translate(covers_simp)
  covers_orig.extend(preprocessing_lemma_covers)
  return Unsat(covers_orig)                // in ORIGINAL positions
```

## Core types

```rust
// src/preprocess.rs (new)

pub struct Preprocessed {
    /// Simplified NNF — what the search actually runs on.
    pub nnf: NNF,
    /// Replay log for SAT-witness reconstruction.
    pub recon: ReconstructionStack,
    /// Position map for UNSAT-witness translation.
    pub pos_map: PositionMap,
    /// Lemma covers derived during preprocessing (failed-literal
    /// probing, contradictions in unit propagation). Prepended to
    /// the search's covers on UNSAT.
    pub lemma_covers: Vec<Pair>,
    /// If `Some(verdict)`, preprocessing alone settled the formula.
    /// `Some(true)`  = TAUTOLOGY (every path covered by lemmas)
    /// `Some(false)` = FALSIFIABLE with `assignment_witness`
    pub trivial: Option<Trivial>,
}

pub enum Trivial {
    Valid,                            // proved by lemma_covers alone
    Falsifiable(Vec<Lit>),            // partial assignment witness
}

pub enum ReconStep {
    /// `var := value`; recovered trivially during extension.
    Unit { var: Var, value: bool },
    /// `var := defn.evaluate(surviving_asgn)` — used by BVE and
    /// at-most-1 collapse to define eliminated vars by formula.
    Defined { var: Var, defn: NNF },
}

pub struct ReconstructionStack(Vec<ReconStep>);

impl ReconstructionStack {
    /// Replay in reverse, extending `asgn` with values for every
    /// variable eliminated during preprocessing.
    pub fn extend_assignment(&self, asgn: &mut Vec<Lit>) { … }
}

/// Forward-map from a leaf position in the preprocessed NNF to
/// the set of leaf positions in the original NNF that it represents.
/// One-to-one for unit propagation and FLP. One-to-many possible
/// for BVE (duplication during resolution).
pub struct PositionMap {
    forward: HashMap<Position, Vec<Position>>,
}

impl PositionMap {
    pub fn translate_pair(&self, p: &Pair) -> Vec<Pair> { … }
}
```

## Per-pass reconstruction

### Pass 1 — Unit propagation (Phase 1 of implementation)

**What it does.** Walk the NNF top-down. If a `Prod` node contains a
`Lit` child, that literal is forced true at this point in the formula.
Propagate: substitute the variable's forced value everywhere, then
simplify (drop `1`s from `Prod`, drop `0`s from `Sum`, etc.). Iterate
to fixpoint.

**Assignment reconstruction.** For every forced `var := value`, push
`ReconStep::Unit { var, value }`. Trivial replay.

**Cover reconstruction.** Two sub-cases:

- **A cover discovered by the search uses only surviving leaves.**
  Translate each leaf's preprocessed position to its original-NNF
  position via `PositionMap`. The map is built by the rewrite: every
  surviving leaf carries its original position; the simplified NNF's
  position tree differs only by index renumbering after deletions.

- **Preprocessing itself derived a contradiction** (e.g. `Prod` contains
  both `x` and `x'`). That `(x_pos, x'_pos)` pair is a single-pair cover
  for the whole subformula. Push it onto `lemma_covers` and replace the
  subformula with `0`.

- **Original-NNF covers that involved a unit-propagated literal** are
  no longer needed: the surviving NNF's covers + lemma covers already
  dominate every original-NNF path, because every original path either
  (a) is consistent with the unit assignment (so it appears in the
  preprocessed NNF, possibly covered there) or (b) is inconsistent with
  it (so the lemma cover at the unit's enforcement point covers it).

**Edge cases.**

- A `Prod` with empty children (true) inside a `Sum` annihilates the
  `Sum` to true; the `Sum` collapses to `Prod(vec![])`. That's an
  unconditional satisfaction — record `Trivial::Valid` with empty
  lemma_covers if this happens at the root (the *whole* formula was a
  tautology, so the search would have produced an empty cover anyway —
  consistent).
- A `Sum` with all children false collapses to false. At root: the
  formula is falsifiable trivially — record `Trivial::Falsifiable` with
  the partial assignment that triggered the collapse.

### Pass 2 — Failed-literal probing

**What it does.** For each variable `x` that survives Pass 1, tentatively
assert `x = true` and run unit propagation. If propagation derives ⊥,
conclude `x = false` as a new unit. Symmetric for `x = false`. Repeat
until no new units appear.

**Assignment reconstruction.** Each successful probe produces a unit,
handled exactly like Pass 1.

**Cover reconstruction.** Each failed probe produces a *derivation
chain*: the sequence of complementary pairs that fired during the
failed propagation. That chain is a valid cover for "any path
consistent with `x = true`" — which is what we need when we then assert
`¬x`. Stash the chain on `lemma_covers`. (Concretely: each step
`l implies l'` resolves with a clause that contains `l'`; the
participating literal pair forms a cover pair.)

**Caveat.** Probing pairs are typically positions that survive into the
preprocessed NNF. They get translated through the same `PositionMap` as
search covers — no special-casing needed.

### Pass 3 — At-most-1 counter collapse

**What it does.** Detect the canonical sequential-counter encoding for
`AtMost1(d_1, …, d_k)`:

```
(¬d_1 ∨ u_1)
(¬d_2 ∨ u_2)  (¬u_1 ∨ u_2)  (¬d_2 ∨ ¬u_1)
(¬d_3 ∨ u_3)  (¬u_2 ∨ u_3)  (¬d_3 ∨ ¬u_2)
…
```

Pattern-match on the NNF (counters are uniform in shape). When detected,
replace the sequential-counter cluster with a compact pairwise NNF:

```
∏_{i<j} (¬d_i ∨ ¬d_j)
```

**Assignment reconstruction.** `u_i := d_1 ∨ d_2 ∨ … ∨ d_i`. Push
`ReconStep::Defined { var: u_i, defn: Sum(d_1..d_i) }`.

**Cover reconstruction.** Original-NNF covers from the counter-chain
clauses *can* appear in proofs the search wouldn't find on the new
formula. We avoid this by **also keeping** the sequential-counter
clauses logically (as lemma covers, on demand) — but in practice, the
pairwise form's covers already imply the chain's covers, so we
translate via `PositionMap` like everything else.

Concretely: the `PositionMap` for this pass is one-to-many — a single
pairwise-form position represents the *multiple* chain-form positions
that encoded the same constraint. Translating a cover pair returns
*one* representative original position (sufficient to certify UNSAT;
not all positions covered).

### Pass 4 — BVE on Tseitin auxiliaries

**What it does.** A *Tseitin auxiliary* is a variable `x` introduced
purely as a name for some gate expression `G(survivors)`, with the
property that `x` has a single definitional occurrence (the `(x ↔ G)`
biconditional) and a small number of *use* occurrences. Eliminate `x`
by substituting:

- `x` is replaced by `G` everywhere it appears positively.
- `¬x` is replaced by `¬G` everywhere it appears negatively.

Then drop the definitional clauses (now tautologous).

**Assignment reconstruction.** `x := G(surviving_asgn)`. Push
`ReconStep::Defined { var: x, defn: G }`.

**Cover reconstruction.** This is the hardest case. Substituting `G`
into multiple use sites *duplicates* `G`'s leaves — each copy is a new
position in the preprocessed NNF that maps back to the *same* original
position. `PositionMap` becomes one-to-one in the forward direction
(each new position → unique original) but many copies share originals.
That's fine for translation: any cover pair in the preprocessed NNF
translates to a valid original-position pair.

**Restrictions to keep this tractable:**

- Eliminate `x` only if it has **at most one polarity occurrence on the
  definition side** (so the substitution doesn't blow up).
- Bound NNF size growth: skip the elimination if it would grow the NNF
  beyond a configurable multiplier (default 1.5×).

## Reconstruction order

`extend_assignment` walks the stack in **reverse** insertion order. This
matters when one elimination depends on a variable eliminated later in
the pipeline: by the time we recover that variable, all *later*
eliminations have already been undone, and the current step's `defn`
evaluates against survivors plus already-recovered variables.

## Verification harness

Add a debug-only `--verify-witnesses` mode in `Preprocessed::solve`:

```rust
match outcome {
    Sat(asgn) => {
        debug_assert_eq!(original_nnf.evaluate(&asgn), Ok(true));
    }
    Unsat(covers) => {
        debug_assert!(every_path_covered(original_nnf, &covers));
    }
}
```

This catches reconstruction bugs immediately during the test suite.
Production builds skip the verification (it's `O(paths)`).

## Implementation plan — Phase 1

Phase 1 ships **unit propagation only**, with the full scaffolding for
later passes:

1. New file `src/preprocess.rs` containing:
   - `Preprocessed`, `ReconstructionStack`, `PositionMap`, `Trivial`,
     `ReconStep` (full enum, only `Unit` variant used in Phase 1).
   - `pub fn preprocess(nnf: &NNF) -> Preprocessed` running unit
     propagation to fixpoint.
   - `impl Preprocessed { pub fn reconstruct_assignment(...) -> Vec<Lit>; pub fn translate_cover(...) -> Cover; }`

2. New API on `Matrix`:
   - `pub fn try_from_with_preprocessing(formula: &str) -> Result<(Matrix, Preprocessed), String>`
   - returns the original `Matrix` and a `Preprocessed` view of `nnf`
     (and a separate `Preprocessed` of `nnf_complement` when needed).
   - Existing `Matrix::try_from` is unchanged; preprocessing is opt-in.

3. Output translation helpers, used by callers that want witnesses in
   original-NNF terms:
   - `Preprocessed::reconstruct_sat(prod_path) -> Vec<Lit>`
   - `Preprocessed::reconstruct_unsat(covers) -> Cover`

4. Tests (`#[cfg(test)] mod tests`):
   - Toy formulas (`a * (a + b)`, `a * a'`, `(a + b) * (a' + c)`,
     `a' * (a + b) * (b' + c)`) hand-checked.
   - Round-trip: for each test formula, run `preprocess` then verify
     the reconstructed witness against the original NNF.
   - Quine-McCluskey-style fuzz: generate random small formulas,
     preprocess, run reference search, verify witness.

5. Bench hook: add a `--preprocess` flag to `bench_focused_top_config`'s
   row helper that runs preprocessing first and reports the configs'
   times on the preprocessed NNF. We're looking for whether the
   preprocessed problem is faster (or, more dramatically, trivially
   solved before the search starts).

## Phase 1 measured impact

Phase 1 landed as `src/preprocess.rs` + a hook into the focused bench
(`bench_focused_top_config_preprocessed`).  Results on the four
benchmark rows:

```
                                            cadical  matrix.smart  matrix.cdcl  greedy×cdcl  greedy×eff
random-3sat n=30 (SAT)        baseline   0.10 ms       0.29 ms       0.18 ms       1.34 ms      1.41 ms
                              with pp    0.06 ms       0.27 ms       0.20 ms       1.34 ms      1.38 ms
                              ratio        ~                                                  (pp = no-op: 0 units found)

faulty_add 16/1 UNSAT         baseline   0.93 ms      50.25 ms      49.56 ms      22.19 ms      8.89 ms
                              with pp    0.83 ms       0.90 ms       0.92 ms       1.36 ms      1.32 ms
                              speedup                     56×           54×           16×          6.7×

faulty_add 16/2 SAT           baseline   0.95 ms    6766    ms    6935    ms    3845    ms    919    ms
                              with pp    0.82 ms      60.81 ms      80.67 ms      17.81 ms     26.47 ms
                              speedup                    111×           86×          216×           35×

bmc count-zeros UNSAT         baseline   4.34 ms       4.91 ms       6.27 ms      90.09 ms      3.87 ms
                              with pp    4.47 ms       5.07 ms       7.32 ms      85.29 ms      5.08 ms
                              ratio        ~             ~             ~             ~      0.76× (slight regression)
```

**Preprocess overhead:** 0.06–0.55 ms (negligible).

**What happens on each row:**

- **random-3sat** — no top-level unit clauses ⇒ 0 units found, total
  no-op.  Timings within noise.
- **faulty_add 16/1 UNSAT** — pp reduces 1210 → 831 leaves with 50
  units and 116 lemma covers (the IO pinning a=3, b=19, s=21, c_0=0,
  c_6=0 cascades through the carry chain).  `matrix.smart` and
  `matrix.cdcl` close their 50× gap with CaDiCaL.
- **faulty_add 16/2 SAT** — pp reduces 1600 → 1221 leaves with the
  same 50 units / 116 lemmas.  The largest absolute wins: 6.9 s →
  17.8 ms for `greedy×cdcl`, 6.8 s → 60 ms for `matrix.smart`.
- **bmc count-zeros UNSAT** — 3600 → 3172 leaves, 16 units, 167
  lemmas.  The 16-bit count-zeros logic isn't reduced by pure
  top-level UP; backends are within noise (≤30% noise band), with a
  small `greedy×eff` regression (3.87 → 5.08 ms).

## Phase 3 / Phase 4 measured impact

Phase 3 implemented **bounded-occurrence BVE** (initially `p ≤ 2`,
`n ≤ 2`) with a strict per-step lit-count size guard.  The BVE
formulation handles at-most-1 *and* at-most-K (≥ 2) sequential
counter chains uniformly: each counter aux has 2 positive and 2
negative occurrences, so it resolves out within the bound.

Phase 4 extended the same machinery with a **looser occurrence bound
of (8, 8)** — capturing gate-Tseitin aux vars that appear in 3–6
clauses per polarity (AND/OR/XOR gate definitions + their downstream
uses).  The size guard stays strict (no lit-count growth):
empirically a +25% growth slack caused *more* BVE eliminations on
faulty_add 16/2 SAT but *fewer* leaf reductions overall, suggesting
BVE was chasing marginal-gain auxes that net-grew the matrix.

```
                                        cadical   smart   cdcl    g×cdcl   g×eff
random-3sat n=30 (SAT)        Phase 1     0.06     0.27    0.20    1.34     1.38
                              Phase 3     0.07     0.22    0.18    1.37     1.39
                              Phase 4     0.21     0.42    0.17    1.46     1.34   (pp no-op; within noise)
faulty_add 16/1 UNSAT         Phase 1     0.83     0.90    0.92    1.36     1.32
                              Phase 3     0.79     1.85    1.93    1.32     3.93
                              Phase 4     0.87     0.79    0.64    1.31     1.36   (~cadical parity)
faulty_add 16/2 SAT           Phase 1     0.82    60.81   80.67   17.81    26.47
                              Phase 3     0.86     4.83    4.64    1.32     1.31
                              Phase 4     0.88     1.31    0.94    1.32     1.30   (🎯 cadical parity)
bmc count-zeros UNSAT         Phase 1     4.47     5.07    7.32   85.29     5.08
                              Phase 3     4.52     4.98    6.53   80.20     5.16
                              Phase 4     4.29     5.60    6.64   86.02     5.08   (~unchanged across phases)
```

**Phase 4 preprocessing depth**, faulty_add 16/2 SAT: leaves 1600 →
1147, 88 recon steps (vs. Phase 3's 1213 leaves / 54 steps).  The
extra 34 BVE eliminations were aux vars with 3-4 occurrences that
Phase 3's tighter bound skipped.

**BMC didn't improve** under either Phase 3 or Phase 4.  Its
count-zeros aux vars appear to have either >8 occurrences per
polarity or BVE-induced lit growth that exceeds the strict guard.
The remaining work on BMC needs different techniques — perhaps Phase
2 (FLP) probing deeper into the carry chain, or a tuned size-budget
specifically for circuit-encoded formulas.

**Result with Phase 4:** `matrix.smart` and `matrix.cdcl` are now
essentially at **cadical parity** on faulty_add 16/2 SAT (1.31 / 0.94
ms vs cadical's 0.88 ms — closed the ~100× gap completely).  No
regressions on the other bench rows.  Reconstruction round-trips
correctly via `ReconStep::Defined` with a pad-survivors-first
extension order.

### Bug surfaced and fixed by Phase 3 (resolved)

The first Phase 3 bench showed `greedy×cdcl` and `greedy×eff`
returning UNSAT (incorrect) on `faulty_add 16/2 SAT` while
`cadical`, `matrix.smart`, and `matrix.cdcl` correctly returned SAT
on the same Phase-3-simplified NNF.

**Root cause** (located via a bisection diagnostic in
`bench.rs::dual_disagreement_on_faulty_add`): `CdclController`
returned `Some(1)` for cascade conflicts ("1-Prod backjump").  The
positions-on DFS engine (`for_each_path_prefix_ord`) honours that
unwind request, which on Phase-3-simplified NNFs propagated up
through an enclosing `Sum` and skipped the subtree that contained
the SAT witness.  The positions-off DFS engine
(`for_each_path_prefix_no_positions_ord`) sidestepped the issue by
casting the controller's `Option<usize>` to `bool` via `.is_none()`
— silently dropping the multi-level-unwind semantics.

**Fix** (committed in `src/controller/cdcl.rs`,
`should_continue_on_prefix`): CDCL now returns `Some(0)` (skip this
alt only) for cascade conflicts instead of `Some(1)` (skip the
whole Prod).  The learned clause is still registered, so future
propagation through the same path still benefits.  The fix is
identical in effect to what positions-off DFS was already doing via
`.is_none()`.  Trade-off: we lose the 1-Prod backjump optimization
when CDCL drives the positions-on DFS engine — typically ~1.5-2.5×
slower on `matrix.smart` / `matrix.cdcl` for SAT-direction searches
with significant cascade activity, but still 12-20× faster than
Phase 1 alone on the targeted faulty_add 16/2 SAT case.

A second cleanup at the same time: BVE candidate selection is now
deterministic (sort by `(cost, var)` instead of relying on `HashMap`
iteration order).  Pre-fix, the bench's `matrix.smart` could swing
from 4 ms to 240 ms across runs because different ordering of
ties in `min_by_key` produced different simplified-NNF clause
orderings.

Diagnostic test `dual_disagreement_on_faulty_add` lives in
`src/dual/bench.rs` as a regression check for any future change to
this area.

## Phase 2 implemented, gated off by default

**Failed-literal probing** is implemented in `src/preprocess.rs`
behind a `const ENABLE_FLP: bool = false` switch.  Why off:

FLP collapses the *search target* dramatically — on the focused
bench it reduces faulty_add 16/1 UNSAT and 16/2 SAT to **zero
leaves** during preprocessing (the formulas are solved entirely
without any matrix-method search) and BMC count-zeros from 3172 →
300 leaves.  Post-FLP search times for `matrix.smart` /
`matrix.cdcl` drop to ~0.05 ms.

But the *preprocessing cost* of probing every surviving variable
twice (`v=true` then `v=false`) on a 1600-leaf NNF is huge:

```
                                   pp time     search time   total
                       Phase 4     ~7 ms        1.0 ms       ~8 ms
                       Phase 2    ~358 ms       0.07 ms     ~358 ms
faulty_add 16/2 SAT
                       cadical                                 0.84 ms
```

Net: Phase 4 wins ~45× on total time-to-answer for these formulas.
Phase 2 only pays off if preprocessing is amortized across many
searches (which isn't how the web app or focused bench use it).

**Code is in place** (`flp_one_round`, `probe_drives_to_false`,
`substitute_units_no_cover`) so a future caller can enable FLP by
flipping the const or adding a builder option.  Outstanding work
before turning it on by default:

1. Reduce per-probe cost.  Currently each probe clones the entire
   tagged tree and runs UP from scratch.  Could be 10-100× cheaper
   with a watched-literal representation or incremental
   substitution that just records overlays.
2. Lemma-cover emission.  FLP-derived units don't emit
   lemma_covers (we use `substitute_units_no_cover` to bypass).
   The UNSAT cover output is therefore incomplete on
   FLP-derived-units paths; soundness for satisfiability is
   preserved.

## Phase 4 done; possible follow-ons

- **Better FLP** (above) — make it competitive in total time.
- **Phase-aware Phase 4 size guard.**  Phase 4's strict no-growth
  rule misses BMC's count-zeros aux vars.  A circuit-aware budget
  (e.g. allow growth proportional to the eliminated variable's
  *fanout*) might capture them without runaway formula bloat.
- **Production integration**.  Phase 4 is plumbed into the web
  app via `Matrix::preprocess_for_search`; covered above.  The
  `preprocessed_to` flag in the response is now also surfaced in
  the frontend: valid / satisfiable / unsatisfiable verdicts that
  preprocessing decided on its own are labelled *"decided by
  preprocessing alone, no search of the N path matrix needed"*
  rather than the usual "all N paths covered" / "uncovered path"
  wording, so the user can tell at a glance when the matrix search
  ran zero / one trivial paths.

## Risks

1. **Solver-controller interaction shifts.** Preprocessing changes the
   formula's structure; expect changes in benchmark ordering across
   `cadical / matrix.smart / matrix.cdcl / greedy×cdcl / greedy×eff`.
   Mitigation: full `bench_focused_top_config` rerun after each phase.
2. **Cover translation correctness.** Easiest place for silent bugs.
   Mitigation: `--verify-witnesses` mode (above), exercised in tests.
3. **Empty NNF after preprocessing.** If preprocessing reduces the NNF
   to `Prod([])` (true) or `Sum([])` (false), the search never runs.
   Output path returns `Trivial::Valid` or `Trivial::Falsifiable`
   directly. Need to plumb this through `Matrix::valid` / `satisfiable`.
4. **BVE size blow-up (Phase 4).** Bounded by size-multiplier guard; a
   formula that the guard rejects falls back to unmodified BVE-pass
   output (which is still semantically the same).
