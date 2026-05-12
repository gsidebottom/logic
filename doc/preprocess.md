# NNF preprocessing with witness reconstruction

## Goal

Run a sequence of cheap, semantics-preserving simplifications on the NNF
*before* the matrix-method search begins, while preserving every
externally-visible certificate the search currently produces:

- **SAT outcome:** a satisfying assignment over the **original**
  variables.
- **VALID outcome (UNSAT of the formula, SAT of validity):** a
  falsifying assignment over the original variables.
- **UNSAT outcome:** a *cover* — a set of complementary literal pairs at
  **original** NNF positions that, together, dominate every path through
  the matrix.

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

## Phase 2+ (deferred, depending on Phase 1 results)

- **Phase 2:** failed-literal probing. Reuses Pass 1's UP machinery;
  adds `lemma_covers` collection.
- **Phase 3:** at-most-1 detection. Pattern match + collapse.
- **Phase 4:** BVE with size-guard.

We'll re-evaluate after Phase 1: if unit propagation alone delivers a
big chunk of the expected wins on the faulty-adder rows, the remaining
phases are clearly worth the effort. If unit propagation is a wash,
that's a useful signal that the bottleneck isn't variables-that-pin
themselves and we should look elsewhere (e.g. BVE on real Tseitin
auxiliaries is the more aggressive transformation, and is a candidate
even if Phase 1 doesn't move the needle).

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
