# Pseudo-Boolean proof emission (VeriPB)

## Why PB over DRAT

DRAT is bounded by resolution: PHP-N-M and RoundRobin-class
instances require exponential resolution proofs (Haken 1985), so
no DRAT proof of usable size exists for them.

Pseudo-Boolean proofs with cutting-planes (`pol`) rules have
polynomial proofs for those problems.  VeriPB
(`gitlab.com/MIAOresearch/software/VeriPB`) is the reference
verifier, and it accepts DIMACS CNF directly as input.

The two formats complement: same RUP scaffolding from CDCL +
cutting-planes for cardinality.

## Producing a PB proof

```bash
sat --backend cdcl --no-preprocess --emit-pbp proof.pbp < problem.cnf
```

Constraints (same as `--emit-drat`):
- `--backend cdcl` only.
- `--no-preprocess` only (proof references input CNF's variable indices).

`--emit-pbp` and `--emit-cover` can be combined.  Both also stack
with `--emit-drat` if you want all three artifacts from one run.

## Verifying a PB proof

```bash
veripb --cnf problem.cnf proof.pbp
```

Output: `s VERIFIED UNSATISFIABLE` on success; specific error
location + reason on failure (most commonly "constraint not
implied by RUP from current database").

## What we emit

Three constraint sources, written to the same proof file:

### 1. Header

```
pseudo-Boolean proof version 3.0
f <num_input_clauses>;
```

The `f` rule sanity-checks that VeriPB loaded the expected number
of constraints from the CNF.

### 2. Cover-pair resolvents (`pol`, cutting-planes)

For each complementary pair `(X@p1, ¬X@p2)` the matrix-method
discovers (via static cover + per-conflict cover events), we emit:

```
pol <id_a> <id_b> + s ;
```

where `id_a, id_b` are the VeriPB ConstraintIDs of the two
F-clauses involved (the original CNF clauses at positions `p1.0`
and `p2.0`; IDs are 1-indexed in load order).  The `+` adds the
two PB constraints, the `s` saturates — and the complementary
literals `X / ¬X` cancel, leaving the resolution product.

Each such rule introduces one new constraint with the next
ConstraintID.  These bake the matrix-method's structural cover
knowledge into the VeriPB database in cutting-planes form.

### 3. CDCL learned clauses (`rup`)

For each pure-resolution learned clause (the `pure_resolution`
filter from `LearnedClause`, see `cdcl.rs`), we emit:

```
rup +1 lit_1 +1 lit_2 ... >= 1 ;
```

The lit polarity is flipped from the matrix-method's complement
domain to F-domain (same as DRAT — alt `a` in the cube becomes
`¬a` in F).

### 4. Termination

```
rup >= 1 ;
output NONE;
conclusion UNSAT : -1;
end pseudo-Boolean proof;
```

The `rup >= 1` step asks VeriPB to derive the empty clause from
the current database.  `conclusion UNSAT : -1` points at the
most-recent constraint (the empty clause we just derived) as the
contradiction witness.

## Results (May 2026, release build)

| Input | Prover | Emitted rules | PBP size | VeriPB |
|-------|--------|---------------|----------|--------|
| tiny (4 cls) | <1 ms | 11 | <1 KB | **VERIFIED UNSAT** |
| PHP-3-2 | <1 ms | 15 | <1 KB | **VERIFIED UNSAT** |
| PHP-4-3 | <1 ms | 43 | ~1 KB | rejected (empty not RUP) |
| PHP-5-4 | <1 ms | 99 | ~3 KB | rejected (empty not RUP) |
| PHP-6-5 | <1 ms | 205 | ~8 KB | rejected (empty not RUP) |
| RoundRobin n16_d13 | 54 s | 113,562 | 18 MB | rejected (empty not RUP, in ~47 s) |

Note: VeriPB *does* verify all 113,561 intermediate rules for
RoundRobin in 47 s before rejecting at the final empty clause.
The intermediate rules are sound; the proof closure isn't
captured.

## Symmetry-based `red` proofs (polynomial-size for PHP-N-2)

VeriPB's `red` rule lets us add constraints justified by a *witness
substitution* that preserves F.  For symmetric problems, a
permutation of variables makes the constraint addition sound.

**A single `red` rule with cyclic-pigeon witness gives a
polynomial-size refutation of PHP-N-2 for any N.**
`tools/php_red_proof.py` generates the proof:

```
pseudo-Boolean proof version 3.0
f <num_clauses>;
red 1 x1 >= 1 : x1 -> x3 x2 -> x4 ... x_{2N-1} -> x1 x_{2N} -> x2 ;
rup >= 1 ;
output NONE;
conclusion UNSAT : -1;
end pseudo-Boolean proof;
```

Measured scaling (VeriPB on the generated proof):

| Problem | CNF clauses | PBP lines | VeriPB |
|---------|-------------|-----------|--------|
| PHP-3-2 | 9 | 13 | 13 ms |
| PHP-5-2 | 25 | 13 | 20 ms |
| PHP-10-2 | 100 | 13 | 19 ms |
| PHP-20-2 | 400 | 13 | 14 ms |
| PHP-50-2 | 2,500 | 13 | 13 ms |

The proof body is constant-length; only the witness substitution
grows linearly in N.  VeriPB verifies in milliseconds even at scale.

### Why M=2 is easy and M≥3 isn't

For PHP-N-2, pigeon clauses are arity-2.  After fixing
`x_{1,1} = 0`, unit propagation cascades:
`x_{2,1} = 0 ⇒ x_{2,2} = 1 ⇒ mutex hole 2 contradicts`.  VeriPB's
autoprove of the red rule's symmetry-preservation proofgoals
succeeds via the same BCP cascade.

For PHP-N-M with M ≥ 3, pigeon clauses have arity ≥ 3.  Forcing
`x_{1,1} = 0` doesn't trigger unit propagation (two unassigned
lits remain).  VeriPB's autoprove fails on proofgoal #1
(`derive x_{2,1} ≥ 1 from F ∧ x_{1,1} = 0`); the implication
holds vacuously (F is UNSAT) but RUP can't derive it.

### Why option 1 (explicit subproof via `pol` pre-derivation) doesn't work

The natural fix is: pre-derive cardinality bounds (at-most-1 per
hole) via cutting-planes before the `red` rule, so the subproof
can use them.  We tested this and confirmed a **fundamental
limitation**:

> **At-most-1 over K binary variables is not derivable from
> pairwise mutex via pure cutting-planes.**

The best we can do with pairwise mutex (K choose 2 binary
clauses `~x_i + ~x_j >= 1`):

- Sum all pairs: `(K-1)(~x_1 + ... + ~x_K) >= K(K-1)/2`
- Divide by `K-1`: `~x_1 + ... + ~x_K >= K/2`

So we get **at-most-⌊K/2⌋ per hole**, not at-most-1.  For PHP-4-3
this gives at-most-2 per hole; summing over 3 holes ≤ 6, vs.
pigeon-sum-lower-bound ≥ 4.  4 ≤ sum ≤ 6 — no contradiction.

MIR cuts (`pol C k m`, `pol C k n`) don't help either:
divisor-1 MIR on at-most-2 gives `>= 0` (degenerate), and larger
divisors don't tighten cardinality in this regime.

### Why option 2 (nested `red`) doesn't work either

VeriPB explicitly disallows `red` inside `proofgoal` contexts:

```
Error: Syntax error while parsing proof file!
Caused by:
    The rule `red` is not allowed in a proofgoal context
```

This blocks the obvious recursion ("inside the outer red's
subproof, use another red with hole-swap symmetry").

### Conclusion: extension variables or PR rules required

To get polynomial-size PHP-N-M proofs (M≥3) in VeriPB:

1. **Cook 1976 extension variables**: introduce aux variables
   `y_{p,k}` = "pigeon p is in some hole in [1..k]"; derive the
   counting argument arithmetically.  Substantial implementation;
   requires careful encoding of the recursive structure.

2. **PR (Propagation Redundancy) rules**: Heule et al's stronger
   rule that handles PHP-class symmetry in polynomial size.
   VeriPB supports related rules; the encoding uses conditional
   substitutions tracking the witness target's RUP-validity.

3. **Domain-specific cardinality detection**: if the input is
   *known* to be PHP-shaped, hardcode the Cook proof for that
   shape.  Brittle but tractable.

For RoundRobin n16_d13 (arity-13 pigeon clauses), the same wall
applies even more sharply.  None of these options is a quick
follow-up.

## What's missing for PHP-N-M (M≥3) and RoundRobin

The cover-pair `pol +s` rules give VeriPB many derived
constraints — all the per-pair resolvents that the matrix-method
discovers.  But the final UNSAT closure for cardinality-flavored
problems (PHP, RoundRobin) requires *aggregating* those
constraints and applying cutting-planes *division*, not just
addition.

For RoundRobin n16_d13 specifically:
- Aggregate the 120 pigeon clauses → `sum of all match-day vars ≥ 120`
- Aggregate the mutex clauses per day, divide by 2 (each match
  uses 2 team-day slots), aggregate over days → `sum of all
  match-day vars ≤ 104`
- Contradiction: 120 ≤ 104.

VeriPB has the cutting-planes operators (`pol ... + d` for divide)
to express this in ~3-5 rules, but the matrix-method doesn't
naturally produce that aggregation argument — it reasons
per-path, not per-cardinality-bound.

Possible paths to close this gap:

1. **Domain-specific cardinality detection**: scan the CNF for
   pigeon-style and mutex-style structure; emit hardcoded
   aggregation argument when detected.  Works for PHP and
   RoundRobin and any input that fits these templates; brittle.

2. **`red` (redundance-based strengthening) with symmetric
   witnesses**: VeriPB supports a stronger rule than RUP/pol
   that handles PHP-style symmetry in polynomial size.  See
   `tests/instances/correct/version3/redundance_explicit_subproof.pbp`
   in the VeriPB tree for a worked PHP example.  Translation
   from matrix-method's connection proofs to symmetric witnesses
   is non-obvious but plausible.

3. **Generic cardinality preprocessing**: tools like
   `roundingsat` or `kissat-cardinality` detect cardinality
   structure in CNF and produce cutting-planes proofs.
   Possibility: pipeline through such a tool for the closure
   step.

## What works today

- **Pipeline end-to-end**: emit, verify, get verdict.
- **Sound intermediate emission**: every `pol`/`rup` rule is
  individually accepted by VeriPB (we verified up to 113K rules
  on RoundRobin).
- **Small problems**: tiny and PHP-3-2 verify clean.
- **Large RUP-friendly UNSATs**: any problem where CDCL learns
  enough for BCP-empty (same domain as DRAT works on) will
  verify with PBP too.

## What doesn't work today

- **PHP-4-3 and up**: hits the same resolution wall as DRAT.
  Cover-pair resolvents alone aren't sufficient closure.
- **RoundRobin**: same wall.
- **Cardinality reasoning**: not yet implemented; future work.

## See also

- [`cover_certify.md`](cover_certify.md) — the matrix-cover
  format, always sound and complete but with verifier-side
  hardness equal to the input problem.
- [`drat_emission.md`](drat_emission.md) — DRAT analog, same
  RUP-only limits but uses standard tooling.
- `src/bin/sat.rs::PbpWriter` — PBP emission code (RUP +
  cover-pair pol rules).
- `tools/php_red_proof.py` — standalone proof generator for
  PHP-N-M using `red` rules with cyclic-pigeon symmetry.
  Polynomial-size proof for any PHP-N-2; M≥3 requires future
  work on explicit subproofs.
- `~/projects/veripb/` — VeriPB source/binary location (after
  `cargo install --path ~/projects/veripb`).
