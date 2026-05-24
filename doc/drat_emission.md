# DRAT proof emission

## Why DRAT

The matrix-cover certificate (`--emit-cover`, see
[`cover_certify.md`](cover_certify.md)) captures the matrix-method
UNSAT proof in its native form.  Verification is sound but, for hard
inputs like RoundRobin, equivalent in hardness to solving the
original formula (the matrix-path CSP is isomorphic to F itself).

DRAT (Delete Resolution Asymmetric Tautology) is the SAT-competition
standard proof format: a sequence of clauses each derivable from the
current clause set by *Reverse Unit Propagation* (RUP), terminated by
the empty clause.  A DRAT checker (`drat-trim`, or this repo's
`sat-drat-verify`) replays the proof in time linear in proof
length × BCP work — **the verifier never has to re-solve the original
problem**, so for hard UNSAT instances DRAT verification is dramatically
faster than the matrix-cover CSP.

Trade-off: DRAT is solver-trace-native (it captures the prover's
resolution chain), while the matrix-cover cert exposes the
"every-path-is-covered" structural argument.

## Producing a DRAT proof

```bash
sat --backend cdcl --no-preprocess --emit-drat proof.drat < problem.cnf
```

Output (proof.drat):

```text
1 -2 0          # first learned clause: (x_1 ∨ ¬x_2)
-3 0            # second learned clause: (¬x_3)
...
0               # empty clause = proof end (UNSAT marker)
```

Constraints:
- Only `--backend cdcl` (the only backend producing learned clauses).
- Only `--no-preprocess` (a DRAT proof references the input CNF's
  variables; preprocessing would shift indices).

## Verifying a DRAT proof

```bash
sat-drat-verify <cnf-file> <drat-file>
```

Exit codes:
- **0** — `VALID UNSAT PROOF`. Every emitted clause is RUP-implied by
  the current set; the empty clause is BCP-derivable from F ∪ {emitted
  clauses}.
- **1** — `INVALID DRAT PROOF (...)`. Either some clause isn't RUP, or
  the proof never reaches the empty clause.
- **2** — I/O or argv error.

`sat-drat-verify` is a small Rust DRUP checker (~400 LoC):

- Clause DB with watched literals.
- For each `Add(C)` step: assume each `¬l for l in C` as a unit,
  propagate, expect conflict; if not, REJECT.
- For each `Delete(C)` step: mark clause as deleted (no soundness
  check; just shrinks the active DB).
- The empty clause step succeeds iff BCP on the current set already
  derives a conflict.

A standards-compliant DRAT checker like `drat-trim` accepts the same
file format and will also reject non-RUP clauses.

## Implementation note: cdcl's emission filter

The `CdclController` learns clauses via 1UIP analysis on the matrix-
method trail.  The matrix-method trail has three Reason types:

- `Decision`: pushed by the DFS picking a Prod alt.
- `SumForced`: pushed by the engine descending into a Sum's only
  unblocked branch.  Matrix-method-specific — no CNF-resolution analog.
- `Implied(rid)`: pushed by unit propagation from clause `rid`.

Standards-DRAT requires every emitted clause to be RUP-implied: a
purely-resolution-derivable chain from F + earlier-RUP-emitted
clauses.  We track this per-learned-clause via
[`LearnedClause::pure_resolution`](../src/controller/cdcl.rs):

`pure_resolution = true` iff
1. The 1UIP loop terminated naturally (no SumForced bailout).
2. Every clause resolved through in the chain was itself RUP-valid
   (transitively).
3. No surviving learning lit corresponds to a SumForced trail entry.

Only `pure_resolution=true` clauses get emitted to the DRAT file.
The non-emitted (matrix-method-specific) clauses are sound for the
internal search but not standards-RUP.

## Known limitations

### 1. Incompleteness on PHP-family inputs

Even when every emitted clause is individually RUP-valid, the matrix-
method engine may exhaust its search via DFS pruning *before* CDCL
learns enough clauses for BCP to reach the empty clause.  Empirically
(May 2026, release build):

| Input               | Prover time | Emitted clauses | Verifier (time)            |
|---------------------|-------------|-----------------|----------------------------|
| tiny (4 cls)        | <1 ms       | 2               | VALID UNSAT PROOF (<1 ms)  |
| PHP-3-2             | <1 ms       | 2               | VALID UNSAT PROOF (<1 ms)  |
| PHP-4-3             | <1 ms       | 6               | INVALID (empty not RUP)    |
| PHP-5-4             | <1 ms       | 18              | INVALID (empty not RUP)    |
| PHP-6-5             | <1 ms       | 54              | INVALID (step 48 non-RUP)  |
| RoundRobin n16_d13  | 4:51 min    | 51,161          | INVALID (step 53 non-RUP, ~30 ms) |

The DRAT trace for PHP-4-3 / PHP-5-4 is *sound prefix-wise* (each
clause is genuinely RUP-implied) but the prover stopped learning
before the BCP-closure was complete.  A pure-CDCL solver on the same
input would continue learning until conflict at decision level 0
yields the empty clause; the matrix-method shortcuts this via DFS
exhaustion.

### 2. Some matrix-method-specific clauses leak past the filter

On PHP-6-5 and larger, the `pure_resolution` flag is a sound
over-approximation but not a complete characterization of RUP-validity
under matrix-method semantics.  Some clauses pass the filter but are
rejected by `sat-drat-verify` as non-RUP.  Empirically: PHP-6-5
emits 54 clauses, all `pure_resolution=true`; the verifier rejects
clause 48 as non-RUP.

The gap comes from matrix-method-specific inference paths through
the Sum/Prod structure that aren't fully captured by tracking trail
reasons alone.  A robust fix would either:
- Restrict the cdcl backend to "pure CDCL mode" (disable matrix-
  method shortcuts when `--emit-drat` is on) — loses the matrix-
  method's pruning power.
- Translate matrix-method inferences to explicit resolution steps
  emitted alongside the 1UIP learnings — substantial work.

### 3. Performance overhead

The `pure_resolution` check adds an O(|trail|)-per-learning-lit cost
to `analyze_conflict`.  On RoundRobin-scale inputs this measurably
increases search time vs vanilla `cdcl`.

## Recommendation

For **sound, replay-able UNSAT certificates** on matrix-method
outputs, use [`--emit-cover`](cover_certify.md) — the cover cert is
matrix-native, always complete (modulo the static-cover cap), and
verifiable by `sat-cover-verify`.

The DRAT emission is **best-effort**: useful as a sanity check on
small inputs where the proof happens to complete, and as raw material
for future work on translating matrix-method proofs to standards-DRAT.
Pair it with `--emit-cover` for inputs where DRAT incompleteness might
matter.

## See also

- [`cover_certify.md`](cover_certify.md) — matrix-cover certificates,
  the reliable path for matrix-method UNSAT replay.
- `src/controller/cdcl.rs::analyze_conflict` — where
  `pure_resolution` is computed.
- `src/bin/sat.rs::DratWriter` — emission side.
- `src/bin/sat_drat_verify.rs` — Rust DRUP verifier.
