# `mm55proof` — a Lean 4 proof that the 55-addition scheme multiplies matrices

This Lake project machine-checks that the rank-23 (23-multiplication),
**55-addition** straight-line program for 3×3 matrix multiplication —
de Groote class `i19w225c4efh`, fewer additions than any previously
published rank-23 3×3 scheme (the prior record was 56) — actually
computes the matrix product.

The program itself is `../external/i19-55adds-slp.txt`, transcribed and
fuzz-tested in Rust at `../../src/mm55.rs`. The Lean files here are
generated from that Rust source by `../lean_gen.py`, which also
independently pre-verifies the scheme over a non-commutative polynomial
ring before emitting the proof.

## What is proved

Both statements are over a **general, not-necessarily-commutative**
ring `R`. Because every product keeps its left factor on the left, this
certifies a genuine bilinear algorithm that applies recursively to
block matrices.

- **`Matmul55.correct`** (`Mm55proof/Correct.lean`) — the faithful
  straight-line program: the 78 intermediate wires (`aw*`, `bw*`, `m*`,
  `cw*`) appear as hypotheses fixing them to their defining expressions,
  and the theorem concludes each of the 9 outputs equals the
  matrix-product entry `∑ₖ aᵢₖ bₖⱼ`. Proof: `subst_vars; noncomm_ring`
  (with `abel` for the one output that is a pure additive reordering).
  Depends only on the axiom `propext`.

- **`Matmul55.scheme_eq_mul`** (`Mm55proof/Matrix.lean`) — the same
  scheme written as a function `scheme : Matrix (Fin 3) (Fin 3) R →
  Matrix (Fin 3) (Fin 3) R → Matrix (Fin 3) (Fin 3) R` in four labeled
  sections — `A_in` (13 adds on the A input side), `B_in` (14 on the
  B side), `M` (the 23 multiplies), `C_in` (28 adds on the C output
  side) — proved equal to Mathlib's own matrix product `A * B`. This
  packages the result in Mathlib's native `Matrix` API. Depends on the
  three standard foundational axioms `propext, Classical.choice,
  Quot.sound`.

Neither proof uses `sorry` (each file ends with a `#print axioms`
audit, printed during the build).

## Reproduce

Requires [`elan`](https://github.com/leanprover/elan) (the Lean version
manager); the toolchain (`lean-toolchain`) and the exact Mathlib commit
(`lake-manifest.json`) are pinned.

```sh
lake exe cache get      # fetch prebuilt Mathlib oleans (no local Mathlib build)
lake build              # elaborate both proofs; prints the #print axioms audits
```

A successful `lake build` *is* the verification: Lean's kernel accepts
the proof terms. To regenerate the Lean sources from the Rust program:

```sh
python3 ../lean_gen.py  # re-emits Correct.lean and Matrix.lean, with a
                        # non-commutative pre-check of all 9 outputs
```
