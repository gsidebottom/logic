/-
Copyright (c) 2026 Greg Sidebottom and Claude Fable 5. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom, Claude Fable 5
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# The 55-addition scheme equals the Mathlib matrix product

`scheme A B` runs the 55-addition, 23-multiplication straight-line
program on two `3×3` matrices over any ring `R`, and `scheme_eq_mul`
proves it equals Mathlib's own matrix product `A * B`.  This packages
`Matmul55.correct` in Mathlib's native `Matrix` API.
-/

namespace Matmul55

variable {R : Type _} [Ring R]

/-- The 55-addition, 23-multiplication scheme as a map on `3×3`
matrices: the exact straight-line program of `src/mm55.rs`, reading the
inputs from `A`, `B` and assembling the 9 outputs into a matrix. -/
def scheme (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  let a11 := A 0 0
  let a12 := A 0 1
  let a13 := A 0 2
  let a21 := A 1 0
  let a22 := A 1 1
  let a23 := A 1 2
  let a31 := A 2 0
  let a32 := A 2 1
  let a33 := A 2 2
  let b11 := B 0 0
  let b12 := B 0 1
  let b13 := B 0 2
  let b21 := B 1 0
  let b22 := B 1 1
  let b23 := B 1 2
  let b31 := B 2 0
  let b32 := B 2 1
  let b33 := B 2 2
  let aw0 := a13 - a23
  let aw1 := a11 - aw0
  let aw2 := a12 + aw1
  let aw3 := aw2 - a23
  let aw4 := aw2 - a22
  let aw5 := a33 + aw3
  let aw6 := aw5 - a12
  let aw7 := aw4 - a21
  let aw8 := a31 + aw7
  let aw9 := a32 + aw8
  let aw10 := aw5 - a32
  let aw11 := a21 - a31
  let aw12 := aw1 - aw11
  let bw0 := b13 + b33
  let bw1 := b11 + b31
  let bw2 := b11 - b21
  let bw3 := b11 + b13
  let bw4 := b23 + b33
  let bw5 := b13 + bw2
  let bw6 := bw2 - bw4
  let bw7 := bw5 - b23
  let bw8 := b32 + bw1
  let bw9 := b12 + bw8
  let bw10 := bw8 - bw6
  let bw11 := b22 + bw10
  let bw12 := bw10 - b21
  let bw13 := bw12 - b23
  let m1 := aw2 * bw10
  let m2 := aw8 * bw5
  let m3 := a11 * bw0
  let m4 := a32 * b22
  let m5 := a11 * bw9
  let m6 := aw6 * bw4
  let m7 := aw10 * b23
  let m8 := a33 * b31
  let m9 := aw9 * b21
  let m10 := aw1 * bw6
  let m11 := a33 * b32
  let m12 := aw3 * bw13
  let m13 := a23 * b32
  let m14 := aw7 * bw3
  let m15 := a21 * b12
  let m16 := a31 * b12
  let m17 := a31 * b13
  let m18 := aw0 * bw1
  let m19 := aw5 * bw12
  let m20 := aw12 * bw2
  let m21 := a12 * bw11
  let m22 := a22 * b22
  let m23 := aw4 * bw7
  let cw0 := m6 - m19
  let cw1 := cw0 + m11
  let cw2 := m8 + cw1
  let cw3 := -(m12 + cw2)
  let cw4 := -(m17 + cw3)
  let cw5 := m2 + cw4
  let cw6 := m1 - m13
  let cw7 := cw6 + m10
  let cw8 := -(m14 + m12)
  let cw9 := cw8 + cw5
  let cw10 := m18 + cw7
  let cw11 := cw2 + cw10
  let cw12 := m5 + m21
  let cw13 := cw12 - cw10
  let cw14 := m3 + cw3
  let cw15 := cw7 - m20
  let cw16 := cw15 + cw9
  let cw17 := m15 + m22
  let cw18 := cw17 + m13
  let cw19 := m23 - cw5
  let cw20 := cw19 - m10
  let cw21 := cw20 + m20
  let cw22 := m9 - cw1
  let cw23 := cw22 + cw9
  let cw24 := m4 + m16
  let cw25 := cw24 + m11
  let cw26 := m6 - m7
  let cw27 := cw26 - cw4
  !![cw11, cw13, cw14;
     cw16, cw18, cw21;
     cw23, cw25, cw27]

-- `scheme` unfolds to a ~100-binding straight-line program, so a single
-- elaboration exceeds the default heartbeat budget; raise it for this proof.
set_option maxHeartbeats 1600000 in
-- Plain `simp` (below) evaluates the concrete `!![..] i j` indexing via
-- Mathlib's matrix simprocs; the explicit `simp only` lemma set for this is
-- version-fragile, so we accept the flexible-`simp` lint here.
set_option linter.flexible false in
/-- The scheme computes the matrix product, in Mathlib's own terms. -/
theorem scheme_eq_mul (A B : Matrix (Fin 3) (Fin 3) R) :
    scheme A B = A * B := by
  simp only [scheme]                    -- unfold the SLP once (not per goal)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | noncomm_ring | abel

end Matmul55

#print axioms Matmul55.scheme_eq_mul
