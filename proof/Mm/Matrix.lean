/-
Copyright (c) 2026 Greg Sidebottom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom
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
matrices: the exact straight-line program of `src/mm55.rs`, in four
sections — `A_in` (13 additions on the `A` side), `B_in` (14 on the
`B` side), `M` (the 23 multiplies, each one `A`-combination times one
`B`-combination), and `C_out` (28 additions recombining the products
into the 9 outputs). -/
def scheme (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  -- 13 adds on the A input side
  let A_in : Fin 13 → R :=
    let aw0 := A 0 2 - A 1 2
    let aw1 := A 0 0 - aw0
    let aw2 := A 0 1 + aw1
    let aw3 := aw2 - A 1 2
    let aw4 := aw2 - A 1 1
    let aw5 := A 2 2 + aw3
    let aw6 := aw5 - A 0 1
    let aw7 := aw4 - A 1 0
    let aw8 := A 2 0 + aw7
    let aw9 := A 2 1 + aw8
    let aw10 := aw5 - A 2 1
    let aw11 := A 1 0 - A 2 0
    let aw12 := aw1 - aw11
    ![aw0, aw1, aw2, aw3, aw4, aw5, aw6, aw7, aw8,
      aw9, aw10, aw11, aw12]
  -- 14 adds on the B input side
  let B_in : Fin 14 → R :=
    let bw0 := B 0 2 + B 2 2
    let bw1 := B 0 0 + B 2 0
    let bw2 := B 0 0 - B 1 0
    let bw3 := B 0 0 + B 0 2
    let bw4 := B 1 2 + B 2 2
    let bw5 := B 0 2 + bw2
    let bw6 := bw2 - bw4
    let bw7 := bw5 - B 1 2
    let bw8 := B 2 1 + bw1
    let bw9 := B 0 1 + bw8
    let bw10 := bw8 - bw6
    let bw11 := B 1 1 + bw10
    let bw12 := bw10 - B 1 0
    let bw13 := bw12 - B 1 2
    ![bw0, bw1, bw2, bw3, bw4, bw5, bw6, bw7, bw8,
      bw9, bw10, bw11, bw12, bw13]
  -- 23 multiplies
  let M : Fin 23 → R :=
    ![A_in 2 * B_in 10, A_in 8 * B_in 5, A 0 0 * B_in 0,
      A 2 1 * B 1 1, A 0 0 * B_in 9, A_in 6 * B_in 4,
      A_in 10 * B 1 2, A 2 2 * B 2 0, A_in 9 * B 1 0,
      A_in 1 * B_in 6, A 2 2 * B 2 1, A_in 3 * B_in 13,
      A 1 2 * B 2 1, A_in 7 * B_in 3, A 1 0 * B 0 1,
      A 2 0 * B 0 1, A 2 0 * B 0 2, A_in 0 * B_in 1,
      A_in 5 * B_in 12, A_in 12 * B_in 2, A 0 1 * B_in 11,
      A 1 1 * B 1 1, A_in 4 * B_in 7]
  -- 28 adds on the C output side
  let C_out : Fin 28 → R :=
    let cw0 := M 5 - M 18
    let cw1 := cw0 + M 10
    let cw2 := M 7 + cw1
    let cw3 := -(M 11 + cw2)
    let cw4 := -(M 16 + cw3)
    let cw5 := M 1 + cw4
    let cw6 := M 0 - M 12
    let cw7 := cw6 + M 9
    let cw8 := -(M 13 + M 11)
    let cw9 := cw8 + cw5
    let cw10 := M 17 + cw7
    let cw11 := cw2 + cw10
    let cw12 := M 4 + M 20
    let cw13 := cw12 - cw10
    let cw14 := M 2 + cw3
    let cw15 := cw7 - M 19
    let cw16 := cw15 + cw9
    let cw17 := M 14 + M 21
    let cw18 := cw17 + M 12
    let cw19 := M 22 - cw5
    let cw20 := cw19 - M 9
    let cw21 := cw20 + M 19
    let cw22 := M 8 - cw1
    let cw23 := cw22 + cw9
    let cw24 := M 3 + M 15
    let cw25 := cw24 + M 10
    let cw26 := M 5 - M 6
    let cw27 := cw26 - cw4
    ![cw0, cw1, cw2, cw3, cw4, cw5, cw6, cw7, cw8,
      cw9, cw10, cw11, cw12, cw13, cw14, cw15, cw16, cw17,
      cw18, cw19, cw20, cw21, cw22, cw23, cw24, cw25, cw26,
      cw27]
  !![C_out 11, C_out 13, C_out 14;
     C_out 16, C_out 18, C_out 21;
     C_out 23, C_out 25, C_out 27]

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
