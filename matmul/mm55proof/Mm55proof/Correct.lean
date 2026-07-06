/-
Copyright (c) 2026 Greg Sidebottom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom
-/
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# The 55-addition, 23-multiplication scheme computes 3×3 matrix multiplication

Machine-checked correctness of the rank-23 scheme of de Groote class
`i19w225c4efh` (fewer additions than any previously published rank-23
3×3 scheme; the prior record was 56).  Generated from `src/mm55.rs`
by `matmul/lean_gen.py`.

The statement is over a **general, not-necessarily-commutative** ring
`R`: every product keeps its left factor on the left, so this certifies
a genuine bilinear algorithm that applies recursively to block matrices.
The 78 intermediate wires (`aw*`, `bw*`, `m*`, `cw*`) are the exact
straight-line program; `subst_vars` inlines them and `noncomm_ring`
verifies each of the 9 outputs equals `∑ₖ aᵢₖ bₖⱼ`.
-/

namespace Matmul55

variable {R : Type _} [Ring R]

/-- Each of the 9 outputs of the 55-addition scheme equals the
corresponding entry of the matrix product `A · B`, over any ring. -/
theorem correct
    (a11 a12 a13 a21 a22 a23 a31 a32 a33
     b11 b12 b13 b21 b22 b23 b31 b32 b33 : R)
    (aw0 aw1 aw2 aw3 aw4 aw5 aw6 aw7 aw8 aw9 aw10 aw11
     aw12 bw0 bw1 bw2 bw3 bw4 bw5 bw6 bw7 bw8 bw9 bw10
     bw11 bw12 bw13 m1 m2 m3 m4 m5 m6 m7 m8 m9
     m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21
     m22 m23 cw0 cw1 cw2 cw3 cw4 cw5 cw6 cw7 cw8 cw9
     cw10 cw11 cw12 cw13 cw14 cw15 cw16 cw17 cw18 cw19 cw20 cw21
     cw22 cw23 cw24 cw25 cw26 cw27 : R)
    (haw0 : aw0 = a13 - a23)
    (haw1 : aw1 = a11 - aw0)
    (haw2 : aw2 = a12 + aw1)
    (haw3 : aw3 = aw2 - a23)
    (haw4 : aw4 = aw2 - a22)
    (haw5 : aw5 = a33 + aw3)
    (haw6 : aw6 = aw5 - a12)
    (haw7 : aw7 = aw4 - a21)
    (haw8 : aw8 = a31 + aw7)
    (haw9 : aw9 = a32 + aw8)
    (haw10 : aw10 = aw5 - a32)
    (haw11 : aw11 = a21 - a31)
    (haw12 : aw12 = aw1 - aw11)
    (hbw0 : bw0 = b13 + b33)
    (hbw1 : bw1 = b11 + b31)
    (hbw2 : bw2 = b11 - b21)
    (hbw3 : bw3 = b11 + b13)
    (hbw4 : bw4 = b23 + b33)
    (hbw5 : bw5 = b13 + bw2)
    (hbw6 : bw6 = bw2 - bw4)
    (hbw7 : bw7 = bw5 - b23)
    (hbw8 : bw8 = b32 + bw1)
    (hbw9 : bw9 = b12 + bw8)
    (hbw10 : bw10 = bw8 - bw6)
    (hbw11 : bw11 = b22 + bw10)
    (hbw12 : bw12 = bw10 - b21)
    (hbw13 : bw13 = bw12 - b23)
    (hm1 : m1 = aw2 * bw10)
    (hm2 : m2 = aw8 * bw5)
    (hm3 : m3 = a11 * bw0)
    (hm4 : m4 = a32 * b22)
    (hm5 : m5 = a11 * bw9)
    (hm6 : m6 = aw6 * bw4)
    (hm7 : m7 = aw10 * b23)
    (hm8 : m8 = a33 * b31)
    (hm9 : m9 = aw9 * b21)
    (hm10 : m10 = aw1 * bw6)
    (hm11 : m11 = a33 * b32)
    (hm12 : m12 = aw3 * bw13)
    (hm13 : m13 = a23 * b32)
    (hm14 : m14 = aw7 * bw3)
    (hm15 : m15 = a21 * b12)
    (hm16 : m16 = a31 * b12)
    (hm17 : m17 = a31 * b13)
    (hm18 : m18 = aw0 * bw1)
    (hm19 : m19 = aw5 * bw12)
    (hm20 : m20 = aw12 * bw2)
    (hm21 : m21 = a12 * bw11)
    (hm22 : m22 = a22 * b22)
    (hm23 : m23 = aw4 * bw7)
    (hcw0 : cw0 = m6 - m19)
    (hcw1 : cw1 = cw0 + m11)
    (hcw2 : cw2 = m8 + cw1)
    (hcw3 : cw3 = -(m12 + cw2))
    (hcw4 : cw4 = -(m17 + cw3))
    (hcw5 : cw5 = m2 + cw4)
    (hcw6 : cw6 = m1 - m13)
    (hcw7 : cw7 = cw6 + m10)
    (hcw8 : cw8 = -(m14 + m12))
    (hcw9 : cw9 = cw8 + cw5)
    (hcw10 : cw10 = m18 + cw7)
    (hcw11 : cw11 = cw2 + cw10)
    (hcw12 : cw12 = m5 + m21)
    (hcw13 : cw13 = cw12 - cw10)
    (hcw14 : cw14 = m3 + cw3)
    (hcw15 : cw15 = cw7 - m20)
    (hcw16 : cw16 = cw15 + cw9)
    (hcw17 : cw17 = m15 + m22)
    (hcw18 : cw18 = cw17 + m13)
    (hcw19 : cw19 = m23 - cw5)
    (hcw20 : cw20 = cw19 - m10)
    (hcw21 : cw21 = cw20 + m20)
    (hcw22 : cw22 = m9 - cw1)
    (hcw23 : cw23 = cw22 + cw9)
    (hcw24 : cw24 = m4 + m16)
    (hcw25 : cw25 = cw24 + m11)
    (hcw26 : cw26 = m6 - m7)
    (hcw27 : cw27 = cw26 - cw4) :
      cw11 = a11 * b11 + a12 * b21 + a13 * b31 ∧
      cw13 = a11 * b12 + a12 * b22 + a13 * b32 ∧
      cw14 = a11 * b13 + a12 * b23 + a13 * b33 ∧
      cw16 = a21 * b11 + a22 * b21 + a23 * b31 ∧
      cw18 = a21 * b12 + a22 * b22 + a23 * b32 ∧
      cw21 = a21 * b13 + a22 * b23 + a23 * b33 ∧
      cw23 = a31 * b11 + a32 * b21 + a33 * b31 ∧
      cw25 = a31 * b12 + a32 * b22 + a33 * b32 ∧
      cw27 = a31 * b13 + a32 * b23 + a33 * b33 := by
  subst_vars
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (first | noncomm_ring | abel)

end Matmul55

-- Axiom audit: elaborating this prints the axiom dependencies; a valid
-- proof shows only Lean's standard axioms (no `sorryAx`).
#print axioms Matmul55.correct
