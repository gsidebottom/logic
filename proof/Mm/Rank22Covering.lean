/-
Copyright (c) 2026 Greg Sidebottom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases

/-!
# Covering lemma for the rank-22 root strata (F₂)

A 22-product scheme is a triple of maps `α β γ : Fin 22 → M₃(F₂)`
satisfying the Brent equations. The symmetry group — product
relabeling `S₂₂` and the A-side sandwich `(U, V) ∈ GL₃(F₂)²` acting by

  `α ↦ Uᵀ ⬝ α ⬝ Vᵀ,  β ↦ V⁻ᵀ ⬝ β,  γ ↦ U⁻¹ ⬝ γ`

— preserves the Brent equations. The root strata split on the minimal
α-rank; the covering theorem says every Brent solution maps into one:

  S0: some product is dead (an α, β, or γ is 0)
  S1: some α has rank 1; witness canonicalized to `E₁₁` in slot 0
  S2: all α-ranks ≥ 2; witness canonicalized to `diag (1, 1, 0)`
  S3: all α invertible; witness canonicalized to `1`

Each stratum's emptiness is then a per-stratum SAT certificate
(`matmul/r22/S*.cnf`, SR proofs via the satsuma pipeline); this file
carries the symmetry side of the argument. The gate script
`matmul/r22/strata.py --selftest` checks the same action numerically
(Laderman canonicalizes with Brent preserved).

Proof status: statements fixed; `sorry`-stubbed pending the mathlib
plumbing (rank normal forms over `ZMod 2`, sum reindexing).
-/

namespace Rank22

open Matrix

abbrev F2 : Type := ZMod 2
abbrev M3 : Type := Matrix (Fin 3) (Fin 3) F2

/-- The Brent equations for a 22-product 3×3 scheme over `F₂`. -/
def BrentHolds (α β γ : Fin 22 → M3) : Prop :=
  ∀ a b c d p q : Fin 3,
    (∑ m : Fin 22, α m a b * β m c d * γ m p q) =
      if b = c ∧ a = p ∧ d = q then 1 else 0

/-- Product relabeling preserves the Brent equations. -/
theorem brent_perm (α β γ : Fin 22 → M3) (σ : Equiv.Perm (Fin 22))
    (h : BrentHolds α β γ) : BrentHolds (α ∘ σ) (β ∘ σ) (γ ∘ σ) := by
  intro a b c d p q
  simpa [Function.comp] using
    (Fintype.sum_equiv σ _ _ (fun m ↦ rfl)).trans (h a b c d p q)

/-- The A-side sandwich action on a scheme triple. -/
noncomputable def act (U V : M3) (α β γ : Fin 22 → M3) :
    (Fin 22 → M3) × (Fin 22 → M3) × (Fin 22 → M3) :=
  (fun m ↦ Uᵀ * α m * Vᵀ,
   fun m ↦ (V⁻¹)ᵀ * β m,
   fun m ↦ U⁻¹ * γ m)

/-- The sandwich action preserves the Brent equations (invertible U, V).
Numerically gated by `strata.py --selftest` (Laderman round-trip). -/
theorem brent_act (U V : M3) (hU : IsUnit U.det) (hV : IsUnit V.det)
    (α β γ : Fin 22 → M3) (h : BrentHolds α β γ) :
    BrentHolds (act U V α β γ).1 (act U V α β γ).2.1 (act U V α β γ).2.2 := by
  sorry

/-- Every rank-1 matrix over `F₂` is `U ⬝ E₁₁ ⬝ V` for invertible `U, V`;
equivalently a witness can be canonicalized to `E₁₁`. -/
theorem rank1_canonical (M : M3) (h : Matrix.rank M = 1) :
    ∃ U V : M3, IsUnit U.det ∧ IsUnit V.det ∧
      Uᵀ * M * Vᵀ = Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]] := by
  sorry

/-- Rank-2 canonical form `diag (1, 1, 0)`. -/
theorem rank2_canonical (M : M3) (h : Matrix.rank M = 2) :
    ∃ U V : M3, IsUnit U.det ∧ IsUnit V.det ∧
      Uᵀ * M * Vᵀ = Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]] := by
  sorry

/-- The root-strata covering theorem: every Brent solution maps, under
relabeling and the sandwich action, into stratum S0, S1, S2, or S3. -/
theorem covering (α β γ : Fin 22 → M3) (h : BrentHolds α β γ) :
    -- S0: dead product
    (∃ m, α m = 0 ∨ β m = 0 ∨ γ m = 0) ∨
    -- S1/S2/S3: a group element lands the witness in canonical form
    (∃ σ : Equiv.Perm (Fin 22), ∃ U V : M3, IsUnit U.det ∧ IsUnit V.det ∧
      ((act U V (α ∘ σ) (β ∘ σ) (γ ∘ σ)).1 0 =
          Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]] ∨
       ((∀ m, Matrix.rank ((act U V (α ∘ σ) (β ∘ σ) (γ ∘ σ)).1 m) ≥ 2) ∧
        (act U V (α ∘ σ) (β ∘ σ) (γ ∘ σ)).1 0 =
          Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]]) ∨
       ((∀ m, IsUnit (Matrix.det ((act U V (α ∘ σ) (β ∘ σ) (γ ∘ σ)).1 m))) ∧
        (act U V (α ∘ σ) (β ∘ σ) (γ ∘ σ)).1 0 = 1))) := by
  sorry

end Rank22
