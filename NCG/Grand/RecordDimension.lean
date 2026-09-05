/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Protected-record dimension obstruction
  (`thm:record-dimension-obstruction`, Gran-Tensor manuscript)

* `record_dimension_obstruction`: `r` mutually orthogonal
  nonzero self-adjoint point-Read projections force every
  faithful carrier to have dimension at least `r` — so a growing
  protected record admits no single finite faithful carrier.

Rendering disclosed: faithfulness is rendered by the point Reads
acting as nonzero maps on the carrier; the chronology clause
`r_X ≥ X` is the instantiation on pairwise-separated
chronological point Reads.
-/

open InnerProductSpace

namespace NCG

/-- `thm:record-dimension-obstruction`: orthogonal nonzero
point Reads force carrier dimension at least `r`. -/
theorem record_dimension_obstruction {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {r : ℕ}
    (P : Fin r → (V →ₗ[ℂ] V))
    (hsa : ∀ i (x y : V), ⟪P i x, y⟫_ℂ = ⟪x, P i y⟫_ℂ)
    (horth : ∀ i j, i ≠ j → P i ∘ₗ P j = 0)
    (hne : ∀ i, P i ≠ 0) :
    r ≤ Module.finrank ℂ V := by
  -- pick a nonzero vector in each range
  have hex : ∀ i, ∃ x, P i x ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    exact hne i (LinearMap.ext fun x => h x)
  choose x hx using hex
  set v : Fin r → V := fun i => P i (x i) with hv
  have hvo : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = 0 := by
    intro i j hij
    rw [hv]
    calc ⟪P i (x i), P j (x j)⟫_ℂ
        = ⟪x i, P i (P j (x j))⟫_ℂ := hsa i _ _
      _ = 0 := by
          have h0 : P i (P j (x j)) = 0 := by
            have := congrArg (fun f : V →ₗ[ℂ] V => f (x j))
              (horth i j hij)
            simpa using this
          rw [h0, inner_zero_right]
  -- normalize to an orthonormal family
  have hvne : ∀ i, v i ≠ 0 := fun i => hx i
  set u : Fin r → V := fun i => ((‖v i‖ : ℂ))⁻¹ • v i with hu
  have huon : Orthonormal ℂ u := by
    constructor
    · intro i
      rw [hu]
      simp only [norm_smul, norm_inv, Complex.norm_real,
        norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hvne i))
    · intro i j hij
      rw [hu]
      simp only [inner_smul_left, inner_smul_right]
      rw [hvo i j hij, mul_zero, mul_zero]
  have hcard := huon.linearIndependent.fintype_card_le_finrank
  simpa using hcard

end NCG
