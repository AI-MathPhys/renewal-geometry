/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Line-valued quantum action and covariant Einstein residual
  (`thm:SMST-line-valued-Einstein`, Gran-Tensor manuscript)

* `log_derivative_unique`: the connection one-form of a
  nowhere-zero amplitude — there is a unique `Ξ` with
  `∇𝒵 = Ξ⊗𝒵` (scalar rendering along any curve: `z' = Ξ·z`
  with `Ξ = z'/z`);
* `amplitude_polar`: the boxed polar splitting — every
  nowhere-zero amplitude factors as `𝒵 = e^{-𝒮_ℝ}·s` with
  `‖s‖ = 1` (`𝒮_ℝ = -log‖𝒵‖`);
* `covariant_residual_split`: the boxed covariant residual —
  for a positive-definite variation metric,
  `Δ_Ein^cov = ‖ℰ^ℝ‖²_{G⁻¹} + ‖𝗍_ph‖²_{G⁻¹} = 0` exactly when
  `ℰ^ℝ = 0` and `𝗍_ph = 0`: a real Einstein-source mismatch
  cannot cancel a phase stress.

Rendering disclosed: the line-bundle formulation (`dΞ = iΩ_ph`,
holonomy triviality as the existence criterion for a global
scalar effective action) is the manuscript's geometric layer;
the uniqueness of the logarithmic derivative, the polar
splitting, and the residual dichotomy are proved here.
-/

open Matrix

namespace NCG

/-- Unique connection coefficient of a nowhere-zero amplitude:
`z' = Ξ·z` has the unique solution `Ξ = z'/z`. -/
theorem log_derivative_unique (z z' : ℂ) (hz : z ≠ 0) :
    ∃! Ξ : ℂ, z' = Ξ * z := by
  refine ⟨z' / z, by field_simp, ?_⟩
  intro Ξ hΞ
  rw [hΞ, mul_div_cancel_right₀ _ hz]

/-- Boxed polar splitting: every nowhere-zero amplitude is
`e^{-𝒮}·s` with `‖s‖ = 1` and `𝒮 = -log‖𝒵‖`. -/
theorem amplitude_polar (z : ℂ) (hz : z ≠ 0) :
    ∃ S : ℝ, ∃ s : ℂ, ‖s‖ = 1
      ∧ z = Real.exp (-S) • s
      ∧ S = -Real.log ‖z‖ := by
  refine ⟨-Real.log ‖z‖, ‖z‖⁻¹ • z, ?_, ?_, rfl⟩
  · rw [norm_smul, norm_inv, norm_norm]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  · rw [neg_neg, Real.exp_log (norm_pos_iff.mpr hz),
      smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),
      one_smul]

open scoped ComplexOrder in
/-- Boxed covariant residual dichotomy: the sum of the two
`G⁻¹`-norms vanishes exactly when both sources vanish — a real
Einstein mismatch cannot cancel a phase stress. -/
theorem covariant_residual_split {n : Type*} [Fintype n]
    [DecidableEq n] (G : Matrix n n ℂ) (hG : G.PosDef)
    (E t : n → ℂ) :
    ((star E ⬝ᵥ G⁻¹.mulVec E).re
        + (star t ⬝ᵥ G⁻¹.mulVec t).re = 0)
      ↔ E = 0 ∧ t = 0 := by
  have hGinv : (G⁻¹).PosDef := hG.inv
  have hEnn : 0 ≤ (star E ⬝ᵥ G⁻¹.mulVec E).re := by
    rcases eq_or_ne E 0 with rfl | hE
    · simp
    · exact (hGinv.re_dotProduct_pos hE).le
  have htnn : 0 ≤ (star t ⬝ᵥ G⁻¹.mulVec t).re := by
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · exact (hGinv.re_dotProduct_pos ht).le
  constructor
  · intro h0
    constructor
    · by_contra hE
      have hpos : 0 < (star E ⬝ᵥ G⁻¹.mulVec E).re :=
        hGinv.re_dotProduct_pos hE
      linarith
    · by_contra ht
      have hpos : 0 < (star t ⬝ᵥ G⁻¹.mulVec t).re :=
        hGinv.re_dotProduct_pos ht
      linarith
  · rintro ⟨rfl, rfl⟩
    simp

end NCG
