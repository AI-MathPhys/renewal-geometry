/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GramHelpers

/-!
# Efficient connected-score short and refinement innovations
  (`thm:efficient-connected-score` and
  `thm:interaction-refinement-innovations`,
  Gran-Tensor manuscript)

* `efficient_connected_score`: the connected Gram
  `ℂ_e = ((I-P)F)ᴴ((I-P)F)` with `P` the nuisance projection
  `Z(ZᴴZ)⁻¹Zᴴ`:
  (i) the boxed short formula
      `ℂ_e = FᴴF - (ZᴴF)ᴴ(ZᴴZ)⁻¹(ZᴴF)`;
  (ii) positivity;
  (iii) vanishing exactly when every joint score lies in the
      nuisance span (`(I-P)F = 0`);
  (iv) frame invariance up to congruence
      (`ℂ(F·U) = Uᴴ·ℂ(F)·U`).

* `interaction_refinement_innovations`: the boxed
  explanation identity `ℂ₀ = ℂ₁ + Fᴴ(P₁-P₀)F` for an
  enlarged nuisance projection, positivity of the explained
  part for nested orthogonal projections `P₀ ⪯ P₁`, and
  exact restriction along a response-row inclusion.
-/

open Matrix
open scoped ComplexOrder

set_option linter.unusedSimpArgs false

namespace NCG

/-- `thm:efficient-connected-score`. -/
theorem efficient_connected_score {H k l : Type*}
    [Fintype H] [Fintype k] [Fintype l] [DecidableEq H]
    [DecidableEq l] (F : Matrix H k ℂ) (Z : Matrix H l ℂ)
    [Invertible (Zᴴ * Z)] :
    -- (i) the boxed short formula
    ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * F)ᴴ
        * ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * F)
      = Fᴴ * F - (Zᴴ * F)ᴴ * (Zᴴ * Z)⁻¹ * (Zᴴ * F)
    -- (ii) positivity
    ∧ (((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * F)ᴴ
        * ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * F)).PosSemidef
    -- (iii) vanishing ↔ scores in the nuisance span
    ∧ (((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * F)ᴴ
          * ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * F) = 0
        ↔ (1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * F = 0)
    -- (iv) frame invariance up to congruence
    ∧ (∀ U : Matrix k k ℂ,
        ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * (F * U))ᴴ
            * ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * (F * U))
          = Uᴴ * (((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * F)ᴴ
              * ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * F)) * U) := by
  have hGH : (Zᴴ * Z)ᴴ = Zᴴ * Z := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hGinvH : ((Zᴴ * Z)⁻¹)ᴴ = (Zᴴ * Z)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hGinvH, Matrix.conjTranspose_conjTranspose,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    simp only [Matrix.mul_assoc, proj_cancel Z]
    abel
  · exact Matrix.posSemidef_conjTranspose_mul_self _
  · exact Matrix.conjTranspose_mul_self_eq_zero
  · intro U
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- `thm:interaction-refinement-innovations`. -/
theorem interaction_refinement_innovations {H k m : Type*}
    [Fintype H] [Fintype k] [DecidableEq H]
    (F : Matrix H k ℂ) (P0 P1 : Matrix H H ℂ)
    (h0H : P0ᴴ = P0) (h1H : P1ᴴ = P1)
    (h02 : P0 * P0 = P0) (h12 : P1 * P1 = P1)
    (hnest : P1 * P0 = P0)
    (j : Matrix k m ℂ) :
    -- boxed explanation identity `ℂ₀ = ℂ₁ + Fᴴ(P₁-P₀)F`
    Fᴴ * (1 - P0) * F
      = Fᴴ * (1 - P1) * F + Fᴴ * (P1 - P0) * F
    -- the explained part is positive
    ∧ (Fᴴ * (P1 - P0) * F).PosSemidef
    -- exact restriction along a response-row inclusion
    ∧ jᴴ * (Fᴴ * (1 - P0) * F) * j
      = (F * j)ᴴ * (1 - P0) * (F * j) := by
  have h01 : P0 * P1 = P0 := by
    have h := congrArg conjTranspose hnest
    rwa [Matrix.conjTranspose_mul, h0H, h1H] at h
  have hDH : (P1 - P0)ᴴ = P1 - P0 := by
    rw [Matrix.conjTranspose_sub, h0H, h1H]
  have hD2 : (P1 - P0) * (P1 - P0) = P1 - P0 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, h02, h12,
      hnest, h01]
    abel
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul]
    abel
  · have hfac : Fᴴ * (P1 - P0) * F
        = ((P1 - P0) * F)ᴴ * ((P1 - P0) * F) := by
      rw [Matrix.conjTranspose_mul, hDH]
      calc Fᴴ * (P1 - P0) * F
          = Fᴴ * ((P1 - P0) * ((P1 - P0) * F)) := by
            rw [← Matrix.mul_assoc (P1 - P0) (P1 - P0), hD2,
              Matrix.mul_assoc]
        _ = Fᴴ * (P1 - P0) * ((P1 - P0) * F) := by
            simp only [Matrix.mul_assoc]
    rw [hfac]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end NCG
