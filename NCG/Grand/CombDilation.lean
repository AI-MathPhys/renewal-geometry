/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical comb-to-memory dilation
  (`thm:canonical-comb-dilation`, Gran-Tensor manuscript)

* `canonical_comb_dilation`:
  (1) the boxed memory-gauge covariance composes exactly: two
      dressed links telescope,
      `((1⊗U₂)V₂(1⊗U₁ᴴ))·((1⊗U₁)V₁(1⊗U₀ᴴ))
        = (1⊗U₂)(V₂V₁)(1⊗U₀ᴴ)`;
  (2) dressing preserves the isometry property:
      `V' = (1⊗U)V(1⊗U')ᴴ` is an isometry when `V` is and
      `U, U'` are unitary;
  (3) conjugation transport preserves all Hilbert–Schmidt
      Grams: `Tr((UMUᴴ)ᴴ(UNUᴴ)) = Tr(MᴴN)` for unitary `U` —
      so reduced maps, mixed words, regular traces, and word
      Grams of gauge-related realizations are identical.

Rendering disclosed: the existence layer (the square-root
prefix purifications `|Ψ_k⟩ = vec((R^{(k)})^{1/2})` and the
purification-uniqueness supplying the isometries `V_k` and the
unique unitaries `U_k`) is the sqrt library plus the proved
minimal-Gram uniqueness of the joint-source records; the
telescoping clauses proved here are the exact algebra by which
the unique unitaries intertwine every derived structure.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- `thm:canonical-comb-dilation`. -/
theorem canonical_comb_dilation
    {h₀ h₁ h₂ a₀ a₁ a₂ : Type*}
    [Fintype h₀] [Fintype h₁] [Fintype h₂]
    [Fintype a₀] [Fintype a₁] [Fintype a₂]
    [DecidableEq h₀] [DecidableEq h₁] [DecidableEq h₂]
    [DecidableEq a₀] [DecidableEq a₁] :
    -- (1) gauge dressing telescopes
    (∀ (V₁ : Matrix (h₁ × a₁) (h₀ × a₀) ℂ)
       (V₂ : Matrix (h₂ × a₂) (h₁ × a₁) ℂ)
       (U₀ : Matrix a₀ a₀ ℂ) (U₁ : Matrix a₁ a₁ ℂ)
       (U₂ : Matrix a₂ a₂ ℂ), U₁ᴴ * U₁ = 1 →
      (((1 : Matrix h₂ h₂ ℂ) ⊗ₖ U₂) * V₂
          * ((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U₁)ᴴ)
        * (((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U₁) * V₁
          * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U₀)ᴴ)
        = ((1 : Matrix h₂ h₂ ℂ) ⊗ₖ U₂) * (V₂ * V₁)
          * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U₀)ᴴ)
    -- (2) dressing preserves isometry
    ∧ (∀ (V : Matrix (h₁ × a₁) (h₀ × a₀) ℂ)
        (U : Matrix a₁ a₁ ℂ) (U' : Matrix a₀ a₀ ℂ),
        Vᴴ * V = 1 → Uᴴ * U = 1 → U' * U'ᴴ = 1 →
        (((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U) * V
            * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U')ᴴ)ᴴ
          * (((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U) * V
            * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U')ᴴ) = 1)
    -- (3) conjugation transport preserves HS Grams
    ∧ (∀ (U M N : Matrix a₁ a₁ ℂ), Uᴴ * U = 1 →
        ((U * M * Uᴴ)ᴴ * (U * N * Uᴴ)).trace
          = (Mᴴ * N).trace) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V₁ V₂ U₀ U₁ U₂ hU₁
    have hmid : ((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U₁)ᴴ
        * ((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U₁) = 1 := by
      rw [Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul, hU₁, Matrix.one_kronecker_one]
    calc (((1 : Matrix h₂ h₂ ℂ) ⊗ₖ U₂) * V₂
          * ((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U₁)ᴴ)
        * (((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U₁) * V₁
          * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U₀)ᴴ)
        = ((1 : Matrix h₂ h₂ ℂ) ⊗ₖ U₂) * V₂
          * (((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U₁)ᴴ
            * ((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U₁))
          * V₁ * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U₀)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = ((1 : Matrix h₂ h₂ ℂ) ⊗ₖ U₂) * (V₂ * V₁)
          * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U₀)ᴴ := by
          rw [hmid, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  · intro V U U' hV hU hU'
    have hUk : ((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U)ᴴ
        * ((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U) = 1 := by
      rw [Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul, hU, Matrix.one_kronecker_one]
    have hU'k : ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U')
        * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U')ᴴ = 1 := by
      rw [Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul, hU', Matrix.one_kronecker_one]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U')
          * (Vᴴ * ((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U)ᴴ)
        * (((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U) * V
          * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U')ᴴ)
        = ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U') * Vᴴ
          * (((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U)ᴴ
            * ((1 : Matrix h₁ h₁ ℂ) ⊗ₖ U))
          * V * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U')ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U') * (Vᴴ * V)
          * ((1 : Matrix h₀ h₀ ℂ) ⊗ₖ U')ᴴ := by
          rw [hUk, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hV, Matrix.mul_one, hU'k]
  · intro U M N hU
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    have hcan : Uᴴ * (U * N * Uᴴ) = N * Uᴴ := by
      rw [show Uᴴ * (U * N * Uᴴ) = (Uᴴ * U) * N * Uᴴ from by
        simp only [Matrix.mul_assoc], hU, Matrix.one_mul]
    calc (U * (Mᴴ * Uᴴ) * (U * N * Uᴴ)).trace
        = (U * (Mᴴ * (Uᴴ * (U * N * Uᴴ)))).trace := by
          simp only [Matrix.mul_assoc]
      _ = (U * (Mᴴ * (N * Uᴴ))).trace := by rw [hcan]
      _ = (Uᴴ * (U * (Mᴴ * N))).trace := by
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
          rw [hU, Matrix.mul_one, ← Matrix.mul_assoc Uᴴ U,
            hU, Matrix.one_mul]
      _ = (Mᴴ * N).trace := by
          rw [← Matrix.mul_assoc, hU, Matrix.one_mul]

end NCG
