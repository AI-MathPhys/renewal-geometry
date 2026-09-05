/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Canonical endpoint-coherence defect and its intrinsic record
  (`thm:endpoint-coherence-defect` and
  `thm:endpoint-defect-record`, Gran-Tensor manuscript)

* `endpoint_coherence_defect`: for the two endpoint-sheet
  isometries `V₀, V₁` with visibility `C = V₀ᴴV₁` and defect
  `𝔻 = 1 - CᴴC`:
  (i) the boxed column decomposition `V₁ = V₀C + L` with
      `V₀ᴴL = 0` and `LᴴL = 𝔻` (hence `𝔻 ⪰ 0`);
  (ii) the boxed joint-carrier source isometry
      `J₁ = (C, 𝔻^{1/2})ᵀ` satisfies `J₁ᴴJ₁ = 1`;
  (iii) full nondemolition exactly when `C = 1`
      (`C = 1 ↔ V₁ = V₀`).

* `endpoint_defect_record`: (i) every unitary commuting with
  `𝔻` preserves each eigenspace of `𝔻` (the spectral PVM is
  the finest invariant sharp record); (ii) on a scalar sector
  `𝔻 = δ·1` every unitary commutes — the defect contains no
  basis-free classical point record.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:endpoint-coherence-defect`. -/
theorem endpoint_coherence_defect {H K : Type*} [Fintype H]
    [Fintype K] [DecidableEq H]
    (V₀ V₁ : Matrix K H ℂ) (h₀ : V₀ᴴ * V₀ = 1)
    (h₁ : V₁ᴴ * V₁ = 1) :
    -- (i) the boxed column decomposition
    (V₁ = V₀ * (V₀ᴴ * V₁) + (V₁ - V₀ * (V₀ᴴ * V₁)))
    ∧ V₀ᴴ * (V₁ - V₀ * (V₀ᴴ * V₁)) = 0
    ∧ (V₁ - V₀ * (V₀ᴴ * V₁))ᴴ * (V₁ - V₀ * (V₀ᴴ * V₁))
      = 1 - (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁)
    ∧ ((1 : Matrix H H ℂ)
        - (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁)).PosSemidef
    -- (ii) the joint-carrier source isometry
    ∧ (fromRows (V₀ᴴ * V₁)
        (CFC.sqrt (1 - (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁))))ᴴ
      * fromRows (V₀ᴴ * V₁)
          (CFC.sqrt (1 - (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁))) = 1
    -- (iii) full nondemolition exactly when `C = 1`
    ∧ (V₀ᴴ * V₁ = 1 ↔ V₁ = V₀) := by
  have hL0 : V₀ᴴ * (V₁ - V₀ * (V₀ᴴ * V₁)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h₀,
      Matrix.one_mul, sub_self]
  have h2 : (V₀ * (V₀ᴴ * V₁))ᴴ * (V₀ * (V₀ᴴ * V₁))
      = (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁) := by
    rw [Matrix.conjTranspose_mul]
    calc (V₀ᴴ * V₁)ᴴ * V₀ᴴ * (V₀ * (V₀ᴴ * V₁))
        = (V₀ᴴ * V₁)ᴴ * ((V₀ᴴ * V₀) * (V₀ᴴ * V₁)) := by
          simp only [Matrix.mul_assoc]
      _ = (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁) := by
          rw [h₀, Matrix.one_mul]
  have h3 : (V₀ * (V₀ᴴ * V₁))ᴴ * V₁
      = (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁) := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have h4 : V₁ᴴ * (V₀ * (V₀ᴴ * V₁))
      = (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁) := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hLL : (V₁ - V₀ * (V₀ᴴ * V₁))ᴴ
      * (V₁ - V₀ * (V₀ᴴ * V₁))
      = 1 - (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁) := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul,
      Matrix.mul_sub, h₁]
    rw [h2, h3, h4]
    abel
  have hDpsd : ((1 : Matrix H H ℂ)
      - (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁)).PosSemidef := by
    rw [← hLL]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  refine ⟨by abel, hL0, hLL, hDpsd, ?_, ?_⟩
  · rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, sqrt_isHermitian,
      sqrt_mul_self_eq _ hDpsd]
    abel
  · constructor
    · intro hC
      have h := hLL
      rw [hC, Matrix.conjTranspose_one, Matrix.one_mul,
        sub_self] at h
      have hL := Matrix.conjTranspose_mul_self_eq_zero.mp h
      have := sub_eq_zero.mp hL
      rw [Matrix.mul_one] at this
      exact this
    · intro hV
      rw [hV, h₀]

/-- `thm:endpoint-defect-record`. -/
theorem endpoint_defect_record {H : Type*} [Fintype H]
    [DecidableEq H]
    (D U : Matrix H H ℂ) (hU : U * D = D * U) :
    -- (i) commuting unitaries preserve every eigenspace
    (∀ (δ : ℂ) (v : H → ℂ), D *ᵥ v = δ • v →
      D *ᵥ (U *ᵥ v) = δ • (U *ᵥ v))
    -- (ii) a scalar sector commutes with every unitary
    ∧ (∀ (δ : ℂ) (W : Matrix H H ℂ),
        W * (δ • (1 : Matrix H H ℂ))
          = (δ • (1 : Matrix H H ℂ)) * W) := by
  constructor
  · intro δ v hv
    rw [Matrix.mulVec_mulVec, ← hU, ← Matrix.mulVec_mulVec,
      hv, Matrix.mulVec_smul]
  · intro δ W
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]

end NCG
