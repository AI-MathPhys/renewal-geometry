/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PsdBlockSchurExact

/-!
# Affine quadratic common landing

Exact encoding of `thm:SMYM-affine-common-landing` (CY.14–CY.18).

The frozen source profiles `s_ℓ` (weighted by `√μ_ℓ`) are the rows of the source
synthesis `S : Matrix L d ℂ`, so that `G = ∑ μ_ℓ s_ℓ s_ℓ^* = S^* S`; the response
synthesis is `T = P S` for one physical self-adjoint slab `P`, giving
`C = ∑ μ_ℓ s_ℓ t_ℓ^* = S^* T` and `D = ∑ μ_ℓ t_ℓ t_ℓ^* = T^* T`.

* `triplet_eq` (CY.15): `(G, C, D) = (S^* S, S^* P S, S^* P² S)`, the literal
  Hankel–moment transfer triplet;
* `innovation_eq_gram` (CY.16): `𝕀 = D - C^* G^† C = R^* R` with
  `R = T - S G^† C` (rows `r_ℓ = t_ℓ - C^* G^† s_ℓ`);
* `symForm_eq` / `symForm_posSemidef` (CY.17): `G - ½(C + C^*) = S^*(I - P)S ⪰ 0`
  and `skewForm_eq_zero`: the skew form `(C - C^*)/2τ` vanishes for a self-adjoint slab;
* `residual_eq_zero_iff` / `triplet_congr` (CY.18): the residual
  `Δ = ∑ μ_ℓ ‖t⁽¹⁾_ℓ - t⁽²⁾_ℓ‖² = tr((T₁ - T₂)^*(T₁ - T₂))` vanishes exactly when the
  frozen response writers agree, and then the quadratic triplets agree.
-/

open Matrix NCG.GeometricThresholdBank NCG.SourceCoercivityInfluence NCG.PsdBlockSchur
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace SMYMAffineCommonLanding

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

variable {L d : Type*} [Fintype L] [Fintype d] [DecidableEq L] [DecidableEq d]
variable (S : Matrix L d ℂ) (P : Matrix L L ℂ)

/-- The source Gram `G = ∑ μ_ℓ s_ℓ s_ℓ^* = S^* S`. -/
def sourceGram : Matrix d d ℂ := Sᴴ * S

/-- The cross Gram `C = ∑ μ_ℓ s_ℓ t_ℓ^* = S^* (P S)`. -/
def crossGram : Matrix d d ℂ := Sᴴ * (P * S)

/-- The response Gram `D = ∑ μ_ℓ t_ℓ t_ℓ^* = (P S)^* (P S)`. -/
def responseGram : Matrix d d ℂ := (P * S)ᴴ * (P * S)

theorem sourceGram_posSemidef : (sourceGram S).PosSemidef := posSemidef_conjTranspose_mul_self S

/-- **(CY.15)**: the triplet is the literal Hankel–moment transfer triplet
`M_n = S^* P^n S`. -/
theorem triplet_eq (hP : P.IsHermitian) :
    sourceGram S = Sᴴ * P ^ 0 * S ∧ crossGram S P = Sᴴ * P ^ 1 * S ∧
      responseGram S P = Sᴴ * P ^ 2 * S := by
  refine ⟨by simp [sourceGram], by simp [crossGram, Matrix.mul_assoc], ?_⟩
  unfold responseGram
  rw [conjTranspose_mul, hP.eq, pow_two]
  simp only [Matrix.mul_assoc]

/-- **(CY.16)**: the first response innovation `𝕀 = D - C^* G^† C`. -/
noncomputable def innovation : Matrix d d ℂ :=
  responseGram S P - (crossGram S P)ᴴ * pinv (sourceGram_posSemidef S).1 * crossGram S P

/-- The residual profile `R = T - S G^† C` (rows `r_ℓ = t_ℓ - C^* G^† s_ℓ`). -/
noncomputable def residualProfile : Matrix L d ℂ :=
  P * S - S * pinv (sourceGram_posSemidef S).1 * crossGram S P

/-- **(CY.16)**: `𝕀 = R^* R = ∑ μ_ℓ r_ℓ r_ℓ^*`. -/
theorem innovation_eq_gram :
    innovation S P = (residualProfile S P)ᴴ * residualProfile S P := by
  have hJ := (pinv_isHermitian (sourceGram_posSemidef S).1).eq
  have hJGJ : ∀ X : Matrix d d ℂ, pinv (sourceGram_posSemidef S).1
      * (Sᴴ * (S * (pinv (sourceGram_posSemidef S).1 * X)))
      = pinv (sourceGram_posSemidef S).1 * X := by
    intro X
    calc pinv (sourceGram_posSemidef S).1 * (Sᴴ * (S * (pinv (sourceGram_posSemidef S).1 * X)))
        = (pinv (sourceGram_posSemidef S).1 * (Sᴴ * S) * pinv (sourceGram_posSemidef S).1) * X := by
          simp only [Matrix.mul_assoc]
      _ = (pinv (sourceGram_posSemidef S).1 * sourceGram S * pinv (sourceGram_posSemidef S).1)
            * X := rfl
      _ = _ := by rw [pinv_mul_self_mul_pinv]
  unfold innovation residualProfile crossGram responseGram
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hJGJ]
  abel

theorem innovation_posSemidef : (innovation S P).PosSemidef := by
  rw [innovation_eq_gram]
  exact posSemidef_conjTranspose_mul_self _

/-- **(CY.17)**: `G - ½(C + C^*) = S^*(I - P)S`. -/
theorem symForm_eq (hP : P.IsHermitian) :
    sourceGram S - (1 / 2 : ℂ) • (crossGram S P + (crossGram S P)ᴴ) = Sᴴ * (1 - P) * S := by
  have hC : (crossGram S P)ᴴ = crossGram S P := by
    unfold crossGram
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hP.eq,
      Matrix.mul_assoc]
  rw [hC, ← two_smul ℂ (crossGram S P), smul_smul]
  norm_num
  unfold sourceGram crossGram
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

/-- **(CY.17)**: the finite-step symmetric form is positive for a contraction slab. -/
theorem symForm_posSemidef (hP : P.IsHermitian) (hP1 : ((1 : Matrix L L ℂ) - P).PosSemidef) :
    (sourceGram S - (1 / 2 : ℂ) • (crossGram S P + (crossGram S P)ᴴ)).PosSemidef := by
  rw [symForm_eq S P hP]
  exact hP1.conjTranspose_mul_mul_same S

/-- **(CY.17)**: the skew form `(C - C^*)/(2τ)` vanishes for a self-adjoint slab. -/
theorem skewForm_eq_zero (hP : P.IsHermitian) (τ : ℂ) :
    (1 / (2 * τ)) • (crossGram S P - (crossGram S P)ᴴ) = 0 := by
  have hC : (crossGram S P)ᴴ = crossGram S P := by
    unfold crossGram
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hP.eq,
      Matrix.mul_assoc]
  rw [hC, sub_self, smul_zero]

/-- **(CY.18)**: the residual `Δ = ∑ μ_ℓ ‖t⁽¹⁾_ℓ - t⁽²⁾_ℓ‖²` between two response rows. -/
def residual (P₁ P₂ : Matrix L L ℂ) : ℂ :=
  trace ((P₁ * S - P₂ * S)ᴴ * (P₁ * S - P₂ * S))

/-- **(CY.18)**: the residual vanishes exactly when the frozen response writers agree. -/
theorem residual_eq_zero_iff (P₁ P₂ : Matrix L L ℂ) :
    residual S P₁ P₂ = 0 ↔ P₁ * S = P₂ * S := by
  unfold residual
  rw [trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero]

/-- **(CY.18)**: equal response writers give the same complete quadratic triplet. -/
theorem triplet_congr (P₁ P₂ : Matrix L L ℂ) (hT : P₁ * S = P₂ * S) :
    crossGram S P₁ = crossGram S P₂ ∧ responseGram S P₁ = responseGram S P₂ ∧
      innovation S P₁ = innovation S P₂ := by
  unfold crossGram responseGram innovation crossGram responseGram
  rw [hT]
  exact ⟨rfl, rfl, rfl⟩

end SMYMAffineCommonLanding
end NCG
