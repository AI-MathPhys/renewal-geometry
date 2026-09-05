/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.YMNSHodgeShort
import NCG.Grand.PsdBlockSchurExact
import NCG.Grand.GRHRestoringShortExact
import NCG.Grand.ProtectedObservableRieszPseudoinverseExact

/-!
# Matrix two-scale Yang--Mills Feshbach floor

This file lifts the scalar envelope in `YMNSHodgeShort` to the actual finite
Hermitian block matrix.  The Schur completion, corrector norm estimate, and
Loewner floor are all derived from the matrix hypotheses.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace YMTwoScaleFeshbachMatrix

open PsdBlockSchur ProtectedObservableRiesz SourceCoercivityInfluence

set_option maxHeartbeats 800000

variable {p q : Type*} [Fintype p] [Fintype q]
  [DecidableEq p] [DecidableEq q]

private noncomputable def eNorm {i : Type*} [Fintype i] (x : i → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℂ i)‖

private theorem directSum_eNorm_sq (x : p → ℂ) (y : q → ℂ) :
    eNorm (Sum.elim x y) ^ 2 = eNorm x ^ 2 + eNorm y ^ 2 := by
  have hdot : star (Sum.elim x y) ⬝ᵥ Sum.elim x y =
      star x ⬝ᵥ x + star y ⬝ᵥ y := by
    simp [dotProduct, Fintype.sum_sum_type]
  rw [star_dot_self_eq_norm_sq, star_dot_self_eq_norm_sq,
    star_dot_self_eq_norm_sq] at hdot
  exact_mod_cast hdot

private theorem floor_form {i : Type*} [Fintype i] [DecidableEq i]
    (M : Matrix i i ℂ) (a : ℝ)
    (h : (M - (a : ℂ) • 1).PosSemidef) (x : i → ℂ) :
    a * eNorm x ^ 2 ≤ (star x ⬝ᵥ (M *ᵥ x)).re := by
  have hx := h.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.le_def] at hx
  have hself := star_dot_self_eq_norm_sq x
  rw [hself] at hx
  have hre := hx.1
  rw [Complex.zero_re, Complex.sub_re, Complex.mul_re] at hre
  rw [Complex.ofReal_re, Complex.ofReal_im] at hre
  have hnorm_re :
      (↑(‖(WithLp.toLp 2 x : EuclideanSpace ℂ i)‖ ^ 2) : ℂ).re =
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ i)‖ ^ 2 := rfl
  rw [hnorm_re] at hre
  norm_num at hre
  change a * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ i)‖ ^ 2 ≤ _
  exact hre

private theorem corrector_eNorm_sq_le
    (K : Matrix q p ℂ) (β : ℝ) (hβ : 0 ≤ β) (hK : ‖K‖ ≤ β)
    (x : p → ℂ) : eNorm (K *ᵥ x) ^ 2 ≤ β ^ 2 * eNorm x ^ 2 := by
  have hop := Matrix.l2_opNorm_mulVec K
    (WithLp.toLp 2 x : EuclideanSpace ℂ p)
  have hlin : eNorm (K *ᵥ x) ≤ β * eNorm x := by
    calc
      eNorm (K *ᵥ x) ≤ ‖K‖ * eNorm x := by simpa [eNorm] using hop
      _ ≤ β * eNorm x :=
        mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  have hleft : 0 ≤ eNorm (K *ᵥ x) := norm_nonneg _
  have hright : 0 ≤ β * eNorm x := mul_nonneg hβ (norm_nonneg _)
  nlinarith [sq_nonneg (β * eNorm x - eNorm (K *ᵥ x))]

private theorem corrected_directSum_domination
    (K : Matrix q p ℂ) (β : ℝ) (hβ : 0 ≤ β) (hK : ‖K‖ ≤ β)
    (x : p → ℂ) (y : q → ℂ) :
    let w := y + K *ᵥ x
    eNorm (Sum.elim x y) ^ 2 ≤
      (1 + 2 * β ^ 2) * eNorm x ^ 2 + 2 * eNorm w ^ 2 := by
  dsimp only
  let w := y + K *ᵥ x
  have hy : y = w - K *ᵥ x := by
    funext i
    simp [w]
  have htri : eNorm y ≤ eNorm w + eNorm (K *ᵥ x) := by
    rw [hy]
    simpa [eNorm] using norm_sub_le
      (WithLp.toLp 2 w : EuclideanSpace ℂ q)
      (WithLp.toLp 2 (K *ᵥ x) : EuclideanSpace ℂ q)
  have hy2 : eNorm y ^ 2 ≤
      2 * eNorm w ^ 2 + 2 * eNorm (K *ᵥ x) ^ 2 := by
    have hy_nonneg : 0 ≤ eNorm y := norm_nonneg _
    have hsum_nonneg : 0 ≤ eNorm w + eNorm (K *ᵥ x) :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : eNorm y ^ 2 ≤ (eNorm w + eNorm (K *ᵥ x)) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg (eNorm w - eNorm (K *ᵥ x))]
  have hK2 := corrector_eNorm_sq_le K β hβ hK x
  rw [directSum_eNorm_sq]
  nlinarith

/-- The exact vector-level Schur completion for the physical block order. -/
private theorem block_completion
    (A : Matrix p p ℂ) (B : Matrix p q ℂ) (C : Matrix q q ℂ)
    [Invertible C] (hC : C.PosDef) (x : p → ℂ) (y : q → ℂ) :
    let K := C⁻¹ * Bᴴ
    let S := A - B * C⁻¹ * Bᴴ
    star (Sum.elim x y) ⬝ᵥ
        (Matrix.fromBlocks A B Bᴴ C *ᵥ Sum.elim x y) =
      star x ⬝ᵥ (S *ᵥ x) +
      star (y + K *ᵥ x) ⬝ᵥ (C *ᵥ (y + K *ᵥ x)) := by
  dsimp only
  have hpinv : pinv hC.1 = C⁻¹ :=
    (Matrix.inv_eq_left_inv (GRHRestoringShort.pinv_mul_self hC)).symm
  have hrange : C * pinv hC.1 * Bᴴ = Bᴴ :=
    GRHRestoringShort.range_condition_of_posDef hC Bᴴ
  have hc := completion_of_square hC.posSemidef Bᴴ A hrange y x
  rw [hpinv] at hc
  have hc' :
      star (Sum.elim y x) ⬝ᵥ
          (Matrix.fromBlocks C Bᴴ B A *ᵥ Sum.elim y x) =
        star (y + C⁻¹ *ᵥ (Bᴴ *ᵥ x)) ⬝ᵥ
            (C *ᵥ (y + C⁻¹ *ᵥ (Bᴴ *ᵥ x))) +
          star x ⬝ᵥ ((A - B * C⁻¹ * Bᴴ) *ᵥ x) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hc
  calc
    star (Sum.elim x y) ⬝ᵥ
        (Matrix.fromBlocks A B Bᴴ C *ᵥ Sum.elim x y) =
      star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ (B *ᵥ y) +
        star y ⬝ᵥ (Bᴴ *ᵥ x) + star y ⬝ᵥ (C *ᵥ y) :=
          block_form A B C x y
    _ = star y ⬝ᵥ (C *ᵥ y) + star y ⬝ᵥ (Bᴴ *ᵥ x) +
        star x ⬝ᵥ (B *ᵥ y) + star x ⬝ᵥ (A *ᵥ x) := by ring
    _ = star (Sum.elim y x) ⬝ᵥ
        (Matrix.fromBlocks C Bᴴ B A *ᵥ Sum.elim y x) := by
          simpa only [Matrix.conjTranspose_conjTranspose] using
            (block_form C Bᴴ A y x).symm
    _ = star (y + C⁻¹ *ᵥ (Bᴴ *ᵥ x)) ⬝ᵥ
          (C *ᵥ (y + C⁻¹ *ᵥ (Bᴴ *ᵥ x))) +
        star x ⬝ᵥ ((A - B * C⁻¹ * Bᴴ) *ᵥ x) := hc'
    _ = star x ⬝ᵥ ((A - B * C⁻¹ * Bᴴ) *ᵥ x) +
        star (y + (C⁻¹ * Bᴴ) *ᵥ x) ⬝ᵥ
          (C *ᵥ (y + (C⁻¹ * Bᴴ) *ᵥ x)) := by
          rw [Matrix.mulVec_mulVec]
          abel

/-- **`thm:YM-two-scale-Feshbach`, genuine matrix form.** -/
theorem ym_two_scale_feshbach_matrix
    (A : Matrix p p ℂ) (B : Matrix p q ℂ) (C : Matrix q q ℂ)
    [Invertible C] (hAH : A.IsHermitian) (hC : C.PosDef)
    (δ γ β : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hβ : 0 ≤ β)
    (hCfloor : (C - (γ : ℂ) • 1).PosSemidef)
    (hSfloor : ((A - B * C⁻¹ * Bᴴ) - (δ : ℂ) • 1).PosSemidef)
    (hrouter : ‖C⁻¹ * Bᴴ‖ ≤ β) :
    let μ := min (δ / (1 + 2 * β ^ 2)) (γ / 2)
    (Matrix.fromBlocks A B Bᴴ C -
      (μ : ℂ) • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ)).PosSemidef := by
  dsimp only
  let μ := min (δ / (1 + 2 * β ^ 2)) (γ / 2)
  let L := Matrix.fromBlocks A B Bᴴ C
  have hLH : L.IsHermitian := by
    unfold L
    rw [Matrix.isHermitian_fromBlocks_iff]
    exact ⟨hAH, rfl, Matrix.conjTranspose_conjTranspose B, hC.1⟩
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · change (L - (μ : ℂ) • 1).IsHermitian
    exact hLH.sub (Matrix.isHermitian_one.smul (by
      change star (μ : ℂ) = (μ : ℂ)
      simp))
  · intro z
    let x : p → ℂ := z ∘ Sum.inl
    let y : q → ℂ := z ∘ Sum.inr
    have hz : z = Sum.elim x y := by ext (_ | _) <;> rfl
    let K := C⁻¹ * Bᴴ
    let S := A - B * C⁻¹ * Bᴴ
    let w := y + K *ᵥ x
    have hcomp := block_completion A B C hC x y
    have hS := floor_form S δ hSfloor x
    have hCf := floor_form C γ hCfloor w
    have hdom := corrected_directSum_domination K β hβ hrouter x y
    have hscalar := ym_two_scale_feshbach.1
      (star (Sum.elim x y) ⬝ᵥ (L *ᵥ Sum.elim x y)).re
      (star x ⬝ᵥ (S *ᵥ x)).re
      (star w ⬝ᵥ (C *ᵥ w)).re
      (eNorm x ^ 2) (eNorm w ^ 2) (eNorm (Sum.elim x y) ^ 2)
      δ γ β hδ hγ hβ (sq_nonneg _) (sq_nonneg _)
      (by simpa [L, S, K, w] using congrArg Complex.re hcomp)
      hS hCf (by simpa [K, w] using hdom)
    rw [hz]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.le_def]
    constructor
    · rw [Complex.zero_re, Complex.sub_re, Complex.mul_re]
      have hself := star_dot_self_eq_norm_sq (Sum.elim x y)
      rw [hself]
      rw [Complex.ofReal_re, Complex.ofReal_im]
      have hnorm_re :
          (↑(‖(WithLp.toLp 2 (Sum.elim x y) :
              EuclideanSpace ℂ (p ⊕ q))‖ ^ 2) : ℂ).re =
            ‖(WithLp.toLp 2 (Sum.elim x y) :
              EuclideanSpace ℂ (p ⊕ q))‖ ^ 2 := rfl
      rw [hnorm_re]
      norm_num
      simpa [μ, L, eNorm] using hscalar
    · have him := (hLH.im_star_dotProduct_mulVec_self (Sum.elim x y))
      rw [Complex.zero_im, Complex.sub_im, Complex.mul_im]
      have hself := star_dot_self_eq_norm_sq (Sum.elim x y)
      rw [hself]
      rw [Complex.ofReal_re, Complex.ofReal_im]
      have hmu_im : (↑μ : ℂ).im = 0 := rfl
      rw [hmu_im]
      norm_num
      simpa [L] using him.symm

end YMTwoScaleFeshbachMatrix
end NCG
