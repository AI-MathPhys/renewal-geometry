/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AcceptedArithmeticAndAffineConsequences

/-!
# Affine reflection and cutoff transport

Exact finite-dimensional completion of `thm:SMYM-affine-transport`.  A genuine
matrix frame floor is converted into the weighted `L²` estimate, rather than
being replaced by a scalar hypothesis.  The reflection defect is also tied to
the complete coordinate profile and to its three quadratic Gram blocks.
-/

open Finset Matrix
open scoped MatrixOrder

namespace NCG
namespace AffineReflectionCutoffTransport

/-- Weighted squared `L²` norm of a finite vector-valued profile. -/
def weightedL2Sq {l d : Type*} [Fintype l] [Fintype d]
    (μ : l → ℝ) (x : l → d → ℝ) : ℝ :=
  ∑ ell, μ ell * ∑ i, (x ell i) ^ 2

/-- Weighted bilinear Gram block of two response profiles. -/
def weightedGram {l d e : Type*} [Fintype l]
    (μ : l → ℝ) (x : l → d → ℝ) (y : l → e → ℝ) : Matrix d e ℝ :=
  fun i j => ∑ ell, μ ell * x ell i * y ell j

/-- A matrix Loewner floor gives its pointwise Euclidean frame inequality. -/
theorem frame_floor_pointwise {k d : Type*} [Fintype k] [Fintype d]
    [DecidableEq d] (B : Matrix k d ℝ) (α : ℝ)
    (hfloor : (B.transpose * B - α • (1 : Matrix d d ℝ)).PosSemidef)
    (x : d → ℝ) :
    α * ∑ i, (x i) ^ 2 ≤ ∑ j, ((B *ᵥ x) j) ^ 2 := by
  have h := hfloor.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul] at h
  simp only [starRingEnd_apply, star_id_of_comm] at h
  have hgram : x ⬝ᵥ ((B.transpose * B) *ᵥ x) =
      (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.dotProduct_transpose_mulVec]
    simp
  rw [hgram] at h
  simpa [dotProduct, smul_eq_mul, pow_two] using h

/-- The pointwise frame floor sums to the exact weighted transport estimate. -/
theorem weighted_frame_transport_sq {l k d : Type*}
    [Fintype l] [Fintype k] [Fintype d] [DecidableEq d]
    (μ : l → ℝ) (hμ : ∀ ell, 0 ≤ μ ell)
    (B : Matrix k d ℝ) (α : ℝ)
    (hfloor : (B.transpose * B - α • (1 : Matrix d d ℝ)).PosSemidef)
    (x : l → d → ℝ) :
    α * weightedL2Sq μ x ≤ weightedL2Sq μ (fun ell => B *ᵥ x ell) := by
  unfold weightedL2Sq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ell _
  calc
    α * (μ ell * ∑ i, (x ell i) ^ 2) =
        μ ell * (α * ∑ i, (x ell i) ^ 2) := by ring
    _ ≤ μ ell * ∑ i, ((B *ᵥ x ell) i) ^ 2 :=
      mul_le_mul_of_nonneg_left (frame_floor_pointwise B α hfloor (x ell)) (hμ ell)

/-- The manuscript's `α⁻¹/² ε_b` estimate, now derived from an actual
finite probe-frame Loewner floor. -/
theorem affine_cutoff_transport_l2 {l k d : Type*}
    [Fintype l] [Fintype k] [Fintype d] [DecidableEq d]
    (μ : l → ℝ) (hμ : ∀ ell, 0 ≤ μ ell)
    (B : Matrix k d ℝ) (α εb : ℝ) (hα : 0 < α) (hεb : 0 ≤ εb)
    (hfloor : (B.transpose * B - α • (1 : Matrix d d ℝ)).PosSemidef)
    (θX θY : l → d → ℝ)
    (hraw : weightedL2Sq μ (fun ell => B *ᵥ (θY ell - θX ell)) ≤ εb ^ 2) :
    Real.sqrt (weightedL2Sq μ (fun ell => θY ell - θX ell))
      ≤ α⁻¹ ^ (1 / 2 : ℝ) * εb := by
  have hweighted := weighted_frame_transport_sq μ hμ B α hfloor
    (fun ell => θY ell - θX ell)
  have herr : α * weightedL2Sq μ (fun ell => θY ell - θX ell) ≤ εb ^ 2 :=
    hweighted.trans hraw
  have hnonneg : 0 ≤ weightedL2Sq μ (fun ell => θY ell - θX ell) := by
    unfold weightedL2Sq
    exact Finset.sum_nonneg fun ell _ =>
      mul_nonneg (hμ ell) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hsqrtα : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hroot : Real.sqrt (weightedL2Sq μ (fun ell => θY ell - θX ell))
      ≤ εb / Real.sqrt α := by
    apply (le_div_iff₀ hsqrtα).2
    have hsquare :
        (Real.sqrt α * Real.sqrt (weightedL2Sq μ (fun ell => θY ell - θX ell))) ^ 2
          ≤ εb ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hα.le, Real.sq_sqrt hnonneg]
      simpa [mul_comm] using herr
    nlinarith [Real.sqrt_nonneg α,
      Real.sqrt_nonneg (weightedL2Sq μ (fun ell => θY ell - θX ell))]
  rw [Real.inv_rpow, ← Real.sqrt_eq_rpow]
  · simpa [div_eq_inv_mul, mul_comm] using hroot
  · exact hα.le

/-- Vanishing affine reflection defect is equality of the complete predictable
coordinate profile and therefore transports all three quadratic blocks. -/
theorem affine_reflection_profile_and_grams
    {l d e : Type*} [Fintype l] [Fintype d] [Fintype e]
    (μ : l → ℝ) (hμ : ∀ ell, 0 < μ ell)
    (minus reflectedPlus : l → d → ℝ) (source : l → e → ℝ) :
    AcceptedArithmeticAndAffineConsequences.affineReflectionDefect
        μ minus reflectedPlus = 0 ↔
      (minus = reflectedPlus ∧
        weightedGram μ minus minus = weightedGram μ reflectedPlus reflectedPlus ∧
        weightedGram μ source minus = weightedGram μ source reflectedPlus ∧
        weightedGram μ minus source = weightedGram μ reflectedPlus source) := by
  constructor
  · intro hz
    have hcoord :=
      (AcceptedArithmeticAndAffineConsequences.affine_reflection_defect_zero_iff
        μ minus reflectedPlus hμ).mp hz
    have hprofile : minus = reflectedPlus := by
      funext ell i
      exact hcoord ell i
    subst hprofile
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨hprofile, -, -, -⟩
    exact (AcceptedArithmeticAndAffineConsequences.affine_reflection_defect_zero_iff
      μ minus reflectedPlus hμ).mpr (by simpa [hprofile])

/-- Exact finite package corresponding to equations (CY.19)--(CY.20). -/
theorem smym_affine_transport
    {l k d e : Type*} [Fintype l] [Fintype k] [Fintype d] [Fintype e]
    [DecidableEq d]
    (μ : l → ℝ) (hμ : ∀ ell, 0 < μ ell)
    (B : Matrix k d ℝ) (α εb : ℝ) (hα : 0 < α) (hεb : 0 ≤ εb)
    (hfloor : (B.transpose * B - α • (1 : Matrix d d ℝ)).PosSemidef)
    (θminus θplus θX θY : l → d → ℝ) (source : l → e → ℝ)
    (hreflect : AcceptedArithmeticAndAffineConsequences.affineReflectionDefect
      μ θminus θplus = 0)
    (hraw : weightedL2Sq μ (fun ell => B *ᵥ (θY ell - θX ell)) ≤ εb ^ 2) :
    (θminus = θplus ∧
      weightedGram μ θminus θminus = weightedGram μ θplus θplus ∧
      weightedGram μ source θminus = weightedGram μ source θplus ∧
      weightedGram μ θminus source = weightedGram μ θplus source)
      ∧ Real.sqrt (weightedL2Sq μ (fun ell => θY ell - θX ell))
        ≤ α⁻¹ ^ (1 / 2 : ℝ) * εb := by
  refine ⟨(affine_reflection_profile_and_grams μ hμ θminus θplus source).mp hreflect, ?_⟩
  exact affine_cutoff_transport_l2 μ (fun ell => (hμ ell).le) B α εb hα hεb
    hfloor θX θY hraw

end AffineReflectionCutoffTransport
end NCG
