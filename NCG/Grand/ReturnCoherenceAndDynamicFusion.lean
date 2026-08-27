/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTSourceVariance
import NCG.Grand.PsdCalculusExact

/-!
# Return coherence variance and dynamic fusion

This file completes the operator-variance clause for random return
isometries and instantiates the abstract projection Pythagoras at the actual
dynamic fusion residual.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG
namespace ReturnCoherenceAndDynamicFusion

/-- Mean of a finite family of return operators. -/
def meanReturn {i n : Type} [Fintype i]
    (w : i → ℂ) (U : i → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ e, w e • U e

/-- `SC.6`: the contractivity defect of the mean return is exactly the
operator variance of the random isometry. -/
theorem return_coherence_variance_identity
    {i n : Type} [Fintype i] [Fintype n] [DecidableEq n]
    (w : i → ℂ) (U : i → Matrix n n ℂ)
    (hw : ∑ e, w e = 1) (hwr : ∀ e, star (w e) = w e)
    (hU : ∀ e, (U e)ᴴ * U e = 1) :
    (1 : Matrix n n ℂ) - (meanReturn w U)ᴴ * meanReturn w U =
      ∑ e, w e •
        ((U e - meanReturn w U)ᴴ * (U e - meanReturn w U)) := by
  have h := gt_return_coherence_loss (ι := i) (n := n) (m := n) w U
    (1 : Matrix n n ℂ) (meanReturn w U) hw hwr hU
  have hbase :
      (1 : Matrix n n ℂ) - (meanReturn w U)ᴴ * meanReturn w U =
        ∑ e, w e • ((meanReturn w U - U e)ᴴ *
          (meanReturn w U - U e)) := by
    simpa [meanReturn] using h.symm
  rw [hbase]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  have hneg : meanReturn w U - U e = -(U e - meanReturn w U) := by
    abel
  rw [hneg, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg]

/-- The variance representation proves positive semidefiniteness of the mean
return contractivity defect when the weights are nonnegative. -/
theorem return_coherence_loss_posSemidef
    {i n : Type} [Fintype i] [Fintype n] [DecidableEq n]
    (w : i → ℝ) (U : i → Matrix n n ℂ)
    (hw : ∑ e, w e = 1) (hw0 : ∀ e, 0 ≤ w e)
    (hU : ∀ e, (U e)ᴴ * U e = 1) :
    let wc : i → ℂ := fun e ↦ w e
    ((1 : Matrix n n ℂ) - (meanReturn wc U)ᴴ * meanReturn wc U).PosSemidef := by
  intro wc
  have hwc : ∑ e, wc e = 1 := by
    simpa [wc] using congrArg Complex.ofReal hw
  have hwcr : ∀ e, star (wc e) = wc e := by
    intro e
    simp [wc]
  rw [return_coherence_variance_identity wc U hwc hwcr hU]
  exact Matrix.posSemidef_sum Finset.univ fun e _ ↦ by
    simpa [wc] using QRE.posSemidef_smul_real (hw0 e)
      (Matrix.posSemidef_conjTranspose_mul_self
        (U e - meanReturn wc U))
/-- Actual dynamic fusion residual. -/
def dynamicResidual {a b : Type} [Fintype a] [Fintype b]
    (Gamma : Matrix a b ℂ) (Tbig : Matrix a a ℂ)
    (Tproduct : Matrix b b ℂ) : Matrix a b ℂ :=
  Tbig * Gamma - Gamma * Tproduct

/-- Leakage of the actual transfer out of the product-fusion range. -/
def dynamicLeakage {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] (Gamma : Matrix a b ℂ) (Tbig : Matrix a a ℂ) :
    Matrix a b ℂ :=
  (1 - Gamma * Gammaᴴ) * Tbig * Gamma

/-- Compression mismatch of the actual transfer on the product carrier. -/
def dynamicCompression {a b : Type} [Fintype a] [Fintype b]
    (Gamma : Matrix a b ℂ) (Tbig : Matrix a a ℂ)
    (Tproduct : Matrix b b ℂ) : Matrix b b ℂ :=
  Gammaᴴ * Tbig * Gamma - Tproduct

/-- The abstract fusion Pythagoras specialized to the manuscript's actual
transfer residual, leakage, and compression mismatch. -/
theorem dynamic_fusion_pythagoras_exact
    {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (Gamma : Matrix a b ℂ) (Tbig : Matrix a a ℂ)
    (Tproduct : Matrix b b ℂ) (hGamma : Gammaᴴ * Gamma = 1) :
    (dynamicResidual Gamma Tbig Tproduct)ᴴ *
        dynamicResidual Gamma Tbig Tproduct =
      (dynamicLeakage Gamma Tbig)ᴴ * dynamicLeakage Gamma Tbig +
        (dynamicCompression Gamma Tbig Tproduct)ᴴ *
          dynamicCompression Gamma Tbig Tproduct := by
  have hpyth := gt_dynamic_fusion (a := a) (b := b) (m := b) Gamma
    (dynamicResidual Gamma Tbig Tproduct) hGamma
  have hcompressed : Gammaᴴ * dynamicResidual Gamma Tbig Tproduct =
      dynamicCompression Gamma Tbig Tproduct := by
    unfold dynamicResidual dynamicCompression
    rw [Matrix.mul_sub]
    have hproduct : Gammaᴴ * (Gamma * Tproduct) = Tproduct := by
      rw [← Matrix.mul_assoc, hGamma, Matrix.one_mul]
    rw [hproduct]
    simp only [Matrix.mul_assoc]
  have hperpGamma : ((1 : Matrix a a ℂ) - Gamma * Gammaᴴ) * Gamma = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    calc
      Gamma - (Gamma * Gammaᴴ) * Gamma =
          Gamma - Gamma * (Gammaᴴ * Gamma) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hGamma, Matrix.mul_one, sub_self]
  have hleakage : ((1 : Matrix a a ℂ) - Gamma * Gammaᴴ) *
      dynamicResidual Gamma Tbig Tproduct = dynamicLeakage Gamma Tbig := by
    unfold dynamicResidual dynamicLeakage
    rw [Matrix.mul_sub]
    have hzero : ((1 : Matrix a a ℂ) - Gamma * Gammaᴴ) *
        (Gamma * Tproduct) = 0 := by
      rw [← Matrix.mul_assoc, hperpGamma, Matrix.zero_mul]
    rw [hzero, sub_zero]
    simp only [Matrix.mul_assoc]
  simpa only [hcompressed, hleakage, add_comm] using hpyth

end ReturnCoherenceAndDynamicFusion
end NCG
