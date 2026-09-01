/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BkmJointContinuityExact

/-!
# Integral remainder for affine relative entropy

For a trace-zero Hermitian tangent, literal affine relative entropy is the
twice-integrated affine BKM form.  This exact FTC identity is the starting
point for transferring the affine Hessian to arbitrary differentiable state
paths.
-/

open Matrix Filter Topology MeasureTheory intervalIntegral
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ d : Matrix n n ℂ}

/-- The affine relative-entropy first variation is the integral of the affine
BKM form along every faithful segment from the base. -/
theorem affineRelativeEntropyFirstVariation_eq_integral_bkm
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {A B u : ℝ}
    (hpos : ∀ s ∈ Set.Ioo A B, (σ + s • d).PosDef)
    (hseg : Set.uIcc 0 u ⊆ Set.Ioo A B) :
    affineRelativeEntropyFirstVariation hσ hd u =
      ∫ s in (0 : ℝ)..u, affineBkmForm hσ hd s := by
  have hcont : ContinuousOn (affineBkmForm hσ hd) (Set.Ioo A B) :=
    affineBkmForm_continuousOn hσ hd isOpen_Ioo (convex_Ioo A B) hpos
  have hint : IntervalIntegrable (affineBkmForm hσ hd) volume 0 u :=
    (hcont.mono hseg).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => affineRelativeEntropyFirstVariation_hasDerivAt
      hσ hd hpos (hseg hs)) hint
  have hzero : affineRelativeEntropyFirstVariation hσ hd 0 = 0 := by
    unfold affineRelativeEntropyFirstVariation
    have hlog : matLog (affineMatrix_isHermitian hσ hd 0) = matLog hσ :=
      matLog_congr (by simp) (affineMatrix_isHermitian hσ hd 0) hσ
    rw [hlog, sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  linarith [hftc]

/-- Exact twice-integrated BKM remainder for normalized affine state paths. -/
theorem affineRelativeEntropy_eq_iteratedBkmIntegral
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (htrace : d.trace.re = 0)
    {A B t : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef)
    (hseg : Set.uIcc 0 t ⊆ Set.Ioo A B) :
    affineRelativeEntropy hσ hd t =
      ∫ u in (0 : ℝ)..t,
        ∫ s in (0 : ℝ)..u, affineBkmForm hσ hd s := by
  have hder : ∀ u ∈ Set.uIcc 0 t,
      HasDerivAt (affineRelativeEntropy hσ hd)
        (affineRelativeEntropyFirstVariation hσ hd u) u := by
    intro u hu
    have hraw := affineRelativeEntropy_hasDerivAt hσ hd hpos (hseg hu)
    unfold affineRelativeEntropyDerivative at hraw
    simpa only [htrace, zero_add] using hraw
  have hcontD : ContinuousOn
      (affineRelativeEntropyFirstVariation hσ hd) (Set.Ioo A B) := by
    intro u hu
    exact (affineRelativeEntropyFirstVariation_hasDerivAt
      hσ hd hpos hu).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (affineRelativeEntropyFirstVariation hσ hd) volume 0 t :=
    (hcontD.mono hseg).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have hzero : affineRelativeEntropy hσ hd 0 = 0 := by
    unfold affineRelativeEntropy relEntropy
    have hlog : matLog (affineMatrix_isHermitian hσ hd 0) = matLog hσ :=
      matLog_congr (by simp) (affineMatrix_isHermitian hσ hd 0) hσ
    rw [hlog, sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  rw [hzero, sub_zero] at hftc
  rw [← hftc]
  apply intervalIntegral.integral_congr
  intro u hu
  exact affineRelativeEntropyFirstVariation_eq_integral_bkm
    hσ hd hpos ((Set.uIcc_subset_uIcc_left hu).trans hseg)

end QRE
end NCG
