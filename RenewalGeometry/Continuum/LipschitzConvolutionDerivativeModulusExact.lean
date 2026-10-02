/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Derivative modulus of a convolution with Lipschitz data

Infrastructure for `lem:A3-uniform-distance-smoothing` (paper `predictive_spectral_geometry`).

For a compactly supported `C¹` kernel `k` and `K`-Lipschitz scalar data `f`, the derivative of
`k ⋆ f` is `(Dk) ⋆ f` (Mathlib's `HasCompactSupport.hasFDerivAt_convolution_left`), hence

  `‖D(k ⋆ f)(q) - D(k ⋆ f)(p)‖ ≤ K · (∫ ‖Dk‖) · ‖q - p‖`.

Only one derivative falls on the kernel; the second "derivative" is absorbed by the Lipschitz
bound of the data.  For a rescaled bump `η_ε` the integral `∫ ‖Dη_ε‖` scales like `ε⁻¹`, which
is the `ε⁻¹` rate of the paper (instead of the `ε⁻²` rate of two derivatives on the kernel).
-/

open MeasureTheory Filter
open scoped Convolution

namespace RenewalGeometry.LipschitzConvolutionDerivativeModulus

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

omit [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] in
/-- The derivative bilinear map of a scalar convolution: `precompL (lsmul) u c = c • u`. -/
theorem lsmul_precompL_apply (u : G →L[ℝ] ℝ) (c : ℝ) :
    (ContinuousLinearMap.lsmul ℝ ℝ).precompL G u c = c • u := by
  ext x
  simp [ContinuousLinearMap.precompL, ContinuousLinearMap.precompR, mul_comm]

/-- **First-derivative modulus for convolution with Lipschitz data.**  If the scalar kernel `k`
is compactly supported and `C¹` and `f` is `K`-Lipschitz, the derivative of `k ⋆ f` is Lipschitz
with constant `K · ∫ ‖Dk‖`:
`‖D(k ⋆ f)(q) - D(k ⋆ f)(p)‖ ≤ K · (∫ ‖Dk‖) · ‖q - p‖`. -/
theorem norm_fderiv_convolution_sub_le_of_lipschitz
    (μ : Measure G) [μ.IsAddHaarMeasure] [μ.IsNegInvariant]
    (k : G → ℝ) (hk : HasCompactSupport k)
    (hkC : ContDiff ℝ 1 k) (f : G → ℝ) (K : NNReal) (hf : LipschitzWith K f) (p q : G) :
    ‖fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) q -
        fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) p‖ ≤
      K * (∫ x, ‖fderiv ℝ k x‖ ∂μ) * ‖q - p‖ := by
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL
  have hloc : LocallyIntegrable f μ := hf.continuous.locallyIntegrable
  have hD : ∀ x, fderiv ℝ (k ⋆[L, μ] f) x = (fderiv ℝ k ⋆[L.precompL G, μ] f) x :=
    fun x => (hk.hasFDerivAt_convolution_left L hkC hloc x).fderiv
  have hdk_cont : Continuous (fderiv ℝ k) := hkC.continuous_fderiv one_ne_zero
  have hdk_cs : HasCompactSupport (fderiv ℝ k) := hk.fderiv ℝ
  have hex := hdk_cs.convolutionExists_left (L.precompL G) hdk_cont hloc
  have hint : Integrable (fun t => ‖fderiv ℝ k t‖ * ((K : ℝ) * ‖q - p‖)) μ :=
    (hdk_cont.norm.integrable_of_hasCompactSupport hdk_cs.norm).mul_const _
  rw [hD, hD, convolution_def, convolution_def, ← integral_sub (hex q) (hex p)]
  calc
    _ ≤ ∫ t, ‖fderiv ℝ k t‖ * ((K : ℝ) * ‖q - p‖) ∂μ := by
      refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun t => ?_)
      rw [← map_sub, hL, lsmul_precompL_apply, norm_smul, mul_comm]
      gcongr
      have h := hf.dist_le_mul (q - t) (p - t)
      rw [dist_sub_right, dist_eq_norm q p, Real.dist_eq] at h
      simpa only [Real.norm_eq_abs] using h
    _ = K * (∫ x, ‖fderiv ℝ k x‖ ∂μ) * ‖q - p‖ := by
      rw [integral_mul_const]
      ring

end RenewalGeometry.LipschitzConvolutionDerivativeModulus
