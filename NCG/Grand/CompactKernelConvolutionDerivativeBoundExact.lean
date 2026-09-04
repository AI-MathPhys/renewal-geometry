/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedConvolutionKernelEstimateExact

/-!
# A common derivative modulus for bounded-data convolution

For a fixed compactly supported C2 kernel, every convolution against locally
integrable data bounded by C has a derivative with one common Lipschitz
constant. It depends only on the kernel, bilinear map, and C, not the data.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped Convolution

namespace NCG.CompactKernelConvolutionDerivativeBound

open BoundedConvolutionKernelEstimate

noncomputable section

variable {G E F : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def derivativeBound (μ : Measure G) (L : E →L[ℝ] ℝ →L[ℝ] F) (k : G → E) (C : ℝ) : ℝ :=
  ‖(L.precompL G).precompL G‖ * C * ∫ x, ‖fderiv ℝ (fderiv ℝ k) x‖ ∂μ

theorem derivativeBound_nonneg
    (μ : Measure G) (L : E →L[ℝ] ℝ →L[ℝ] F) (k : G → E) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ derivativeBound μ L k C := by
  exact mul_nonneg (mul_nonneg (norm_nonneg _) hC) (integral_nonneg (fun _ => norm_nonneg _))

theorem norm_fderiv_convolution_sub_le
    (μ : Measure G) [IsAddHaarMeasure μ] [IsNegInvariant μ] [SFinite μ]
    (L : E →L[ℝ] ℝ →L[ℝ] F) (k : G → E) (hk : HasCompactSupport k)
    (hkC : ContDiff ℝ 2 k) (f : G → ℝ) (hf : LocallyIntegrable f μ)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) (p q : G) :
    ‖fderiv ℝ (k ⋆[L, μ] f) q - fderiv ℝ (k ⋆[L, μ] f) p‖ ≤
      derivativeBound μ L k C * ‖q - p‖ := by
  let D : G → G →L[ℝ] F := fderiv ℝ k ⋆[L.precompL G, μ] f
  let DD : G → G →L[ℝ] G →L[ℝ] F :=
    fderiv ℝ (fderiv ℝ k) ⋆[(L.precompL G).precompL G, μ] f
  have hk1 : ContDiff ℝ 1 (fderiv ℝ k) := hkC.fderiv_right (by norm_num)
  have hD (x : G) : HasFDerivAt (k ⋆[L, μ] f) (D x) x :=
    hk.hasFDerivAt_convolution_left L (hkC.of_le (by norm_num)) hf x
  have hDD (x : G) : HasFDerivAt D (DD x) x :=
    (hk.fderiv ℝ).hasFDerivAt_convolution_left (L.precompL G) hk1 hf x
  have hki : Integrable (fderiv ℝ (fderiv ℝ k)) μ :=
    (hk1.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport ((hk.fderiv ℝ).fderiv ℝ)
  have hDDbound (x : G) : ‖DD x‖ ≤ derivativeBound μ L k C :=
    norm_convolution_le_kernel_integral μ ((L.precompL G).precompL G)
      (fderiv ℝ (fderiv ℝ k)) f C hki hbound x
  have hderiv : fderiv ℝ (k ⋆[L, μ] f) = D := by
    funext x
    exact (hD x).fderiv
  rw [hderiv]
  exact (convex_univ : Convex ℝ (univ : Set G)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hDD x).hasFDerivWithinAt) (fun x _ => hDDbound x) (mem_univ p) (mem_univ q)

end

end NCG.CompactKernelConvolutionDerivativeBound
