/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform norm control for convolution against bounded data

An integrable kernel convolved through a continuous bilinear map against
uniformly bounded data has a bound independent of the spatial base point.
The estimate also applies to operator-valued differentiated kernels.
-/

open MeasureTheory Filter
open scoped Convolution

namespace NCG.BoundedConvolutionKernelEstimate

variable {G E E' F : Type*} [Sub G] [MeasurableSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_convolution_le_kernel_integral
    (μ : Measure G) (L : E →L[ℝ] E' →L[ℝ] F) (k : G → E) (f : G → E')
    (C : ℝ) (hk : Integrable k μ) (hf : ∀ x, ‖f x‖ ≤ C) (p : G) :
    ‖(k ⋆[L, μ] f) p‖ ≤ ‖L‖ * C * ∫ x, ‖k x‖ ∂μ := by
  rw [convolution_def]
  calc
    _ ≤ ∫ x, (‖L‖ * C) * ‖k x‖ ∂μ :=
      norm_integral_le_of_norm_le (hk.norm.const_mul _) (Eventually.of_forall (fun x => by
        calc
          ‖L (k x) (f (p - x))‖ ≤ ‖L‖ * ‖k x‖ * ‖f (p - x)‖ := L.le_opNorm₂ _ _
          _ ≤ ‖L‖ * ‖k x‖ * C :=
            mul_le_mul_of_nonneg_left (hf _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = (‖L‖ * C) * ‖k x‖ := by ring))
    _ = _ := integral_const_mul _ _

end NCG.BoundedConvolutionKernelEstimate
