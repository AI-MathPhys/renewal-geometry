/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform first-order remainders and finite differences

Uniform continuity of the actual derivative, together with differentiability,
gives a uniform Taylor remainder via the mean-value inequality on balls. The
directional result is uniform over all base points and a bounded direction
bank. No Taylor remainder or sampling-convergence hypothesis is supplied.
-/

open Set Metric

namespace NCG.UniformFiniteDifferenceRemainder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_first_order_remainder
    (f : E → F) (df : E → E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : UniformContinuous df)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : E, dist y x < δ →
      ‖f y - f x - df x (y - x)‖ ≤ ε * ‖y - x‖ := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hdf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  apply (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hf z).hasFDerivWithinAt)
    (fun z hz => ?_) (mem_ball_self hδ) hxy
  exact (show ‖df z - df x‖ < ε from by
    simpa only [dist_eq_norm] using hmod hz).le

/-- Uniform finite-difference consistency for every direction in a fixed norm ball. -/
theorem uniform_bounded_direction_difference
    (f : E → ℝ) (df : E → E →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : UniformContinuous df)
    (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ x v : E, ‖v‖ ≤ R →
      |(f (x + h • v) - f x) / h - df x v| ≤ ε := by
  have hRp : 0 < R + 1 := by linarith
  obtain ⟨δ, hδ, hrem⟩ := uniform_first_order_remainder f df hf hdf
    (ε / (R + 1)) (div_pos hε hRp)
  refine ⟨δ / (R + 1), div_pos hδ hRp, ?_⟩
  intro h hh hsmall x v hv
  have hstep : dist (x + h • v) x < δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have hmul := (lt_div_iff₀ hRp).mp hsmall
    nlinarith
  have hb := hrem x (x + h • v) hstep
  simp only [add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hh,
    smul_eq_mul] at hb
  have hcoeff : ε / (R + 1) * ‖v‖ ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hRp]
    nlinarith
  have hb' : |f (x + h • v) - f x - h * df x v| ≤ ε * h := by
    change |f (x + h • v) - f x - h * df x v| ≤ _ at hb
    calc
      _ ≤ ε / (R + 1) * (h * ‖v‖) := hb
      _ = (ε / (R + 1) * ‖v‖) * h := by ring
      _ ≤ ε * h := mul_le_mul_of_nonneg_right hcoeff hh.le
  have hid : (f (x + h • v) - f x) / h - df x v =
      (f (x + h • v) - f x - h * df x v) / h := by
    field_simp [hh.ne']
  rw [hid, abs_div, abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr hb'

end NCG.UniformFiniteDifferenceRemainder
