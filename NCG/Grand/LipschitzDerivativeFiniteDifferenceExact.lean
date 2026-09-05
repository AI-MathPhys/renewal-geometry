/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Finite differences uniform over a derivative-Lipschitz class

One derivative Lipschitz bound gives a common Taylor radius for all functions
in the class, and hence a common finite-difference scale for bounded directions.
The quantifier over functions comes after the choice of scale.
-/

open Set Metric

namespace NCG.LipschitzDerivativeFiniteDifference

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_first_order_remainder
    (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (f : E → F) (df : E → E →L[ℝ] F),
      (∀ x, HasFDerivAt f (df x) x) →
      (∀ x y, ‖df y - df x‖ ≤ M * ‖y - x‖) →
      ∀ x y, dist y x < δ → ‖f y - f x - df x (y - x)‖ ≤ ε * ‖y - x‖ := by
  have hMp : 0 < M + 1 := by linarith
  refine ⟨ε / (M + 1), div_pos hε hMp, ?_⟩
  intro f df hf hdf x y hxy
  apply (convex_ball x (ε / (M + 1))).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hf z).hasFDerivWithinAt) (fun z hz => ?_)
    (mem_ball_self (div_pos hε hMp)) hxy
  have hz' : ‖z - x‖ < ε / (M + 1) := by simpa only [mem_ball, dist_eq_norm] using hz
  have hmul := (lt_div_iff₀ hMp).mp hz'
  exact (hdf x z).trans (by nlinarith [norm_nonneg (z - x)])

theorem uniform_bounded_direction_difference
    (M : ℝ) (hM : 0 ≤ M) (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (f : E → ℝ) (df : E → E →L[ℝ] ℝ),
      (∀ x, HasFDerivAt f (df x) x) →
      (∀ x y, ‖df y - df x‖ ≤ M * ‖y - x‖) →
      ∀ h : ℝ, 0 < h → h < δ → ∀ x v, ‖v‖ ≤ R →
        |(f (x + h • v) - f x) / h - df x v| ≤ ε := by
  have hRp : 0 < R + 1 := by linarith
  obtain ⟨δ, hδ, hrem⟩ := uniform_first_order_remainder (E := E) (F := ℝ) M hM
    (ε / (R + 1)) (div_pos hε hRp)
  refine ⟨δ / (R + 1), div_pos hδ hRp, ?_⟩
  intro f df hf hdf h hh hsmall x v hv
  have hstep : dist (x + h • v) x < δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have hmul := (lt_div_iff₀ hRp).mp hsmall
    nlinarith
  have hb := hrem f df hf hdf x (x + h • v) hstep
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
      (f (x + h • v) - f x - h * df x v) / h := by field_simp [hh.ne']
  rw [hid, abs_div, abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr hb'

end NCG.LipschitzDerivativeFiniteDifference
