/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Gravity.MittagLeffler

/-!
# Regularity of the Mittag-Leffler function

Analytic infrastructure for the driven fractional threshold
equation:

* `ml_abs_le` — the triangle bound
  `|E_{α,β}(x)| ≤ E_{α,β}(|x|)`;
* `ml_mono_nonneg` — monotonicity on the nonnegative axis;
* `ml_continuous` — continuity of `E_{α,β}` (Weierstrass M-test on
  balls against the Gautschi-dominated majorant).
-/

namespace NCG

open Real

/-- Triangle bound: `|E_{α,β}(x)| ≤ E_{α,β}(|x|)`. -/
theorem ml_abs_le {al be : ℝ} (hal : 0 < al) (hbe : 0 < be)
    (x : ℝ) :
    |mittagLeffler al be x| ≤ mittagLeffler al be |x| := by
  unfold mittagLeffler
  have habs : Summable
      (fun n : ℕ => ‖x ^ n / Real.Gamma (al * n + be)‖) := by
    apply Summable.congr (mlSummable hal hbe |x|)
    intro n
    have hG : (0 : ℝ) < Real.Gamma (al * n + be) :=
      Real.Gamma_pos_of_pos (by positivity)
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hG]
  have h1 := norm_tsum_le_tsum_norm habs
  rw [Real.norm_eq_abs] at h1
  calc |∑' n : ℕ, x ^ n / Real.Gamma (al * n + be)|
      ≤ ∑' n : ℕ, ‖x ^ n / Real.Gamma (al * n + be)‖ := h1
  _ = ∑' n : ℕ, |x| ^ n / Real.Gamma (al * n + be) := by
        apply tsum_congr
        intro n
        have hG : (0 : ℝ) < Real.Gamma (al * n + be) :=
          Real.Gamma_pos_of_pos (by positivity)
        rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hG]

/-- Monotonicity of `E_{α,β}` on the nonnegative axis. -/
theorem ml_mono_nonneg {al be x y : ℝ} (hal : 0 < al) (hbe : 0 < be)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    mittagLeffler al be x ≤ mittagLeffler al be y := by
  unfold mittagLeffler
  apply Summable.tsum_le_tsum _ (mlSummable hal hbe x)
    (mlSummable hal hbe y)
  intro n
  have hG : (0 : ℝ) < Real.Gamma (al * n + be) :=
    Real.Gamma_pos_of_pos (by positivity)
  gcongr

/-- Continuity of the Mittag-Leffler function. -/
theorem ml_continuous {al be : ℝ} (hal : 0 < al) (hbe : 0 < be) :
    Continuous (mittagLeffler al be) := by
  rw [continuous_iff_continuousAt]
  intro x0
  set M : ℝ := |x0| + 1 with hM
  have hM0 : 0 < M := by positivity
  have hcont : ContinuousOn (mittagLeffler al be)
      (Metric.ball (0 : ℝ) M) := by
    unfold mittagLeffler
    apply continuousOn_tsum
      (u := fun n : ℕ => M ^ n / Real.Gamma (al * n + be))
    · intro n
      apply ContinuousOn.div_const
      exact (continuous_pow n).continuousOn
    · exact mlSummable hal hbe M
    · intro n y hy
      have hG : (0 : ℝ) < Real.Gamma (al * n + be) :=
        Real.Gamma_pos_of_pos (by positivity)
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hG]
      have hyM : |y| ≤ M := by
        have h := Metric.mem_ball.mp hy
        rw [Real.dist_eq, sub_zero] at h
        exact h.le
      gcongr
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds
    (by simp [hM]))

end NCG
