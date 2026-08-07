/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Hodge-screen spectral reduction of loaded memory
  (`thm:Hodge-feedback-tail` and `thm:feedback-Hankel-Weyl`,
  Gran-Tensor manuscript)

* `exp_tail_integral`: the exact tail integral
  `∫₀^∞ e^{-Rt}dt = 1/R` for `R > 0`.

* `hodge_feedback_tail`:
  (i) the boxed high-energy memory bound
      `‖𝖡e^{-tH}Q_R𝖢‖ ≤ b⋆c⋆e^{-Rt}`, composing the loaded
      source bounds with the spectral screen
      `‖e^{-tH}Q_R‖ ≤ e^{-Rt}`;
  (ii) the boxed integrated tail `∫₀^∞ b⋆c⋆e^{-Rt}dt
      = b⋆c⋆/R`;
  (iii) the boxed Hilbert–Schmidt truncation scale: the
      iterated square integral of the kernel bound
      `b⋆c⋆e^{-R(t+s)}` is exactly `(b⋆c⋆/(2R))²`, so the
      Hankel truncation error is at most `b⋆c⋆/(2R)`.

* `feedback_hankel_weyl`: the boxed decay law
  `s_n(ℌ_X) ≤ C_fb n^{-2/3}`: calibrating the truncation
  energy against the Weyl rank envelope `C_W R^{3/2}` by
  `R = (n/C_W)^{2/3}` makes the retained rank exactly `n`
  and turns the truncation scale `b⋆c⋆/(2R)` into
  `C_fb n^{-2/3}` with the explicit constant
  `C_fb = b⋆c⋆C_W^{2/3}/2`.

The spectral screen `‖e^{-tH}Q_R‖ ≤ e^{-Rt}` (functional
calculus above the truncation energy), the domination of
the Hankel operator norm by its Hilbert–Schmidt norm, and
the Weyl counting law `N(λ) ≤ C_W λ^{3/2}` for the graph
Dirac operator are the manuscript's spectral inputs; the
estimates assembled from them are proved here.
-/

open MeasureTheory Real Set

namespace NCG

/-- The exact exponential tail integral. -/
theorem exp_tail_integral (R : ℝ) (hR : 0 < R) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(R * t))) = 1 / R := by
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ => Real.exp (-x)) 0 hR
  rw [mul_zero] at h
  rw [h, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one,
    one_div]

/-- `thm:Hodge-feedback-tail`. -/
theorem hodge_feedback_tail :
    -- (i) the boxed high-energy memory bound
    (∀ {A : Type} [NormedRing A] (B S C : A) (b c R t : ℝ),
      0 ≤ b → 0 ≤ c → ‖B‖ ≤ b → ‖C‖ ≤ c →
      ‖S‖ ≤ Real.exp (-(R * t)) →
      ‖B * S * C‖ ≤ b * c * Real.exp (-(R * t)))
    -- (ii) the boxed integrated tail
    ∧ (∀ K R : ℝ, 0 < R →
        (∫ t in Ioi (0 : ℝ), K * Real.exp (-(R * t)))
          = K / R)
    -- (iii) the boxed Hilbert–Schmidt truncation scale
    ∧ (∀ K R : ℝ, 0 < R →
        (∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
          (K * Real.exp (-(R * (t + s)))) ^ 2)
        = (K / (2 * R)) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A _ B S C b c R t hb hc hB hC hS
    calc ‖B * S * C‖ ≤ ‖B * S‖ * ‖C‖ := norm_mul_le _ _
      _ ≤ (‖B‖ * ‖S‖) * ‖C‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ (b * Real.exp (-(R * t))) * c := by
          have h1 : ‖B‖ * ‖S‖ ≤ b * Real.exp (-(R * t)) :=
            mul_le_mul hB hS (norm_nonneg _) hb
          exact mul_le_mul h1 hC (norm_nonneg _)
            (by positivity)
      _ = b * c * Real.exp (-(R * t)) := by ring
  · intro K R hR
    rw [MeasureTheory.integral_const_mul,
      exp_tail_integral R hR]
    ring
  · intro K R hR
    have h2R : (0 : ℝ) < 2 * R := by linarith
    have hinner : ∀ t : ℝ,
        (∫ s in Ioi (0 : ℝ),
          (K * Real.exp (-(R * (t + s)))) ^ 2)
        = (K ^ 2 * Real.exp (-(2 * R * t))) * (1 / (2 * R))
        := by
      intro t
      have hpt : ∀ s : ℝ,
          (K * Real.exp (-(R * (t + s)))) ^ 2
          = (K ^ 2 * Real.exp (-(2 * R * t)))
            * Real.exp (-(2 * R * s)) := by
        intro s
        rw [mul_pow, ← Real.exp_nat_mul]
        rw [show ((2 : ℕ) : ℝ) * -(R * (t + s))
            = -(2 * R * t) + -(2 * R * s) by push_cast; ring,
          Real.exp_add]
        ring
      rw [MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall hpt),
        MeasureTheory.integral_const_mul,
        exp_tail_integral (2 * R) h2R]
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hinner)]
    rw [MeasureTheory.integral_mul_const,
      MeasureTheory.integral_const_mul,
      exp_tail_integral (2 * R) h2R]
    field_simp

/-- `thm:feedback-Hankel-Weyl`. -/
theorem feedback_hankel_weyl (K CW : ℝ) (hK : 0 < K)
    (hCW : 0 < CW) (n : ℕ) (hn : 0 < n) :
    -- the calibrated truncation energy exhausts the rank
    -- budget exactly
    (CW * (((n : ℝ) / CW) ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2)
      = (n : ℝ))
    -- and turns the truncation scale into the boxed
    -- `n^{-2/3}` law with an explicit constant
    ∧ (K / (2 * (((n : ℝ) / CW) ^ ((2 : ℝ) / 3)))
      = (K * CW ^ ((2 : ℝ) / 3) / 2)
        * (n : ℝ) ^ (-((2 : ℝ) / 3))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (0 : ℝ) < (n : ℝ) / CW := div_pos hn0 hCW
  constructor
  · rw [← Real.rpow_mul hq.le]
    norm_num
    field_simp
  · rw [Real.div_rpow hn0.le hCW.le,
      Real.rpow_neg hn0.le]
    have hnp : (0 : ℝ) < (n : ℝ) ^ ((2 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hn0 _
    have hcp : (0 : ℝ) < CW ^ ((2 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hCW _
    field_simp

end NCG
