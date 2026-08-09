import NCG.Grand.FeedbackL1

/-!
# Exact EASY batch 25: the unit-disk feedback resolvent estimate

This closes the only formula not stated explicitly by
`NCG.feedback_l1_limit`: the manuscript's `(1-q)⁻²` specialization of
the two-inverse identity on `‖z‖ ≤ 1`.
-/

namespace NCG

/-- `thm:feedback-l1-limit`, unit-disk clause.  For the two feedback
denominators
`Bₙ(z) = 1 - z Aₙ - z² Kₙ(z)` and
`B(z) = 1 - z A - z² K(z)`, inverse bounds by `(1-q)⁻¹` give exactly
the manuscript's uniform resolvent estimate. -/
theorem feedback_unit_disk_resolvent_bound
    {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
    (q : ℝ) (hq : q < 1) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (An A Kn K Xn X : 𝔄)
    (hnL : (1 - z • An - z ^ 2 • Kn) * Xn = 1)
    (hnR : Xn * (1 - z • An - z ^ 2 • Kn) = 1)
    (hL : (1 - z • A - z ^ 2 • K) * X = 1)
    (hXn : ‖Xn‖ ≤ (1 - q)⁻¹) (hX : ‖X‖ ≤ (1 - q)⁻¹) :
    ‖Xn - X‖ ≤ (‖An - A‖ + ‖Kn - K‖) / (1 - q) ^ 2 := by
  let B : 𝔄 := 1 - z • An - z ^ 2 • Kn
  let C : 𝔄 := 1 - z • A - z ^ 2 • K
  have hid : Xn - X = Xn * (C - B) * X := by
    have hstep : Xn * (C - B) * X = Xn * (C * X) - Xn * B * X := by
      simp only [mul_sub, sub_mul, mul_assoc]
    rw [hstep, hL, hnR, mul_one, one_mul]
  have hz2 : ‖z ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have hCB : ‖C - B‖ ≤ ‖An - A‖ + ‖Kn - K‖ := by
    have heq : C - B = z • (An - A) + z ^ 2 • (Kn - K) := by
      dsimp [B, C]
      module
    rw [heq]
    calc
      ‖z • (An - A) + z ^ 2 • (Kn - K)‖
          ≤ ‖z • (An - A)‖ + ‖z ^ 2 • (Kn - K)‖ := norm_add_le _ _
      _ = ‖z‖ * ‖An - A‖ + ‖z ^ 2‖ * ‖Kn - K‖ := by
          rw [norm_smul, norm_smul]
      _ ≤ 1 * ‖An - A‖ + 1 * ‖Kn - K‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hz2 (norm_nonneg _))
      _ = ‖An - A‖ + ‖Kn - K‖ := by ring
  have hr : 0 ≤ (1 - q)⁻¹ :=
    (inv_pos.mpr (sub_pos.mpr hq)).le
  have hd : 0 ≤ ‖An - A‖ + ‖Kn - K‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hprod : ‖Xn‖ * ‖C - B‖
      ≤ (1 - q)⁻¹ * (‖An - A‖ + ‖Kn - K‖) :=
    mul_le_mul hXn hCB (norm_nonneg _) hr
  rw [hid]
  calc
    ‖Xn * (C - B) * X‖ ≤ ‖Xn * (C - B)‖ * ‖X‖ := norm_mul_le _ _
    _ ≤ (‖Xn‖ * ‖C - B‖) * ‖X‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ((1 - q)⁻¹ * (‖An - A‖ + ‖Kn - K‖)) * (1 - q)⁻¹ :=
      mul_le_mul hprod hX (norm_nonneg _) (mul_nonneg hr hd)
    _ = (‖An - A‖ + ‖Kn - K‖) / (1 - q) ^ 2 := by
      field_simp [ne_of_gt (sub_pos.mpr hq)]
      <;> ring

end NCG
