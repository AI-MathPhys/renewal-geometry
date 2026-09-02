/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SelfAdjointSemigroupBounds

/-!
# Cross-leakage bounds from supported semigroups

This file turns the abstract separated Sylvester estimate into the precise
off-diagonal estimate used in Davis--Kahan arguments.  A left screen `P`
reduces `A`, a right screen `R` reduces `B`, and their supported semigroups
are separated.  The cross corner `P R` is then controlled by `A - B`.
-/

noncomputable section

namespace NCG.SemigroupSylvester

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [CompleteSpace H]

/-- Supported semigroup separation controls the cross corner of two reducing
idempotents. -/
theorem norm_cross_le_of_supported_semigroups
    (A B P R : H →L[ℂ] H) (upper lower epsilon : ℝ)
    (hsep : upper < lower)
    (hP2 : P * P = P) (hR2 : R * R = R)
    (hPA : P * A = A * P) (hRB : R * B = B * R)
    (hPnorm : ‖P‖ ≤ 1) (hRnorm : ‖R‖ ≤ 1)
    (hAB : ‖A - B‖ ≤ epsilon)
    (hleft : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A) * P‖ ≤ Real.exp (upper * t))
    (hright : ∀ t : ℝ, 0 ≤ t →
      ‖R * NormedSpace.exp ((-t) • B)‖ ≤ Real.exp (-lower * t)) :
    ‖P * R‖ ≤ epsilon / (lower - upper) := by
  let X : H →L[ℂ] H := P * R
  let C : H →L[ℂ] H := P * (B - A) * R
  have hSylvester : X * B - A * X = C := by
    dsimp only [X, C]
    rw [hRB, ← hPA]
    noncomm_ring
  have hPX : P * X = X := by
    dsimp only [X]
    rw [← mul_assoc, hP2]
  have hXR : X * R = X := by
    dsimp only [X]
    rw [mul_assoc, hR2]
  have hPC : P * C = C := by
    dsimp only [C]
    rw [← mul_assoc, hP2]
  have hCR : C * R = C := by
    dsimp only [C]
    rw [mul_assoc, hR2]
  have hCnorm : ‖C‖ ≤ epsilon := by
    dsimp only [C]
    calc
      ‖P * (B - A) * R‖ ≤ (‖P‖ * ‖B - A‖) * ‖R‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * epsilon) * 1 := by
        apply mul_le_mul
        · apply mul_le_mul hPnorm
            (by simpa [norm_sub_rev] using hAB)
            (norm_nonneg _) zero_le_one
        · exact hRnorm
        · exact norm_nonneg _
        · exact mul_nonneg zero_le_one (by
            exact (norm_nonneg _).trans (by simpa [norm_sub_rev] using hAB))
      _ = epsilon := by ring
  have hmain : ‖X‖ ≤ ‖C‖ / (lower - upper) := by
    apply norm_le_div_of_supported_sylvester
      A B P R X C upper lower hsep
    · simpa only [X, C] using hSylvester
    · simpa only [X] using hPX
    · simpa only [X] using hXR
    · simpa only [C] using hPC
    · simpa only [C] using hCR
    · simpa only [ContinuousLinearMap.mul_def] using hleft
    · simpa only [ContinuousLinearMap.mul_def] using hright
  change ‖X‖ ≤ epsilon / (lower - upper)
  exact hmain.trans (div_le_div_of_nonneg_right hCnorm (sub_nonneg.mpr hsep.le))

end NCG.SemigroupSylvester
