/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SupportedCrossLeakage
import NCG.Grand.CanonicalScreenRankStability

/-!
# Davis--Kahan transport for certified canonical screens

The two supported Sylvester estimates are assembled here into the exact
`2 * epsilon / (gap - epsilon)` transport constant in SC.3.  The semigroup
hypotheses are the spectral-calculus certificates for the old low/high and
new low/high screens.
-/

noncomputable section

namespace NCG.CanonicalScreen

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Exact SC.3 projection transport from the four supported spectral
semigroup estimates. -/
theorem norm_screen_sub_le_of_supported_spectral_semigroups_strong
    (A B P Q : H →L[ℂ] H) (beta gap epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsGap : epsilon < gap)
    (hP2 : P * P = P) (hQ2 : Q * Q = Q)
    (hPA : P * A = A * P) (hQB : Q * B = B * Q)
    (hPnorm : ‖P‖ ≤ 1) (hPcnorm : ‖1 - P‖ ≤ 1)
    (hQnorm : ‖Q‖ ≤ 1) (hQcnorm : ‖1 - Q‖ ≤ 1)
    (hAB : ‖A - B‖ ≤ epsilon)
    (hOldLow : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A) * P‖ ≤ Real.exp ((beta - gap) * t))
    (hNewHigh : ∀ t : ℝ, 0 ≤ t →
      ‖(1 - Q) * NormedSpace.exp ((-t) • B)‖ ≤
        Real.exp (-(beta + gap - epsilon) * t))
    (hOldHigh : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • (-A)) * (1 - P)‖ ≤
        Real.exp (-(beta + gap) * t))
    (hNewLow : ∀ t : ℝ, 0 ≤ t →
      ‖Q * NormedSpace.exp ((-t) • (-B))‖ ≤
        Real.exp (-(-(beta - gap + epsilon)) * t)) :
    ‖P - Q‖ ≤ 2 * epsilon / (2 * gap - epsilon) := by
  have hgap0 : 0 < gap := lt_of_le_of_lt hepsilon hepsGap
  have hsep1 : beta - gap < beta + gap - epsilon := by linarith
  have hsep2 : -(beta + gap) < -(beta - gap + epsilon) := by linarith
  have hPc2 : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hP2]
  have hQc2 : (1 - Q) * (1 - Q) = 1 - Q := by
    noncomm_ring [hQ2]
  have hQcB : (1 - Q) * B = B * (1 - Q) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hQB]
  have hPcNegA : (1 - P) * (-A) = (-A) * (1 - P) := by
    rw [sub_mul, one_mul, mul_sub, mul_one]
    simp only [mul_neg, neg_mul]
    rw [hPA]
  have hQNegB : Q * (-B) = (-B) * Q := by
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg hQB
  have hpertNeg : ‖(-A) - (-B)‖ ≤ epsilon := by
    simpa [norm_sub_rev] using hAB
  have hleftStrong :
      ‖P * (1 - Q)‖ ≤ epsilon / (2 * gap - epsilon) := by
    have h := NCG.SemigroupSylvester.norm_cross_le_of_supported_semigroups
      A B P (1 - Q) (beta - gap) (beta + gap - epsilon) epsilon
      hsep1 hP2 hQc2 hPA hQcB hPnorm hQcnorm hAB hOldLow hNewHigh
    convert h using 1 <;> ring
  have hrightStrong :
      ‖(1 - P) * Q‖ ≤ epsilon / (2 * gap - epsilon) := by
    have h := NCG.SemigroupSylvester.norm_cross_le_of_supported_semigroups
      (-A) (-B) (1 - P) Q (-(beta + gap)) (-(beta - gap + epsilon)) epsilon
      hsep2 hPc2 hQ2 hPcNegA hQNegB hPcnorm hQnorm hpertNeg hOldHigh hNewLow
    convert h using 1 <;> ring
  have h := NCG.ResolventStability.norm_projection_sub_le_two_mul_of_cross_bounds
    P Q (epsilon / (2 * gap - epsilon)) hleftStrong hrightStrong
  convert h using 1 <;> ring

/-- The manuscript's displayed (slightly weaker) SC.3 constant. -/
theorem norm_screen_sub_le_of_supported_spectral_semigroups
    (A B P Q : H →L[ℂ] H) (beta gap epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsGap : epsilon < gap)
    (hP2 : P * P = P) (hQ2 : Q * Q = Q)
    (hPA : P * A = A * P) (hQB : Q * B = B * Q)
    (hPnorm : ‖P‖ ≤ 1) (hPcnorm : ‖1 - P‖ ≤ 1)
    (hQnorm : ‖Q‖ ≤ 1) (hQcnorm : ‖1 - Q‖ ≤ 1)
    (hAB : ‖A - B‖ ≤ epsilon)
    (hOldLow : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A) * P‖ ≤ Real.exp ((beta - gap) * t))
    (hNewHigh : ∀ t : ℝ, 0 ≤ t →
      ‖(1 - Q) * NormedSpace.exp ((-t) • B)‖ ≤
        Real.exp (-(beta + gap - epsilon) * t))
    (hOldHigh : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • (-A)) * (1 - P)‖ ≤
        Real.exp (-(beta + gap) * t))
    (hNewLow : ∀ t : ℝ, 0 ≤ t →
      ‖Q * NormedSpace.exp ((-t) • (-B))‖ ≤
        Real.exp (-(-(beta - gap + epsilon)) * t)) :
    ‖P - Q‖ ≤ 2 * epsilon / (gap - epsilon) := by
  have hstrong := norm_screen_sub_le_of_supported_spectral_semigroups_strong
    A B P Q beta gap epsilon hepsilon hepsGap hP2 hQ2 hPA hQB
      hPnorm hPcnorm hQnorm hQcnorm hAB hOldLow hNewHigh hOldHigh hNewLow
  have hdenSmall : 0 < gap - epsilon := sub_pos.mpr hepsGap
  have hdenLarge : 0 < 2 * gap - epsilon := by linarith
  have hdenOrder : gap - epsilon ≤ 2 * gap - epsilon := by
    have hgap0 : 0 < gap := lt_of_le_of_lt hepsilon hepsGap
    linarith
  have hfrac : epsilon / (2 * gap - epsilon) ≤
      epsilon / (gap - epsilon) :=
    div_le_div_of_nonneg_left hepsilon hdenSmall hdenOrder
  exact hstrong.trans (by nlinarith)

end NCG.CanonicalScreen
