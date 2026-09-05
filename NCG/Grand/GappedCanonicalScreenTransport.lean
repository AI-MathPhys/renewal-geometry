/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GappedCanonicalScreen

/-!
# Quantitative transport of exact gapped canonical screens

This assembles the functional-calculus screen certificates with the supported
Sylvester theorem.  The old operator has gap `gap`; the new operator has the
Weyl-reduced gap `gap - epsilon`.
-/

noncomputable section

namespace NCG.CanonicalScreen

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Exact Davis--Kahan norm transport once the old and perturbed spectral-gap
dichotomies have been established. -/
theorem norm_gappedCanonicalScreen_sub_le_strong
    (A B : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (beta gap epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsGap : epsilon < gap)
    (hAB : ‖A - B‖ ≤ epsilon)
    (hspecA : ∀ x ∈ spectrum ℝ A,
      x ≤ beta - gap ∨ beta + gap ≤ x)
    (hspecB : ∀ x ∈ spectrum ℝ B,
      x ≤ beta - (gap - epsilon) ∨
        beta + (gap - epsilon) ≤ x) :
    ‖gappedCanonicalScreen A beta gap -
        gappedCanonicalScreen B beta (gap - epsilon)‖ ≤
      2 * epsilon / (2 * gap - epsilon) := by
  let P := gappedCanonicalScreen A beta gap
  let Q := gappedCanonicalScreen B beta (gap - epsilon)
  have hgap : 0 < gap := lt_of_le_of_lt hepsilon hepsGap
  have hgapB : 0 < gap - epsilon := sub_pos.mpr hepsGap
  have hPstar := gappedCanonicalScreen_isStarProjection
    A hA beta gap hgap hspecA
  have hQstar := gappedCanonicalScreen_isStarProjection
    B hB beta (gap - epsilon) hgapB hspecB
  have hPA := gappedCanonicalScreen_commutes A hA beta gap
  have hQB := gappedCanonicalScreen_commutes B hB beta (gap - epsilon)
  have hOldLow : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A) * P‖ ≤ Real.exp ((beta - gap) * t) := by
    intro t ht
    exact norm_exp_mul_gappedCanonicalScreen_le
      A hA beta gap hgap hspecA t ht
  have hNewHigh : ∀ t : ℝ, 0 ≤ t →
      ‖(1 - Q) * NormedSpace.exp ((-t) • B)‖ ≤
        Real.exp (-(beta + gap - epsilon) * t) := by
    intro t ht
    convert norm_complement_mul_exp_neg_le
      B hB beta (gap - epsilon) hgapB hspecB t ht using 1 <;> ring
  have hOldHigh : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • (-A)) * (1 - P)‖ ≤
        Real.exp (-(beta + gap) * t) := by
    intro t ht
    have hcommAP : A * P = P * A := by simpa [P] using hPA.symm
    have hcommExpP :
        NormedSpace.exp ((-t) • A) * P =
          P * NormedSpace.exp ((-t) • A) :=
      ((show Commute A P from hcommAP).smul_left (-t)).exp_left.eq
    have hcommComp :
        NormedSpace.exp ((-t) • A) * (1 - P) =
          (1 - P) * NormedSpace.exp ((-t) • A) := by
      rw [mul_sub, mul_one, sub_mul, one_mul, hcommExpP]
    rw [show t • (-A) = (-t) • A by
      simp only [smul_neg, neg_smul]; rfl, hcommComp]
    exact norm_complement_mul_exp_neg_le
      A hA beta gap hgap hspecA t ht
  have hNewLow : ∀ t : ℝ, 0 ≤ t →
      ‖Q * NormedSpace.exp ((-t) • (-B))‖ ≤
        Real.exp (-(-(beta - gap + epsilon)) * t) := by
    intro t ht
    have hcommBQ : B * Q = Q * B := by simpa [Q] using hQB.symm
    have hcommExpQ :
        NormedSpace.exp (t • B) * Q =
          Q * NormedSpace.exp (t • B) :=
      ((show Commute B Q from hcommBQ).smul_left t).exp_left.eq
    rw [show (-t) • (-B) = t • B by simp, ← hcommExpQ]
    convert norm_exp_mul_gappedCanonicalScreen_le
      B hB beta (gap - epsilon) hgapB hspecB t ht using 1 <;> ring
  apply norm_screen_sub_le_of_supported_spectral_semigroups_strong
    A B P Q beta gap epsilon hepsilon hepsGap
  · exact hPstar.isIdempotentElem.eq
  · exact hQstar.isIdempotentElem.eq
  · simpa [P] using hPA
  · simpa [Q] using hQB
  · exact hPstar.norm_le
  · exact hPstar.one_sub.norm_le
  · exact hQstar.norm_le
  · exact hQstar.one_sub.norm_le
  · exact hAB
  · exact hOldLow
  · exact hNewHigh
  · exact hOldHigh
  · exact hNewLow

/-- The displayed SC.3 constant for exact functional-calculus screens. -/
theorem norm_gappedCanonicalScreen_sub_le
    (A B : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (beta gap epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsGap : epsilon < gap)
    (hAB : ‖A - B‖ ≤ epsilon)
    (hspecA : ∀ x ∈ spectrum ℝ A,
      x ≤ beta - gap ∨ beta + gap ≤ x)
    (hspecB : ∀ x ∈ spectrum ℝ B,
      x ≤ beta - (gap - epsilon) ∨
        beta + (gap - epsilon) ≤ x) :
    ‖gappedCanonicalScreen A beta gap -
        gappedCanonicalScreen B beta (gap - epsilon)‖ ≤
      2 * epsilon / (gap - epsilon) := by
  have hstrong := norm_gappedCanonicalScreen_sub_le_strong
    A B hA hB beta gap epsilon hepsilon hepsGap hAB hspecA hspecB
  have hdenSmall : 0 < gap - epsilon := sub_pos.mpr hepsGap
  have hdenOrder : gap - epsilon ≤ 2 * gap - epsilon := by
    have hgap0 : 0 < gap := lt_of_le_of_lt hepsilon hepsGap
    linarith
  have hfrac : epsilon / (2 * gap - epsilon) ≤
      epsilon / (gap - epsilon) :=
    div_le_div_of_nonneg_left hepsilon hdenSmall hdenOrder
  exact hstrong.trans (by nlinarith)

end NCG.CanonicalScreen
