/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectralScreenSemigroup

/-!
# A continuous threshold multiplier on a protected spectral gap

The linear ramp is globally continuous and takes only the values zero and one
on a spectrum avoiding the protected interval.  Its functional calculus is
therefore the exact strict-threshold spectral projection.
-/

noncomputable section

namespace NCG.CanonicalScreen

/-- Continuous low-screen multiplier.  It equals one below `beta - gap`, zero
above `beta + gap`, and interpolates linearly in between. -/
def gappedLowMultiplier (beta gap x : ℝ) : ℝ :=
  max 0 (min 1 ((beta + gap - x) / (2 * gap)))

theorem continuous_gappedLowMultiplier (beta gap : ℝ) :
    Continuous (gappedLowMultiplier beta gap) := by
  unfold gappedLowMultiplier
  fun_prop

theorem gappedLowMultiplier_eq_one_of_le
    (beta gap x : ℝ) (hgap : 0 < gap) (hx : x ≤ beta - gap) :
    gappedLowMultiplier beta gap x = 1 := by
  unfold gappedLowMultiplier
  have hden : 0 < 2 * gap := by linarith
  have hfrac : 1 ≤ (beta + gap - x) / (2 * gap) := by
    rw [le_div_iff₀ hden]
    linarith
  rw [min_eq_left hfrac, max_eq_right zero_le_one]

theorem gappedLowMultiplier_eq_zero_of_ge
    (beta gap x : ℝ) (hgap : 0 < gap) (hx : beta + gap ≤ x) :
    gappedLowMultiplier beta gap x = 0 := by
  unfold gappedLowMultiplier
  have hden : 0 < 2 * gap := by linarith
  have hfrac0 : (beta + gap - x) / (2 * gap) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  have hfrac1 : (beta + gap - x) / (2 * gap) ≤ 1 :=
    hfrac0.trans zero_le_one
  rw [min_eq_right hfrac1, max_eq_left hfrac0]

theorem gappedLowMultiplier_nonneg (beta gap x : ℝ) :
    0 ≤ gappedLowMultiplier beta gap x := by
  exact le_max_left _ _

theorem gappedLowMultiplier_le_one (beta gap x : ℝ) :
    gappedLowMultiplier beta gap x ≤ 1 := by
  unfold gappedLowMultiplier
  exact max_le zero_le_one (min_le_left _ _)

theorem abs_gappedLowMultiplier_le_one (beta gap x : ℝ) :
    |gappedLowMultiplier beta gap x| ≤ 1 := by
  rw [abs_of_nonneg (gappedLowMultiplier_nonneg beta gap x)]
  exact gappedLowMultiplier_le_one beta gap x

theorem gappedLowMultiplier_zero_or_one_of_separated
    (beta gap x : ℝ) (hgap : 0 < gap)
    (hx : x ≤ beta - gap ∨ beta + gap ≤ x) :
    gappedLowMultiplier beta gap x = 0 ∨
      gappedLowMultiplier beta gap x = 1 := by
  rcases hx with hx | hx
  · exact Or.inr (gappedLowMultiplier_eq_one_of_le beta gap x hgap hx)
  · exact Or.inl (gappedLowMultiplier_eq_zero_of_ge beta gap x hgap hx)

theorem gappedLowMultiplier_support_le
    (beta gap x : ℝ) (hgap : 0 < gap)
    (hx : x ≤ beta - gap ∨ beta + gap ≤ x)
    (hnz : gappedLowMultiplier beta gap x ≠ 0) :
    x ≤ beta - gap := by
  rcases hx with hx | hx
  · exact hx
  · exact False.elim (hnz
      (gappedLowMultiplier_eq_zero_of_ge beta gap x hgap hx))

theorem gappedLowMultiplier_complement_support_ge
    (beta gap x : ℝ) (hgap : 0 < gap)
    (hx : x ≤ beta - gap ∨ beta + gap ≤ x)
    (hnz : 1 - gappedLowMultiplier beta gap x ≠ 0) :
    beta + gap ≤ x := by
  rcases hx with hx | hx
  · have hone := gappedLowMultiplier_eq_one_of_le beta gap x hgap hx
    exact False.elim (hnz (by rw [hone]; ring))
  · exact hx

end NCG.CanonicalScreen
