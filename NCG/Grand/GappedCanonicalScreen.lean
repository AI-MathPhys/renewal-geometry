/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GappedThresholdMultiplier
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Exact canonical spectral screen on a protected gap

The continuous gapped multiplier is sent through real functional calculus.
On a separated spectrum it is a genuine orthogonal projection, reduces its
operator, is contractive together with its complement, and carries the sharp
supported semigroup bounds.
-/

noncomputable section

namespace NCG.CanonicalScreen

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Functional-calculus realization of the strict sub-threshold screen. -/
def gappedCanonicalScreen (A : H →L[ℂ] H) (beta gap : ℝ) : H →L[ℂ] H :=
  cfc (gappedLowMultiplier beta gap) A

theorem gappedCanonicalScreen_isStarProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (beta gap : ℝ) (hgap : 0 < gap)
    (hspec : ∀ x ∈ spectrum ℝ A,
      x ≤ beta - gap ∨ beta + gap ≤ x) :
    IsStarProjection (gappedCanonicalScreen A beta gap) := by
  constructor
  · change IsIdempotentElem (cfc (gappedLowMultiplier beta gap) A)
    rw [show IsIdempotentElem (cfc (gappedLowMultiplier beta gap) A) ↔
        cfc (gappedLowMultiplier beta gap) A *
          cfc (gappedLowMultiplier beta gap) A =
            cfc (gappedLowMultiplier beta gap) A from iff_rfl]
    rw [← cfc_mul (gappedLowMultiplier beta gap)
      (gappedLowMultiplier beta gap) A
      (continuous_gappedLowMultiplier beta gap).continuousOn
      (continuous_gappedLowMultiplier beta gap).continuousOn]
    apply cfc_congr
    intro x hx
    rcases gappedLowMultiplier_zero_or_one_of_separated
      beta gap x hgap (hspec x hx) with hp | hp
    · simp [hp]
    · simp [hp]
  · exact IsSelfAdjoint.cfc

theorem gappedCanonicalScreen_idempotent
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (beta gap : ℝ) (hgap : 0 < gap)
    (hspec : ∀ x ∈ spectrum ℝ A,
      x ≤ beta - gap ∨ beta + gap ≤ x) :
    gappedCanonicalScreen A beta gap * gappedCanonicalScreen A beta gap =
      gappedCanonicalScreen A beta gap :=
  (gappedCanonicalScreen_isStarProjection A hA beta gap hgap hspec).isIdempotentElem.eq

theorem gappedCanonicalScreen_commutes
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (beta gap : ℝ) :
    gappedCanonicalScreen A beta gap * A =
      A * gappedCanonicalScreen A beta gap := by
  exact ((Commute.refl A).cfc_real (gappedLowMultiplier beta gap)).eq

theorem norm_gappedCanonicalScreen_le_one
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (beta gap : ℝ) :
    ‖gappedCanonicalScreen A beta gap‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro x _
  simpa [Real.norm_eq_abs] using abs_gappedLowMultiplier_le_one beta gap x

theorem norm_one_sub_gappedCanonicalScreen_le_one
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (beta gap : ℝ) (hgap : 0 < gap)
    (hspec : ∀ x ∈ spectrum ℝ A,
      x ≤ beta - gap ∨ beta + gap ≤ x) :
    ‖1 - gappedCanonicalScreen A beta gap‖ ≤ 1 :=
  (gappedCanonicalScreen_isStarProjection A hA beta gap hgap hspec).one_sub.norm_le

theorem norm_exp_mul_gappedCanonicalScreen_le
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (beta gap : ℝ) (hgap : 0 < gap)
    (hspec : ∀ x ∈ spectrum ℝ A,
      x ≤ beta - gap ∨ beta + gap ≤ x)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A) * gappedCanonicalScreen A beta gap‖ ≤
      Real.exp ((beta - gap) * t) := by
  apply norm_exp_smul_mul_cfc_le_of_support_le A hA
    (gappedLowMultiplier beta gap)
    (continuous_gappedLowMultiplier beta gap).continuousOn
    (fun x _ => abs_gappedLowMultiplier_le_one beta gap x)
    (fun x hx hnz =>
      gappedLowMultiplier_support_le beta gap x hgap (hspec x hx) hnz)
    (beta - gap) t ht

theorem one_sub_gappedCanonicalScreen_eq_cfc_complement
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (beta gap : ℝ) :
    1 - gappedCanonicalScreen A beta gap =
      cfc (fun x : ℝ => 1 - gappedLowMultiplier beta gap x) A := by
  rw [gappedCanonicalScreen, cfc_sub]
  simp only [cfc_const_one]

theorem norm_complement_mul_exp_neg_le
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (beta gap : ℝ) (hgap : 0 < gap)
    (hspec : ∀ x ∈ spectrum ℝ A,
      x ≤ beta - gap ∨ beta + gap ≤ x)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖(1 - gappedCanonicalScreen A beta gap) *
        NormedSpace.exp ((-t) • A)‖ ≤
      Real.exp (-(beta + gap) * t) := by
  rw [one_sub_gappedCanonicalScreen_eq_cfc_complement A hA beta gap]
  apply norm_cfc_mul_exp_neg_smul_le_of_support_ge A hA
    (fun x : ℝ => 1 - gappedLowMultiplier beta gap x)
    ((continuous_const.sub
      (continuous_gappedLowMultiplier beta gap)).continuousOn)
    (fun x hx => by
      rcases gappedLowMultiplier_zero_or_one_of_separated
        beta gap x hgap (hspec x hx) with hp | hp
      · simp [hp]
      · simp [hp])
    (fun x hx hnz =>
      gappedLowMultiplier_complement_support_ge
        beta gap x hgap (hspec x hx) hnz)
    (beta + gap) t ht

end NCG.CanonicalScreen
