/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SelfAdjointGapResolvent

/-!
# Weyl transfer of a self-adjoint spectral gap

An operator-norm perturbation by at most `epsilon` shrinks a protected real
spectral gap of radius `gap` by at most `epsilon`.
-/

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Quantitative Weyl gap transfer for bounded self-adjoint operators. -/
theorem selfAdjoint_spectrum_separated_of_norm_sub_le
    (A B : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (beta gap epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsGap : epsilon < gap)
    (hAB : ‖A - B‖ ≤ epsilon)
    (hspecA : ∀ x ∈ spectrum ℝ A,
      x ≤ beta - gap ∨ beta + gap ≤ x) :
    ∀ y ∈ spectrum ℝ B,
      y ≤ beta - (gap - epsilon) ∨
        beta + (gap - epsilon) ≤ y := by
  intro y hy
  by_contra hsep
  push_neg at hsep
  let distance : ℝ := min (y - (beta - gap)) ((beta + gap) - y)
  have hleft : epsilon < y - (beta - gap) := by linarith [hsep.1]
  have hright : epsilon < (beta + gap) - y := by linarith [hsep.2]
  have hdistance : epsilon < distance := by
    exact lt_min hleft hright
  have hdistance0 : 0 < distance := lt_of_le_of_lt hepsilon hdistance
  have hgapA : ∀ x ∈ spectrum ℝ A, distance ≤ |y - x| := by
    intro x hx
    rcases hspecA x hx with hxlow | hxhigh
    · have hdistLow : distance ≤ y - (beta - gap) := min_le_left _ _
      have hnonneg : 0 ≤ y - x := by linarith
      rw [abs_of_nonneg hnonneg]
      linarith
    · have hdistHigh : distance ≤ (beta + gap) - y := min_le_right _ _
      have hnonpos : y - x ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      linarith
  obtain ⟨hyAres, hyAnorm⟩ :=
    real_mem_resolventSet_and_norm_resolvent_le_inv_of_gap
      A hA y distance hdistance0 hgapA
  have hsmall : ‖resolvent A y‖ * ‖A - B‖ < 1 := by
    calc
      ‖resolvent A y‖ * ‖A - B‖ ≤ distance⁻¹ * epsilon := by
        exact mul_le_mul hyAnorm hAB (norm_nonneg _) (inv_nonneg.mpr hdistance0.le)
      _ = epsilon / distance := by rw [div_eq_mul_inv, mul_comm]
      _ < 1 := (div_lt_one hdistance0).mpr hdistance
  have hyBres := mem_resolventSet_of_norm_resolvent_mul_norm_sub_lt_one
    A B y hyAres hsmall
  exact hy hyBres

end NCG.ResolventStability
