/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WordLocalizerScoreAndInfluence

/-!
# Score cutoff loss: zero loss ⇔ coarse measurability, nested telescoping

Completes `thm:GT-score-cutoff-loss` on top of
`WordLocalizerScoreAndInfluence.deterministic_score_information_loss`
(NL.11–NL.13: coarse synthesis as conditional expectation, Pythagoras
`A^* I_Y A = I_X + R^loss`, positivity of the loss).

* `fisherBlock_diag_re`: the diagonal of a Fisher block is the weighted
  squared score mass;
* `fisherBlock_eq_zero_iff` / `loss_zero_iff_measurable`: the loss vanishes
  exactly when every transported fine score agrees with its coarse conditional
  expectation on the support of the fine law (coarse measurability);
* `nested_cutoff_telescoping`: for three nested deterministic cutoffs the
  losses telescope as orthogonal (PSD) increments.
-/

open Finset Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace ScoreCutoffLoss

variable {Ω Index : Type*} [Fintype Ω]

theorem fisherBlock_apply (p : Ω → ℝ) (s : Index → Ω → ℂ) (i j : Index) :
    fisherBlock p s i j = ∑ x, (p x : ℂ) * (starRingEnd ℂ) (s i x) * s j x := rfl

/-- Diagonal entries are real weighted score masses. -/
theorem fisherBlock_diag_re (p : Ω → ℝ) (s : Index → Ω → ℂ) (i : Index) :
    (fisherBlock p s i i).re = ∑ x, p x * ‖s i x‖ ^ 2 := by
  rw [fisherBlock_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- A Fisher block vanishes iff every score vanishes on the support of `p`. -/
theorem fisherBlock_eq_zero_iff (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (s : Index → Ω → ℂ) :
    fisherBlock p s = 0 ↔ ∀ i x, p x ≠ 0 → s i x = 0 := by
  constructor
  · intro h i x hx
    have hdiag : (fisherBlock p s i i).re = 0 := by rw [h]; simp
    rw [fisherBlock_diag_re] at hdiag
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      fun y _ => mul_nonneg (hp y) (sq_nonneg _)).mp hdiag x (Finset.mem_univ x)
    rcases mul_eq_zero.mp hterm with h0 | h0
    · exact absurd h0 hx
    · rw [sq_eq_zero_iff, norm_eq_zero] at h0
      exact h0
  · intro h
    ext i j
    rw [fisherBlock_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : p x = 0
    · simp [hx]
    · rw [h i x hx]; simp

/-- **Zero loss ⇔ coarse measurability**: the loss block vanishes exactly when
each transported fine score equals its coarse conditional expectation on the
support of the fine law. -/
theorem loss_zero_iff_measurable {Coarse : Type*}
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (score : Index → Ω → ℂ)
    (coarse : Ω → Coarse) (coarseScore : Index → Coarse → ℂ) :
    fisherBlock p (fun i x => score i x - coarseScore i (coarse x)) = 0 ↔
      ∀ i x, p x ≠ 0 → score i x = coarseScore i (coarse x) := by
  rw [fisherBlock_eq_zero_iff p hp]
  simp only [sub_eq_zero]

/-- **Nested telescoping**: two successive deterministic cutoffs
`Ω → C₁ → C₂` decompose the fine localizer into the coarsest localizer plus
two PSD loss increments. -/
theorem nested_cutoff_telescoping {C₁ C₂ : Type*} [Fintype C₁] [Fintype C₂]
    [DecidableEq C₁] [DecidableEq C₂] [Finite Index]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (score : Index → Ω → ℂ) (coarse₁ : Ω → C₁) (coarse₂ : C₁ → C₂)
    (p₁ : C₁ → ℝ) (hp₁ : ∀ y, p₁ y = (Finset.univ.filter (fun x => coarse₁ x = y)).sum p)
    (hp₁pos : ∀ y, p₁ y ≠ 0)
    (score₁ : Index → C₁ → ℂ)
    (hscore₁ : ∀ i y, score₁ i y = (p₁ y : ℂ)⁻¹ *
      (Finset.univ.filter (fun x => coarse₁ x = y)).sum (fun x => (p x : ℂ) * score i x))
    (p₂ : C₂ → ℝ) (hp₂ : ∀ z, p₂ z = (Finset.univ.filter (fun y => coarse₂ y = z)).sum p₁)
    (hp₂pos : ∀ z, p₂ z ≠ 0)
    (score₂ : Index → C₂ → ℂ)
    (hscore₂ : ∀ i z, score₂ i z = (p₂ z : ℂ)⁻¹ *
      (Finset.univ.filter (fun y => coarse₂ y = z)).sum (fun y => (p₁ y : ℂ) * score₁ i y)) :
    fisherBlock p score = fisherBlock p₂ score₂
      + fisherBlock p₁ (fun i y => score₁ i y - score₂ i (coarse₂ y))
      + fisherBlock p (fun i x => score i x - score₁ i (coarse₁ x))
    ∧ (fisherBlock p₁ (fun i y => score₁ i y - score₂ i (coarse₂ y))).PosSemidef
    ∧ (fisherBlock p (fun i x => score i x - score₁ i (coarse₁ x))).PosSemidef := by
  have hp₁nonneg : ∀ y, 0 ≤ p₁ y := by
    intro y; rw [hp₁ y]; exact Finset.sum_nonneg fun x _ => hp x
  obtain ⟨_, _, h1, h1pos, _⟩ :=
    WordLocalizerScoreAndInfluence.deterministic_score_information_loss p hp score coarse₁ p₁ hp₁
      hp₁pos score₁ hscore₁
  obtain ⟨_, _, h2, h2pos, _⟩ :=
    WordLocalizerScoreAndInfluence.deterministic_score_information_loss p₁ hp₁nonneg score₁
      coarse₂ p₂ hp₂ hp₂pos score₂ hscore₂
  refine ⟨?_, h2pos, h1pos⟩
  rw [h1, h2]

end ScoreCutoffLoss
end NCG
