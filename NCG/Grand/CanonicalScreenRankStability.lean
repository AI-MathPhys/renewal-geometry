/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.QuantitativeRieszProjectionStability

/-!
# Rank stability for separated canonical screens

This is the min--max-free rank part of SC.3.  Two spectral screens have equal
finite rank whenever the old and new quadratic forms are separated across the
threshold and their quadratic perturbation is smaller than the gap.
-/

noncomputable section

namespace NCG.CanonicalScreen

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def quadratic (A : H →L[ℂ] H) (x : H) : ℝ :=
  RCLike.re (inner ℂ (A x) x)

/-- Operator-norm perturbation controls every real quadratic-form
perturbation with the same constant. -/
theorem abs_quadratic_sub_le_opNorm_mul
    (A B : H →L[ℂ] H) (x : H) :
    |quadratic A x - quadratic B x| ≤ ‖A - B‖ * ‖x‖ ^ 2 := by
  have heq :
      quadratic A x - quadratic B x =
        RCLike.re (inner ℂ ((A - B) x) x) := by
    simp only [quadratic, ContinuousLinearMap.sub_apply, inner_sub_left,
      map_sub]
  rw [heq]
  calc
    |RCLike.re (inner ℂ ((A - B) x) x)|
        ≤ ‖inner ℂ ((A - B) x) x‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(A - B) x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖A - B‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right ((A - B).le_opNorm x) (norm_nonneg x)
    _ = ‖A - B‖ * ‖x‖ ^ 2 := by ring

/-- A declared operator-norm perturbation budget supplies the quadratic
perturbation premise used by the rank theorem. -/
theorem abs_quadratic_sub_le_of_norm_sub_le
    (A B : H →L[ℂ] H) (epsilon : ℝ)
    (hAB : ‖A - B‖ ≤ epsilon) (x : H) :
    |quadratic A x - quadratic B x| ≤ epsilon * ‖x‖ ^ 2 :=
  (abs_quadratic_sub_le_opNorm_mul A B x).trans
    (mul_le_mul_of_nonneg_right hAB (sq_nonneg ‖x‖))

/-- The new low-screen range maps injectively into the old low-screen range. -/
theorem oldRangeMap_injective
    (A B P Q : H →L[ℂ] H) (beta gap epsilon : ℝ)
    (hP : IsIdempotentElem P.toLinearMap)
    (hQ : IsIdempotentElem Q.toLinearMap)
    (hgap : epsilon < gap)
    (hAhigh : ∀ x, P x = 0 →
      (beta + gap) * ‖x‖ ^ 2 ≤ quadratic A x)
    (hBlow : ∀ x, Q x = x →
      quadratic B x ≤ beta * ‖x‖ ^ 2)
    (hpert : ∀ x,
      |quadratic A x - quadratic B x| ≤ epsilon * ‖x‖ ^ 2) :
    Function.Injective (NCG.ProjectionStability.rangeMap Q P) := by
  intro x y hxy
  apply sub_eq_zero.mp
  let u := x - y
  have hmap : NCG.ProjectionStability.rangeMap Q P u = 0 := by
    dsimp only [u]
    rw [map_sub, hxy, sub_self]
  have hPu : P (u : H) = 0 := by
    have := congrArg Subtype.val hmap
    simpa [NCG.ProjectionStability.rangeMap] using this
  have hQu : Q (u : H) = u := by
    exact LinearMap.IsIdempotentElem.mem_range_iff hQ |>.mp u.property
  have hhi := hAhigh (u : H) hPu
  have hlo := hBlow (u : H) hQu
  have hp := hpert (u : H)
  have hdiff :
      quadratic A (u : H) - quadratic B (u : H)
        ≤ epsilon * ‖(u : H)‖ ^ 2 :=
    (le_abs_self _).trans hp
  have hn : 0 ≤ ‖(u : H)‖ ^ 2 := sq_nonneg _
  have hzero : ‖(u : H)‖ ^ 2 = 0 := by
    nlinarith
  apply Subtype.ext
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)

/-- The old low-screen range maps injectively into the new low-screen range. -/
theorem newRangeMap_injective
    (A B P Q : H →L[ℂ] H) (beta gap epsilon : ℝ)
    (hP : IsIdempotentElem P.toLinearMap)
    (hQ : IsIdempotentElem Q.toLinearMap)
    (hgap : epsilon < gap)
    (hAlow : ∀ x, P x = x →
      quadratic A x ≤ (beta - gap) * ‖x‖ ^ 2)
    (hBhigh : ∀ x, Q x = 0 →
      beta * ‖x‖ ^ 2 ≤ quadratic B x)
    (hpert : ∀ x,
      |quadratic A x - quadratic B x| ≤ epsilon * ‖x‖ ^ 2) :
    Function.Injective (NCG.ProjectionStability.rangeMap P Q) := by
  intro x y hxy
  apply sub_eq_zero.mp
  let u := x - y
  have hmap : NCG.ProjectionStability.rangeMap P Q u = 0 := by
    dsimp only [u]
    rw [map_sub, hxy, sub_self]
  have hQu : Q (u : H) = 0 := by
    have := congrArg Subtype.val hmap
    simpa [NCG.ProjectionStability.rangeMap] using this
  have hPu : P (u : H) = u := by
    exact LinearMap.IsIdempotentElem.mem_range_iff hP |>.mp u.property
  have hlo := hAlow (u : H) hPu
  have hhi := hBhigh (u : H) hQu
  have hp := hpert (u : H)
  have hdiff :
      quadratic B (u : H) - quadratic A (u : H)
        ≤ epsilon * ‖(u : H)‖ ^ 2 := by
    rw [abs_sub_comm] at hp
    exact (le_abs_self _).trans hp
  have hn : 0 ≤ ‖(u : H)‖ ^ 2 := sq_nonneg _
  have hzero : ‖(u : H)‖ ^ 2 = 0 := by
    nlinarith
  apply Subtype.ext
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)

/-- SC.3 rank stability from the four spectral-side quadratic inequalities.
The manuscript assumption epsilon less than gap over two is stronger than the
epsilon less than gap condition used here. -/
theorem rank_stable_of_separated_quadratic_forms
    (A B P Q : H →L[ℂ] H) (beta gap epsilon : ℝ)
    (hP : IsIdempotentElem P.toLinearMap)
    (hQ : IsIdempotentElem Q.toLinearMap)
    (hgap : epsilon < gap)
    (hAhigh : ∀ x, P x = 0 →
      (beta + gap) * ‖x‖ ^ 2 ≤ quadratic A x)
    (hAlow : ∀ x, P x = x →
      quadratic A x ≤ (beta - gap) * ‖x‖ ^ 2)
    (hBhigh : ∀ x, Q x = 0 →
      beta * ‖x‖ ^ 2 ≤ quadratic B x)
    (hBlow : ∀ x, Q x = x →
      quadratic B x ≤ beta * ‖x‖ ^ 2)
    (hpert : ∀ x,
      |quadratic A x - quadratic B x| ≤ epsilon * ‖x‖ ^ 2)
    [Module.Finite ℂ (LinearMap.range P.toLinearMap)]
    [Module.Finite ℂ (LinearMap.range Q.toLinearMap)] :
    Module.finrank ℂ (LinearMap.range P.toLinearMap) =
      Module.finrank ℂ (LinearMap.range Q.toLinearMap) := by
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective
      (newRangeMap_injective A B P Q beta gap epsilon hP hQ hgap
        hAlow hBhigh hpert)
  · exact LinearMap.finrank_le_finrank_of_injective
      (oldRangeMap_injective A B P Q beta gap epsilon hP hQ hgap
        hAhigh hBlow hpert)

/-- Operator-norm form of SC.3 rank stability. -/
theorem rank_stable_of_separated_screens_of_norm_sub_le
    (A B P Q : H →L[ℂ] H) (beta gap epsilon : ℝ)
    (hP : IsIdempotentElem P.toLinearMap)
    (hQ : IsIdempotentElem Q.toLinearMap)
    (hgap : epsilon < gap)
    (hAhigh : ∀ x, P x = 0 →
      (beta + gap) * ‖x‖ ^ 2 ≤ quadratic A x)
    (hAlow : ∀ x, P x = x →
      quadratic A x ≤ (beta - gap) * ‖x‖ ^ 2)
    (hBhigh : ∀ x, Q x = 0 →
      beta * ‖x‖ ^ 2 ≤ quadratic B x)
    (hBlow : ∀ x, Q x = x →
      quadratic B x ≤ beta * ‖x‖ ^ 2)
    (hAB : ‖A - B‖ ≤ epsilon)
    [Module.Finite ℂ (LinearMap.range P.toLinearMap)]
    [Module.Finite ℂ (LinearMap.range Q.toLinearMap)] :
    Module.finrank ℂ (LinearMap.range P.toLinearMap) =
      Module.finrank ℂ (LinearMap.range Q.toLinearMap) :=
  rank_stable_of_separated_quadratic_forms
    A B P Q beta gap epsilon hP hQ hgap hAhigh hAlow hBhigh hBlow
      (abs_quadratic_sub_le_of_norm_sub_le A B epsilon hAB)

end NCG.CanonicalScreen
