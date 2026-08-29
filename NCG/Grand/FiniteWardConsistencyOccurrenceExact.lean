/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Algebraic Ward consistency versus direct physical occurrence

This file formalizes `cor:SMOS-Ward-occurrence` on a finite represented Ward
source bank.  The contact-cocycle Gram tests equality of the two reconstructed
staged expansions.  The occurrence residual makes the independent, stronger
comparison of both predictions with a directly acquired triple history.
-/

open Finset

namespace NCG
namespace FiniteWardConsistencyOccurrence

variable {ι : Type*} [Fintype ι]

/-- Squared Hilbert--Schmidt norm of a finite represented source vector. -/
noncomputable def sourceNormSq (x : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (x i)

theorem sourceNormSq_nonneg (x : ι → ℂ) : 0 ≤ sourceNormSq x := by
  exact Finset.sum_nonneg fun i hi => Complex.normSq_nonneg _

theorem sourceNormSq_eq_zero_iff (x : ι → ℂ) :
    sourceNormSq x = 0 ↔ x = 0 := by
  classical
  unfold sourceNormSq
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  constructor
  · intro h
    funext i
    exact Complex.normSq_eq_zero.mp (h i (Finset.mem_univ i))
  · rintro rfl i hi
    simp
  · exact fun i hi => Complex.normSq_nonneg _

/-- Positive Gram of the reconstructed Ward contact cocycle. -/
noncomputable def contactCocycleGram (cocycle : ι → ℂ) : ℝ :=
  sourceNormSq cocycle

/-- Faithfulness of the finite supported metric: the cocycle Gram vanishes
exactly when the reconstructed algebraic Ward cochain is consistent. -/
theorem contactCocycleGram_eq_zero_iff (cocycle : ι → ℂ) :
    contactCocycleGram cocycle = 0 ↔ cocycle = 0 := by
  exact sourceNormSq_eq_zero_iff cocycle

/-- Direct triple Ward occurrence residual from the manuscript. -/
noncomputable def tripleWardOccurrenceResidual
    (direct predictedLeft predictedRight : ι → ℂ) : ℝ :=
  sourceNormSq (direct - predictedLeft) +
    sourceNormSq (direct - predictedRight)

/-- Vanishing occurrence residual identifies the direct history with both
staged Ward expansions, not merely the two predictions with one another. -/
theorem tripleWardOccurrenceResidual_eq_zero_iff
    (direct predictedLeft predictedRight : ι → ℂ) :
    tripleWardOccurrenceResidual direct predictedLeft predictedRight = 0 ↔
      direct = predictedLeft ∧ direct = predictedRight := by
  constructor
  · intro h
    have hL : sourceNormSq (direct - predictedLeft) = 0 := by
      have hnL := sourceNormSq_nonneg (direct - predictedLeft)
      have hnR := sourceNormSq_nonneg (direct - predictedRight)
      unfold tripleWardOccurrenceResidual at h
      linarith
    have hR : sourceNormSq (direct - predictedRight) = 0 := by
      have hnL := sourceNormSq_nonneg (direct - predictedLeft)
      have hnR := sourceNormSq_nonneg (direct - predictedRight)
      unfold tripleWardOccurrenceResidual at h
      linarith
    constructor
    · exact sub_eq_zero.mp ((sourceNormSq_eq_zero_iff _).mp hL)
    · exact sub_eq_zero.mp ((sourceNormSq_eq_zero_iff _).mp hR)
  · rintro ⟨rfl, h⟩
    subst predictedRight
    simp [tripleWardOccurrenceResidual, sourceNormSq]

/-- The algebraic consistency test is strictly weaker: two perfectly
consistent zero predictions need not match an independently occurring triple
history. -/
theorem consistency_does_not_imply_occurrence :
    ∃ (direct predictedLeft predictedRight cocycle : PUnit → ℂ),
      contactCocycleGram cocycle = 0 ∧
      predictedLeft = predictedRight ∧
      tripleWardOccurrenceResidual direct predictedLeft predictedRight = 2 := by
  let direct : PUnit → ℂ := fun _ => 1
  let predictedLeft : PUnit → ℂ := fun _ => 0
  let predictedRight : PUnit → ℂ := fun _ => 0
  let cocycle : PUnit → ℂ := fun _ => 0
  refine ⟨direct, predictedLeft, predictedRight, cocycle, ?_, rfl, ?_⟩
  · simp [contactCocycleGram, sourceNormSq, cocycle]
  · norm_num [tripleWardOccurrenceResidual, sourceNormSq, direct,
      predictedLeft, predictedRight]

/-- **`cor:SMOS-Ward-occurrence`.**  The two zero tests have their exact
meanings, and the explicit one-coordinate model proves that reconstructed
Ward consistency cannot replace direct physical occurrence. -/
theorem smos_Ward_consistency_versus_occurrence :
    (∀ cocycle : ι → ℂ,
      contactCocycleGram cocycle = 0 ↔ cocycle = 0) ∧
    (∀ direct predictedLeft predictedRight : ι → ℂ,
      tripleWardOccurrenceResidual direct predictedLeft predictedRight = 0 ↔
        direct = predictedLeft ∧ direct = predictedRight) ∧
    (∃ (direct predictedLeft predictedRight cocycle : PUnit → ℂ),
      contactCocycleGram cocycle = 0 ∧
      predictedLeft = predictedRight ∧
      tripleWardOccurrenceResidual direct predictedLeft predictedRight = 2) :=
  ⟨contactCocycleGram_eq_zero_iff,
    tripleWardOccurrenceResidual_eq_zero_iff,
    consistency_does_not_imply_occurrence⟩

end FiniteWardConsistencyOccurrence
end NCG
