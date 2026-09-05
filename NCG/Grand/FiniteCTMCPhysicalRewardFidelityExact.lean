/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCGeneralPathLawExact

/-!
# Fidelity of the physical reward in the clock-augmented construction

The reward is the occupation-time sum plus the jump-reward sum over exactly
the state-changing ticks. Thus auxiliary flips cannot create phantom jump
rewards, and an absorbing physical trajectory has only its state reward.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NCG.FiniteCTMCPhysicalRewardFidelity

open FiniteCTMCClockProjection FiniteCTMCPathCarrierMeasurability
open FiniteCTMCPathEvaluationMeasurability FiniteCTMCAdditiveRewardMeasurability
open NonexplosiveFiniteStatePath

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Exactly the state-changing ticks contribute to the physical jump sum. -/
theorem visibleReward_eq_occupation_add_visibleJumps
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (z : AdmissibleJumpSequence (S := S)) :
    visibleReward v g T z =
      (∑ i ∈ Finset.range (admissibleJumpIndex z T), physicalHold z.1 i * v (z.1 i).2) +
      (∑ i ∈ (Finset.range (admissibleJumpIndex z T)).filter
        (fun i => (z.1 i).2 ≠ (z.1 (i + 1)).2), g (z.1 i).2 (z.1 (i + 1)).2) +
      (T - cumulativeJumpTime z.1 (admissibleJumpIndex z T)) *
        v (z.1 (admissibleJumpIndex z T)).2 := by
  unfold visibleReward finiteHorizonAdditiveReward fixedJumpCountAdditiveReward
  rw [Finset.sum_add_distrib, Finset.sum_filter]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : (z.1 i).2 = (z.1 (i + 1)).2 <;> simp [visibleJumpReward, h]

/-- The physical observable never depends on a value assigned to `g(i,i)`. -/
theorem visibleReward_congr_offDiagonal
    (v : S → ℝ) (g h : S → S → ℝ) (heq : ∀ i j, i ≠ j → g i j = h i j)
    (T : ℝ) (z : AdmissibleJumpSequence (S := S)) :
    visibleReward v g T z = visibleReward v h T z := by
  have hfun : visibleJumpReward g = visibleJumpReward h := by
    funext i j
    by_cases hij : i = j
    · simp [visibleJumpReward, hij]
    · simp [visibleJumpReward, hij, heq i j hij]
  simp only [visibleReward, hfun]

/-- An absorbing physical path collects exactly `T*v(x)`, regardless of
how many invisible auxiliary-clock ticks occur. -/
theorem visibleReward_of_constant_state
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (z : AdmissibleJumpSequence (S := S))
    (x : S) (hstate : ∀ n, (z.1 n).2 = x) : visibleReward v g T z = T * v x := by
  simp only [visibleReward, finiteHorizonAdditiveReward, fixedJumpCountAdditiveReward,
    hstate, visibleJumpReward, ite_true, add_zero]
  rw [← Finset.sum_mul]
  unfold cumulativeJumpTime cumulativeHold
  ring

end

end NCG.FiniteCTMCPhysicalRewardFidelity
