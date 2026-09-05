/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFirstJumpIntegrationExact

/-!
# The first-jump kernel equals the tilted generator

Multiplying the embedded destination probability by the escape rate restores
the original off-diagonal generator entry.  Consequently, the killed
diagonal contribution plus the exponentially weighted destination sum is
exactly multiplication by the Feynman--Kac tilted matrix.
-/

open Matrix Finset
open scoped BigOperators

noncomputable section

namespace NCG.FiniteCTMCFirstJumpGenerator

open NCG.DrivenProcess
open NCG.DrivenProcess.FinitePath
open NCG.FiniteCTMCJumpSequenceLaw

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Escape rate times embedded-chain probability is the off-diagonal jump
rate (and vanishes on the diagonal). -/
theorem escapeRate_mul_destinationProbability
    (L : Matrix S S ℝ) (hescape : ∀ x, 0 < escapeRate L x) (x y : S) :
    escapeRate L x * destinationProbability L x y =
      if y = x then 0 else L x y := by
  by_cases hyx : y = x
  · simp [destinationProbability, hyx]
  · rw [destinationProbability, ite_eq_right hyx]
    field_simp [(hescape x).ne']
    simp [hyx]

/-- The diagonal contribution and the first-jump destination contribution
assemble to the exact tilted-generator action. -/
theorem diagonal_add_weightedDestination_eq_tilt_mulVec
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hescape : ∀ x, 0 < escapeRate L x) (f : S → ℝ) (x : S) :
    (L x x + k * v x) * f x +
        ∑ y, escapeRate L x * destinationProbability L x y *
          Real.exp (k * g x y) * f y =
      (tilt L v g k).mulVec f x := by
  rw [Matrix.mulVec, dotProduct]
  calc
    (L x x + k * v x) * f x +
        ∑ y, escapeRate L x * destinationProbability L x y *
          Real.exp (k * g x y) * f y =
      (L x x + k * v x) * f x +
        ∑ y ∈ Finset.univ.erase x,
          escapeRate L x * destinationProbability L x y *
            Real.exp (k * g x y) * f y := by
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
      simp [destinationProbability]
    _ = tilt L v g k x x * f x +
        ∑ y ∈ Finset.univ.erase x, tilt L v g k x y * f y := by
      rw [tilt_apply_self]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := Finset.ne_of_mem_erase hy
      rw [escapeRate_mul_destinationProbability L hescape x y,
        ite_eq_right hyx, tilt_apply_ne L v g k (Ne.symm hyx)]
    _ = ∑ y, tilt L v g k x y * f y :=
      Finset.add_sum_erase Finset.univ
        (fun y => tilt L v g k x y * f y) (Finset.mem_univ x)

end NCG.FiniteCTMCFirstJumpGenerator
