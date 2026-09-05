/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFeynmanKacCompilerExact

/-!
# Concrete finite-CTMC Feynman--Kac path moments

This file fixes the exact random variable to which first-jump conditioning
will be applied: the exponential of the measurable finite-horizon additive
reward, multiplied by a terminal-state test function, under the genuine
admissible CTMC path law.
-/

open MeasureTheory Finset Set
open scoped BigOperators

noncomputable section

namespace NCG.FiniteCTMCFeynmanKacPathMoment

open NCG.DrivenProcess
open NCG.DrivenProcess.FinitePath
open NCG.FiniteCTMCPathCarrierMeasurability
open NCG.FiniteCTMCPathEvaluationMeasurability
open NCG.FiniteCTMCAdditiveRewardMeasurability
open NCG.FiniteCTMCAdmissiblePathLaw
open NCG.NonexplosiveFiniteStatePath

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The occupied jump index at time zero is zero. -/
theorem admissibleJumpIndex_zero
    (z : AdmissibleJumpSequence (S := S)) :
    admissibleJumpIndex z 0 = 0 := by
  rw [admissibleJumpIndex_eq_iff z le_rfl 0]
  constructor
  · simp [cumulativeJumpTime, cumulativeHold]
  · simpa [cumulativeJumpTime, cumulativeHold, physicalHold] using z.2.1 0

/-- The finite-horizon reward starts at zero. -/
theorem finiteHorizonAdditiveReward_zero
    (v : S → ℝ) (g : S → S → ℝ)
    (z : AdmissibleJumpSequence (S := S)) :
    finiteHorizonAdditiveReward v g 0 z = 0 := by
  simp [finiteHorizonAdditiveReward, admissibleJumpIndex_zero,
    fixedJumpCountAdditiveReward, cumulativeJumpTime, cumulativeHold]

/-- Terminal-state evaluation at time zero is the stored initial state. -/
theorem admissibleStateAt_zero
    (z : AdmissibleJumpSequence (S := S)) :
    admissibleStateAt z 0 = (z.1 0).2 := by
  simp [admissibleStateAt, admissibleJumpIndex_zero]

/-- The exact Feynman--Kac integrand on the admissible path carrier. -/
def feynmanKacIntegrand
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ)
    (z : AdmissibleJumpSequence (S := S)) : ℝ :=
  Real.exp (k * finiteHorizonAdditiveReward v g T z) *
    f (admissibleStateAt z T)

/-- The pathwise Feynman--Kac integrand is measurable at every nonnegative
horizon. -/
theorem measurable_feynmanKacIntegrand
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ)
    (hT : 0 ≤ T) :
    Measurable (feynmanKacIntegrand v g k T f) := by
  unfold feynmanKacIntegrand
  exact ((measurable_finiteHorizonAdditiveReward v g T hT).const_mul k).exp.mul
    ((measurable_of_countable f).comp (measurable_admissibleStateAt T hT))

/-- Concrete path expectation appearing on the left side of the manuscript's
Feynman--Kac identity. -/
def pathMoment
    (x₀ : S) (p : S → ℝ) (L : Matrix S S ℝ)
    (hL : IsGenerator L) (hescape : ∀ x, 0 < escapeRate L x)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) : ℝ :=
  ∫ z, feynmanKacIntegrand v g k T f z
    ∂(admissiblePathLaw x₀ p L hL hescape)

/-- Point-mass initial distribution. -/
def pointMass (x : S) : S → ℝ :=
  fun y => if y = x then 1 else 0

theorem pointMass_nonnegative (x : S) :
    ∀ y, 0 ≤ pointMass x y := by
  intro y
  by_cases hyx : y = x <;> simp [pointMass, hyx]

theorem sum_pointMass (x : S) : ∑ y, pointMass x y = 1 := by
  simp [pointMass]

/-- The concrete conditional moment vector, indexed by the starting state. -/
def conditionalPathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) :
    S → ℝ :=
  fun x => pathMoment x (pointMass x) L hL hescape v g k T f

end NCG.FiniteCTMCFeynmanKacPathMoment
