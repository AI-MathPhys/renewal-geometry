/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCJumpSequenceLawExact
import NCG.Grand.FiniteCTMCPathCarrierMeasurabilityExact
import NCG.Grand.TrajectoryKernelAlmostSureEventExact

/-!
# Almost-sure positivity of finite-CTMC holding times

The exponential holding-time component of every transition is strictly
positive almost surely.  The generic Ionescu--Tulcea event-transfer lemma
then gives positivity of each physical holding coordinate, and a countable
intersection gives positivity of the entire infinite holding sequence.
-/

open MeasureTheory ProbabilityTheory Finset Set Preorder
open ProbabilityTheory.Kernel
open scoped ENNReal

noncomputable section

namespace NCG.FiniteCTMCHoldingPositivity

open NCG.DrivenProcess
open NCG.DrivenProcess.FinitePath
open NCG.FiniteCTMCJumpSequenceLaw
open NCG.FiniteCTMCPathCarrierMeasurability
open NCG.QuantumCylinderInverseLimit
open NCG.TrajectoryKernelAlmostSureEvent

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- An exponential random variable with positive rate is strictly positive
almost surely. -/
theorem expMeasure_Ioi_zero_eq_one {r : ℝ} (hr : 0 < r) :
    ProbabilityTheory.expMeasure r (Set.Ioi 0) = 1 := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  have hzero : ProbabilityTheory.expMeasure r (Set.Iic 0) = 0 := by
    rw [← ProbabilityTheory.ofReal_cdf,
      ProbabilityTheory.cdf_expMeasure_eq hr]
    norm_num
  rw [← compl_Iic,
    measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, hzero]
  norm_num

/-- Every CTMC one-step law assigns mass one to a positive holding time. -/
theorem holdingDestinationMeasure_positive_eq_one
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (x : S) :
    holdingDestinationMeasure L x (Set.Ioi 0 ×ˢ (Set.univ : Set S)) = 1 := by
  letI : IsProbabilityMeasure (destinationMeasure L x) :=
    destinationMeasure_isProbabilityMeasure L hL hescape x
  unfold holdingDestinationMeasure
  rw [Measure.prod_prod, expMeasure_Ioi_zero_eq_one (hescape x)]
  simp

/-- Every individual physical holding coordinate is positive almost surely
under the genuine jump-sequence law. -/
theorem jumpSequenceLaw_physicalHold_positive_eq_one
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (n : ℕ) :
    jumpSequenceLaw p L hL hescape
        {z | 0 < physicalHold z n} = 1 := by
  letI : IsProbabilityMeasure (initialHoldingStateMeasure p) :=
    initialHoldingStateMeasure_isProbabilityMeasure p hp hp1
  letI : ∀ a, IsMarkovKernel (historyJumpKernel L a) :=
    fun a => historyJumpKernel_isMarkov L hL hescape a
  have hnext :
      trajMeasure (initialHoldingStateMeasure p) (historyJumpKernel L)
          {z : ℕ → ℝ × S |
            z (n + 1) ∈ Set.Ioi 0 ×ˢ (Set.univ : Set S)} = 1 :=
    trajMeasure_next_mem_eq_one
      (X := fun _ => ℝ × S)
      (μ₀ := initialHoldingStateMeasure p)
      (κ := historyJumpKernel L) n
      (Set.Ioi 0 ×ˢ (Set.univ : Set S))
      (measurableSet_Ioi.prod MeasurableSet.univ)
      (fun history => by
        change holdingDestinationMeasure L (currentState n history)
          (Set.Ioi 0 ×ˢ (Set.univ : Set S)) = 1
        exact holdingDestinationMeasure_positive_eq_one
          L hL hescape (currentState n history))
  simpa [jumpSequenceLaw, historyJumpKernel, jumpKernel,
    physicalHold] using hnext

/-- All physical holding coordinates are simultaneously positive almost
surely. -/
theorem jumpSequenceLaw_positiveHoldingSet_eq_one
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) :
    jumpSequenceLaw p L hL hescape (positiveHoldingSet (S := S)) = 1 := by
  letI : IsProbabilityMeasure (jumpSequenceLaw p L hL hescape) :=
    jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
  calc
    jumpSequenceLaw p L hL hescape (positiveHoldingSet (S := S)) =
        jumpSequenceLaw p L hL hescape Set.univ := by
      apply (ae_iff_measure_eq
        measurableSet_positiveHoldingSet.nullMeasurableSet).mp
      change ∀ᵐ z ∂jumpSequenceLaw p L hL hescape,
        ∀ n : ℕ, 0 < physicalHold z n
      apply ae_all_iff.2
      intro n
      apply (ae_iff_measure_eq
        (measurableSet_lt measurable_const
          (measurable_fst.comp
            (measurable_pi_apply (n + 1)))).nullMeasurableSet).2
      simpa [physicalHold] using
        jumpSequenceLaw_physicalHold_positive_eq_one
          p hp hp1 L hL hescape n
    _ = 1 := measure_univ

end NCG.FiniteCTMCHoldingPositivity
