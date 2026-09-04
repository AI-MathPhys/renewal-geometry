/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCAdditiveRewardMeasurabilityExact

/-!
# Probability law on the admissible finite-CTMC path carrier

The Ionescu--Tulcea jump law gives the admissible event probability one.  A
measurable projection (using one fixed admissible sequence off that event)
therefore pushes the law to the subtype of admissible paths without changing
the underlying jump-sequence law after coercion.  This is the concrete
probability space on which the terminal state and additive reward are
measurable random variables.
-/

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal BigOperators

noncomputable section

namespace NCG.FiniteCTMCAdmissiblePathLaw

open NCG.DrivenProcess
open NCG.DrivenProcess.FinitePath
open NCG.FiniteCTMCJumpSequenceLaw
open NCG.FiniteCTMCPathCarrierMeasurability
open NCG.FiniteCTMCNonexplosion
open NCG.NonexplosiveFiniteStatePath

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- A canonical everywhere-unit holding sequence, used only as the value of
the measurable projection off the probability-one admissible event. -/
def unitHoldingJumpSequence (x : S) : ℕ → ℝ × S :=
  fun _ => (1, x)

/-- The unit-holding sequence is admissible. -/
theorem unitHoldingJumpSequence_mem (x : S) :
    unitHoldingJumpSequence x ∈ admissibleJumpSequenceSet (S := S) := by
  constructor
  · intro n
    simp [physicalHold, unitHoldingJumpSequence]
  · intro m
    refine ⟨m, ?_⟩
    simp [cumulativeJumpTime, cumulativeHold,
      physicalHold, unitHoldingJumpSequence]

/-- Fixed admissible sequence used by the total measurable projection. -/
def unitAdmissibleJumpSequence (x : S) :
    AdmissibleJumpSequence (S := S) :=
  ⟨unitHoldingJumpSequence x, unitHoldingJumpSequence_mem x⟩

/-- Total projection to the admissible subtype.  It is the identity on the
admissible event and takes a fixed admissible value elsewhere. -/
noncomputable def admissibleProjection (x : S) (z : ℕ → ℝ × S) :
    AdmissibleJumpSequence (S := S) := by
  classical
  exact if hz : z ∈ admissibleJumpSequenceSet (S := S) then ⟨z, hz⟩
    else unitAdmissibleJumpSequence x

/-- The projection to the measurable admissible carrier is measurable. -/
theorem measurable_admissibleProjection (x : S) :
    Measurable (admissibleProjection (S := S) x) := by
  classical
  unfold admissibleProjection
  exact Measurable.dite measurable_id measurable_const
    measurableSet_admissibleJumpSequenceSet

/-- Probability law of the genuine CTMC on the admissible path carrier. -/
def admissiblePathLaw
    (x₀ : S) (p : S → ℝ) (L : Matrix S S ℝ)
    (hL : IsGenerator L) (hescape : ∀ x, 0 < escapeRate L x) :
    Measure (AdmissibleJumpSequence (S := S)) :=
  (jumpSequenceLaw p L hL hescape).map (admissibleProjection x₀)

/-- The admissible path law is a probability measure. -/
theorem admissiblePathLaw_isProbabilityMeasure
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) :
    IsProbabilityMeasure (admissiblePathLaw x₀ p L hL hescape) := by
  letI : IsProbabilityMeasure (jumpSequenceLaw p L hL hescape) :=
    jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
  unfold admissiblePathLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_admissibleProjection x₀).aemeasurable

/-- On the probability-one admissible event, coercing the projection back to
the ambient jump-sequence space is the identity almost surely. -/
theorem ae_coe_admissibleProjection_eq_id
    [Nonempty S]
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) :
    (fun z => (admissibleProjection x₀ z : ℕ → ℝ × S)) =ᵐ[
      jumpSequenceLaw p L hL hescape] id := by
  classical
  let μ := jumpSequenceLaw p L hL hescape
  letI : IsProbabilityMeasure μ :=
    jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
  have hadm : ∀ᵐ z ∂μ,
      z ∈ admissibleJumpSequenceSet (S := S) := by
    apply (ae_mem_iff_measure_eq
      measurableSet_admissibleJumpSequenceSet.nullMeasurableSet).2
    simpa [μ] using jumpSequenceLaw_admissibleJumpSequenceSet_eq_one
      p hp hp1 L hL hescape
  filter_upwards [hadm] with z hz
  simp [admissibleProjection, hz]

/-- Coercing the admissible path law back to ambient jump sequences recovers
the original Ionescu--Tulcea law exactly. -/
theorem map_subtypeVal_admissiblePathLaw
    [Nonempty S]
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) :
    (admissiblePathLaw x₀ p L hL hescape).map
        ((↑) : AdmissibleJumpSequence (S := S) → ℕ → ℝ × S) =
      jumpSequenceLaw p L hL hescape := by
  unfold admissiblePathLaw
  rw [Measure.map_map measurable_subtype_coe
    (measurable_admissibleProjection x₀)]
  have hae :
      (Subtype.val ∘ admissibleProjection x₀) =ᵐ[
        jumpSequenceLaw p L hL hescape] id := by
    simpa [Function.comp_def] using
      ae_coe_admissibleProjection_eq_id x₀ p hp hp1 L hL hescape
  rw [Measure.map_congr hae]
  exact Measure.map_id

end NCG.FiniteCTMCAdmissiblePathLaw
