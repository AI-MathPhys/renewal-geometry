/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NonexplosiveFiniteStatePathExact

/-!
# Measurable carrier of finite-CTMC càdlàg paths

Positive holding times and nonexplosion are countable measurable conditions
on an infinite holding-time/state sequence.  This file isolates that event
and constructs the canonical finite-state càdlàg step path from every point
of the resulting measurable carrier.
-/

open MeasureTheory Set Finset
open scoped BigOperators ENNReal

noncomputable section

namespace NCG.FiniteCTMCPathCarrierMeasurability

open NCG.NonexplosiveFiniteStatePath

set_option linter.unusedSectionVars false

variable {S : Type*} [MeasurableSpace S]

/-- Physical holding-time sequence obtained by dropping the dummy initial
entry of a jump sequence. -/
def physicalHold (z : ℕ → ℝ × S) (n : ℕ) : ℝ :=
  (z (n + 1)).1

/-- Time of the `n`th physical jump in an infinite jump sequence. -/
def cumulativeJumpTime (z : ℕ → ℝ × S) (n : ℕ) : ℝ :=
  cumulativeHold (physicalHold z) n

/-- Each finite cumulative jump-time coordinate is measurable. -/
theorem measurable_cumulativeJumpTime (n : ℕ) :
    Measurable (fun z : ℕ → ℝ × S => cumulativeJumpTime z n) := by
  unfold cumulativeJumpTime cumulativeHold physicalHold
  fun_prop

/-- Event that every physical holding time is strictly positive. -/
def positiveHoldingSet : Set (ℕ → ℝ × S) :=
  {z | ∀ n, 0 < physicalHold z n}

/-- Positivity of all holding times is a measurable event. -/
theorem measurableSet_positiveHoldingSet :
    MeasurableSet (positiveHoldingSet (S := S)) := by
  rw [show positiveHoldingSet (S := S) =
      ⋂ n : ℕ, {z : ℕ → ℝ × S | 0 < physicalHold z n} by
    ext z
    simp [positiveHoldingSet]]
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_lt measurable_const
    (measurable_fst.comp (measurable_pi_apply (n + 1)))

/-- Countable nonexplosion event: every natural time level is eventually
strictly below a cumulative jump time. -/
def nonexplosiveHoldingSet : Set (ℕ → ℝ × S) :=
  {z | ∀ m : ℕ, ∃ n : ℕ, (m : ℝ) < cumulativeJumpTime z (n + 1)}

/-- Nonexplosion is a measurable event. -/
theorem measurableSet_nonexplosiveHoldingSet :
    MeasurableSet (nonexplosiveHoldingSet (S := S)) := by
  rw [show nonexplosiveHoldingSet (S := S) =
      ⋂ m : ℕ, ⋃ n : ℕ,
        {z : ℕ → ℝ × S | (m : ℝ) < cumulativeJumpTime z (n + 1)} by
    ext z
    simp [nonexplosiveHoldingSet]]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_lt measurable_const
    (measurable_cumulativeJumpTime (S := S) (n + 1))

/-- Measurable event of sequences that define nonexplosive finite-state
càdlàg paths. -/
def admissibleJumpSequenceSet : Set (ℕ → ℝ × S) :=
  positiveHoldingSet ∩ nonexplosiveHoldingSet

theorem measurableSet_admissibleJumpSequenceSet :
    MeasurableSet (admissibleJumpSequenceSet (S := S)) :=
  measurableSet_positiveHoldingSet.inter measurableSet_nonexplosiveHoldingSet

/-- The measurable carrier of admissible jump sequences. -/
abbrev AdmissibleJumpSequence :=
  ↥(admissibleJumpSequenceSet (S := S))

/-- A countably nonexplosive sequence is nonexplosive at every real time. -/
theorem real_nonexplosion_of_mem
    {z : ℕ → ℝ × S} (hz : z ∈ nonexplosiveHoldingSet) :
    ∀ T : ℝ, ∃ n : ℕ,
      T < cumulativeHold (physicalHold z) (n + 1) := by
  intro T
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt T
  obtain ⟨n, hn⟩ := hz m
  exact ⟨n, hm.trans hn⟩

/-- Canonical nonexplosive clock carried by an admissible sequence. -/
def clockOfAdmissible (z : AdmissibleJumpSequence (S := S)) : Clock :=
  clockOfJumpSequence z.1
    (by
      intro n
      exact z.2.1 n)
    (real_nonexplosion_of_mem z.2.2)

/-- Canonical càdlàg finite-state path carried by an admissible sequence. -/
def cadlagPathOfAdmissible
    (z : AdmissibleJumpSequence (S := S)) : CadlagStepPath S :=
  cadlagStepPathOfJumpSequence z.1
    (by
      intro n
      exact z.2.1 n)
    (real_nonexplosion_of_mem z.2.2)

/-- Every point of the measurable admissible carrier therefore determines a
right-continuous finite-state path with left limits and finitely bounded jump
index on each compact horizon. -/
theorem cadlagPathOfAdmissible_regular
    (z : AdmissibleJumpSequence (S := S)) :
    (∀ t, ∃ delta : ℝ, 0 < delta ∧
      ∀ s, t ≤ s → s < t + delta →
        (cadlagPathOfAdmissible z).toFun s =
          (cadlagPathOfAdmissible z).toFun t) ∧
    (∀ t, 0 < t → ∃ leftState : S, ∃ delta : ℝ, 0 < delta ∧
      ∀ s, 0 ≤ s → t - delta < s → s < t →
        (cadlagPathOfAdmissible z).toFun s = leftState) :=
  ⟨(cadlagPathOfAdmissible z).rightLocallyConstant,
    (cadlagPathOfAdmissible z).leftLocallyConstant⟩

end NCG.FiniteCTMCPathCarrierMeasurability
