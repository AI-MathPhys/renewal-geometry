/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCAdmissiblePathRestartExact

/-!
# Canonical reset of the CTMC dummy coordinate

Fresh jump-sequence laws store zero in the initial holding-time coordinate.
A raw tail does not have this property. Resetting only that dummy coordinate
preserves admissibility and all physical finite-horizon observables. The
first-jump Feynman--Kac cocycle therefore holds for the canonically reset
tail, the correct carrier for the subsequent law-level restart identity.
-/

open MeasureTheory

namespace NCG.FiniteCTMCCanonicalRestart

open FiniteCTMCPathCarrierMeasurability FiniteCTMCPathEvaluationMeasurability
open FiniteCTMCAdditiveRewardMeasurability FiniteCTMCFeynmanKacPathMoment
open FiniteCTMCAdmissiblePathRestart

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Reset only the nonphysical holding-time coordinate at index zero. -/
def resetDummy (z : ℕ → ℝ × S) (n : ℕ) : ℝ × S :=
  (if n = 0 then 0 else (z n).1, (z n).2)

theorem measurable_resetDummy : Measurable (resetDummy (S := S)) := by
  apply measurable_pi_lambda
  intro n
  by_cases hn : n = 0
  · simp only [resetDummy, hn, ite_true]
    fun_prop
  · simp only [resetDummy, hn, ite_false]
    fun_prop

@[simp] theorem resetDummy_state (z : ℕ → ℝ × S) (n : ℕ) :
    (resetDummy z n).2 = (z n).2 := rfl

@[simp] theorem resetDummy_initial_hold (z : ℕ → ℝ × S) :
    (resetDummy z 0).1 = 0 := by simp [resetDummy]

@[simp] theorem physicalHold_resetDummy (z : ℕ → ℝ × S) (n : ℕ) :
    physicalHold (resetDummy z) n = physicalHold z n := by
  simp [physicalHold, resetDummy]

@[simp] theorem cumulativeJumpTime_resetDummy (z : ℕ → ℝ × S) (n : ℕ) :
    cumulativeJumpTime (resetDummy z) n = cumulativeJumpTime z n := by
  simp [cumulativeJumpTime, funext (physicalHold_resetDummy z)]

theorem resetDummy_mem (z : AdmissibleJumpSequence (S := S)) :
    resetDummy z.1 ∈ admissibleJumpSequenceSet (S := S) := by
  simpa only [admissibleJumpSequenceSet, positiveHoldingSet, nonexplosiveHoldingSet,
    Set.mem_inter_iff, Set.mem_setOf_eq, physicalHold_resetDummy,
    cumulativeJumpTime_resetDummy] using z.2

def resetAdmissible (z : AdmissibleJumpSequence (S := S)) :
    AdmissibleJumpSequence (S := S) := ⟨resetDummy z.1, resetDummy_mem z⟩

@[simp] theorem resetAdmissible_coe (z : AdmissibleJumpSequence (S := S)) :
    (resetAdmissible z).1 = resetDummy z.1 := rfl

theorem measurable_resetAdmissible : Measurable (resetAdmissible (S := S)) :=
  Measurable.subtype_mk (measurable_resetDummy.comp measurable_subtype_coe)

theorem admissibleJumpIndex_resetAdmissible (z : AdmissibleJumpSequence (S := S))
    {T : ℝ} (hT : 0 ≤ T) :
    admissibleJumpIndex (resetAdmissible z) T = admissibleJumpIndex z T := by
  apply (admissibleJumpIndex_eq_iff (resetAdmissible z) hT _).mpr
  simpa only [resetAdmissible_coe, cumulativeJumpTime_resetDummy] using
    (admissibleJumpIndex_eq_iff z hT (admissibleJumpIndex z T)).mp rfl

theorem admissibleStateAt_resetAdmissible (z : AdmissibleJumpSequence (S := S))
    {T : ℝ} (hT : 0 ≤ T) : admissibleStateAt (resetAdmissible z) T = admissibleStateAt z T := by
  simp [admissibleStateAt, admissibleJumpIndex_resetAdmissible z hT]

theorem finiteHorizonAdditiveReward_resetAdmissible
    (v : S → ℝ) (g : S → S → ℝ) (z : AdmissibleJumpSequence (S := S))
    {T : ℝ} (hT : 0 ≤ T) :
    finiteHorizonAdditiveReward v g T (resetAdmissible z) =
      finiteHorizonAdditiveReward v g T z := by
  simp [finiteHorizonAdditiveReward, fixedJumpCountAdditiveReward,
    admissibleJumpIndex_resetAdmissible z hT]

theorem feynmanKacIntegrand_resetAdmissible
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) (f : S → ℝ)
    (z : AdmissibleJumpSequence (S := S)) {T : ℝ} (hT : 0 ≤ T) :
    feynmanKacIntegrand v g k T f (resetAdmissible z) =
      feynmanKacIntegrand v g k T f z := by
  rw [feynmanKacIntegrand, finiteHorizonAdditiveReward_resetAdmissible v g z hT,
    admissibleStateAt_resetAdmissible z hT]
  rfl

/-- The correctly normalized path carrier after the first physical jump. -/
def canonicalRestart (z : AdmissibleJumpSequence (S := S)) :
    AdmissibleJumpSequence (S := S) := resetAdmissible (tailAdmissibleJumpSequence z)

theorem measurable_canonicalRestart : Measurable (canonicalRestart (S := S)) :=
  measurable_resetAdmissible.comp measurable_tailAdmissibleJumpSequence

@[simp] theorem canonicalRestart_initial (z : AdmissibleJumpSequence (S := S)) :
    (canonicalRestart z).1 0 = (0, (z.1 1).2) := by
  simp [canonicalRestart, resetDummy, tailJumpSequence]

theorem feynmanKacIntegrand_eq_firstJump_mul_canonicalRestart
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ) (f : S → ℝ)
    (hfirst : physicalHold z.1 0 ≤ T) :
    feynmanKacIntegrand v g k T f z =
      Real.exp (k *
        (physicalHold z.1 0 * v (z.1 0).2 + g (z.1 0).2 (z.1 1).2)) *
        feynmanKacIntegrand v g k (T - physicalHold z.1 0) f (canonicalRestart z) := by
  rw [canonicalRestart, feynmanKacIntegrand_resetAdmissible v g k f
    (tailAdmissibleJumpSequence z) (sub_nonneg.mpr hfirst)]
  exact feynmanKacIntegrand_eq_firstJump_mul_tail v g k z T f hfirst

end

end NCG.FiniteCTMCCanonicalRestart
