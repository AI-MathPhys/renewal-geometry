/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteGeneratorPositiveEscapeLiftExact
import NCG.Grand.FiniteCTMCInitialMixtureExact

/-!
# Measurable projection of the auxiliary-clock CTMC path

Forgetting the Boolean clock preserves every holding interval and therefore
the nonexplosive cadlag physical path. Repeated physical states are allowed
on this carrier: their clock-only ticks are not physical jumps and receive
zero jump reward. Occupation reward and all visible jump rewards agree
pathwise with those of the lifted process.
-/

open MeasureTheory Set
open scoped Topology

namespace NCG.FiniteCTMCClockProjection

open FiniteGeneratorPositiveEscapeLift FiniteCTMCPathCarrierMeasurability
open FiniteCTMCPathEvaluationMeasurability FiniteCTMCAdditiveRewardMeasurability

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Drop the auxiliary state but keep the nonexplosive physical clock. -/
def forgetClockSequence (z : ℕ → ℝ × (Bool × S)) : ℕ → ℝ × S :=
  fun n => ((z n).1, (z n).2.2)

/-- Admissibility depends only on holding times and is preserved exactly. -/
theorem forgetClockSequence_mem (z : AdmissibleJumpSequence (S := Bool × S)) :
    forgetClockSequence z.1 ∈ admissibleJumpSequenceSet (S := S) := z.2

/-- The physical path carried by the lifted process. -/
def forgetClockPath (z : AdmissibleJumpSequence (S := Bool × S)) :
    AdmissibleJumpSequence (S := S) :=
  ⟨forgetClockSequence z.1, forgetClockSequence_mem z⟩

/-- Forgetting the clock is a measurable map of actual path spaces. -/
theorem measurable_forgetClockPath : Measurable (forgetClockPath (S := S)) := by
  unfold forgetClockPath forgetClockSequence
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro n
  have hn : Measurable (fun z : AdmissibleJumpSequence (S := Bool × S) => z.1 n) :=
    (measurable_pi_apply n).comp measurable_subtype_coe
  exact hn.fst.prodMk hn.snd.snd

/-- The occupied-interval index is unchanged by projection. -/
theorem admissibleJumpIndex_forgetClockPath
    (z : AdmissibleJumpSequence (S := Bool × S)) (T : ℝ) :
    admissibleJumpIndex (forgetClockPath z) T = admissibleJumpIndex z T := rfl

/-- Terminal physical state is exactly the second component of the lifted state. -/
theorem admissibleStateAt_forgetClockPath
    (z : AdmissibleJumpSequence (S := Bool × S)) (T : ℝ) :
    admissibleStateAt (forgetClockPath z) T = (admissibleStateAt z T).2 := rfl

/-- A tick that does not change the physical state is not a physical jump. -/
def visibleJumpReward (g : S → S → ℝ) : S → S → ℝ :=
  fun i j => if i = j then 0 else g i j

@[simp] theorem visibleJumpReward_self (g : S → S → ℝ) (i : S) :
    visibleJumpReward g i i = 0 := by simp [visibleJumpReward]

theorem visibleJumpReward_apply_ne (g : S → S → ℝ) (i j : S) (hij : i ≠ j) :
    visibleJumpReward g i j = g i j := by simp [visibleJumpReward, hij]

/-- The occupation-plus-visible-jump reward of the physical process. -/
def visibleReward (v : S → ℝ) (g : S → S → ℝ) (T : ℝ)
    (z : AdmissibleJumpSequence (S := S)) : ℝ :=
  finiteHorizonAdditiveReward v (visibleJumpReward g) T z

theorem measurable_visibleReward (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    Measurable (visibleReward v g T) :=
  measurable_finiteHorizonAdditiveReward v (visibleJumpReward g) T hT

/-- Exact pathwise reward identity: invisible clock flips contribute zero,
and no occupation or genuine jump reward is lost. -/
theorem visibleReward_forgetClockPath (v : S → ℝ) (g : S → S → ℝ) (T : ℝ)
    (z : AdmissibleJumpSequence (S := Bool × S)) :
    visibleReward v g T (forgetClockPath z) =
      finiteHorizonAdditiveReward (liftFunction v) (liftJumpReward g) T z := rfl

end

end NCG.FiniteCTMCClockProjection
