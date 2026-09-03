/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCNonexplosionExact

/-!
# Measurable finite-horizon evaluation of admissible CTMC paths

On the admissible jump-sequence carrier, the occupied-state index at a
nonnegative time is characterized by two finite cumulative-time inequalities.
This makes the index measurable.  A countable decomposition by that index
then proves measurability of the terminal state.
-/

open MeasureTheory Finset Set
open scoped BigOperators

noncomputable section

namespace NCG.FiniteCTMCPathEvaluationMeasurability

open NCG.NonexplosiveFiniteStatePath
open NCG.FiniteCTMCPathCarrierMeasurability

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- At nonnegative time, a clock's jump index is exactly characterized by
the two adjacent cumulative jump times. -/
theorem jumpIndex_eq_iff_of_nonnegative_time
    (clock : Clock) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    jumpIndex clock T = n ↔
      cumulativeHold clock.hold n ≤ T ∧
        T < cumulativeHold clock.hold (n + 1) := by
  constructor
  · intro hindex
    constructor
    · cases n with
      | zero => simpa using hT
      | succ m =>
          have hm : m < jumpIndex clock T := by omega
          simpa using earlierJump_le_time clock T hm
    · simpa [hindex] using jumpIndex_lt_nextJump clock T
  · rintro ⟨hlower, hupper⟩
    exact jumpIndex_eq_of_between clock n T hlower hupper

/-- Occupied-state index of an admissible jump sequence at time `T`. -/
def admissibleJumpIndex
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ) : ℕ :=
  jumpIndex (clockOfAdmissible z) T

/-- Characterization in the original measurable jump-sequence coordinates. -/
theorem admissibleJumpIndex_eq_iff
    (z : AdmissibleJumpSequence (S := S)) {T : ℝ}
    (hT : 0 ≤ T) (n : ℕ) :
    admissibleJumpIndex z T = n ↔
      cumulativeJumpTime z.1 n ≤ T ∧
        T < cumulativeJumpTime z.1 (n + 1) := by
  simpa [admissibleJumpIndex, clockOfAdmissible,
    clockOfJumpSequence, cumulativeJumpTime, physicalHold] using
    jumpIndex_eq_iff_of_nonnegative_time (clockOfAdmissible z) hT n

/-- The random finite-horizon jump index is measurable on the admissible
carrier. -/
theorem measurable_admissibleJumpIndex (T : ℝ) (hT : 0 ≤ T) :
    Measurable (fun z : AdmissibleJumpSequence (S := S) =>
      admissibleJumpIndex z T) := by
  apply measurable_to_countable'
  intro n
  have hset :
      (fun z : AdmissibleJumpSequence (S := S) =>
        admissibleJumpIndex z T) ⁻¹' ({n} : Set ℕ) =
      {z | cumulativeJumpTime z.1 n ≤ T} ∩
        {z | T < cumulativeJumpTime z.1 (n + 1)} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    exact admissibleJumpIndex_eq_iff z hT n
  rw [hset]
  apply MeasurableSet.inter
  · exact measurableSet_le
      ((measurable_cumulativeJumpTime (S := S) n).comp
        measurable_subtype_coe) measurable_const
  · exact measurableSet_lt measurable_const
      ((measurable_cumulativeJumpTime (S := S) (n + 1)).comp
        measurable_subtype_coe)

/-- State occupied by an admissible jump sequence at time `T`. -/
def admissibleStateAt
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ) : S :=
  (z.1 (admissibleJumpIndex z T)).2

/-- Finite-state terminal evaluation is measurable. -/
theorem measurable_admissibleStateAt (T : ℝ) (hT : 0 ≤ T) :
    Measurable (fun z : AdmissibleJumpSequence (S := S) =>
      admissibleStateAt z T) := by
  apply measurable_to_countable'
  intro x
  have hpreimage :
      (fun z : AdmissibleJumpSequence (S := S) =>
        admissibleStateAt z T) ⁻¹' ({x} : Set S) =
      ⋃ n : ℕ,
        {z | admissibleJumpIndex z T = n} ∩
          {z | (z.1 n).2 = x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq, admissibleStateAt]
    constructor
    · intro hz
      exact ⟨admissibleJumpIndex z T, rfl, hz⟩
    · rintro ⟨n, hn, hx⟩
      simpa [hn] using hx
  rw [hpreimage]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact (measurable_admissibleJumpIndex T hT)
      (measurableSet_singleton n)
  · exact (measurable_snd.comp
      ((measurable_pi_apply n).comp measurable_subtype_coe))
        (measurableSet_singleton x)

/-- The state evaluation agrees definitionally with the canonical càdlàg
step path on the admissible carrier. -/
theorem admissibleStateAt_eq_cadlagPath
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ) :
    admissibleStateAt z T = (cadlagPathOfAdmissible z).toFun T := rfl

end NCG.FiniteCTMCPathEvaluationMeasurability
