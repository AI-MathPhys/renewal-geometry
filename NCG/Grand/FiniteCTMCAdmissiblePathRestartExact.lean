/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFeynmanKacPathMomentExact

/-!
# Restarting an admissible finite-CTMC path after its first jump

Dropping the first stored pair preserves strict positivity and nonexplosion.
The accompanying cumulative-time identity is the deterministic clock change
needed for the first-jump reward decomposition.
-/

open Finset Set
open scoped BigOperators

noncomputable section

namespace NCG.FiniteCTMCAdmissiblePathRestart

open NCG.FiniteCTMCPathCarrierMeasurability
open NCG.FiniteCTMCPathEvaluationMeasurability
open NCG.FiniteCTMCAdditiveRewardMeasurability
open NCG.FiniteCTMCFeynmanKacPathMoment
open NCG.NonexplosiveFiniteStatePath

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Tail of a stored holding-time/state sequence after its first physical
jump.  Its zeroth state is the destination of that jump. -/
def tailJumpSequence (z : ℕ → ℝ × S) : ℕ → ℝ × S :=
  fun n => z (n + 1)

/-- Dropping the first coordinate is measurable on the ambient sequence
space. -/
theorem measurable_tailJumpSequence :
    Measurable (tailJumpSequence : (ℕ → ℝ × S) → ℕ → ℝ × S) := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply (n + 1)

theorem physicalHold_tailJumpSequence
    (z : ℕ → ℝ × S) (n : ℕ) :
    physicalHold (tailJumpSequence z) n = physicalHold z (n + 1) := by
  simp [physicalHold, tailJumpSequence, Nat.add_assoc]

/-- Removing the first holding time shifts cumulative sums by exactly that
holding time. -/
theorem cumulativeHold_tail_add_first
    (hold : ℕ → ℝ) (n : ℕ) :
    cumulativeHold (fun i => hold (i + 1)) n + hold 0 =
      cumulativeHold hold (n + 1) := by
  induction n with
  | zero =>
      rw [cumulativeHold_zero, cumulativeHold_succ, cumulativeHold_zero,
        zero_add]
  | succ n ih =>
      rw [cumulativeHold_succ, cumulativeHold_succ]
      calc
        cumulativeHold (fun i => hold (i + 1)) n + hold (n + 1) + hold 0 =
            (cumulativeHold (fun i => hold (i + 1)) n + hold 0) +
              hold (n + 1) := by ring
        _ = cumulativeHold hold (n + 1) + hold (n + 1) := by rw [ih]

theorem cumulativeJumpTime_tail_add_first
    (z : ℕ → ℝ × S) (n : ℕ) :
    cumulativeJumpTime (tailJumpSequence z) n + physicalHold z 0 =
      cumulativeJumpTime z (n + 1) := by
  unfold cumulativeJumpTime
  have hfun : physicalHold (tailJumpSequence z) =
      fun i => physicalHold z (i + 1) := by
    funext i
    exact physicalHold_tailJumpSequence z i
  rw [hfun]
  exact cumulativeHold_tail_add_first (physicalHold z) n

/-- The tail of an admissible path is again admissible. -/
theorem tailJumpSequence_mem
    (z : AdmissibleJumpSequence (S := S)) :
    tailJumpSequence z.1 ∈ admissibleJumpSequenceSet (S := S) := by
  constructor
  · intro n
    rw [physicalHold_tailJumpSequence]
    exact z.2.1 (n + 1)
  · intro m
    obtain ⟨M : ℕ, hM⟩ := exists_nat_gt ((m : ℝ) + physicalHold z.1 0)
    obtain ⟨n, hn⟩ := z.2.2 M
    refine ⟨n, ?_⟩
    have hstep : cumulativeJumpTime z.1 (n + 1) <
        cumulativeJumpTime z.1 (n + 2) := by
      change cumulativeHold (physicalHold z.1) (n + 1) <
        cumulativeHold (physicalHold z.1) ((n + 1) + 1)
      exact (clockOfAdmissible z).cumulativeHold_strictMono (by omega)
    have hlarge : (m : ℝ) + physicalHold z.1 0 <
        cumulativeJumpTime z.1 (n + 2) :=
      hM.trans (hn.trans hstep)
    rw [← cumulativeJumpTime_tail_add_first z.1 (n + 1)] at hlarge
    linarith

/-- Canonical admissible tail path. -/
def tailAdmissibleJumpSequence
    (z : AdmissibleJumpSequence (S := S)) :
    AdmissibleJumpSequence (S := S) :=
  ⟨tailJumpSequence z.1, tailJumpSequence_mem z⟩

/-- Restarting is measurable on the admissible path carrier. -/
theorem measurable_tailAdmissibleJumpSequence :
    Measurable (tailAdmissibleJumpSequence :
      AdmissibleJumpSequence (S := S) → AdmissibleJumpSequence (S := S)) := by
  unfold tailAdmissibleJumpSequence
  exact Measurable.subtype_mk
    ((measurable_tailJumpSequence (S := S)).comp measurable_subtype_coe)

@[simp] theorem tailAdmissibleJumpSequence_coe
    (z : AdmissibleJumpSequence (S := S)) :
    (tailAdmissibleJumpSequence z : ℕ → ℝ × S) = tailJumpSequence z.1 := rfl

@[simp] theorem tailAdmissibleJumpSequence_initialState
    (z : AdmissibleJumpSequence (S := S)) :
    ((tailAdmissibleJumpSequence z).1 0).2 = (z.1 1).2 := by
  rfl

/-- Before the first holding time expires, the path has made no jump. -/
theorem admissibleJumpIndex_eq_zero_iff
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ) (hT : 0 ≤ T) :
    admissibleJumpIndex z T = 0 ↔ T < physicalHold z.1 0 := by
  rw [admissibleJumpIndex_eq_iff z hT 0]
  simp [cumulativeJumpTime, cumulativeHold_succ, hT]

/-- Once the first jump has occurred, the original jump index is one plus
the index of the restarted tail path. -/
theorem admissibleJumpIndex_eq_tail_add_one
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ)
    (hfirst : physicalHold z.1 0 ≤ T) :
    admissibleJumpIndex z T =
      admissibleJumpIndex (tailAdmissibleJumpSequence z)
        (T - physicalHold z.1 0) + 1 := by
  let ztail := tailAdmissibleJumpSequence z
  let n := admissibleJumpIndex ztail (T - physicalHold z.1 0)
  have htailT : 0 ≤ T - physicalHold z.1 0 := sub_nonneg.mpr hfirst
  have hT : 0 ≤ T := le_trans (z.2.1 0).le hfirst
  have hn := (admissibleJumpIndex_eq_iff ztail htailT n).1 rfl
  apply (admissibleJumpIndex_eq_iff z hT (n + 1)).2
  constructor
  · have hid := cumulativeJumpTime_tail_add_first z.1 n
    change cumulativeJumpTime ztail.1 n + physicalHold z.1 0 =
      cumulativeJumpTime z.1 (n + 1) at hid
    linarith [hn.1]
  · have hid := cumulativeJumpTime_tail_add_first z.1 (n + 1)
    change cumulativeJumpTime ztail.1 (n + 1) + physicalHold z.1 0 =
      cumulativeJumpTime z.1 (n + 1 + 1) at hid
    linarith [hn.2]

/-- Terminal-state evaluation is invariant under restarting after the first
jump, with the horizon shortened by the first holding time. -/
theorem admissibleStateAt_eq_tail
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ)
    (hfirst : physicalHold z.1 0 ≤ T) :
    admissibleStateAt z T =
      admissibleStateAt (tailAdmissibleJumpSequence z)
        (T - physicalHold z.1 0) := by
  unfold admissibleStateAt
  rw [admissibleJumpIndex_eq_tail_add_one z T hfirst]
  rfl

/-- Exact additive-reward cocycle at the first jump. -/
theorem finiteHorizonAdditiveReward_eq_firstJump_add_tail
    (v : S → ℝ) (g : S → S → ℝ)
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ)
    (hfirst : physicalHold z.1 0 ≤ T) :
    finiteHorizonAdditiveReward v g T z =
      physicalHold z.1 0 * v (z.1 0).2 + g (z.1 0).2 (z.1 1).2 +
        finiteHorizonAdditiveReward v g
          (T - physicalHold z.1 0) (tailAdmissibleJumpSequence z) := by
  let ztail := tailAdmissibleJumpSequence z
  let n := admissibleJumpIndex ztail (T - physicalHold z.1 0)
  have hindex : admissibleJumpIndex z T = n + 1 :=
    admissibleJumpIndex_eq_tail_add_one z T hfirst
  have htailIndex : admissibleJumpIndex ztail
      (T - physicalHold z.1 0) = n := rfl
  unfold finiteHorizonAdditiveReward
  rw [hindex, htailIndex]
  unfold fixedJumpCountAdditiveReward
  rw [Finset.sum_range_succ']
  have hcum := cumulativeJumpTime_tail_add_first z.1 n
  change cumulativeJumpTime ztail.1 n + physicalHold z.1 0 =
    cumulativeJumpTime z.1 (n + 1) at hcum
  dsimp [ztail, tailAdmissibleJumpSequence, tailJumpSequence] at hcum ⊢
  simp only [physicalHold, Nat.zero_add] at hcum ⊢
  rw [← hcum]
  have hsum :
      (∑ i ∈ Finset.range n,
        ((z.1 (i + 1 + 1)).1 * v (z.1 (i + 1)).2 +
          g (z.1 (i + 1)).2 (z.1 (i + 1 + 1)).2)) =
      ∑ i ∈ Finset.range n,
        ((tailJumpSequence z.1 (i + 1)).1 * v (z.1 (i + 1)).2 +
          g (z.1 (i + 1)).2 (z.1 (i + 1 + 1)).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [tailJumpSequence, Nat.add_comm, Nat.add_left_comm]
  rw [hsum]
  ring

/-- Before the first jump, the reward is just occupation reward in the
initial state. -/
theorem finiteHorizonAdditiveReward_eq_noJump
    (v : S → ℝ) (g : S → S → ℝ)
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ) (hT : 0 ≤ T)
    (hbefore : T < physicalHold z.1 0) :
    finiteHorizonAdditiveReward v g T z = T * v (z.1 0).2 := by
  have hindex : admissibleJumpIndex z T = 0 :=
    (admissibleJumpIndex_eq_zero_iff z T hT).2 hbefore
  unfold finiteHorizonAdditiveReward
  rw [hindex]
  simp [fixedJumpCountAdditiveReward, cumulativeJumpTime, cumulativeHold]

/-- Before the first jump, the Feynman--Kac integrand is the killed diagonal
term. -/
theorem feynmanKacIntegrand_eq_noJump
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ) (f : S → ℝ)
    (hT : 0 ≤ T) (hbefore : T < physicalHold z.1 0) :
    feynmanKacIntegrand v g k T f z =
      Real.exp (k * T * v (z.1 0).2) * f (z.1 0).2 := by
  unfold feynmanKacIntegrand
  rw [finiteHorizonAdditiveReward_eq_noJump v g z T hT hbefore]
  have hindex : admissibleJumpIndex z T = 0 :=
    (admissibleJumpIndex_eq_zero_iff z T hT).2 hbefore
  have hstate : admissibleStateAt z T = (z.1 0).2 := by
    simp [admissibleStateAt, hindex]
  have hexponent : k * (T * v (z.1 0).2) =
      k * T * v (z.1 0).2 := by ring
  rw [hstate, hexponent]

/-- After the first jump, the Feynman--Kac integrand factors into its first
holding/jump weight and the integrand of the restarted tail path. -/
theorem feynmanKacIntegrand_eq_firstJump_mul_tail
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (z : AdmissibleJumpSequence (S := S)) (T : ℝ) (f : S → ℝ)
    (hfirst : physicalHold z.1 0 ≤ T) :
    feynmanKacIntegrand v g k T f z =
      Real.exp (k *
        (physicalHold z.1 0 * v (z.1 0).2 + g (z.1 0).2 (z.1 1).2)) *
        feynmanKacIntegrand v g k (T - physicalHold z.1 0) f
          (tailAdmissibleJumpSequence z) := by
  unfold feynmanKacIntegrand
  rw [finiteHorizonAdditiveReward_eq_firstJump_add_tail v g z T hfirst,
    admissibleStateAt_eq_tail z T hfirst]
  rw [show k *
      (physicalHold z.1 0 * v (z.1 0).2 + g (z.1 0).2 (z.1 1).2 +
        finiteHorizonAdditiveReward v g (T - physicalHold z.1 0)
          (tailAdmissibleJumpSequence z)) =
      k * (physicalHold z.1 0 * v (z.1 0).2 + g (z.1 0).2 (z.1 1).2) +
        k * finiteHorizonAdditiveReward v g (T - physicalHold z.1 0)
          (tailAdmissibleJumpSequence z) by ring,
    Real.exp_add]
  ring

end NCG.FiniteCTMCAdmissiblePathRestart
