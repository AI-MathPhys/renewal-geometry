/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFeynmanKacIntegrabilityExact
import NCG.Grand.FiniteCTMCRestartMomentExact

/-!
# First-jump conditioning of the concrete Feynman--Kac expectation

The genuine path expectation is disintegrated over its first sampled jump.
Continuation support fixes the retained prefix; the pathwise cocycle and
proved homogeneous restart identify its conditional moment. Integrability
is derived from the actual CTMC law, not postulated.
-/

open MeasureTheory ProbabilityTheory Preorder
open ProbabilityTheory.Kernel

namespace NCG.FiniteCTMCFirstJumpConditioning

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCJumpSequenceLaw
open FiniteCTMCPathLawDisintegration FiniteCTMCHomogeneousRestartLaw
open FiniteCTMCPathCarrierMeasurability FiniteCTMCAdmissiblePathLaw
open FiniteCTMCFeynmanKacPathMoment FiniteCTMCFeynmanKacIntegrability
open FiniteCTMCAdmissiblePathRestart FiniteCTMCCanonicalRestart FiniteCTMCRestartMoment
open FiniteCTMCRestartPrefixLaw

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
  (hescape : ∀ x, 0 < escapeRate L x)

/-- A continuation retains exactly the finite history it is given. -/
theorem ae_continuation_prefix_eq (a : ℕ) (h : Finset.Iic a → ℝ × S) :
    ∀ᵐ z ∂continuationKernel L hL hescape a h, frestrictLe a z = h := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  apply ae_of_ae_map (μ := continuationKernel L hL hescape a h) (p := fun y => y = h)
    (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) a).aemeasurable
  change ∀ᵐ z ∂(Kernel.traj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) a h).map
    (frestrictLe a), z = h
  rw [Kernel.traj_map_frestrictLe_apply, partialTraj_self, Kernel.id_apply]
  exact (ae_dirac_iff (measurableSet_singleton h)).mpr rfl

/-- Conditional first-jump moment as an explicit function of the sampled
two-pair history. The branch at a jump exactly at the horizon is the jump branch. -/
def firstJumpPrefixMoment
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ)
    (h : Finset.Iic 1 → ℝ × S) : ℝ :=
  let x := (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩).2
  let q := h ⟨1, Finset.mem_Iic.mpr le_rfl⟩
  if T < q.1 then Real.exp (k*T*v x) * f x
  else Real.exp (k * (q.1*v x + g x q.2)) *
    conditionalPathMoment L hL hescape v g k (T-q.1) f q.2

/-- Exact conditional expectation for almost surely admissible continuations. -/
theorem integral_continuation_eq_firstJumpPrefixMoment
    (x₀ : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T)
    (h : Finset.Iic 1 → ℝ × S)
    (hadm : ∀ᵐ z ∂continuationKernel L hL hescape 1 h,
      z ∈ admissibleJumpSequenceSet (S := S)) :
    (∫ z, feynmanKacIntegrand v g k T f (admissibleProjection x₀ z)
      ∂continuationKernel L hL hescape 1 h) =
      firstJumpPrefixMoment L hL hescape v g k T f h := by
  have hp := ae_continuation_prefix_eq L hL hescape 1 h
  by_cases hbefore : T < (h ⟨1, Finset.mem_Iic.mpr le_rfl⟩).1
  · have heq : (fun z => feynmanKacIntegrand v g k T f (admissibleProjection x₀ z)) =ᵐ[
        continuationKernel L hL hescape 1 h]
        (fun _ => Real.exp (k*T*v (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩).2) * f (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩).2) := by
      filter_upwards [hadm, hp] with z hz hprefix
      have hz0 : z 0 = h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩ := congrFun hprefix ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩
      have hz1 : z 1 = h ⟨1, Finset.mem_Iic.mpr le_rfl⟩ := congrFun hprefix ⟨1, Finset.mem_Iic.mpr le_rfl⟩
      simp only [admissibleProjection, dif_pos hz]
      rw [feynmanKacIntegrand_eq_noJump v g k ⟨z,hz⟩ T f hT (by
        simpa only [physicalHold, hz1] using hbefore)]
      simp only [Subtype.coe_mk, hz0]
    rw [integral_congr_ae heq]
    simp only [firstJumpPrefixMoment, if_pos hbefore, MeasureTheory.integral_const,
      probReal_univ, one_smul]
  · have hafter : (h ⟨1, Finset.mem_Iic.mpr le_rfl⟩).1 ≤ T := le_of_not_gt hbefore
    have heq : (fun z => feynmanKacIntegrand v g k T f (admissibleProjection x₀ z)) =ᵐ[
        continuationKernel L hL hescape 1 h]
        (fun z => Real.exp (k * ((h ⟨1, Finset.mem_Iic.mpr le_rfl⟩).1 * v (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩).2 +
            g (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩).2 (h ⟨1, Finset.mem_Iic.mpr le_rfl⟩).2)) *
          feynmanKacIntegrand v g k (T-(h ⟨1, Finset.mem_Iic.mpr le_rfl⟩).1) f
            (admissibleProjection (currentState 1 h) (resetShift 1 z))) := by
      filter_upwards [hadm, hp] with z hz hprefix
      have hz0 : z 0 = h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩ := congrFun hprefix ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩
      have hz1 : z 1 = h ⟨1, Finset.mem_Iic.mpr le_rfl⟩ := congrFun hprefix ⟨1, Finset.mem_Iic.mpr le_rfl⟩
      have hre : admissibleProjection (currentState 1 h) (resetShift 1 z) =
          canonicalRestart ⟨z,hz⟩ := by
        rw [resetShift_one_eq_canonicalRestart ⟨z,hz⟩]
        simp only [admissibleProjection, dif_pos (canonicalRestart ⟨z,hz⟩).2]
      rw [hre]
      simp only [admissibleProjection, dif_pos hz]
      rw [feynmanKacIntegrand_eq_firstJump_mul_canonicalRestart v g k ⟨z,hz⟩ T f (by
        simpa only [physicalHold, hz1] using hafter)]
      simp only [physicalHold, hz0, hz1]
    rw [integral_congr_ae heq, integral_const_mul,
      integral_restart_eq_conditionalPathMoment L hL hescape 1 h v g k
        (T-(h ⟨1, Finset.mem_Iic.mpr le_rfl⟩).1) f (sub_nonneg.mpr hafter)]
    simp only [firstJumpPrefixMoment, if_neg hbefore, currentState]

/-- First-jump total expectation for the actual point-start path moment.
This is derived from integrability, full path disintegration, and restart. -/
theorem conditionalPathMoment_eq_integral_firstJumpPrefixMoment
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    conditionalPathMoment L hL hescape v g k T f x =
      ∫ h, firstJumpPrefixMoment L hL hescape v g k T f h
        ∂jumpPrefixLaw (pointMass x) L hL hescape 1 := by
  letI : Nonempty S := ⟨x⟩
  have hf := integrable_feynmanKacIntegrand L hL hescape x v g k T f hT
  have hm := measurable_feynmanKacIntegrand v g k T f hT
  have hraw : Integrable (fun z => feynmanKacIntegrand v g k T f (admissibleProjection x z))
      (jumpSequenceLaw (pointMass x) L hL hescape) :=
    (integrable_map_measure hm.aestronglyMeasurable
      (measurable_admissibleProjection x).aemeasurable).mp hf
  unfold conditionalPathMoment pathMoment admissiblePathLaw
  rw [integral_map (measurable_admissibleProjection x).aemeasurable hm.aestronglyMeasurable,
    integral_jumpSequenceLaw_eq_prefix_continuation L hL hescape (pointMass x)
      (pointMass_nonnegative x) (sum_pointMass x) hraw 1]
  apply integral_congr_ae
  filter_upwards [ae_continuation_admissible L hL hescape (pointMass x)
    (pointMass_nonnegative x) (sum_pointMass x) 1] with h hh
  exact integral_continuation_eq_firstJumpPrefixMoment L hL hescape x v g k T f hT h hh

/-- The explicit prefix-conditioned moment is integrable, as a consequence
of integrability of the original path observable. -/
theorem integrable_firstJumpPrefixMoment
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    Integrable (firstJumpPrefixMoment L hL hescape v g k T f)
      (jumpPrefixLaw (pointMass x) L hL hescape 1) := by
  letI : Nonempty S := ⟨x⟩
  letI : IsProbabilityMeasure (jumpPrefixLaw (pointMass x) L hL hescape 1) :=
    jumpPrefixLaw_isProbabilityMeasure (pointMass x) (pointMass_nonnegative x)
      (sum_pointMass x) L hL hescape 1
  have hm := measurable_feynmanKacIntegrand v g k T f hT
  have hraw : Integrable (fun z => feynmanKacIntegrand v g k T f (admissibleProjection x z))
      (jumpSequenceLaw (pointMass x) L hL hescape) :=
    (integrable_map_measure hm.aestronglyMeasurable
      (measurable_admissibleProjection x).aemeasurable).mp
      (integrable_feynmanKacIntegrand L hL hescape x v g k T f hT)
  rw [jumpSequenceLaw_eq_continuation_comp_prefix L hL hescape (pointMass x) 1,
    Measure.comp_eq_comp_const_apply] at hraw
  have hi := hraw.integral_comp
  simp only [Kernel.const_apply] at hi
  apply hi.congr
  filter_upwards [ae_continuation_admissible L hL hescape (pointMass x)
    (pointMass_nonnegative x) (sum_pointMass x) 1] with h hh
  exact integral_continuation_eq_firstJumpPrefixMoment L hL hescape x v g k T f hT h hh

/-- The first sampled prefix has the actual holding/destination law. -/
theorem jumpPrefixLaw_pointMass_one (x : S) :
    jumpPrefixLaw (pointMass x) L hL hescape 1 =
      (holdingDestinationMeasure L x).map (appendHistory 0 (pointInitialPrefix x)) := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  unfold jumpPrefixLaw
  rw [jumpSequenceLaw_pointMass_eq_continuation L hL hescape x]
  change (Kernel.traj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) 0
    (pointInitialPrefix x)).map (frestrictLe 1) = _
  rw [Kernel.traj_map_frestrictLe_apply, partialTraj_step_apply L hL hescape]
  rfl

/-- The exact first-jump renewal integrand on holding-time/destination space. -/
def firstJumpHoldingMoment
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (q : ℝ × S) : ℝ :=
  if T < q.1 then Real.exp (k*T*v x) * f x
  else Real.exp (k * (q.1*v x + g x q.2)) *
    conditionalPathMoment L hL hescape v g k (T-q.1) f q.2

theorem firstJumpPrefixMoment_append_initial
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (q : ℝ × S) :
    firstJumpPrefixMoment L hL hescape v g k T f
      (appendHistory 0 (pointInitialPrefix x) q) =
      firstJumpHoldingMoment L hL hescape x v g k T f q := by
  have hzero : appendHistory 0 (pointInitialPrefix x) q
      ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 1)⟩ = (0,x) :=
    appendHistory_apply_le 0 (pointInitialPrefix x) q _ le_rfl
  simp only [firstJumpPrefixMoment, hzero, appendHistory_apply_last, firstJumpHoldingMoment]

/-- Integrability of the concrete first-jump renewal integrand. -/
theorem integrable_firstJumpHoldingMoment
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    Integrable (firstJumpHoldingMoment L hL hescape x v g k T f)
      (holdingDestinationMeasure L x) := by
  have hi := integrable_firstJumpPrefixMoment L hL hescape x v g k T f hT
  rw [jumpPrefixLaw_pointMass_one] at hi
  have hcomp := (integrable_map_measure hi.aestronglyMeasurable
    (measurable_appendHistory 0 (pointInitialPrefix x)).aemeasurable).mp hi
  simpa only [Function.comp_def, firstJumpPrefixMoment_append_initial] using hcomp

/-- The concrete Feynman--Kac moment satisfies the genuine first-jump
renewal equation, with no supplied conditioning or integrability assumption. -/
theorem conditionalPathMoment_eq_integral_firstJumpHoldingMoment
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    conditionalPathMoment L hL hescape v g k T f x =
      ∫ q, firstJumpHoldingMoment L hL hescape x v g k T f q
        ∂holdingDestinationMeasure L x := by
  have hi := integrable_firstJumpPrefixMoment L hL hescape x v g k T f hT
  rw [jumpPrefixLaw_pointMass_one] at hi
  rw [conditionalPathMoment_eq_integral_firstJumpPrefixMoment,
    jumpPrefixLaw_pointMass_one,
    integral_map (measurable_appendHistory 0 (pointInitialPrefix x)).aemeasurable
      hi.aestronglyMeasurable]
  · simp only [firstJumpPrefixMoment_append_initial]
  · exact hT

end

end NCG.FiniteCTMCFirstJumpConditioning
