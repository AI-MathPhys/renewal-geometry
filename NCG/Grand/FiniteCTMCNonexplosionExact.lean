/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCHoldingPositivityExact
import NCG.Grand.ConditionalBorelCantelliNonexplosionExact
import Mathlib.Probability.Kernel.Condexp

/-!
# Nonexplosion of a finite continuous-time Markov chain

Escape rates on a finite state space have a finite uniform upper bound.  An
exponential holding time therefore has a uniformly positive conditional
chance to exceed one.  The conditional Borel--Cantelli criterion proves that
the cumulative jump times diverge almost surely, hence the genuine
Ionescu--Tulcea jump-sequence law is concentrated on the measurable carrier
of nonexplosive càdlàg paths.
-/

open MeasureTheory ProbabilityTheory Filter Finset Set Preorder
open ProbabilityTheory.Kernel
open scoped ENNReal BigOperators

noncomputable section

namespace NCG.FiniteCTMCNonexplosion

open NCG.DrivenProcess
open NCG.DrivenProcess.FinitePath
open NCG.FiniteCTMCJumpSequenceLaw
open NCG.FiniteCTMCPathCarrierMeasurability
open NCG.FiniteCTMCHoldingPositivity
open NCG.ConditionalBorelCantelliNonexplosion
open NCG.NonexplosiveFiniteStatePath

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Real-valued upper tail of an exponential law at one. -/
theorem expMeasure_real_Ioi_one {r : ℝ} (hr : 0 < r) :
    (ProbabilityTheory.expMeasure r).real (Set.Ioi 1) = Real.exp (-r) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  have hic : (ProbabilityTheory.expMeasure r).real (Set.Iic 1) =
      1 - Real.exp (-r) := by
    rw [← ProbabilityTheory.cdf_eq_real,
      ProbabilityTheory.cdf_expMeasure_eq hr]
    norm_num
  rw [← compl_Iic, measureReal_compl measurableSet_Iic,
    probReal_univ, hic]
  ring

/-- The real mass of a holding-time tail is the exponential tail, with the
destination coordinate integrated out. -/
theorem holdingDestinationMeasure_real_positiveTail
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (x : S) :
    (holdingDestinationMeasure L x).real
        (Set.Ioi 1 ×ˢ (Set.univ : Set S)) =
      Real.exp (-(escapeRate L x)) := by
  letI : IsProbabilityMeasure (destinationMeasure L x) :=
    destinationMeasure_isProbabilityMeasure L hL hescape x
  unfold holdingDestinationMeasure
  rw [measureReal_prod_prod, expMeasure_real_Ioi_one (hescape x)]
  simp

/-- The sum of all escape rates is a convenient finite upper bound for each
individual escape rate. -/
theorem escapeRate_le_sum_escapeRate
    (L : Matrix S S ℝ) (hescape : ∀ x, 0 < escapeRate L x) (x : S) :
    escapeRate L x ≤ ∑ y, escapeRate L y := by
  exact Finset.single_le_sum
    (fun y _ => (hescape y).le) (Finset.mem_univ x)

/-- Every one-step holding kernel has a common positive lower bound on the
probability that its holding time exceeds one. -/
theorem uniform_holdingTail_lower_bound
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (x : S) :
    Real.exp (-(∑ y, escapeRate L y)) ≤
      (holdingDestinationMeasure L x).real
        (Set.Ioi 1 ×ˢ (Set.univ : Set S)) := by
  rw [holdingDestinationMeasure_real_positiveTail L hL hescape x]
  exact Real.exp_le_exp.mpr
    (neg_le_neg (escapeRate_le_sum_escapeRate L hescape x))

/-- A physical holding-time exceedance is measurable in the canonical
trajectory filtration when its coordinate has been revealed. -/
theorem measurableSet_physicalHold_exceeds_one (n : ℕ) :
    MeasurableSet[(Filtration.piLE (X := fun _ : ℕ => ℝ × S)) (n + 1)]
      {z : ℕ → ℝ × S | 1 < physicalHold z n} := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hrestrict :
      Measurable[MeasurableSpace.comap (frestrictLe (n + 1)) inferInstance]
        (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + 1)) :=
    Measurable.of_comap_le le_rfl
  have heval : Measurable
      (fun q : Π _ : Finset.Iic (n + 1), ℝ × S =>
        q ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) :=
    measurable_pi_apply _
  exact measurableSet_lt measurable_const
    (measurable_fst.comp (heval.comp hrestrict))

/-- Under the CTMC law, the conditional expectation of the next holding-tail
indicator is bounded below by the common finite-state exponential tail. -/
theorem ae_condExp_holdingExceedance_lower_bound
    [Nonempty S]
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (n : ℕ) :
    let μ := jumpSequenceLaw p L hL hescape
    ∀ᵐ z ∂μ,
      Real.exp (-(∑ y, escapeRate L y)) ≤
        μ[((holdingExceedance (fun k z => physicalHold z k) 1 (n + 1)).indicator
          (1 : (ℕ → ℝ × S) → ℝ)) |
          Filtration.piLE (X := fun _ : ℕ => ℝ × S) n] z := by
  let μ := jumpSequenceLaw p L hL hescape
  letI : IsProbabilityMeasure μ :=
    jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
  let A : Set (ℝ × S) := Set.Ioi 1 ×ˢ (Set.univ : Set S)
  let past : (ℕ → ℝ × S) → (Π _ : Finset.Iic n, ℝ × S) := frestrictLe n
  let nextCoord : (ℕ → ℝ × S) → ℝ × S := fun z => z (n + 1)
  have hA : MeasurableSet A := measurableSet_Ioi.prod MeasurableSet.univ
  have hnext : Measurable nextCoord := by
    exact measurable_pi_apply (n + 1)
  have hpast : Measurable past := measurable_frestrictLe n
  have hevent :
      (holdingExceedance (fun k z => physicalHold z k) 1 (n + 1)).indicator
          (1 : (ℕ → ℝ × S) → ℝ) =
        fun z => A.indicator (1 : (ℝ × S) → ℝ) (nextCoord z) := by
    funext z
    by_cases hz : 1 < (z (n + 1)).1
    · simp [holdingExceedance, physicalHold, A, nextCoord, hz]
    · simp [holdingExceedance, physicalHold, A, nextCoord, hz]
  have hint : Integrable
      (fun z => A.indicator (1 : (ℝ × S) → ℝ) (nextCoord z)) μ := by
    exact (integrable_const 1).indicator
      (hA.preimage hnext)
  have hce :
      μ[(holdingExceedance (fun k z => physicalHold z k) 1 (n + 1)).indicator
          (1 : (ℕ → ℝ × S) → ℝ) |
          Filtration.piLE (X := fun _ : ℕ => ℝ × S) n] =ᵐ[μ]
        fun z => ∫ y, A.indicator (1 : (ℝ × S) → ℝ) y
          ∂condDistrib nextCoord past μ (past z) := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    rw [hevent]
    exact condExp_ae_eq_integral_condDistrib hpast hnext.aemeasurable
      (stronglyMeasurable_one.indicator hA) hint
  have hkernelPrefix :
      condDistrib nextCoord past μ =ᵐ[μ.map past]
        historyJumpKernel L n := by
    simpa [μ, past, nextCoord] using
      condDistrib_jumpSequenceLaw p hp hp1 L hL hescape n
  have hkernel :
      (fun z => condDistrib nextCoord past μ (past z)) =ᵐ[μ]
        fun z => historyJumpKernel L n (past z) := by
    simpa [Function.comp_def] using
      ae_eq_comp hpast.aemeasurable hkernelPrefix
  filter_upwards [hce, hkernel] with z hz hzkernel
  rw [hz, hzkernel, integral_indicator_one hA]
  change Real.exp (-(∑ y, escapeRate L y)) ≤
    (holdingDestinationMeasure L (currentState n (past z))).real A
  simpa [A] using uniform_holdingTail_lower_bound
    L hL hescape (currentState n (past z))

/-- The cumulative physical holding time tends to infinity almost surely. -/
theorem ae_cumulativePhysicalHold_tendsto_atTop
    [Nonempty S]
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) :
    ∀ᵐ z ∂jumpSequenceLaw p L hL hescape,
      Tendsto (fun n => ∑ k ∈ Finset.range n, physicalHold z k)
        atTop atTop := by
  let μ := jumpSequenceLaw p L hL hescape
  letI : IsProbabilityMeasure μ :=
    jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
  have hnonneg : ∀ n, ∀ᵐ z ∂μ, 0 ≤ physicalHold z n := by
    intro n
    have hpos : ∀ᵐ z ∂μ, 0 < physicalHold z n := by
      apply (ae_iff_measure_eq
        (measurableSet_lt measurable_const
          (measurable_fst.comp
            (measurable_pi_apply (n + 1)))).nullMeasurableSet).2
      simpa [μ, physicalHold] using
        jumpSequenceLaw_physicalHold_positive_eq_one
          p hp hp1 L hL hescape n
    exact hpos.mono fun _ hz => hz.le
  exact ae_cumulativeHolding_tendsto_atTop
    μ (Filtration.piLE (X := fun _ : ℕ => ℝ × S))
      (fun k z => physicalHold z k) 1
      (Real.exp (-(∑ y, escapeRate L y)))
      zero_lt_one (Real.exp_pos _)
      measurableSet_physicalHold_exceeds_one hnonneg
      (ae_condExp_holdingExceedance_lower_bound
        p hp hp1 L hL hescape)

/-- The genuine finite-state CTMC jump sequence is nonexplosive almost
surely. -/
theorem jumpSequenceLaw_nonexplosiveHoldingSet_eq_one
    [Nonempty S]
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) :
    jumpSequenceLaw p L hL hescape
      (nonexplosiveHoldingSet (S := S)) = 1 := by
  let μ := jumpSequenceLaw p L hL hescape
  letI : IsProbabilityMeasure μ :=
    jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
  calc
    μ (nonexplosiveHoldingSet (S := S)) = μ Set.univ := by
      apply (ae_iff_measure_eq
        measurableSet_nonexplosiveHoldingSet.nullMeasurableSet).mp
      filter_upwards [ae_cumulativePhysicalHold_tendsto_atTop
        p hp hp1 L hL hescape] with z hz
      intro m
      have hev : ∀ᶠ n in atTop,
          (m : ℝ) < ∑ k ∈ Finset.range n, physicalHold z k :=
        hz.eventually (eventually_gt_atTop (m : ℝ))
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      refine ⟨N, ?_⟩
      simpa [cumulativeJumpTime, cumulativeHold] using
        hN (N + 1) (Nat.le_succ N)
    _ = 1 := measure_univ

/-- Consequently the jump-sequence law is concentrated on the exact
measurable carrier from which the canonical càdlàg path is constructed. -/
theorem jumpSequenceLaw_admissibleJumpSequenceSet_eq_one
    [Nonempty S]
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) :
    jumpSequenceLaw p L hL hescape
      (admissibleJumpSequenceSet (S := S)) = 1 := by
  let μ := jumpSequenceLaw p L hL hescape
  letI : IsProbabilityMeasure μ :=
    jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
  calc
    μ (admissibleJumpSequenceSet (S := S)) = μ Set.univ := by
      apply (ae_iff_measure_eq
        measurableSet_admissibleJumpSequenceSet.nullMeasurableSet).mp
      have hpos : ∀ᵐ z ∂μ, z ∈ positiveHoldingSet (S := S) := by
        apply (ae_mem_iff_measure_eq
          measurableSet_positiveHoldingSet.nullMeasurableSet).2
        simpa [μ] using jumpSequenceLaw_positiveHoldingSet_eq_one
          p hp hp1 L hL hescape
      have hnexp : ∀ᵐ z ∂μ, z ∈ nonexplosiveHoldingSet (S := S) := by
        apply (ae_mem_iff_measure_eq
          measurableSet_nonexplosiveHoldingSet.nullMeasurableSet).2
        simpa [μ] using jumpSequenceLaw_nonexplosiveHoldingSet_eq_one
          p hp hp1 L hL hescape
      filter_upwards [hpos, hnexp] with z hzpos hznexp
      exact ⟨hzpos, hznexp⟩
    _ = 1 := measure_univ

end NCG.FiniteCTMCNonexplosion
