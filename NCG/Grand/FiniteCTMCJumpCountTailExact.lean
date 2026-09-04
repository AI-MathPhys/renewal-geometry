/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCPrefixLaplaceBoundExact
import NCG.Grand.FiniteCTMCHomogeneousRestartLawExact

/-!
# Exponential jump-count tails for the genuine admissible CTMC law

The finite-prefix Laplace estimate is transported to the full admissible
path law. Markov's inequality then bounds the probability of making at least
`n` jumps before a fixed horizon. The Laplace parameter is free, allowing an
arbitrarily small geometric ratio.
-/

open MeasureTheory ProbabilityTheory Preorder Set
open ProbabilityTheory.Kernel

namespace NCG.FiniteCTMCJumpCountTail

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCJumpSequenceLaw
open FiniteCTMCHoldingLaplace FiniteCTMCPrefixLaplaceBound
open FiniteCTMCHomogeneousRestartLaw FiniteCTMCPathLawDisintegration
open FiniteCTMCPathCarrierMeasurability FiniteCTMCPathEvaluationMeasurability
open FiniteCTMCAdmissiblePathLaw FiniteCTMCFeynmanKacPathMoment
open NonexplosiveFiniteStatePath

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- On an admissible path the bounded prefix discount is exactly the
negative exponential of its genuine cumulative jump time. -/
theorem prefixDiscount_eq_exp_cumulativeJumpTime
    (s : ℝ) (n : ℕ) (z : AdmissibleJumpSequence (S := S)) :
    prefixDiscount s n (frestrictLe n z.1) =
      Real.exp (-(s * cumulativeJumpTime z.1 n)) := by
  induction n with
  | zero => simp [prefixDiscount, cumulativeJumpTime, cumulativeHold]
  | succ n ih =>
    have hp : previousPrefix n (frestrictLe (n+1) z.1) = frestrictLe n z.1 := rfl
    change prefixDiscount s n (previousPrefix n (frestrictLe (n+1) z.1)) *
      holdingDiscount s (physicalHold z.1 n) = _
    rw [hp, ih, holdingDiscount, max_eq_left (z.2.1 n).le, ← Real.exp_add]
    unfold cumulativeJumpTime
    rw [cumulativeHold_succ]
    congr 1
    ring

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
  (hescape : ∀ x, 0 < escapeRate L x)

/-- The prefix Laplace bound under the actual point-start infinite law. -/
theorem integral_raw_prefixDiscount_le_pow
    (x : S) (s R : ℝ) (hs : 0 ≤ s) (hRpos : 0 < R)
    (hR : ∀ y, escapeRate L y ≤ R) (n : ℕ) :
    (∫ z, prefixDiscount s n (frestrictLe n z)
      ∂jumpSequenceLaw (pointMass x) L hL hescape) ≤ (R / (R+s)) ^ n := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  rw [← integral_map (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) n).aemeasurable
    (measurable_prefixDiscount s n).aestronglyMeasurable]
  rw [jumpSequenceLaw_pointMass_eq_continuation L hL hescape x]
  change (∫ z, prefixDiscount s n z ∂((Kernel.traj (X := fun _ : ℕ => ℝ × S) (historyJumpKernel L) 0
    (pointInitialPrefix x)).map (frestrictLe n))) ≤ _
  rw [Kernel.traj_map_frestrictLe_apply]
  exact integral_prefixDiscount_le_pow L hL hescape s R hs hRpos hR n (pointInitialPrefix x)

/-- Laplace bound for the actual cumulative jump time on the physical carrier. -/
theorem integral_exp_cumulativeJumpTime_le_pow
    (x : S) (s R : ℝ) (hs : 0 ≤ s) (hRpos : 0 < R)
    (hR : ∀ y, escapeRate L y ≤ R) (n : ℕ) :
    (∫ z, Real.exp (-(s * cumulativeJumpTime z.1 n))
      ∂admissiblePathLaw x (pointMass x) L hL hescape) ≤ (R / (R+s)) ^ n := by
  letI : Nonempty S := ⟨x⟩
  simp_rw [← prefixDiscount_eq_exp_cumulativeJumpTime]
  have hm : Measurable (fun z : ℕ → ℝ × S => prefixDiscount s n (frestrictLe n z)) :=
    (measurable_prefixDiscount s n).comp
      (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) n)
  have hcoe : Measurable (fun z : AdmissibleJumpSequence (S := S) => z.1) :=
    measurable_subtype_coe
  have hmap := integral_map (μ := admissiblePathLaw x (pointMass x) L hL hescape)
    hcoe.aemeasurable hm.aestronglyMeasurable
  rw [map_subtypeVal_admissiblePathLaw x (pointMass x) (pointMass_nonnegative x)
    (sum_pointMass x) L hL hescape] at hmap
  rw [← hmap]
  exact integral_raw_prefixDiscount_le_pow L hL hescape x s R hs hRpos hR n

/-- Integrability of the nonnegative cumulative-time discount on the true law. -/
theorem integrable_exp_cumulativeJumpTime
    (x : S) (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    Integrable (fun z => Real.exp (-(s * cumulativeJumpTime z.1 n)))
      (admissiblePathLaw x (pointMass x) L hL hescape) := by
  letI : IsProbabilityMeasure (admissiblePathLaw x (pointMass x) L hL hescape) :=
    admissiblePathLaw_isProbabilityMeasure x (pointMass x) (pointMass_nonnegative x)
      (sum_pointMass x) L hL hescape
  have hm : Measurable (fun z : AdmissibleJumpSequence (S := S) =>
      prefixDiscount s n (frestrictLe n z.1)) :=
    ((measurable_prefixDiscount s n).comp
      (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) n)).comp measurable_subtype_coe
  simp_rw [← prefixDiscount_eq_exp_cumulativeJumpTime]
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (prefixDiscount_nonneg s n _)]
    exact prefixDiscount_le_one s hs n _

/-- A geometric tail for the number of jumps under the exact point-start
admissible law. The rate parameter `s` can be chosen arbitrarily large. -/
theorem jumpCount_tail_le
    (x : S) (s R T : ℝ) (hs : 0 ≤ s) (hRpos : 0 < R)
    (hR : ∀ y, escapeRate L y ≤ R) (hT : 0 ≤ T) (n : ℕ) :
    (admissiblePathLaw x (pointMass x) L hL hescape).real
        {z | n ≤ admissibleJumpIndex z T} ≤
      Real.exp (s*T) * (R / (R+s)) ^ n := by
  let μ := admissiblePathLaw x (pointMass x) L hL hescape
  letI : IsProbabilityMeasure μ :=
    admissiblePathLaw_isProbabilityMeasure x (pointMass x) (pointMass_nonnegative x)
      (sum_pointMass x) L hL hescape
  have hsub : {z : AdmissibleJumpSequence (S := S) | n ≤ admissibleJumpIndex z T} ⊆
      {z | Real.exp (-(s*T)) ≤ Real.exp (-(s * cumulativeJumpTime z.1 n))} := by
    intro z hz
    have ht := ((admissibleJumpIndex_eq_iff z hT (admissibleJumpIndex z T)).mp rfl).1
    have hmono := (clockOfAdmissible z).cumulativeHold_strictMono.monotone hz
    change cumulativeJumpTime z.1 n ≤ cumulativeJumpTime z.1 (admissibleJumpIndex z T) at hmono
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (hmono.trans ht) hs))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun z => (Real.exp_pos (-(s * cumulativeJumpTime z.1 n))).le)
    (integrable_exp_cumulativeJumpTime L hL hescape x s hs n) (Real.exp (-(s*T)))
  have hbound := integral_exp_cumulativeJumpTime_le_pow L hL hescape x s R hs hRpos hR n
  have hmul : Real.exp (-(s*T)) * μ.real {z | n ≤ admissibleJumpIndex z T} ≤
      (R / (R+s)) ^ n :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos _).le).trans
      (hmarkov.trans hbound)
  have hcancel : Real.exp (s*T) * Real.exp (-(s*T)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = Real.exp (s*T) * (Real.exp (-(s*T)) * μ.real {z | n ≤ admissibleJumpIndex z T}) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmul (Real.exp_pos _).le

end

end NCG.FiniteCTMCJumpCountTail
