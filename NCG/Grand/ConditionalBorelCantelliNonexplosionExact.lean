/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Probability.Martingale.BorelCantelli

/-!
# A conditional Borel--Cantelli criterion for nonexplosion

For an adapted sequence of nonnegative holding times, suppose the conditional
probability that the next holding time exceeds a fixed positive threshold is
uniformly bounded below by a positive constant.  Lévy's conditional
Borel--Cantelli theorem then forces the number of such long holds, and hence
the cumulative holding time, to diverge almost surely.
-/

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped BigOperators

noncomputable section

namespace NCG.ConditionalBorelCantelliNonexplosion

set_option linter.unusedSectionVars false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Event sequence indexed as required by Lévy's theorem: index zero is
vacuous, while index `n+1` records that holding time `n` exceeds `δ`. -/
def holdingExceedance (hold : ℕ → Ω → ℝ) (δ : ℝ) : ℕ → Set Ω
  | 0 => Set.univ
  | n + 1 => {ω | δ < hold n ω}

@[simp] theorem holdingExceedance_zero (hold : ℕ → Ω → ℝ) (δ : ℝ) :
    holdingExceedance hold δ 0 = Set.univ := rfl

@[simp] theorem holdingExceedance_succ (hold : ℕ → Ω → ℝ)
    (δ : ℝ) (n : ℕ) :
    holdingExceedance hold δ (n + 1) = {ω | δ < hold n ω} := rfl

/-- Uniformly positive conditional probabilities force the predictable
exceedance count to diverge. -/
theorem ae_predictableExceedanceCount_tendsto_atTop
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (hold : ℕ → Ω → ℝ) (δ c : ℝ)
    (hc : 0 < c)
    (hcond : ∀ n, ∀ᵐ ω ∂μ,
      c ≤ μ[((holdingExceedance hold δ (n + 1)).indicator
        (1 : Ω → ℝ)) | ℱ n] ω) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ k ∈ Finset.range n,
      (μ[((holdingExceedance hold δ (k + 1)).indicator
        (1 : Ω → ℝ)) | ℱ k]) ω) atTop atTop := by
  filter_upwards [ae_all_iff.2 hcond] with ω hω
  have hlinear : Tendsto (fun n : ℕ => (n : ℝ) * c) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hc
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [] with n
  calc
    (n : ℝ) * c = ∑ k ∈ Finset.range n, c := by simp
    _ ≤ ∑ k ∈ Finset.range n,
        (μ[((holdingExceedance hold δ (k + 1)).indicator
          (1 : Ω → ℝ)) | ℱ k]) ω := by
      exact Finset.sum_le_sum fun k _ => hω k

/-- Conditional Borel--Cantelli nonexplosion criterion in its strongest
useful form: cumulative holding times tend to `+∞` almost surely. -/
theorem ae_cumulativeHolding_tendsto_atTop
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (hold : ℕ → Ω → ℝ) (δ c : ℝ)
    (hδ : 0 < δ) (hc : 0 < c)
    (hmeas : ∀ n,
      MeasurableSet[ℱ (n + 1)] {ω | δ < hold n ω})
    (hnonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ hold n ω)
    (hcond : ∀ n, ∀ᵐ ω ∂μ,
      c ≤ μ[((holdingExceedance hold δ (n + 1)).indicator
        (1 : Ω → ℝ)) | ℱ n] ω) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => ∑ k ∈ Finset.range n, hold k ω) atTop atTop := by
  have hsmeas : ∀ n, MeasurableSet[ℱ n]
      (holdingExceedance hold δ n) := by
    intro n
    cases n with
    | zero => exact MeasurableSet.univ
    | succ n => exact hmeas n
  have hpredict := ae_predictableExceedanceCount_tendsto_atTop
    μ ℱ hold δ c hc hcond
  have hcount : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ k ∈ Finset.range n,
      (holdingExceedance hold δ (k + 1)).indicator
        (1 : Ω → ℝ) ω) atTop atTop := by
    filter_upwards [
      MeasureTheory.tendsto_sum_indicator_atTop_iff'
        (μ := μ) (ℱ := ℱ) hsmeas,
      hpredict] with ω hiff ht
    exact hiff.mpr ht
  filter_upwards [hcount, ae_all_iff.2 hnonneg] with ω hω hnonnegω
  have hscaled : Tendsto (fun n => δ *
      (∑ k ∈ Finset.range n,
        (holdingExceedance hold δ (k + 1)).indicator
          (1 : Ω → ℝ) ω)) atTop atTop :=
    hω.const_mul_atTop hδ
  refine tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards [] with n
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => by
    by_cases hk : δ < hold k ω
    · simp [holdingExceedance, hk, hk.le]
    · simp [holdingExceedance, hk, hnonnegω k]

end NCG.ConditionalBorelCantelliNonexplosion
