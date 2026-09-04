/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCNormalizedRewardLawExact
import NCG.Grand.RealTimeExtendedRateUpperBoundExact

/-!
# Upper deviation bounds for actual CTMC rewards at every real horizon

The all-real-time upper-bound machinery is instantiated with the genuine
law of `Y_T / T`. All probability and moment assumptions are discharged.
This closes the real-horizon upper-bound gap, not the remaining full LDP
lower-bound or degenerate-generator gaps.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace NCG.FiniteCTMCRealTimeUpperBound

open DrivenProcess FiniteCTMCNormalizedRewardLaw FiniteCTMCSCGFConvexity
open IrreducibleGeneratorEscape MetzlerExponentialPositivity MetzlerSpectralAbscissa
open FiniteExponentialCoverUpperBound

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] [Nontrivial S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The actual empirical reward family is exponentially tight over all
sufficiently large real horizons, not only at integer times. -/
theorem exists_compact_exponential_tightness
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ M : ℝ, 0 < M ∧ IsCompact (Icc (-M) M) ∧
      ∀ᶠ T : ℝ in atTop,
        (normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g T).real
          (Icc (-M) M)ᶜ ≤ Real.exp (-T * A) := by
  let mu : ℝ → Measure ℝ := fun T =>
    normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g T
  have hone : ∀ T, 0 ≤ T → Integrable (fun _ : ℝ => (1 : ℝ)) (mu T) := by
    intro T hT
    letI := normalizedRewardLaw_isProbabilityMeasure L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g T hT
    exact integrable_const 1
  obtain ⟨M, hM, hK, hbound⟩ :=
    RealTimeExtendedRateUpperBound.exists_compact_exponential_tightness
      mu (fun q => spectralAbscissa (tilt L v g q)) A hA
      (fun T hT q => integrable_exp_normalizedRewardLaw L hL (escapeRate_pos L hL hirr)
        x₀ p v g q T hT) hone
      (fun T hT q => integral_exp_normalizedRewardLaw_pos L hL (escapeRate_pos L hL hirr)
        x₀ p hp hsum v g q T hT)
      (fun q => tendsto_scaled_log_integral_exp L hL hirr x₀ p hp hsum v g q)
  refine ⟨M, hM, hK, ?_⟩
  filter_upwards [hbound] with T hT
  simpa only [originalMass_eq_measureReal (mu T) _ measurableSet_Icc.compl] using hT

/-- The extended-rate closed-set upper bound for the actual reward law,
valid for every sufficiently large real horizon. -/
theorem eventually_empirical_closed_le
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (F : Set ℝ) (A epsilon : ℝ)
    (hF : IsClosed F) (hepsilon : 0 < epsilon)
    (hgap : ∀ a ∈ F, ((A + 3 * epsilon : ℝ) : EReal) < spectralRate L v g a) :
    ∀ᶠ T : ℝ in atTop,
      (normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g T).real F ≤
        Real.exp (-T * A) := by
  let mu : ℝ → Measure ℝ := fun T =>
    normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g T
  have hprob : ∀ T, 0 ≤ T → IsProbabilityMeasure (mu T) := fun T hT =>
    normalizedRewardLaw_isProbabilityMeasure L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g T hT
  have hfinite : ∀ T, 0 ≤ T → IsFiniteMeasure (mu T) := by
    intro T hT
    letI := hprob T hT
    infer_instance
  have hone : ∀ T, 0 ≤ T → Integrable (fun _ : ℝ => (1 : ℝ)) (mu T) := by
    intro T hT
    letI := hprob T hT
    exact integrable_const 1
  have hbound := RealTimeExtendedRateUpperBound.eventually_mass_closed_le
    mu hfinite (fun q => spectralAbscissa (tilt L v g q)) F A epsilon hF hepsilon hgap
    (fun T hT q => integrable_exp_normalizedRewardLaw L hL (escapeRate_pos L hL hirr)
      x₀ p v g q T hT) hone
    (fun T hT q => integral_exp_normalizedRewardLaw_pos L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g q T hT)
    (fun q => tendsto_scaled_log_integral_exp L hL hirr x₀ p hp hsum v g q)
  filter_upwards [hbound] with T hT
  simpa only [originalMass_eq_measureReal (mu T) F hF.measurableSet] using hT

end

end NCG.FiniteCTMCRealTimeUpperBound
