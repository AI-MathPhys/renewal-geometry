/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RealTimeExtendedRateUpperBoundExact
import NCG.Grand.RealTimeExtendedRateLowerBoundExact

/-!
# A real-time Gartner--Ellis theorem with a full extended rate

The LDP is expressed by exponential inequalities at every strict finite
threshold above or below the set-rate infimum. This formulation includes
infinite rates and zero probabilities without using the real logarithm
at zero. Time ranges over all real horizons, not just natural numbers.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace NCG.RealTimeLargeDeviations

noncomputable section

/-- Extended infimum of the rate over a set, equal to infinity on the empty set. -/
def setRate (I : ℝ → EReal) (s : Set ℝ) : EReal := ⨅ x ∈ s, I x

theorem setRate_le (I : ℝ → EReal) (s : Set ℝ) (x : ℝ) (hx : x ∈ s) :
    setRate I s ≤ I x := iInf_le_of_le x (iInf_le _ hx)

theorem exists_rate_lt_of_setRate_lt (I : ℝ → EReal) (s : Set ℝ) (A : ℝ)
    (h : setRate I s < (A : EReal)) : ∃ x ∈ s, I x < (A : EReal) := by
  by_contra hn
  push_neg at hn
  exact (not_le_of_gt h) (le_iInf fun x => le_iInf fun hx => hn x hx)

/-- Full real-time LDP in its strict-threshold exponential formulation.
For closed sets every threshold below the rate infimum gives an eventual
upper estimate; for open sets every threshold above it gives a lower one. -/
def HasLargeDeviationPrinciple (mu : ℝ → Measure ℝ) (I : ℝ → EReal) : Prop :=
  (∀ t, 0 ≤ t → IsProbabilityMeasure (mu t)) ∧
  (∀ F : Set ℝ, IsClosed F → ∀ A : ℝ, (A : EReal) < setRate I F →
    ∀ᶠ t : ℝ in atTop, (mu t).real F ≤ Real.exp (-t * A)) ∧
  (∀ G : Set ℝ, IsOpen G → ∀ A : ℝ, setRate I G < (A : EReal) →
    ∀ᶠ t : ℝ in atTop, Real.exp (-t * A) ≤ (mu t).real G)

/-- All-real-time Gartner--Ellis: finite differentiable pressure, actual
moment limits and integrability imply both full LDP bounds. Tightness and
finite-rate endpoint approximation are proved internally. -/
theorem hasLargeDeviationPrinciple_of_differentiable_logMoment
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (mu t))
    (hd : Differentiable ℝ psi)
    (hint : ∀ t, 0 ≤ t → ∀ u, Integrable (fun x : ℝ => Real.exp (t * u * x)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ u, 0 < RealTimeExponentialUpperBound.moment (mu t) t u)
    (hlim : ∀ u, Tendsto (fun t => RealTimeExponentialUpperBound.logMoment mu t u)
      atTop (𝓝 (psi u))) :
    HasLargeDeviationPrinciple mu (ExtendedLegendreRate.rate psi) := by
  have hfinite : ∀ t, 0 ≤ t → IsFiniteMeasure (mu t) := by
    intro t ht
    letI := hprob t ht
    infer_instance
  have hone : ∀ t, 0 ≤ t → Integrable (fun _ : ℝ => (1 : ℝ)) (mu t) := by
    intro t ht
    letI := hprob t ht
    exact integrable_const 1
  refine ⟨hprob, ?_, ?_⟩
  · intro F hF A hA
    obtain ⟨B, hAB, hB⟩ := EReal.exists_between_coe_real hA
    have hAB' : A < B := EReal.coe_lt_coe_iff.mp hAB
    have heps : 0 < (B - A) / 3 := by positivity
    have hgap : ∀ x ∈ F, ((A + 3 * ((B - A) / 3) : ℝ) : EReal) <
        ExtendedLegendreRate.rate psi x := by
      intro x hx
      have heq : A + 3 * ((B - A) / 3) = B := by ring
      rw [heq]
      exact hB.trans_le (setRate_le _ F x hx)
    have hbound := RealTimeExtendedRateUpperBound.eventually_mass_closed_le mu hfinite psi F
      A ((B - A) / 3) hF heps hgap hint hone hpos hlim
    filter_upwards [hbound] with t ht
    simpa only [FiniteExponentialCoverUpperBound.originalMass_eq_measureReal
      (mu t) F hF.measurableSet] using ht
  · intro G hG A hA
    obtain ⟨a, ha, hrate⟩ := exists_rate_lt_of_setRate_lt _ G A hA
    have hbound := RealTimeExtendedRateLowerBound.eventually_mass_open_ge_of_rate_lt
      mu psi G a A hd hG ha hrate hint hone hpos hlim
    filter_upwards [hbound] with t ht
    simpa only [FiniteExponentialCoverUpperBound.originalMass_eq_measureReal
      (mu t) G hG.measurableSet] using ht

end

end NCG.RealTimeLargeDeviations
