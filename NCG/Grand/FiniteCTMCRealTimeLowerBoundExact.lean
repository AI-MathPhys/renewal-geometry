/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCNormalizedRewardLawExact
import NCG.Grand.RealTimeTiltedLowerBoundExact

/-!
# Real-horizon lower bounds for the actual finite-CTMC reward law

Analyticity of the spectral pressure and the proved stochastic moment
limits discharge every concentration hypothesis. The lower bound holds
at every derivative slope over arbitrary real horizons. It does not yet
assert the endpoint approximation needed for a full open-set LDP bound.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace NCG.FiniteCTMCRealTimeLowerBound

open DrivenProcess FiniteCTMCNormalizedRewardLaw FiniteCTMCSCGFConvexity
open IrreducibleGeneratorEscape MetzlerExponentialPositivity MetzlerSpectralAbscissa
open FiniteExponentialCoverUpperBound

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] [Nontrivial S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- At every derivative slope the full extended rate equals the finite
spectral tangent cost; no boundedness of an unproved supremum is assumed. -/
theorem spectralRate_at_derivative
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    spectralRate L v g (deriv (fun q => spectralAbscissa (tilt L v g q)) k) =
      ((k * deriv (fun q => spectralAbscissa (tilt L v g q)) k -
        spectralAbscissa (tilt L v g k) : ℝ) : EReal) := by
  exact ExtendedLegendreRate.rate_at_derivative
    (convexOn_spectralAbscissa L hL hirr v g)
    (IrreducibleFiniteCTMCSCGF.analyticAt_spectralAbscissa
      L hL hirr v g k).differentiableAt.hasDerivAt

/-- Open-set lower estimate at each derivative slope for the genuine
normalized reward law, at all sufficiently large real horizons. -/
theorem eventually_empirical_open_ge_at_derivative
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (G : Set ℝ) (k epsilon : ℝ)
    (hG : IsOpen G)
    (ha : deriv (fun q => spectralAbscissa (tilt L v g q)) k ∈ G)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp (-T *
        (k * deriv (fun q => spectralAbscissa (tilt L v g q)) k -
          spectralAbscissa (tilt L v g k) + epsilon)) ≤
        (normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g T).real G := by
  let mu : ℝ → Measure ℝ := fun T =>
    normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g T
  have hone : ∀ T, 0 ≤ T → Integrable (fun _ : ℝ => (1 : ℝ)) (mu T) := by
    intro T hT
    letI := normalizedRewardLaw_isProbabilityMeasure L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g T hT
    exact integrable_const 1
  have hd := (IrreducibleFiniteCTMCSCGF.analyticAt_spectralAbscissa
    L hL hirr v g k).differentiableAt.hasDerivAt
  have hbound := RealTimeTiltedLowerBound.eventually_mass_open_lower_bound_at_derivative
    mu (fun q => spectralAbscissa (tilt L v g q)) G k _ epsilon hG ha hd hepsilon
    (fun T hT q => integrable_exp_normalizedRewardLaw L hL (escapeRate_pos L hL hirr)
      x₀ p v g q T hT) hone
    (fun T hT q => integral_exp_normalizedRewardLaw_pos L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g q T hT)
    (fun q => tendsto_scaled_log_integral_exp L hL hirr x₀ p hp hsum v g q)
  filter_upwards [hbound] with T hT
  simpa only [originalMass_eq_measureReal (mu T) G hG.measurableSet] using hT

end

end NCG.FiniteCTMCRealTimeLowerBound
