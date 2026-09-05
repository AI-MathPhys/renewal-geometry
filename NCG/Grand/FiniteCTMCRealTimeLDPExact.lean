/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCNormalizedRewardLawExact
import NCG.Grand.RealTimeGartnerEllisExact

/-!
# Full real-time large deviations for irreducible finite CTMC rewards

On a nontrivial finite state space, the actual laws of `Y_T/T` satisfy both
LDP bounds over all real horizons with their convex good extended spectral
rate. Every probabilistic and analytic input is discharged by the proved
path-law and Perron machinery. Singleton and general absorbing-generator
Feynman--Kac cases are deliberately not included in this theorem.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace NCG.FiniteCTMCRealTimeLDP

open DrivenProcess FiniteCTMCNormalizedRewardLaw FiniteCTMCSCGFConvexity
open IrreducibleGeneratorEscape MetzlerExponentialPositivity MetzlerSpectralAbscissa
open RealTimeLargeDeviations

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] [Nontrivial S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Full LDP of the actual normalized reward laws, with no unproved
probability, integrability, convexity, tightness, or endpoint inputs. -/
theorem hasLargeDeviationPrinciple
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) :
    HasLargeDeviationPrinciple
      (fun T => normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g T)
      (spectralRate L v g) := by
  apply hasLargeDeviationPrinciple_of_differentiable_logMoment
    _ (fun q => spectralAbscissa (tilt L v g q))
  · exact fun T hT => normalizedRewardLaw_isProbabilityMeasure L hL
      (escapeRate_pos L hL hirr) x₀ p hp hsum v g T hT
  · exact fun q => (IrreducibleFiniteCTMCSCGF.analyticAt_spectralAbscissa
      L hL hirr v g q).differentiableAt
  · exact fun T hT q => integrable_exp_normalizedRewardLaw L hL
      (escapeRate_pos L hL hirr) x₀ p v g q T hT
  · exact fun T hT q => integral_exp_normalizedRewardLaw_pos L hL
      (escapeRate_pos L hL hirr) x₀ p hp hsum v g q T hT
  · exact fun q => tendsto_scaled_log_integral_exp L hL hirr x₀ p hp hsum v g q

/-- Complete package: the genuine real-time LDP, nonnegative rate attaining
zero, compact finite sublevels, and convex extended-rate epigraph. -/
theorem largeDeviationPrinciple_with_convex_good_rate
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) :
    HasLargeDeviationPrinciple
      (fun T => normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g T)
      (spectralRate L v g) ∧
    (∀ a : ℝ, 0 ≤ spectralRate L v g a) ∧
    (∃ a : ℝ, spectralRate L v g a = 0) ∧
    (∀ r : ℝ, IsCompact {a : ℝ | spectralRate L v g a ≤ (r : EReal)}) ∧
    Convex ℝ {z : ℝ × ℝ | spectralRate L v g z.1 ≤ (z.2 : EReal)} := by
  exact ⟨hasLargeDeviationPrinciple L hL hirr x₀ p hp hsum v g,
    spectralRate_nonneg L hL hirr v g, exists_spectralRate_zero L hL hirr v g,
    isCompact_spectralRate_sublevel L v g, convex_spectralRate_epigraph L v g⟩

end

end NCG.FiniteCTMCRealTimeLDP
