/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCNormalizedRewardLawExact
import NCG.Grand.ExtendedRateLargeDeviationUpperBoundExact

/-!
# Deviation bounds for the actual finite-CTMC empirical reward

The natural-time closed-set upper bound and open-set lower bound at
derivative slopes now apply to the actual law of `Y_n / n`. All moment,
convexity, differentiability, and tightness inputs are proved internally.
This is not yet the full all-real-time, all-open-set manuscript LDP.
-/

open MeasureTheory Filter Set Topology
open scoped BigOperators

namespace NCG.FiniteCTMCRewardDeviationBounds

open DrivenProcess FiniteCTMCNormalizedRewardLaw FiniteCTMCSCGFConvexity
open IrreducibleGeneratorEscape MetzlerExponentialPositivity MetzlerSpectralAbscissa
open ExponentialTiltLocalLowerBound ExponentialTiltMeasure
open FiniteExponentialCoverUpperBound

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] [Nontrivial S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Exponential tightness of the actual empirical reward laws at natural times. -/
theorem exists_compact_exponential_tightness
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ M : ℝ, 0 < M ∧ IsCompact (Icc (-M) M) ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g n).real
          (Icc (-M) M)ᶜ ≤ Real.exp (-(n : ℝ) * A) := by
  let mu : ℕ → Measure ℝ := fun n =>
    normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g n
  letI : ∀ n, IsProbabilityMeasure (mu n) := fun n =>
    normalizedRewardLaw_isProbabilityMeasure L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g n (Nat.cast_nonneg n)
  obtain ⟨M, hM, hK, hbound⟩ :=
    SCGFExponentialTightness.exists_compactInterval_exponential_tightness
      mu (fun q => spectralAbscissa (tilt L v g q)) A hA
      (fun n q => integrable_exp_normalizedRewardLaw L hL (escapeRate_pos L hL hirr)
        x₀ p v g q n (Nat.cast_nonneg n))
      (fun _ => integrable_const 1)
      (fun n q => integral_exp_normalizedRewardLaw_pos L hL (escapeRate_pos L hL hirr)
        x₀ p hp hsum v g q n (Nat.cast_nonneg n))
      (fun q => tendsto_normalizedLogMoment L hL hirr x₀ p hp hsum v g q)
  refine ⟨M, hM, hK, ?_⟩
  filter_upwards [hbound] with n hn
  simpa only [originalMass_eq_measureReal (mu n) _ measurableSet_Icc.compl] using hn

/-- The closed-set exponential upper bound for the actual empirical law,
using the full extended spectral rate and no supplied analytic inputs. -/
theorem eventually_empirical_closed_le
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (F : Set ℝ) (A epsilon : ℝ)
    (hF : IsClosed F) (hepsilon : 0 < epsilon)
    (hgap : ∀ a ∈ F, ((A + 3 * epsilon : ℝ) : EReal) < spectralRate L v g a) :
    ∀ᶠ n : ℕ in atTop,
      (normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g n).real F ≤
        Real.exp (-(n : ℝ) * A) := by
  let mu : ℕ → Measure ℝ := fun n =>
    normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g n
  letI : ∀ n, IsProbabilityMeasure (mu n) := fun n =>
    normalizedRewardLaw_isProbabilityMeasure L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g n (Nat.cast_nonneg n)
  have hbound := ExtendedRateLargeDeviationUpperBound.eventually_mass_closed_le
    mu (fun q => spectralAbscissa (tilt L v g q)) F A epsilon hF hepsilon hgap
    (fun n q => integrable_exp_normalizedRewardLaw L hL (escapeRate_pos L hL hirr)
      x₀ p v g q n (Nat.cast_nonneg n))
    (fun _ => integrable_const 1)
    (fun n q => integral_exp_normalizedRewardLaw_pos L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g q n (Nat.cast_nonneg n))
    (fun q => tendsto_normalizedLogMoment L hL hirr x₀ p hp hsum v g q)
  filter_upwards [hbound] with n hn
  simpa only [originalMass_eq_measureReal (mu n) F hF.measurableSet] using hn

/-- The open-set lower bound at every SCGF derivative slope for the actual
empirical law. The finite cost equals the full extended Legendre rate there. -/
theorem eventually_empirical_open_ge_at_derivative
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (G : Set ℝ) (k epsilon : ℝ)
    (hG : IsOpen G)
    (ha : deriv (fun q => spectralAbscissa (tilt L v g q)) k ∈ G)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) *
        (k * deriv (fun q => spectralAbscissa (tilt L v g q)) k -
          spectralAbscissa (tilt L v g k) + epsilon)) ≤
        (normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g n).real G := by
  let mu : ℕ → Measure ℝ := fun n =>
    normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g n
  letI : ∀ n, IsProbabilityMeasure (mu n) := fun n =>
    normalizedRewardLaw_isProbabilityMeasure L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g n (Nat.cast_nonneg n)
  have hconv := convexOn_spectralAbscissa L hL hirr v g
  have hd := (IrreducibleFiniteCTMCSCGF.analyticAt_spectralAbscissa
    L hL hirr v g k).differentiableAt.hasDerivAt
  have hbound := GartnerEllisOpenSetLowerBound.eventually_originalMass_open_lower_bound_at_exposed
    mu (fun q => spectralAbscissa (tilt L v g q)) G k _ epsilon hG ha hconv hd hepsilon
    (fun n q => integrable_exp_normalizedRewardLaw L hL (escapeRate_pos L hL hirr)
      x₀ p v g q n (Nat.cast_nonneg n))
    (fun _ => integrable_const 1)
    (fun n q => integral_exp_normalizedRewardLaw_pos L hL (escapeRate_pos L hL hirr)
      x₀ p hp hsum v g q n (Nat.cast_nonneg n))
    (fun q => tendsto_normalizedLogMoment L hL hirr x₀ p hp hsum v g q)
  rw [DifferentiableLegendreDual.rateFunction_at_derivative hconv hd] at hbound
  filter_upwards [hbound] with n hn
  simpa only [originalMass_eq_measureReal (mu n) G hG.measurableSet] using hn

end

end NCG.FiniteCTMCRewardDeviationBounds
