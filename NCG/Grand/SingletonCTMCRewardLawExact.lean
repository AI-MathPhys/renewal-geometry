/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCGeneralRewardLawExact
import NCG.Grand.SingletonGeneratorSpectralExact

/-!
# Exact stochastic SCGF and large deviations for the singleton process

The same physical law used for general generators has the deterministic
exponential moment `exp(T*k*v(x))` on a singleton carrier. Thus the full
real-time LDP follows without excluding the zero generator or assuming a
positive escape rate. The rate is zero at the deterministic mean and
infinite everywhere else.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace NCG.SingletonCTMCRewardLaw

open DrivenProcess FiniteCTMCGeneralPathLaw FiniteCTMCGeneralRewardLaw
open SingletonGeneratorSpectral MetzlerSpectralAbscissa FiniteCTMCSCGFConvexity

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] [Subsingleton S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem integral_exp_physicalRewardLaw_eq
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (hT : 0 ≤ T) :
    (∫ a : ℝ, Real.exp (T * k * a) ∂physicalRewardLaw L hL x₀ p v g T) =
      Real.exp (T * (k * v x₀)) := by
  rw [integral_exp_physicalRewardLaw_eq_pathMoment L hL x₀ p v g k T hT,
    physicalPathMoment_eq_exponentialEntry_pairing L hL x₀ p hp v g k T (fun _ => 1) hT]
  have heig : Matrix.mulVec (tilt L v g k) (fun _ => 1) = (k * v x₀) • (fun _ => 1) := by
    ext i
    have hi : i = x₀ := Subsingleton.elim _ _
    simp [Matrix.mulVec, dotProduct, univ_eq_singleton x₀, hi, tilt,
      generator_eq_zero L hL x₀]
  rw [IrreducibleMetzlerSCGF.exponentialEntry_smul_mulVec_eigenvector
    (tilt L v g k) (fun _ => 1) (k * v x₀) T heig]
  simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  rw [← Finset.sum_mul, hsum, one_mul]

theorem tendsto_scaled_log_integral_exp
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    Tendsto (fun T : ℝ => Real.log
      (∫ a : ℝ, Real.exp (T * k * a) ∂physicalRewardLaw L hL x₀ p v g T) / T)
      atTop (𝓝 (spectralAbscissa (tilt L v g k))) := by
  rw [spectralAbscissa_tilt_eq L hL x₀ v g k]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hTpos : 0 < T := by linarith
  rw [integral_exp_physicalRewardLaw_eq L hL x₀ p hp hsum v g k T hTpos.le, Real.log_exp]
  field_simp

theorem hasLargeDeviationPrinciple
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) :
    RealTimeLargeDeviations.HasLargeDeviationPrinciple
      (fun T => physicalRewardLaw L hL x₀ p v g T) (spectralRate L v g) := by
  apply RealTimeLargeDeviations.hasLargeDeviationPrinciple_of_differentiable_logMoment
    _ (fun q => spectralAbscissa (tilt L v g q))
  · exact fun T hT => physicalRewardLaw_isProbabilityMeasure L hL x₀ p hp hsum v g T hT
  · exact fun q => (analyticAt_spectralAbscissa_tilt L hL x₀ v g q).differentiableAt
  · exact fun T hT q => integrable_exp_physicalRewardLaw L hL x₀ p v g q T hT
  · exact fun T hT q => integral_exp_physicalRewardLaw_pos L hL x₀ p hp hsum v g q T hT
  · exact fun q => tendsto_scaled_log_integral_exp L hL x₀ p hp hsum v g q

theorem spectralRate_at_mean (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S)
    (v : S → ℝ) (g : S → S → ℝ) : spectralRate L v g (v x₀) = 0 := by
  have hfun : (fun q => spectralAbscissa (tilt L v g q)) = (fun q => q * v x₀) :=
    funext fun q => spectralAbscissa_tilt_eq L hL x₀ v g q
  unfold spectralRate
  rw [hfun]
  exact ExtendedLegendreRate.rate_linear_at_mean (v x₀)

theorem spectralRate_eq_top_of_ne (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S)
    (v : S → ℝ) (g : S → S → ℝ) (a : ℝ) (ha : a ≠ v x₀) : spectralRate L v g a = ⊤ := by
  have hfun : (fun q => spectralAbscissa (tilt L v g q)) = (fun q => q * v x₀) :=
    funext fun q => spectralAbscissa_tilt_eq L hL x₀ v g q
  unfold spectralRate
  rw [hfun]
  exact ExtendedLegendreRate.rate_linear_eq_top_of_ne (v x₀) a ha

/-- Direct positive left/right Perron vectors, avoiding the positive-loop
irreducibility predicate which would exclude the singleton zero matrix. -/
theorem exists_normalized_positive_left_right_eigenvectors
    (A : Matrix S S ℝ) (x₀ : S) :
    ∃ r ell : S → ℝ, (∀ i, 0 < r i) ∧ (∀ i, 0 < ell i) ∧
      A.mulVec r = spectralAbscissa A • r ∧
      A.vecMul ell = spectralAbscissa A • ell ∧ ell ⬝ᵥ r = 1 := by
  refine ⟨fun _ => 1, fun _ => 1, fun _ => zero_lt_one, fun _ => zero_lt_one, ?_, ?_, ?_⟩
  · ext i
    have hi : i = x₀ := Subsingleton.elim _ _
    simp [Matrix.mulVec, dotProduct, univ_eq_singleton x₀, hi, spectralAbscissa_eq_entry A x₀]
  · ext i
    have hi : i = x₀ := Subsingleton.elim _ _
    simp [Matrix.vecMul, dotProduct, univ_eq_singleton x₀, hi, spectralAbscissa_eq_entry A x₀]
  · simp [dotProduct, univ_eq_singleton x₀]

end

end NCG.SingletonCTMCRewardLaw
