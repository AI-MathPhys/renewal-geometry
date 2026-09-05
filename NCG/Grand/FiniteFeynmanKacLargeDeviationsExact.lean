/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteGeneratorCommunicationExact
import NCG.Grand.SingletonCTMCRewardLawExact

/-!
# Finite Feynman--Kac, analytic SCGF, and the full large-deviation compiler

This is the all-carrier assembly for `thm:accepted-Feynman-Kac-LDP`.
The physical law is a measurable projection of a genuine positive-escape
Ionescu--Tulcea process and is available for every finite generator.
Irreducibility is standard positive-rate reachability, including singleton
zero generators. Both full LDP bounds hold at arbitrary real horizons with
the extended-valued Legendre rate; no spectral, stochastic, differentiability,
integrability, tightness, or endpoint approximation oracle is assumed.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators Matrix

namespace NCG.FiniteFeynmanKacLargeDeviations

open DrivenProcess FiniteGeneratorCommunication FiniteCTMCGeneralPathLaw
open FiniteCTMCGeneralRewardLaw FiniteCTMCSCGFConvexity
open MetzlerSpectralAbscissa MetzlerPerronExponent IrreducibleGeneratorEscape

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Analyticity under standard irreducibility, including the singleton branch. -/
theorem analyticAt_spectralAbscissa
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hconn : IsCommunicating L) (x₀ : S)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    AnalyticAt ℝ (fun q => spectralAbscissa (tilt L v g q)) k := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    exact SingletonGeneratorSpectral.analyticAt_spectralAbscissa_tilt L hL x₀ v g k
  · letI := hS
    exact IrreducibleFiniteCTMCSCGF.analyticAt_spectralAbscissa L hL
      (isIrreducibleMetzler_of_isCommunicating L hL hconn) v g k

/-- Positive normalized left and right eigenvectors at the actual spectral bound. -/
theorem exists_positive_perron_pair
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hconn : IsCommunicating L) (x₀ : S)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    ∃ r ell : S → ℝ, (∀ i, 0 < r i) ∧ (∀ i, 0 < ell i) ∧
      (tilt L v g k).mulVec r = spectralAbscissa (tilt L v g k) • r ∧
      (tilt L v g k).vecMul ell = spectralAbscissa (tilt L v g k) • ell ∧ ell ⬝ᵥ r = 1 := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    exact SingletonCTMCRewardLaw.exists_normalized_positive_left_right_eigenvectors
      (tilt L v g k) x₀
  · letI := hS
    have htilt := tilt_isIrreducibleMetzler L hL
      (isIrreducibleMetzler_of_isCommunicating L hL hconn) v g k
    rw [spectralAbscissa_eq_exponent _ htilt]
    exact exists_normalized_positive_left_right_eigenvectors (tilt L v g k) htilt

/-- Algebraic simplicity in the actual complex spectrum, on every finite carrier. -/
theorem complex_rootMultiplicity_spectralAbscissa_eq_one
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hconn : IsCommunicating L) (x₀ : S)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    ((tilt L v g k).map Complex.ofReal).charpoly.rootMultiplicity
      (spectralAbscissa (tilt L v g k) : ℂ) = 1 := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    exact SingletonGeneratorSpectral.complex_rootMultiplicity_spectralAbscissa_eq_one
      (tilt L v g k) x₀
  · letI := hS
    exact PerronAlgebraicSimplicity.complex_rootMultiplicity_spectralAbscissa_eq_one
      (tilt L v g k) (tilt_isIrreducibleMetzler L hL
        (isIrreducibleMetzler_of_isCommunicating L hL hconn) v g k)

/-- The actual physical-path log moment converges along all real horizons. -/
theorem tendsto_scaled_log_physicalPathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hconn : IsCommunicating L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    Tendsto (fun T : ℝ => Real.log (physicalPathMoment L hL x₀ p v g k T (fun _ => 1)) / T)
      atTop (𝓝 (spectralAbscissa (tilt L v g k))) := by
  have hlim : Tendsto (fun T : ℝ => Real.log
      (∫ a : ℝ, Real.exp (T * k * a) ∂physicalRewardLaw L hL x₀ p v g T) / T)
      atTop (𝓝 (spectralAbscissa (tilt L v g k))) := by
    rcases subsingleton_or_nontrivial S with hS | hS
    · letI := hS
      exact SingletonCTMCRewardLaw.tendsto_scaled_log_integral_exp L hL x₀ p hp hsum v g k
    · letI := hS
      exact FiniteCTMCGeneralRewardLaw.tendsto_scaled_log_integral_exp L hL
        (isIrreducibleMetzler_of_isCommunicating L hL hconn) x₀ p hp hsum v g k
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [integral_exp_physicalRewardLaw_eq_pathMoment L hL x₀ p v g k T hT]

/-- The full real-time LDP for the same physical probability law, on all finite carriers. -/
theorem hasLargeDeviationPrinciple
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hconn : IsCommunicating L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) :
    RealTimeLargeDeviations.HasLargeDeviationPrinciple
      (fun T => physicalRewardLaw L hL x₀ p v g T) (spectralRate L v g) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    exact SingletonCTMCRewardLaw.hasLargeDeviationPrinciple L hL x₀ p hp hsum v g
  · letI := hS
    exact FiniteCTMCGeneralRewardLaw.hasLargeDeviationPrinciple L hL
      (isIrreducibleMetzler_of_isCommunicating L hL hconn) x₀ p hp hsum v g

theorem spectralRate_nonnegative
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hconn : IsCommunicating L) (x₀ : S)
    (v : S → ℝ) (g : S → S → ℝ) (a : ℝ) : 0 ≤ spectralRate L v g a := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    by_cases ha : a = v x₀
    · rw [ha, SingletonCTMCRewardLaw.spectralRate_at_mean L hL x₀ v g]
    · rw [SingletonCTMCRewardLaw.spectralRate_eq_top_of_ne L hL x₀ v g a ha]
      exact le_top
  · letI := hS
    exact spectralRate_nonneg L hL (isIrreducibleMetzler_of_isCommunicating L hL hconn) v g a

theorem exists_spectralRate_zero
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hconn : IsCommunicating L) (x₀ : S)
    (v : S → ℝ) (g : S → S → ℝ) : ∃ a : ℝ, spectralRate L v g a = 0 := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    exact ⟨v x₀, SingletonCTMCRewardLaw.spectralRate_at_mean L hL x₀ v g⟩
  · letI := hS
    exact FiniteCTMCSCGFConvexity.exists_spectralRate_zero L hL
      (isIrreducibleMetzler_of_isCommunicating L hL hconn) v g

/-- Complete manuscript compiler: arbitrary-generator Feynman--Kac, and,
under standard irreducibility only, the simple analytic Perron SCGF, genuine
real-time moment limit, and full LDP with a nonnegative convex good rate. -/
theorem finite_feynmanKac_scgf_largeDeviations
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) :
    (∀ k T : ℝ, ∀ f : S → ℝ, 0 ≤ T →
      physicalPathMoment L hL x₀ p v g k T f =
        ∑ x, p x * Matrix.mulVec (Matrix.exponentialEntry (T • tilt L v g k)) f x) ∧
    (IsCommunicating L →
      (∀ k : ℝ, AnalyticAt ℝ (fun q => spectralAbscissa (tilt L v g q)) k) ∧
      (∀ k : ℝ, ∃ r ell : S → ℝ, (∀ i, 0 < r i) ∧ (∀ i, 0 < ell i) ∧
        (tilt L v g k).mulVec r = spectralAbscissa (tilt L v g k) • r ∧
        (tilt L v g k).vecMul ell = spectralAbscissa (tilt L v g k) • ell ∧ ell ⬝ᵥ r = 1) ∧
      (∀ k : ℝ, ((tilt L v g k).map Complex.ofReal).charpoly.rootMultiplicity
        (spectralAbscissa (tilt L v g k) : ℂ) = 1) ∧
      (∀ k : ℝ, Tendsto (fun T : ℝ =>
        Real.log (physicalPathMoment L hL x₀ p v g k T (fun _ => 1)) / T)
        atTop (𝓝 (spectralAbscissa (tilt L v g k)))) ∧
      RealTimeLargeDeviations.HasLargeDeviationPrinciple
        (fun T => physicalRewardLaw L hL x₀ p v g T) (spectralRate L v g) ∧
      (∀ a : ℝ, 0 ≤ spectralRate L v g a) ∧
      (∃ a : ℝ, spectralRate L v g a = 0) ∧
      (∀ r : ℝ, IsCompact {a : ℝ | spectralRate L v g a ≤ (r : EReal)}) ∧
      Convex ℝ {z : ℝ × ℝ | spectralRate L v g z.1 ≤ (z.2 : EReal)}) := by
  refine ⟨fun k T f hT => physicalPathMoment_eq_exponentialEntry_pairing
    L hL x₀ p hp v g k T f hT, ?_⟩
  intro hconn
  exact ⟨analyticAt_spectralAbscissa L hL hconn x₀ v g,
    exists_positive_perron_pair L hL hconn x₀ v g,
    complex_rootMultiplicity_spectralAbscissa_eq_one L hL hconn x₀ v g,
    tendsto_scaled_log_physicalPathMoment L hL hconn x₀ p hp hsum v g,
    hasLargeDeviationPrinciple L hL hconn x₀ p hp hsum v g,
    spectralRate_nonnegative L hL hconn x₀ v g,
    exists_spectralRate_zero L hL hconn x₀ v g,
    isCompact_spectralRate_sublevel L v g, convex_spectralRate_epigraph L v g⟩

end

end NCG.FiniteFeynmanKacLargeDeviations
