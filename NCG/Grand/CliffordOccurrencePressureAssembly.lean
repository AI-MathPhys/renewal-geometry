/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CliffordTwirlMatterAudit
import NCG.Grand.SMSTCliffordPressureMatterExact

/-!
# Clifford occurrence to accepted-pressure assembly

This module closes the operator-to-probability bridge in
`cor:SMST-Clifford-pressure-matter`.  The probability supplied to the renewal
pressure is not an independent scalar: it is the real value of the normalized
Hilbert--Schmidt Clifford occurrence.  Positivity of the cross-corner Gram and
of the complementary chirality residual prove that it lies in `[0,1]`.
-/

open Finset Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace CliffordOccurrencePressure

open CliffordTwirlMatterAudit SMSTChannel

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The real Clifford flip probability extracted from the operator packet. -/
def probability (J : Block n) (σ : Fin 4 → Block n) : ℝ :=
  (cliffordProbability J σ).re

/-- The real Hilbert--Schmidt Clifford occurrence mass. -/
def occurrenceMass (J : Block n) (σ : Fin 4 → Block n) : ℝ :=
  (cliffordOccurrence J σ).re

theorem cliffordProbability_nonnegative
    (J : Block n) (σ : Fin 4 → Block n) :
    (0 : ℂ) ≤ cliffordProbability J σ := by
  unfold cliffordProbability
  apply mul_nonneg
  · norm_num [Complex.nonneg_iff]
  · apply Finset.sum_nonneg
    intro μ _
    unfold axisProbability
    positivity [axisOccurrence_nonnegative J (σ μ)]

theorem chiralityResidual_nonnegative
    (J : Block n) (σ : Fin 4 → Block n) :
    (0 : ℂ) ≤ chiralityResidual J σ := by
  unfold chiralityResidual
  exact Finset.sum_nonneg fun μ _ =>
    (Matrix.posSemidef_conjTranspose_mul_self
      (J * σ μ * J + σ μ)).trace_nonneg

/-- The operator-defined Clifford probability lies in the physical interval. -/
theorem probability_mem_unitInterval
    (J : Block n) (σ : Fin 4 → Block n)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : ∀ μ, (σ μ)ᴴ = σ μ) (hσ2 : ∀ μ, σ μ * σ μ = 1) :
    0 ≤ probability J σ ∧ probability J σ ≤ 1 := by
  have hpC := cliffordProbability_nonnegative J σ
  have hp0 : 0 ≤ probability J σ := by
    exact (Complex.nonneg_iff.mp hpC).1
  have hchirC := chiralityResidual_nonnegative J σ
  have hchir0 : 0 ≤ (chiralityResidual J σ).re :=
    (Complex.nonneg_iff.mp hchirC).1
  have hformula :=
    (cliffordResidual_formulas J σ hJH hJ2 hσH hσ2).2.1
  have hformulaRe := congrArg Complex.re hformula
  have hcard : 0 < (Fintype.card n : ℝ) := by positivity
  have hreal : (chiralityResidual J σ).re =
      16 * (Fintype.card n : ℝ) * (1 - probability J σ) := by
    simpa [probability] using hformulaRe
  constructor
  · exact hp0
  · rw [hreal] at hchir0
    nlinarith

/-- The operator occurrence mass is exactly `2 D p_Cl`. -/
theorem occurrenceMass_eq_two_card_mul_probability
    (J : Block n) (σ : Fin 4 → Block n)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : ∀ μ, (σ μ)ᴴ = σ μ) (hσ2 : ∀ μ, σ μ * σ μ = 1) :
    occurrenceMass J σ =
      2 * (Fintype.card n : ℝ) * probability J σ := by
  have h := (cliffordOccurrence_formulas J σ hJH hJ2 hσH hσ2).2
  have hre := congrArg Complex.re h
  simpa [occurrenceMass, probability] using hre

/-- One certificate tying the common-carrier Clifford occurrence directly to
the accepted-count pressure, both mass readings, and the binary Hessian gap. -/
structure Certificate
    (J : Block n) (σ : Fin 4 → Block n) (ϑ : ℝ) : Prop where
  probabilityRange : 0 ≤ probability J σ ∧ probability J σ ≤ 1
  occurrenceMassFormula : occurrenceMass J σ =
    2 * (Fintype.card n : ℝ) * probability J σ
  countPressure : ∀ q (k : ℕ), 0 < k →
    (1 / k) * Real.log
      (∑ g : Fin k → CliffordSample,
        (∏ i, flipWeight ϑ (probability J σ) (g i)) *
          Real.exp (-q * (∑ i, (flipCount (g i) : ℝ)))) =
      cliffordPressure ϑ (probability J σ) q
  countPressureSlope : HasDerivAt
    (fun q => cliffordPressure ϑ (probability J σ) q)
    (-(ϑ * probability J σ)) 0
  massFromCountSlope :
    -(2 * (Fintype.card n : ℝ) / ϑ) *
        (-(ϑ * probability J σ)) = occurrenceMass J σ
  rawTimeSlope :
    (-(ϑ * probability J σ)) / (11 / 4) =
      -(4 * ϑ / 11) * probability J σ
  massFromRawTimeSlope :
    -(11 * (Fintype.card n : ℝ) / (2 * ϑ)) *
        (-(4 * ϑ / 11) * probability J σ) = occurrenceMass J σ
  stationaryVariance : ∀ dp dm xp xm : ℝ, dp + dm ≠ 0 →
    (dp / (dp + dm)) * xp ^ 2 + (dm / (dp + dm)) * xm ^ 2 -
        ((dp * xp + dm * xm) / (dp + dm)) ^ 2 =
      (dp * dm / (dp + dm) ^ 2) * (xp - xm) ^ 2
  binaryHessian : ∀ xp xm : ℝ,
    (∑ ω : CliffordSample, flipWeight ϑ (probability J σ) ω *
      ((flipCount ω : ℝ) * (xp - xm) ^ 2)) =
      ϑ * probability J σ * (xp - xm) ^ 2
  countGap : ∀ dp dm xp xm : ℝ,
    dp ≠ 0 → dm ≠ 0 → dp + dm ≠ 0 →
    ϑ * probability J σ * (xp - xm) ^ 2 =
      (ϑ * probability J σ * (dp + dm) ^ 2 / (dp * dm)) *
        ((dp * dm / (dp + dm) ^ 2) * (xp - xm) ^ 2)
  rawTimeGap : ∀ dp dm : ℝ,
    (4 / 11) *
        (ϑ * probability J σ * (dp + dm) ^ 2 / (dp * dm)) =
      4 * ϑ * probability J σ * (dp + dm) ^ 2 /
        (11 * (dp * dm))

/-- `cor:SMST-Clifford-pressure-matter`, assembled from the actual finite
operator packet rather than an independently declared flip probability. -/
theorem acceptedPressure_from_cliffordOccurrence
    (J : Block n) (σ : Fin 4 → Block n) (ϑ : ℝ)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : ∀ μ, (σ μ)ᴴ = σ μ) (hσ2 : ∀ μ, σ μ * σ μ = 1)
    (hϑ0 : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) (hϑ : ϑ ≠ 0) :
    Certificate J σ ϑ := by
  have hp := probability_mem_unitInterval J σ hJH hJ2 hσH hσ2
  have hmass := occurrenceMass_eq_two_card_mul_probability
    J σ hJH hJ2 hσH hσ2
  refine {
    probabilityRange := hp
    occurrenceMassFormula := hmass
    countPressure := fun q k hk => pressure_scgf ϑ (probability J σ) q k hk
    countPressureSlope := pressure_hasDerivAt_zero ϑ (probability J σ)
      hϑ0 hϑ1 hp.1 hp.2
    massFromCountSlope := ?_
    rawTimeSlope := raw_time_slope ϑ (probability J σ)
    massFromRawTimeSlope := ?_
    stationaryVariance := stationary_variance_form
    binaryHessian := hessian_second_moment ϑ (probability J σ)
    countGap := hessian_gap ϑ (probability J σ)
    rawTimeGap := hessian_gap_time ϑ (probability J σ) }
  · rw [mass_from_count_slope ϑ (probability J σ)
      (Fintype.card n : ℝ) hϑ, hmass]
  · rw [mass_from_time_slope ϑ (probability J σ)
      (Fintype.card n : ℝ) hϑ, hmass]

end CliffordOccurrencePressure
end NCG
