/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveQuotientFamily
import NCG.Grand.AtomicResetOrderedCone

/-!
# Dynamics and minimality of the positive renewal quotient family

This module completes the dynamical and minimal-ordered-quotient clauses of
`thm:positive-renewal-quotient-family`.
-/

open Matrix

namespace NCG

def positiveRenewalBackflow (a : ℚ) : ℚ :=
  (5 * a - 1) * (1 - 3 * a) / (15 * (1 - a))

def positiveRenewalDwell (a : ℚ) : ℚ := 8 / 15 - a

def positiveRenewalCompletion (a : ℚ) : ℚ := 8 / (15 * (1 - a))

def positiveRenewalQ (a : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![a, 1 - a; positiveRenewalBackflow a, positiveRenewalDwell a]

/-- Resetting every completion to the anchored first state produces the
two-state stochastic recurrent chain. -/
def positiveRenewalResetChain (a : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![a, 1 - a;
      positiveRenewalBackflow a + positiveRenewalCompletion a,
      positiveRenewalDwell a]

/-- Reachability matrix of the anchored row source `e₀`. -/
def positiveRenewalReachability (a : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0; a, 1 - a]

/-- Observability matrix for the completion column `(0,r_P)`. -/
def positiveRenewalObservability (a : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, positiveRenewalCompletion a;
      (1 - a) * positiveRenewalCompletion a,
      positiveRenewalDwell a * positiveRenewalCompletion a]

/-- Every member of the positive interval is reachable and future separated:
both canonical two-step Krylov matrices are invertible. -/
theorem positiveRenewal_reachable_futureSeparated (a : ℚ)
    (ha1 : 1 / 5 ≤ a) (ha2 : a ≤ 1 / 3) :
    IsUnit (positiveRenewalReachability a).det
      ∧ IsUnit (positiveRenewalObservability a).det := by
  have h1a : 1 - a ≠ 0 := by
    intro h
    have : a = 1 := by linarith
    linarith
  have hr : positiveRenewalCompletion a ≠ 0 := by
    simp only [positiveRenewalCompletion]
    positivity
  constructor <;> apply isUnit_iff_ne_zero.mpr
  · simp [positiveRenewalReachability, Matrix.det_fin_two_of, h1a]
  · simp [positiveRenewalObservability, Matrix.det_fin_two_of, h1a, hr]

/-- The reset chain is stochastic, has eigenvalues `1,-7/15`, and its
stationary completion flux is exactly `4/11`, independently of `a`. -/
theorem positiveRenewal_resetChain_spectrum_flux (a : ℚ)
    (ha1 : 1 / 5 ≤ a) (ha2 : a ≤ 1 / 3) :
    (∀ i, ∑ j, positiveRenewalResetChain a i j = 1)
      ∧ (positiveRenewalResetChain a).trace = 8 / 15
      ∧ (positiveRenewalResetChain a).det = -7 / 15
      ∧ (∃ π : Fin 2 → ℚ,
          π 0 + π 1 = 1
            ∧ (fun j => ∑ i, π i * positiveRenewalResetChain a i j) = π
            ∧ π 1 * positiveRenewalCompletion a = 4 / 11) := by
  have h1a : 1 - a ≠ 0 := by
    intro h
    have : a = 1 := by linarith
    linarith
  have hfamily := positive_renewal_quotient_family a ha1 ha2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp [positiveRenewalResetChain]
    · simp [positiveRenewalResetChain, positiveRenewalBackflow,
        positiveRenewalCompletion, positiveRenewalDwell]
      field_simp
      ring
  · simp [positiveRenewalResetChain, positiveRenewalDwell,
      Matrix.trace_fin_two_of]
  · simp [positiveRenewalResetChain, Matrix.det_fin_two_of,
      positiveRenewalBackflow, positiveRenewalCompletion,
      positiveRenewalDwell]
    field_simp [h1a]
    ring
  · refine ⟨![(7 + 15 * a) / 22, 15 * (1 - a) / 22],
      by simp; ring, ?_, ?_⟩
    · funext j
      fin_cases j
      · simp [positiveRenewalResetChain, positiveRenewalBackflow,
          positiveRenewalCompletion]
        field_simp [h1a]
        ring
      · simp [positiveRenewalResetChain, positiveRenewalDwell]
        ring
    · simp [positiveRenewalCompletion]
      field_simp [h1a]
      ring

/-- The first four nonzero first-return coefficients have a nonzero leading
two-by-two Hankel minor; hence the target scalar renewal law has Hankel rank at
least two. -/
theorem targetRenewal_leadingHankelMinor :
    (!![(8 / 15 : ℚ), 64 / 225;
        64 / 225, 392 / 3375] : Matrix (Fin 2) (Fin 2) ℚ).det
      = -64 / 3375
      ∧ (!![(8 / 15 : ℚ), 64 / 225;
          64 / 225, 392 / 3375] : Matrix (Fin 2) (Fin 2) ℚ).rank = 2 := by
  constructor
  · rw [Matrix.det_fin_two_of]
    norm_num
  · have hunit : IsUnit
        (!![(8 / 15 : ℚ), 64 / 225;
            64 / 225, 392 / 3375] : Matrix (Fin 2) (Fin 2) ℚ).det := by
      apply isUnit_iff_ne_zero.mpr
      rw [Matrix.det_fin_two_of]
      norm_num
    rw [Matrix.rank_of_isUnit _
      ((Matrix.isUnit_iff_isUnit_det _).mpr hunit), Fintype.card_fin]

/-- A minimal predictive quotient realizing this law is necessarily
two-dimensional once its dimension is identified with scalar Hankel rank. -/
theorem minimalPositiveRenewalQuotient_dimension_two
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (hminimalRank : Module.finrank ℚ V =
      (!![(8 / 15 : ℚ), 64 / 225;
          64 / 225, 392 / 3375] : Matrix (Fin 2) (Fin 2) ℚ).rank) :
    Module.finrank ℚ V = 2 := by
  rw [hminimalRank, targetRenewal_leadingHankelMinor.2]

/-- The back-transition vanishes exactly at the two serial endpoints. -/
theorem positiveRenewal_serialEndpoints (a : ℚ) (ha : a ≠ 1) :
    positiveRenewalBackflow a = 0 ↔ a = 1 / 5 ∨ a = 1 / 3 := by
  simp only [positiveRenewalBackflow]
  have hden : (15 : ℚ) * (1 - a) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm ha))
  constructor
  · intro h
    have hnum : (5 * a - 1) * (1 - 3 * a) = 0 :=
      (div_eq_zero_iff.mp h).resolve_right hden
    rcases mul_eq_zero.mp hnum with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Once a two-dimensional proper cone is written in its two normalized
extreme-ray coordinates, comparison with the target first-return numerator,
trace, and determinant forces exactly the manuscript family. -/
theorem anchoredPositiveRenewal_coefficients_forced
    (a c d rP : ℚ) (ha : a ≠ 1)
    (htrace : a + d = 8 / 15)
    (hdet : a * d - (1 - a) * c = 1 / 15)
    (hnorm : (1 - a) * rP = 8 / 15) :
    d = positiveRenewalDwell a
      ∧ c = positiveRenewalBackflow a
      ∧ rP = positiveRenewalCompletion a := by
  have h1a : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hd : d = 8 / 15 - a := by linarith
  constructor
  · simp only [positiveRenewalDwell]
    exact hd
  constructor
  · simp only [positiveRenewalBackflow]
    apply (eq_div_iff (mul_ne_zero (by norm_num) h1a)).2
    rw [hd] at hdet
    field_simp [h1a] at hdet ⊢
    nlinarith
  · simp only [positiveRenewalCompletion]
    apply (eq_div_iff (mul_ne_zero (by norm_num) h1a)).2
    linarith

end NCG
