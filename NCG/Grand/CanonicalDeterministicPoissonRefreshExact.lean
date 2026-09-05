/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CoarseAndHiddenEntropyProduction

/-!
# Canonical deterministic Poisson refresh

The large-rate Markov assertion for the canonical deterministic quotient and
its faithful stationary decoder, together with the exact semigroup, quotient,
and small-time obstruction clauses.
-/

open Matrix NormedSpace Finset

namespace NCG
namespace CanonicalDeterministicPoissonRefreshExact

open CanonicalFiniteRateFibreRefresh UniversalMarkovRetract
open CoarseAndHiddenEntropyProduction

/-- Every row of the stationary conditional decoder has mass one. -/
theorem stationaryDecoder_row_sum
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (z : Z) :
    ∑ u, stationaryDecoder c m z u = 1 := by
  classical
  simp only [stationaryDecoder]
  rw [← Finset.sum_filter, ← Finset.sum_div]
  have hmass : ∑ u ∈ Finset.univ.filter (fun u ↦ c u = z), m u =
      cellMass c m z := by
    simp [cellMass, Finset.sum_filter]
  rw [hmass, div_self (cellMass_pos c hc m hm z).ne']

/-- The deterministic conditional expectation is stochastic row-wise. -/
theorem conditionalExpectation_row_sum
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (u : U) :
    ∑ v, conditionalExpectation c m u v = 1 := by
  classical
  rw [show conditionalExpectation c m = recordMatrix c * stationaryDecoder c m by rfl]
  simp only [Matrix.mul_apply]
  calc
    ∑ v, ∑ z, recordMatrix c u z * stationaryDecoder c m z v =
        ∑ z, recordMatrix c u z * (∑ v, stationaryDecoder c m z v) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.mul_sum]
    _ = ∑ z, recordMatrix c u z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [stationaryDecoder_row_sum c hc m hm z, mul_one]
    _ = 1 := by simp [recordMatrix]

/-- Lifting a coarse zero-row-sum generator through the canonical decoder
again gives zero row sums. -/
theorem embedded_coarse_row_sum
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (A : Matrix Z Z ℝ)
    (hAsum : ∀ z, ∑ z', A z z' = 0) (u : U) :
    ∑ v, (recordMatrix c * A * stationaryDecoder c m) u v = 0 := by
  classical
  simp only [Matrix.mul_apply]
  calc
    ∑ v, ∑ z, (∑ x, recordMatrix c u x * A x z) *
          stationaryDecoder c m z v =
        ∑ z, (∑ x, recordMatrix c u x * A x z) *
          (∑ v, stationaryDecoder c m z v) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro z _
            rw [Finset.mul_sum]
    _ = ∑ z, ∑ x, recordMatrix c u x * A x z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [stationaryDecoder_row_sum c hc m hm z, mul_one]
    _ = ∑ x, recordMatrix c u x * (∑ z, A x z) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ = 0 := by simp [hAsum]

/-- The canonical conditional expectation has nonnegative off-diagonal
entries, and every same-cell entry is strictly positive. -/
theorem conditionalExpectation_offdiag_and_same_cell_pos
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) :
    (∀ u v, u ≠ v → 0 ≤ conditionalExpectation c m u v) ∧
      (∀ u v, c u = c v → 0 < conditionalExpectation c m u v) := by
  constructor
  · intro u v _
    unfold conditionalExpectation
    rw [conditional_expectation_apply]
    split
    · exact (div_pos (hm v) (cellMass_pos c hc m hm (c v))).le
    · exact le_rfl
  · intro u v huv
    unfold conditionalExpectation
    rw [conditional_expectation_apply, if_pos huv]
    exact div_pos (hm v) (cellMass_pos c hc m hm (c v))

/-- For a genuine coarse Markov generator, every negative lifted
off-diagonal rate is necessarily internal to a record cell and hence lies on
a strictly positive refresh edge. -/
theorem negative_embedded_rate_has_refresh_support
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (A : Matrix Z Z ℝ)
    (hAoff : ∀ x z, x ≠ z → 0 ≤ A x z) :
    ∀ u v, u ≠ v →
      (recordMatrix c * A * stationaryDecoder c m) u v < 0 →
      0 < conditionalExpectation c m u v := by
  intro u v huv hneg
  have hcell : c u = c v := by
    by_contra hcell
    rw [embedded_coarse_generator_apply] at hneg
    have hweight : 0 < m v / cellMass c m (c v) :=
      div_pos (hm v) (cellMass_pos c hc m hm (c v))
    rw [div_eq_mul_inv] at hneg hweight
    rw [mul_assoc] at hneg
    exact (not_lt_of_ge (mul_nonneg (hAoff _ _ hcell) hweight.le)) hneg
  exact (conditionalExpectation_offdiag_and_same_cell_pos c hc m hm).2 u v hcell

/-- Exact canonical finite-rate Poisson refresh.  The Markov threshold now
follows from the defining deterministic quotient and faithful conditional
decoder; no extra support hypothesis is required. -/
theorem canonical_finite_rate_fibre_refresh
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (A : Matrix Z Z ℝ)
    (hA : IsFiniteMarkovGenerator A) :
    let C := recordMatrix c
    let R := stationaryDecoder c m
    let E := C * R
    (∃ threshold : ℝ, ∀ lam ≥ threshold,
        IsFiniteMarkovGenerator (refreshGenerator C R A lam)) ∧
      (∀ lam t : ℝ,
        exp (t • refreshGenerator C R A lam) =
          C * exp (t • A) * R + Real.exp (-lam * t) • (1 - E)) ∧
      (∀ lam : ℝ,
        refreshGenerator C R A lam * C = C * A ∧
          R * refreshGenerator C R A lam = A * R) ∧
      (∀ (S : ℕ → Matrix U U ℝ),
        Filter.Tendsto S Filter.atTop (nhds 1) →
        (∀ n, S n = E * S n * E) → E = 1) := by
  dsimp
  let C := recordMatrix c
  let R := stationaryDecoder c m
  have hRC : R * C = (1 : Matrix Z Z ℝ) :=
    stationaryDecoder_mul_recordMatrix c hc m hm
  have hEsum : ∀ u, ∑ v, (C * R) u v = 1 :=
    conditionalExpectation_row_sum c hc m hm
  have hEoff : ∀ u v, u ≠ v → 0 ≤ (C * R) u v :=
    (conditionalExpectation_offdiag_and_same_cell_pos c hc m hm).1
  have hBsum : ∀ u, ∑ v, (C * A * R) u v = 0 :=
    embedded_coarse_row_sum c hc m hm A hA.2
  have hsupport : ∀ u v, u ≠ v → (C * A * R) u v < 0 →
      0 < (C * R) u v :=
    negative_embedded_rate_has_refresh_support c hc m hm A hA.1
  refine ⟨exists_rate_making_all_larger_refreshes_markov C R A
      hBsum hEsum hEoff hsupport, ?_, ?_, ?_⟩
  · intro lam t
    exact refreshGenerator_exp C R A hRC lam t
  · intro lam
    exact refreshGenerator_exact_quotient_dynamics C R A hRC lam
  · intro S hcontinuous hreset
    have hE2 : (C * R) * (C * R) = C * R := by
      calc
        (C * R) * (C * R) = C * (R * C) * R := by simp [Matrix.mul_assoc]
        _ = C * R := by rw [hRC]; simp
    exact exact_reset_at_arbitrarily_small_times_forces_identity
      (C * R) hE2 S hcontinuous hreset

end CanonicalDeterministicPoissonRefreshExact
end NCG
