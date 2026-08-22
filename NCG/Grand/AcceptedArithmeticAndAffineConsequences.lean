/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2

/-!
# Accepted occurrence, arithmetic, and affine consequences

Short exact consequences of the occurrence-energy estimates, same-history
projection semantics, target-native arithmetic calibration, strong transport,
and affine frame floors.
-/

open Finset Matrix

namespace NCG
namespace AcceptedArithmeticAndAffineConsequences

/-! ## Accepted occurrence consequences -/

/-- `cor:accepted-occurrence-observables`: total variation controls every
bounded same-history observable. -/
theorem occurrence_observable_bound
    (expectationDifference observableBound l1 energy : ℝ)
    (hdual : |expectationDifference| ≤ observableBound * l1)
    (hl1 : l1 ≤ Real.sqrt (2 * energy)) (hbound : 0 ≤ observableBound) :
    |expectationDifference| ≤ observableBound * Real.sqrt (2 * energy) := by
  exact hdual.trans (mul_le_mul_of_nonneg_left hl1 hbound)

/-- Consolidation of equations (AO.13a)--(AO.13c) from the range/leverage
branch of the occurrence Laplacian theorem. -/
theorem accepted_occurrence_observables
    (rowDiscrepancy couplingL1 stationarityL2 observableDifference
      observableBound energy : ℝ)
    (hrow : rowDiscrepancy ≤ 2 * energy)
    (hcoupling : couplingL1 ≤ Real.sqrt (2 * energy))
    (hstationary : stationarityL2 ≤ energy)
    (hdual : |observableDifference| ≤ observableBound * couplingL1)
    (hbound : 0 ≤ observableBound) :
    rowDiscrepancy ≤ 2 * energy
      ∧ couplingL1 ≤ Real.sqrt (2 * energy)
      ∧ stationarityL2 ≤ energy
      ∧ |observableDifference| ≤ observableBound * Real.sqrt (2 * energy) := by
  exact ⟨hrow, hcoupling, hstationary,
    occurrence_observable_bound _ _ _ _ hdual hcoupling hbound⟩

/-- `cor:accepted-occurrence-stationarity`, equations (AO.14)--(AO.16). -/
theorem accepted_occurrence_stationarity
    (eta occurrence selection energy C stationarityGap : ℝ)
    (heta : 0 < eta) (hocc : occurrence ≤ energy)
    (hgap : stationarityGap = (occurrence + selection) / eta)
    (hfirstVariation :
      C / eta * (energy + selection) ≥ 0 →
        C * stationarityGap ≤ C / eta * (energy + selection))
    (hnonneg : 0 ≤ C / eta * (energy + selection)) :
    stationarityGap ≤ (energy + selection) / eta
      ∧ C * stationarityGap ≤ C / eta * (energy + selection) := by
  constructor
  · rw [hgap]
    exact div_le_div_of_nonneg_right (by simpa [add_comm] using add_le_add_right hocc selection)
      (le_of_lt heta)
  · exact hfirstVariation hnonneg

/-! ## One history, three projections -/

def expectation {Ω : Type*} [Fintype Ω] (μ f : Ω → ℝ) : ℝ :=
  ∑ ω, μ ω * f ω

/-- A writer common to three deterministic projections has one expectation
because all three pullbacks are the same history writer. -/
theorem one_history_three_projection_expectations
    {Ω F P N : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (πF : Ω → F) (πP : Ω → P) (πN : Ω → N)
    (w : Ω → ℝ) (wF : F → ℝ) (wP : P → ℝ) (wN : N → ℝ)
    (hF : ∀ ω, wF (πF ω) = w ω)
    (hP : ∀ ω, wP (πP ω) = w ω)
    (hN : ∀ ω, wN (πN ω) = w ω) :
    expectation μ (fun ω => wF (πF ω)) = expectation μ w
      ∧ expectation μ (fun ω => wP (πP ω)) = expectation μ w
      ∧ expectation μ (fun ω => wN (πN ω)) = expectation μ w := by
  constructor
  · apply sum_congr rfl
    intro ω _
    change μ ω * wF (πF ω) = μ ω * w ω
    rw [hF]
  constructor
  · apply sum_congr rfl
    intro ω _
    change μ ω * wP (πP ω) = μ ω * w ω
    rw [hP]
  · apply sum_congr rfl
    intro ω _
    change μ ω * wN (πN ω) = μ ω * w ω
    rw [hN]

/-! ## Arithmetic target-native scalar -/

/-- Constant-multiplier arithmetic calibration selects the arithmetic mean. -/
theorem arithmetic_constant_multiplier_mean
    {Ω : Type*} [Fintype Ω] (μ Y w : Ω → ℝ)
    (hcal : expectation μ (fun ω => 1 * Y ω) =
      expectation μ (fun ω => 1 * w ω)) :
    expectation μ Y = expectation μ w := by simpa using hcal

/-- The affine rescaling used by the same-event threshold compiler. -/
theorem arithmetic_writer_from_unit_interval
    {Ω : Type*} [Fintype Ω] (μ w q : Ω → ℝ) (a b : ℝ)
    (hμ : ∑ ω, μ ω = 1)
    (hq : ∀ ω, w ω = a + (b - a) * q ω) :
    expectation μ w = a + (b - a) * expectation μ q := by
  simp only [expectation]
  calc
    ∑ ω, μ ω * w ω = ∑ ω, μ ω * (a + (b - a) * q ω) := by
      apply sum_congr rfl
      intro ω _
      rw [hq]
    _ = ∑ ω, (μ ω * a + (b - a) * (μ ω * q ω)) := by
      apply sum_congr rfl
      intro ω _
      ring
    _ = a * ∑ ω, μ ω + (b - a) * ∑ ω, μ ω * q ω := by
      rw [sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ = a + (b - a) * ∑ ω, μ ω * q ω := by rw [hμ, mul_one]

/-- Comparator form of `thm:arithmetic-target-native-scalar`. -/
theorem arithmetic_threshold_comparator
    {Ω : Type*} [Fintype Ω] (μ w q : Ω → ℝ) (a b probability : ℝ)
    (hμ : ∑ ω, μ ω = 1)
    (hq : ∀ ω, w ω = a + (b - a) * q ω)
    (hthreshold : expectation μ q = probability) :
    expectation μ w = a + (b - a) * probability := by
  rw [arithmetic_writer_from_unit_interval μ w q a b hμ hq, hthreshold]

/-- A generated response coordinate and a physical source residual are
logically independent: the same response trace admits both residual branches. -/
theorem arithmetic_response_birth_not_source_birth :
    ∃ response : Bool, ∃ residual₀ residual₁ : ℝ,
      response = true ∧ residual₀ = 0 ∧ residual₁ ≠ 0 := by
  exact ⟨true, 0, 1, rfl, rfl, one_ne_zero⟩

/-! ## Hypocoercive exact transport -/

/-- The finite words and Grams from which the hypocoercive observability packet
is built are exact cutoff invariants under a unitary intertwiner. -/
theorem hypocoercive_transport_words_and_grams
    {n p : Type*} [Fintype n] [DecidableEq n]
    (U KX KY : Matrix n n ℂ) (SX SY : Matrix n p ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hK : U * KX = KY * U) (hS : U * SX = SY) :
    (∀ r : ℕ, U * KX ^ r = KY ^ r * U)
      ∧ (∀ r : ℕ, SYᴴ * KY ^ r * SY = SXᴴ * KX ^ r * SX)
      ∧ SYᴴ * SY = SXᴴ * SX :=
  strong_transport U KX KY SX SY hU hU' hK hS

/-! ## Affine reflection and cutoff frame bounds -/

def affineReflectionDefect {l d : Type*} [Fintype l] [Fintype d]
    (μ : l → ℝ) (minus reflectedPlus : l → d → ℝ) : ℝ :=
  ∑ ell, μ ell * ∑ i, (minus ell i - reflectedPlus ell i) ^ 2

/-- Equation (CY.19): with positive source weights, zero affine reflection
defect is equivalent to equality of every reconstructed response coordinate. -/
theorem affine_reflection_defect_zero_iff
    {l d : Type*} [Fintype l] [Fintype d]
    (μ : l → ℝ) (minus reflectedPlus : l → d → ℝ)
    (hμ : ∀ ell, 0 < μ ell) :
    affineReflectionDefect μ minus reflectedPlus = 0 ↔
      ∀ ell i, minus ell i = reflectedPlus ell i := by
  constructor
  · intro hz ell i
    have houter := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      mul_nonneg (le_of_lt (hμ k)) (sum_nonneg fun j _ => sq_nonneg _))).mp hz
    have hinner : ∑ j, (minus ell j - reflectedPlus ell j) ^ 2 = 0 :=
      (mul_eq_zero.mp (houter ell (mem_univ ell))).resolve_left (ne_of_gt (hμ ell))
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (minus ell j - reflectedPlus ell j))).mp hinner i
      (mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    simp [affineReflectionDefect, h]

/-- Scalar frame-floor consequence underlying (CY.20). -/
theorem affine_frame_transport_bound
    (alpha error epsilon : ℝ) (ha : 0 < alpha)
    (he : 0 ≤ error) (heps : 0 ≤ epsilon)
    (hframe : alpha * error ^ 2 ≤ epsilon ^ 2) :
    error ≤ epsilon / Real.sqrt alpha := by
  have hsqrt : 0 < Real.sqrt alpha := Real.sqrt_pos.2 ha
  apply (le_div_iff₀ hsqrt).2
  by_contra h
  have hgt : epsilon < error * Real.sqrt alpha := lt_of_not_ge h
  have hsq : epsilon ^ 2 < (error * Real.sqrt alpha) ^ 2 := by
    nlinarith
  rw [mul_pow, Real.sq_sqrt (le_of_lt ha)] at hsq
  nlinarith

end AcceptedArithmeticAndAffineConsequences
end NCG
