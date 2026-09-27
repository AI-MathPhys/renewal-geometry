/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.ShiftedPlaquetteLogarithmExact
/-!
# Unit conjugation of the series logarithm and unitary invariance of the Frobenius norm

Infrastructure for the gauge-covariance clause of `thm:finite-action-identities`
(spacetime–gauge duality paper): class functions of the plaquette holonomy.

* `unitConjCLE u`: conjugation `z ↦ u z u⁻¹` by a unit of a real normed algebra, as a
  continuous linear automorphism; `tsum_unit_conj`: it commutes with `∑'` unconditionally.
* `ShiftedPlaquette.logQuotient_unit_conj`, `ShiftedPlaquette.logOneAdd_unit_conj`,
  `ShiftedPlaquette.logOneAdd_conj_of_mul_eq_one`: the principal (series) logarithm
  `log (1 + z) = ∑ₙ (−1)ⁿ/(n+1) · z^{n+1}` is equivariant under conjugation by units,
  `log (1 + u z u⁻¹) = u · log (1 + z) · u⁻¹`, for every `z` (both sides are the junk value
  `0`-based `tsum` outside the disc of convergence, so no smallness hypothesis is needed).
* `frobSq M = Re tr (Mᴴ M)`, the squared Frobenius norm of a complex matrix, is invariant
  under left multiplication by an isometry (`Uᴴ U = 1`), right multiplication by a
  co-isometry (`W Wᴴ = 1`), and hence under unitary conjugation.
-/

open NormedSpace Matrix

namespace RenewalGeometry

section UnitConjugation

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

/-- Conjugation `z ↦ u z u⁻¹` by a unit, as a continuous `ℝ`-linear automorphism. -/
noncomputable def unitConjCLE (u : 𝔄ˣ) : 𝔄 ≃L[ℝ] 𝔄 :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.mul ℝ 𝔄 (u : 𝔄)).comp
      ((ContinuousLinearMap.mul ℝ 𝔄).flip (↑u⁻¹ : 𝔄)))
    ((ContinuousLinearMap.mul ℝ 𝔄 (↑u⁻¹ : 𝔄)).comp
      ((ContinuousLinearMap.mul ℝ 𝔄).flip (u : 𝔄)))
    (fun z => by simp [mul_assoc]) (fun z => by simp [mul_assoc])

@[simp] theorem unitConjCLE_apply (u : 𝔄ˣ) (z : 𝔄) :
    unitConjCLE u z = (u : 𝔄) * z * ↑u⁻¹ := by
  change (u : 𝔄) * (z * ↑u⁻¹) = _
  rw [mul_assoc]

/-- Conjugation by a unit commutes with `∑'` (no summability hypothesis: both sides are
`0` when the series does not converge). -/
theorem tsum_unit_conj (u : 𝔄ˣ) (f : ℕ → 𝔄) :
    (u : 𝔄) * (∑' n, f n) * ↑u⁻¹ = ∑' n, (u : 𝔄) * f n * ↑u⁻¹ := by
  have h := (unitConjCLE u).map_tsum (L := SummationFilter.unconditional ℕ) (f := f)
  simpa using h

/-- The removable-quotient series `L(z) = ∑ₙ (−1)ⁿ/(n+1) zⁿ` of `log (1 + z) = z L(z)` is
equivariant under conjugation by units. -/
theorem ShiftedPlaquette.logQuotient_unit_conj (u : 𝔄ˣ) (z : 𝔄) :
    ShiftedPlaquette.logQuotient ((u : 𝔄) * z * ↑u⁻¹) =
      (u : 𝔄) * ShiftedPlaquette.logQuotient z * ↑u⁻¹ := by
  have h1 : ∀ w : 𝔄, ShiftedPlaquette.logQuotient w =
      ∑' n, ShiftedPlaquette.logQuotientCoeff n • w ^ n := fun w =>
    FormalMultilinearSeries.ofScalars_sum_eq ShiftedPlaquette.logQuotientCoeff w
  rw [h1, h1, tsum_unit_conj]
  refine tsum_congr fun n => ?_
  rw [Units.conj_pow, mul_smul_comm, smul_mul_assoc]

/-- **The principal (series) logarithm is equivariant under conjugation by units**:
`log (1 + u z u⁻¹) = u · log (1 + z) · u⁻¹`. -/
theorem ShiftedPlaquette.logOneAdd_unit_conj (u : 𝔄ˣ) (z : 𝔄) :
    ShiftedPlaquette.logOneAdd ((u : 𝔄) * z * ↑u⁻¹) =
      (u : 𝔄) * ShiftedPlaquette.logOneAdd z * ↑u⁻¹ := by
  unfold ShiftedPlaquette.logOneAdd
  rw [ShiftedPlaquette.logQuotient_unit_conj]
  simp [mul_assoc]

/-- The series logarithm is equivariant under conjugation by a two-sided inverse pair
`u v = v u = 1`. -/
theorem ShiftedPlaquette.logOneAdd_conj_of_mul_eq_one {u v : 𝔄} (huv : u * v = 1)
    (hvu : v * u = 1) (z : 𝔄) :
    ShiftedPlaquette.logOneAdd (u * z * v) = u * ShiftedPlaquette.logOneAdd z * v :=
  ShiftedPlaquette.logOneAdd_unit_conj ⟨u, v, huv, hvu⟩ z

end UnitConjugation

section Frobenius

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-- The squared Frobenius norm `Re tr (Mᴴ M)` of a complex matrix (the norms `|F|²` and
`‖D_U H‖²` of `eq:finite-SM-action`). -/
noncomputable def frobSq (M : Matrix m n ℂ) : ℝ := (Mᴴ * M).trace.re

/-- Left multiplication by an isometry preserves the Frobenius norm. -/
theorem frobSq_mul_left_of_conjTranspose_mul [DecidableEq m] (U : Matrix k m ℂ)
    (hU : Uᴴ * U = 1) (M : Matrix m n ℂ) : frobSq (U * M) = frobSq M := by
  unfold frobSq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]

/-- Right multiplication by a co-isometry preserves the Frobenius norm. -/
theorem frobSq_mul_right_of_mul_conjTranspose [DecidableEq n] (M : Matrix m n ℂ)
    (W : Matrix n k ℂ) (hW : W * Wᴴ = 1) : frobSq (M * W) = frobSq M := by
  unfold frobSq
  rw [Matrix.conjTranspose_mul, Matrix.trace_mul_cycle, Matrix.mul_assoc M W, hW,
    Matrix.mul_one, Matrix.trace_mul_comm]

/-- Conjugation `M ↦ U M V` by an isometry `U` and a co-isometry `V` (in particular unitary
conjugation) preserves the Frobenius norm. -/
theorem frobSq_conj_of_mul [DecidableEq m] [DecidableEq n] (U : Matrix k m ℂ)
    (hU : Uᴴ * U = 1) (M : Matrix m n ℂ) (V : Matrix n k ℂ) (hV : V * Vᴴ = 1) :
    frobSq (U * M * V) = frobSq M := by
  rw [frobSq_mul_right_of_mul_conjTranspose _ V hV, frobSq_mul_left_of_conjTranspose_mul U hU]

end Frobenius

end RenewalGeometry
