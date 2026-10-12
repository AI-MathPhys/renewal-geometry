/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Grading projectors and the cross-sign mass of a linear map

Split out of `MathPhys.Operational.ActiveOddLiftInvarianceExact`:

* `eq_sum_smul_single`, `linearMap_apply_eq_sum`: a matrix is the sum of its scaled matrix
  units, so a linear map on matrices is determined by its values on matrix units;
* `gradingPlus Z = (1 + Z)/2`, `gradingMinus Z = (1 − Z)/2`;
* `activeCrossSignMass Z Φ = Tr[P₋ Φ(P₊)] + Tr[P₊ Φ(P₋)]` (`eq:active-cross-sign-mass`).
-/

open Matrix
open scoped Kronecker

namespace MathPhys
namespace ActiveOddLift

variable {dA dK : Type*} [Fintype dA] [Fintype dK] [DecidableEq dA] [DecidableEq dK]

/-- A matrix is the sum of its scaled matrix units. -/
theorem eq_sum_smul_single {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℂ) :
    A = ∑ i, ∑ j, A i j • single i j (1 : ℂ) := by
  conv_lhs => rw [matrix_eq_sum_single A]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_single, smul_eq_mul, mul_one]

/-- A linear map on matrices is determined by its values on matrix units. -/
theorem linearMap_apply_eq_sum {m : Type*} [Fintype m] [DecidableEq m]
    (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ) (A : Matrix m m ℂ) :
    Φ A = ∑ i, ∑ j, A i j • Φ (single i j 1) := by
  conv_lhs => rw [eq_sum_smul_single A]
  simp only [map_sum, map_smul]

/-- The grading projector `P₊ = (1 + Z)/2`. -/
noncomputable def gradingPlus (Z : Matrix dA dA ℂ) : Matrix dA dA ℂ :=
  (2 : ℂ)⁻¹ • (1 + Z)

/-- The grading projector `P₋ = (1 − Z)/2`. -/
noncomputable def gradingMinus (Z : Matrix dA dA ℂ) : Matrix dA dA ℂ :=
  (2 : ℂ)⁻¹ • (1 - Z)

/-- The active cross-sign mass `μ_Z^act(Φ) = Tr[P₋ Φ(P₊)] + Tr[P₊ Φ(P₋)]`
(`eq:active-cross-sign-mass`). -/
noncomputable def activeCrossSignMass (Z : Matrix dA dA ℂ)
    (Φ : Matrix dA dA ℂ →ₗ[ℂ] Matrix dA dA ℂ) : ℂ :=
  (gradingMinus Z * Φ (gradingPlus Z)).trace + (gradingPlus Z * Φ (gradingMinus Z)).trace

end ActiveOddLift
end MathPhys
