/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Complex eigenvalue bounds from a positive left Perron vector

A positive left eigenvector gives a weighted L1 estimate. The triangle
inequality then bounds the modulus of every complex eigenvalue of a
nonnegative real matrix by its positive-vector eigenvalue.
-/

namespace NCG.NonnegativeMatrixComplexEigenvalueBound

open Matrix
open scoped BigOperators

variable {S : Type*} [Fintype S]

/-- Triangle inequality for a complex vector acted on by a nonnegative real matrix. -/
theorem norm_mulVec_le (B : Matrix S S ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (z : S → ℂ) (i : S) :
    ‖(B.map Complex.ofReal).mulVec z i‖ ≤ ∑ j, B i j * ‖z j‖ := by
  calc
    _ ≤ ∑ j, ‖(B i j : ℂ) * z j‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hB i j)]

/-- A strictly positive left eigenvector controls the modulus of every
complex eigenvalue; no positivity of the complex eigenvector is assumed. -/
theorem norm_eigenvalue_le
    (B : Matrix S S ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (ell : S → ℝ) (hell : ∀ i, 0 < ell i) (rho : ℝ)
    (hleft : B.vecMul ell = rho • ell)
    (lam : ℂ) (z : S → ℂ) (hz : z ≠ 0)
    (heig : (B.map Complex.ofReal).mulVec z = lam • z) : ‖lam‖ ≤ rho := by
  have hzpos : ∃ i, 0 < ‖z i‖ := by
    by_contra! h
    apply hz
    funext i
    exact norm_eq_zero.mp (le_antisymm (h i) (norm_nonneg _))
  let mass : ℝ := ∑ i, ell i * ‖z i‖
  have hmass : 0 < mass := by
    obtain ⟨i, hi⟩ := hzpos
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hell j).le (norm_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hell i) hi⟩
  have hbound : ‖lam‖ * mass ≤ rho * mass := by
    calc
      _ = ∑ i, ell i * ‖(B.map Complex.ofReal).mulVec z i‖ := by
        rw [heig]
        simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, ell i * (∑ j, B i j * ‖z j‖) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (norm_mulVec_le B hB z i) (hell i).le
      _ = ∑ j, B.vecMul ell j * ‖z j‖ := by
        simp only [Finset.mul_sum, Matrix.vecMul, dotProduct, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = rho * mass := by
        rw [hleft]
        simp only [Pi.smul_apply, smul_eq_mul, mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  nlinarith

end NCG.NonnegativeMatrixComplexEigenvalueBound
