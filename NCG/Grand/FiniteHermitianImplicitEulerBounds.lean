/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianResolventGap
import NCG.Grand.ScalarImplicitEulerBounds

/-!
# Uniform implicit-Euler approximation for finite Hermitian operators

The scalar implicit-Euler estimate is dimension free.  This file transports it first to a
diagonal finite nonnegative spectrum, and then through the canonical unitary eigenbasis of a
positive-semidefinite Hermitian matrix.  The resulting operator-norm estimate is uniform both in
the dimension and over the whole nonnegative spectrum.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The exact heat multiplier in a finite diagonal spectral frame. -/
def finiteSpectralHeat (ν : ι → ℝ) (t : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i ↦ ((Real.exp (-(t * ν i)) : ℝ) : ℂ)

/-- The order-`k` implicit-Euler multiplier in a finite diagonal spectral frame. -/
def finiteSpectralEuler (ν : ι → ℝ) (t : ℝ) (k : ℕ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i ↦ ((multiplier k (t * ν i) : ℝ) : ℂ)

/-- Dimension-free operator-norm Euler approximation in a nonnegative diagonal spectral frame. -/
theorem norm_finiteSpectralEuler_sub_heat_le_inv_sqrt
    (ν : ι → ℝ) (t : ℝ) (k : ℕ) (ht : 0 ≤ t) (hk : 0 < k)
    (hν : ∀ i, 0 ≤ ν i) :
    ‖finiteSpectralEuler ν t k - finiteSpectralHeat ν t‖ ≤
      (Real.sqrt (k : ℝ))⁻¹ := by
  have htarget : 0 ≤ (Real.sqrt (k : ℝ))⁻¹ := by positivity
  have hdiag :
      finiteSpectralEuler ν t k - finiteSpectralHeat ν t =
        Matrix.diagonal (fun i ↦
          ((multiplier k (t * ν i) - Real.exp (-(t * ν i)) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [finiteSpectralEuler, finiteSpectralHeat]
    · simp [finiteSpectralEuler, finiteSpectralHeat, hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg htarget).2
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_multiplier_sub_exp_neg_le_inv_sqrt hk
    (mul_nonneg ht (hν i))

/-- The heat multiplier transported by a chosen unitary spectral frame. -/
def finiteUnitarySpectralHeat (U : Matrix.unitaryGroup ι ℂ)
    (ν : ι → ℝ) (t : ℝ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (finiteSpectralHeat ν t)

/-- The implicit-Euler multiplier transported by a chosen unitary spectral frame. -/
def finiteUnitarySpectralEuler (U : Matrix.unitaryGroup ι ℂ)
    (ν : ι → ℝ) (t : ℝ) (k : ℕ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (finiteSpectralEuler ν t k)

/-- Unitary spectral transport preserves the dimension-free Euler approximation estimate. -/
theorem norm_finiteUnitarySpectralEuler_sub_heat_le_inv_sqrt
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (t : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hk : 0 < k) (hν : ∀ i, 0 ≤ ν i) :
    ‖finiteUnitarySpectralEuler U ν t k - finiteUnitarySpectralHeat U ν t‖ ≤
      (Real.sqrt (k : ℝ))⁻¹ := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have hsub :
      finiteUnitarySpectralEuler U ν t k - finiteUnitarySpectralHeat U ν t =
        e (finiteSpectralEuler ν t k - finiteSpectralHeat ν t) := by
    change e (finiteSpectralEuler ν t k) - e (finiteSpectralHeat ν t) =
      e (finiteSpectralEuler ν t k - finiteSpectralHeat ν t)
    exact (map_sub e _ _).symm
  rw [hsub]
  change ‖(U : Matrix ι ι ℂ) *
      (finiteSpectralEuler ν t k - finiteSpectralHeat ν t) *
      (star U : Matrix ι ι ℂ)‖ ≤ _
  rw [← Unitary.coe_star]
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  exact norm_finiteSpectralEuler_sub_heat_le_inv_sqrt ν t k ht hk hν

/-- Canonical spectral heat operator of a Hermitian matrix. -/
def finiteHermitianHeat {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    Matrix ι ι ℂ :=
  finiteUnitarySpectralHeat hA.eigenvectorUnitary hA.eigenvalues t

/-- Canonical spectral implicit-Euler operator of a Hermitian matrix. -/
def finiteHermitianEuler {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) (k : ℕ) :
    Matrix ι ι ℂ :=
  finiteUnitarySpectralEuler hA.eigenvectorUnitary hA.eigenvalues t k

/-- Uniform operator-norm implicit-Euler approximation for a positive-semidefinite Hermitian
matrix.  The bound is independent of the matrix size and of its spectral radius. -/
theorem norm_finiteHermitianEuler_sub_heat_le_inv_sqrt
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hk : 0 < k) :
    ‖finiteHermitianEuler hA.1 t k - finiteHermitianHeat hA.1 t‖ ≤
      (Real.sqrt (k : ℝ))⁻¹ := by
  exact norm_finiteUnitarySpectralEuler_sub_heat_le_inv_sqrt
    hA.1.eigenvectorUnitary hA.1.eigenvalues t k ht hk hA.eigenvalues_nonneg

/-- Zero-indexed uniform Euler estimate, ready for convergence compilers. -/
theorem norm_finiteHermitianEuler_succ_sub_heat_le_errorRate
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) (m : ℕ) (ht : 0 ≤ t) :
    ‖finiteHermitianEuler hA.1 t (m + 1) - finiteHermitianHeat hA.1 t‖ ≤ errorRate m := by
  simpa [errorRate, Nat.cast_add, Nat.cast_one] using
    norm_finiteHermitianEuler_sub_heat_le_inv_sqrt hA t (m + 1) ht (Nat.succ_pos m)

end NCG.ImplicitEuler
