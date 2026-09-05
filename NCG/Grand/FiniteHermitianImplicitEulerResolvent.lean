/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianImplicitEulerBounds

/-!
# Implicit Euler as a literal resolvent power

This file identifies the spectral implicit-Euler operator with the usual matrix formula
`(I + (t / k) A)⁻ᵏ`.  Combined with the dimension-free estimate in
`FiniteHermitianImplicitEulerBounds`, this removes the spectral-frame notation from the final
operator-norm bound.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The one-step diagonal implicit-Euler resolvent before taking its kth power. -/
def finiteSpectralEulerRoot (ν : ι → ℝ) (t : ℝ) (k : ℕ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i ↦
    ((((1 + (t * ν i) / (k : ℝ))⁻¹) : ℝ) : ℂ)

/-- The spectral Euler multiplier is the kth power of its one-step diagonal resolvent. -/
theorem finiteSpectralEuler_eq_root_pow (ν : ι → ℝ) (t : ℝ) (k : ℕ) :
    finiteSpectralEuler ν t k = finiteSpectralEulerRoot ν t k ^ k := by
  unfold finiteSpectralEuler finiteSpectralEulerRoot multiplier
  rw [Matrix.diagonal_pow]
  congr 1
  funext i
  exact Complex.ofReal_pow _ _

omit [Fintype ι] in
/-- The shifted diagonal matrix used by one implicit-Euler step is literally diagonal. -/
theorem one_add_smul_diagonal_eq_diagonal
    (ν : ι → ℝ) (t : ℝ) (k : ℕ) :
    (1 : Matrix ι ι ℂ) +
        (((t / (k : ℝ) : ℝ) : ℂ) •
          Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))) =
      Matrix.diagonal (fun i ↦
        (((1 + (t * ν i) / (k : ℝ)) : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, if_pos]
    push_cast
    ring
  · simp [Matrix.add_apply, Matrix.smul_apply, hij]

/-- Under the natural positivity hypotheses, the diagonal Euler root is a left inverse of the
shifted diagonal generator. -/
theorem finiteSpectralEulerRoot_mul_one_add_smul_diagonal
    (ν : ι → ℝ) (t : ℝ) (k : ℕ) (ht : 0 ≤ t) (hk : 0 < k)
    (hν : ∀ i, 0 ≤ ν i) :
    finiteSpectralEulerRoot ν t k *
        ((1 : Matrix ι ι ℂ) +
          (((t / (k : ℝ) : ℝ) : ℂ) •
            Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)))) = 1 := by
  rw [one_add_smul_diagonal_eq_diagonal]
  unfold finiteSpectralEulerRoot
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hdenom : 1 + (t * ν i) / (k : ℝ) ≠ 0 := by
      have : 0 ≤ (t * ν i) / (k : ℝ) := div_nonneg (mul_nonneg ht (hν i)) hkR.le
      linarith
    simp only [Matrix.diagonal_apply, Matrix.one_apply, if_pos]
    rw [Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hdenom)
  · simp [hij]

/-- The one-step diagonal Euler resolvent is the literal matrix inverse. -/
theorem finiteSpectralEulerRoot_eq_inv_one_add_smul
    (ν : ι → ℝ) (t : ℝ) (k : ℕ) (ht : 0 ≤ t) (hk : 0 < k)
    (hν : ∀ i, 0 ≤ ν i) :
    finiteSpectralEulerRoot ν t k =
      ((1 : Matrix ι ι ℂ) +
        (((t / (k : ℝ) : ℝ) : ℂ) •
          Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))))⁻¹ := by
  exact (Matrix.inv_eq_left_inv
    (finiteSpectralEulerRoot_mul_one_add_smul_diagonal ν t k ht hk hν)).symm

/-- The diagonal spectral Euler multiplier is the literal power of the corresponding shifted
diagonal inverse. -/
theorem finiteSpectralEuler_eq_inv_one_add_smul_pow
    (ν : ι → ℝ) (t : ℝ) (k : ℕ) (ht : 0 ≤ t) (hk : 0 < k)
    (hν : ∀ i, 0 ≤ ν i) :
    finiteSpectralEuler ν t k =
      ((1 : Matrix ι ι ℂ) +
        (((t / (k : ℝ) : ℝ) : ℂ) •
          Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))))⁻¹ ^ k := by
  rw [finiteSpectralEuler_eq_root_pow,
    finiteSpectralEulerRoot_eq_inv_one_add_smul ν t k ht hk hν]

/-- A unitary spectral change of frame turns the diagonal Euler multiplier into the literal
resolvent power of the transported diagonal generator. -/
theorem finiteUnitarySpectralEuler_eq_inv_one_add_smul_pow
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (t : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hk : 0 < k) (hν : ∀ i, 0 ≤ ν i) :
    finiteUnitarySpectralEuler U ν t k =
      ((1 : Matrix ι ι ℂ) +
        (((t / (k : ℝ) : ℝ) : ℂ) •
          Unitary.conjStarAlgAut ℂ _ U
            (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)))))⁻¹ ^ k := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have hroot :
      e (finiteSpectralEulerRoot ν t k) =
        ((1 : Matrix ι ι ℂ) +
          (((t / (k : ℝ) : ℝ) : ℂ) •
            e (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)))))⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    calc
      e (finiteSpectralEulerRoot ν t k) *
          ((1 : Matrix ι ι ℂ) +
            (((t / (k : ℝ) : ℝ) : ℂ) •
              e (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))))) =
        e (finiteSpectralEulerRoot ν t k *
          ((1 : Matrix ι ι ℂ) +
            (((t / (k : ℝ) : ℝ) : ℂ) •
              Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))))) := by
          simp only [map_mul, map_add, map_one, map_smul]
      _ = e 1 := by
        rw [finiteSpectralEulerRoot_mul_one_add_smul_diagonal ν t k ht hk hν]
      _ = 1 := map_one e
  change e (finiteSpectralEuler ν t k) = _
  rw [finiteSpectralEuler_eq_root_pow, map_pow, hroot]

/-- In the canonical eigenbasis, the spectral Euler operator is the literal implicit-Euler
resolvent power of the Hermitian matrix. -/
theorem finiteHermitianEuler_eq_inv_one_add_smul_pow
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hk : 0 < k) (hν : ∀ i, 0 ≤ hA.eigenvalues i) :
    finiteHermitianEuler hA t k =
      ((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ k := by
  have hspectral :
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (Matrix.diagonal (fun i ↦ ((hA.eigenvalues i : ℝ) : ℂ))) = A := by
    calc
      _ = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
        apply congrArg (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary)
        ext i j
        by_cases hij : i = j
        · subst j
          simp only [Matrix.diagonal_apply, if_pos, Function.comp_apply]
          apply Complex.ext <;> simp [RCLike.ofReal]
        · simp [hij]
      _ = A := hA.spectral_theorem.symm
  unfold finiteHermitianEuler
  rw [finiteUnitarySpectralEuler_eq_inv_one_add_smul_pow
    _ _ _ _ ht hk hν, hspectral]

/-- Dimension-free approximation of the finite heat operator by the literal implicit-Euler
resolvent power. -/
theorem norm_inv_one_add_smul_pow_sub_finiteHermitianHeat_le_inv_sqrt
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hk : 0 < k) :
    ‖((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ k -
        finiteHermitianHeat hA.1 t‖ ≤ (Real.sqrt (k : ℝ))⁻¹ := by
  rw [← finiteHermitianEuler_eq_inv_one_add_smul_pow hA.1 t k ht hk hA.eigenvalues_nonneg]
  exact norm_finiteHermitianEuler_sub_heat_le_inv_sqrt hA t k ht hk

/-- Zero-indexed literal-resolvent version, with the explicit rate consumed by convergence
compilers. -/
theorem norm_inv_one_add_smul_succ_pow_sub_finiteHermitianHeat_le_errorRate
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) (m : ℕ) (ht : 0 ≤ t) :
    ‖((1 : Matrix ι ι ℂ) +
          (((t / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ (m + 1) -
        finiteHermitianHeat hA.1 t‖ ≤ errorRate m := by
  rw [← finiteHermitianEuler_eq_inv_one_add_smul_pow hA.1 t (m + 1)
    ht (Nat.succ_pos m) hA.eigenvalues_nonneg]
  exact norm_finiteHermitianEuler_succ_sub_heat_le_errorRate hA t m ht

end NCG.ImplicitEuler
