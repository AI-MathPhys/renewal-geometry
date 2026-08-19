/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianSemigroupConvergence
import NCG.Grand.FiniteHermitianResolventGap

/-!
# Euler roots as scaled shifted resolvents

For a positive time and Euler order `k`, the one-step multiplier
`(I + (t/k)A)⁻¹` is exactly `(k/t) ((k/t)I + A)⁻¹`.  This elementary scaling
identity connects the finite Hermitian semigroup compiler directly to positive-shift resolvent
families obtained from graph-form Mosco convergence.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The literal positive-shift resolvent of a finite Hermitian generator, bundled as a
continuous operator on Euclidean space. -/
def finiteHermitianShiftedResolventOperator (A : Matrix ι ι ℂ) (lam : ℝ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
    ((((lam : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹)

omit [Fintype ι] in
/-- The diagonal one-step Euler multiplier is a positive scalar multiple of the shifted
diagonal resolvent. -/
theorem finiteSpectralEulerRoot_eq_smul_finiteSpectralResolvent
    (ν : ι → ℝ) (t : ℝ) (k : ℕ) (ht : 0 < t) (hk : 0 < k)
    (hν : ∀ i, 0 ≤ ν i) :
    finiteSpectralEulerRoot ν t k =
      ((((k : ℝ) / t : ℝ) : ℂ)) •
        NCG.SpectralGap.finiteSpectralResolvent ν ((k : ℝ) / t) := by
  unfold finiteSpectralEulerRoot NCG.SpectralGap.finiteSpectralResolvent
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply, if_pos, Matrix.smul_apply]
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
    have hkR : (k : ℝ) ≠ 0 := ne_of_gt hkPos
    have hfracNonneg : 0 ≤ t * ν i / (k : ℝ) :=
      div_nonneg (mul_nonneg ht.le (hν i)) hkPos.le
    have hleft : 1 + t * ν i / (k : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hlamPos : 0 < (k : ℝ) / t := div_pos hkPos ht
    have hright : (k : ℝ) / t + ν i ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg hlamPos (hν i))
    have hreal :
        (1 + t * ν i / (k : ℝ))⁻¹ =
          ((k : ℝ) / t) * (((k : ℝ) / t + ν i)⁻¹) := by
      field_simp [ht0, hkR, hleft, hright]
    change (((1 + t * ν i / (k : ℝ))⁻¹ : ℝ) : ℂ) =
      (((k : ℝ) / t : ℝ) : ℂ) * ((((k : ℝ) / t + ν i)⁻¹ : ℝ) : ℂ)
    exact_mod_cast hreal
  · simp [Matrix.smul_apply, hij]

/-- Unitary spectral transport preserves the one-step Euler root formula. -/
theorem finiteUnitarySpectralEulerRoot_eq_inv_one_add_smul
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (t : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hk : 0 < k) (hν : ∀ i, 0 ≤ ν i) :
    Unitary.conjStarAlgAut ℂ _ U (finiteSpectralEulerRoot ν t k) =
      ((1 : Matrix ι ι ℂ) +
        (((t / (k : ℝ) : ℝ) : ℂ) •
          Unitary.conjStarAlgAut ℂ _ U
            (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)))))⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  calc
    Unitary.conjStarAlgAut ℂ _ U (finiteSpectralEulerRoot ν t k) *
          ((1 : Matrix ι ι ℂ) +
            (((t / (k : ℝ) : ℝ) : ℂ) •
              Unitary.conjStarAlgAut ℂ _ U
                (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))))) =
        Unitary.conjStarAlgAut ℂ _ U
          (finiteSpectralEulerRoot ν t k *
            ((1 : Matrix ι ι ℂ) +
              (((t / (k : ℝ) : ℝ) : ℂ) •
                Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))))) := by
          simp only [map_mul, map_add, map_one, map_smul]
    _ = Unitary.conjStarAlgAut ℂ _ U 1 := by
      rw [finiteSpectralEulerRoot_mul_one_add_smul_diagonal ν t k ht hk hν]
    _ = 1 := map_one _

/-- The literal finite Hermitian Euler root is the positive scalar multiple of the literal
shifted Hermitian resolvent at shift `(m+1)/t`. -/
theorem finiteHermitianEulerRootOperator_eq_smul_shiftedResolvent
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (t : ℝ) (m : ℕ) (ht : 0 < t) :
    finiteHermitianEulerRootOperator A t m =
      (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
        finiteHermitianShiftedResolventOperator A
          (((m + 1 : ℕ) : ℝ) / t) := by
  let k : ℕ := m + 1
  let lam : ℝ := (k : ℝ) / t
  have hk : 0 < k := Nat.succ_pos m
  have hlam : 0 < lam := div_pos (by exact_mod_cast hk) ht
  have hspectral :
      Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
          (Matrix.diagonal (fun i ↦ ((hA.1.eigenvalues i : ℝ) : ℂ))) = A := by
    calc
      _ = Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hA.1.eigenvalues)) := by
        apply congrArg (Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary)
        ext i j
        by_cases hij : i = j
        · subst j
          simp only [Matrix.diagonal_apply, if_pos, Function.comp_apply]
          apply Complex.ext <;> simp [RCLike.ofReal]
        · simp [hij]
      _ = A := hA.1.spectral_theorem.symm
  have hroot :
      ((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ =
        Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
          (finiteSpectralEulerRoot hA.1.eigenvalues t k) := by
    calc
      _ = ((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) •
          Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
            (Matrix.diagonal (fun i ↦ ((hA.1.eigenvalues i : ℝ) : ℂ)))))⁻¹ :=
        congrArg
          (fun B : Matrix ι ι ℂ ↦
            ((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • B))⁻¹)
          hspectral.symm
      _ = _ := (finiteUnitarySpectralEulerRoot_eq_inv_one_add_smul
        hA.1.eigenvectorUnitary hA.1.eigenvalues t k ht.le hk
          hA.eigenvalues_nonneg).symm
  unfold finiteHermitianEulerRootOperator finiteHermitianShiftedResolventOperator
  change Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • A))⁻¹) = _
  rw [hroot,
    finiteSpectralEulerRoot_eq_smul_finiteSpectralResolvent
      hA.1.eigenvalues t k ht hk hA.eigenvalues_nonneg, map_smul, map_smul]
  change ((lam : ℂ) • Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (NCG.SpectralGap.finiteUnitarySpectralResolvent
        hA.1.eigenvectorUnitary hA.1.eigenvalues lam)) = _
  rw [NCG.SpectralGap.finiteUnitarySpectralResolvent_eigenvector_eq_inv_shiftedHermitian
    hA.1 lam hlam hA.eigenvalues_nonneg]

end NCG.ImplicitEuler
