/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExteriorSecondQuantizationRankExact
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Independent fine Gaussian factor

Finite Fock-space direct-sum and rank machinery for
`thm:SMQG-fine-factor`.  In an orthonormal exterior basis the full Fock
carrier on `I ⊕ J` is the function space on finite subsets of `I ⊕ J`.
Splitting a subset into its old and fine parts gives the canonical tensor
factorization.  Diagonalizing the two Hermitian covariance blocks then makes
exterior second quantization a product of eigenvalue weights, proving its
tensor multiplicativity.  The existing compound-matrix rank theorem supplies
the exact `2^m` source-minimal rank multiplier.

The last theorem uses the actual determinant of a Hermitian mixed two-by-two
minor.  A nonzero old/fine covariance changes that grade-two coefficient by
`|c|²`, providing the held-out mixed-word witness in the manuscript.
-/

open Matrix

namespace NCG
namespace IndependentFineGaussianFactor

open ExteriorSecondQuantizationRank

/-- Concrete finite exterior-Fock coordinates. -/
abbrev Fock (I : Type*) := Finset I → ℂ

/-- Currying, with the old coordinate first in the pair and the fine
coordinate outermost in the curried function. -/
def pairCurryLinearEquiv (A B : Type*) :
    (A × B → ℂ) ≃ₗ[ℂ] (B → A → ℂ) where
  toFun f b a := f (a, b)
  invFun f p := f p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Finite tensor coordinates are functions on pairs of exterior basis
subsets. -/
noncomputable def tensorFockEquivPair (I J : Type*)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    TensorProduct ℂ (Fock I) (Fock J) ≃ₗ[ℂ]
      (Finset I × Finset J → ℂ) :=
  (TensorProduct.piScalarRight ℂ ℂ (Fock I) (Finset J)) ≪≫ₗ
    (pairCurryLinearEquiv (Finset I) (Finset J)).symm

/-- **QG.75.**  The exterior-Fock carrier of a direct sum is canonically the
tensor product of the two exterior-Fock carriers. -/
noncomputable def fockDirectSumTensorEquiv (I J : Type*)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    Fock (I ⊕ J) ≃ₗ[ℂ] TensorProduct ℂ (Fock I) (Fock J) :=
  LinearEquiv.piCongrLeft ℂ (fun _ : Finset I × Finset J => ℂ)
      Finset.sumEquiv.toEquiv ≪≫ₗ
    (tensorFockEquivPair I J).symm

/-- Eigenvalue of diagonal exterior second quantization on a subset-basis
word. -/
def diagonalGammaWeight {I : Type*} (eig : I → ℂ) (S : Finset I) : ℂ :=
  ∏ i ∈ S, eig i

/-- On an old/fine subset, the second-quantized eigenvalue is the product of
the old and fine eigenvalues.  This is QG.76 in the joint spectral frame. -/
theorem diagonalGammaWeight_disjSum {I J : Type*}
    (eigOld : I → ℂ) (eigFine : J → ℂ) (S : Finset I) (T : Finset J) :
    diagonalGammaWeight (Sum.elim eigOld eigFine) (S.disjSum T) =
      diagonalGammaWeight eigOld S * diagonalGammaWeight eigFine T := by
  simp [diagonalGammaWeight, Finset.prod_disjSum]

/-- Pointwise diagonal second quantization on concrete Fock coordinates. -/
def diagonalGamma {I : Type*} (eig : I → ℂ) (ψ : Fock I) : Fock I :=
  fun S => diagonalGammaWeight eig S * ψ S

/-- QG.76 on pure tensor coordinates: the block-direct-sum exterior action
is the tensor product of the old and fine exterior actions. -/
theorem diagonalGamma_disjSum_pure {I J : Type*}
    (eigOld : I → ℂ) (eigFine : J → ℂ) (ψ : Fock I) (φ : Fock J)
    (S : Finset I) (T : Finset J) :
    diagonalGamma (Sum.elim eigOld eigFine)
        (fun U => ψ U.toLeft * φ U.toRight) (S.disjSum T) =
      diagonalGamma eigOld ψ S * diagonalGamma eigFine φ T := by
  simp [diagonalGamma, diagonalGammaWeight_disjSum]
  ring

/-- Adding a fine one-particle rank `m` multiplies the source-minimal Fock
rank by exactly `2^m`. -/
theorem sourceMinimalRank_mul_two_pow (r m : ℕ) :
    2 ^ (r + m) = 2 ^ r * 2 ^ m := by
  exact pow_add 2 r m

/-- The preceding multiplier applied to the actual ranks of two Hermitian
covariance blocks. -/
theorem sourceMinimalExteriorRank_block_factor
    {d e : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (Q : Matrix (Fin e) (Fin e) ℂ) :
    2 ^ (P.rank + Q.rank) = 2 ^ P.rank * 2 ^ Q.rank :=
  sourceMinimalRank_mul_two_pow P.rank Q.rank

/-- A Hermitian old/fine two-by-two covariance minor. -/
def mixedCovarianceMinor (a b c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a, c; star c, b]

/-- Its grade-two Wick coefficient is the block-factorized coefficient minus
the squared off-diagonal covariance. -/
theorem det_mixedCovarianceMinor (a b c : ℂ) :
    (mixedCovarianceMinor a b c).det = a * b - c * star c := by
  simp [mixedCovarianceMinor, Matrix.det_fin_two]

/-- A nonzero old/fine covariance is detected by the held-out mixed
grade-two word: its actual minor differs from the independent tensor-factor
prediction `a*b`. -/
theorem mixed_gradeTwo_detects_nonzero_offDiagonal
    (a b c : ℂ) (hc : c ≠ 0) :
    (mixedCovarianceMinor a b c).det ≠ a * b := by
  rw [det_mixedCovarianceMinor]
  intro h
  have hz : c * star c = 0 := by
    exact sub_eq_self.mp h
  exact hc (mul_eq_zero.mp hz |>.resolve_right (star_ne_zero.mpr hc))

/-- Every nonzero old/fine covariance block contains a scalar mixed
grade-two witness of the preceding form. -/
theorem exists_mixed_gradeTwo_witness_of_block_ne_zero
    {I J : Type*} [Nonempty I] [Nonempty J]
    (C : Matrix I J ℂ) (hC : C ≠ 0) :
    ∃ i j, C i j ≠ 0 ∧ ∀ a b,
      (mixedCovarianceMinor a b (C i j)).det ≠ a * b := by
  have hex : ∃ i j, C i j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hC
    ext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hex
  exact ⟨i, j, hij, fun a b =>
    mixed_gradeTwo_detects_nonzero_offDiagonal a b (C i j) hij⟩

/-- Consolidated exact certificate for `thm:SMQG-fine-factor`: canonical
Fock factorization, multiplicative exterior weights, exact source-rank growth,
and detection of every nonzero Hermitian old/fine scalar block. -/
theorem independent_fine_Gaussian_factor
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (eigOld : I → ℂ) (eigFine : J → ℂ) (r m : ℕ) :
    Nonempty (Fock (I ⊕ J) ≃ₗ[ℂ] TensorProduct ℂ (Fock I) (Fock J)) ∧
      (∀ S T, diagonalGammaWeight (Sum.elim eigOld eigFine) (S.disjSum T) =
        diagonalGammaWeight eigOld S * diagonalGammaWeight eigFine T) ∧
      2 ^ (r + m) = 2 ^ r * 2 ^ m ∧
      (∀ a b c : ℂ, c ≠ 0 →
        (mixedCovarianceMinor a b c).det ≠ a * b) := by
  exact ⟨⟨fockDirectSumTensorEquiv I J⟩,
    diagonalGammaWeight_disjSum eigOld eigFine,
    sourceMinimalRank_mul_two_pow r m,
    mixed_gradeTwo_detects_nonzero_offDiagonal⟩

end IndependentFineGaussianFactor
end NCG
