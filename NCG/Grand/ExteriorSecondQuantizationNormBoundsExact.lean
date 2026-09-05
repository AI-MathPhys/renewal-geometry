/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExteriorPowerOperatorNormBoundsExact

/-!
# Norm bounds for finite fermionic second quantization

This module realizes the full exterior Fock operator as a genuine
heterogeneous block-diagonal matrix and proves its Euclidean operator-norm
bounds from the corresponding grade estimates.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NCG
namespace ExteriorSecondQuantizationNormBounds

open FiniteCompoundMatrixExteriorPower
open ExteriorPowerOperatorNormBounds

variable {d : ℕ}

/-- The finite exterior Fock carrier, indexed first by grade and then by an
orthonormal wedge-basis element in that grade. -/
abbrev ExteriorFockIdx (d : ℕ) :=
  Σ r : Fin (d + 1), GradeIdx r.1 d

/-- The full finite fermionic second quantization as a genuine block-diagonal
matrix on `⊕_{r=0}^d ⋀^r ℂ^d`. -/
noncomputable def exteriorGamma (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (ExteriorFockIdx d) (ExteriorFockIdx d) ℂ :=
  Matrix.blockDiagonal' (fun r : Fin (d + 1) => cmpd r.1 A)

@[simp]
theorem exteriorGamma_apply_same (A : Matrix (Fin d) (Fin d) ℂ)
    (r : Fin (d + 1)) (S T : GradeIdx r.1 d) :
    exteriorGamma A ⟨r, S⟩ ⟨r, T⟩ = cmpd r.1 A S T := by
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _

@[simp]
theorem exteriorGamma_apply_ne (A : Matrix (Fin d) (Fin d) ℂ)
    {r s : Fin (d + 1)} (S : GradeIdx r.1 d) (T : GradeIdx s.1 d)
    (hrs : r ≠ s) :
    exteriorGamma A ⟨r, S⟩ ⟨s, T⟩ = 0 := by
  exact Matrix.blockDiagonal'_apply_ne _ _ _ hrs

/-- Restriction of a Fock-space vector to one homogeneous grade. -/
noncomputable def gradeVector
    {ι : Type*} [Fintype ι] {m : ι → Type*} [∀ i, Fintype (m i)]
    (x : EuclideanSpace ℂ (Σ i, m i)) (i : ι) : EuclideanSpace ℂ (m i) :=
  WithLp.toLp 2 (fun a => x ⟨i, a⟩)

theorem gradeVector_norm_sq_sum
    {ι : Type*} [Fintype ι] {m : ι → Type*} [∀ i, Fintype (m i)]
    (x : EuclideanSpace ℂ (Σ i, m i)) :
    ∑ i, ‖gradeVector x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, gradeVector]
  simp only [← Finset.univ_sigma_univ, Finset.sum_sigma]

theorem blockDiagonal'_toEuclideanCLM_apply_grade
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (M : ∀ i, Matrix (m i) (m i) ℂ)
    (x : EuclideanSpace ℂ (Σ i, m i)) (i : ι) :
    gradeVector
        (Matrix.toEuclideanCLM (n := Σ i, m i) (𝕜 := ℂ)
          (Matrix.blockDiagonal' M) x) i =
      Matrix.toEuclideanCLM (n := m i) (𝕜 := ℂ) (M i)
        (gradeVector x i) := by
  apply WithLp.ofLp_injective
  funext a
  change
    (∑ z : Σ j, m j,
      Matrix.blockDiagonal' M ⟨i, a⟩ z * x z) =
      ∑ b, M i a b * x ⟨i, b⟩
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp [Matrix.blockDiagonal'_apply']

/-- The Euclidean operator norm of a heterogeneous block diagonal is bounded
by any common upper bound for the norms of its blocks. -/
theorem blockDiagonal'_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (M : ∀ i, Matrix (m i) (m i) ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hM : ∀ i, ‖M i‖ ≤ C) :
    ‖Matrix.blockDiagonal' M‖ ≤ C := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hgrade : ∀ i,
      ‖Matrix.toEuclideanCLM (n := m i) (𝕜 := ℂ) (M i)
        (gradeVector x i)‖ ≤
      C * ‖gradeVector x i‖ := by
    intro i
    calc
      ‖Matrix.toEuclideanCLM (n := m i) (𝕜 := ℂ) (M i)
          (gradeVector x i)‖
          ≤ ‖M i‖ * ‖gradeVector x i‖ :=
        (Matrix.toEuclideanCLM (n := m i) (𝕜 := ℂ) (M i)).le_opNorm _
      _ ≤ C * ‖gradeVector x i‖ :=
        mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _)
  have hsq :
      ‖Matrix.toEuclideanCLM (n := Σ i, m i) (𝕜 := ℂ)
      (Matrix.blockDiagonal' M) x‖ ^ 2 ≤
      (C * ‖x‖) ^ 2 := by
    rw [← gradeVector_norm_sq_sum]
    simp_rw [blockDiagonal'_toEuclideanCLM_apply_grade M x]
    rw [mul_pow, ← gradeVector_norm_sq_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa [mul_pow] using
      (pow_le_pow_left₀ (norm_nonneg _) (hgrade i) 2)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg hC (norm_nonneg _)) two_ne_zero).mp hsq

/-- Every grade exponent up to d is controlled by the larger of the vacuum
bound and the top-grade power. -/
theorem pow_le_max_one_pow_top (a : ℝ) (ha : 0 ≤ a)
    {r d : ℕ} (hrd : r ≤ d) :
    a ^ r ≤ max 1 (a ^ d) := by
  by_cases ha1 : a ≤ 1
  · exact (pow_le_one₀ ha ha1).trans (le_max_left _ _)
  · have h1a : 1 ≤ a := le_of_not_ge ha1
    exact (pow_le_pow_right₀ h1a hrd).trans (le_max_right _ _)

/-- The zeroth compound is the one-dimensional identity. -/
theorem cmpd_zero (A : Matrix (Fin d) (Fin d) ℂ) :
    cmpd 0 A = 1 := by
  ext S T
  have hST : S = T := by
    apply Subtype.ext
    rw [Finset.card_eq_zero.mp S.2, Finset.card_eq_zero.mp T.2]
  subst T
  rw [cmpd_apply, Matrix.one_apply, if_pos rfl]
  exact Matrix.det_isEmpty

/-- The full finite exterior second quantization is bounded by the larger of
the vacuum norm and the top-grade power. -/
theorem exteriorGamma_norm_le_max (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖exteriorGamma A‖ ≤ max 1 (‖A‖ ^ d) := by
  apply blockDiagonal'_norm_le
  · exact le_trans zero_le_one (le_max_left _ _)
  · intro r
    exact (cmpd_norm_le_pow A r.1).trans
      (pow_le_max_one_pow_top ‖A‖ (norm_nonneg A)
        (Nat.le_of_lt_succ r.2))

/-- The preceding maximum is bounded by the convenient polynomial envelope
used in the manuscript. -/
theorem max_one_pow_le_one_add_pow (A : Matrix (Fin d) (Fin d) ℂ) :
    max 1 (‖A‖ ^ d) ≤ (1 + ‖A‖) ^ d := by
  apply max_le
  · exact one_le_pow₀ (by linarith [norm_nonneg A])
  · gcongr
    linarith

/-- Absolute part of lem:SMQG-Gamma-bound. -/
theorem exteriorGamma_norm_bound (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖exteriorGamma A‖ ≤ max 1 (‖A‖ ^ d) ∧
      max 1 (‖A‖ ^ d) ≤ (1 + ‖A‖) ^ d :=
  ⟨exteriorGamma_norm_le_max A, max_one_pow_le_one_add_pow A⟩

/-- The exact finite coefficient sum from grades one through d. -/
def exteriorGammaLipschitzConstant (d : ℕ) (M : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 d, (r : ℝ) * M ^ (r - 1)

theorem exteriorGammaLipschitzConstant_nonneg
    (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ exteriorGammaLipschitzConstant d M := by
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _)

theorem exteriorGamma_sub (A B : Matrix (Fin d) (Fin d) ℂ) :
    exteriorGamma A - exteriorGamma B =
      Matrix.blockDiagonal'
        (fun r : Fin (d + 1) => cmpd r.1 A - cmpd r.1 B) := by
  exact (Matrix.blockDiagonal'_sub
    (fun r : Fin (d + 1) => cmpd r.1 A)
    (fun r : Fin (d + 1) => cmpd r.1 B)).symm

/-- Every homogeneous perturbation block is bounded by the sum of all
non-vacuum grade coefficients. -/
theorem cmpd_sub_norm_le_gamma_constant
    (A B : Matrix (Fin d) (Fin d) ℂ) (r : Fin (d + 1)) :
    ‖cmpd r.1 A - cmpd r.1 B‖ ≤
      exteriorGammaLipschitzConstant d (max ‖A‖ ‖B‖) * ‖A - B‖ := by
  let M := max ‖A‖ ‖B‖
  have hM : 0 ≤ M := le_trans (norm_nonneg A) (le_max_left _ _)
  by_cases hr0 : r.1 = 0
  · have hzero : cmpd r.1 A - cmpd r.1 B = 0 := by
      rw [hr0, cmpd_zero, cmpd_zero, sub_self]
    rw [hzero, norm_zero]
    exact mul_nonneg (exteriorGammaLipschitzConstant_nonneg M hM)
      (norm_nonneg _)
  · have hr1 : 1 ≤ r.1 := Nat.one_le_iff_ne_zero.mpr hr0
    have hrd : r.1 ≤ d := Nat.le_of_lt_succ r.2
    have hterm :
        ((r.1 : ℕ) : ℝ) * M ^ (r.1 - 1) ≤
          exteriorGammaLipschitzConstant d M := by
      have hrmem : r.1 ∈ Finset.Icc 1 d := Finset.mem_Icc.mpr ⟨hr1, hrd⟩
      have hnonneg : ∀ x ∈ Finset.Icc 1 d,
          0 ≤ ((x : ℝ) * M ^ (x - 1)) := by
        intro x _
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _)
      have hsingle := Finset.single_le_sum hnonneg hrmem
      simpa [exteriorGammaLipschitzConstant] using hsingle
    calc
      ‖cmpd r.1 A - cmpd r.1 B‖
          ≤ ((r.1 : ℕ) : ℝ) * M ^ (r.1 - 1) * ‖A - B‖ := by
        simpa [M] using
          exterior_power_perturbation_bound A B r.1
            hr1
      _ ≤ exteriorGammaLipschitzConstant d M * ‖A - B‖ :=
        mul_le_mul_of_nonneg_right hterm (norm_nonneg _)

/-- Perturbative part of lem:SMQG-Gamma-bound. On a norm ball the full
exterior second quantization has the finite coefficient sum from the
manuscript as a Lipschitz constant. -/
theorem exteriorGamma_sub_norm_bound
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    ‖exteriorGamma A - exteriorGamma B‖ ≤
      exteriorGammaLipschitzConstant d (max ‖A‖ ‖B‖) * ‖A - B‖ := by
  rw [exteriorGamma_sub]
  apply blockDiagonal'_norm_le
  · exact mul_nonneg
      (exteriorGammaLipschitzConstant_nonneg _
        (le_trans (norm_nonneg A) (le_max_left _ _)))
      (norm_nonneg _)
  · exact cmpd_sub_norm_le_gamma_constant A B

end ExteriorSecondQuantizationNormBounds
end NCG
