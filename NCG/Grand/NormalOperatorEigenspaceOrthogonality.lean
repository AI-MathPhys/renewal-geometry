/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# Orthogonality of eigenspaces of normal operators

For a normal operator, distinct eigenspaces are orthogonal.  The proof shifts by one eigenvalue:
the shifted operator remains normal, so its kernel is the orthogonal complement of its range; an
eigenvector for a different eigenvalue lies in that range.
-/

open Complex Module End

noncomputable section

namespace NCG.NormalSpectrum

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Subtracting a scalar operator preserves star-normality. -/
theorem sub_smul_one_isStarNormal
    (T : E →L[ℂ] E) (hnormal : IsStarNormal T) (μ : ℂ) :
    IsStarNormal (T - μ • (1 : E →L[ℂ] E)) := by
  rw [isStarNormal_iff, commute_iff_eq]
  simp only [star_sub, star_smul, star_one, mul_sub, sub_mul]
  rw [((isStarNormal_iff T).mp hnormal).eq]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [mul_comm (star μ) μ]
  abel

/-- On an eigenvector of a normal operator, the adjoint acts by the conjugate eigenvalue. -/
theorem adjoint_apply_eigenvector_of_isStarNormal
    (T : E →L[ℂ] E) (hnormal : IsStarNormal T)
    {μ : ℂ} {x : E} (hx : T x = μ • x) :
    ContinuousLinearMap.adjoint T x = star μ • x := by
  let A : E →L[ℂ] E := T - μ • 1
  have hA : IsStarNormal A := by
    simpa [A] using sub_smul_one_isStarNormal T hnormal μ
  have hxker : x ∈ A.ker := by
    change A x = 0
    simp [A, hx]
  have hxadjker : x ∈ (ContinuousLinearMap.adjoint A).ker := by
    rw [ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker hA]
    exact hxker
  change ContinuousLinearMap.adjoint A x = 0 at hxadjker
  have hadjA : ContinuousLinearMap.adjoint A =
      ContinuousLinearMap.adjoint T - star μ • 1 := by
    calc
      ContinuousLinearMap.adjoint A = star A :=
        (ContinuousLinearMap.star_eq_adjoint A).symm
      _ = star T - star μ • star (1 : E →L[ℂ] E) := by simp [A]
      _ = ContinuousLinearMap.adjoint T - star μ • 1 := by
        rw [ContinuousLinearMap.star_eq_adjoint, star_one]
  rw [hadjA] at hxadjker
  exact sub_eq_zero.mp (by simpa using hxadjker)

/-- Every eigenspace of a normal operator has invariant orthogonal complement. -/
theorem invariant_orthogonalComplement_eigenspace_of_isStarNormal
    (T : E →L[ℂ] E) (hnormal : IsStarNormal T) (μ : ℂ) :
    ∀ y : E, y ∈ (eigenspace T.toLinearMap μ)ᗮ →
      T y ∈ (eigenspace T.toLinearMap μ)ᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro x hx
  rw [← T.adjoint_inner_left y x,
    adjoint_apply_eigenvector_of_isStarNormal T hnormal
      (mem_eigenspace_iff.mp hx), inner_smul_left, hy x hx, mul_zero]

/-- Eigenvectors of a normal operator belonging to distinct eigenvalues are orthogonal. -/
theorem inner_eq_zero_of_isStarNormal_of_eigenvectors
    (T : E →L[ℂ] E) (hnormal : IsStarNormal T)
    {μ ν : ℂ} (hμν : μ ≠ ν) {x y : E}
    (hx : T x = μ • x) (hy : T y = ν • y) :
    inner ℂ x y = 0 := by
  let A : E →L[ℂ] E := T - ν • 1
  have hA : IsStarNormal A := by
    rw [isStarNormal_iff, commute_iff_eq]
    dsimp [A]
    simp only [star_sub, star_smul, star_one, mul_sub, sub_mul]
    rw [((isStarNormal_iff T).mp hnormal).eq]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    rw [mul_comm (star ν) ν]
    abel
  have hyker : y ∈ A.ker := by
    change A y = 0
    simp [A, hy]
  have hxrange : x ∈ A.range := by
    have hdiff : μ - ν ≠ 0 := sub_ne_zero.mpr hμν
    refine ⟨(μ - ν)⁻¹ • x, ?_⟩
    change A ((μ - ν)⁻¹ • x) = x
    calc
      A ((μ - ν)⁻¹ • x) =
          (μ - ν)⁻¹ • (T x - ν • x) := by
        simp [A, smul_sub]
      _ = (μ - ν)⁻¹ • ((μ - ν) • x) := by
        rw [hx, sub_smul]
      _ = x := by
        rw [smul_smul, inv_mul_cancel₀ hdiff, one_smul]
  have hyOrth : y ∈ A.rangeᗮ := by
    rw [ContinuousLinearMap.IsStarNormal.orthogonal_range hA]
    exact hyker
  exact (Submodule.mem_orthogonal A.range y).mp hyOrth x hxrange

/-- Distinct eigenspaces of a normal operator are pairwise orthogonal. -/
theorem orthogonal_eigenspaces_of_isStarNormal
    (T : E →L[ℂ] E) (hnormal : IsStarNormal T)
    {μ ν : ℂ} (hμν : μ ≠ ν) :
    ∀ x ∈ eigenspace T.toLinearMap μ,
      ∀ y ∈ eigenspace T.toLinearMap ν, inner ℂ x y = 0 := by
  intro x hx y hy
  exact inner_eq_zero_of_isStarNormal_of_eigenvectors
    T hnormal hμν (mem_eigenspace_iff.mp hx) (mem_eigenspace_iff.mp hy)

end NCG.NormalSpectrum
