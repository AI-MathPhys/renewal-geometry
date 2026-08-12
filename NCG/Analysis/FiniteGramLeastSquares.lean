/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib

/-!
# Finite Gram least-squares projection

An invertible Gram matrix gives the exact normal-equation solution for a
finite family in a real Hilbert space. This file proves the Pythagorean
identity, unique least-squares minimization, the zero-residual criterion, and
the fact that a positive normalized residual lies outside the fitted span.
-/

open Matrix

namespace NCG

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Gram matrix of a finite real-Hilbert family. -/
noncomputable def finiteGramMatrix (v : I → E) : Matrix I I ℝ :=
  fun i j => inner ℝ (v i) (v j)

/-- Right-hand side of the normal equations. -/
noncomputable def finiteGramRhs (v : I → E) (y : E) : I → ℝ :=
  fun i => inner ℝ (v i) y

/-- Coefficients obtained by inverting the Gram matrix. -/
noncomputable def finiteGramCoefficients (v : I → E) (y : E) : I → ℝ :=
  (finiteGramMatrix v)⁻¹ *ᵥ finiteGramRhs v y

/-- The finite Gram projection of `y` onto the span of `v`. -/
noncomputable def finiteGramProjection (v : I → E) (y : E) : E :=
  ∑ i, finiteGramCoefficients v y i • v i

theorem finiteGram_normal_equation (v : I → E) (y : E)
    [Invertible (finiteGramMatrix v)] (i : I) :
    inner ℝ (v i) (y - finiteGramProjection v y) = 0 := by
  have hsolve : finiteGramMatrix v *ᵥ finiteGramCoefficients v y
      = finiteGramRhs v y := by
    rw [finiteGramCoefficients, Matrix.mulVec_mulVec,
      Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hi := congrFun hsolve i
  simp only [Matrix.mulVec, dotProduct, finiteGramMatrix,
    finiteGramRhs] at hi
  rw [finiteGramProjection, inner_sub_right, inner_sum]
  simp only [real_inner_smul_right]
  rw [sub_eq_zero]
  simpa [mul_comm] using hi.symm

theorem finiteGram_residual_orthogonal_span (v : I → E) (y : E)
    [Invertible (finiteGramMatrix v)] :
    y - finiteGramProjection v y ∈
      (Submodule.span ℝ (Set.range v))ᗮ := by
  refine ((Submodule.span ℝ (Set.range v)).mem_orthogonal'
    (y - finiteGramProjection v y)).2 ?_
  intro x hx
  refine Submodule.span_induction (p := fun z _ =>
    inner ℝ (y - finiteGramProjection v y) z = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    rw [real_inner_comm]
    exact finiteGram_normal_equation v y i
  · simp
  · intro a b ha hb
    intro hia hib
    rw [inner_add_right, hia, hib, add_zero]
  · intro c x hx
    intro hix
    rw [real_inner_smul_right, hix, mul_zero]

/-- Exact Pythagorean identity for every competitor in the generated span. -/
theorem finiteGram_pythagoras (v : I → E) (y x : E)
    [Invertible (finiteGramMatrix v)]
    (hx : x ∈ Submodule.span ℝ (Set.range v)) :
    ‖y - x‖ ^ 2 = ‖y - finiteGramProjection v y‖ ^ 2
      + ‖finiteGramProjection v y - x‖ ^ 2 := by
  have hr := finiteGram_residual_orthogonal_span v y
  have hdelta : finiteGramProjection v y - x ∈
      Submodule.span ℝ (Set.range v) := by
    exact Submodule.sub_mem _
      (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hx
  have horth : inner ℝ (y - finiteGramProjection v y)
      (finiteGramProjection v y - x) = 0 := by
    exact ((Submodule.span ℝ (Set.range v)).mem_orthogonal'
      (y - finiteGramProjection v y)).1 hr
      (finiteGramProjection v y - x) hdelta
  rw [show y - x = (y - finiteGramProjection v y)
      + (finiteGramProjection v y - x) by abel]
  simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth

/-- The Gram solution is the unique least-squares minimizer in the generated
span, with equality only at the projection itself. -/
theorem finiteGram_unique_minimizer (v : I → E) (y : E)
    [Invertible (finiteGramMatrix v)] :
    finiteGramProjection v y ∈ Submodule.span ℝ (Set.range v)
      ∧ (∀ x ∈ Submodule.span ℝ (Set.range v),
        ‖y - finiteGramProjection v y‖ ^ 2 ≤ ‖y - x‖ ^ 2)
      ∧ (∀ x ∈ Submodule.span ℝ (Set.range v),
        ‖y - x‖ ^ 2 = ‖y - finiteGramProjection v y‖ ^ 2 →
          x = finiteGramProjection v y) := by
  have hproj : finiteGramProjection v y ∈
      Submodule.span ℝ (Set.range v) := by
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨hproj, ?_, ?_⟩
  · intro x hx
    rw [finiteGram_pythagoras v y x hx]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · intro x hx heq
    have hpyth := finiteGram_pythagoras v y x hx
    have hzero : ‖finiteGramProjection v y - x‖ ^ 2 = 0 := by
      linarith
    have hnorm : ‖finiteGramProjection v y - x‖ = 0 :=
      sq_eq_zero_iff.mp hzero
    have hsub : finiteGramProjection v y - x = 0 := norm_eq_zero.mp hnorm
    exact (sub_eq_zero.mp hsub).symm

/-- The squared least-squares defect vanishes exactly when the datum equals
its Hamiltonian/Gram projection. -/
theorem finiteGram_residual_sq_eq_zero_iff (v : I → E) (y : E) :
    ‖y - finiteGramProjection v y‖ ^ 2 = 0 ↔
      y = finiteGramProjection v y := by
  rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

/-- On the positive branch, the normalized residual is nonzero and lies
outside the fitted span. -/
theorem finiteGram_normalized_residual_not_mem (v : I → E) (y : E)
    [Invertible (finiteGramMatrix v)]
    (hpos : 0 < ‖y - finiteGramProjection v y‖ ^ 2) :
    (Real.sqrt (‖y - finiteGramProjection v y‖ ^ 2))⁻¹ •
        (y - finiteGramProjection v y)
      ∉ Submodule.span ℝ (Set.range v) := by
  intro hmem
  let r := y - finiteGramProjection v y
  change 0 < ‖r‖ ^ 2 at hpos
  change (Real.sqrt (‖r‖ ^ 2))⁻¹ • r ∈
    Submodule.span ℝ (Set.range v) at hmem
  have hrorth := finiteGram_residual_orthogonal_span v y
  change r ∈ (Submodule.span ℝ (Set.range v))ᗮ at hrorth
  have hsqrt : Real.sqrt (‖r‖ ^ 2) ≠ 0 := by positivity
  have hscalar : (Real.sqrt (‖r‖ ^ 2))⁻¹ ≠ 0 := inv_ne_zero hsqrt
  have hrmem : r ∈ Submodule.span ℝ (Set.range v) := by
    exact ((Submodule.span ℝ (Set.range v)).smul_mem_iff hscalar).mp hmem
  have hself : inner ℝ r r = 0 :=
    ((Submodule.span ℝ (Set.range v)).mem_orthogonal' r).1 hrorth r hrmem
  rw [real_inner_self_eq_norm_sq] at hself
  exact (ne_of_gt hpos) hself

end NCG
