/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Positive square roots on finite-dimensional real Hilbert spaces

For a positive operator `T` on a finite-dimensional real inner product space, the finite spectral
theorem (`LinearMap.IsSymmetric.eigenvectorBasis`) gives the positive square root
`sqrt T = ∑ᵢ √λᵢ ⟪bᵢ, ·⟫ bᵢ` with `sqrt T ∘ sqrt T = T` (`sqrt_mul_sqrt`), self-adjoint and
positive (`isSelfAdjoint_sqrt`, `sqrt_isPositive`), and `‖sqrt T x‖² = ⟪T x, x⟫`
(`norm_sqrt_apply_sq`).  This is the `T^{1/2}` used by the manuscript's whitening and
Hilbert–Schmidt identities (`(I - R*R)^{1/2}`, `H^{†/2}`, `R_w^{†/2}`).
-/

open ContinuousLinearMap Module
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace PositiveSqrt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem inner_sum_smul_basis {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (b : OrthonormalBasis ι ℝ E) (x : E) : ⟪∑ i, c i • b i, x⟫ = ∑ i, c i * ⟪b i, x⟫ := by
  rw [sum_inner]
  simp [inner_smul_left]

omit [FiniteDimensional ℝ E] in
/-- A diagonal operator with entries `≤ c` in an orthonormal basis has quadratic form
`≤ c ‖x‖²`. -/
theorem inner_apply_le_of_basis_eigen {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) (a : ι → ℝ) (hA : ∀ i, A (b i) = a i • b i) {c : ℝ} (hc : ∀ i, a i ≤ c)
    (x : E) : ⟪A x, x⟫ ≤ c * ‖x‖ ^ 2 := by
  have hx : A x = ∑ i, (a i * ⟪b i, x⟫) • b i := by
    conv_lhs => rw [← b.sum_repr' x, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hA, smul_smul, mul_comm]
  rw [hx, sum_inner, ← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner x x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [real_inner_smul_left, real_inner_comm x (b i)]
  nlinarith [mul_nonneg (sub_nonneg.mpr (hc i)) (mul_self_nonneg ⟪x, b i⟫)]

variable (T : E →L[ℝ] E) (hT : T.IsPositive)
include hT

omit [FiniteDimensional ℝ E] in
/-- The positive linear map underlying `T`. -/
theorem isPositive_toLinearMap : (T : E →ₗ[ℝ] E).IsPositive :=
  (isPositive_toLinearMap_iff T).mpr hT

/-- The eigenvector basis of `T`. -/
noncomputable def basis : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  (isPositive_toLinearMap T hT).isSymmetric.eigenvectorBasis rfl

/-- The eigenvalues of `T`. -/
noncomputable def eigen : Fin (finrank ℝ E) → ℝ :=
  (isPositive_toLinearMap T hT).isSymmetric.eigenvalues rfl

theorem eigen_nonneg (i : Fin (finrank ℝ E)) : 0 ≤ eigen T hT i :=
  (isPositive_toLinearMap T hT).nonneg_eigenvalues rfl i

theorem apply_basis (i : Fin (finrank ℝ E)) : T (basis T hT i) = eigen T hT i • basis T hT i := by
  have := (isPositive_toLinearMap T hT).isSymmetric.apply_eigenvectorBasis rfl i
  unfold basis eigen
  exact this

theorem inner_basis (i j : Fin (finrank ℝ E)) :
    ⟪basis T hT i, basis T hT j⟫ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (basis T hT).orthonormal i j

/-- The positive square root `sqrt T = ∑ᵢ √λᵢ ⟪bᵢ, ·⟫ bᵢ`. -/
noncomputable def sqrt : E →L[ℝ] E :=
  ∑ i, Real.sqrt (eigen T hT i) • (innerSL ℝ (basis T hT i)).smulRight (basis T hT i)

theorem sqrt_apply (x : E) :
    sqrt T hT x = ∑ i, Real.sqrt (eigen T hT i) • ⟪basis T hT i, x⟫ • basis T hT i := by
  simp [sqrt, _root_.sum_apply, smulRight_apply, innerSL_apply_apply]

theorem inner_sqrt_apply_basis (x : E) (j : Fin (finrank ℝ E)) :
    ⟪basis T hT j, sqrt T hT x⟫ = Real.sqrt (eigen T hT j) * ⟪basis T hT j, x⟫ := by
  rw [sqrt_apply, inner_sum]
  simp only [inner_smul_right, inner_basis, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j]
  simp

/-- **`sqrt T ∘ sqrt T = T`**. -/
theorem sqrt_mul_sqrt : sqrt T hT ∘L sqrt T hT = T := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, sqrt_apply]
  simp only [inner_sqrt_apply_basis, smul_smul]
  have hlam : ∀ i, Real.sqrt (eigen T hT i) * (Real.sqrt (eigen T hT i) * ⟪basis T hT i, x⟫)
      = ⟪basis T hT i, x⟫ * eigen T hT i := by
    intro i
    rw [← mul_assoc, Real.mul_self_sqrt (eigen_nonneg T hT i), mul_comm]
  simp only [hlam]
  conv_rhs => rw [← (basis T hT).sum_repr' x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, apply_basis, smul_smul]

/-- `sqrt T` is self-adjoint. -/
theorem isSelfAdjoint_sqrt : IsSelfAdjoint (sqrt T hT) := by
  rw [isSelfAdjoint_iff']
  refine ContinuousLinearMap.ext fun y => ?_
  refine ext_inner_right ℝ fun x => ?_
  rw [adjoint_inner_left, sqrt_apply, sqrt_apply, inner_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right, real_inner_comm x,
    show ⟪basis T hT i, y⟫ = ⟪y, basis T hT i⟫ from real_inner_comm _ _]
  simp only [RCLike.conj_to_real]
  ring

/-- `sqrt T` is positive. -/
theorem sqrt_isPositive : (sqrt T hT).IsPositive := by
  refine ⟨(isSelfAdjoint_sqrt T hT).isSymmetric, fun x => ?_⟩
  rw [reApplyInnerSelf_apply, RCLike.re_to_real, sqrt_apply, sum_inner]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [inner_smul_left, inner_smul_left, real_inner_comm]
  simp only [RCLike.conj_to_real]
  have := Real.sqrt_nonneg (eigen T hT i)
  nlinarith [mul_self_nonneg ⟪basis T hT i, x⟫]

/-- **`‖sqrt T x‖² = ⟪T x, x⟫`**. -/
theorem norm_sqrt_apply_sq (x : E) : ‖sqrt T hT x‖ ^ 2 = ⟪T x, x⟫ := by
  rw [← real_inner_self_eq_norm_sq]
  conv_rhs => rw [← sqrt_mul_sqrt T hT, comp_apply]
  rw [← adjoint_inner_left, isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrt T hT)]

/-- `sqrt T` acts as `√c` on every `c`-eigenvector of `T`. -/
theorem sqrt_apply_of_eigen {x : E} {c : ℝ} (hx : T x = c • x) :
    sqrt T hT x = Real.sqrt c • x := by
  rw [sqrt_apply]
  have hcoef : ∀ i, Real.sqrt (eigen T hT i) • ⟪basis T hT i, x⟫ • basis T hT i
      = Real.sqrt c • ⟪basis T hT i, x⟫ • basis T hT i := by
    intro i
    have hsym := (isPositive_toLinearMap T hT).isSymmetric (basis T hT i) x
    change ⟪T (basis T hT i), x⟫ = ⟪basis T hT i, T x⟫ at hsym
    rw [apply_basis, hx, real_inner_smul_left, real_inner_smul_right] at hsym
    by_cases h : ⟪basis T hT i, x⟫ = 0
    · rw [h, zero_smul, smul_zero, smul_zero]
    · rw [mul_right_cancel₀ h hsym]
  simp only [hcoef]
  rw [← Finset.smul_sum, (basis T hT).sum_repr' x]

end PositiveSqrt
end NCG
