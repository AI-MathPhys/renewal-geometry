/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MoorePenroseSchurExact
import NCG.Grand.PositiveSqrtExact

/-!
# Spectral Moore–Penrose half-inverses `H^{†/2}` and polar frames

For `S : E →L[ℝ] F` on finite-dimensional real Hilbert spaces with Gram `H = S† S` and
Moore–Penrose inverse `H†` (`gramPinv`), the positive square root `H^{†/2} = sqrt H†`
(`sqrtPinv`) and `H^{1/2} = sqrt H` (`sqrtGram`) are simultaneously diagonal in the Gram
eigenbasis.  Consequently

* `H^{†/2} H^{1/2} = H^{1/2} H^{†/2} = P_{ran H}` (`sqrtPinv_comp_sqrtGram`);
* `H^{†/2} H H^{†/2} = P_{ran H}` (`sqrtPinv_comp_gram_comp_sqrtPinv`);
* the polar frame `S H^{†/2}` (`frame`) is a partial isometry with initial space `ran H` and
  final space `ran S` (`adjoint_frame_comp_frame`, `range_frame`), realises the polar
  decomposition `S = (S H^{†/2}) H^{1/2}` (`frame_comp_sqrtGram`), and is the unique such factor
  vanishing on `ker S` (`frame_unique`);
* `rank H = rank S` (`finrank_range_gram`).
-/

open ContinuousLinearMap Submodule Module NCG.MoorePenrose NCG.PositiveSqrt
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace GramSqrt

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

variable (S : E →L[ℝ] F)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem gram_isPositive : (gram S).IsPositive := isPositive_adjoint_comp_self S

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem gram_inner_nonneg (y : E) : 0 ≤ ⟪gram S y, y⟫ := by
  have := (gram_isPositive S).2 y
  rwa [reApplyInnerSelf_apply, RCLike.re_to_real] at this

omit [FiniteDimensional ℝ F] in
/-- The Moore–Penrose Gram inverse is positive. -/
theorem gramPinv_isPositive : (gramPinv S).IsPositive := by
  refine ⟨(isSelfAdjoint_gramPinv S).isSymmetric, fun x => ?_⟩
  rw [reApplyInnerSelf_apply, RCLike.re_to_real]
  have h1 : ⟪gramPinv S x, x⟫ = ⟪gramPinv S x, (gramRange S).starProjection x⟫ := by
    have := (gramRange S).starProjection_inner_eq_zero x _ (gramPinv_mem S x)
    rw [inner_sub_left, sub_eq_zero] at this
    rw [real_inner_comm, this, real_inner_comm]
  rw [h1, ← gram_gramPinv S x, real_inner_comm]
  exact gram_inner_nonneg S _

/-! ### The Gram eigenbasis -/

/-- The eigenbasis of the Gram `H = S† S`. -/
noncomputable def basis : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  PositiveSqrt.basis (gram S) (gram_isPositive S)

/-- The Gram eigenvalues. -/
noncomputable def eigen : Fin (finrank ℝ E) → ℝ := PositiveSqrt.eigen (gram S) (gram_isPositive S)

omit [FiniteDimensional ℝ F] in
theorem eigen_nonneg (i : Fin (finrank ℝ E)) : 0 ≤ eigen S i :=
  PositiveSqrt.eigen_nonneg _ _ i

omit [FiniteDimensional ℝ F] in
theorem gram_basis (i : Fin (finrank ℝ E)) : gram S (basis S i) = eigen S i • basis S i :=
  PositiveSqrt.apply_basis _ _ i

/-- The pseudo-inverse eigenvalue `λ⁺ = λ⁻¹` (`0` when `λ = 0`). -/
noncomputable def eigenPinv (i : Fin (finrank ℝ E)) : ℝ :=
  if eigen S i = 0 then 0 else (eigen S i)⁻¹

omit [FiniteDimensional ℝ F] in
theorem eigenPinv_nonneg (i : Fin (finrank ℝ E)) : 0 ≤ eigenPinv S i := by
  unfold eigenPinv
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (eigen_nonneg S i)

omit [FiniteDimensional ℝ F] in
theorem eigenPinv_mul_eigen (i : Fin (finrank ℝ E)) :
    eigenPinv S i * eigen S i = if eigen S i = 0 then 0 else 1 := by
  unfold eigenPinv
  by_cases h : eigen S i = 0
  · simp [h]
  · rw [if_neg h, if_neg h, inv_mul_cancel₀ h]

omit [FiniteDimensional ℝ F] in
theorem sqrt_eigenPinv_mul_sqrt_eigen (i : Fin (finrank ℝ E)) :
    Real.sqrt (eigenPinv S i) * Real.sqrt (eigen S i) = if eigen S i = 0 then 0 else 1 := by
  unfold eigenPinv
  by_cases h : eigen S i = 0
  · simp [h]
  · rw [if_neg h, if_neg h, Real.sqrt_inv, inv_mul_cancel₀]
    exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (eigen_nonneg S i) (Ne.symm h))

omit [FiniteDimensional ℝ F] in
/-- `P_{ran H}` acts on the eigenbasis as the indicator of nonzero eigenvalues. -/
theorem starProjection_basis (i : Fin (finrank ℝ E)) :
    (gramRange S).starProjection (basis S i)
      = (if eigen S i = 0 then 0 else 1 : ℝ) • basis S i := by
  by_cases h : eigen S i = 0
  · rw [if_pos h, zero_smul, starProjection_apply_eq_zero_iff, gramRange_orthogonal_ker]
    have : basis S i ∈ (gram S).ker := by
      rw [LinearMap.mem_ker]
      change gram S (basis S i) = 0
      rw [gram_basis, h, zero_smul]
    rw [ker_gram] at this
    exact this
  · rw [if_neg h, one_smul, starProjection_eq_self_iff]
    refine ⟨(eigen S i)⁻¹ • basis S i, ?_⟩
    change gram S ((eigen S i)⁻¹ • basis S i) = basis S i
    rw [map_smul, gram_basis, smul_smul, inv_mul_cancel₀ h, one_smul]

omit [FiniteDimensional ℝ F] in
/-- `H†` acts on the eigenbasis by the pseudo-inverse eigenvalues. -/
theorem gramPinv_basis (i : Fin (finrank ℝ E)) :
    gramPinv S (basis S i) = eigenPinv S i • basis S i := by
  unfold eigenPinv
  by_cases h : eigen S i = 0
  · rw [if_pos h, zero_smul, ← gramPinv_apply_starProjection, starProjection_basis, if_pos h,
      zero_smul, map_zero]
  · rw [if_neg h]
    have hb : gram S ((eigen S i)⁻¹ • basis S i) = basis S i := by
      rw [map_smul, gram_basis, smul_smul, inv_mul_cancel₀ h, one_smul]
    conv_lhs => rw [← hb]
    rw [gramPinv_gram, map_smul, starProjection_basis, if_neg h, one_smul]

omit [FiniteDimensional ℝ F] in
/-- Two operators agreeing on the Gram eigenbasis are equal. -/
theorem ext_basis {A B : E →L[ℝ] E} (h : ∀ i, A (basis S i) = B (basis S i)) : A = B := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [← (basis S).sum_repr' x, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h i]

/-! ### `H^{1/2}` and `H^{†/2}` -/

/-- `H^{1/2} = sqrt (S† S)`. -/
noncomputable def sqrtGram : E →L[ℝ] E := sqrt (gram S) (gram_isPositive S)

/-- `H^{†/2} = sqrt H†`. -/
noncomputable def sqrtPinv : E →L[ℝ] E := sqrt (gramPinv S) (gramPinv_isPositive S)

omit [FiniteDimensional ℝ F] in
theorem sqrtGram_basis (i : Fin (finrank ℝ E)) :
    sqrtGram S (basis S i) = Real.sqrt (eigen S i) • basis S i :=
  sqrt_apply_of_eigen _ _ (gram_basis S i)

omit [FiniteDimensional ℝ F] in
theorem sqrtPinv_basis (i : Fin (finrank ℝ E)) :
    sqrtPinv S (basis S i) = Real.sqrt (eigenPinv S i) • basis S i :=
  sqrt_apply_of_eigen _ _ (gramPinv_basis S i)

omit [FiniteDimensional ℝ F] in
theorem sqrtGram_mul_self : sqrtGram S ∘L sqrtGram S = gram S := sqrt_mul_sqrt _ _

omit [FiniteDimensional ℝ F] in
theorem sqrtPinv_mul_self : sqrtPinv S ∘L sqrtPinv S = gramPinv S := sqrt_mul_sqrt _ _

omit [FiniteDimensional ℝ F] in
theorem isSelfAdjoint_sqrtGram : IsSelfAdjoint (sqrtGram S) := isSelfAdjoint_sqrt _ _

omit [FiniteDimensional ℝ F] in
theorem isSelfAdjoint_sqrtPinv : IsSelfAdjoint (sqrtPinv S) := isSelfAdjoint_sqrt _ _

omit [FiniteDimensional ℝ F] in
theorem sqrtGram_isPositive : (sqrtGram S).IsPositive := sqrt_isPositive _ _

omit [FiniteDimensional ℝ F] in
theorem sqrtPinv_isPositive : (sqrtPinv S).IsPositive := sqrt_isPositive _ _

omit [FiniteDimensional ℝ F] in
/-- `H^{†/2} H^{1/2} = P_{ran H}`. -/
theorem sqrtPinv_comp_sqrtGram :
    sqrtPinv S ∘L sqrtGram S = (gramRange S).starProjection := by
  refine ext_basis S fun i => ?_
  rw [comp_apply, sqrtGram_basis, map_smul, sqrtPinv_basis, smul_smul, mul_comm,
    sqrt_eigenPinv_mul_sqrt_eigen, starProjection_basis]

omit [FiniteDimensional ℝ F] in
/-- `H^{1/2} H^{†/2} = P_{ran H}`. -/
theorem sqrtGram_comp_sqrtPinv :
    sqrtGram S ∘L sqrtPinv S = (gramRange S).starProjection := by
  refine ext_basis S fun i => ?_
  rw [comp_apply, sqrtPinv_basis, map_smul, sqrtGram_basis, smul_smul,
    sqrt_eigenPinv_mul_sqrt_eigen, starProjection_basis]

omit [FiniteDimensional ℝ F] in
/-- `H^{†/2} H H^{†/2} = P_{ran H}`. -/
theorem sqrtPinv_comp_gram_comp_sqrtPinv :
    sqrtPinv S ∘L gram S ∘L sqrtPinv S = (gramRange S).starProjection := by
  refine ext_basis S fun i => ?_
  rw [comp_apply, comp_apply, sqrtPinv_basis, map_smul, gram_basis, map_smul, map_smul,
    sqrtPinv_basis, smul_smul, smul_smul, starProjection_basis]
  congr 1
  have : Real.sqrt (eigenPinv S i) * eigen S i * Real.sqrt (eigenPinv S i)
      = Real.sqrt (eigenPinv S i) * Real.sqrt (eigenPinv S i) * eigen S i := by ring
  rw [this, Real.mul_self_sqrt (eigenPinv_nonneg S i), eigenPinv_mul_eigen]

omit [FiniteDimensional ℝ F] in
/-- `P_{ran H} H^{†/2} = H^{†/2}`: `H^{†/2}` maps into the support. -/
theorem starProjection_comp_sqrtPinv :
    (gramRange S).starProjection ∘L sqrtPinv S = sqrtPinv S := by
  refine ext_basis S fun i => ?_
  rw [comp_apply, sqrtPinv_basis, map_smul, starProjection_basis, smul_smul]
  congr 1
  unfold eigenPinv
  by_cases h : eigen S i = 0
  · simp [h]
  · simp [h]

omit [FiniteDimensional ℝ F] in
theorem sqrtPinv_apply_mem (x : E) : sqrtPinv S x ∈ gramRange S := by
  rw [← starProjection_eq_self_iff]
  exact congrArg (fun T : E →L[ℝ] E => T x) (starProjection_comp_sqrtPinv S)

omit [FiniteDimensional ℝ F] in
/-- `H^{†/2} H = H^{1/2}`. -/
theorem sqrtPinv_comp_gram : sqrtPinv S ∘L gram S = sqrtGram S := by
  refine ext_basis S fun i => ?_
  rw [comp_apply, gram_basis, map_smul, sqrtPinv_basis, sqrtGram_basis, smul_smul]
  congr 1
  unfold eigenPinv
  by_cases h : eigen S i = 0
  · simp [h]
  · rw [if_neg h, Real.sqrt_inv]
    have h0 : Real.sqrt (eigen S i) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (eigen_nonneg S i) (Ne.symm h))
    calc eigen S i * (Real.sqrt (eigen S i))⁻¹
        = Real.sqrt (eigen S i) * Real.sqrt (eigen S i) * (Real.sqrt (eigen S i))⁻¹ := by
          rw [Real.mul_self_sqrt (eigen_nonneg S i)]
      _ = Real.sqrt (eigen S i) := mul_inv_cancel_right₀ h0 _

omit [FiniteDimensional ℝ F] in
/-- `⟨H† x, x⟩ ≤ ‖x‖² / λ` when every nonzero Gram eigenvalue is `≥ λ`. -/
theorem inner_gramPinv_le {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ i, eigen S i ≠ 0 → lam ≤ eigen S i) (x : E) :
    ⟪gramPinv S x, x⟫ ≤ lam⁻¹ * ‖x‖ ^ 2 := by
  refine inner_apply_le_of_basis_eigen (basis S) (gramPinv S) (eigenPinv S) (gramPinv_basis S)
    (fun i => ?_) x
  unfold eigenPinv
  by_cases h : eigen S i = 0
  · rw [if_pos h]; exact inv_nonneg.mpr hlam.le
  · rw [if_neg h]; exact inv_anti₀ hlam (hmin i h)

omit [FiniteDimensional ℝ F] in
/-- `‖H^{†/2} x‖ ≤ ‖x‖ / √λ` when every nonzero Gram eigenvalue is `≥ λ`. -/
theorem norm_sqrtPinv_apply_le {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ i, eigen S i ≠ 0 → lam ≤ eigen S i) (x : E) :
    ‖sqrtPinv S x‖ ≤ (Real.sqrt lam)⁻¹ * ‖x‖ := by
  have h1 : ‖sqrtPinv S x‖ ^ 2 ≤ lam⁻¹ * ‖x‖ ^ 2 := by
    rw [sqrtPinv, norm_sqrt_apply_sq]
    exact inner_gramPinv_le S hlam hmin x
  have h2 : ((Real.sqrt lam)⁻¹ * ‖x‖) ^ 2 = lam⁻¹ * ‖x‖ ^ 2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hlam.le]
  rw [← h2] at h1
  exact pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (norm_nonneg _)) two_ne_zero |>.mp h1

omit [FiniteDimensional ℝ F] in
/-- `‖H^{†/2}‖ ≤ 1 / √λ_min⁺`. -/
theorem norm_sqrtPinv_le {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ i, eigen S i ≠ 0 → lam ≤ eigen S i) :
    ‖sqrtPinv S‖ ≤ (Real.sqrt lam)⁻¹ :=
  opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _)) (norm_sqrtPinv_apply_le S hlam hmin)

omit [FiniteDimensional ℝ F] in
/-- `H^{†/2} P_{ran H} = H^{†/2}`. -/
theorem sqrtPinv_comp_starProjection :
    sqrtPinv S ∘L (gramRange S).starProjection = sqrtPinv S := by
  refine ext_basis S fun i => ?_
  rw [comp_apply, starProjection_basis, map_smul, sqrtPinv_basis, smul_smul]
  congr 1
  unfold eigenPinv
  by_cases h : eigen S i = 0
  · simp [h]
  · simp [h]

omit [FiniteDimensional ℝ F] in
/-- `S P_{ran H} = S`: `S` vanishes on `ker S = (ran H)ᗮ`. -/
theorem comp_starProjection_gramRange : S ∘L (gramRange S).starProjection = S := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply]
  have hk : x - (gramRange S).starProjection x ∈ S.ker := by
    rw [← gramRange_orthogonal_ker]
    exact (gramRange S).sub_starProjection_mem_orthogonal x
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hk
  exact hk.symm

/-! ### The polar frame `S H^{†/2}` -/

/-- The polar frame `S H^{†/2}`: the partial-isometry factor of `S = (S H^{†/2}) H^{1/2}`. -/
noncomputable def frame : E →L[ℝ] F := S ∘L sqrtPinv S

omit [FiniteDimensional ℝ F] in
/-- `(S H^{†/2})† (S H^{†/2}) = P_{ran H}`: the polar frame is a partial isometry with initial
space `ran H = (ker S)ᗮ`. -/
theorem adjoint_frame_comp_frame : (frame S)† ∘L frame S = (gramRange S).starProjection := by
  rw [← sqrtPinv_comp_gram_comp_sqrtPinv]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [frame, comp_apply, adjoint_comp, gram_apply,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv S)]

omit [FiniteDimensional ℝ F] in
/-- Polar decomposition `S = (S H^{†/2}) H^{1/2}`. -/
theorem frame_comp_sqrtGram : frame S ∘L sqrtGram S = S := by
  rw [frame, comp_assoc, sqrtPinv_comp_sqrtGram, comp_starProjection_gramRange]

omit [FiniteDimensional ℝ F] in
theorem frame_comp_starProjection : frame S ∘L (gramRange S).starProjection = frame S := by
  rw [frame, comp_assoc, sqrtPinv_comp_starProjection]

omit [FiniteDimensional ℝ F] in
/-- The polar frame has final space `ran S`. -/
theorem range_frame : LinearMap.range (frame S).toLinearMap = LinearMap.range S.toLinearMap := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨sqrtPinv S x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨sqrtGram S x, ?_⟩
    change (frame S ∘L sqrtGram S) x = S x
    rw [frame_comp_sqrtGram]

omit [FiniteDimensional ℝ F] in
/-- Uniqueness of the polar frame: any `U` with `U H^{1/2} = S` vanishing on `(ran H)ᗮ = ker S`
equals `S H^{†/2}`. -/
theorem frame_unique {U : E →L[ℝ] F} (hU : U ∘L sqrtGram S = S)
    (hP : U ∘L (gramRange S).starProjection = U) : U = frame S :=
  calc U = U ∘L (gramRange S).starProjection := hP.symm
    _ = U ∘L (sqrtGram S ∘L sqrtPinv S) := by rw [sqrtGram_comp_sqrtPinv]
    _ = (U ∘L sqrtGram S) ∘L sqrtPinv S := by rw [comp_assoc]
    _ = frame S := by rw [hU, frame]

/-! ### Rank -/

omit [FiniteDimensional ℝ F] in
/-- `rank (S† S) = rank S`. -/
theorem finrank_range_gram :
    finrank ℝ (LinearMap.range (gram S).toLinearMap)
      = finrank ℝ (LinearMap.range S.toLinearMap) := by
  rw [range_gram]
  have h1 := Submodule.finrank_add_finrank_orthogonal S.ker
  have h2 := LinearMap.finrank_range_add_finrank_ker (S : E →ₗ[ℝ] F)
  omega

end GramSqrt
end NCG
