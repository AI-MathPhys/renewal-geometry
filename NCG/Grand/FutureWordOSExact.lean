/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GramSqrtPinvExact
import NCG.Grand.NSDynamicTerminalShortExact

/-!
# Future-word OS quotient and returning-memory short

Machinery for `thm:GT-future-word-OS`.  `N : E →L[ℝ] H` is the stacked flat return map with
Gram `G = N†N`, `H_fut ⪰ 0` the reflected returned-cylinder Hamiltonian, `𝔏` the reconstructed
generator, and `Δ = N 𝔏 + H_fut N` the shadow defect (FC.3).  The supported quotient is
`supp G = ran G` and the whitening map is the polar frame `U = N G^{†/2}`.

* On the supported quotient `U† U = I` (`adjoint_U_comp_U`), and `U U† = P_{ran N}`
  (`U_comp_adjoint_U`); the ambient frame satisfies `U† U = P_{supp G}`.
* (FC.4) the whitened generator `G^{1/2} 𝔏 G^{†/2}` satisfies `L_w + U† H_fut U = U† Δ G^{†/2}`
  (`whitenedGen_add`); on the exact branch `Δ = 0` it equals `L_fut = -U† H_fut U = L_fut† ⪯ 0`
  (`whitenedGen_eq`, `isSelfAdjoint_quotGen`, `quotGen_nonpos`), and in ambient form
  `e^{t L_fut} = (I - P_{supp G}) + U† e^{-t H_fut} U` (`exp_genE`), i.e.
  `e^{t L_fut} z = U† e^{-t H_fut} U z` on the quotient (`exp_genE_apply_mem`);
* (FC.5) for a visible head `𝒱` and returned memory `ℳ`, the memory short
  `S_mem = S_MM - C† S_VV† C ⪰ 0` is the Moore–Penrose Schur complement of `-L_fut = Q†Q`
  with `Q = H_fut^{1/2} N G^{†/2}`, its quadratic form is the infimum of
  `⟨(v, m), Q†Q (v, m)⟩` over `v`, attained at the dressed soft source `(-S_VV† C m, m)`, which
  is a null vector of `Q†Q` when the short vanishes (`memory_*`);
* (FC.6) `‖L_w + U† H_fut U‖ ≤ ‖Δ‖ / √λ_min⁺(G)` (`norm_whitenedGen_add_le`,
  `norm_whitenedGenE_add_le`).
-/

open ContinuousLinearMap Submodule Module NCG.MoorePenrose NCG.GramSqrt NCG.NSTerminalShort
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace FutureWordOS

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [CompleteSpace H]

variable (N : E →L[ℝ] H) (Hf : H →L[ℝ] H) (Lg : E →L[ℝ] E)

/-- (FC.3) the shadow defect `Δ_fut = N 𝔏 + H_fut N`. -/
noncomputable def defect : E →L[ℝ] H := N ∘L Lg + Hf ∘L N

/-- The supported quotient `supp G_fut = ran G_fut`. -/
noncomputable abbrev supp : Submodule ℝ E := gramRange N

/-- The whitening isometry `U = N G^{†/2}` on the supported quotient. -/
noncomputable def U : supp N →L[ℝ] H := frame N ∘L (supp N).subtypeL

omit [FiniteDimensional ℝ H] in
theorem U_apply (x : supp N) : U N x = N (sqrtPinv N x) := rfl

omit [FiniteDimensional ℝ H] in
/-- `U† U = I`: `U` is an isometry on the supported quotient. -/
theorem adjoint_U_comp_U : (U N)† ∘L U N = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [U, comp_apply, adjoint_comp, Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
  have h := congrArg (fun T : E →L[ℝ] E => T (x : E)) (adjoint_frame_comp_frame N)
  simp only [comp_apply] at h
  rw [h, starProjection_eq_self_iff.mpr x.2]
  exact (supp N).orthogonalProjectionOnto_mem_subspace_eq_self x

/-- `U U† = P_{ran N}` (ambient frame form). -/
theorem frame_comp_adjoint_frame :
    frame N ∘L (frame N)† = (LinearMap.range N.toLinearMap).starProjection := by
  refine ContinuousLinearMap.ext fun y => ?_
  rw [← comp_gramPinv_comp_adjoint]
  simp only [frame, comp_apply, adjoint_comp, isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv N)]
  have h2 := congrArg (fun T : E →L[ℝ] E => T ((N†) y)) (sqrtPinv_mul_self N)
  simp only [comp_apply] at h2
  rw [h2]

/-- `U U† = P_{ran N}`. -/
theorem U_comp_adjoint_U :
    U N ∘L (U N)† = (LinearMap.range N.toLinearMap).starProjection := by
  rw [← frame_comp_adjoint_frame]
  refine ContinuousLinearMap.ext fun y => ?_
  simp only [U, comp_apply, adjoint_comp, Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
  change frame N ((supp N).starProjection (((frame N)†) y)) = frame N (((frame N)†) y)
  exact congrArg (fun T : E →L[ℝ] H => T (((frame N)†) y)) (frame_comp_starProjection N)

omit [FiniteDimensional ℝ H] in
theorem norm_U_apply (x : supp N) : ‖U N x‖ = ‖x‖ := by
  have h : ‖U N x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← adjoint_inner_right, ← comp_apply, adjoint_U_comp_U,
      one_apply_eq_self, real_inner_self_eq_norm_sq]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

omit [FiniteDimensional ℝ H] in
theorem norm_U_le : ‖U N‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by rw [norm_U_apply, one_mul]

omit [FiniteDimensional ℝ H] in
theorem norm_adjoint_U_le : ‖(U N)†‖ ≤ 1 := by
  rw [(adjoint : (supp N →L[ℝ] H) ≃ₗᵢ⋆[ℝ] (H →L[ℝ] supp N)).norm_map (U N)]
  exact norm_U_le N

omit [FiniteDimensional ℝ H] in
/-- The ambient frame is contractive: `‖N G^{†/2} x‖² = ⟨P_{supp} x, x⟩ ≤ ‖x‖²`. -/
theorem norm_frame_apply_le (x : E) : ‖frame N x‖ ≤ ‖x‖ := by
  have h : ‖frame N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← adjoint_inner_right, ← comp_apply,
      adjoint_frame_comp_frame]
    calc ⟪x, (gramRange N).starProjection x⟫ ≤ ‖x‖ * ‖(gramRange N).starProjection x‖ :=
          real_inner_le_norm _ _
      _ ≤ ‖x‖ * ‖x‖ := by gcongr; exact (gramRange N).norm_starProjection_apply_le x
      _ = ‖x‖ ^ 2 := (pow_two _).symm
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

omit [FiniteDimensional ℝ H] in
theorem norm_frame_le : ‖frame N‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by rw [one_mul]; exact norm_frame_apply_le N x

omit [FiniteDimensional ℝ H] in
theorem norm_adjoint_frame_le : ‖(frame N)†‖ ≤ 1 := by
  rw [(adjoint : (E →L[ℝ] H) ≃ₗᵢ⋆[ℝ] (H →L[ℝ] E)).norm_map (frame N)]
  exact norm_frame_le N

omit [FiniteDimensional ℝ H] in
/-- `P_{ran N} U = U` (ambient frame form). -/
theorem starProjection_comp_frame :
    (LinearMap.range N.toLinearMap).starProjection ∘L frame N = frame N := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, starProjection_eq_self_iff]
  exact ⟨_, rfl⟩

/-! ### Invariance on the exact branch -/

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ H] [CompleteSpace H] in
/-- On the exact branch `Δ = 0`, `ran N` is `H_fut`-invariant. -/
theorem range_invariant (hΔ : defect N Hf Lg = 0) (y : H)
    (hy : y ∈ LinearMap.range N.toLinearMap) : Hf y ∈ LinearMap.range N.toLinearMap := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨-(Lg x), ?_⟩
  have h := congrArg (fun T : E →L[ℝ] H => T x) hΔ
  simp only [defect, add_apply, comp_apply, zero_apply] at h
  change N (-(Lg x)) = Hf (N x)
  rw [map_neg]
  exact neg_eq_of_add_eq_zero_right h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ H] in
/-- A self-adjoint operator commutes with the projection onto an invariant subspace. -/
theorem starProjection_comm {K : Submodule ℝ H} [K.HasOrthogonalProjection]
    (hA : IsSelfAdjoint Hf) (hK : ∀ y ∈ K, Hf y ∈ K) :
    K.starProjection ∘L Hf = Hf ∘L K.starProjection := by
  have hA' : Hf† = Hf := isSelfAdjoint_iff'.mp hA
  refine ContinuousLinearMap.ext fun y => ?_
  simp only [comp_apply]
  refine K.eq_starProjection_of_mem_of_inner_eq_zero (hK _ (K.starProjection_apply_mem y))
    fun w hw => ?_
  rw [← map_sub]
  calc ⟪Hf (y - K.starProjection y), w⟫ = ⟪(Hf†) (y - K.starProjection y), w⟫ := by rw [hA']
    _ = ⟪y - K.starProjection y, Hf w⟫ := adjoint_inner_left _ _ _
    _ = 0 := K.starProjection_inner_eq_zero y (Hf w) (hK w hw)

/-! ### (FC.4): the quotient generator -/

/-- `L_fut = -U† H_fut U` on the supported quotient. -/
noncomputable def quotGen : supp N →L[ℝ] supp N := -((U N)† ∘L Hf ∘L U N)

/-- The ambient representative `-(N G^{†/2})† H_fut (N G^{†/2})` of `L_fut` (it vanishes on
`(supp G)ᗮ` and agrees with `L_fut` on the quotient, `coe_quotGen`). -/
noncomputable def genE : E →L[ℝ] E := -((frame N)† ∘L Hf ∘L frame N)

omit [FiniteDimensional ℝ H] in
theorem coe_quotGen (z : supp N) : ((quotGen N Hf z : supp N) : E) = genE N Hf z := by
  simp only [quotGen, genE, neg_apply, comp_apply, U, frame, adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.subtypeL_apply, Submodule.coe_neg,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv N)]
  congr 1
  change (supp N).starProjection _ = _
  rw [starProjection_eq_self_iff]
  exact sqrtPinv_apply_mem N _

omit [FiniteDimensional ℝ H] in
theorem isSelfAdjoint_quotGen (hA : IsSelfAdjoint Hf) : IsSelfAdjoint (quotGen N Hf) :=
  (hA.adjoint_conj (U N)).neg

omit [FiniteDimensional ℝ H] in
theorem quotGen_nonpos (hH : Hf.IsPositive) (x : supp N) : ⟪quotGen N Hf x, x⟫ ≤ 0 := by
  rw [quotGen, neg_apply, inner_neg_left, neg_nonpos, comp_apply, comp_apply, adjoint_inner_left]
  have := hH.2 (U N x)
  rwa [reApplyInnerSelf_apply, RCLike.re_to_real] at this

omit [FiniteDimensional ℝ H] in
theorem isSelfAdjoint_genE (hA : IsSelfAdjoint Hf) : IsSelfAdjoint (genE N Hf) :=
  (hA.adjoint_conj (frame N)).neg

omit [FiniteDimensional ℝ H] in
theorem genE_nonpos (hH : Hf.IsPositive) (x : E) : ⟪genE N Hf x, x⟫ ≤ 0 := by
  rw [genE, neg_apply, inner_neg_left, neg_nonpos, comp_apply, comp_apply, adjoint_inner_left]
  have := hH.2 (frame N x)
  rwa [reApplyInnerSelf_apply, RCLike.re_to_real] at this

/-- The whitened generator `G^{1/2} 𝔏 G^{†/2}` on the supported quotient. -/
noncomputable def whitenedGen : supp N →L[ℝ] supp N :=
  (supp N).orthogonalProjectionOnto ∘L (sqrtGram N ∘L Lg ∘L sqrtPinv N) ∘L (supp N).subtypeL

/-- The ambient whitened generator `G^{1/2} 𝔏 G^{†/2}`. -/
noncomputable def whitenedGenE : E →L[ℝ] E := sqrtGram N ∘L Lg ∘L sqrtPinv N

omit [FiniteDimensional ℝ H] in
/-- `L_w + U† H_fut U = U† Δ G^{†/2}`. -/
theorem whitenedGen_add :
    whitenedGen N Lg + (U N)† ∘L Hf ∘L U N
      = (U N)† ∘L defect N Hf Lg ∘L (sqrtPinv N ∘L (supp N).subtypeL) := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [whitenedGen, defect, U, frame, add_apply, comp_apply, adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.subtypeL_apply, map_add,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv N)]
  have h := congrArg (fun T : E →L[ℝ] E => T (Lg (sqrtPinv N x))) (sqrtPinv_comp_gram N)
  simp only [comp_apply, gram_apply] at h
  rw [h]

omit [FiniteDimensional ℝ H] in
/-- Ambient form: `L_w + U† H_fut U = U† Δ G^{†/2}`. -/
theorem whitenedGenE_add :
    whitenedGenE N Lg + (frame N)† ∘L Hf ∘L frame N
      = (frame N)† ∘L defect N Hf Lg ∘L sqrtPinv N := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [whitenedGenE, defect, frame, add_apply, comp_apply, adjoint_comp, map_add,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv N)]
  have h := congrArg (fun T : E →L[ℝ] E => T (Lg (sqrtPinv N x))) (sqrtPinv_comp_gram N)
  simp only [comp_apply, gram_apply] at h
  rw [h]

omit [FiniteDimensional ℝ H] in
/-- **(FC.4)**: on the exact branch the whitened generator is `-U† H_fut U`. -/
theorem whitenedGen_eq (hΔ : defect N Hf Lg = 0) : whitenedGen N Lg = quotGen N Hf := by
  have h := whitenedGen_add N Hf Lg
  rw [hΔ, zero_comp, comp_zero] at h
  rw [quotGen]
  exact eq_neg_of_add_eq_zero_left h

omit [FiniteDimensional ℝ H] in
theorem whitenedGenE_eq (hΔ : defect N Hf Lg = 0) : whitenedGenE N Lg = genE N Hf := by
  have h := whitenedGenE_add N Hf Lg
  rw [hΔ, zero_comp, comp_zero] at h
  rw [genE]
  exact eq_neg_of_add_eq_zero_left h

/-- Powers compress: `(U† H U)ⁿ⁺¹ = U† Hⁿ⁺¹ U` when `ran N` is `H`-invariant. -/
theorem pow_compression_frame (hA : IsSelfAdjoint Hf)
    (hinv : ∀ y ∈ LinearMap.range N.toLinearMap, Hf y ∈ LinearMap.range N.toLinearMap)
    (n : ℕ) :
    ((frame N)† ∘L Hf ∘L frame N) ^ (n + 1) = (frame N)† ∘L (Hf ^ (n + 1)) ∘L frame N := by
  induction n with
  | zero => rw [pow_one, pow_one]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ Hf (n + 1)]
    have hP := frame_comp_adjoint_frame N
    have hcomm := starProjection_comm Hf hA hinv
    have hPU := starProjection_comp_frame N
    refine ContinuousLinearMap.ext fun x => ?_
    change (((frame N)† ∘L (Hf ^ (n + 1)) ∘L frame N) ∘L ((frame N)† ∘L Hf ∘L frame N)) x
      = ((frame N)† ∘L ((Hf ^ (n + 1)) ∘L Hf) ∘L frame N) x
    simp only [comp_apply]
    have e1 : frame N (((frame N)†) (Hf (frame N x)))
        = (LinearMap.range N.toLinearMap).starProjection (Hf (frame N x)) :=
      congrArg (fun T : H →L[ℝ] H => T (Hf (frame N x))) hP
    have e2 : (LinearMap.range N.toLinearMap).starProjection (Hf (frame N x))
        = Hf ((LinearMap.range N.toLinearMap).starProjection (frame N x)) :=
      congrArg (fun T : H →L[ℝ] H => T (frame N x)) hcomm
    have e3 : (LinearMap.range N.toLinearMap).starProjection (frame N x) = frame N x :=
      congrArg (fun T : E →L[ℝ] H => T x) hPU
    rw [e1, e2, e3]

/-- The compression map `T ↦ U† T U` as a continuous linear map. -/
noncomputable def compressE : (H →L[ℝ] H) →L[ℝ] (E →L[ℝ] E) :=
  ((compL ℝ E H E).flip (frame N)) ∘L (compL ℝ H H E ((frame N)†))

omit [FiniteDimensional ℝ H] in
theorem compressE_apply (T : H →L[ℝ] H) : compressE N T = (frame N)† ∘L T ∘L frame N := by
  rw [compressE, comp_apply, flip_apply, compL_apply, compL_apply, comp_assoc]

/-- **(FC.4)**: `e^{t L_fut} = (I - P_{supp G}) + U† e^{-t H_fut} U` in ambient form. -/
theorem exp_genE (hA : IsSelfAdjoint Hf)
    (hinv : ∀ y ∈ LinearMap.range N.toLinearMap, Hf y ∈ LinearMap.range N.toLinearMap)
    (t : ℝ) :
    NormedSpace.exp (t • genE N Hf)
      = (1 - (supp N).starProjection)
        + (frame N)† ∘L NormedSpace.exp ((-t) • Hf) ∘L frame N := by
  have hq : t • genE N Hf = (-t) • ((frame N)† ∘L Hf ∘L frame N) := by
    rw [genE, smul_neg, ← neg_smul]
  rw [hq, NormedSpace.exp_eq_tsum ℝ (𝔸 := E →L[ℝ] E), NormedSpace.exp_eq_tsum ℝ (𝔸 := H →L[ℝ] H)]
  simp only
  have hsA : Summable fun n : ℕ =>
      ((n.factorial : ℝ)⁻¹) • ((-t) • ((frame N)† ∘L Hf ∘L frame N)) ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) _
  have hsx : Summable fun n : ℕ => ((n.factorial : ℝ)⁻¹) • ((-t) • Hf) ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) _
  rw [hsA.tsum_eq_zero_add, hsx.tsum_eq_zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero]
  have hterm : ∀ n : ℕ,
      (((n + 1).factorial : ℝ)⁻¹) • ((-t) • ((frame N)† ∘L Hf ∘L frame N)) ^ (n + 1)
        = compressE N ((((n + 1).factorial : ℝ)⁻¹) • ((-t) • Hf) ^ (n + 1)) := by
    intro n
    rw [map_smul, smul_pow, smul_pow, map_smul, compressE_apply,
      pow_compression_frame N Hf hA hinv]
  simp only [hterm]
  have h1 : (frame N)† ∘L (1 : H →L[ℝ] H) ∘L frame N = (frame N)† ∘L frame N := rfl
  rw [← (compressE N).map_tsum ((summable_nat_add_iff 1).mpr hsx), ← compressE_apply,
    map_add, compressE_apply N 1, h1, adjoint_frame_comp_frame]
  abel

/-- **(FC.4)**: on the supported quotient, `e^{t L_fut} z = U† e^{-t H_fut} U z`. -/
theorem exp_genE_apply_mem (hA : IsSelfAdjoint Hf)
    (hinv : ∀ y ∈ LinearMap.range N.toLinearMap, Hf y ∈ LinearMap.range N.toLinearMap)
    (t : ℝ) (z : supp N) :
    NormedSpace.exp (t • genE N Hf) z = ((U N)†) (NormedSpace.exp ((-t) • Hf) (U N z)) := by
  rw [exp_genE N Hf hA hinv t, add_apply, sub_apply, one_apply_eq_self,
    starProjection_eq_self_iff.mpr z.2, sub_self, zero_add]
  simp only [U, comp_apply, adjoint_comp, Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
  change _ = (supp N).starProjection _
  refine (starProjection_eq_self_iff.mpr ?_).symm
  simp only [frame, adjoint_comp, comp_apply, isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv N)]
  exact sqrtPinv_apply_mem N _

/-- **(FC.4)** on the exact branch, in terms of the whitened generator. -/
theorem exp_whitenedGenE (hH : Hf.IsPositive) (hΔ : defect N Hf Lg = 0) (t : ℝ) :
    NormedSpace.exp (t • whitenedGenE N Lg)
      = (1 - (supp N).starProjection)
        + (frame N)† ∘L NormedSpace.exp ((-t) • Hf) ∘L frame N := by
  rw [whitenedGenE_eq N Hf Lg hΔ]
  exact exp_genE N Hf hH.isSelfAdjoint (range_invariant N Hf Lg hΔ) t

/-! ### (FC.5): the returning-memory short -/

variable (hH : Hf.IsPositive)
include hH

/-- `Q = H_fut^{1/2} N G^{†/2}`, the ambient representative of `H_fut^{1/2} U`; `-L_fut` is the
restriction of `Q† Q` to the supported quotient (`coe_neg_quotGen`). -/
noncomputable def Q : E →L[ℝ] H := PositiveSqrt.sqrt Hf hH ∘L N ∘L sqrtPinv N

theorem Q_apply_coe (z : supp N) : Q N Hf hH z = PositiveSqrt.sqrt Hf hH (U N z) := rfl

/-- `-L_fut` is `Q† Q` restricted to the supported quotient. -/
theorem coe_neg_quotGen (z : supp N) :
    (((-quotGen N Hf) z : supp N) : E) = gram (Q N Hf hH) z := by
  rw [neg_apply, Submodule.coe_neg, coe_quotGen, genE, neg_apply, neg_neg]
  simp only [comp_apply, frame, adjoint_comp, gram_apply, Q,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv N),
    isSelfAdjoint_iff'.mp (PositiveSqrt.isSelfAdjoint_sqrt Hf hH)]
  have h1 := congrArg (fun T : H →L[ℝ] H => T (N (sqrtPinv N z)))
    (PositiveSqrt.sqrt_mul_sqrt Hf hH)
  simp only [comp_apply] at h1
  rw [h1]

/-- `⟨-L_fut z, z⟩ = ⟨Q†Q z, z⟩` on the supported quotient. -/
theorem inner_neg_quotGen (z : supp N) :
    ⟪(-quotGen N Hf) z, z⟫ = ⟪gram (Q N Hf hH) z, z⟫ := by
  rw [Submodule.coe_inner, coe_neg_quotGen]

theorem inner_gram_Q (z : E) : ⟪gram (Q N Hf hH) z, z⟫ = ‖Q N Hf hH z‖ ^ 2 := by
  rw [gram_apply, adjoint_inner_left, real_inner_self_eq_norm_sq]

variable (Vh Mh : Submodule ℝ E)

/-- (FC.5) the memory short `S_mem = S_MM - C† S_VV† C` for the visible head `𝒱` and returned
memory `ℳ`. -/
noncomputable def memoryShort : Mh →L[ℝ] Mh := short (Q N Hf hH) Vh Mh

theorem memoryShort_def :
    memoryShort N Hf hH Vh Mh
      = gram (tailMap (Q N Hf hH) Mh)
        - (crossGram (headMap (Q N Hf hH) Vh) (tailMap (Q N Hf hH) Mh))†
          ∘L gramPinv (headMap (Q N Hf hH) Vh)
          ∘L crossGram (headMap (Q N Hf hH) Vh) (tailMap (Q N Hf hH) Mh) := rfl

theorem memoryShort_isPositive : (memoryShort N Hf hH Vh Mh).IsPositive :=
  short_isPositive _ _ _

/-- The memory quadratic form is the squared irreducible residual. -/
theorem memory_quadratic (m : Mh) :
    ⟪memoryShort N Hf hH Vh Mh m, m⟫
      = ‖residual (headMap (Q N Hf hH) Vh) (tailMap (Q N Hf hH) Mh) m‖ ^ 2 := by
  rw [memoryShort, short_eq, real_inner_comm]
  exact inner_innovation _ _ m

theorem head_add_tail (v : Vh) (m : Mh) :
    headMap (Q N Hf hH) Vh v + tailMap (Q N Hf hH) Mh m = Q N Hf hH ((v : E) + m) := by
  rw [map_add]; rfl

/-- **(FC.5)**: `⟨m, S_mem m⟩ = inf_v ⟨(v, m), Q†Q (v, m)⟩`, attained. -/
theorem memory_variational (m : Mh) :
    (∀ v : Vh, ⟪memoryShort N Hf hH Vh Mh m, m⟫
        ≤ ⟪gram (Q N Hf hH) ((v : E) + m), (v : E) + m⟫) ∧
      ∃ v : Vh, ⟪memoryShort N Hf hH Vh Mh m, m⟫
        = ⟪gram (Q N Hf hH) ((v : E) + m), (v : E) + m⟫ := by
  obtain ⟨hle, v₀, hv₀⟩ :=
    innovation_variational (headMap (Q N Hf hH) Vh) (tailMap (Q N Hf hH) Mh) m
  refine ⟨fun v => ?_, v₀, ?_⟩
  · rw [memory_quadratic, inner_gram_Q, ← head_add_tail]
    exact pow_le_pow_left₀ (norm_nonneg _) (hle v) 2
  · rw [memory_quadratic, inner_gram_Q, ← head_add_tail, hv₀]

/-- The dressed soft source `v_m = -S_VV† C m`. -/
noncomputable def dressedSource (m : Mh) : Vh :=
  -(gramPinv (headMap (Q N Hf hH) Vh)
    (crossGram (headMap (Q N Hf hH) Vh) (tailMap (Q N Hf hH) Mh) m))

/-- The dressed soft source realises the residual: `Q_V v_m + Q_M m = (I - P) Q_M m`. -/
theorem head_dressedSource_add (m : Mh) :
    headMap (Q N Hf hH) Vh (dressedSource N Hf hH Vh Mh m) + tailMap (Q N Hf hH) Mh m
      = residual (headMap (Q N Hf hH) Vh) (tailMap (Q N Hf hH) Mh) m := by
  rw [dressedSource, map_neg, residual_apply, crossGram, comp_apply, comp_gramPinv_comp_adjoint]
  abel

/-- The dressed soft source attains the memory action. -/
theorem memory_eq_dressed (m : Mh) :
    ⟪memoryShort N Hf hH Vh Mh m, m⟫
      = ⟪gram (Q N Hf hH) ((dressedSource N Hf hH Vh Mh m : E) + m),
          (dressedSource N Hf hH Vh Mh m : E) + m⟫ := by
  rw [memory_quadratic, inner_gram_Q, ← head_add_tail, head_dressedSource_add]

/-- A null vector of the memory short returns the dressed soft source `(-S_VV† C m, m)` as a
null vector of `Q†Q` (that is, of `-L_fut` on the supported quotient). -/
theorem gram_Q_dressed_eq_zero (m : Mh) (hm : ⟪memoryShort N Hf hH Vh Mh m, m⟫ = 0) :
    gram (Q N Hf hH) ((dressedSource N Hf hH Vh Mh m : E) + m) = 0 := by
  have hQ : Q N Hf hH ((dressedSource N Hf hH Vh Mh m : E) + m) = 0 := by
    rw [← head_add_tail, head_dressedSource_add]
    rw [memory_quadratic] at hm
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hm)
  rw [gram_apply, hQ, map_zero]

/-! ### (FC.6): the approximate shadow branch -/

omit hH [FiniteDimensional ℝ H] in
/-- **(FC.6)**: `‖L_w + U† H_fut U‖ ≤ ‖Δ_fut‖ / √λ_min⁺(G_fut)` on the supported quotient. -/
theorem norm_whitenedGen_add_le {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ i, eigen N i ≠ 0 → lam ≤ eigen N i) :
    ‖whitenedGen N Lg + (U N)† ∘L Hf ∘L U N‖ ≤ ‖defect N Hf Lg‖ / Real.sqrt lam := by
  rw [whitenedGen_add, div_eq_mul_inv]
  calc ‖(U N)† ∘L defect N Hf Lg ∘L (sqrtPinv N ∘L (supp N).subtypeL)‖
      ≤ ‖(U N)†‖ * ‖defect N Hf Lg ∘L (sqrtPinv N ∘L (supp N).subtypeL)‖ := opNorm_comp_le _ _
    _ ≤ 1 * (‖defect N Hf Lg‖ * ((Real.sqrt lam)⁻¹ * 1)) := by
        gcongr
        · exact norm_adjoint_U_le N
        · refine le_trans (opNorm_comp_le _ _) ?_
          gcongr
          refine le_trans (opNorm_comp_le _ _) ?_
          gcongr
          · exact norm_sqrtPinv_le N hlam hmin
          · exact Submodule.norm_subtypeL_le _
    _ = ‖defect N Hf Lg‖ * (Real.sqrt lam)⁻¹ := by ring

omit hH [FiniteDimensional ℝ H] in
/-- **(FC.6)** in ambient form. -/
theorem norm_whitenedGenE_add_le {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ i, eigen N i ≠ 0 → lam ≤ eigen N i) :
    ‖whitenedGenE N Lg + (frame N)† ∘L Hf ∘L frame N‖ ≤ ‖defect N Hf Lg‖ / Real.sqrt lam := by
  rw [whitenedGenE_add, div_eq_mul_inv]
  calc ‖(frame N)† ∘L defect N Hf Lg ∘L sqrtPinv N‖
      ≤ ‖(frame N)†‖ * ‖defect N Hf Lg ∘L sqrtPinv N‖ := opNorm_comp_le _ _
    _ ≤ 1 * (‖defect N Hf Lg‖ * (Real.sqrt lam)⁻¹) := by
        gcongr
        · exact norm_adjoint_frame_le N
        · refine le_trans (opNorm_comp_le _ _) ?_
          gcongr
          exact norm_sqrtPinv_le N hlam hmin
    _ = ‖defect N Hf Lg‖ * (Real.sqrt lam)⁻¹ := by ring

/-- **`thm:GT-future-word-OS`**: `U† U = I` on the supported quotient; (FC.4) on the exact branch
the whitened generator is the self-adjoint nonpositive `L_fut = -U† H_fut U` and
`e^{t L_fut} z = U† e^{-t H_fut} U z` on the quotient; (FC.5) `-L_fut` is the restriction of
`Q†Q`, the memory short is positive, its quadratic form is the attained infimum of
`⟨(v, m), Q†Q (v, m)⟩`, attained at the dressed soft source, which is a null vector when the
short vanishes; (FC.6) the approximate-branch bound. -/
theorem future_word_OS :
    (U N)† ∘L U N = 1 ∧
      (defect N Hf Lg = 0 →
        whitenedGen N Lg = quotGen N Hf ∧ IsSelfAdjoint (quotGen N Hf) ∧
          (∀ x, ⟪quotGen N Hf x, x⟫ ≤ 0) ∧
          whitenedGenE N Lg = genE N Hf ∧
          ∀ (t : ℝ) (z : supp N), NormedSpace.exp (t • whitenedGenE N Lg) z
            = ((U N)†) (NormedSpace.exp ((-t) • Hf) (U N z))) ∧
      (∀ z : supp N, ⟪(-quotGen N Hf) z, z⟫ = ⟪gram (Q N Hf hH) z, z⟫) ∧
      (memoryShort N Hf hH Vh Mh).IsPositive ∧
      (∀ m : Mh, (∀ v : Vh, ⟪memoryShort N Hf hH Vh Mh m, m⟫
          ≤ ⟪gram (Q N Hf hH) ((v : E) + m), (v : E) + m⟫) ∧
        ⟪memoryShort N Hf hH Vh Mh m, m⟫
          = ⟪gram (Q N Hf hH) ((dressedSource N Hf hH Vh Mh m : E) + m),
              (dressedSource N Hf hH Vh Mh m : E) + m⟫ ∧
        (⟪memoryShort N Hf hH Vh Mh m, m⟫ = 0 →
          gram (Q N Hf hH) ((dressedSource N Hf hH Vh Mh m : E) + m) = 0)) ∧
      ∀ lam : ℝ, 0 < lam → (∀ i, eigen N i ≠ 0 → lam ≤ eigen N i) →
        ‖whitenedGen N Lg + (U N)† ∘L Hf ∘L U N‖ ≤ ‖defect N Hf Lg‖ / Real.sqrt lam :=
  ⟨adjoint_U_comp_U N,
    fun hΔ => ⟨whitenedGen_eq N Hf Lg hΔ, isSelfAdjoint_quotGen N Hf hH.isSelfAdjoint,
      quotGen_nonpos N Hf hH, whitenedGenE_eq N Hf Lg hΔ, fun t z => by
        rw [whitenedGenE_eq N Hf Lg hΔ]
        exact exp_genE_apply_mem N Hf hH.isSelfAdjoint (range_invariant N Hf Lg hΔ) t z⟩,
    inner_neg_quotGen N Hf hH, memoryShort_isPositive N Hf hH Vh Mh,
    fun m => ⟨(memory_variational N Hf hH Vh Mh m).1, memory_eq_dressed N Hf hH Vh Mh m,
      gram_Q_dressed_eq_zero N Hf hH Vh Mh m⟩,
    fun _ hlam hmin => norm_whitenedGen_add_le N Hf Lg hlam hmin⟩

end FutureWordOS
end NCG
