/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Moore–Penrose Schur innovations

Reusable machinery for the Gram-based "Moore–Penrose Schur complement" used throughout the
manuscript (`thm:GT-source-terminal-nonduplication`, `thm:NS-dynamic-terminal-short`,
`thm:GT-word-localizer-extension`, `thm:GT-future-word-OS`, `thm:SM-command-quotient-hessian`).

For a finite-dimensional real Hilbert space and `S : E →L[ℝ] F` with Gram `G = S† S`:

* `gramPinv S` is the Moore–Penrose pseudoinverse `G†` of the Gram (inverse on `ran G = (ker S)ᗮ`,
  zero on `ker G`), satisfying the four Penrose conditions (`isMoorePenrose_gramPinv`);
* `comp_gramPinv_comp_adjoint`: `S G† S† = P_{ran S}`, the orthogonal projection onto the range;
* `schur_innovation`: for a second map `T : E' →L[ℝ] F`, with `B = S† T` and `D = T† T`,
  `D - B† G† B = T† (I - P_{ran S}) T` — the Moore–Penrose Schur complement is the Gram of the
  orthogonal residual `(I - P_{ran S}) T`;
* `innovation_variational`: `⟨y, (D - B† G† B) y⟩ = ‖(I - P) T y‖² = min_x ‖S x + T y‖²`.
-/

open ContinuousLinearMap Submodule
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace MoorePenrose

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The four Penrose conditions. -/
structure IsMoorePenrose (A : E →L[ℝ] E) (A' : E →L[ℝ] E) : Prop where
  aa'a : A ∘L A' ∘L A = A
  a'aa' : A' ∘L A ∘L A' = A'
  sa_aa' : IsSelfAdjoint (A ∘L A')
  sa_a'a : IsSelfAdjoint (A' ∘L A)

section Gram

variable (S : E →L[ℝ] F)

/-- The Gram `G = S† S`. -/
noncomputable def gram : E →L[ℝ] E := S† ∘L S

omit [FiniteDimensional ℝ E] in
theorem gram_apply (x : E) : gram S x = (S†) (S x) := rfl

omit [FiniteDimensional ℝ E] in
theorem isSelfAdjoint_gram : IsSelfAdjoint (gram S) := by
  rw [isSelfAdjoint_iff', gram, adjoint_comp, adjoint_adjoint]

omit [FiniteDimensional ℝ E] in
theorem gram_isSymmetric : (gram S : E →ₗ[ℝ] E).IsSymmetric :=
  (isSelfAdjoint_gram S).isSymmetric

omit [FiniteDimensional ℝ E] in
theorem ker_gram : (gram S).ker = S.ker := ker_adjoint_comp_self S

/-- The range of the Gram is the orthogonal complement of the kernel of `S`. -/
theorem range_gram : LinearMap.range (gram S).toLinearMap = S.kerᗮ := by
  have h := (gram_isSymmetric S).orthogonal_range
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range (gram S).toLinearMap), h]
  congr 1
  exact ker_gram S

/-- `ran G` as a submodule of `E`. -/
noncomputable def gramRange : Submodule ℝ E := LinearMap.range (gram S).toLinearMap

omit [FiniteDimensional ℝ E] in
theorem mem_gramRange_of_gram (x : E) : gram S x ∈ gramRange S := ⟨x, rfl⟩

theorem gramRange_orthogonal_ker : (gramRange S)ᗮ = S.ker := by
  rw [gramRange, range_gram, Submodule.orthogonal_orthogonal]

omit [FiniteDimensional ℝ E] in
/-- `G` maps `ran G` into itself. -/
theorem gram_mem_gramRange {x : E} (_hx : x ∈ gramRange S) : gram S x ∈ gramRange S :=
  ⟨x, rfl⟩

/-- `G` is injective on `ran G`. -/
theorem gram_injOn : Set.InjOn (gram S) (gramRange S) := by
  intro x hx y hy hxy
  have h1 : x - y ∈ (gram S).ker := by
    rw [LinearMap.mem_ker]
    change gram S (x - y) = 0
    rw [map_sub, hxy, sub_self]
  rw [ker_gram, ← gramRange_orthogonal_ker] at h1
  have h2 : x - y ∈ gramRange S := (gramRange S).sub_mem hx hy
  have h3 : x - y ∈ gramRange S ⊓ (gramRange S)ᗮ := ⟨h2, h1⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h3
  exact sub_eq_zero.mp h3

/-- `G` restricted to `ran G` is surjective onto `ran G`. -/
theorem gram_surjOn : ∀ y ∈ gramRange S, ∃ x ∈ gramRange S, gram S x = y := by
  rintro _ ⟨z, rfl⟩
  refine ⟨(gramRange S).starProjection z, (gramRange S).starProjection_apply_mem z, ?_⟩
  have hk : z - (gramRange S).starProjection z ∈ S.ker := by
    rw [← gramRange_orthogonal_ker]
    exact (gramRange S).sub_starProjection_mem_orthogonal z
  have : gram S (z - (gramRange S).starProjection z) = 0 := by
    rw [gram_apply S]
    rw [LinearMap.mem_ker] at hk
    have hk' : S (z - (gramRange S).starProjection z) = 0 := hk
    rw [hk', map_zero]
  rw [map_sub, sub_eq_zero] at this
  exact this.symm

/-- The restriction of `G` to `ran G` as a linear equivalence. -/
noncomputable def gramEquiv : gramRange S ≃ₗ[ℝ] gramRange S :=
  LinearEquiv.ofBijective
    ((gram S : E →ₗ[ℝ] E).restrict fun x hx => gram_mem_gramRange S hx)
    ⟨fun x y hxy => Subtype.ext (gram_injOn S x.2 y.2 (congrArg Subtype.val hxy)),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := gram_surjOn S y y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem gramEquiv_apply (x : gramRange S) : (gramEquiv S x : E) = gram S x := rfl

/-- The Moore–Penrose pseudoinverse of the Gram: inverse on `ran G`, zero on `ker G`. -/
noncomputable def gramPinv : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    ((gramRange S).subtype ∘ₗ (gramEquiv S).symm.toLinearMap ∘ₗ
      ((gramRange S).orthogonalProjectionOnto : E →ₗ[ℝ] gramRange S))

theorem gramPinv_apply (x : E) :
    gramPinv S x = ((gramEquiv S).symm ((gramRange S).orthogonalProjectionOnto x) : E) := rfl

theorem gramPinv_mem (x : E) : gramPinv S x ∈ gramRange S := by
  rw [gramPinv_apply]
  exact Subtype.mem _

/-- `G G† = P_{ran G}`. -/
theorem gram_gramPinv (x : E) : gram S (gramPinv S x) = (gramRange S).starProjection x := by
  rw [gramPinv_apply, ← gramEquiv_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- `G† G = P_{ran G}`. -/
theorem gramPinv_gram (x : E) : gramPinv S (gram S x) = (gramRange S).starProjection x := by
  -- `G x = G (P x)` since `x - P x ∈ ker G`
  have hk : x - (gramRange S).starProjection x ∈ (gram S).ker := by
    rw [ker_gram, ← gramRange_orthogonal_ker]
    exact (gramRange S).sub_starProjection_mem_orthogonal x
  have hGx : gram S x = gram S ((gramRange S).starProjection x) := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hk
    exact hk
  rw [hGx, gramPinv_apply]
  have hmem : gram S ((gramRange S).starProjection x) ∈ gramRange S := ⟨_, rfl⟩
  have h1 : (gramRange S).orthogonalProjectionOnto (gram S ((gramRange S).starProjection x))
      = ⟨_, hmem⟩ := by
    apply Subtype.ext
    change (gramRange S).starProjection _ = _
    exact (gramRange S).starProjection_eq_self_iff.mpr hmem
  rw [h1]
  have h2 : (⟨gram S ((gramRange S).starProjection x), hmem⟩ : gramRange S)
      = gramEquiv S ⟨(gramRange S).starProjection x, (gramRange S).starProjection_apply_mem x⟩ :=
    Subtype.ext rfl
  rw [h2, LinearEquiv.symm_apply_apply]

/-- `G†` kills `ker G`. -/
theorem gramPinv_apply_starProjection (x : E) :
    gramPinv S ((gramRange S).starProjection x) = gramPinv S x := by
  rw [gramPinv_apply, gramPinv_apply]
  congr 2
  apply Subtype.ext
  change (gramRange S).starProjection ((gramRange S).starProjection x)
    = (gramRange S).starProjection x
  exact (gramRange S).starProjection_eq_self_iff.mpr ((gramRange S).starProjection_apply_mem x)

/-- `G†` is self-adjoint. -/
theorem isSelfAdjoint_gramPinv : IsSelfAdjoint (gramPinv S) := by
  rw [isSelfAdjoint_iff']
  refine ContinuousLinearMap.ext fun y => ?_
  refine ext_inner_right ℝ fun x => ?_
  rw [adjoint_inner_left]
  have h1 : ⟪gramPinv S x, y⟫ = ⟪gramPinv S x, (gramRange S).starProjection y⟫ := by
    have horth := (gramRange S).sub_starProjection_mem_orthogonal y
    have := (Submodule.mem_orthogonal _ _).mp horth _ (gramPinv_mem S x)
    rw [inner_sub_right] at this
    linarith
  have h2 : ⟪gramPinv S y, x⟫ = ⟪gramPinv S y, (gramRange S).starProjection x⟫ := by
    have horth := (gramRange S).sub_starProjection_mem_orthogonal x
    have := (Submodule.mem_orthogonal _ _).mp horth _ (gramPinv_mem S y)
    rw [inner_sub_right] at this
    linarith
  calc ⟪y, gramPinv S x⟫ = ⟪gramPinv S x, y⟫ := real_inner_comm _ _
    _ = ⟪gramPinv S x, (gramRange S).starProjection y⟫ := h1
    _ = ⟪gramPinv S x, gram S (gramPinv S y)⟫ := by rw [gram_gramPinv]
    _ = ⟪gram S (gramPinv S x), gramPinv S y⟫ := ((gram_isSymmetric S) _ _).symm
    _ = ⟪(gramRange S).starProjection x, gramPinv S y⟫ := by rw [gram_gramPinv]
    _ = ⟪gramPinv S y, (gramRange S).starProjection x⟫ := real_inner_comm _ _
    _ = ⟪gramPinv S y, x⟫ := h2.symm

/-- **The Penrose conditions** for `G†`. -/
theorem isMoorePenrose_gramPinv : IsMoorePenrose (gram S) (gramPinv S) := by
  have hP : IsSelfAdjoint ((gramRange S).starProjection) := isSelfAdjoint_starProjection _
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun x => ?_
    simp only [comp_apply]
    rw [gramPinv_gram]
    -- G (P x) = G x
    have hk : x - (gramRange S).starProjection x ∈ (gram S).ker := by
      rw [ker_gram, ← gramRange_orthogonal_ker]
      exact (gramRange S).sub_starProjection_mem_orthogonal x
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hk
    exact hk.symm
  · refine ContinuousLinearMap.ext fun x => ?_
    simp only [comp_apply]
    rw [gram_gramPinv, gramPinv_apply_starProjection]
  · have : gram S ∘L gramPinv S = (gramRange S).starProjection :=
      ContinuousLinearMap.ext fun x => gram_gramPinv S x
    rw [this]
    exact hP
  · have : gramPinv S ∘L gram S = (gramRange S).starProjection :=
      ContinuousLinearMap.ext fun x => gramPinv_gram S x
    rw [this]
    exact hP

/-- `ran S†` lies in `ran G = (ker S)ᗮ`. -/
theorem adjoint_apply_mem_gramRange (y : F) : (S†) y ∈ gramRange S := by
  rw [gramRange, range_gram, Submodule.mem_orthogonal]
  intro k hk
  rw [LinearMap.mem_ker] at hk
  have hk' : S k = 0 := hk
  rw [real_inner_comm, adjoint_inner_left, hk', inner_zero_right]

/-- **`S G† S† = P_{ran S}`**: the Moore–Penrose Gram inverse reconstructs the orthogonal
projection onto the range of `S`. -/
theorem comp_gramPinv_comp_adjoint [FiniteDimensional ℝ F] (y : F) :
    S (gramPinv S ((S†) y)) = (LinearMap.range S.toLinearMap).starProjection y := by
  haveI : FiniteDimensional ℝ (LinearMap.range S.toLinearMap) := inferInstance
  symm
  refine (LinearMap.range S.toLinearMap).eq_starProjection_of_mem_of_inner_eq_zero ⟨_, rfl⟩ ?_
  rintro _ ⟨x, rfl⟩
  change ⟪y - S (gramPinv S ((S†) y)), S x⟫ = 0
  have e1 : ⟪y, S x⟫ = ⟪(S†) y, x⟫ := (adjoint_inner_left S x y).symm
  have e2 : ⟪S (gramPinv S ((S†) y)), S x⟫ = ⟪gram S (gramPinv S ((S†) y)), x⟫ :=
    (adjoint_inner_left S x _).symm
  rw [inner_sub_left, e1, e2, gram_gramPinv,
    (gramRange S).starProjection_eq_self_iff.mpr (adjoint_apply_mem_gramRange S y), sub_self]

end Gram

/-! ### The Schur innovation -/

section Schur

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']
variable [FiniteDimensional ℝ F] (S : E →L[ℝ] F) (T : E' →L[ℝ] F)

/-- The orthogonal residual `(I - P_{ran S}) T`. -/
noncomputable def residual : E' →L[ℝ] F :=
  (1 - (LinearMap.range S.toLinearMap).starProjection) ∘L T

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [FiniteDimensional ℝ F] in
theorem residual_apply (y : E') :
    residual S T y = T y - (LinearMap.range S.toLinearMap).starProjection (T y) := rfl

/-- The cross Gram `B = S† T`. -/
noncomputable def crossGram : E' →L[ℝ] E := S† ∘L T

/-- **The Moore–Penrose Schur innovation**: `D - B† G† B = T† (I - P_{ran S}) T`, i.e. the Schur
complement of the Gram is the Gram of the orthogonal residual. -/
theorem schur_innovation :
    T† ∘L T - (crossGram S T)† ∘L gramPinv S ∘L crossGram S T = T† ∘L residual S T := by
  refine ContinuousLinearMap.ext fun y => ?_
  simp only [sub_apply, comp_apply, crossGram, adjoint_comp, adjoint_adjoint]
  rw [residual_apply, map_sub, ← comp_gramPinv_comp_adjoint S (T y)]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [FiniteDimensional ℝ F] in
/-- The residual is orthogonal to the range of `S`. -/
theorem residual_inner_eq_zero (y : E') (x : E) : ⟪residual S T y, S x⟫ = 0 := by
  rw [residual_apply]
  exact (LinearMap.range S.toLinearMap).starProjection_inner_eq_zero _ _ ⟨x, rfl⟩

omit [CompleteSpace E] [FiniteDimensional ℝ F] in
/-- The innovation quadratic form is the squared residual. -/
theorem inner_innovation (y : E') :
    ⟪y, (T† ∘L residual S T) y⟫ = ‖residual S T y‖ ^ 2 := by
  simp only [comp_apply]
  rw [adjoint_inner_right, residual_apply]
  set P := (LinearMap.range S.toLinearMap).starProjection with hP
  have h : ⟪T y - P (T y), P (T y)⟫ = 0 :=
    (LinearMap.range S.toLinearMap).starProjection_inner_eq_zero (T y) (P (T y))
      ((LinearMap.range S.toLinearMap).starProjection_apply_mem _)
  have e : ⟪T y, T y - P (T y)⟫ = ⟪T y - P (T y), T y - P (T y)⟫ + ⟪P (T y), T y - P (T y)⟫ := by
    rw [← inner_add_left, sub_add_cancel]
  rw [e, real_inner_self_eq_norm_sq, real_inner_comm (T y - P (T y)) (P (T y)), h, add_zero]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [FiniteDimensional ℝ F] in
/-- **Variational characterization**: `‖(I - P) T y‖² = min_x ‖S x + T y‖²`, attained. -/
theorem innovation_variational (y : E') :
    (∀ x : E, ‖residual S T y‖ ≤ ‖S x + T y‖) ∧ ∃ x : E, ‖S x + T y‖ = ‖residual S T y‖ := by
  set P := (LinearMap.range S.toLinearMap).starProjection with hP
  constructor
  · intro x
    have hmem : P (T y) + S x ∈ LinearMap.range S.toLinearMap :=
      (LinearMap.range S.toLinearMap).add_mem
        ((LinearMap.range S.toLinearMap).starProjection_apply_mem _)
        ⟨x, rfl⟩
    have horth : ⟪T y - P (T y), P (T y) + S x⟫ = 0 :=
      (LinearMap.range S.toLinearMap).starProjection_inner_eq_zero _ _ hmem
    have hdecomp : S x + T y = (T y - P (T y)) + (P (T y) + S x) := by abel
    have h2 : ‖S x + T y‖ ^ 2 = ‖T y - P (T y)‖ ^ 2 + ‖P (T y) + S x‖ ^ 2 := by
      rw [hdecomp, pow_two, pow_two, pow_two]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    have h3 : ‖residual S T y‖ ^ 2 ≤ ‖S x + T y‖ ^ 2 := by
      rw [h2, residual_apply]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact le_of_sq_le_sq h3 (norm_nonneg _)
  · obtain ⟨x, hx⟩ := (LinearMap.range S.toLinearMap).starProjection_apply_mem (T y)
    refine ⟨-x, ?_⟩
    rw [map_neg, residual_apply]
    have hx' : S x = P (T y) := hx
    change ‖-S x + T y‖ = ‖T y - P (T y)‖
    rw [hx']
    congr 1
    abel

/-- The innovation is a positive operator. -/
theorem innovation_isPositive : (T† ∘L residual S T).IsPositive := by
  have hself : IsSelfAdjoint (T† ∘L residual S T) := by
    rw [← schur_innovation]
    refine IsSelfAdjoint.sub ?_ ?_
    · rw [isSelfAdjoint_iff', adjoint_comp, adjoint_adjoint]
    · rw [isSelfAdjoint_iff', adjoint_comp, adjoint_comp, adjoint_adjoint,
        (isSelfAdjoint_iff'.mp (isSelfAdjoint_gramPinv S)), comp_assoc]
  refine ⟨hself.isSymmetric, fun y => ?_⟩
  rw [reApplyInnerSelf_apply, real_inner_comm, inner_innovation]
  exact sq_nonneg _

end Schur

/-! ### Minimum-norm solutions (the Moore–Penrose Thomson principle) -/

section MinNorm

variable [FiniteDimensional ℝ F] (L : E →L[ℝ] F)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The compliance `C = L L†` is the Gram of `L†`. -/
theorem gram_adjoint_eq : gram (L†) = L ∘L L† := by
  rw [gram, adjoint_adjoint]

/-- `ran (L L†) = ran L`. -/
theorem gramRange_adjoint : gramRange (L†) = LinearMap.range L.toLinearMap := by
  rw [gramRange, range_gram, ← orthogonal_range, Submodule.orthogonal_orthogonal]

/-- The minimum-norm solution `q₀ = L† C† b` of `L q = b`. -/
noncomputable def minNormSolution (b : F) : E := (L†) (gramPinv (L†) b)

theorem minNormSolution_apply {b : F} (hb : b ∈ LinearMap.range L.toLinearMap) :
    L (minNormSolution L b) = b := by
  have h : gram (L†) (gramPinv (L†) b) = (gramRange (L†)).starProjection b := gram_gramPinv (L†) b
  rw [gram_adjoint_eq] at h
  rw [minNormSolution]
  change (L ∘L L†) (gramPinv (L†) b) = b
  rw [h, (gramRange (L†)).starProjection_eq_self_iff]
  rw [gramRange_adjoint]
  exact hb

theorem minNormSolution_mem : minNormSolution L b ∈ L.kerᗮ := by
  have := adjoint_apply_mem_gramRange L (gramPinv (L†) b)
  rwa [gramRange, range_gram] at this

/-- **The Moore–Penrose Thomson principle**: `q₀` has minimal norm among the solutions. -/
theorem norm_minNormSolution_le {b : F} {q : E} (hq : L q = b) :
    ‖minNormSolution L b‖ ≤ ‖q‖ := by
  have hb : b ∈ LinearMap.range L.toLinearMap := ⟨q, hq⟩
  have hk : q - minNormSolution L b ∈ L.ker := by
    rw [LinearMap.mem_ker]
    change L (q - minNormSolution L b) = 0
    rw [map_sub, hq, minNormSolution_apply L hb, sub_self]
  have horth : ⟪minNormSolution L b, q - minNormSolution L b⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).mp (minNormSolution_mem L) _ hk
  have hdecomp : q = minNormSolution L b + (q - minNormSolution L b) := by abel
  have h2 : ‖q‖ ^ 2 = ‖minNormSolution L b‖ ^ 2 + ‖q - minNormSolution L b‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    rw [← hdecomp] at this
    rw [pow_two, pow_two, pow_two]
    exact this
  have h3 : ‖minNormSolution L b‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [h2]; exact le_add_of_nonneg_right (sq_nonneg _)
  exact le_of_sq_le_sq h3 (norm_nonneg _)

/-- The minimal action `‖q₀‖² = ⟨b, C† b⟩`. -/
theorem norm_sq_minNormSolution {b : F} (hb : b ∈ LinearMap.range L.toLinearMap) :
    ‖minNormSolution L b‖ ^ 2 = ⟪b, gramPinv (L†) b⟫ := by
  rw [← real_inner_self_eq_norm_sq, minNormSolution, ← adjoint_inner_right, adjoint_adjoint]
  change ⟪gramPinv (L†) b, (L ∘L L†) (gramPinv (L†) b)⟫ = _
  rw [← gram_adjoint_eq, gram_gramPinv, (gramRange (L†)).starProjection_eq_self_iff.mpr,
    real_inner_comm]
  rw [gramRange_adjoint]
  exact hb

end MinNorm

end MoorePenrose
end NCG
