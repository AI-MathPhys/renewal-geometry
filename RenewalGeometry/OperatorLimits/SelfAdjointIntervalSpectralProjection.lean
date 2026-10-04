/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.UnboundedSelfAdjointResolvent
import RenewalGeometry.OperatorLimits.CircleRieszProjectionEigenvector
import RenewalGeometry.OperatorLimits.CompactNormalEigenspaces

/-!
# Interval spectral projections of self-adjoint operators with discrete spectrum

Paper `predictive_spectral_geometry`, spectral-projection clause of
`thm:supp-compact-spin-resolvent` ("isolated bounded-energy spectral projections converge").

For a self-adjoint operator `T` presented by its resolvents (`SelfAdjointResolventData`) on a
complex Hilbert space `K`:

* `opEigenspace T μ`: the eigenspace `{x ∈ dom T | T x = μ x}` of the unbounded operator;
  eigenvalues are real (`im_eq_zero_of_mem_opEigenspace`) and distinct eigenspaces are
  orthogonal (`inner_eq_zero_of_mem_opEigenspace`).
* `spectralSubspace T a b = ⨆_{μ ∈ (a,b)} ker (T - μ)` and the **spectral projection**
  `spectralProjection T a b = 1_{(a,b)}(T)`: the orthogonal projection onto the closed span of the
  eigenvectors with eigenvalue in the bounded interval `(a,b)`.  For an operator with compact
  resolvent the spectral measure is atomic on the eigenvalues, so this is the spectral projection
  of the functional calculus; for a finite-dimensional (bounded) operator it is the usual sum of
  the eigenprojections (`spectralProjection_apply_of_mem`, `spectralProjection_apply_of_not_mem`).
* For an isometry `W : K → H`, the compressed resolvent `W (T - z)⁻¹ W^*` (`compressedResolvent`)
  is normal; its nonzero eigenvectors are `W`-images of eigenvectors of `T` with eigenvalue
  `λ = z + w⁻¹` (`compressedResolvent_eigen`), and its kernel is `ker W^*`.
* Circle geometry (`intervalPoint`, `intervalCenter`, `intervalRadius`): for `a < b`,
  `z = (a+b)/2 + i (b-a)/2`, the Möbius map `λ ↦ (λ - z)⁻¹` sends the real interval `(a,b)` exactly
  into the open disc of centre `i/r`, radius `1/(√2 r)` (`r = (b-a)/2`), the endpoints onto its
  boundary circle and the rest of the real line outside the closed disc, while `0` lies outside the
  closed disc (`inv_sub_intervalPoint_mem_ball_iff`, `..._mem_sphere_iff`).
* **Identification theorem** `circleRieszProjection_compressedResolvent_eq`: when the compressed
  resolvent is compact and the circle lies in its resolvent set, its circle Riesz projection is
  `W 1_{(a,b)}(T) W^*`.  With `W = id` this identifies the Riesz projection of `(T - z)⁻¹` with the
  spectral projection `1_{(a,b)}(T)` (`circleRieszProjection_resolvent_eq`).
* `sphere_subset_resolventSet_compressedResolvent`: if the compressed resolvent is compact and
  `a`, `b` are not eigenvalues of `T` (i.e. the cluster in `(a,b)` is isolated), the circle lies in
  its resolvent set.
-/

open Filter Topology ComplexConjugate Complex
open scoped InnerProductSpace

noncomputable section

namespace RenewalGeometry

namespace SelfAdjointResolventData

universe u v

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! ### Eigenspaces of the unbounded operator -/

/-- The eigenspace `{x ∈ dom T | T x = μ x}` of the unbounded operator `T.op`. -/
def opEigenspace (T : SelfAdjointResolventData K) (μ : ℂ) : Submodule ℂ K where
  carrier := {x | ∃ hx : x ∈ T.op.domain, T.op ⟨x, hx⟩ = μ • x}
  add_mem' := by
    rintro x y ⟨hx, hTx⟩ ⟨hy, hTy⟩
    refine ⟨T.op.domain.add_mem hx hy, ?_⟩
    have : (⟨x + y, T.op.domain.add_mem hx hy⟩ : T.op.domain) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, LinearPMap.map_add, hTx, hTy, smul_add]
  zero_mem' := ⟨T.op.domain.zero_mem, by
    have : (⟨0, T.op.domain.zero_mem⟩ : T.op.domain) = 0 := rfl
    rw [this, LinearPMap.map_zero, smul_zero]⟩
  smul_mem' := by
    rintro c x ⟨hx, hTx⟩
    refine ⟨T.op.domain.smul_mem c hx, ?_⟩
    have : (⟨c • x, T.op.domain.smul_mem c hx⟩ : T.op.domain) = c • ⟨x, hx⟩ := rfl
    rw [this, LinearPMap.map_smul, hTx, smul_comm]

variable (T : SelfAdjointResolventData K)

theorem mem_opEigenspace {μ : ℂ} {x : K} :
    x ∈ T.opEigenspace μ ↔ ∃ hx : x ∈ T.op.domain, T.op ⟨x, hx⟩ = μ • x := Iff.rfl

/-- Eigenvalues of a self-adjoint operator are real. -/
theorem im_eq_zero_of_mem_opEigenspace {μ : ℂ} {x : K} (hx : x ∈ T.opEigenspace μ)
    (hx0 : x ≠ 0) : μ.im = 0 := by
  obtain ⟨hxd, hTx⟩ := hx
  have h := T.im_inner_op_self ⟨x, hxd⟩
  change (⟪T.op ⟨x, hxd⟩, x⟫_ℂ).im = 0 at h
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    positivity
  have him0 : (⟪x, x⟫_ℂ).im = 0 := by simpa using (inner_self_im (𝕜 := ℂ) x)
  have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  rw [hTx, inner_smul_left, Complex.mul_im, him0, hre, Complex.conj_im, mul_zero,
    zero_add] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · linarith
  · exact absurd h1 hpos.ne'

/-- Eigenvectors of distinct eigenvalues are orthogonal (the first eigenvalue real). -/
theorem inner_eq_zero_of_mem_opEigenspace {μ ν : ℂ} {x y : K} (hx : x ∈ T.opEigenspace μ)
    (hy : y ∈ T.opEigenspace ν) (hμ : μ.im = 0) (hne : μ ≠ ν) : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨hxd, hTx⟩ := hx
  obtain ⟨hyd, hTy⟩ := hy
  have h := T.symm ⟨x, hxd⟩ ⟨y, hyd⟩
  change ⟪T.op ⟨x, hxd⟩, y⟫_ℂ = ⟪x, T.op ⟨y, hyd⟩⟫_ℂ at h
  rw [hTx, hTy, inner_smul_left, inner_smul_right] at h
  have hconj : conj μ = μ := Complex.conj_eq_iff_im.mpr hμ
  rw [hconj] at h
  have : (μ - ν) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

/-! ### The interval spectral projection -/

/-- The algebraic sum of the eigenspaces with eigenvalue in the open interval `(a,b)`. -/
def spectralSubspace (a b : ℝ) : Submodule ℂ K :=
  ⨆ (μ : ℝ) (_ : μ ∈ Set.Ioo a b), T.opEigenspace (μ : ℂ)

variable [CompleteSpace K]

/-- **The spectral projection `1_{(a,b)}(T)`**: the orthogonal projection onto the closed span of
the eigenvectors of `T` whose eigenvalue lies in the open interval `(a,b)`.  (The closed span is
written as the double orthogonal complement.) -/
def spectralProjection (a b : ℝ) : K →L[ℂ] K :=
  ((T.spectralSubspace a b)ᗮᗮ).starProjection

omit [CompleteSpace K] in
theorem mem_spectralSubspace {a b μ : ℝ} (hμ : μ ∈ Set.Ioo a b) {x : K}
    (hx : x ∈ T.opEigenspace (μ : ℂ)) : x ∈ T.spectralSubspace a b := by
  unfold spectralSubspace
  exact (le_iSup₂ (f := fun (μ : ℝ) (_ : μ ∈ Set.Ioo a b) => T.opEigenspace (μ : ℂ)) μ hμ) hx

/-- `1_{(a,b)}(T)` fixes the eigenvectors with eigenvalue in `(a,b)`. -/
theorem spectralProjection_apply_of_mem {a b μ : ℝ} (hμ : μ ∈ Set.Ioo a b) {x : K}
    (hx : x ∈ T.opEigenspace (μ : ℂ)) : T.spectralProjection a b x = x := by
  unfold spectralProjection
  rw [Submodule.starProjection_eq_self_iff]
  exact Submodule.le_orthogonal_orthogonal _ (T.mem_spectralSubspace hμ hx)

/-- `1_{(a,b)}(T)` kills the eigenvectors with real eigenvalue outside `(a,b)`. -/
theorem spectralProjection_apply_of_not_mem {a b μ : ℝ} (hμ : μ ∉ Set.Ioo a b) {x : K}
    (hx : x ∈ T.opEigenspace (μ : ℂ)) : T.spectralProjection a b x = 0 := by
  unfold spectralProjection
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.triorthogonal_eq_orthogonal]
  rw [Submodule.mem_orthogonal']
  intro y hy
  unfold spectralSubspace at hy
  refine Submodule.iSup_induction (motive := fun y => ⟪x, y⟫_ℂ = 0)
    (fun ν : ℝ => ⨆ (_ : ν ∈ Set.Ioo a b), T.opEigenspace (ν : ℂ)) hy ?_ ?_ ?_
  · intro ν y hy
    by_cases hν : ν ∈ Set.Ioo a b
    · rw [iSup_pos hν] at hy
      refine T.inner_eq_zero_of_mem_opEigenspace hx hy (by simp) ?_
      intro h
      apply hμ
      have : μ = ν := by exact_mod_cast h
      rw [this]; exact hν
    · rw [iSup_neg hν] at hy
      rw [(Submodule.mem_bot ℂ).mp hy, inner_zero_right]
  · exact inner_zero_right x
  · intro y₁ y₂ h₁ h₂
    rw [inner_add_right, h₁, h₂, add_zero]

/-- `1_{(a,b)}(T)` is an orthogonal projection. -/
theorem isStarProjection_spectralProjection (a b : ℝ) :
    IsStarProjection (T.spectralProjection a b) :=
  isStarProjection_starProjection

/-! ### Resolvent identities -/

omit [CompleteSpace K] in
/-- The resolvent is injective. -/
theorem resolvent_eq_zero_iff {z : ℂ} (hz : z.im ≠ 0) (f : K) :
    T.resolvent z hz f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have h0 : (⟨T.resolvent z hz f, T.resolvent_mem z hz f⟩ : T.op.domain) = 0 := Subtype.ext h
    calc f = T.op ⟨T.resolvent z hz f, T.resolvent_mem z hz f⟩ - z • T.resolvent z hz f :=
          (T.op_resolvent z hz f).symm
      _ = 0 := by rw [h0, LinearPMap.map_zero, h, smul_zero, sub_zero]
  · rintro rfl
    exact map_zero _

omit [CompleteSpace K] in
/-- On an eigenvector with real eigenvalue `μ`, `(T - z)⁻¹ x = (μ - z)⁻¹ x`. -/
theorem resolvent_apply_of_mem_opEigenspace {z : ℂ} (hz : z.im ≠ 0) {μ : ℂ} {x : K}
    (hx : x ∈ T.opEigenspace μ) (hμ : μ.im = 0) :
    T.resolvent z hz x = (μ - z)⁻¹ • x := by
  obtain ⟨hxd, hTx⟩ := hx
  have hne : μ - z ≠ 0 := by
    intro h
    apply hz
    rw [← sub_eq_zero.mp h]
    exact hμ
  have h := T.resolvent_op z hz ⟨x, hxd⟩
  change T.resolvent z hz (T.op ⟨x, hxd⟩ - z • x) = x at h
  rw [hTx, ← sub_smul, map_smul] at h
  calc T.resolvent z hz x = (μ - z)⁻¹ • ((μ - z) • T.resolvent z hz x) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (μ - z)⁻¹ • x := by rw [h]

omit [CompleteSpace K] in
/-- A nonzero eigenvalue `w` of the resolvent `(T - z)⁻¹` comes from the eigenvalue `z + w⁻¹`
of `T`. -/
theorem mem_opEigenspace_of_resolvent_eq_smul {z : ℂ} (hz : z.im ≠ 0) {w : ℂ} (hw : w ≠ 0)
    {y : K} (hy : T.resolvent z hz y = w • y) : y ∈ T.opEigenspace (z + w⁻¹) := by
  have hyd : y ∈ T.op.domain := by
    have : y = w⁻¹ • T.resolvent z hz y := by
      rw [hy, smul_smul, inv_mul_cancel₀ hw, one_smul]
    rw [this]
    exact T.op.domain.smul_mem _ (T.resolvent_mem z hz y)
  refine ⟨hyd, ?_⟩
  have h := T.op_resolvent z hz y
  have hdom : (⟨T.resolvent z hz y, T.resolvent_mem z hz y⟩ : T.op.domain) = w • ⟨y, hyd⟩ :=
    Subtype.ext hy
  rw [hdom, LinearPMap.map_smul, hy] at h
  have h2 : w • (T.op ⟨y, hyd⟩ - z • y) = y := by
    rw [smul_sub, smul_comm w z y]
    exact h
  have h3 : T.op ⟨y, hyd⟩ - z • y = w⁻¹ • y := by
    calc T.op ⟨y, hyd⟩ - z • y = w⁻¹ • (w • (T.op ⟨y, hyd⟩ - z • y)) := by
          rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
      _ = w⁻¹ • y := by rw [h2]
  rw [add_smul, ← h3]
  abel

omit [CompleteSpace K] in
/-- The first resolvent identity `R(z) - R(w) = (z - w) R(z) R(w)`. -/
theorem resolvent_sub_resolvent {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) (f : K) :
    T.resolvent z hz f - T.resolvent w hw f =
      (z - w) • T.resolvent z hz (T.resolvent w hw f) := by
  have h1 := T.op_resolvent w hw f
  have h2 := T.resolvent_op z hz ⟨T.resolvent w hw f, T.resolvent_mem w hw f⟩
  change T.resolvent z hz (T.op ⟨T.resolvent w hw f, T.resolvent_mem w hw f⟩ -
    z • T.resolvent w hw f) = T.resolvent w hw f at h2
  have e : f = (T.op ⟨T.resolvent w hw f, T.resolvent_mem w hw f⟩ - z • T.resolvent w hw f) +
      (z - w) • T.resolvent w hw f := by
    linear_combination (norm := module) -h1
  have h3 : T.resolvent z hz f =
      T.resolvent w hw f + (z - w) • T.resolvent z hz (T.resolvent w hw f) := by
    conv_lhs => rw [e]
    rw [map_add, map_smul, h2]
  rw [h3]
  abel

omit [CompleteSpace K] in
/-- Resolvents at different points commute. -/
theorem resolvent_comm {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) (f : K) :
    T.resolvent z hz (T.resolvent w hw f) = T.resolvent w hw (T.resolvent z hz f) := by
  by_cases hzw : z = w
  · subst hzw
    rfl
  have h1 := T.resolvent_sub_resolvent hz hw f
  have h2 := T.resolvent_sub_resolvent hw hz f
  have h3 : (z - w) • (T.resolvent z hz (T.resolvent w hw f) -
      T.resolvent w hw (T.resolvent z hz f)) = 0 := by
    linear_combination (norm := module) -h1 - h2
  rw [smul_eq_zero] at h3
  rcases h3 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hzw
  · exact sub_eq_zero.mp h3

/-! ### Compressed resolvents -/

section compressed

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `W^* W = 1` for an isometry. -/
theorem adjoint_isometry_comp_self (W : K →ₗᵢ[ℂ] H) :
    ContinuousLinearMap.adjoint W.toContinuousLinearMap ∘L W.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ K := by
  ext x
  apply ext_inner_right ℂ
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.id_apply]
  exact W.inner_map_map x v

theorem adjoint_isometry_apply_self (W : K →ₗᵢ[ℂ] H) (x : K) :
    ContinuousLinearMap.adjoint W.toContinuousLinearMap (W x) = x := by
  have := congrArg (fun F : K →L[ℂ] K => F x) (adjoint_isometry_comp_self W)
  exact this

/-- The compressed resolvent `W (T - z)⁻¹ W^*` along an isometry `W : K → H`. -/
def compressedResolvent (W : K →ₗᵢ[ℂ] H) (z : ℂ) (hz : z.im ≠ 0) : H →L[ℂ] H :=
  W.toContinuousLinearMap ∘L T.resolvent z hz ∘L
    ContinuousLinearMap.adjoint W.toContinuousLinearMap

theorem compressedResolvent_apply (W : K →ₗᵢ[ℂ] H) (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    T.compressedResolvent W z hz x =
      W (T.resolvent z hz (ContinuousLinearMap.adjoint W.toContinuousLinearMap x)) := rfl

theorem adjoint_id_isometry :
    ContinuousLinearMap.adjoint (LinearIsometry.id : K →ₗᵢ[ℂ] K).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ K := by
  ext x
  exact adjoint_isometry_apply_self (LinearIsometry.id : K →ₗᵢ[ℂ] K) x

/-- With `W = id` the compressed resolvent is the resolvent. -/
theorem compressedResolvent_id (z : ℂ) (hz : z.im ≠ 0) :
    T.compressedResolvent (LinearIsometry.id : K →ₗᵢ[ℂ] K) z hz = T.resolvent z hz := by
  ext x
  rw [compressedResolvent_apply, adjoint_id_isometry]
  rfl

/-- The compressed resolvent is a normal operator. -/
theorem isStarNormal_compressedResolvent (W : K →ₗᵢ[ℂ] H) (z : ℂ) (hz : z.im ≠ 0) :
    IsStarNormal (T.compressedResolvent W z hz) := by
  have hz' : (conj z).im ≠ 0 := conj_im_ne_zero hz
  have hadj : star (T.compressedResolvent W z hz) = T.compressedResolvent W (conj z) hz' := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    unfold compressedResolvent
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, T.adjoint_resolvent hz hz',
      ContinuousLinearMap.comp_assoc]
  rw [isStarNormal_iff, hadj, commute_iff_eq]
  ext x
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, compressedResolvent_apply,
    adjoint_isometry_apply_self]
  rw [T.resolvent_comm hz' hz]

/-- The compressed resolvent of a finite-dimensional stage is compact. -/
theorem isCompactOperator_compressedResolvent [FiniteDimensional ℂ K] (W : K →ₗᵢ[ℂ] H)
    (z : ℂ) (hz : z.im ≠ 0) : IsCompactOperator (T.compressedResolvent W z hz) := by
  have hid : IsCompactOperator (_root_.id : K → K) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)).mpr inferInstance
  exact (hid.clm_comp (W.toContinuousLinearMap ∘L T.resolvent z hz)).comp_clm
    (ContinuousLinearMap.adjoint W.toContinuousLinearMap)

/-- A nonzero eigenvector of the compressed resolvent lies in the range of `W` and is the image
of an eigenvector of `T` with eigenvalue `z + w⁻¹`. -/
theorem compressedResolvent_eigen (W : K →ₗᵢ[ℂ] H) {z : ℂ} (hz : z.im ≠ 0) {w : ℂ}
    (hw : w ≠ 0) {x : H} (hx : T.compressedResolvent W z hz x = w • x) :
    W (ContinuousLinearMap.adjoint W.toContinuousLinearMap x) = x ∧
      ContinuousLinearMap.adjoint W.toContinuousLinearMap x ∈ T.opEigenspace (z + w⁻¹) := by
  have hxW : x = W (w⁻¹ • T.resolvent z hz
      (ContinuousLinearMap.adjoint W.toContinuousLinearMap x)) := by
    rw [LinearIsometry.map_smul, ← compressedResolvent_apply, hx, smul_smul,
      inv_mul_cancel₀ hw, one_smul]
  have hWy : W (ContinuousLinearMap.adjoint W.toContinuousLinearMap x) = x := by
    set v := w⁻¹ • T.resolvent z hz (ContinuousLinearMap.adjoint W.toContinuousLinearMap x)
    have hx' : x = W v := hxW
    rw [hx', adjoint_isometry_apply_self]
  refine ⟨hWy, ?_⟩
  apply T.mem_opEigenspace_of_resolvent_eq_smul hz hw
  have h := congrArg (ContinuousLinearMap.adjoint W.toContinuousLinearMap) hx
  rw [compressedResolvent_apply, adjoint_isometry_apply_self, map_smul] at h
  exact h

/-- The kernel of the compressed resolvent is `ker W^*`. -/
theorem adjoint_eq_zero_of_compressedResolvent_eq_zero (W : K →ₗᵢ[ℂ] H) {z : ℂ}
    (hz : z.im ≠ 0) {x : H} (hx : T.compressedResolvent W z hz x = 0) :
    ContinuousLinearMap.adjoint W.toContinuousLinearMap x = 0 := by
  rw [compressedResolvent_apply] at hx
  have h : T.resolvent z hz (ContinuousLinearMap.adjoint W.toContinuousLinearMap x) = 0 := by
    have := congrArg norm hx
    rw [LinearIsometry.norm_map, norm_zero] at this
    exact norm_eq_zero.mp this
  exact (T.resolvent_eq_zero_iff hz _).mp h

end compressed

end SelfAdjointResolventData

/-! ### Circle geometry of an interval under `λ ↦ (λ - z)⁻¹` -/

namespace IntervalCircle

/-- The non-real point `z = (a+b)/2 + i (b-a)/2`. -/
def point (a b : ℝ) : ℂ := (((a + b) / 2 : ℝ) : ℂ) + (((b - a) / 2 : ℝ) : ℂ) * I

/-- The circle centre `i / r`, `r = (b-a)/2` (the image of the midpoint). -/
def center (a b : ℝ) : ℂ := I * ((((b - a) / 2 : ℝ) : ℂ))⁻¹

/-- The circle radius `1 / (√2 r)` (the distance from the centre to the images of `a`, `b`). -/
def radius (a b : ℝ) : ℝ := (Real.sqrt 2 * ((b - a) / 2))⁻¹

theorem point_im (a b : ℝ) : (point a b).im = (b - a) / 2 := by
  simp [point]

theorem point_im_ne_zero {a b : ℝ} (hab : a < b) : (point a b).im ≠ 0 := by
  rw [point_im]
  linarith

theorem radius_pos {a b : ℝ} (hab : a < b) : 0 < radius a b := by
  unfold radius
  have : 0 < (b - a) / 2 := by linarith
  positivity

theorem normSq_inv_aux (t r : ℝ) (hr : r ≠ 0) :
    Complex.normSq (((t : ℂ) - (r : ℂ) * I)⁻¹ - I * (r : ℂ)⁻¹) =
      t ^ 2 / (r ^ 2 * (t ^ 2 + r ^ 2)) := by
  have hs : t ^ 2 + r ^ 2 ≠ 0 := by positivity
  have hinv : ((t : ℂ) - (r : ℂ) * I)⁻¹ =
      ((t / (t ^ 2 + r ^ 2) : ℝ) : ℂ) + ((r / (t ^ 2 + r ^ 2) : ℝ) : ℂ) * I := by
    apply inv_eq_of_mul_eq_one_right
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.I_re,
        Complex.I_im, Complex.one_re]
      field_simp
      ring
    · simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.I_re,
        Complex.I_im, Complex.one_im]
      field_simp
      ring
  have hc : I * (r : ℂ)⁻¹ = ((r⁻¹ : ℝ) : ℂ) * I := by push_cast; ring
  rw [hinv, hc, add_sub_assoc, ← sub_mul, ← Complex.ofReal_sub, Complex.normSq_add_mul_I]
  field_simp
  ring

theorem normSq_inv_sub_point_sub_center {a b : ℝ} (hab : a < b) (l : ℝ) :
    Complex.normSq (((l : ℂ) - point a b)⁻¹ - center a b) =
      (l - (a + b) / 2) ^ 2 /
        (((b - a) / 2) ^ 2 * ((l - (a + b) / 2) ^ 2 + ((b - a) / 2) ^ 2)) := by
  have hr : (b - a) / 2 ≠ 0 := by linarith
  have hp : (l : ℂ) - point a b =
      (((l - (a + b) / 2 : ℝ)) : ℂ) - (((b - a) / 2 : ℝ) : ℂ) * I := by
    simp only [point]
    push_cast
    ring
  rw [hp]
  exact normSq_inv_aux _ _ hr

theorem sub_radius_aux (t r : ℝ) (hr : r ≠ 0) :
    t ^ 2 / (r ^ 2 * (t ^ 2 + r ^ 2)) - (Real.sqrt 2 * r)⁻¹ ^ 2 =
      (t ^ 2 - r ^ 2) / (2 * r ^ 2 * (t ^ 2 + r ^ 2)) := by
  have hs : t ^ 2 + r ^ 2 ≠ 0 := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [inv_pow, mul_pow, h2]
  field_simp
  ring

theorem normSq_sub_radius_sq {a b : ℝ} (hab : a < b) (l : ℝ) :
    Complex.normSq (((l : ℂ) - point a b)⁻¹ - center a b) - radius a b ^ 2 =
      ((l - (a + b) / 2) ^ 2 - ((b - a) / 2) ^ 2) /
        (2 * ((b - a) / 2) ^ 2 * ((l - (a + b) / 2) ^ 2 + ((b - a) / 2) ^ 2)) := by
  rw [normSq_inv_sub_point_sub_center hab]
  exact sub_radius_aux _ _ (by linarith)

theorem dist_sq_eq_normSq (w c : ℂ) : dist w c ^ 2 = Complex.normSq (w - c) := by
  rw [Complex.dist_eq, Complex.sq_norm]

/-- The Möbius image `(λ - z)⁻¹` of a real `λ` lies in the open disc iff `λ ∈ (a,b)`. -/
theorem inv_sub_point_mem_ball_iff {a b : ℝ} (hab : a < b) (l : ℝ) :
    ((l : ℂ) - point a b)⁻¹ ∈ Metric.ball (center a b) (radius a b) ↔ l ∈ Set.Ioo a b := by
  have hR := radius_pos hab
  have hden : 0 < 2 * ((b - a) / 2) ^ 2 * ((l - (a + b) / 2) ^ 2 + ((b - a) / 2) ^ 2) := by
    have : 0 < (b - a) / 2 := by linarith
    positivity
  rw [Metric.mem_ball, ← sq_lt_sq₀ dist_nonneg hR.le, dist_sq_eq_normSq, ← sub_neg,
    normSq_sub_radius_sq hab, div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd hden (not_lt.mpr h.le)
    · have h' : (l - (a + b) / 2) ^ 2 < ((b - a) / 2) ^ 2 := by linarith
      have := abs_lt_of_sq_lt_sq' h' (by linarith)
      constructor <;> linarith [this.1, this.2]
  · rintro ⟨h1, h2⟩
    right
    refine ⟨?_, hden⟩
    nlinarith

/-- The Möbius image lies on the circle iff `λ` is an endpoint. -/
theorem inv_sub_point_mem_sphere_iff {a b : ℝ} (hab : a < b) (l : ℝ) :
    ((l : ℂ) - point a b)⁻¹ ∈ Metric.sphere (center a b) (radius a b) ↔ l = a ∨ l = b := by
  have hR := radius_pos hab
  have hden : 0 < 2 * ((b - a) / 2) ^ 2 * ((l - (a + b) / 2) ^ 2 + ((b - a) / 2) ^ 2) := by
    have : 0 < (b - a) / 2 := by linarith
    positivity
  rw [Metric.mem_sphere, ← sq_eq_sq₀ dist_nonneg hR.le, dist_sq_eq_normSq, ← sub_eq_zero,
    normSq_sub_radius_sq hab, div_eq_zero_iff, or_iff_left hden.ne']
  constructor
  · intro h
    have : (l - a) * (l - b) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-- `0` lies outside the closed disc. -/
theorem zero_not_mem_closedBall {a b : ℝ} (hab : a < b) :
    (0 : ℂ) ∉ Metric.closedBall (center a b) (radius a b) := by
  intro h
  rw [Metric.mem_closedBall, dist_comm, dist_zero_right] at h
  have hr : 0 < (b - a) / 2 := by linarith
  have hc : ‖center a b‖ = ((b - a) / 2)⁻¹ := by
    unfold center
    rw [norm_mul, Complex.norm_I, one_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
  rw [hc] at h
  unfold radius at h
  have h2 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [mul_inv] at h
  have hpos : 0 < ((b - a) / 2)⁻¹ := inv_pos.mpr hr
  have : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
  nlinarith

theorem zero_not_mem_ball {a b : ℝ} (hab : a < b) :
    (0 : ℂ) ∉ Metric.ball (center a b) (radius a b) :=
  fun h => zero_not_mem_closedBall hab (Metric.ball_subset_closedBall h)

end IntervalCircle

/-! ### Circle Riesz projections acting on eigenvectors -/

namespace ResolventStability

universe w

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

open Classical in
/-- On an eigenvector, a circle Riesz operator whose contour avoids the spectrum acts as the
indicator of the open disc. -/
theorem circleRieszProjection_apply_eigenvector (T : E →L[ℂ] E) (center μ : ℂ) (radius : ℝ)
    (hR : 0 < radius) (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (x : E) (hx : T x = μ • x) :
    circleRieszProjection T center radius x =
      if μ ∈ Metric.ball center radius then x else 0 := by
  by_cases hxzero : x = 0
  · simp [hxzero]
  by_cases hμball : μ ∈ Metric.ball center radius
  · rw [if_pos hμball]
    exact circleRieszProjection_apply_eigenvector_of_mem_ball T center μ radius x hμball
      hcontour hx
  · rw [if_neg hμball]
    have hnotSphere : μ ∉ Metric.sphere center radius := by
      intro hμsphere
      have hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) μ - T) := hcontour μ hμsphere
      have hkill : (algebraMap ℂ (E →L[ℂ] E) μ - T) x = 0 := by
        simp [hx]
      have hunitkill : (↑hu.unit : E →L[ℂ] E) x = 0 := by
        simpa using hkill
      apply hxzero
      calc x = ((↑hu.unit⁻¹ : E →L[ℂ] E) * (↑hu.unit : E →L[ℂ] E)) x := by
            rw [hu.unit.inv_mul]
            rfl
        _ = (↑hu.unit⁻¹ : E →L[ℂ] E) ((↑hu.unit : E →L[ℂ] E) x) := rfl
        _ = 0 := by rw [hunitkill]; simp
    have hμoutside : μ ∉ Metric.closedBall center radius := by
      intro hμclosed
      have hle : dist μ center ≤ radius := Metric.mem_closedBall.mp hμclosed
      have hge : radius ≤ dist μ center :=
        le_of_not_gt (fun hlt => hμball (Metric.mem_ball.mpr hlt))
      exact hnotSphere (Metric.mem_sphere.mpr (hle.antisymm hge))
    exact circleRieszProjection_apply_eigenvector_of_not_mem_closedBall T center μ radius x hR
      hμoutside hcontour hx

open Classical in
/-- A circle Riesz operator is determined by its action on eigenvectors when the eigenspaces
are dense. -/
theorem circleRieszProjection_eq_of_dense_eigenspaces (T P : E →L[ℂ] E)
    (hdense : Dense
      (((⨆ μ, Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ E) : Set E))
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (hP : ∀ μ x, T x = μ • x → P x = if μ ∈ Metric.ball center radius then x else 0) :
    circleRieszProjection T center radius = P := by
  let Q : E →L[ℂ] E := circleRieszProjection T center radius
  have hEqOn : Set.EqOn Q P
      (((⨆ μ, Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ E) : Set E) := by
    intro x hx
    refine Submodule.iSup_induction (motive := fun x => Q x = P x)
      (fun μ => Module.End.eigenspace T.toLinearMap μ) hx ?_ ?_ ?_
    · intro μ x hx
      have hx' : T x = μ • x := Module.End.mem_eigenspace_iff.mp hx
      rw [hP μ x hx']
      exact circleRieszProjection_apply_eigenvector T center μ radius hR hcontour x hx'
    · simp
    · intro x y hx hy
      simp only [map_add, hx, hy]
  have hfun : (Q : E → E) = P :=
    Continuous.ext_on hdense Q.continuous P.continuous hEqOn
  exact ContinuousLinearMap.coe_injective (DFunLike.coe_injective hfun)

end ResolventStability

/-! ### Identification of circle Riesz projections with spectral projections -/

namespace SelfAdjointResolventData

open ResolventStability IntervalCircle

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : SelfAdjointResolventData K)

omit [CompleteSpace K] in
/-- An eigenvalue of `T` is the real number `λ.re`. -/
theorem eq_ofReal_re_of_mem_opEigenspace {μ : ℂ} {x : K} (hx : x ∈ T.opEigenspace μ)
    (hx0 : x ≠ 0) : μ = ((μ.re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [T.im_eq_zero_of_mem_opEigenspace hx hx0])

/-- **Riesz projection = spectral projection.**  If the compressed resolvent
`W (T - z)⁻¹ W^*` at `z = (a+b)/2 + i(b-a)/2` is compact and the circle of centre `i/r` and
radius `1/(√2 r)` lies in its resolvent set, its circle Riesz projection is
`W 1_{(a,b)}(T) W^*`. -/
theorem circleRieszProjection_compressedResolvent_eq (W : K →ₗᵢ[ℂ] H) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompactOperator (T.compressedResolvent W (point a b) (point_im_ne_zero hab)))
    (hcontour : ∀ w ∈ Metric.sphere (center a b) (radius a b),
      w ∈ resolventSet ℂ (T.compressedResolvent W (point a b) (point_im_ne_zero hab))) :
    circleRieszProjection (T.compressedResolvent W (point a b) (point_im_ne_zero hab))
        (center a b) (radius a b) =
      W.toContinuousLinearMap ∘L T.spectralProjection a b ∘L
        ContinuousLinearMap.adjoint W.toContinuousLinearMap := by
  have hz : (point a b).im ≠ 0 := point_im_ne_zero hab
  have hdense := NormalSpectrum.dense_iSup_eigenspaces_of_compact_of_isStarNormal
    (T.compressedResolvent W (point a b) hz) hcompact
    (T.isStarNormal_compressedResolvent W (point a b) hz)
  refine circleRieszProjection_eq_of_dense_eigenspaces _ _ hdense (center a b) (radius a b)
    (radius_pos hab) hcontour ?_
  intro w x hx
  simp only [ContinuousLinearMap.comp_apply]
  by_cases hw : w = 0
  · subst hw
    rw [if_neg (zero_not_mem_ball hab)]
    have hx0 : T.compressedResolvent W (point a b) hz x = 0 := by rw [hx, zero_smul]
    rw [T.adjoint_eq_zero_of_compressedResolvent_eq_zero W hz hx0, map_zero, map_zero]
  obtain ⟨hWy, hy⟩ := T.compressedResolvent_eigen W hz hw hx
  by_cases hy0 : ContinuousLinearMap.adjoint W.toContinuousLinearMap x = 0
  · have hx0 : x = 0 := by rw [← hWy, hy0, map_zero]
    subst hx0
    simp
  have hreal := T.eq_ofReal_re_of_mem_opEigenspace hy hy0
  have hyl : ContinuousLinearMap.adjoint W.toContinuousLinearMap x ∈
      T.opEigenspace (((point a b + w⁻¹).re : ℝ) : ℂ) := by
    rw [← hreal]; exact hy
  have hwl : w = (((((point a b + w⁻¹).re : ℝ)) : ℂ) - point a b)⁻¹ := by
    rw [← hreal]
    simp
  rw [hwl, inv_sub_point_mem_ball_iff hab]
  by_cases hl : (point a b + w⁻¹).re ∈ Set.Ioo a b
  · rw [if_pos hl, T.spectralProjection_apply_of_mem hl hyl]
    exact hWy
  · rw [if_neg hl, T.spectralProjection_apply_of_not_mem hl hyl]
    simp

/-- **Isolation of the cluster.**  If the compressed resolvent is compact and neither endpoint
`a`, `b` is an eigenvalue of `T`, the circle lies in its resolvent set. -/
theorem sphere_subset_resolventSet_compressedResolvent (W : K →ₗᵢ[ℂ] H) {a b : ℝ}
    (hab : a < b)
    (hcompact : IsCompactOperator (T.compressedResolvent W (point a b) (point_im_ne_zero hab)))
    (ha : T.opEigenspace (a : ℂ) = ⊥) (hb : T.opEigenspace (b : ℂ) = ⊥) :
    ∀ w ∈ Metric.sphere (center a b) (radius a b),
      w ∈ resolventSet ℂ (T.compressedResolvent W (point a b) (point_im_ne_zero hab)) := by
  intro w hwS
  have hz : (point a b).im ≠ 0 := point_im_ne_zero hab
  have hw : w ≠ 0 := by
    rintro rfl
    exact zero_not_mem_closedBall hab (Metric.sphere_subset_closedBall hwS)
  rcases hcompact.hasEigenvalue_or_mem_resolventSet hw with heig | hres
  · exfalso
    obtain ⟨x, hxmem, hx0⟩ := heig.exists_hasEigenvector
    have hx : T.compressedResolvent W (point a b) hz x = w • x :=
      Module.End.mem_eigenspace_iff.mp hxmem
    obtain ⟨hWy, hy⟩ := T.compressedResolvent_eigen W hz hw hx
    have hy0 : ContinuousLinearMap.adjoint W.toContinuousLinearMap x ≠ 0 := by
      intro h
      apply hx0
      rw [← hWy, h, map_zero]
    have hreal := T.eq_ofReal_re_of_mem_opEigenspace hy hy0
    have hyl : ContinuousLinearMap.adjoint W.toContinuousLinearMap x ∈
        T.opEigenspace (((point a b + w⁻¹).re : ℝ) : ℂ) := by
      rw [← hreal]; exact hy
    have hwl : w = (((((point a b + w⁻¹).re : ℝ)) : ℂ) - point a b)⁻¹ := by
      rw [← hreal]
      simp
    rw [hwl, inv_sub_point_mem_sphere_iff hab] at hwS
    rcases hwS with h | h
    · rw [h, ha] at hyl
      exact hy0 ((Submodule.mem_bot ℂ).mp hyl)
    · rw [h, hb] at hyl
      exact hy0 ((Submodule.mem_bot ℂ).mp hyl)
  · exact hres

/-- **Riesz projection of the resolvent = spectral projection** (`W = id`): for a self-adjoint
operator with compact resolvent and an interval `(a,b)` whose endpoints are not eigenvalues,
the circle lies in the resolvent set of `(T - z)⁻¹` and its circle Riesz projection is
`1_{(a,b)}(T)`. -/
theorem circleRieszProjection_resolvent_eq {a b : ℝ} (hab : a < b)
    (hcompact : IsCompactOperator (T.resolvent (point a b) (point_im_ne_zero hab)))
    (ha : T.opEigenspace (a : ℂ) = ⊥) (hb : T.opEigenspace (b : ℂ) = ⊥) :
    (∀ w ∈ Metric.sphere (center a b) (radius a b),
      w ∈ resolventSet ℂ (T.resolvent (point a b) (point_im_ne_zero hab))) ∧
    circleRieszProjection (T.resolvent (point a b) (point_im_ne_zero hab))
        (center a b) (radius a b) = T.spectralProjection a b := by
  have hid := T.compressedResolvent_id (point a b) (point_im_ne_zero hab)
  have hcompact' : IsCompactOperator
      (T.compressedResolvent LinearIsometry.id (point a b) (point_im_ne_zero hab)) := by
    rw [hid]; exact hcompact
  have hcont := T.sphere_subset_resolventSet_compressedResolvent LinearIsometry.id hab hcompact'
    ha hb
  refine ⟨by rw [← hid]; exact hcont, ?_⟩
  have h := T.circleRieszProjection_compressedResolvent_eq LinearIsometry.id hab hcompact' hcont
  rw [hid] at h
  rw [h, adjoint_id_isometry]
  rfl

/-- For a bounded self-adjoint operator (e.g. a finite stage `D_h`), the eigenspaces of the
resolvent data are the usual eigenspaces. -/
theorem ofBounded_opEigenspace (A : K →L[ℂ] K) (hA : IsSelfAdjoint A)
    (μ : ℂ) : (ofBounded A hA).opEigenspace μ = Module.End.eigenspace A.toLinearMap μ := by
  ext x
  rw [Module.End.mem_eigenspace_iff, mem_opEigenspace]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨Submodule.mem_top, h⟩

end SelfAdjointResolventData

end RenewalGeometry
