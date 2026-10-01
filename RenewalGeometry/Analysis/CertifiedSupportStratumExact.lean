/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SingularSubspacePerturbation

/-!
# Certified support stratum from a singular-value gap (`thm:certified-support-stratum`)

For a represented coefficient map `F : E → H` between finite-dimensional inner product spaces
and an observed `F̂` with `‖F̂ - F‖_op ≤ ε` (or `‖F̂ - F‖_HS ≤ ε`), an independent premise
`rank F ≤ r` and an observed gap `σ̂_r > 2ε` give `rank F = r`, and the support projectors
`p = supp(F^*F)`, `q = supp(FF^*)` are within `ε / (σ̂_r - 2ε)` of the right and left singular
projectors `p̂_r`, `q̂_r` of `F̂` for its `r` largest singular values.

Conventions.  Singular values are Mathlib's `LinearMap.singularValues` (zero-indexed, so the
paper's `σ̂_r` is `singularValues (r - 1)`, `r ≥ 1`).  The right (left) singular projector of `F̂`
for its `r` largest singular values is the spectral projector of `F̂^*F̂` (of `F̂F̂^*`) onto
`[σ̂_r², ∞)`; the theorem proves that these projectors have rank exactly `r`, so they are the
projectors onto the spans of the top `r` right (left) singular vectors.  The support projection
`supp(A)` of a positive operator is the orthogonal projection onto `Ran A`.
-/

open scoped InnerProductSpace
open Module Module.End
open RenewalGeometry.HermitianSpectral RenewalGeometry.SingularSubspace

noncomputable section

namespace RenewalGeometry
namespace CertifiedSupportStratum

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]

/-- The support projection `supp(A)` of an operator: the orthogonal projection onto `Ran A`. -/
def supportProjection (A : E →ₗ[𝕜] E) : E →L[𝕜] E :=
  (LinearMap.range A).starProjection

/-- The right singular subspace of `A` for its `r` largest singular values: the spectral
subspace of `A^*A` on `[σ_r², ∞)` (`σ_r = singularValues (r - 1)`). -/
def rightSingularSubspace (A : E →ₗ[𝕜] H) (r : ℕ) : Submodule 𝕜 E :=
  spectralSubspace (LinearMap.adjoint A ∘ₗ A) (Set.Ici (A.singularValues (r - 1) ^ 2))

/-- The left singular subspace of `A` for its `r` largest singular values: the spectral
subspace of `AA^*` on `[σ_r², ∞)`. -/
def leftSingularSubspace (A : E →ₗ[𝕜] H) (r : ℕ) : Submodule 𝕜 H :=
  spectralSubspace (A ∘ₗ LinearMap.adjoint A) (Set.Ici (A.singularValues (r - 1) ^ 2))

/-- The right singular projector `p̂_r`. -/
def rightSingularProjector (A : E →ₗ[𝕜] H) (r : ℕ) : E →L[𝕜] E :=
  (rightSingularSubspace A r).starProjection

/-- The left singular projector `q̂_r`. -/
def leftSingularProjector (A : E →ₗ[𝕜] H) (r : ℕ) : H →L[𝕜] H :=
  (leftSingularSubspace A r).starProjection

theorem starProjection_congr {K K' : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [K'.HasOrthogonalProjection] (h : K = K') : K.starProjection = K'.starProjection := by
  subst h
  rfl

/-- `supp(A^*A) = P_{(ker A)ᗮ}`. -/
theorem supportProjection_adjoint_comp_self (A : E →ₗ[𝕜] H) :
    supportProjection (LinearMap.adjoint A ∘ₗ A) = (LinearMap.ker A)ᗮ.starProjection := by
  unfold supportProjection
  apply starProjection_congr
  rw [LinearMap.range_adjoint_comp_self, LinearMap.orthogonal_ker]

/-- `supp(AA^*) = P_{(ker A^*)ᗮ}`. -/
theorem supportProjection_self_comp_adjoint (A : E →ₗ[𝕜] H) :
    supportProjection (A ∘ₗ LinearMap.adjoint A) =
      (LinearMap.ker (LinearMap.adjoint A))ᗮ.starProjection := by
  unfold supportProjection
  apply starProjection_congr
  rw [LinearMap.range_self_comp_adjoint, LinearMap.orthogonal_ker, LinearMap.adjoint_adjoint]

theorem isSymmetric_self_comp_adjoint (A : E →ₗ[𝕜] H) :
    (A ∘ₗ LinearMap.adjoint A).IsSymmetric := by
  simpa using (LinearMap.adjoint A).isSymmetric_adjoint_comp_self

/-- **`thm:certified-support-stratum`, linear-map form.**  If `‖F̂ - F‖ ≤ ε` (pointwise operator
bound), `rank F ≤ r`, `r ≥ 1` and `σ̂_r > 2ε`, then `rank F = r`, both singular projectors of
`F̂` have rank `r`, and
`‖supp(F^*F) - p̂_r‖, ‖supp(FF^*) - q̂_r‖ ≤ ε / (σ̂_r - 2ε)`. -/
theorem certified_support_stratum_of_le (F Fh : E →ₗ[𝕜] H) {ε : ℝ} {r : ℕ} (hr : 0 < r)
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(Fh - F) x‖ ≤ ε * ‖x‖)
    (hrank : finrank 𝕜 (LinearMap.range F) ≤ r)
    (hgap : 2 * ε < Fh.singularValues (r - 1)) :
    finrank 𝕜 (LinearMap.range F) = r ∧
      finrank 𝕜 (rightSingularSubspace Fh r) = r ∧
      finrank 𝕜 (leftSingularSubspace Fh r) = r ∧
      ‖supportProjection (LinearMap.adjoint F ∘ₗ F) - rightSingularProjector Fh r‖ ≤
        ε / (Fh.singularValues (r - 1) - 2 * ε) ∧
      ‖supportProjection (F ∘ₗ LinearMap.adjoint F) - leftSingularProjector Fh r‖ ≤
        ε / (Fh.singularValues (r - 1) - 2 * ε) := by
  set σ := Fh.singularValues (r - 1) with hσ
  have hσ0 : 0 < σ := by linarith
  have hr1 : r - 1 < finrank 𝕜 E := by
    by_contra h
    rw [hσ, Fh.singularValues_of_finrank_le (not_lt.mp h)] at hσ0
    exact lt_irrefl _ hσ0
  set V := rightSingularSubspace Fh r with hVdef
  set W := leftSingularSubspace Fh r with hWdef
  -- right side
  have hV : r ≤ finrank 𝕜 V := by
    have := succ_le_finrank_Ici Fh hr1
    rw [Nat.sub_add_cancel hr] at this
    exact this
  have hinvV : ∀ v ∈ V, (LinearMap.adjoint Fh ∘ₗ Fh) v ∈ V := fun v hv =>
    apply_mem_spectralSubspace Fh.isSymmetric_adjoint_comp_self hv
  have hlowV : ∀ v ∈ V, σ * ‖v‖ ≤ ‖Fh v‖ := fun v hv =>
    le_norm_apply_of_mem_Ici Fh hσ0.le hv
  obtain ⟨hFr, hVr, hp⟩ :=
    support_projector_perturbation Fh F V hε0 hε hgap hrank hV hinvV hlowV
  -- left side
  have hT' := isSymmetric_self_comp_adjoint Fh
  have hεadj : ∀ y, ‖(LinearMap.adjoint Fh - LinearMap.adjoint F) y‖ ≤ ε * ‖y‖ := by
    intro y
    rw [← map_sub]
    exact norm_adjoint_apply_le (Fh - F) hε0 hε y
  have hrank' : finrank 𝕜 (LinearMap.range (LinearMap.adjoint F)) ≤ r := by
    rw [LinearMap.finrank_range_adjoint]
    exact hrank
  have hW : r ≤ finrank 𝕜 W := by
    let f : V →ₗ[𝕜] W := LinearMap.codRestrict W (Fh ∘ₗ V.subtype)
      (fun v => apply_mem_spectralSubspace_self_comp_adjoint Fh v.2)
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro v hv
      rw [LinearMap.mem_ker] at hv
      have hfapply : ((f v : W) : H) = Fh (v : E) := rfl
      have h0 : Fh (v : E) = 0 := by
        rw [← hfapply, hv]
        rfl
      have h1 := hlowV v v.2
      rw [h0, norm_zero] at h1
      have : ‖(v : E)‖ = 0 := by
        have := norm_nonneg (v : E)
        nlinarith
      rw [Submodule.mem_bot]
      exact Subtype.ext (by simpa using this)
    have := LinearMap.finrank_le_finrank_of_injective hf
    omega
  have hinvW : ∀ w ∈ W,
      (LinearMap.adjoint (LinearMap.adjoint Fh) ∘ₗ LinearMap.adjoint Fh) w ∈ W := by
    intro w hw
    rw [LinearMap.adjoint_adjoint]
    exact apply_mem_spectralSubspace hT' hw
  have hlowW : ∀ w ∈ W, σ * ‖w‖ ≤ ‖LinearMap.adjoint Fh w‖ := by
    intro w hw
    have h := le_re_inner_of_mem hT' (a := σ ^ 2) (fun μ hμ _ => hμ) hw
    have hq : RCLike.re ⟪w, (Fh ∘ₗ LinearMap.adjoint Fh) w⟫_𝕜 =
        ‖LinearMap.adjoint Fh w‖ ^ 2 := by
      rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
    rw [hq, ← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h
  obtain ⟨-, hWr, hq⟩ := support_projector_perturbation (LinearMap.adjoint Fh)
    (LinearMap.adjoint F) W hε0 hεadj hgap hrank' hW hinvW hlowW
  refine ⟨hFr, hVr, hWr, ?_, ?_⟩
  · rw [supportProjection_adjoint_comp_self]
    exact hp
  · rw [supportProjection_self_comp_adjoint]
    exact hq

/-- The Hilbert–Schmidt norm (computed in any orthonormal basis) dominates the operator norm. -/
theorem opNorm_le_of_sum_norm_sq_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    (T : E →L[𝕜] H) {ε : ℝ} (hε0 : 0 ≤ ε) (hHS : ∑ i, ‖T (b i)‖ ^ 2 ≤ ε ^ 2) :
    ‖T‖ ≤ ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ hε0 fun x => ?_
  have hx : T x = ∑ i, b.repr x i • T (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    simp [map_smul]
  have h1 : ‖T x‖ ≤ ∑ i, ‖b.repr x i‖ * ‖T (b i)‖ := by
    rw [hx]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_smul]
  have h2 : (∑ i, ‖b.repr x i‖ * ‖T (b i)‖) ^ 2 ≤
      (∑ i, ‖b.repr x i‖ ^ 2) * (∑ i, ‖T (b i)‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]
  rw [h3] at h2
  have h4 : ‖T x‖ ^ 2 ≤ (ε * ‖x‖) ^ 2 := by
    calc ‖T x‖ ^ 2 ≤ (∑ i, ‖b.repr x i‖ * ‖T (b i)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ ‖x‖ ^ 2 * (∑ i, ‖T (b i)‖ ^ 2) := h2
      _ ≤ ‖x‖ ^ 2 * ε ^ 2 := mul_le_mul_of_nonneg_left hHS (sq_nonneg _)
      _ = (ε * ‖x‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4

/-- **`thm:certified-support-stratum`** (operator-norm hypothesis).  Let `F, F̂ : E → H` with
`‖F̂ - F‖_op ≤ ε`, `rank F ≤ r`, `r ≥ 1`, and `σ̂_r > 2ε`.  Then `rank F = r`, the right and
left singular projectors `p̂_r, q̂_r` of `F̂` for its `r` largest singular values have rank `r`,
and with `p = supp(F^*F)`, `q = supp(FF^*)`,
`‖p - p̂_r‖_op, ‖q - q̂_r‖_op ≤ ε / (σ̂_r - 2ε)`. -/
theorem certified_support_stratum (F Fh : E →L[𝕜] H) {ε : ℝ} {r : ℕ} (hr : 0 < r)
    (hε : ‖Fh - F‖ ≤ ε) (hrank : finrank 𝕜 (LinearMap.range (F : E →ₗ[𝕜] H)) ≤ r)
    (hgap : 2 * ε < (Fh : E →ₗ[𝕜] H).singularValues (r - 1)) :
    finrank 𝕜 (LinearMap.range (F : E →ₗ[𝕜] H)) = r ∧
      finrank 𝕜 (rightSingularSubspace (Fh : E →ₗ[𝕜] H) r) = r ∧
      finrank 𝕜 (leftSingularSubspace (Fh : E →ₗ[𝕜] H) r) = r ∧
      ‖supportProjection (LinearMap.adjoint (F : E →ₗ[𝕜] H) ∘ₗ (F : E →ₗ[𝕜] H)) -
          rightSingularProjector (Fh : E →ₗ[𝕜] H) r‖ ≤
        ε / ((Fh : E →ₗ[𝕜] H).singularValues (r - 1) - 2 * ε) ∧
      ‖supportProjection ((F : E →ₗ[𝕜] H) ∘ₗ LinearMap.adjoint (F : E →ₗ[𝕜] H)) -
          leftSingularProjector (Fh : E →ₗ[𝕜] H) r‖ ≤
        ε / ((Fh : E →ₗ[𝕜] H).singularValues (r - 1) - 2 * ε) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  refine certified_support_stratum_of_le (F : E →ₗ[𝕜] H) (Fh : E →ₗ[𝕜] H) hr hε0
    (fun x => ?_) hrank hgap
  have : ((Fh : E →ₗ[𝕜] H) - (F : E →ₗ[𝕜] H)) x = (Fh - F) x := rfl
  rw [this]
  exact ((Fh - F).le_opNorm x).trans (mul_le_mul_of_nonneg_right hε (norm_nonneg _))

/-- **`thm:certified-support-stratum`, Hilbert–Schmidt variant.**  The same conclusions under
`‖F̂ - F‖_HS ≤ ε`, the Hilbert–Schmidt norm computed in an orthonormal basis `b` of `E`. -/
theorem certified_support_stratum_hilbertSchmidt {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) (F Fh : E →L[𝕜] H) {ε : ℝ} {r : ℕ} (hr : 0 < r)
    (hε0 : 0 ≤ ε) (hHS : ∑ i, ‖(Fh - F) (b i)‖ ^ 2 ≤ ε ^ 2)
    (hrank : finrank 𝕜 (LinearMap.range (F : E →ₗ[𝕜] H)) ≤ r)
    (hgap : 2 * ε < (Fh : E →ₗ[𝕜] H).singularValues (r - 1)) :
    finrank 𝕜 (LinearMap.range (F : E →ₗ[𝕜] H)) = r ∧
      finrank 𝕜 (rightSingularSubspace (Fh : E →ₗ[𝕜] H) r) = r ∧
      finrank 𝕜 (leftSingularSubspace (Fh : E →ₗ[𝕜] H) r) = r ∧
      ‖supportProjection (LinearMap.adjoint (F : E →ₗ[𝕜] H) ∘ₗ (F : E →ₗ[𝕜] H)) -
          rightSingularProjector (Fh : E →ₗ[𝕜] H) r‖ ≤
        ε / ((Fh : E →ₗ[𝕜] H).singularValues (r - 1) - 2 * ε) ∧
      ‖supportProjection ((F : E →ₗ[𝕜] H) ∘ₗ LinearMap.adjoint (F : E →ₗ[𝕜] H)) -
          leftSingularProjector (Fh : E →ₗ[𝕜] H) r‖ ≤
        ε / ((Fh : E →ₗ[𝕜] H).singularValues (r - 1) - 2 * ε) :=
  certified_support_stratum F Fh hr (opNorm_le_of_sum_norm_sq_le b _ hε0 hHS) hrank hgap

/-- Non-vacuity: the hypotheses of `certified_support_stratum` hold for `F = F̂ = id` on `ℂ`,
`ε = 0`, `r = 1`. -/
example : finrank ℂ (LinearMap.range ((ContinuousLinearMap.id ℂ ℂ : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ)) = 1 :=
  (certified_support_stratum (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ ℂ)
    (ε := 0) (r := 1) one_pos (by simp)
    (by rw [ContinuousLinearMap.coe_id, LinearMap.range_id, finrank_top, Module.finrank_self])
    (by
      rw [mul_zero]
      refine (LinearMap.singularValues_pos_iff_lt_finrank_range _).mpr ?_
      rw [ContinuousLinearMap.coe_id, LinearMap.range_id, finrank_top, Module.finrank_self]
      norm_num)).1

end CertifiedSupportStratum
end RenewalGeometry
