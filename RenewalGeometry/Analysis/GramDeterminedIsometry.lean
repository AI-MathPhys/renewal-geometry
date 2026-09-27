/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
/-!
# Generating families with equal Gram data are unitarily equivalent

Infrastructure for `thm:supp-Naimark-realization` (`eq:supp-Naimark-unitary`) of
`papers/predictive_spectral_geometry`, in the general Hilbert-space form:

Let `g₁ : ι → K₁` and `g₂ : ι → K₂` be families in Hilbert spaces whose closed spans are the whole
spaces and whose Gram data agree, `⟪g₁ i, g₁ j⟫ = ⟪g₂ i, g₂ j⟫`.  Then there is a **unique**
unitary `U : K₁ ≃ₗᵢ[ℂ] K₂` with `U (g₁ i) = g₂ i` (`GramIsometry.existsUnique_linearIsometryEquiv`).

The construction: on finite linear combinations `Σ cᵢ g₁ i ↦ Σ cᵢ g₂ i` is well defined because the
two squared norms agree (`inner_comb`), it is an isometry on the algebraic span (`partialIsometry`),
it extends by continuity to the closure (`ContinuousLinearMap.extend`), and the extension from the
symmetric construction is its inverse (`toLinearIsometryEquiv`).  Uniqueness is agreement on a
generating family plus density (`ContinuousLinearMap.ext_on`).
-/

open scoped InnerProductSpace

namespace RenewalGeometry
namespace GramIsometry

variable {ι : Type*} {K₁ K₂ : Type*}
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]

/-- Finite linear combinations `c ↦ Σᵢ cᵢ g i` of a family. -/
noncomputable abbrev comb {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (g : ι → K) :
    (ι →₀ ℂ) →ₗ[ℂ] K := Finsupp.linearCombination ℂ g

theorem comb_single {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (g : ι → K) (i : ι) :
    comb g (Finsupp.single i (1 : ℂ)) = g i := by
  simp [comb, Finsupp.linearCombination_single]

theorem range_comb {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (g : ι → K) :
    LinearMap.range (comb g) = Submodule.span ℂ (Set.range g) :=
  Finsupp.range_linearCombination ℂ

/-- The inner product of two finite combinations depends only on the Gram data. -/
theorem inner_comb {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (g : ι → K)
    (c d : ι →₀ ℂ) :
    ⟪comb g c, comb g d⟫_ℂ =
      ∑ i ∈ c.support, ∑ j ∈ d.support, (starRingEnd ℂ) (c i) * d j * ⟪g i, g j⟫_ℂ := by
  simp only [comb, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum]
  first
  | (refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring)
  | (rw [Finset.sum_comm]
     refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
     ring)

section Gram

variable {g₁ : ι → K₁} {g₂ : ι → K₂} (hG : ∀ i j, ⟪g₁ i, g₁ j⟫_ℂ = ⟪g₂ i, g₂ j⟫_ℂ)
include hG

theorem inner_comb_eq (c d : ι →₀ ℂ) : ⟪comb g₁ c, comb g₁ d⟫_ℂ = ⟪comb g₂ c, comb g₂ d⟫_ℂ := by
  rw [inner_comb, inner_comb]
  simp only [hG]

theorem norm_comb_eq (c : ι →₀ ℂ) : ‖comb g₁ c‖ = ‖comb g₂ c‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, inner_comb_eq hG]

theorem ker_comb_le : LinearMap.ker (comb g₁) ≤ LinearMap.ker (comb g₂) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  rw [← norm_eq_zero, ← norm_comb_eq hG, hc, norm_zero]

/-- The map `Σ cᵢ g₁ i ↦ Σ cᵢ g₂ i` on the algebraic span of `g₁`. -/
noncomputable def partialMap : LinearMap.range (comb g₁) →ₗ[ℂ] K₂ :=
  (Submodule.liftQ (LinearMap.ker (comb g₁)) (comb g₂) (ker_comb_le hG)) ∘ₗ
    (LinearMap.quotKerEquivRange (comb g₁)).symm.toLinearMap

theorem partialMap_apply (c : ι →₀ ℂ) :
    partialMap hG ⟨comb g₁ c, LinearMap.mem_range_self _ c⟩ = comb g₂ c := by
  unfold partialMap
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply]

theorem norm_partialMap (x : LinearMap.range (comb g₁)) : ‖partialMap hG x‖ = ‖x‖ := by
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp x.2
  have hx : x = ⟨comb g₁ c, LinearMap.mem_range_self _ c⟩ := Subtype.ext hc.symm
  rw [hx, partialMap_apply hG, ← norm_comb_eq hG]
  rfl

/-- The isometry `Σ cᵢ g₁ i ↦ Σ cᵢ g₂ i` on the algebraic span of `g₁`. -/
noncomputable def partialIsometry : LinearMap.range (comb g₁) →ₗᵢ[ℂ] K₂ where
  toLinearMap := partialMap hG
  norm_map' := norm_partialMap hG

theorem partialIsometry_apply (c : ι →₀ ℂ) :
    partialIsometry hG ⟨comb g₁ c, LinearMap.mem_range_self _ c⟩ = comb g₂ c :=
  partialMap_apply hG c

/-- The continuous extension of the partial isometry to `K₁`. -/
noncomputable def extended : K₁ →L[ℂ] K₂ :=
  ContinuousLinearMap.extend (partialIsometry hG).toContinuousLinearMap
    (LinearMap.range (comb g₁)).subtypeL

variable (h₁ : (Submodule.span ℂ (Set.range g₁)).topologicalClosure = ⊤)
include h₁

theorem denseRange_subtypeL : DenseRange (LinearMap.range (comb g₁)).subtypeL := by
  rw [Submodule.coe_subtypeL, Submodule.coe_subtype]
  apply Dense.denseRange_val
  rw [range_comb]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr h₁

omit h₁ in
theorem isUniformInducing_subtypeL : IsUniformInducing (LinearMap.range (comb g₁)).subtypeL := by
  rw [Submodule.coe_subtypeL, Submodule.coe_subtype]
  exact isUniformEmbedding_subtype_val.isUniformInducing

theorem extended_apply (c : ι →₀ ℂ) : extended hG (comb g₁ c) = comb g₂ c := by
  have h := ContinuousLinearMap.extend_eq (partialIsometry hG).toContinuousLinearMap
    (denseRange_subtypeL hG h₁) (isUniformInducing_subtypeL hG)
    ⟨comb g₁ c, LinearMap.mem_range_self _ c⟩
  rw [Submodule.subtypeL_apply] at h
  exact h.trans (partialIsometry_apply hG c)

theorem extended_gen (i : ι) : extended hG (g₁ i) = g₂ i := by
  rw [← comb_single g₁ i, extended_apply hG h₁, comb_single]

theorem norm_extended (x : K₁) : ‖extended hG x‖ = ‖x‖ := by
  refine (denseRange_subtypeL hG h₁).induction_on x ?_ fun y => ?_
  · exact isClosed_eq (continuous_norm.comp (extended hG).continuous) continuous_norm
  · obtain ⟨c, hc⟩ := LinearMap.mem_range.mp y.2
    rw [Submodule.subtypeL_apply, ← hc, extended_apply hG h₁, norm_comb_eq hG]

/-- The isometry `K₁ → K₂` sending `g₁ i` to `g₂ i`. -/
noncomputable def toLinearIsometry : K₁ →ₗᵢ[ℂ] K₂ where
  toLinearMap := (extended hG).toLinearMap
  norm_map' := norm_extended hG h₁

theorem toLinearIsometry_apply (x : K₁) : toLinearIsometry hG h₁ x = extended hG x := rfl

theorem toLinearIsometry_gen (i : ι) : toLinearIsometry hG h₁ (g₁ i) = g₂ i := extended_gen hG h₁ i

end Gram

/-- **Uniqueness**: two continuous linear maps agreeing on a family with dense span agree. -/
theorem clm_ext_of_forall_gen {g₁ : ι → K₁}
    (h₁ : (Submodule.span ℂ (Set.range g₁)).topologicalClosure = ⊤) {T T' : K₁ →L[ℂ] K₂}
    (h : ∀ i, T (g₁ i) = T' (g₁ i)) : T = T' := by
  refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr h₁) ?_
  rintro _ ⟨i, rfl⟩
  exact h i

theorem linearIsometryEquiv_ext_of_forall_gen {g₁ : ι → K₁}
    (h₁ : (Submodule.span ℂ (Set.range g₁)).topologicalClosure = ⊤) {U U' : K₁ ≃ₗᵢ[ℂ] K₂}
    (h : ∀ i, U (g₁ i) = U' (g₁ i)) : U = U' := by
  have hT : (U.toLinearIsometry.toContinuousLinearMap : K₁ →L[ℂ] K₂) =
      U'.toLinearIsometry.toContinuousLinearMap := clm_ext_of_forall_gen h₁ h
  ext x
  have := congrArg (fun T : K₁ →L[ℂ] K₂ => T x) hT
  simpa using this

section Equiv

variable {g₁ : ι → K₁} {g₂ : ι → K₂} (hG : ∀ i j, ⟪g₁ i, g₁ j⟫_ℂ = ⟪g₂ i, g₂ j⟫_ℂ)
  (h₁ : (Submodule.span ℂ (Set.range g₁)).topologicalClosure = ⊤)
  (h₂ : (Submodule.span ℂ (Set.range g₂)).topologicalClosure = ⊤)
include hG h₁ h₂

theorem hG_symm : ∀ i j, ⟪g₂ i, g₂ j⟫_ℂ = ⟪g₁ i, g₁ j⟫_ℂ := fun i j => (hG i j).symm

theorem toLinearIsometry_surjective : Function.Surjective (toLinearIsometry hG h₁) := by
  intro y
  refine ⟨toLinearIsometry (hG_symm hG h₁ h₂) h₂ y, ?_⟩
  have hT : ((toLinearIsometry hG h₁).toContinuousLinearMap ∘L
      (toLinearIsometry (hG_symm hG h₁ h₂) h₂).toContinuousLinearMap) =
      ContinuousLinearMap.id ℂ K₂ := by
    refine clm_ext_of_forall_gen h₂ fun i => ?_
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      ContinuousLinearMap.id_apply]
    rw [toLinearIsometry_gen, toLinearIsometry_gen]
  have := congrArg (fun T : K₂ →L[ℂ] K₂ => T y) hT
  simpa using this

/-- **The unitary `K₁ ≃ K₂` determined by matching Gram data on generating families.** -/
noncomputable def toLinearIsometryEquiv : K₁ ≃ₗᵢ[ℂ] K₂ :=
  LinearIsometryEquiv.ofSurjective (toLinearIsometry hG h₁) (toLinearIsometry_surjective hG h₁ h₂)

theorem toLinearIsometryEquiv_gen (i : ι) : toLinearIsometryEquiv hG h₁ h₂ (g₁ i) = g₂ i := by
  unfold toLinearIsometryEquiv
  rw [LinearIsometryEquiv.coe_ofSurjective]
  exact toLinearIsometry_gen hG h₁ i

/-- **Generating families with equal Gram data are related by a unique unitary**
(the abstract form of `eq:supp-Naimark-unitary`). -/
theorem existsUnique_linearIsometryEquiv :
    ∃! U : K₁ ≃ₗᵢ[ℂ] K₂, ∀ i, U (g₁ i) = g₂ i := by
  refine ⟨toLinearIsometryEquiv hG h₁ h₂, toLinearIsometryEquiv_gen hG h₁ h₂, fun U hU => ?_⟩
  exact linearIsometryEquiv_ext_of_forall_gen h₁ fun i => by
    rw [hU i, toLinearIsometryEquiv_gen hG h₁ h₂]

end Equiv

end GramIsometry
end RenewalGeometry
