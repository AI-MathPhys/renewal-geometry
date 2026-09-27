/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.MemoryCutoffSemigroupMeasureExact
import RenewalGeometry.Spectralization.OperatorTailMeasureNaimarkUniquenessExact
/-!
# Head compression of positive tail measures and the source rank of the minimal dilation

Infrastructure for `thm:supp-fibre-RG` of `papers/predictive_spectral_geometry` (the memory
component `(A, μ) ↦ (W^*(A - Q_{>Λ})W, W^* μ|_{(0,Λ]} W)` of `eq:supp-U-map` and the clause
"minimal dilation rank cannot increase").

* `conjCLM W : M ↦ Wᴴ M W`, the head compression of matrices as a continuous real-linear map;
  `PositiveTailMeasure.compress W μ = W^* μ W` is again a positive tail measure.
* Compression commutes with the cutoff (`compress_cutoff`), with the operator integrals
  (`integral_mapRange_conjCLM`), hence with the self-energy (`stieltjesSelfEnergy_compress`), the
  head correction (`headCorrection_compress`) and the memory RG step (`rg_compress`); compressions
  compose (`compress_compress`); for an isometric `W` the dynamic function of the compressed data is
  the compressed dynamic function (`dynamicFunction_compress`).
* **Source rank of the minimal dilation.**  `sourceRank μ = rank μ((0,∞))` equals the rank of the
  source map `V = B^*` of every minimal realization of `μ` (`IsMinimalRealization.finrank_range_eq`),
  in particular of the canonical `V_μ : H → K_μ`.  It cannot increase under compression
  (`sourceRank_compress_le`) nor under a memory cutoff (`sourceRank_cutoff_le`).
-/

open MeasureTheory Set
open scoped InnerProductSpace ComplexOrder Matrix

namespace RenewalGeometry
namespace OperatorTailMeasure

variable {H H' H'' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
  [Fintype H''] [DecidableEq H'']

/-! ## The head compression of matrices -/

/-- `M ↦ Wᴴ M W` as a continuous real-linear map `(H → H → ℂ) → (H' → H' → ℂ)`. -/
noncomputable def conjCLM (W : Matrix H H' ℂ) : (H → H → ℂ) →L[ℝ] (H' → H' → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Matrix.of.symm (Wᴴ * Matrix.of M * W)
      map_add' := fun M N => by
        rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.add_mul]
        rfl
      map_smul' := fun c M => by
        rw [← Matrix.smul_of, Matrix.mul_smul, Matrix.smul_mul]
        rfl }

@[simp]
theorem conjCLM_apply (W : Matrix H H' ℂ) (M : H → H → ℂ) :
    conjCLM W M = Matrix.of.symm (Wᴴ * Matrix.of M * W) := rfl

theorem of_conjCLM (W : Matrix H H' ℂ) (M : H → H → ℂ) :
    Matrix.of (conjCLM W M) = Wᴴ * Matrix.of M * W := rfl

/-- The compression is complex-linear. -/
theorem conjCLM_smul (W : Matrix H H' ℂ) (c : ℂ) (M : H → H → ℂ) :
    conjCLM W (c • M) = c • conjCLM W M := by
  change Matrix.of.symm (Wᴴ * Matrix.of (c • M) * W) = c • Matrix.of.symm (Wᴴ * Matrix.of M * W)
  rw [← Matrix.smul_of, Matrix.mul_smul, Matrix.smul_mul]
  rfl

theorem conjCLM_conjCLM (W₁ : Matrix H H' ℂ) (W₂ : Matrix H' H'' ℂ) (M : H → H → ℂ) :
    conjCLM W₂ (conjCLM W₁ M) = conjCLM (W₁ * W₂) M := by
  simp only [conjCLM_apply, Equiv.apply_symm_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-! ## Compressed vector measures and their integrals -/

/-- The push-forward of a vector measure along a continuous linear map, evaluated. -/
theorem mapRange_clm_apply {X F F' : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] (ν : VectorMeasure X F)
    (L : F →L[ℝ] F') (s : Set X) :
    ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous s = L (ν s) := rfl

/-- The variation of a vector measure pushed forward by a continuous linear map is dominated by
the operator norm times the variation. -/
theorem variation_mapRange_le {X F F' : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] (ν : VectorMeasure X F)
    (L : F →L[ℝ] F') :
    (ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous).variation ≤ ‖L‖₊ • ν.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le (fun s _ => ?_)
  rw [mapRange_clm_apply]
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  calc ‖L (ν s)‖ₑ ≤ ‖L‖ₑ * ‖ν s‖ₑ := L.le_opENorm _
    _ ≤ ‖L‖ₑ * ν.variation s := by
        gcongr
        exact VectorMeasure.enorm_measure_le_variation ν s
    _ = ↑‖L‖₊ * ν.variation s := by rw [enorm_eq_nnnorm]

theorem integrable_mapRange {X F F' : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] (ν : VectorMeasure X F)
    (L : F →L[ℝ] F') {f : X → ℂ} (hf : Integrable f ν.variation) :
    Integrable f (ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous).variation := by
  have h1 : Integrable f (‖L‖₊ • ν.variation) := hf.smul_measure_nnreal
  exact h1.mono_measure (variation_mapRange_le ν L)

/-- The operator integral against a compressed measure is the compressed operator integral. -/
theorem integral_mapRange_conjCLM (W : Matrix H H' ℂ) (ν : VectorMeasure ℝ (H → H → ℂ))
    {f : ℝ → ℂ} (hf : Integrable f ν.variation) :
    VectorMeasure.integral (ν.mapRange (conjCLM W).toLinearMap.toAddMonoidHom (conjCLM W).continuous)
        f (ContinuousLinearMap.lsmul ℝ ℂ) =
      conjCLM W (VectorMeasure.integral ν f (ContinuousLinearMap.lsmul ℝ ℂ)) := by
  rw [VectorMeasure.continuousLinearMap_apply_integral hf,
    VectorMeasure.integral_eq_setToFun_transpose (integrable_mapRange ν (conjCLM W) hf),
    VectorMeasure.integral_eq_setToFun_transpose hf]
  have hT : (ν.mapRange (conjCLM W).toLinearMap.toAddMonoidHom (conjCLM W).continuous).transpose
      (ContinuousLinearMap.lsmul ℝ ℂ) =
      ν.transpose ((ContinuousLinearMap.compL ℝ (H → H → ℂ) (H → H → ℂ) (H' → H' → ℂ) (conjCLM W)) ∘L
        ContinuousLinearMap.lsmul ℝ ℂ) := by
    refine VectorMeasure.ext fun s hs => ?_
    refine ContinuousLinearMap.ext fun c => ?_
    change c • conjCLM W (ν s) = conjCLM W (c • ν s)
    rw [conjCLM_smul]
  simp only [hT]

/-- Restriction commutes with the push-forward. -/
theorem mapRange_restrict {X F F' : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] (ν : VectorMeasure X F)
    (L : F →L[ℝ] F') {s : Set X} (hs : MeasurableSet s) :
    (ν.restrict s).mapRange L.toLinearMap.toAddMonoidHom L.continuous =
      (ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous).restrict s := by
  refine VectorMeasure.ext fun t ht => ?_
  rw [mapRange_clm_apply, VectorMeasure.restrict_apply _ hs ht,
    VectorMeasure.restrict_apply _ hs ht, mapRange_clm_apply]

/-! ## Compressed positive tail measures -/

namespace PositiveTailMeasure

variable (μ : PositiveTailMeasure H)

/-- **Head compression `W^* μ W`** of a positive tail measure along `W : H' → H`. -/
noncomputable def compress (W : Matrix H H' ℂ) : PositiveTailMeasure H' where
  toVectorMeasure :=
    μ.toVectorMeasure.mapRange (conjCLM W).toLinearMap.toAddMonoidHom (conjCLM W).continuous
  posSemidef s hs := by
    rw [mapRange_clm_apply]
    exact (μ.posSemidef s hs).conjTranspose_mul_mul_same W
  eq_zero_of_subset_Iic s hs hsub := by
    rw [mapRange_clm_apply, μ.eq_zero_of_subset_Iic s hs hsub, map_zero]

theorem compress_toVectorMeasure (W : Matrix H H' ℂ) :
    (μ.compress W).toVectorMeasure =
      μ.toVectorMeasure.mapRange (conjCLM W).toLinearMap.toAddMonoidHom (conjCLM W).continuous :=
  rfl

theorem compress_apply (W : Matrix H H' ℂ) (s : Set ℝ) :
    (μ.compress W).toVectorMeasure s = conjCLM W (μ.toVectorMeasure s) := rfl

theorem of_compress_apply (W : Matrix H H' ℂ) (s : Set ℝ) :
    Matrix.of ((μ.compress W).toVectorMeasure s) = Wᴴ * Matrix.of (μ.toVectorMeasure s) * W := rfl

/-- Compressions compose: `W₂^* (W₁^* μ W₁) W₂ = (W₁ W₂)^* μ (W₁ W₂)`. -/
theorem compress_compress (W₁ : Matrix H H' ℂ) (W₂ : Matrix H' H'' ℂ) :
    (μ.compress W₁).compress W₂ = μ.compress (W₁ * W₂) := by
  rw [ext_iff']
  refine VectorMeasure.ext fun s _ => ?_
  rw [compress_apply, compress_apply, compress_apply, conjCLM_conjCLM]

/-- Compression commutes with the memory cutoff. -/
theorem compress_cutoff (W : Matrix H H' ℂ) (Λ : ℝ) :
    (μ.compress W).cutoff Λ = (μ.cutoff Λ).compress W := by
  rw [ext_iff', cutoff_toVectorMeasure, compress_toVectorMeasure, compress_toVectorMeasure,
    cutoff_toVectorMeasure, mapRange_restrict _ _ measurableSet_Iic]

theorem integrable_compress (W : Matrix H H' ℂ) {f : ℝ → ℂ}
    (hf : Integrable f μ.toVectorMeasure.variation) :
    Integrable f (μ.compress W).toVectorMeasure.variation :=
  integrable_mapRange _ _ hf

/-- The self-energy of the compressed measure is the compressed self-energy. -/
theorem stieltjesSelfEnergy_compress (W : Matrix H H' ℂ) {z : ℂ} (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) :
    (μ.compress W).stieltjesSelfEnergy z = Wᴴ * μ.stieltjesSelfEnergy z * W := by
  unfold stieltjesSelfEnergy
  rw [compress_toVectorMeasure, integral_mapRange_conjCLM _ _ (μ.integrable_resolvent hz)]
  rfl

/-- The head correction of the compressed measure is the compressed head correction. -/
theorem headCorrection_compress (W : Matrix H H' ℂ) {Λ : ℝ} (hΛ : 0 < Λ) :
    (μ.compress W).headCorrection Λ = Wᴴ * μ.headCorrection Λ * W := by
  unfold headCorrection
  rw [compress_toVectorMeasure, ← mapRange_restrict _ _ measurableSet_Ioi,
    integral_mapRange_conjCLM _ _ (μ.integrableOn_inv_Ioi hΛ)]
  rfl

/-- **Compression commutes with the memory RG step**: `RG_Λ(W^*AW, W^*μW) = W^* RG_Λ(A, μ) W`. -/
theorem rg_compress (W : Matrix H H' ℂ) (A : Matrix H H ℂ) {Λ : ℝ} (hΛ : 0 < Λ) :
    (μ.compress W).rg (Wᴴ * A * W) Λ =
      (Wᴴ * (μ.rg A Λ).1 * W, (μ.rg A Λ).2.compress W) := by
  simp only [rg]
  refine Prod.ext ?_ (μ.compress_cutoff W Λ)
  show Wᴴ * A * W - (μ.compress W).headCorrection Λ = Wᴴ * (A - μ.headCorrection Λ) * W
  rw [μ.headCorrection_compress W hΛ, Matrix.mul_sub, Matrix.sub_mul]

/-- For an isometric head map `W` (`Wᴴ W = 1`), the dynamic function of the compressed data is the
compressed dynamic function: `F_{W^*AW, W^*μW}(z) = W^* F_{A,μ}(z) W`. -/
theorem dynamicFunction_compress (W : Matrix H H' ℂ) (hW : Wᴴ * W = 1) (A : Matrix H H ℂ) {z : ℂ}
    (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) :
    (μ.compress W).dynamicFunction (Wᴴ * A * W) z = Wᴴ * μ.dynamicFunction A z * W := by
  unfold dynamicFunction
  rw [μ.stieltjesSelfEnergy_compress W hz, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hW]

/-! ## The source rank of the minimal dilation -/

/-- **The source rank**: the rank of the total mass `μ((0,∞)) = B_μ B_μ^*`, i.e. the rank of the
source map `B_μ^* = V_μ : H → K_μ` of the minimal dilation (`finrank_range_eq`). -/
noncomputable def sourceRank : ℕ := μ.totalMass.rank

theorem totalMass_compress (W : Matrix H H' ℂ) :
    (μ.compress W).totalMass = Wᴴ * μ.totalMass * W := rfl

/-- **Compression cannot increase the source rank** (`thm:supp-fibre-RG`). -/
theorem sourceRank_compress_le (W : Matrix H H' ℂ) : (μ.compress W).sourceRank ≤ μ.sourceRank := by
  unfold sourceRank
  rw [totalMass_compress]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- A positive semidefinite summand cannot lower the rank: `rank A ≤ rank (A + C)` for `A, C ⪰ 0`. -/
theorem rank_le_rank_add_of_posSemidef {A C : Matrix H H ℂ} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    A.rank ≤ (A + C).rank := by
  have hker : LinearMap.ker (A + C).mulVecLin ≤ LinearMap.ker A.mulVecLin := by
    intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
    have h0 : star x ⬝ᵥ A *ᵥ x + star x ⬝ᵥ C *ᵥ x = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, hx, dotProduct_zero]
    have hA0 : star x ⬝ᵥ A *ᵥ x = 0 :=
      (add_eq_zero_iff_of_nonneg ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 x)
        ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hC).2 x)).mp h0 |>.1
    exact (hA.dotProduct_mulVec_zero_iff x).mp hA0
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker (A + C).mulVecLin
  have h3 := Submodule.finrank_mono hker
  unfold Matrix.rank
  omega

theorem totalMass_cutoff (Λ : ℝ) :
    (μ.cutoff Λ).totalMass = Matrix.of (μ.toVectorMeasure (Ioi 0 ∩ Iic Λ)) := by
  unfold totalMass
  rw [cutoff_toVectorMeasure, VectorMeasure.restrict_apply _ measurableSet_Iic measurableSet_Ioi]

/-- **The memory cutoff cannot increase the source rank.** -/
theorem sourceRank_cutoff_le (Λ : ℝ) : (μ.cutoff Λ).sourceRank ≤ μ.sourceRank := by
  unfold sourceRank
  rw [totalMass_cutoff]
  have hsplit : μ.toVectorMeasure (Ioi 0) =
      μ.toVectorMeasure (Ioi 0 ∩ Iic Λ) + μ.toVectorMeasure (Ioi 0 ∩ (Iic Λ)ᶜ) := by
    rw [← VectorMeasure.of_union ((disjoint_compl_right (a := Iic Λ)).mono
      Set.inter_subset_right Set.inter_subset_right) (measurableSet_Ioi.inter measurableSet_Iic)
      (measurableSet_Ioi.inter measurableSet_Iic.compl), Set.inter_union_compl]
  unfold totalMass
  rw [hsplit]
  exact rank_le_rank_add_of_posSemidef (μ.posSemidef _ (measurableSet_Ioi.inter measurableSet_Iic))
    (μ.posSemidef _ (measurableSet_Ioi.inter measurableSet_Iic.compl))

end PositiveTailMeasure

/-! ## The source rank as the rank of the source map of any minimal realization -/

namespace IsMinimalRealization

variable {μ : PositiveTailMeasure H} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] {P : ∀ s : Set ℝ, MeasurableSet s → K →L[ℂ] K}
  {V : EuclideanSpace ℂ H →L[ℂ] K} (h : IsMinimalRealization μ P V)

include h

/-- `μ((-∞,0] ∪ (0,∞)) = μ((0,∞))`. -/
theorem toVectorMeasure_univ_eq (μ : PositiveTailMeasure H) :
    μ.toVectorMeasure univ = μ.toVectorMeasure (Ioi 0) := by
  have := VectorMeasure.of_union (v := μ.toVectorMeasure) (A := Iic 0) (B := Ioi 0)
    (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Iic measurableSet_Ioi
  rw [Set.Iic_union_Ioi, μ.eq_zero_of_subset_Iic _ measurableSet_Iic le_rfl, zero_add] at this
  exact this

/-- `⟪V ξ, V η⟫ = ⟪ξ, μ((0,∞)) η⟫`. -/
theorem inner_source_source (ξ η : EuclideanSpace ℂ H) :
    ⟪V ξ, V η⟫_ℂ = ⟪ξ, Matrix.toEuclideanLin μ.totalMass η⟫_ℂ := by
  have := h.inner_eq univ MeasurableSet.univ ξ η
  rw [h.isSpectralMeasure.univ, ContinuousLinearMap.id_apply] at this
  rw [this]
  unfold PositiveTailMeasure.totalMass
  rw [toVectorMeasure_univ_eq h μ]

/-- The kernel of the source map is the kernel of the total mass. -/
theorem ker_source_eq :
    LinearMap.ker (V : EuclideanSpace ℂ H →ₗ[ℂ] K) =
      (LinearMap.ker μ.totalMass.mulVecLin).comap (WithLp.linearEquiv 2 ℂ (H → ℂ)).toLinearMap := by
  ext ξ
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_comap,
    LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
  have hpos := μ.posSemidef (Ioi 0) measurableSet_Ioi
  have key : ⟪V ξ, V ξ⟫_ℂ = star (WithLp.ofLp ξ) ⬝ᵥ μ.totalMass *ᵥ WithLp.ofLp ξ := by
    rw [h.inner_source_source, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply,
      dotProduct_comm]
  constructor
  · intro hV
    have h0 : star (WithLp.ofLp ξ) ⬝ᵥ μ.totalMass *ᵥ WithLp.ofLp ξ = 0 := by
      rw [← key, hV, inner_zero_left]
    exact (hpos.dotProduct_mulVec_zero_iff _).mp h0
  · intro hM
    rw [← inner_self_eq_zero (𝕜 := ℂ), key]
    change star (WithLp.ofLp ξ) ⬝ᵥ μ.totalMass *ᵥ WithLp.ofLp ξ = 0
    rw [show μ.totalMass *ᵥ WithLp.ofLp ξ = 0 from hM, dotProduct_zero]

/-- **The rank of the source map of any minimal realization is the source rank of `μ`**:
`rank V = rank B^* = rank μ((0,∞))`. -/
theorem finrank_range_eq :
    Module.finrank ℂ (LinearMap.range (V : EuclideanSpace ℂ H →ₗ[ℂ] K)) = μ.sourceRank := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (V : EuclideanSpace ℂ H →ₗ[ℂ] K)
  have h2 := LinearMap.finrank_range_add_finrank_ker μ.totalMass.mulVecLin
  rw [h.ker_source_eq, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    finrank_euclideanSpace] at h1
  rw [Module.finrank_pi] at h2
  unfold PositiveTailMeasure.sourceRank Matrix.rank
  omega

end IsMinimalRealization

/-- The source rank of `μ` is the rank of the canonical source map `V_μ = B_μ^* : H → K_μ`. -/
theorem PositiveTailMeasure.finrank_range_embedV (μ : PositiveTailMeasure H) :
    Module.finrank ℂ (LinearMap.range (μ.embedV : EuclideanSpace ℂ H →ₗ[ℂ] μ.kSpace)) =
      μ.sourceRank :=
  μ.isMinimalRealization_canonical.finrank_range_eq

end OperatorTailMeasure
end RenewalGeometry
