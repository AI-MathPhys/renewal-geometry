/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.MemoryCutoffSemigroupMeasureExact
/-!
# Integral calculus for positive operator-valued tail measures

Reusable toolkit for the operator-valued Stieltjes integrals of `def:supp-POVM`
(`OperatorTailMeasure.PositiveTailMeasure`, `papers/predictive_spectral_geometry`), used by
`thm:supp-dynamic-jets`, `thm:supp-Naimark-realization` and `thm:supp-contact-escape`:

* `conjTransposeCLM_integral`: the conjugate transpose of `∫ f dμ` is `∫ conj f dμ`
  (`μ` is Hermitian-valued);
* `isHermitian_integral_ofReal`, `quadForm_integral_ofReal`: for real `f` the operator integral
  is Hermitian and its quadratic form is the scalar integral `∫ f d⟨ξ, μ ξ⟩`;
* `posSemidef_integral_ofReal_of_nonneg`: for `f ≥ 0` the operator integral is positive
  semidefinite;
* `integral_const_mul`: complex constants come out of the operator integral;
* `ae_pos_variation`: the variation of `μ` is concentrated on `(0, ∞)`;
* `matrixIm_stieltjesSelfEnergy`, `posSemidef_matrixIm_stieltjesSelfEnergy`
  (`eq:supp-Herglotz-sign`): `Im Σ_μ(z) = (Im z) ∫ |λ - z|⁻² dμ(λ) ⪰ 0` for `Im z > 0`, where
  `Im M = (M - Mᴴ)/(2i)`.
-/

open MeasureTheory Filter Topology Set
open scoped ComplexOrder ENNReal Matrix

namespace RenewalGeometry
namespace OperatorTailMeasure

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The conjugate transpose `M ↦ Mᴴ` as a real continuous linear map on `H → H → ℂ`. -/
noncomputable def conjTransposeCLM : (H → H → ℂ) →L[ℝ] (H → H → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M i j => star (M j i)
      map_add' := fun M N => by
        funext i j
        simp
      map_smul' := fun c M => by
        funext i j
        simp [Complex.real_smul, Complex.star_def, Complex.conj_ofReal, mul_comm] }

@[simp]
theorem conjTransposeCLM_apply (M : H → H → ℂ) (i j : H) :
    conjTransposeCLM M i j = star (M j i) := rfl

/-- The imaginary part `Im M = (M - Mᴴ)/(2i)` of a complex matrix. -/
noncomputable def matrixIm (M : Matrix H H ℂ) : Matrix H H ℂ := (2 * Complex.I)⁻¹ • (M - Mᴴ)

/-- The scalar identity `(λ - z)⁻¹ - conj (λ - z)⁻¹ = 2i (Im z) |λ - z|⁻²`. -/
theorem resolvent_sub_star (z : ℂ) (lam : ℝ) :
    ((lam : ℂ) - z)⁻¹ - star ((lam : ℂ) - z)⁻¹ =
      (2 * Complex.I * z.im) * (((‖(lam : ℂ) - z‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [Complex.sq_norm]
  have hN : Complex.normSq ((lam : ℂ) - (starRingEnd ℂ) z) = Complex.normSq ((lam : ℂ) - z) := by
    rw [← Complex.normSq_conj ((lam : ℂ) - z)]
    congr 1
    rw [map_sub, Complex.conj_ofReal]
  apply Complex.ext
  · simp [Complex.inv_re, Complex.inv_im, Complex.star_def, hN]
  · simp [Complex.inv_re, Complex.inv_im, Complex.star_def, hN]
    ring

namespace PositiveTailMeasure

variable (μ : PositiveTailMeasure H)

/-- `μ(E)` is Hermitian for every set `E`. -/
theorem conjTransposeCLM_apply_measure (s : Set ℝ) :
    conjTransposeCLM (μ.toVectorMeasure s) = μ.toVectorMeasure s := by
  funext i j
  exact (μ.posSemidef_apply s).1.apply i j

/-- **Adjoint of the operator integral**: `(∫ f dμ)ᴴ = ∫ conj f dμ`. -/
theorem conjTransposeCLM_integral {f : ℝ → ℂ} (hf : Integrable f μ.toVectorMeasure.variation) :
    conjTransposeCLM
        (VectorMeasure.integral μ.toVectorMeasure f (ContinuousLinearMap.lsmul ℝ ℂ)) =
      VectorMeasure.integral μ.toVectorMeasure (fun x => star (f x))
        (ContinuousLinearMap.lsmul ℝ ℂ) := by
  rw [VectorMeasure.continuousLinearMap_apply_integral hf]
  have hconj : (fun x => star (f x)) = fun x => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (f x) := rfl
  rw [hconj, VectorMeasure.integral_continuousLinearMap_comp hf]
  set B₁ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ) :=
    (ContinuousLinearMap.compL ℝ (H → H → ℂ) (H → H → ℂ) (H → H → ℂ) conjTransposeCLM) ∘L
      ContinuousLinearMap.lsmul ℝ ℂ
  set B₂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ) :=
    ContinuousLinearMap.lsmul ℝ ℂ ∘L (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have hT : μ.toVectorMeasure.transpose B₁ = μ.toVectorMeasure.transpose B₂ := by
    refine VectorMeasure.ext fun s hs => ?_
    change B₁.flip (μ.toVectorMeasure s) = B₂.flip (μ.toVectorMeasure s)
    refine ContinuousLinearMap.ext fun c => ?_
    funext i j
    change star ((c • μ.toVectorMeasure s) j i) = ((Complex.conjCLE c) • μ.toVectorMeasure s) i j
    have h := (μ.posSemidef_apply s).1.apply i j
    simp only [Matrix.of_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', h, Complex.conjCLE_apply, Complex.star_def]
  rw [VectorMeasure.integral_eq_setToFun, VectorMeasure.integral_eq_setToFun]
  exact setToFun_congr_left' _ _ (fun s _ _ => by rw [hT]) f

/-- For real `f` the operator integral is Hermitian. -/
theorem isHermitian_integral_ofReal {f : ℝ → ℝ} (hf : Integrable f μ.toVectorMeasure.variation) :
    (Matrix.of (VectorMeasure.integral μ.toVectorMeasure (fun x => (f x : ℂ))
      (ContinuousLinearMap.lsmul ℝ ℂ))).IsHermitian := by
  have h : conjTransposeCLM (VectorMeasure.integral μ.toVectorMeasure (fun x => (f x : ℂ))
      (ContinuousLinearMap.lsmul ℝ ℂ)) =
      VectorMeasure.integral μ.toVectorMeasure (fun x => star (f x : ℂ))
        (ContinuousLinearMap.lsmul ℝ ℂ) :=
    μ.conjTransposeCLM_integral hf.ofReal
  have h2 : (fun x => star ((f x : ℝ) : ℂ)) = fun x => ((f x : ℝ) : ℂ) := by
    funext x
    exact Complex.conj_ofReal (f x)
  rw [h2] at h
  refine Matrix.IsHermitian.ext fun i j => ?_
  have h3 := congrFun (congrFun h i) j
  rw [conjTransposeCLM_apply] at h3
  exact h3

/-- **Quadratic form of a real operator integral**: `⟨ξ, (∫ f dμ) ξ⟩ = ∫ f d⟨ξ, μ ξ⟩`. -/
theorem quadForm_integral_ofReal (ξ : H → ℂ) {f : ℝ → ℝ}
    (hf : Integrable f μ.toVectorMeasure.variation) :
    quadForm ξ (Matrix.of (VectorMeasure.integral μ.toVectorMeasure (fun x => (f x : ℂ))
      (ContinuousLinearMap.lsmul ℝ ℂ))) = ((∫ x, f x ∂(μ.formMeasure ξ) : ℝ) : ℂ) := by
  have hH := μ.isHermitian_integral_ofReal hf
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    have := μ.quadFormCLM_integral ξ hf
    rw [quadFormCLM_apply] at this
    rw [← this, μ.integral_ofReal_lsmul hf]
  · simp only [Complex.ofReal_im]
    have := sesqForm_swap hH ξ ξ
    rw [sesqForm_self] at this
    exact Complex.conj_eq_iff_im.mp this.symm

/-- For `f ≥ 0` the operator integral is positive semidefinite. -/
theorem posSemidef_integral_ofReal_of_nonneg {f : ℝ → ℝ}
    (hf : Integrable f μ.toVectorMeasure.variation) (hf0 : 0 ≤ᵐ[μ.toVectorMeasure.variation] f) :
    (Matrix.of (VectorMeasure.integral μ.toVectorMeasure (fun x => (f x : ℂ))
      (ContinuousLinearMap.lsmul ℝ ℂ))).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨μ.isHermitian_integral_ofReal hf, fun ξ => ?_⟩
  change 0 ≤ quadForm ξ _
  rw [μ.quadForm_integral_ofReal ξ hf]
  refine Complex.zero_le_real.mpr (integral_nonneg_of_ae ?_)
  exact (Measure.absolutelyContinuous_of_le_smul (μ.formMeasure_le_smul_variation ξ)).ae_le hf0

/-- Complex constants come out of the operator integral. -/
theorem integral_const_mul (c : ℂ) {f : ℝ → ℂ} (hf : Integrable f μ.toVectorMeasure.variation) :
    VectorMeasure.integral μ.toVectorMeasure (fun x => c * f x) (ContinuousLinearMap.lsmul ℝ ℂ) =
      c • VectorMeasure.integral μ.toVectorMeasure f (ContinuousLinearMap.lsmul ℝ ℂ) := by
  have h1 : (fun x => c * f x) = fun x => (ContinuousLinearMap.lsmul ℝ ℂ c : ℂ →L[ℝ] ℂ) (f x) := by
    funext x
    simp
  rw [h1, VectorMeasure.integral_continuousLinearMap_comp hf]
  have h2 := VectorMeasure.continuousLinearMap_apply_integral (μ := μ.toVectorMeasure)
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (C := (ContinuousLinearMap.lsmul ℝ ℂ c : (H → H → ℂ) →L[ℝ] (H → H → ℂ))) hf
  rw [ContinuousLinearMap.lsmul_apply] at h2
  rw [h2]
  congr 1
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun M => ?_
  simp [smul_smul, mul_comm]

/-- The variation of `μ` is concentrated on `(0, ∞)`. -/
theorem ae_pos_variation : ∀ᵐ lam ∂μ.toVectorMeasure.variation, 0 < lam := by
  rw [ae_iff]
  refine measure_mono_null (t := Iic 0) (fun x (hx : ¬ (0 : ℝ) < x) => not_lt.mp hx) ?_
  exact (VectorMeasure.variation_apply_eq_zero measurableSet_Iic).2
    fun t hts ht => μ.eq_zero_of_subset_Iic t ht hts

/-- The trace measure is concentrated on `(0, ∞)`. -/
theorem traceMeasure_Iic : μ.traceMeasure (Iic 0) = 0 := by
  rw [traceMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i _ => μ.formMeasure_Iic _

theorem ae_pos_traceMeasure : ∀ᵐ lam ∂μ.traceMeasure, 0 < lam := by
  rw [ae_iff]
  exact measure_mono_null (fun x (hx : ¬ (0 : ℝ) < x) => not_lt.mp hx) μ.traceMeasure_Iic

/-- Integrability against the trace measure gives integrability against the variation. -/
theorem integrable_variation_of_traceMeasure {f : ℝ → ℝ} (hf : Integrable f μ.traceMeasure) :
    Integrable f μ.toVectorMeasure.variation :=
  hf.mono_measure μ.variation_le_traceMeasure

/-- `|λ - z|⁻²` is `μ`-integrable for `z ∉ [0, ∞)`. -/
theorem integrable_inv_sq_norm_sub {z : ℂ} (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) :
    Integrable (fun lam : ℝ => (‖(lam : ℂ) - z‖ ^ 2)⁻¹) μ.toVectorMeasure.variation := by
  have hf := μ.integrable_resolvent hz
  -- `δ ≤ ‖λ - z‖` on `[0, ∞)`
  set δ : ℝ := if z.im = 0 then -z.re else |z.im| with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    split_ifs with h
    · have : ¬ 0 ≤ z.re := fun h' => hz ⟨h, h'⟩
      linarith [not_le.mp this]
    · exact abs_pos.mpr h
  have hlow : ∀ lam : ℝ, 0 ≤ lam → δ ≤ ‖(lam : ℂ) - z‖ := by
    intro lam hlam
    rw [hδ]
    split_ifs with h
    · have hre : z.re < 0 := not_le.mp fun h' => hz ⟨h, h'⟩
      have e1 : |((lam : ℂ) - z).re| = lam - z.re := by
        rw [Complex.sub_re, Complex.ofReal_re, abs_of_nonneg (by linarith)]
      have e2 := Complex.abs_re_le_norm ((lam : ℂ) - z)
      rw [e1] at e2
      linarith
    · have e1 : |((lam : ℂ) - z).im| = |z.im| := by
        rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg]
      have e2 := Complex.abs_im_le_norm ((lam : ℂ) - z)
      rw [e1] at e2
      exact e2
  have hprod : Integrable (fun lam : ℝ => ‖((lam : ℂ) - z)⁻¹‖ * ‖((lam : ℂ) - z)⁻¹‖)
      μ.toVectorMeasure.variation := by
    refine hf.norm.bdd_mul (c := δ⁻¹) hf.norm.aestronglyMeasurable ?_
    filter_upwards [μ.ae_pos_variation] with lam hlam
    rw [norm_norm, norm_inv]
    exact inv_anti₀ hδpos (hlow lam hlam.le)
  refine hprod.congr (ae_of_all _ fun lam => ?_)
  beta_reduce
  rw [norm_inv, ← sq, inv_pow]

/-- **`eq:supp-Herglotz-sign`, identity.**  `Im Σ_μ(z) = (Im z) ∫ |λ - z|⁻² dμ(λ)` for
`z ∉ [0, ∞)`. -/
theorem matrixIm_stieltjesSelfEnergy {z : ℂ} (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) :
    matrixIm (μ.stieltjesSelfEnergy z) =
      (z.im : ℂ) • Matrix.of (VectorMeasure.integral μ.toVectorMeasure
        (fun lam : ℝ => (((‖(lam : ℂ) - z‖ ^ 2)⁻¹ : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
  have hf := μ.integrable_resolvent hz
  have hw := μ.integrable_inv_sq_norm_sub hz
  have hH : (μ.stieltjesSelfEnergy z)ᴴ = Matrix.of (conjTransposeCLM
      (VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => ((lam : ℂ) - z)⁻¹)
        (ContinuousLinearMap.lsmul ℝ ℂ))) := by
    ext i j
    rfl
  unfold matrixIm
  rw [hH, μ.conjTransposeCLM_integral hf]
  have hsub : μ.stieltjesSelfEnergy z - Matrix.of (VectorMeasure.integral μ.toVectorMeasure
      (fun lam : ℝ => star ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) =
      Matrix.of (VectorMeasure.integral μ.toVectorMeasure
        (fun lam : ℝ => (2 * Complex.I * z.im) * (((‖(lam : ℂ) - z‖ ^ 2)⁻¹ : ℝ) : ℂ))
        (ContinuousLinearMap.lsmul ℝ ℂ)) := by
    have hstar : Integrable (fun lam : ℝ => star ((lam : ℂ) - z)⁻¹) μ.toVectorMeasure.variation :=
      hf.norm.mono' (continuous_star.comp_aestronglyMeasurable hf.aestronglyMeasurable)
        (ae_of_all _ fun lam => by rw [norm_star])
    have hAB : VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => ((lam : ℂ) - z)⁻¹)
        (ContinuousLinearMap.lsmul ℝ ℂ) -
        VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => star ((lam : ℂ) - z)⁻¹)
          (ContinuousLinearMap.lsmul ℝ ℂ) =
        VectorMeasure.integral μ.toVectorMeasure
          (fun lam : ℝ => (2 * Complex.I * z.im) * (((‖(lam : ℂ) - z‖ ^ 2)⁻¹ : ℝ) : ℂ))
          (ContinuousLinearMap.lsmul ℝ ℂ) := by
      rw [← VectorMeasure.integral_fun_sub hf hstar]
      congr 1
      funext lam
      exact resolvent_sub_star z lam
    unfold stieltjesSelfEnergy
    ext i j
    simp only [Matrix.sub_apply, Matrix.of_apply]
    exact congrFun (congrFun hAB i) j
  rw [hsub, μ.integral_const_mul _ (f := fun lam : ℝ => (((‖(lam : ℂ) - z‖ ^ 2)⁻¹ : ℝ) : ℂ))
    hw.ofReal]
  ext i j
  simp only [Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  have hI : (2 * Complex.I)⁻¹ * (2 * Complex.I * z.im) = z.im := by
    have : (2 * Complex.I) ≠ 0 := by simp
    field_simp
  rw [← mul_assoc, hI]

/-- **`eq:supp-Herglotz-sign`, sign.**  For `Im z > 0`, `Im Σ_μ(z) ⪰ 0`. -/
theorem posSemidef_matrixIm_stieltjesSelfEnergy {z : ℂ} (hz : 0 < z.im) :
    (matrixIm (μ.stieltjesSelfEnergy z)).PosSemidef := by
  have hz' : ¬ (z.im = 0 ∧ 0 ≤ z.re) := fun h => by linarith [h.1]
  rw [μ.matrixIm_stieltjesSelfEnergy hz']
  refine (μ.posSemidef_integral_ofReal_of_nonneg (μ.integrable_inv_sq_norm_sub hz')
    (ae_of_all _ fun lam => by positivity)).smul (Complex.zero_le_real.mpr hz.le)

end PositiveTailMeasure

end OperatorTailMeasure
end RenewalGeometry
