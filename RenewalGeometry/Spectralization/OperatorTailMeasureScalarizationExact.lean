/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.OperatorTailMeasureStieltjesExact
/-!
# Scalarisation of positive operator-valued tail measures

Support file for `thm:supp-memory-determinacy` and `thm:supp-memory-RG` of
`papers/predictive_spectral_geometry`, built on the encoding `PositiveTailMeasure` of
`def:supp-POVM` (file `OperatorTailMeasureStieltjesExact`).

For a vector `ξ : H → ℂ` the quadratic form `q_ξ(M) = ⟨ξ, M ξ⟩ = star ξ ⬝ᵥ (M *ᵥ ξ)` scalarises
the operator measure `μ` to

* the signed measure `signedForm μ ξ : E ↦ Re ⟨ξ, μ(E) ξ⟩`, which is nonnegative because
  `μ(E) ⪰ 0`;
* the finite positive measure `formMeasure μ ξ` (`SignedMeasure.toMeasureOfZeroLE`);
* the trace measure `traceMeasure μ = ∑ᵢ formMeasure μ eᵢ`, i.e. `E ↦ Tr μ(E)`.

We prove the entry bound `‖M i j‖ ≤ Re Tr M` for positive semidefinite `M`
(`posSemidef_norm_apply_le_re_trace`), from which the variation of `μ` is dominated by the
trace measure (`variation_le_traceMeasure`; in particular the variation is finite), and every
`formMeasure μ ξ` is dominated by a multiple of `traceMeasure μ`
(`formMeasure_le_smul_traceMeasure`).  The bridge `quadFormCLM_integral` identifies the
scalarised vector-measure integral `Re ⟨ξ, (∫ f dμ) ξ⟩` with the Bochner integral
`∫ f d(formMeasure μ ξ)`, and `integrable_variation_of_continuous` gives integrability of
continuous functions against `μ` when `μ` is supported in `(0, R]`.
-/

open MeasureTheory Filter Topology Set
open scoped ComplexOrder ENNReal Matrix

namespace RenewalGeometry
namespace OperatorTailMeasure

variable {H : Type*} [Fintype H] [DecidableEq H]

/-! ## The quadratic form `q_ξ(M) = ⟨ξ, M ξ⟩` -/

/-- The quadratic form `q_ξ(M) = star ξ ⬝ᵥ (M *ᵥ ξ)` of a matrix. -/
def quadForm (ξ : H → ℂ) (M : Matrix H H ℂ) : ℂ := star ξ ⬝ᵥ (M *ᵥ ξ)

theorem quadForm_add (ξ : H → ℂ) (M N : Matrix H H ℂ) :
    quadForm ξ (M + N) = quadForm ξ M + quadForm ξ N := by
  simp [quadForm, Matrix.add_mulVec, dotProduct_add]

theorem quadForm_smul (ξ : H → ℂ) (c : ℂ) (M : Matrix H H ℂ) :
    quadForm ξ (c • M) = c * quadForm ξ M := by
  simp [quadForm, Matrix.smul_mulVec, dotProduct_smul]

theorem quadForm_zero (ξ : H → ℂ) : quadForm ξ (0 : Matrix H H ℂ) = 0 := by
  simp [quadForm]

/-- The value of the form on `c e_i + d e_j`. -/
theorem quadForm_smul_single_add_smul_single (M : Matrix H H ℂ) (i j : H) (c d : ℂ) :
    quadForm (c • Pi.single i 1 + d • Pi.single j 1) M =
      star c * c * M i i + star c * d * M i j + star d * c * M j i + star d * d * M j j := by
  simp only [quadForm, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one, star_add,
    star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Matrix.col, ← Pi.single_star, star_one, single_dotProduct, Matrix.transpose_apply]
  ring

/-- The form on a coordinate vector is the diagonal entry. -/
theorem quadForm_single (M : Matrix H H ℂ) (i : H) :
    quadForm (Pi.single i 1) M = M i i := by
  have := quadForm_smul_single_add_smul_single M i i 1 0
  simpa using this

/-- Positivity of the form of a positive semidefinite matrix. -/
theorem posSemidef_re_quadForm_nonneg {M : Matrix H H ℂ} (hM : M.PosSemidef) (ξ : H → ℂ) :
    0 ≤ (quadForm ξ M).re :=
  (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg ξ)).1

/-- The form of a positive semidefinite matrix is real. -/
theorem posSemidef_im_quadForm_eq_zero {M : Matrix H H ℂ} (hM : M.PosSemidef) (ξ : H → ℂ) :
    (quadForm ξ M).im = 0 :=
  ((Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg ξ)).2).symm

theorem posSemidef_re_apply_self_nonneg {M : Matrix H H ℂ} (hM : M.PosSemidef) (i : H) :
    0 ≤ (M i i).re := by
  have := posSemidef_re_quadForm_nonneg hM (Pi.single i 1)
  rwa [quadForm_single] at this

/-- The real part of the trace of a positive semidefinite matrix is nonnegative. -/
theorem posSemidef_re_trace_nonneg {M : Matrix H H ℂ} (hM : M.PosSemidef) :
    0 ≤ M.trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => posSemidef_re_apply_self_nonneg hM i

/-- **Entry bound for positive semidefinite matrices**: `2 ‖M i j‖ ≤ Re M i i + Re M j j`. -/
theorem posSemidef_two_mul_norm_apply_le {M : Matrix H H ℂ} (hM : M.PosSemidef) (i j : H) :
    2 * ‖M i j‖ ≤ (M i i).re + (M j j).re := by
  set z := M i j with hz
  by_cases h0 : z = 0
  · rw [h0, norm_zero, mul_zero]
    exact add_nonneg (posSemidef_re_apply_self_nonneg hM i) (posSemidef_re_apply_self_nonneg hM j)
  have hji : M j i = star z := by
    rw [hz, ← hM.1.apply i j, star_star]
  have hq := posSemidef_re_quadForm_nonneg hM
    ((‖z‖ : ℂ) • Pi.single i 1 + (-star z) • Pi.single j 1)
  have hsr : star (‖z‖ : ℂ) = (‖z‖ : ℂ) := by rw [Complex.star_def, Complex.conj_ofReal]
  rw [quadForm_smul_single_add_smul_single, hji, ← hz, star_neg, star_star, hsr] at hq
  have hzz : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hzz' : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [mul_comm, hzz]
  have hkey : (‖z‖ : ℂ) * ‖z‖ * M i i + (‖z‖ : ℂ) * -star z * z +
      -z * ‖z‖ * star z + -z * -star z * M j j =
      ((‖z‖ ^ 2 : ℝ) : ℂ) * (M i i + M j j - 2 * ‖z‖) := by
    push_cast at hzz hzz' ⊢
    linear_combination (-(‖z‖ : ℂ)) * hzz' + (-(‖z‖ : ℂ)) * hzz + (M j j) * hzz
  rw [hkey] at hq
  have hpos : 0 < ‖z‖ ^ 2 := by positivity
  rw [Complex.re_ofReal_mul] at hq
  have : 0 ≤ (M i i + M j j - 2 * (‖z‖ : ℂ)).re := by
    by_contra hneg
    rw [not_le] at hneg
    have := mul_neg_of_pos_of_neg hpos hneg
    linarith
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
  linarith

/-- Every entry of a positive semidefinite matrix is bounded by the real part of the trace. -/
theorem posSemidef_norm_apply_le_re_trace {M : Matrix H H ℂ} (hM : M.PosSemidef) (i j : H) :
    ‖M i j‖ ≤ M.trace.re := by
  have h := posSemidef_two_mul_norm_apply_le hM i j
  have hi : (M i i).re ≤ M.trace.re := by
    rw [Matrix.trace, Complex.re_sum]
    exact Finset.single_le_sum (fun k _ => posSemidef_re_apply_self_nonneg hM k)
      (Finset.mem_univ i)
  have hj : (M j j).re ≤ M.trace.re := by
    rw [Matrix.trace, Complex.re_sum]
    exact Finset.single_le_sum (fun k _ => posSemidef_re_apply_self_nonneg hM k)
      (Finset.mem_univ j)
  linarith

/-- The sup-norm of a positive semidefinite matrix (as an element of `H → H → ℂ`) is bounded by
the real part of the trace. -/
theorem posSemidef_norm_le_re_trace {X : H → H → ℂ} (hX : (Matrix.of X).PosSemidef) :
    ‖X‖ ≤ (Matrix.of X).trace.re := by
  rw [pi_norm_le_iff_of_nonneg (posSemidef_re_trace_nonneg hX)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (posSemidef_re_trace_nonneg hX)]
  intro j
  exact posSemidef_norm_apply_le_re_trace hX i j

/-- The quadratic form of a positive semidefinite matrix is bounded by
`(∑ᵢ ‖ξ i‖)² Re Tr M`. -/
theorem posSemidef_norm_quadForm_le {M : Matrix H H ℂ} (hM : M.PosSemidef) (ξ : H → ℂ) :
    ‖quadForm ξ M‖ ≤ (∑ i, ‖ξ i‖) ^ 2 * M.trace.re := by
  have hq : quadForm ξ M = ∑ i, ∑ j, star (ξ i) * (M i j * ξ j) := by
    simp [quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hq, sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  calc ‖ξ i‖ * (‖M i j‖ * ‖ξ j‖) ≤ ‖ξ i‖ * (M.trace.re * ‖ξ j‖) := by
        gcongr
        exact posSemidef_norm_apply_le_re_trace hM i j
    _ = ‖ξ i‖ * ‖ξ j‖ * M.trace.re := by ring

/-! ## The real continuous linear functional `M ↦ Re q_ξ(M)` -/

/-- `Re q_ξ` as a real continuous linear functional on `H → H → ℂ` (the value space of the
vector measure of `def:supp-POVM`). -/
noncomputable def quadFormCLM (ξ : H → ℂ) : (H → H → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (quadForm ξ (Matrix.of M)).re
      map_add' := fun M N => by
        change (quadForm ξ (Matrix.of M + Matrix.of N)).re = _
        rw [quadForm_add, Complex.add_re]
      map_smul' := fun c M => by
        change (quadForm ξ (Matrix.of (c • M))).re = c * (quadForm ξ (Matrix.of M)).re
        have : Matrix.of (c • M) = (c : ℂ) • Matrix.of M := by
          ext i j
          simp [Complex.real_smul]
        rw [this, quadForm_smul, Complex.re_ofReal_mul] }

@[simp]
theorem quadFormCLM_apply (ξ : H → ℂ) (M : H → H → ℂ) :
    quadFormCLM ξ M = (quadForm ξ (Matrix.of M)).re := rfl

theorem quadFormCLM_single (i : H) (M : H → H → ℂ) :
    quadFormCLM (Pi.single i 1) M = (M i i).re := by
  rw [quadFormCLM_apply, quadForm_single]
  rfl

/-! ## Scalarised measures -/

namespace PositiveTailMeasure

variable (μ : PositiveTailMeasure H)

theorem posSemidef_apply (s : Set ℝ) : (Matrix.of (μ.toVectorMeasure s)).PosSemidef := by
  by_cases hs : MeasurableSet s
  · exact μ.posSemidef s hs
  · rw [VectorMeasure.not_measurable _ hs]
    exact Matrix.PosSemidef.zero

/-- The scalarised signed measure `E ↦ Re ⟨ξ, μ(E) ξ⟩`. -/
noncomputable def signedForm (ξ : H → ℂ) : SignedMeasure ℝ :=
  μ.toVectorMeasure.mapRange (quadFormCLM ξ).toLinearMap.toAddMonoidHom
    (quadFormCLM ξ).continuous

@[simp]
theorem signedForm_apply (ξ : H → ℂ) (s : Set ℝ) :
    μ.signedForm ξ s = quadFormCLM ξ (μ.toVectorMeasure s) := rfl

theorem signedForm_nonneg (ξ : H → ℂ) (s : Set ℝ) : 0 ≤ μ.signedForm ξ s := by
  rw [signedForm_apply, quadFormCLM_apply]
  exact posSemidef_re_quadForm_nonneg (μ.posSemidef_apply s) ξ

theorem zero_le_signedForm (ξ : H → ℂ) : 0 ≤ μ.signedForm ξ :=
  VectorMeasure.le_iff.mpr fun s _ => by simpa using μ.signedForm_nonneg ξ s

theorem zero_le_restrict_signedForm (ξ : H → ℂ) : 0 ≤[Set.univ] μ.signedForm ξ :=
  (VectorMeasure.le_restrict_univ_iff_le _ _).2 (μ.zero_le_signedForm ξ)

/-- The scalarised finite positive measure `E ↦ Re ⟨ξ, μ(E) ξ⟩`. -/
noncomputable def formMeasure (ξ : H → ℂ) : Measure ℝ :=
  (μ.signedForm ξ).toMeasureOfZeroLE Set.univ MeasurableSet.univ (μ.zero_le_restrict_signedForm ξ)

instance (ξ : H → ℂ) : IsFiniteMeasure (μ.formMeasure ξ) :=
  SignedMeasure.toMeasureOfZeroLE_finite _ _ _

theorem formMeasure_real_apply (ξ : H → ℂ) {s : Set ℝ} (hs : MeasurableSet s) :
    (μ.formMeasure ξ).real s = quadFormCLM ξ (μ.toVectorMeasure s) := by
  rw [formMeasure, SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ hs, Set.univ_inter,
    signedForm_apply]

theorem formMeasure_apply (ξ : H → ℂ) {s : Set ℝ} (hs : MeasurableSet s) :
    μ.formMeasure ξ s = ENNReal.ofReal (quadFormCLM ξ (μ.toVectorMeasure s)) := by
  rw [← formMeasure_real_apply μ ξ hs, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem toSignedMeasure_formMeasure (ξ : H → ℂ) :
    (μ.formMeasure ξ).toSignedMeasure = μ.signedForm ξ :=
  SignedMeasure.toMeasureOfZeroLE_toSignedMeasure _ _

/-- The scalarised measures vanish on `(-∞, 0]`. -/
theorem formMeasure_Iic (ξ : H → ℂ) : μ.formMeasure ξ (Set.Iic 0) = 0 := by
  rw [formMeasure_apply μ ξ measurableSet_Iic,
    μ.eq_zero_of_subset_Iic _ measurableSet_Iic subset_rfl]
  simp [quadForm_zero]

/-- The scalarised measures of a measure supported in `(0, R]` vanish on `(R, ∞)`. -/
theorem formMeasure_Ioi {R : ℝ} (hR : μ.IsSupportedIn R) (ξ : H → ℂ) :
    μ.formMeasure ξ (Set.Ioi R) = 0 := by
  rw [formMeasure_apply μ ξ measurableSet_Ioi, hR _ measurableSet_Ioi subset_rfl]
  simp [quadForm_zero]

/-- The trace measure `E ↦ Tr μ(E) = ∑ᵢ ⟨eᵢ, μ(E) eᵢ⟩`. -/
noncomputable def traceMeasure : Measure ℝ := ∑ i, μ.formMeasure (Pi.single i 1)

instance : IsFiniteMeasure μ.traceMeasure where
  measure_univ_lt_top := by
    rw [traceMeasure, Measure.coe_finsetSum, Finset.sum_apply]
    exact ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top _ _

theorem traceMeasure_apply {s : Set ℝ} (hs : MeasurableSet s) :
    μ.traceMeasure s = ENNReal.ofReal (Matrix.of (μ.toVectorMeasure s)).trace.re := by
  rw [traceMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [formMeasure_apply μ _ hs, quadFormCLM_single]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Complex.re_sum]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun i _ => posSemidef_re_apply_self_nonneg (μ.posSemidef_apply s) i)]
  rfl

/-- **The variation of `μ` is dominated by the trace measure**, hence finite. -/
theorem variation_le_traceMeasure : μ.toVectorMeasure.variation ≤ μ.traceMeasure := by
  refine VectorMeasure.variation_le_of_forall_enorm_le fun s hs => ?_
  rw [traceMeasure_apply μ hs]
  calc ‖μ.toVectorMeasure s‖ₑ = ENNReal.ofReal ‖μ.toVectorMeasure s‖ := (ofReal_norm _).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (posSemidef_norm_le_re_trace (μ.posSemidef_apply s))

instance : IsFiniteMeasure μ.toVectorMeasure.variation :=
  isFiniteMeasure_of_le _ μ.variation_le_traceMeasure

/-- Every scalarised measure is dominated by a multiple of the trace measure. -/
theorem formMeasure_le_smul_traceMeasure (ξ : H → ℂ) :
    μ.formMeasure ξ ≤ ENNReal.ofReal ((∑ i, ‖ξ i‖) ^ 2) • μ.traceMeasure := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [formMeasure_apply μ ξ hs, Measure.smul_apply, traceMeasure_apply μ hs, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [quadFormCLM_apply]
  exact (Complex.re_le_norm _).trans (posSemidef_norm_quadForm_le (μ.posSemidef_apply s) ξ)

/-! ## The bridge between operator integrals and scalar integrals -/

/-- Real-valued integrands: the complex-scalar pairing used by `stieltjesSelfEnergy`, `moment`
and `euclideanMemoryKernel` reduces to the real-scalar pairing. -/
theorem integral_ofReal_lsmul {f : ℝ → ℝ} (hf : Integrable f μ.toVectorMeasure.variation) :
    VectorMeasure.integral μ.toVectorMeasure (fun x => (f x : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ) =
      VectorMeasure.integral μ.toVectorMeasure f (ContinuousLinearMap.lsmul ℝ ℝ) := by
  have h := VectorMeasure.integral_continuousLinearMap_comp (μ := μ.toVectorMeasure)
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (C := Complex.ofRealCLM) hf
  simp only [Complex.ofRealCLM_apply] at h
  rw [h]
  congr 1

/-- Domination of the variation of the scalarised signed measure. -/
theorem variation_signedForm_le (ξ : H → ℂ) :
    (μ.signedForm ξ).variation ≤ ‖quadFormCLM ξ‖₊ • μ.toVectorMeasure.variation := by
  refine VectorMeasure.variation_le_of_forall_enorm_le fun s hs => ?_
  rw [signedForm_apply, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [ContinuousLinearMap.le_opENorm, VectorMeasure.enorm_measure_le_variation,
    ← enorm_eq_nnnorm]

/-- **Bridge**: `Re ⟨ξ, (∫ f dμ) ξ⟩ = ∫ f d(formMeasure μ ξ)` for `μ`-integrable real `f`. -/
theorem quadFormCLM_integral (ξ : H → ℂ) {f : ℝ → ℝ}
    (hf : Integrable f μ.toVectorMeasure.variation) :
    quadFormCLM ξ (VectorMeasure.integral μ.toVectorMeasure f (ContinuousLinearMap.lsmul ℝ ℝ)) =
      ∫ x, f x ∂(μ.formMeasure ξ) := by
  set C := quadFormCLM ξ
  set B' : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (H → H → ℂ) (H → H → ℂ) ℝ C) ∘L
      ContinuousLinearMap.lsmul ℝ ℝ
  rw [VectorMeasure.continuousLinearMap_apply_integral hf]
  -- the transposed set functions agree
  have hT : μ.toVectorMeasure.transpose B' =
      (μ.signedForm ξ).transpose (ContinuousLinearMap.lsmul ℝ ℝ) := by
    refine VectorMeasure.ext fun s hs => ?_
    change B'.flip (μ.toVectorMeasure s) =
      (ContinuousLinearMap.lsmul ℝ ℝ).flip (μ.signedForm ξ s)
    ext
    simp [B', C]
  have h₁ := MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure μ.toVectorMeasure B'
  have h₂ : DominatedFinMeasAdditive μ.toVectorMeasure.variation
      ((μ.signedForm ξ).transpose (ContinuousLinearMap.lsmul ℝ ℝ)) ‖B'‖ := hT ▸ h₁
  have hstep1 : VectorMeasure.integral μ.toVectorMeasure f B' =
      setToFun μ.toVectorMeasure.variation
        ((μ.signedForm ξ).transpose (ContinuousLinearMap.lsmul ℝ ℝ)) h₂ f := by
    rw [VectorMeasure.integral_eq_setToFun]
    exact setToFun_congr_left' h₁ h₂ (fun s _ _ => by rw [hT]) f
  have hstep2 : setToFun μ.toVectorMeasure.variation
      ((μ.signedForm ξ).transpose (ContinuousLinearMap.lsmul ℝ ℝ)) h₂ f =
      VectorMeasure.integral (μ.signedForm ξ) f (ContinuousLinearMap.lsmul ℝ ℝ) := by
    rw [VectorMeasure.integral_eq_setToFun]
    exact setToFun_congr_measure_of_integrable (‖C‖₊ : ℝ≥0∞) ENNReal.coe_ne_top
      (μ.variation_signedForm_le ξ) h₂ _ f hf
  rw [hstep1, hstep2, ← μ.toSignedMeasure_formMeasure ξ]
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip := by
    ext
    simp
  rw [hflip]
  exact VectorMeasure.integral_toSignedMeasure

/-- Continuous functions are integrable against a measure supported in `(0, R]`. -/
theorem integrable_variation_of_continuous {R : ℝ} (hR : μ.IsSupportedIn R) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f μ.toVectorMeasure.variation := by
  set ν := μ.toVectorMeasure.variation
  have h1 : ν (Set.Iic 0) = 0 :=
    (VectorMeasure.variation_apply_eq_zero measurableSet_Iic).2
      fun t hts ht => μ.eq_zero_of_subset_Iic t ht hts
  have h2 : ν (Set.Ioi R) = 0 :=
    (VectorMeasure.variation_apply_eq_zero measurableSet_Ioi).2 fun t hts ht => hR t ht hts
  have hmem : ∀ᵐ x ∂ν, x ∈ Set.Icc 0 R := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl (le_of_lt hx)
    · exact Or.inr hx
  rw [← Measure.restrict_eq_self_of_ae_mem hmem]
  exact hf.continuousOn.integrableOn_compact isCompact_Icc

/-- Scalarised moments: `Re ⟨ξ, M_n ξ⟩ = ∫ λⁿ d(formMeasure μ ξ)` for `μ` supported in
`(0, R]`. -/
theorem quadFormCLM_moment {R : ℝ} (hR : μ.IsSupportedIn R) (ξ : H → ℂ) (n : ℕ) :
    quadFormCLM ξ (μ.moment n) = ∫ x, x ^ n ∂(μ.formMeasure ξ) := by
  have hf : Integrable (fun x : ℝ => x ^ n) μ.toVectorMeasure.variation :=
    μ.integrable_variation_of_continuous hR (continuous_pow n)
  change quadFormCLM ξ (VectorMeasure.integral μ.toVectorMeasure
    (fun lam : ℝ => ((lam ^ n : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)) = _
  rw [μ.integral_ofReal_lsmul hf, μ.quadFormCLM_integral ξ hf]

end PositiveTailMeasure

end OperatorTailMeasure
end RenewalGeometry
