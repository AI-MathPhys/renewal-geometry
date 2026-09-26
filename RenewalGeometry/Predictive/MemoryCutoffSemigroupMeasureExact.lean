/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.OperatorTailMeasureDeterminacyExact
import RenewalGeometry.Predictive.MemoryCutoffSemigroupExact
/-!
# The exact memory RG semigroup for general positive operator-valued tail measures

Paper `predictive_spectral_geometry`, label `thm:supp-memory-RG`, for the general (weakly
countably additive) positive operator-valued tail measures of `def:supp-POVM`
(`OperatorTailMeasure.PositiveTailMeasure`).  The finite atomic case is in
`MemoryCutoffSemigroupExact`; here the Stieltjes integrals are Mathlib vector-measure
integrals.

For `μ` a positive tail measure, `A : Matrix H H ℂ` and a cutoff `Λ`:

* `dynamicFunction μ A z = F_{A,μ}(z) = A - z - Σ_μ(z)`;
* `headCorrection μ Λ = Q_{>Λ} = ∫_{(Λ,∞)} λ⁻¹ dμ(λ)`, `cutoff μ Λ = μ|_{(0,Λ]}` and
  `rg μ A Λ = RG_Λ(A, μ) = (A - Q_{>Λ}, μ|_{(0,Λ]})` (`eq:supp-memory-head`, `eq:supp-memory-RG`);
* `eq:supp-memory-static-preserved` (`dynamicFunction_rg_zero`): `F_{RG_Λ(A,μ)}(0) = F_{A,μ}(0)`,
  under the standing hypothesis that `λ⁻¹` is `μ`-integrable (this is exactly the condition
  that `F_{A,μ}(0)` exists);
* `eq:supp-memory-screen-error` (`norm_dynamicFunction_sub_rg_le`): for `‖z‖ ≤ r < Λ` and
  `z ∉ [0,∞)`, `‖F_{A,μ}(z) - F_{RG_Λ(A,μ)}(z)‖ ≤ r/(Λ - r) ‖Q_{>Λ}‖` in the operator norm;
* `eq:supp-memory-semigroup` (`rg_rg`): `RG_{Λ₂} ∘ RG_{Λ₁} = RG_{Λ₂}` for `0 < Λ₂ ≤ Λ₁`.

The analytic core is the **positive-weighted operator-norm bound for operator integrals**
(`l2_opNorm_integral_le_of_norm_le`): if `‖c‖ ≤ κ w` `μ`-a.e. with `w ≥ 0`, then
`‖∫ c dμ‖ ≤ κ ‖∫ w dμ‖`.  It is proved by scalarising along the sesquilinear forms
`⟨x, μ(·) y⟩`, whose total variation is dominated by `(t ⟨x, μ x⟩ + t⁻¹ ⟨y, μ y⟩)/2` for every
`t > 0` (Cauchy–Schwarz for positive semidefinite matrices), integrating and optimising in `t`.
-/

open MeasureTheory Filter Topology Set
open scoped ComplexOrder ENNReal Matrix InnerProductSpace Matrix.Norms.L2Operator

namespace RenewalGeometry
namespace OperatorTailMeasure

variable {H : Type*} [Fintype H] [DecidableEq H]

/-! ## Sesquilinear scalarisation -/

/-- The sesquilinear form `⟨x, M y⟩ = star x ⬝ᵥ (M *ᵥ y)`. -/
def sesqForm (x y : H → ℂ) (M : Matrix H H ℂ) : ℂ := star x ⬝ᵥ (M *ᵥ y)

theorem sesqForm_add (x y : H → ℂ) (M N : Matrix H H ℂ) :
    sesqForm x y (M + N) = sesqForm x y M + sesqForm x y N := by
  simp [sesqForm, Matrix.add_mulVec, dotProduct_add]

theorem sesqForm_smul (x y : H → ℂ) (c : ℂ) (M : Matrix H H ℂ) :
    sesqForm x y (c • M) = c * sesqForm x y M := by
  simp [sesqForm, Matrix.smul_mulVec, dotProduct_smul]

theorem sesqForm_self (x : H → ℂ) (M : Matrix H H ℂ) : sesqForm x x M = quadForm x M := rfl

/-- The form on `c x + d y`, expanded. -/
theorem quadForm_smul_add_smul (M : Matrix H H ℂ) (x y : H → ℂ) (c d : ℂ) :
    quadForm (c • x + d • y) M =
      star c * c * quadForm x M + star c * d * sesqForm x y M +
        star d * c * sesqForm y x M + star d * d * quadForm y M := by
  simp only [quadForm, sesqForm, Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- For a Hermitian matrix, `⟨y, M x⟩ = conj ⟨x, M y⟩`. -/
theorem sesqForm_swap {M : Matrix H H ℂ} (hM : M.IsHermitian) (x y : H → ℂ) :
    sesqForm y x M = star (sesqForm x y M) := by
  simp only [sesqForm]
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hM.eq,
    ← Matrix.dotProduct_mulVec]

/-- **Cauchy–Schwarz for positive semidefinite matrices**:
`‖⟨x, M y⟩‖ ≤ √⟨x, M x⟩ √⟨y, M y⟩`. -/
theorem posSemidef_norm_sesqForm_le {M : Matrix H H ℂ} (hM : M.PosSemidef) (x y : H → ℂ) :
    ‖sesqForm x y M‖ ≤ Real.sqrt (quadForm x M).re * Real.sqrt (quadForm y M).re := by
  set B := sesqForm x y M with hB
  set a := (quadForm x M).re with ha
  set b := (quadForm y M).re with hb
  have ha0 : 0 ≤ a := posSemidef_re_quadForm_nonneg hM x
  have hb0 : 0 ≤ b := posSemidef_re_quadForm_nonneg hM y
  have hBB : B * star B = ((‖B‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hBB' : star B * B = ((‖B‖ ^ 2 : ℝ) : ℂ) := by rw [mul_comm, hBB]
  -- the quadratic polynomial `t ↦ t² a - 2 t ‖B‖² + ‖B‖² b` is nonnegative
  have hpoly : ∀ t : ℝ, 0 ≤ t ^ 2 * a - 2 * t * ‖B‖ ^ 2 + ‖B‖ ^ 2 * b := by
    intro t
    have hq := posSemidef_re_quadForm_nonneg hM ((t : ℂ) • x + (-star B) • y)
    rw [quadForm_smul_add_smul, sesqForm_swap hM.1 x y, ← hB, star_neg, star_star] at hq
    have hsr : star (t : ℂ) = (t : ℂ) := by rw [Complex.star_def, Complex.conj_ofReal]
    rw [hsr] at hq
    obtain ⟨qim, hqim⟩ : ∃ r : ℝ, r = (quadForm x M).im := ⟨_, rfl⟩
    have hkey : (t : ℂ) * t * quadForm x M + (t : ℂ) * -star B * B + -B * t * star B +
        -B * -star B * quadForm y M =
        ((t ^ 2 * a - 2 * t * ‖B‖ ^ 2 : ℝ) : ℂ) + ((‖B‖ ^ 2 : ℝ) : ℂ) * quadForm y M +
          ((t ^ 2 : ℝ) : ℂ) * (qim * Complex.I) := by
      have hx : quadForm x M = (a : ℂ) + qim * Complex.I := by
        rw [ha, hqim]; exact (Complex.re_add_im _).symm
      rw [hx]
      push_cast at hBB hBB' ⊢
      linear_combination (-(t : ℂ)) * hBB' + (-(t : ℂ)) * hBB + (quadForm y M) * hBB
    rw [hkey] at hq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, mul_one, add_zero,
      Complex.mul_im, sub_self] at hq
    rw [← hb] at hq
    linarith
  -- conclude `‖B‖² ≤ a b`
  have hsq : ‖B‖ ^ 2 ≤ a * b := by
    by_cases hb0' : b = 0
    · rw [hb0', mul_zero]
      by_contra hlt
      rw [not_le] at hlt
      by_cases ha0' : a = 0
      · have := hpoly 1
        rw [hb0', ha0'] at this
        linarith
      · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha0')
        have := hpoly (‖B‖ ^ 2 / a)
        rw [hb0'] at this
        have h2 : (‖B‖ ^ 2 / a) ^ 2 * a = ‖B‖ ^ 2 / a * ‖B‖ ^ 2 := by
          field_simp
        rw [h2] at this
        have h3 : ‖B‖ ^ 2 / a * ‖B‖ ^ 2 - 2 * (‖B‖ ^ 2 / a) * ‖B‖ ^ 2 =
            -(‖B‖ ^ 2 / a * ‖B‖ ^ 2) := by ring
        rw [mul_zero, add_zero, h3] at this
        have h4 : 0 < ‖B‖ ^ 2 / a * ‖B‖ ^ 2 := by positivity
        linarith
    · have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb0')
      have := hpoly b
      have h2 : b ^ 2 * a - 2 * b * ‖B‖ ^ 2 + ‖B‖ ^ 2 * b = b * (a * b - ‖B‖ ^ 2) := by ring
      rw [h2] at this
      have := (mul_nonneg_iff_of_pos_left hbpos).mp this
      linarith
  rw [← Real.sqrt_mul ha0]
  exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg ha0 hb0)).2 hsq

/-- `√a √b ≤ (t a + b / t)/2` for `t > 0`. -/
theorem sqrt_mul_sqrt_le_of_pos {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) :
    Real.sqrt a * Real.sqrt b ≤ t / 2 * a + 1 / (2 * t) * b := by
  have hta : 0 ≤ t * a := mul_nonneg ht.le ha
  have hbt : 0 ≤ b / t := div_nonneg hb ht.le
  have h1 : Real.sqrt (t * a) * Real.sqrt (b / t) = Real.sqrt a * Real.sqrt b := by
    rw [← Real.sqrt_mul hta, ← Real.sqrt_mul ha]
    congr 1
    field_simp
  have h2 := Real.mul_self_sqrt hta
  have h3 := Real.mul_self_sqrt hbt
  have h4 := sq_nonneg (Real.sqrt (t * a) - Real.sqrt (b / t))
  have h5 : t / 2 * a + 1 / (2 * t) * b = (t * a + b / t) / 2 := by
    field_simp
  rw [h5, ← h1]
  nlinarith

/-- Optimisation in `t`: `X ≤ (t A + B/t)/2` for all `t > 0` forces `X ≤ √A √B`. -/
theorem le_sqrt_mul_sqrt_of_forall_pos {X A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → X ≤ t / 2 * A + 1 / (2 * t) * B) :
    X ≤ Real.sqrt A * Real.sqrt B := by
  by_cases hA0 : A = 0
  · rw [hA0, Real.sqrt_zero, zero_mul]
    by_contra hX
    rw [not_le] at hX
    have := h (B / X + 1) (by positivity)
    rw [hA0, mul_zero, zero_add] at this
    have hpos : 0 < B / X + 1 := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at this
    have : X * (2 * (B / X + 1)) = 2 * B + 2 * X := by
      field_simp
    linarith
  by_cases hB0 : B = 0
  · rw [hB0, Real.sqrt_zero, mul_zero]
    by_contra hX
    rw [not_le] at hX
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have := h (X / A) (by positivity)
    rw [hB0, mul_zero, add_zero] at this
    have h2 : X / A / 2 * A = X / 2 := by field_simp
    rw [h2] at this
    linarith
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hsA := Real.sqrt_pos.2 hApos
    have hsB := Real.sqrt_pos.2 hBpos
    have := h (Real.sqrt B / Real.sqrt A) (by positivity)
    have hA' := Real.mul_self_sqrt hA
    have hB' := Real.mul_self_sqrt hB
    have key : ∀ sA sB : ℝ, 0 < sA → 0 < sB →
        sB / sA / 2 * (sA * sA) + 1 / (2 * (sB / sA)) * (sB * sB) = sA * sB := by
      intro sA sB hsA hsB
      field_simp
      ring
    have h2 := key _ _ hsA hsB
    rw [hA', hB'] at h2
    rw [h2] at this
    exact this

/-- The sesquilinear form as a real continuous linear functional on `H → H → ℂ`. -/
noncomputable def sesqCLM (x y : H → ℂ) : (H → H → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => sesqForm x y (Matrix.of M)
      map_add' := fun M N => by
        change sesqForm x y (Matrix.of M + Matrix.of N) = _
        rw [sesqForm_add]
      map_smul' := fun c M => by
        change sesqForm x y (Matrix.of (c • M)) = c • sesqForm x y (Matrix.of M)
        have : Matrix.of (c • M) = (c : ℂ) • Matrix.of M := by
          ext i j
          simp [Complex.real_smul]
        rw [this, sesqForm_smul, Complex.real_smul] }

@[simp]
theorem sesqCLM_apply (x y : H → ℂ) (M : H → H → ℂ) :
    sesqCLM x y M = sesqForm x y (Matrix.of M) := rfl

theorem sesqCLM_smul (x y : H → ℂ) (a : ℂ) (M : H → H → ℂ) :
    sesqCLM x y (a • M) = a * sesqCLM x y M := by
  rw [sesqCLM_apply, sesqCLM_apply]
  exact sesqForm_smul x y a (Matrix.of M)

theorem sesqCLM_self (x : H → ℂ) (M : H → H → ℂ) : (sesqCLM x x M).re = quadFormCLM x M := rfl

/-- The quadratic form is bounded by the operator norm: `Re ⟨x, W x⟩ ≤ ‖W‖ ‖x‖²`. -/
theorem quadFormCLM_le_l2_opNorm (x : H → ℂ) (W : H → H → ℂ) :
    quadFormCLM x W ≤ ‖Matrix.of W‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ H)‖ ^ 2 := by
  set X : EuclideanSpace ℂ H := WithLp.toLp 2 x
  set Y : EuclideanSpace ℂ H := WithLp.toLp 2 (Matrix.of W *ᵥ x)
  have hinner : quadFormCLM x W = RCLike.re ⟪X, Y⟫_ℂ := by
    rw [quadFormCLM_apply, EuclideanSpace.inner_eq_star_dotProduct]
    change (star x ⬝ᵥ (Matrix.of W *ᵥ x)).re = _
    rw [dotProduct_comm]
    rfl
  rw [hinner]
  calc RCLike.re ⟪X, Y⟫_ℂ ≤ ‖X‖ * ‖Y‖ := re_inner_le_norm X Y
    _ ≤ ‖X‖ * (‖Matrix.of W‖ * ‖X‖) := by
        gcongr
        exact Matrix.l2_opNorm_mulVec (Matrix.of W) X
    _ = ‖Matrix.of W‖ * ‖X‖ ^ 2 := by ring

namespace PositiveTailMeasure

variable (μ : PositiveTailMeasure H)

/-- The complex measure `E ↦ ⟨x, μ(E) y⟩`. -/
noncomputable def sesqMeasure (x y : H → ℂ) : VectorMeasure ℝ ℂ :=
  μ.toVectorMeasure.mapRange (sesqCLM x y).toLinearMap.toAddMonoidHom (sesqCLM x y).continuous

@[simp]
theorem sesqMeasure_apply (x y : H → ℂ) (s : Set ℝ) :
    μ.sesqMeasure x y s = sesqCLM x y (μ.toVectorMeasure s) := rfl

theorem variation_sesqMeasure_le (x y : H → ℂ) :
    (μ.sesqMeasure x y).variation ≤ ‖sesqCLM x y‖₊ • μ.toVectorMeasure.variation := by
  refine VectorMeasure.variation_le_of_forall_enorm_le fun s hs => ?_
  rw [sesqMeasure_apply, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [ContinuousLinearMap.le_opENorm, VectorMeasure.enorm_measure_le_variation,
    ← enorm_eq_nnnorm]

theorem formMeasure_le_smul_variation (x : H → ℂ) :
    μ.formMeasure x ≤ ‖quadFormCLM x‖₊ • μ.toVectorMeasure.variation := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [formMeasure_apply μ x hs, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  calc ENNReal.ofReal (quadFormCLM x (μ.toVectorMeasure s))
      ≤ ENNReal.ofReal ‖quadFormCLM x (μ.toVectorMeasure s)‖ :=
        ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ‖quadFormCLM x (μ.toVectorMeasure s)‖ₑ := ofReal_norm _
    _ ≤ _ := by
        grw [ContinuousLinearMap.le_opENorm, VectorMeasure.enorm_measure_le_variation,
          ← enorm_eq_nnnorm]

/-- **Sesquilinear bridge**: `⟨x, (∫ f dμ) y⟩ = ∫ f d⟨x, μ y⟩` for `μ`-integrable complex `f`. -/
theorem sesqCLM_integral (x y : H → ℂ) {f : ℝ → ℂ}
    (hf : Integrable f μ.toVectorMeasure.variation) :
    sesqCLM x y (VectorMeasure.integral μ.toVectorMeasure f (ContinuousLinearMap.lsmul ℝ ℂ)) =
      VectorMeasure.integral (μ.sesqMeasure x y) f (ContinuousLinearMap.lsmul ℝ ℂ) := by
  set C := sesqCLM x y
  set B' : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.compL ℝ (H → H → ℂ) (H → H → ℂ) ℂ C) ∘L
      ContinuousLinearMap.lsmul ℝ ℂ
  rw [VectorMeasure.continuousLinearMap_apply_integral hf]
  have hT : μ.toVectorMeasure.transpose B' =
      (μ.sesqMeasure x y).transpose (ContinuousLinearMap.lsmul ℝ ℂ) := by
    refine VectorMeasure.ext fun s hs => ?_
    change B'.flip (μ.toVectorMeasure s) =
      (ContinuousLinearMap.lsmul ℝ ℂ).flip (μ.sesqMeasure x y s)
    ext a
    change C (a • μ.toVectorMeasure s) = a • C (μ.toVectorMeasure s)
    rw [smul_eq_mul]
    exact sesqCLM_smul x y a _
  have h₁ := MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure μ.toVectorMeasure B'
  have h₂ : DominatedFinMeasAdditive μ.toVectorMeasure.variation
      ((μ.sesqMeasure x y).transpose (ContinuousLinearMap.lsmul ℝ ℂ)) ‖B'‖ := hT ▸ h₁
  have hstep1 : VectorMeasure.integral μ.toVectorMeasure f B' =
      setToFun μ.toVectorMeasure.variation
        ((μ.sesqMeasure x y).transpose (ContinuousLinearMap.lsmul ℝ ℂ)) h₂ f := by
    rw [VectorMeasure.integral_eq_setToFun]
    exact setToFun_congr_left' h₁ h₂ (fun s _ _ => by rw [hT]) f
  rw [hstep1, VectorMeasure.integral_eq_setToFun]
  exact setToFun_congr_measure_of_integrable (‖C‖₊ : ℝ≥0∞) ENNReal.coe_ne_top
    (μ.variation_sesqMeasure_le x y) h₂ _ f hf

/-- The scalarised operator integral is bounded by the integral of `‖f‖` against the variation
of the sesquilinear measure. -/
theorem norm_sesqCLM_integral_le (x y : H → ℂ) {f : ℝ → ℂ}
    (hf : Integrable f μ.toVectorMeasure.variation) :
    ‖sesqCLM x y (VectorMeasure.integral μ.toVectorMeasure f (ContinuousLinearMap.lsmul ℝ ℂ))‖ ≤
      ∫ a, ‖f a‖ ∂(μ.sesqMeasure x y).variation := by
  rw [μ.sesqCLM_integral x y hf]
  refine VectorMeasure.norm_integral_le_integral_norm.trans ?_
  exact mul_le_of_le_one_left (integral_nonneg fun a => norm_nonneg _)
    ContinuousLinearMap.opNorm_lsmul_le

/-- The variation of `⟨x, μ y⟩` is dominated by `(t/2) ⟨x, μ x⟩ + (1/(2t)) ⟨y, μ y⟩`. -/
theorem variation_sesqMeasure_le_smul_add_smul (x y : H → ℂ) {t : ℝ} (ht : 0 < t) :
    (μ.sesqMeasure x y).variation ≤
      ENNReal.ofReal (t / 2) • μ.formMeasure x + ENNReal.ofReal (1 / (2 * t)) • μ.formMeasure y := by
  refine VectorMeasure.variation_le_of_forall_enorm_le fun s hs => ?_
  have ha : 0 ≤ quadFormCLM x (μ.toVectorMeasure s) := μ.signedForm_nonneg x s
  have hb : 0 ≤ quadFormCLM y (μ.toVectorMeasure s) := μ.signedForm_nonneg y s
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, formMeasure_apply μ x hs,
    formMeasure_apply μ y hs, smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), sesqMeasure_apply, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcs := posSemidef_norm_sesqForm_le (μ.posSemidef_apply s) x y
  have hamgm := sqrt_mul_sqrt_le_of_pos ha hb ht
  simp only [quadFormCLM_apply, sesqCLM_apply] at ha hb hamgm ⊢
  linarith

/-- Integral form of the domination: `∫ w d|⟨x, μ y⟩| ≤ (t/2) ∫ w d⟨x, μ x⟩ + (1/(2t)) ∫ w d⟨y, μ y⟩`
for nonnegative integrable `w`. -/
theorem integral_variation_sesqMeasure_le (x y : H → ℂ) {w : ℝ → ℝ}
    (hw : Integrable w μ.toVectorMeasure.variation)
    (hw0 : ∀ᵐ a ∂μ.toVectorMeasure.variation, 0 ≤ w a) {t : ℝ} (ht : 0 < t) :
    ∫ a, w a ∂(μ.sesqMeasure x y).variation ≤
      t / 2 * ∫ a, w a ∂(μ.formMeasure x) + 1 / (2 * t) * ∫ a, w a ∂(μ.formMeasure y) := by
  have hx : Integrable w (μ.formMeasure x) :=
    hw.of_measure_le_smul ENNReal.coe_ne_top (μ.formMeasure_le_smul_variation x)
  have hy : Integrable w (μ.formMeasure y) :=
    hw.of_measure_le_smul ENNReal.coe_ne_top (μ.formMeasure_le_smul_variation y)
  have hx0 : ∀ᵐ a ∂μ.formMeasure x, 0 ≤ w a :=
    (Measure.absolutelyContinuous_of_le_smul (μ.formMeasure_le_smul_variation x)).ae_le hw0
  have hy0 : ∀ᵐ a ∂μ.formMeasure y, 0 ≤ w a :=
    (Measure.absolutelyContinuous_of_le_smul (μ.formMeasure_le_smul_variation y)).ae_le hw0
  set m : Measure ℝ :=
    ENNReal.ofReal (t / 2) • μ.formMeasure x + ENNReal.ofReal (1 / (2 * t)) • μ.formMeasure y
  have hm : Integrable w m :=
    (hx.smul_measure ENNReal.ofReal_ne_top).add_measure (hy.smul_measure ENNReal.ofReal_ne_top)
  have hm0 : 0 ≤ᵐ[m] w := by
    rw [Filter.EventuallyLE, ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure hx0 _, Measure.ae_smul_measure hy0 _⟩
  calc ∫ a, w a ∂(μ.sesqMeasure x y).variation ≤ ∫ a, w a ∂m :=
        integral_mono_measure (μ.variation_sesqMeasure_le_smul_add_smul x y ht) hm0 hm
    _ = _ := by
        rw [integral_add_measure (hx.smul_measure ENNReal.ofReal_ne_top)
          (hy.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
          smul_eq_mul, smul_eq_mul]

/-- **Sesquilinear positive-weighted bound.**  If `‖c‖ ≤ κ w` `μ`-a.e. with `w ≥ 0`, then
`‖⟨x, (∫ c dμ) y⟩‖ ≤ κ √⟨x, (∫ w dμ) x⟩ √⟨y, (∫ w dμ) y⟩`. -/
theorem norm_sesqCLM_integral_le_of_norm_le (x y : H → ℂ) {c : ℝ → ℂ} {w : ℝ → ℝ}
    (hc : Integrable c μ.toVectorMeasure.variation)
    (hw : Integrable w μ.toVectorMeasure.variation)
    (hw0 : ∀ᵐ a ∂μ.toVectorMeasure.variation, 0 ≤ w a) {κ : ℝ} (hκ : 0 ≤ κ)
    (hcw : ∀ᵐ a ∂μ.toVectorMeasure.variation, ‖c a‖ ≤ κ * w a) :
    ‖sesqCLM x y (VectorMeasure.integral μ.toVectorMeasure c (ContinuousLinearMap.lsmul ℝ ℂ))‖ ≤
      κ * (Real.sqrt (quadFormCLM x
          (VectorMeasure.integral μ.toVectorMeasure w (ContinuousLinearMap.lsmul ℝ ℝ))) *
        Real.sqrt (quadFormCLM y
          (VectorMeasure.integral μ.toVectorMeasure w (ContinuousLinearMap.lsmul ℝ ℝ)))) := by
  set Var := (μ.sesqMeasure x y).variation
  have hac : Var ≪ μ.toVectorMeasure.variation :=
    Measure.absolutelyContinuous_of_le_smul (μ.variation_sesqMeasure_le x y)
  have hcV : Integrable (fun a => ‖c a‖) Var :=
    (hc.of_measure_le_smul ENNReal.coe_ne_top (μ.variation_sesqMeasure_le x y)).norm
  have hwV : Integrable w Var :=
    hw.of_measure_le_smul ENNReal.coe_ne_top (μ.variation_sesqMeasure_le x y)
  have hw0V : ∀ᵐ a ∂Var, 0 ≤ w a := hac.ae_le hw0
  have hcwV : ∀ᵐ a ∂Var, ‖c a‖ ≤ κ * w a := hac.ae_le hcw
  rw [μ.quadFormCLM_integral x hw, μ.quadFormCLM_integral y hw]
  calc ‖sesqCLM x y (VectorMeasure.integral μ.toVectorMeasure c (ContinuousLinearMap.lsmul ℝ ℂ))‖
      ≤ ∫ a, ‖c a‖ ∂Var := μ.norm_sesqCLM_integral_le x y hc
    _ ≤ ∫ a, κ * w a ∂Var := integral_mono_ae hcV (hwV.const_mul κ) hcwV
    _ = κ * ∫ a, w a ∂Var := integral_const_mul κ w
    _ ≤ κ * (Real.sqrt (∫ a, w a ∂μ.formMeasure x) * Real.sqrt (∫ a, w a ∂μ.formMeasure y)) := by
        gcongr
        refine le_sqrt_mul_sqrt_of_forall_pos (integral_nonneg_of_ae ?_) (integral_nonneg_of_ae ?_)
          fun t ht => μ.integral_variation_sesqMeasure_le x y hw hw0 ht
        · exact (Measure.absolutelyContinuous_of_le_smul
            (μ.formMeasure_le_smul_variation x)).ae_le hw0
        · exact (Measure.absolutelyContinuous_of_le_smul
            (μ.formMeasure_le_smul_variation y)).ae_le hw0

/-- **Positive-weighted operator-norm bound for operator integrals.**  If `‖c‖ ≤ κ w` `μ`-a.e.
with `w ≥ 0`, then `‖∫ c dμ‖ ≤ κ ‖∫ w dμ‖` in the operator norm. -/
theorem l2_opNorm_integral_le_of_norm_le {c : ℝ → ℂ} {w : ℝ → ℝ}
    (hc : Integrable c μ.toVectorMeasure.variation)
    (hw : Integrable w μ.toVectorMeasure.variation)
    (hw0 : ∀ᵐ a ∂μ.toVectorMeasure.variation, 0 ≤ w a) {κ : ℝ} (hκ : 0 ≤ κ)
    (hcw : ∀ᵐ a ∂μ.toVectorMeasure.variation, ‖c a‖ ≤ κ * w a) :
    ‖Matrix.of (VectorMeasure.integral μ.toVectorMeasure c (ContinuousLinearMap.lsmul ℝ ℂ))‖ ≤
      κ * ‖Matrix.of (VectorMeasure.integral μ.toVectorMeasure (fun a => (w a : ℂ))
        (ContinuousLinearMap.lsmul ℝ ℂ))‖ := by
  rw [μ.integral_ofReal_lsmul hw]
  set C := VectorMeasure.integral μ.toVectorMeasure c (ContinuousLinearMap.lsmul ℝ ℂ)
  set W := VectorMeasure.integral μ.toVectorMeasure w (ContinuousLinearMap.lsmul ℝ ℝ)
  set K := κ * ‖Matrix.of W‖
  have hK : 0 ≤ K := mul_nonneg hκ (norm_nonneg _)
  -- the sesquilinear bound in terms of Euclidean norms
  have hbound : ∀ x y : H → ℂ, ‖sesqCLM x y C‖ ≤
      K * (‖(WithLp.toLp 2 x : EuclideanSpace ℂ H)‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ H)‖) := by
    intro x y
    refine (μ.norm_sesqCLM_integral_le_of_norm_le x y hc hw hw0 hκ hcw).trans ?_
    have hx := quadFormCLM_le_l2_opNorm x W
    have hy := quadFormCLM_le_l2_opNorm y W
    have hsx : Real.sqrt (quadFormCLM x W) ≤
        Real.sqrt ‖Matrix.of W‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ H)‖ := by
      calc Real.sqrt (quadFormCLM x W)
          ≤ Real.sqrt (‖Matrix.of W‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ H)‖ ^ 2) :=
            Real.sqrt_le_sqrt hx
        _ = _ := by rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have hsy : Real.sqrt (quadFormCLM y W) ≤
        Real.sqrt ‖Matrix.of W‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ H)‖ := by
      calc Real.sqrt (quadFormCLM y W)
          ≤ Real.sqrt (‖Matrix.of W‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ H)‖ ^ 2) :=
            Real.sqrt_le_sqrt hy
        _ = _ := by rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have hprod := mul_le_mul hsx hsy (Real.sqrt_nonneg _) (by positivity)
    have hW := Real.mul_self_sqrt (norm_nonneg (Matrix.of W))
    calc κ * (Real.sqrt (quadFormCLM x W) * Real.sqrt (quadFormCLM y W))
        ≤ κ * ((Real.sqrt ‖Matrix.of W‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ H)‖) *
            (Real.sqrt ‖Matrix.of W‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ H)‖)) := by
          gcongr
      _ = K * (‖(WithLp.toLp 2 x : EuclideanSpace ℂ H)‖ *
            ‖(WithLp.toLp 2 y : EuclideanSpace ℂ H)‖) := by
          simp only [K]
          linear_combination (κ * (‖(WithLp.toLp 2 x : EuclideanSpace ℂ H)‖ *
            ‖(WithLp.toLp 2 y : EuclideanSpace ℂ H)‖)) * hW
  -- pass to the operator norm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun Y => ?_
  set T := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (Matrix.of C)
  set X : EuclideanSpace ℂ H := T Y
  have hXY : WithLp.ofLp X = Matrix.of C *ᵥ WithLp.ofLp Y := rfl
  have hsq : ‖X‖ ^ 2 = ‖sesqCLM (WithLp.ofLp X) (WithLp.ofLp Y) C‖ := by
    have h1 : ⟪X, X⟫_ℂ = sesqCLM (WithLp.ofLp X) (WithLp.ofLp Y) C := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, sesqCLM_apply, sesqForm, ← hXY, dotProduct_comm]
    rw [← h1, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
  by_cases hX0 : ‖X‖ = 0
  · rw [hX0]
    positivity
  · have hXpos : 0 < ‖X‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hX0)
    have h := hbound (WithLp.ofLp X) (WithLp.ofLp Y)
    rw [← hsq] at h
    have h' : ‖X‖ * ‖X‖ ≤ (K * ‖Y‖) * ‖X‖ := by
      calc ‖X‖ * ‖X‖ = ‖X‖ ^ 2 := (sq _).symm
        _ ≤ K * (‖X‖ * ‖Y‖) := h
        _ = (K * ‖Y‖) * ‖X‖ := by ring
    exact le_of_mul_le_mul_right h' hXpos

/-! ## The memory RG data -/

/-- The cutoff measure `μ|_{(0,Λ]}` (`eq:supp-memory-RG`). -/
noncomputable def cutoff (Λ : ℝ) : PositiveTailMeasure H where
  toVectorMeasure := μ.toVectorMeasure.restrict (Iic Λ)
  posSemidef s hs := by
    rw [VectorMeasure.restrict_apply _ measurableSet_Iic hs]
    exact μ.posSemidef _ (hs.inter measurableSet_Iic)
  eq_zero_of_subset_Iic s hs hsub := by
    rw [VectorMeasure.restrict_apply _ measurableSet_Iic hs]
    exact μ.eq_zero_of_subset_Iic _ (hs.inter measurableSet_Iic) (inter_subset_left.trans hsub)

theorem cutoff_toVectorMeasure (Λ : ℝ) :
    (μ.cutoff Λ).toVectorMeasure = μ.toVectorMeasure.restrict (Iic Λ) := rfl

/-- The inverse-moment head correction `Q_{>Λ} = ∫_{(Λ,∞)} λ⁻¹ dμ(λ)` (`eq:supp-memory-head`). -/
noncomputable def headCorrection (Λ : ℝ) : Matrix H H ℂ :=
  Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
    (fun lam : ℝ => ((lam : ℂ))⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ))

/-- The dynamic function `F_{A,μ}(z) = A - z - Σ_μ(z)` (`eq:supp-memory-head`). -/
noncomputable def dynamicFunction (A : Matrix H H ℂ) (z : ℂ) : Matrix H H ℂ :=
  A - z • (1 : Matrix H H ℂ) - μ.stieltjesSelfEnergy z

/-- **`eq:supp-memory-RG`.**  The memory cutoff map `RG_Λ(A, μ) = (A - Q_{>Λ}, μ|_{(0,Λ]})`. -/
noncomputable def rg (A : Matrix H H ℂ) (Λ : ℝ) : Matrix H H ℂ × PositiveTailMeasure H :=
  (A - μ.headCorrection Λ, μ.cutoff Λ)

/-- Bounded measurable functions are integrable on a set against the variation of `μ`. -/
theorem integrableOn_of_norm_le {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℂ}
    (hf : Measurable f) {K : ℝ} (hK : ∀ x ∈ s, ‖f x‖ ≤ K) :
    Integrable f (μ.toVectorMeasure.restrict s).variation := by
  rw [VectorMeasure.variation_restrict hs]
  refine Integrable.mono' (integrable_const K) hf.aestronglyMeasurable ?_
  rw [ae_restrict_iff' hs]
  exact ae_of_all _ hK

/-- Measurability of the resolvent kernel `λ ↦ (λ - z)⁻¹`. -/
theorem measurable_resolvent (z : ℂ) : Measurable fun lam : ℝ => ((lam : ℂ) - z)⁻¹ :=
  (Complex.measurable_ofReal.sub measurable_const).inv

/-- For `z ∉ [0,∞)` the resolvent kernel is bounded on `[0,∞)`, hence `μ`-integrable. -/
theorem integrable_resolvent {z : ℂ} (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) :
    Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ.toVectorMeasure.variation := by
  -- distance from `z` to `[0, ∞)`
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
  have hmem : ∀ᵐ lam ∂μ.toVectorMeasure.variation, 0 ≤ lam := by
    rw [ae_iff]
    refine measure_mono_null (t := Iic 0) (fun x (hx : ¬ (0 : ℝ) ≤ x) => (not_le.mp hx).le) ?_
    exact (VectorMeasure.variation_apply_eq_zero measurableSet_Iic).2
      fun t hts ht => μ.eq_zero_of_subset_Iic t ht hts
  refine Integrable.mono' (integrable_const δ⁻¹) (measurable_resolvent z).aestronglyMeasurable ?_
  filter_upwards [hmem] with lam hlam
  rw [norm_inv]
  exact inv_anti₀ hδpos (hlow lam hlam)

/-- The resolvent kernel at `z = 0` is the inverse-moment kernel. -/
theorem resolvent_zero : (fun lam : ℝ => ((lam : ℂ) - 0)⁻¹) = fun lam : ℝ => ((lam : ℂ))⁻¹ := by
  funext lam
  rw [sub_zero]

/-- Splitting the Stieltjes integral at the cutoff. -/
theorem stieltjesSelfEnergy_split (Λ : ℝ) {z : ℂ}
    (hz : Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ.toVectorMeasure.variation) :
    μ.stieltjesSelfEnergy z = (μ.cutoff Λ).stieltjesSelfEnergy z +
      Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
        (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
  have h := VectorMeasure.setIntegral_add_compl (μ := μ.toVectorMeasure)
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (f := fun lam : ℝ => ((lam : ℂ) - z)⁻¹) (s := Iic Λ) measurableSet_Iic hz
  rw [Set.compl_Iic] at h
  unfold stieltjesSelfEnergy
  rw [cutoff_toVectorMeasure, ← h]
  rfl

/-- **`eq:supp-memory-static-preserved`.**  The static value is preserved by the cutoff:
`F_{RG_Λ(A,μ)}(0) = F_{A,μ}(0)`, provided `λ⁻¹` is `μ`-integrable (i.e. `F_{A,μ}(0)` exists). -/
theorem dynamicFunction_rg_zero (A : Matrix H H ℂ) (Λ : ℝ)
    (hint : Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹) μ.toVectorMeasure.variation) :
    (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 0 = μ.dynamicFunction A 0 := by
  have hint' : Integrable (fun lam : ℝ => ((lam : ℂ) - 0)⁻¹) μ.toVectorMeasure.variation := by
    rw [resolvent_zero]; exact hint
  simp only [rg, dynamicFunction]
  rw [μ.stieltjesSelfEnergy_split Λ hint']
  unfold headCorrection
  rw [resolvent_zero]
  abel

/-- The inverse-moment kernel `λ⁻¹` is integrable on `(Λ, ∞)` for `Λ > 0`. -/
theorem integrableOn_inv_Ioi {Λ : ℝ} (hΛ : 0 < Λ) :
    Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹) (μ.toVectorMeasure.restrict (Ioi Λ)).variation := by
  refine μ.integrableOn_of_norm_le measurableSet_Ioi Complex.measurable_ofReal.inv (K := Λ⁻¹)
    fun x hx => ?_
  have hx' : Λ < x := hx
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hΛ.trans hx')]
  exact inv_anti₀ hΛ hx'.le

/-- The screening difference is the head-corrected tail integral. -/
theorem dynamicFunction_sub_rg (A : Matrix H H ℂ) {Λ : ℝ} (hΛ : 0 < Λ) {z : ℂ}
    (hz : Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ.toVectorMeasure.variation) :
    μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z =
      Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
        (fun lam : ℝ => ((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
  simp only [rg, dynamicFunction]
  rw [μ.stieltjesSelfEnergy_split Λ hz]
  unfold headCorrection
  have hsub := VectorMeasure.integral_fun_sub (μ := μ.toVectorMeasure.restrict (Ioi Λ))
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (f := fun lam : ℝ => ((lam : ℂ))⁻¹) (g := fun lam : ℝ => ((lam : ℂ) - z)⁻¹)
    (μ.integrableOn_inv_Ioi hΛ)
    (VectorMeasure.Integrable.integrableOn (μ := μ.toVectorMeasure) hz)
  have : Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
      (fun lam : ℝ => ((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) =
      Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
        (fun lam : ℝ => ((lam : ℂ))⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) -
      Matrix.of (VectorMeasure.integral (μ.toVectorMeasure.restrict (Ioi Λ))
        (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
    rw [hsub]
    rfl
  rw [this]
  abel

/-- **`eq:supp-memory-screen-error`** (integrability form).  For `‖z‖ ≤ r < Λ`, if
`(λ - z)⁻¹` is `μ`-integrable, then
`‖F_{A,μ}(z) - F_{RG_Λ(A,μ)}(z)‖ ≤ r/(Λ - r) ‖Q_{>Λ}‖` in the operator norm. -/
theorem norm_dynamicFunction_sub_rg_le_of_integrable (A : Matrix H H ℂ) {Λ r : ℝ} (hr : r < Λ)
    {z : ℂ} (hz : ‖z‖ ≤ r)
    (hzint : Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ.toVectorMeasure.variation) :
    ‖μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z‖ ≤
      r / (Λ - r) * ‖μ.headCorrection Λ‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hΛr : 0 < Λ - r := sub_pos.mpr hr
  have hΛ : 0 < Λ := lt_of_le_of_lt hr0 hr
  rw [μ.dynamicFunction_sub_rg A hΛ hzint]
  -- the tail measure as a positive tail measure
  set ν : PositiveTailMeasure H :=
    { toVectorMeasure := μ.toVectorMeasure.restrict (Ioi Λ)
      posSemidef := fun s hs => by
        rw [VectorMeasure.restrict_apply _ measurableSet_Ioi hs]
        exact μ.posSemidef _ (hs.inter measurableSet_Ioi)
      eq_zero_of_subset_Iic := fun s hs hsub => by
        rw [VectorMeasure.restrict_apply _ measurableSet_Ioi hs]
        exact μ.eq_zero_of_subset_Iic _ (hs.inter measurableSet_Ioi)
          (inter_subset_left.trans hsub) } with hν
  have hνmeas : ν.toVectorMeasure = μ.toVectorMeasure.restrict (Ioi Λ) := rfl
  have hvar : ν.toVectorMeasure.variation = μ.toVectorMeasure.variation.restrict (Ioi Λ) := by
    rw [hνmeas, VectorMeasure.variation_restrict measurableSet_Ioi]
  have hmem : ∀ᵐ lam ∂ν.toVectorMeasure.variation, Λ < lam := by
    rw [hvar, ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun lam h => h
  have hc : Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹)
      ν.toVectorMeasure.variation := by
    rw [hνmeas]
    have h1 : Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹)
        (μ.toVectorMeasure.restrict (Ioi Λ)).variation := μ.integrableOn_inv_Ioi hΛ
    have h2 : Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹)
        (μ.toVectorMeasure.restrict (Ioi Λ)).variation :=
      VectorMeasure.Integrable.integrableOn (μ := μ.toVectorMeasure) hzint
    exact h1.sub h2
  have hw : Integrable (fun lam : ℝ => lam⁻¹) ν.toVectorMeasure.variation := by
    rw [hvar]
    refine Integrable.mono' (integrable_const Λ⁻¹) measurable_inv.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun lam (h : Λ < lam) => ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hΛ.trans h))]
    exact inv_anti₀ hΛ h.le
  have hw0 : ∀ᵐ lam ∂ν.toVectorMeasure.variation, 0 ≤ lam⁻¹ := by
    filter_upwards [hmem] with lam h
    exact (inv_pos.mpr (hΛ.trans h)).le
  have hcw : ∀ᵐ (lam : ℝ) ∂ν.toVectorMeasure.variation,
      ‖((lam : ℂ))⁻¹ - ((lam : ℂ) - z)⁻¹‖ ≤ r / (Λ - r) * lam⁻¹ := by
    filter_upwards [hmem] with lam h
    exact MemoryRG.FiniteAtomicTailMeasure.norm_inv_sub_inv_le h hr hz
  have key := ν.l2_opNorm_integral_le_of_norm_le hc hw hw0 (div_nonneg hr0 hΛr.le) hcw
  have hhead : μ.headCorrection Λ = Matrix.of (VectorMeasure.integral ν.toVectorMeasure
      (fun a : ℝ => ((a⁻¹ : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
    unfold headCorrection
    rw [hνmeas]
    congr 1
    funext a
    push_cast
    rfl
  rw [hhead]
  exact key

/-- **`eq:supp-memory-screen-error`.**  For `‖z‖ ≤ r < Λ` with `z ∉ [0,∞)` (the domain of the
Stieltjes self-energy): `‖F_{A,μ}(z) - F_{RG_Λ(A,μ)}(z)‖ ≤ r/(Λ - r) ‖Q_{>Λ}‖`. -/
theorem norm_dynamicFunction_sub_rg_le (A : Matrix H H ℂ) {Λ r : ℝ} (hr : r < Λ)
    {z : ℂ} (hz : ‖z‖ ≤ r) (hzdom : ¬ (z.im = 0 ∧ 0 ≤ z.re)) :
    ‖μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z‖ ≤
      r / (Λ - r) * ‖μ.headCorrection Λ‖ :=
  μ.norm_dynamicFunction_sub_rg_le_of_integrable A hr hz (μ.integrable_resolvent hzdom)

/-- The cutoff measures compose: `(μ|_{(0,Λ₁]})|_{(0,Λ₂]} = μ|_{(0,Λ₂]}` for `Λ₂ ≤ Λ₁`. -/
theorem cutoff_cutoff {Λ₁ Λ₂ : ℝ} (h : Λ₂ ≤ Λ₁) : (μ.cutoff Λ₁).cutoff Λ₂ = μ.cutoff Λ₂ := by
  rw [ext_iff', cutoff_toVectorMeasure, cutoff_toVectorMeasure, cutoff_toVectorMeasure,
    VectorMeasure.restrict_restrict _ measurableSet_Iic measurableSet_Iic, Set.Iic_inter_Iic,
    min_eq_left h]

/-- The head corrections add over disjoint shells: `Q^{μ}_{>Λ₁} + Q^{μ|Λ₁}_{>Λ₂} = Q^{μ}_{>Λ₂}`
for `0 < Λ₂ ≤ Λ₁`. -/
theorem headCorrection_add_headCorrection_cutoff {Λ₁ Λ₂ : ℝ} (h2 : 0 < Λ₂) (h : Λ₂ ≤ Λ₁) :
    μ.headCorrection Λ₁ + (μ.cutoff Λ₁).headCorrection Λ₂ = μ.headCorrection Λ₂ := by
  unfold headCorrection
  rw [cutoff_toVectorMeasure,
    VectorMeasure.restrict_restrict _ measurableSet_Ioi measurableSet_Iic]
  have hint : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Ioi Λ₂ →
      Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹) (μ.toVectorMeasure.restrict s).variation := by
    intro s hs hsub
    refine μ.integrableOn_of_norm_le hs (Complex.measurable_ofReal.inv) (K := Λ₂⁻¹)
      fun x hx => ?_
    have hx' : Λ₂ < x := hsub hx
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h2.trans hx')]
    exact inv_anti₀ h2 hx'.le
  have hu := VectorMeasure.setIntegral_union (μ := μ.toVectorMeasure)
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (f := fun lam : ℝ => ((lam : ℂ))⁻¹) (s := Ioi Λ₁) (t := Ioi Λ₂ ∩ Iic Λ₁)
    (by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd (show x ≤ Λ₁ from hx'.2) (not_le.mpr (show Λ₁ < x from hx)))
    measurableSet_Ioi (measurableSet_Ioi.inter measurableSet_Iic)
    (hint measurableSet_Ioi fun x hx => lt_of_le_of_lt h hx)
    (hint (measurableSet_Ioi.inter measurableSet_Iic) fun x hx => hx.1)
  have hset : Ioi Λ₁ ∪ Ioi Λ₂ ∩ Iic Λ₁ = Ioi Λ₂ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_inter_iff, Set.mem_Iic]
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact lt_of_le_of_lt h hx
      · exact hx
    · intro hx
      by_cases hx' : Λ₁ < x
      · exact Or.inl hx'
      · exact Or.inr ⟨hx, not_lt.mp hx'⟩
  rw [hset] at hu
  rw [hu]
  rfl

/-- **`eq:supp-memory-semigroup`.**  Two successive cutoffs `0 < Λ₂ ≤ Λ₁` compose to the lower
cutoff: `RG_{Λ₂} ∘ RG_{Λ₁} = RG_{Λ₂}`. -/
theorem rg_rg (A : Matrix H H ℂ) {Λ₁ Λ₂ : ℝ} (h2 : 0 < Λ₂) (h : Λ₂ ≤ Λ₁) :
    (μ.rg A Λ₁).2.rg (μ.rg A Λ₁).1 Λ₂ = μ.rg A Λ₂ := by
  simp only [rg]
  refine Prod.ext ?_ (μ.cutoff_cutoff h)
  show A - μ.headCorrection Λ₁ - (μ.cutoff Λ₁).headCorrection Λ₂ = A - μ.headCorrection Λ₂
  rw [← μ.headCorrection_add_headCorrection_cutoff h2 h]
  abel

/-- **`thm:supp-memory-RG` (Exact memory RG semigroup)** for general positive operator-valued
tail measures (`def:supp-POVM`): the static value is preserved whenever it exists (`λ⁻¹`
`μ`-integrable), the screening error for `‖z‖ ≤ r < Λ`, `z ∉ [0,∞)` is at most
`r/(Λ - r) ‖Q_{>Λ}‖` in operator norm, and `RG_{Λ₂} ∘ RG_{Λ₁} = RG_{Λ₂}` for `0 < Λ₂ ≤ Λ₁`. -/
theorem memory_rg_semigroup (A : Matrix H H ℂ) :
    (Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹) μ.toVectorMeasure.variation →
      ∀ Λ : ℝ, (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 0 = μ.dynamicFunction A 0) ∧
    (∀ (Λ r : ℝ), r < Λ → ∀ z : ℂ, ‖z‖ ≤ r → ¬ (z.im = 0 ∧ 0 ≤ z.re) →
      ‖μ.dynamicFunction A z - (μ.rg A Λ).2.dynamicFunction (μ.rg A Λ).1 z‖ ≤
        r / (Λ - r) * ‖μ.headCorrection Λ‖) ∧
    (∀ Λ₁ Λ₂ : ℝ, 0 < Λ₂ → Λ₂ ≤ Λ₁ → (μ.rg A Λ₁).2.rg (μ.rg A Λ₁).1 Λ₂ = μ.rg A Λ₂) :=
  ⟨fun hint Λ => μ.dynamicFunction_rg_zero A Λ hint,
    fun _ _ hr _ hz hzdom => μ.norm_dynamicFunction_sub_rg_le A hr hz hzdom,
    fun _ _ h2 h => μ.rg_rg A h2 h⟩

end PositiveTailMeasure

end OperatorTailMeasure
end RenewalGeometry
