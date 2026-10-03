/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.OperatorTailMeasureDeterminacyExact
/-!
# Moment determinacy among all positive tail measures

This file completes `thm:supp-memory-determinacy` of `papers/predictive_spectral_geometry`.
`OperatorTailMeasureDeterminacyExact` proves that two positive operator-valued tail measures
`μ, μ'` with equal moment sequences coincide when *both* are supported in `(0, R]`, or when
*both* have an exponential trace moment.  The paper's statement puts the hypothesis on `μ`
only ("the complete moment sequence determines `μ` uniquely"): determinacy holds among all
positive tail measures.  Here the hypothesis on `μ'` is derived from moment equality.

* `integrable_pow_variation_of_moment_eq`: if all powers are `μ`-integrable and
  `M_n(μ) = M_n(μ')` for all `n`, then all powers are `μ'`-integrable (the Bochner convention
  `∫ f = 0` for non-integrable `f` is excluded because `Tr M_n(μ) = ∫ λⁿ d Tr μ` vanishes only
  for `μ = 0`, and then `Tr M_0(μ') = Tr μ'(ℝ) = 0`);
* `re_trace_moment`: `Re Tr M_n(μ) = ∫ λⁿ d Tr μ(λ)`;
* `isSupportedIn_of_moment_eq` (compact clause): Chebyshev,
  `Tr μ'([T,∞)) ≤ T^{-2n} ∫ λ^{2n} d Tr μ' = T^{-2n} ∫ λ^{2n} d Tr μ ≤ (R/T)^{2n} Tr μ(ℝ) → 0`;
* `integrable_exp_traceMeasure_of_moment_eq` (exponential clause): Tonelli,
  `∫⁻ e^{aλ} d Tr μ' = Σ_n aⁿ/n! ∫ λⁿ d Tr μ' = Σ_n aⁿ/n! ∫ λⁿ d Tr μ = ∫⁻ e^{aλ} d Tr μ < ∞`;
* `memory_determinacy_of_moment_eq`: the theorem with hypotheses on `μ` only.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Nat ComplexOrder

namespace RenewalGeometry
namespace OperatorTailMeasure
namespace PositiveTailMeasure

variable {H : Type*} [Fintype H] [DecidableEq H]

section Domination

variable (μ : PositiveTailMeasure H)

/-- Each scalarised measure is dominated by a multiple of the variation of `μ`. -/
theorem formMeasure_le_smul_variation_transfer (ξ : H → ℂ) :
    μ.formMeasure ξ ≤ (‖quadFormCLM ξ‖₊ : ℝ≥0∞) • μ.toVectorMeasure.variation := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [formMeasure_apply μ ξ hs, Measure.smul_apply, smul_eq_mul]
  calc ENNReal.ofReal (quadFormCLM ξ (μ.toVectorMeasure s))
      ≤ ‖quadFormCLM ξ (μ.toVectorMeasure s)‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ‖quadFormCLM ξ‖ₑ * ‖μ.toVectorMeasure s‖ₑ := ContinuousLinearMap.le_opENorm _ _
    _ ≤ (‖quadFormCLM ξ‖₊ : ℝ≥0∞) * μ.toVectorMeasure.variation s := by
        rw [enorm_eq_nnnorm]
        gcongr
        exact VectorMeasure.enorm_measure_le_variation _ _

/-- Integrability against the variation transfers to every scalarised measure. -/
theorem integrable_formMeasure_of_integrable_variation {f : ℝ → ℝ}
    (hf : Integrable f μ.toVectorMeasure.variation) (ξ : H → ℂ) :
    Integrable f (μ.formMeasure ξ) :=
  hf.of_measure_le_smul ENNReal.coe_ne_top (μ.formMeasure_le_smul_variation_transfer ξ)

/-- Integrability against the variation transfers to the trace measure. -/
theorem integrable_traceMeasure_of_integrable_variation {f : ℝ → ℝ}
    (hf : Integrable f μ.toVectorMeasure.variation) : Integrable f μ.traceMeasure := by
  rw [traceMeasure, integrable_finsetSum_measure]
  exact fun i _ => μ.integrable_formMeasure_of_integrable_variation hf _

/-- **Trace moments.**  `Re Tr M_n(μ) = ∫ λⁿ d Tr μ(λ)` whenever `λⁿ` is `μ`-integrable. -/
theorem re_trace_moment (n : ℕ)
    (hf : Integrable (fun x : ℝ => x ^ n) μ.toVectorMeasure.variation) :
    (μ.moment n).trace.re = ∫ x, x ^ n ∂μ.traceMeasure := by
  rw [traceMeasure, integral_finsetSum_measure
    (fun i _ => μ.integrable_formMeasure_of_integrable_variation hf _)]
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← μ.quadFormCLM_moment_of_integrable _ n hf]
  exact (quadFormCLM_single i (μ.moment n)).symm

/-- The zeroth power is always integrable (the variation is finite). -/
theorem integrable_pow_zero_variation :
    Integrable (fun x : ℝ => x ^ 0) μ.toVectorMeasure.variation := by
  simp only [pow_zero]
  exact integrable_const _

/-- `Re Tr M_0(μ) = Tr μ(ℝ)`. -/
theorem re_trace_moment_zero : (μ.moment 0).trace.re = μ.traceMeasure.real univ := by
  rw [μ.re_trace_moment 0 μ.integrable_pow_zero_variation]
  simp

/-- The trace measure is concentrated on `[0, ∞)`. -/
theorem ae_traceMeasure_nonneg : ∀ᵐ x ∂μ.traceMeasure, 0 ≤ x := by
  rw [ae_iff]
  exact measure_mono_null (fun x hx => not_le.mp hx) μ.traceMeasure_Iio

/-- The trace measure vanishes on `(-∞, 0]`. -/
theorem traceMeasure_Iic : μ.traceMeasure (Iic 0) = 0 := by
  rw [traceMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i _ => μ.formMeasure_Iic _

/-- If the trace measure vanishes, every function is integrable against the variation. -/
theorem integrable_variation_of_traceMeasure_eq_zero (h : μ.traceMeasure = 0) (f : ℝ → ℝ) :
    Integrable f μ.toVectorMeasure.variation := by
  have : μ.toVectorMeasure.variation = 0 := le_antisymm (h ▸ μ.variation_le_traceMeasure) bot_le
  rw [this]
  exact integrable_zero_measure

end Domination

variable (μ μ' : PositiveTailMeasure H)

/-- **Moment equality transfers integrability of the powers.**  If every power `λⁿ` is
`μ`-integrable and `M_n(μ) = M_n(μ')` for all `n`, then every power is `μ'`-integrable.  (A
non-integrable power would have Bochner value `M_n(μ') = 0`, forcing `∫ λⁿ d Tr μ = 0`, hence
`μ = 0`, hence `Tr μ'(ℝ) = Re Tr M_0(μ') = 0` and `μ'` is zero as well.) -/
theorem integrable_pow_variation_of_moment_eq
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ.toVectorMeasure.variation)
    (h : ∀ n : ℕ, μ.moment n = μ'.moment n) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) μ'.toVectorMeasure.variation := by
  by_contra hn
  have hmom : μ'.moment n = 0 := by
    have hni : ¬ μ'.toVectorMeasure.Integrable (fun lam : ℝ => ((lam ^ n : ℝ) : ℂ)) := by
      intro hc
      apply hn
      refine hc.re.congr (Eventually.of_forall fun x => ?_)
      exact Complex.ofReal_re _
    unfold moment
    rw [VectorMeasure.integral_undef hni]
    rfl
  -- the trace moment of `μ` vanishes
  have hint : ∫ x, x ^ n ∂μ.traceMeasure = 0 := by
    rw [← μ.re_trace_moment n (hμ n), h n, hmom]
    simp
  have hae : (fun x : ℝ => x ^ n) =ᵐ[μ.traceMeasure] 0 := by
    have hnn : 0 ≤ᵐ[μ.traceMeasure] fun x : ℝ => x ^ n := by
      filter_upwards [μ.ae_traceMeasure_nonneg] with x hx using pow_nonneg hx n
    exact (integral_eq_zero_iff_of_nonneg_ae hnn
      (μ.integrable_traceMeasure_of_integrable_variation (hμ n))).1 hint
  -- hence `Tr μ = 0`
  have htr : μ.traceMeasure = 0 := by
    rw [← Measure.measure_univ_eq_zero]
    refine measure_mono_null (t := {x | ¬ (x ^ n = (0 : ℝ → ℝ) x)} ∪ Iic 0) (fun x _ => ?_)
      (measure_union_null (ae_iff.1 hae) μ.traceMeasure_Iic)
    by_cases hx : x ^ n = 0
    · right
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0; simp at hx
      · exact le_of_eq ((pow_eq_zero_iff hn0.ne').1 hx)
    · left
      simpa using hx
  -- and `Tr μ' = 0`
  have htr' : μ'.traceMeasure = 0 := by
    have h0 := μ'.re_trace_moment_zero
    rw [← h 0, μ.re_trace_moment_zero, htr] at h0
    rw [← Measure.measure_univ_eq_zero]
    have : μ'.traceMeasure.real univ = 0 := by simpa using h0.symm
    exact (measureReal_eq_zero_iff).1 this
  exact hn (μ'.integrable_variation_of_traceMeasure_eq_zero htr' _)

/-- Equal moments give equal trace moments, once all powers are `μ`-integrable. -/
theorem integral_pow_traceMeasure_eq_of_moment_eq
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ.toVectorMeasure.variation)
    (h : ∀ n : ℕ, μ.moment n = μ'.moment n) (n : ℕ) :
    ∫ x, x ^ n ∂μ'.traceMeasure = ∫ x, x ^ n ∂μ.traceMeasure := by
  rw [← μ.re_trace_moment n (hμ n),
    ← μ'.re_trace_moment n (integrable_pow_variation_of_moment_eq μ μ' hμ h n), h n]

/-- A measure supported in `(0, R]` integrates every power. -/
theorem integrable_pow_variation_of_isSupportedIn {R : ℝ} (hR : μ.IsSupportedIn R) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) μ.toVectorMeasure.variation :=
  μ.integrable_variation_of_continuous hR (continuous_pow n)

/-- A vector measure whose trace measure vanishes on `(R, ∞)` is supported in `(0, R]`. -/
theorem isSupportedIn_of_traceMeasure_Ioi {R : ℝ} (h : μ.traceMeasure (Ioi R) = 0) :
    μ.IsSupportedIn R := by
  intro s hs hsub
  have hv : μ.toVectorMeasure.variation s = 0 :=
    le_antisymm ((μ.variation_le_traceMeasure s).trans
      ((measure_mono hsub).trans h.le)) bot_le
  have : ‖μ.toVectorMeasure s‖ₑ = 0 :=
    le_antisymm ((VectorMeasure.enorm_measure_le_variation _ _).trans hv.le) bot_le
  exact enorm_eq_zero.mp this

/-- **`thm:supp-memory-determinacy`, compact clause, support transfer.**  If `μ` is supported
in `(0, R]` and `μ'` has the same moment sequence, then `μ'` is supported in `(0, R]`
(Chebyshev on the trace measures). -/
theorem isSupportedIn_of_moment_eq {R : ℝ} (hR : μ.IsSupportedIn R)
    (h : ∀ n : ℕ, μ.moment n = μ'.moment n) : μ'.IsSupportedIn R := by
  have hμ := μ.integrable_pow_variation_of_isSupportedIn hR
  have hμ' := integrable_pow_variation_of_moment_eq μ μ' hμ h
  set r : ℝ := max R 0 with hr
  -- `Tr μ` lives in `[0, r]`
  have hsuppμ : ∀ᵐ x ∂μ.traceMeasure, 0 ≤ x ∧ x ≤ r := by
    have hIoi : μ.traceMeasure (Ioi R) = 0 := by
      rw [traceMeasure, Measure.coe_finsetSum, Finset.sum_apply]
      exact Finset.sum_eq_zero fun i _ => μ.formMeasure_Ioi hR _
    filter_upwards [μ.ae_traceMeasure_nonneg, measure_eq_zero_iff_ae_notMem.1 hIoi]
      with x hx0 hxR
    exact ⟨hx0, le_max_of_le_left (not_lt.mp hxR)⟩
  -- Chebyshev for every threshold `T > r`
  have hT : ∀ T : ℝ, r < T → μ'.traceMeasure {x | T ≤ x} = 0 := by
    intro T hrT
    have hT0 : 0 < T := lt_of_le_of_lt (le_max_right R 0) hrT
    set q : ℝ := (r / T) ^ 2 with hq
    have hq0 : 0 ≤ q := sq_nonneg _
    have hq1 : q < 1 := by
      have h0 : 0 ≤ r / T := div_nonneg (le_max_right R 0) hT0.le
      have h1 : r / T < 1 := (div_lt_one hT0).2 hrT
      rw [hq]
      nlinarith
    have hbound : ∀ n : ℕ, μ'.traceMeasure.real {x | T ≤ x} ≤ q ^ n * μ.traceMeasure.real univ := by
      intro n
      have hnn : 0 ≤ᵐ[μ'.traceMeasure] fun x : ℝ => x ^ (2 * n) :=
        Eventually.of_forall fun x => (even_two_mul n).pow_nonneg x
      have hcheb := mul_meas_ge_le_integral_of_nonneg hnn
        (μ'.integrable_traceMeasure_of_integrable_variation (hμ' (2 * n))) (T ^ (2 * n))
      rw [integral_pow_traceMeasure_eq_of_moment_eq μ μ' hμ h] at hcheb
      have hupper : ∫ x, x ^ (2 * n) ∂μ.traceMeasure ≤ r ^ (2 * n) * μ.traceMeasure.real univ := by
        have : ∫ x, x ^ (2 * n) ∂μ.traceMeasure ≤ ∫ _x, r ^ (2 * n) ∂μ.traceMeasure :=
          integral_mono_ae (μ.integrable_traceMeasure_of_integrable_variation (hμ (2 * n)))
            (integrable_const _) (by
              filter_upwards [hsuppμ] with x hx
              exact pow_le_pow_left₀ hx.1 hx.2 _)
        simpa [mul_comm] using this
      have hsub : μ'.traceMeasure.real {x | T ≤ x} ≤
          μ'.traceMeasure.real {x | T ^ (2 * n) ≤ x ^ (2 * n)} :=
        measureReal_mono (fun x (hx : T ≤ x) => pow_le_pow_left₀ hT0.le hx _)
      have hTpos : 0 < T ^ (2 * n) := pow_pos hT0 _
      have key : T ^ (2 * n) * μ'.traceMeasure.real {x | T ≤ x} ≤
          r ^ (2 * n) * μ.traceMeasure.real univ :=
        ((mul_le_mul_of_nonneg_left hsub hTpos.le).trans hcheb).trans hupper
      have hqn : q ^ n = r ^ (2 * n) / T ^ (2 * n) := by
        rw [hq, ← pow_mul, div_pow, mul_comm 2 n]
      rw [hqn, div_mul_eq_mul_div, le_div_iff₀ hTpos, mul_comm]
      exact key
    have hlim : Tendsto (fun n : ℕ => q ^ n * μ.traceMeasure.real univ) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
        (μ.traceMeasure.real univ)
    have hle : μ'.traceMeasure.real {x | T ≤ x} ≤ 0 :=
      ge_of_tendsto' hlim hbound
    have hzero : μ'.traceMeasure.real {x | T ≤ x} = 0 := le_antisymm hle measureReal_nonneg
    exact (measureReal_eq_zero_iff).1 hzero
  -- `Tr μ'` vanishes on `(r, ∞)`, hence on `(R, ∞)`
  have hIoi_r : μ'.traceMeasure (Ioi r) = 0 := by
    have hU : Ioi r = ⋃ k : ℕ, {x | r + 1 / ((k : ℝ) + 1) ≤ x} := by
      ext x
      simp only [mem_Ioi, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    rw [hU]
    exact measure_iUnion_null fun k => hT _ (by
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith)
  refine μ'.isSupportedIn_of_traceMeasure_Ioi (measure_mono_null (t := Ioi r ∪ Iic 0)
    (fun x (hx : R < x) => ?_) (measure_union_null hIoi_r μ'.traceMeasure_Iic))
  by_cases hx0 : 0 < x
  · exact Or.inl (max_lt hx hx0)
  · exact Or.inr (not_lt.mp hx0)

/-- **`thm:supp-memory-determinacy`, compact clause (hypothesis on `μ` only).**  If `μ` is
supported in `(0, R]`, any positive tail measure `μ'` with the same moment sequence equals
`μ`. -/
theorem eq_of_isSupportedIn_of_moment_eq' {R : ℝ} (hR : μ.IsSupportedIn R)
    (h : ∀ n : ℕ, μ.moment n = μ'.moment n) : μ = μ' :=
  μ.eq_of_isSupportedIn_of_moment_eq μ' hR (isSupportedIn_of_moment_eq μ μ' hR h) h

/-- **Tonelli expansion of the exponential moment.**  For a finite measure on `[0, ∞)` whose
powers are all integrable, `∫⁻ e^{aλ} dν = Σ_n aⁿ/n! · ∫ λⁿ dν` (`a ≥ 0`). -/
theorem lintegral_exp_eq_tsum {ν : Measure ℝ} (hν0 : ∀ᵐ x ∂ν, 0 ≤ x)
    (hpow : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) ν) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (a * x)) ∂ν =
      ∑' n : ℕ, ENNReal.ofReal (a ^ n / n !) * ENNReal.ofReal (∫ x, x ^ n ∂ν) := by
  have hexp : ∀ y : ℝ, Real.exp y = ∑' n : ℕ, y ^ n / n ! := by
    intro y
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (a * x)) ∂ν
      = ∫⁻ x, ∑' n : ℕ, ENNReal.ofReal (a ^ n / n !) * ENNReal.ofReal (x ^ n) ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [hν0] with x hx
        rw [hexp, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          (Real.summable_pow_div_factorial _)]
        refine tsum_congr fun n => ?_
        rw [← ENNReal.ofReal_mul (by positivity), mul_pow]
        congr 1
        ring
    _ = ∑' n : ℕ, ∫⁻ x, ENNReal.ofReal (a ^ n / n !) * ENNReal.ofReal (x ^ n) ∂ν :=
        lintegral_tsum fun n => by fun_prop
    _ = ∑' n : ℕ, ENNReal.ofReal (a ^ n / n !) * ENNReal.ofReal (∫ x, x ^ n ∂ν) := by
        refine tsum_congr fun n => ?_
        rw [lintegral_const_mul _ (by fun_prop), ofReal_integral_eq_lintegral_ofReal (hpow n)]
        filter_upwards [hν0] with x hx using pow_nonneg hx n

/-- **`thm:supp-memory-determinacy`, exponential clause, transfer.**  If
`∫ e^{aλ} d Tr μ < ∞` (`a > 0`) and `μ'` has the same moment sequence, then
`∫ e^{aλ} d Tr μ' < ∞`. -/
theorem integrable_exp_traceMeasure_of_moment_eq {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * x)) μ.traceMeasure)
    (h : ∀ n : ℕ, μ.moment n = μ'.moment n) :
    Integrable (fun x => Real.exp (a * x)) μ'.traceMeasure := by
  have hμtr : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ.traceMeasure := fun n =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
      (Iio_subset_interior_integrableExpSet μ.traceMeasure_Iio hexp ha) n
  have hμ : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ.toVectorMeasure.variation := fun n =>
    (hμtr n).mono_measure μ.variation_le_traceMeasure
  have hμ'tr : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ'.traceMeasure := fun n =>
    μ'.integrable_traceMeasure_of_integrable_variation
      (integrable_pow_variation_of_moment_eq μ μ' hμ h n)
  have hL : ∫⁻ x, ENNReal.ofReal (Real.exp (a * x)) ∂μ'.traceMeasure =
      ∫⁻ x, ENNReal.ofReal (Real.exp (a * x)) ∂μ.traceMeasure := by
    rw [lintegral_exp_eq_tsum μ'.ae_traceMeasure_nonneg hμ'tr ha.le,
      lintegral_exp_eq_tsum μ.ae_traceMeasure_nonneg hμtr ha.le]
    simp_rw [integral_pow_traceMeasure_eq_of_moment_eq μ μ' hμ h]
  have hfin : ∫⁻ x, ENNReal.ofReal (Real.exp (a * x)) ∂μ.traceMeasure < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le)).1
      hexp.hasFiniteIntegral
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le), hL]
  exact hfin

/-- **`thm:supp-memory-determinacy`, exponential clause (hypothesis on `μ` only).**  If
`∫ e^{aλ} d Tr μ(λ) < ∞` for some `a > 0`, any positive tail measure with the same moment
sequence equals `μ`. -/
theorem eq_of_integrable_exp_traceMeasure_of_moment_eq' {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * x)) μ.traceMeasure)
    (h : ∀ n : ℕ, μ.moment n = μ'.moment n) : μ = μ' :=
  μ.eq_of_integrable_exp_traceMeasure_of_moment_eq μ' ha hexp
    (integrable_exp_traceMeasure_of_moment_eq μ μ' ha hexp h) h

/-- **`thm:supp-memory-determinacy` (Determinacy on controlled support), hypotheses on `μ`
only.**  If `supp μ` is compact (`μ` supported in `(0, R]`), the complete moment sequence
`M_n = ∫ λⁿ dμ(λ)` determines `μ` uniquely among all positive operator-valued tail measures;
the same holds on unbounded support if `∫ e^{aλ} d Tr μ(λ) < ∞` for some `a > 0`. -/
theorem memory_determinacy_of_moment_eq :
    (∀ (R : ℝ) (μ μ' : PositiveTailMeasure H), μ.IsSupportedIn R →
      (∀ n : ℕ, μ.moment n = μ'.moment n) → μ = μ') ∧
    (∀ (a : ℝ), 0 < a → ∀ (μ μ' : PositiveTailMeasure H),
      Integrable (fun x => Real.exp (a * x)) μ.traceMeasure →
      (∀ n : ℕ, μ.moment n = μ'.moment n) → μ = μ') :=
  ⟨fun _ μ μ' hR h => eq_of_isSupportedIn_of_moment_eq' μ μ' hR h,
    fun _ ha μ μ' hexp h => eq_of_integrable_exp_traceMeasure_of_moment_eq' μ μ' ha hexp h⟩

/-- Non-vacuity: the atom `λ Q δ_λ` is supported in `(0, λ]`, so the compact clause applies to
it (e.g. with `Q = 1` on `ℂ²`). -/
theorem atomic_isSupportedIn (lam : ℝ) (hlam : 0 < lam) (Q : Matrix H H ℂ) (hQ : Q.PosSemidef) :
    (atomic lam hlam Q hQ).IsSupportedIn lam :=
  fun _ _ hsub => VectorMeasure.dirac_apply_of_notMem fun h => lt_irrefl lam (hsub h)

example : ∀ μ' : PositiveTailMeasure (Fin 2),
    (∀ n : ℕ, (atomic 1 one_pos 1 Matrix.PosSemidef.one).moment n = μ'.moment n) →
      atomic 1 one_pos 1 Matrix.PosSemidef.one = μ' := fun μ' h =>
  eq_of_isSupportedIn_of_moment_eq' _ μ' (atomic_isSupportedIn 1 one_pos 1 _) h

end PositiveTailMeasure
end OperatorTailMeasure
end RenewalGeometry
