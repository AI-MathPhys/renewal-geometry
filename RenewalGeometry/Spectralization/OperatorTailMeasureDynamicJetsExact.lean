/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.OperatorTailMeasureIntegralCalculus
import RenewalGeometry.Analysis.VectorMeasureParametricIntegral
import RenewalGeometry.Analysis.StieltjesLaplaceScalar
/-!
# Static shadows, inverse moments, and positive Euclidean memory

This file proves `thm:supp-dynamic-jets` of `papers/predictive_spectral_geometry` for the
positive operator-valued tail measures of `def:supp-POVM` (`PositiveTailMeasure`):

* `eq:supp-Herglotz-sign`: `Im Σ_μ(z) = (Im z) ∫ |λ - z|⁻² dμ ⪰ 0` for `Im z > 0`
  (`matrixIm_stieltjesSelfEnergy`, `posSemidef_matrixIm_stieltjesSelfEnergy`, file
  `OperatorTailMeasureIntegralCalculus`);
* `eq:supp-static-inverse-moment`: the static shadow `lim_{s↓0} Σ_μ(-s)` exists **iff** the
  inverse first moment `∫ λ⁻¹ dTr μ` is finite, and then it equals `∫ λ⁻¹ dμ`
  (`tendsto_stieltjesSelfEnergy_neg_iff`, `tendsto_stieltjesSelfEnergy_neg_of_integrable`);
* `eq:supp-dynamic-jet`: if `∫ λ^{-(r+1)} dTr μ < ∞`, the `r`-th one-sided derivative of
  `x ↦ Σ_μ(x)` at `0` within `(-∞, 0]` is `r! ∫ λ^{-(r+1)} dμ`
  (`iteratedDerivWithin_stieltjesSelfEnergy_zero`; derivatives of the matrix-valued function are
  taken entrywise, i.e. in the normed space `H → H → ℂ` via `Matrix.of.symm`);
* `eq:supp-Euclidean-memory`: `K_μ(t) = ∫ e^{-tλ} dμ ⪰ 0` for `t ≥ 0`
  (`posSemidef_euclideanMemoryKernel`) and the Laplace relation
  `Σ_μ(-s) = ∫_0^∞ e^{-st} K_μ(t) dt` for `s > 0`
  (`stieltjesSelfEnergy_neg_eq_integral_euclideanMemoryKernel`), by Tonelli on the scalarisations
  `⟨ξ, μ(·) ξ⟩` and polarisation.

The dilation form `K_μ(t) = B_μ e^{-tC_μ} B_μ^*` of `eq:supp-Euclidean-memory` belongs to the
canonical realization of `thm:supp-Naimark-realization` and is not part of this file.
-/

open MeasureTheory Filter Topology Set
open scoped ComplexOrder ENNReal Matrix

namespace RenewalGeometry
namespace OperatorTailMeasure

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- `(λ^m)⁻¹ ≤ 1 + (λ^n)⁻¹` for `λ > 0` and `m ≤ n`. -/
theorem inv_pow_le_one_add_inv_pow {lam : ℝ} (h : 0 < lam) {m n : ℕ} (hmn : m ≤ n) :
    (lam ^ m)⁻¹ ≤ 1 + (lam ^ n)⁻¹ := by
  rcases le_or_gt 1 lam with h1 | h1
  · have : (lam ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    linarith [inv_nonneg.mpr (pow_nonneg h.le n)]
  · have : (lam ^ m)⁻¹ ≤ (lam ^ n)⁻¹ :=
      inv_anti₀ (pow_pos h n) (pow_le_pow_of_le_one h.le h1.le hmn)
    linarith

namespace PositiveTailMeasure

variable (μ : PositiveTailMeasure H)

/-! ## Inverse moments -/

/-- The inverse moment `∫ λ^{-n} dμ(λ)`. -/
noncomputable def inverseMoment (n : ℕ) : Matrix H H ℂ :=
  Matrix.of (VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => (((lam ^ n)⁻¹ : ℝ) : ℂ))
    (ContinuousLinearMap.lsmul ℝ ℂ))

theorem integrable_inv_pow_traceMeasure {n : ℕ}
    (hn : Integrable (fun lam : ℝ => (lam ^ n)⁻¹) μ.traceMeasure) {m : ℕ} (hmn : m ≤ n) :
    Integrable (fun lam : ℝ => (lam ^ m)⁻¹) μ.traceMeasure := by
  refine Integrable.mono' ((integrable_const 1).add hn)
    (by fun_prop : Measurable fun lam : ℝ => (lam ^ m)⁻¹).aestronglyMeasurable ?_
  filter_upwards [μ.ae_pos_traceMeasure] with lam hlam
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hlam.le m))]
  exact inv_pow_le_one_add_inv_pow hlam hmn

theorem integrable_inv_pow_variation {n : ℕ}
    (hn : Integrable (fun lam : ℝ => (lam ^ n)⁻¹) μ.traceMeasure) {m : ℕ} (hmn : m ≤ n) :
    Integrable (fun lam : ℝ => (lam ^ m)⁻¹) μ.toVectorMeasure.variation :=
  μ.integrable_variation_of_traceMeasure (μ.integrable_inv_pow_traceMeasure hn hmn)

/-- The real trace of a real operator integral is the integral against the trace measure. -/
theorem re_trace_integral_ofReal {f : ℝ → ℝ} (hf : Integrable f μ.toVectorMeasure.variation) :
    (Matrix.of (VectorMeasure.integral μ.toVectorMeasure (fun x => (f x : ℂ))
      (ContinuousLinearMap.lsmul ℝ ℂ))).trace.re = ∫ x, f x ∂μ.traceMeasure := by
  have hi : ∀ i : H, Integrable f (μ.formMeasure (Pi.single i 1)) := fun i =>
    hf.of_measure_le_smul ENNReal.coe_ne_top (μ.formMeasure_le_smul_variation _)
  rw [traceMeasure, integral_finset_sum_measure fun i _ => hi i, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.of_apply]
  have := μ.quadFormCLM_integral (Pi.single i 1) hf
  rw [quadFormCLM_single, ← μ.integral_ofReal_lsmul hf] at this
  exact this

/-! ## The static shadow `eq:supp-static-inverse-moment` -/

theorem stieltjesSelfEnergy_neg_real (s : ℝ) :
    μ.stieltjesSelfEnergy (-(s : ℂ)) = Matrix.of (VectorMeasure.integral μ.toVectorMeasure
      (fun lam : ℝ => (((lam + s)⁻¹ : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
  unfold stieltjesSelfEnergy
  congr 2
  funext lam
  push_cast
  rw [sub_neg_eq_add]

theorem integrable_inv_add_variation {s : ℝ} (hs : 0 < s) :
    Integrable (fun lam : ℝ => (lam + s)⁻¹) μ.toVectorMeasure.variation := by
  refine Integrable.mono' (integrable_const s⁻¹)
    (by fun_prop : Measurable fun lam : ℝ => (lam + s)⁻¹).aestronglyMeasurable ?_
  filter_upwards [μ.ae_pos_variation] with lam hlam
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
  exact inv_anti₀ hs (by linarith)

/-- **`eq:supp-static-inverse-moment`, existence.**  If the inverse first moment is finite the
static shadow exists and equals `∫ λ⁻¹ dμ`. -/
theorem tendsto_stieltjesSelfEnergy_neg_of_integrable
    (h : Integrable (fun lam : ℝ => lam⁻¹) μ.traceMeasure) :
    Tendsto (fun s : ℝ => μ.stieltjesSelfEnergy (-(s : ℂ))) (𝓝[>] 0) (𝓝 (μ.inverseMoment 1)) := by
  simp_rw [stieltjesSelfEnergy_neg_real]
  have h' : Integrable (fun lam : ℝ => lam⁻¹) μ.toVectorMeasure.variation :=
    μ.integrable_variation_of_traceMeasure h
  have key : Tendsto (fun s : ℝ => VectorMeasure.integral μ.toVectorMeasure
      (fun lam : ℝ => (((lam + s)⁻¹ : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)) (𝓝[>] 0)
      (𝓝 (VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => (((lam ^ 1)⁻¹ : ℝ) : ℂ))
        (ContinuousLinearMap.lsmul ℝ ℂ))) := by
    refine VectorMeasure.tendsto_integral_filter_of_dominated_convergence (fun lam => lam⁻¹)
      ?_ ?_ h' ?_
    · exact Eventually.of_forall fun s =>
        (by fun_prop : Measurable fun lam : ℝ => (((lam + s)⁻¹ : ℝ) : ℂ)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s hs
      filter_upwards [μ.ae_pos_variation] with lam hlam
      have hs' : 0 < s := hs
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
      exact inv_anti₀ hlam (by linarith)
    · filter_upwards [μ.ae_pos_variation] with lam hlam
      have hc : ContinuousAt (fun s : ℝ => (((lam + s)⁻¹ : ℝ) : ℂ)) 0 := by
        refine Complex.continuous_ofReal.continuousAt.comp ?_
        exact (continuous_const.add continuous_id).continuousAt.inv₀ (by simpa using hlam.ne')
      have := hc.tendsto
      simp only [add_zero, pow_one] at this ⊢
      exact this.mono_left nhdsWithin_le_nhds
  exact key

/-- **`eq:supp-static-inverse-moment`, necessity.**  If the static shadow `lim_{s↓0} Σ_μ(-s)`
exists, the inverse first moment `∫ λ⁻¹ dTr μ` is finite. -/
theorem integrable_inv_of_tendsto_stieltjesSelfEnergy_neg {L : Matrix H H ℂ}
    (h : Tendsto (fun s : ℝ => μ.stieltjesSelfEnergy (-(s : ℂ))) (𝓝[>] 0) (𝓝 L)) :
    Integrable (fun lam : ℝ => lam⁻¹) μ.traceMeasure := by
  -- the real trace `g(s) = ∫ (λ + s)⁻¹ dTr μ` converges
  have hcont : Continuous fun M : Matrix H H ℂ => M.trace.re :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  have hg : Tendsto (fun s : ℝ => ∫ lam, (lam + s)⁻¹ ∂μ.traceMeasure) (𝓝[>] 0)
      (𝓝 L.trace.re) := by
    refine ((hcont.tendsto L).comp h).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply]
    rw [stieltjesSelfEnergy_neg_real, μ.re_trace_integral_ofReal (μ.integrable_inv_add_variation hs)]
  -- along the sequence `s_n = 1/(n+1)`
  set sq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsq
  have hsq_pos : ∀ n, 0 < sq n := fun n => by
    simp only [hsq]
    positivity
  have hsq_anti : ∀ m n, m ≤ n → sq n ≤ sq m := fun m n hmn => by
    simp only [hsq]
    gcongr
  have hsq_tend : Tendsto sq atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => hsq_pos n⟩
  have hgn : Tendsto (fun n => ∫ lam, (lam + sq n)⁻¹ ∂μ.traceMeasure) atTop (𝓝 L.trace.re) :=
    hg.comp hsq_tend
  have hint_n : ∀ n, Integrable (fun lam => (lam + sq n)⁻¹) μ.traceMeasure := fun n => by
    refine Integrable.mono' (integrable_const (sq n)⁻¹)
      (by fun_prop : Measurable fun lam : ℝ => (lam + sq n)⁻¹).aestronglyMeasurable ?_
    filter_upwards [μ.ae_pos_traceMeasure] with lam hlam
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith [hsq_pos n]))]
    exact inv_anti₀ (hsq_pos n) (by linarith)
  -- monotone convergence of the Lebesgue integrals
  have hmono : ∀ᵐ lam ∂μ.traceMeasure, Monotone fun n => ENNReal.ofReal ((lam + sq n)⁻¹) := by
    filter_upwards [μ.ae_pos_traceMeasure] with lam hlam
    intro m n hmn
    refine ENNReal.ofReal_le_ofReal (inv_anti₀ (by linarith [hsq_pos n]) ?_)
    linarith [hsq_anti m n hmn]
  have hlim : ∀ᵐ lam ∂μ.traceMeasure, Tendsto (fun n => ENNReal.ofReal ((lam + sq n)⁻¹)) atTop
      (𝓝 (ENNReal.ofReal lam⁻¹)) := by
    filter_upwards [μ.ae_pos_traceMeasure] with lam hlam
    have hc : ContinuousAt (fun s : ℝ => (lam + s)⁻¹) 0 :=
      (continuous_const.add continuous_id).continuousAt.inv₀ (by simpa using hlam.ne')
    have hreal : Tendsto (fun n => (lam + sq n)⁻¹) atTop (𝓝 lam⁻¹) := by
      have := hc.tendsto.comp (hsq_tend.mono_right nhdsWithin_le_nhds)
      simpa [Function.comp_def] using this
    exact (ENNReal.continuous_ofReal.tendsto _).comp hreal
  have hmct := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (by fun_prop : Measurable fun lam : ℝ => ENNReal.ofReal ((lam + sq n)⁻¹)).aemeasurable)
    hmono hlim
  have heq : ∀ n, ∫⁻ lam, ENNReal.ofReal ((lam + sq n)⁻¹) ∂μ.traceMeasure =
      ENNReal.ofReal (∫ lam, (lam + sq n)⁻¹ ∂μ.traceMeasure) := fun n => by
    rw [ofReal_integral_eq_lintegral_ofReal (hint_n n)]
    filter_upwards [μ.ae_pos_traceMeasure] with lam hlam
    exact inv_nonneg.mpr (by linarith [hsq_pos n])
  simp_rw [heq] at hmct
  have hlim2 : Tendsto (fun n => ENNReal.ofReal (∫ lam, (lam + sq n)⁻¹ ∂μ.traceMeasure)) atTop
      (𝓝 (ENNReal.ofReal L.trace.re)) := (ENNReal.continuous_ofReal.tendsto _).comp hgn
  have hfin : ∫⁻ lam, ENNReal.ofReal lam⁻¹ ∂μ.traceMeasure = ENNReal.ofReal L.trace.re :=
    tendsto_nhds_unique hmct hlim2
  refine ⟨(by fun_prop : Measurable fun lam : ℝ => lam⁻¹).aestronglyMeasurable, ?_⟩
  change ∫⁻ lam, ‖lam⁻¹‖ₑ ∂μ.traceMeasure < ∞
  rw [lintegral_congr_ae (g := fun lam => ENNReal.ofReal lam⁻¹) ?_, hfin]
  · exact ENNReal.ofReal_lt_top
  · filter_upwards [μ.ae_pos_traceMeasure] with lam hlam
    exact Real.enorm_eq_ofReal (inv_nonneg.mpr hlam.le)

/-- **`eq:supp-static-inverse-moment`.**  The static shadow `lim_{s↓0} Σ_μ(-s)` exists exactly
when the inverse first moment `∫ λ⁻¹ dTr μ` is finite. -/
theorem tendsto_stieltjesSelfEnergy_neg_iff :
    (∃ L : Matrix H H ℂ, Tendsto (fun s : ℝ => μ.stieltjesSelfEnergy (-(s : ℂ))) (𝓝[>] 0) (𝓝 L)) ↔
      Integrable (fun lam : ℝ => lam⁻¹) μ.traceMeasure :=
  ⟨fun ⟨_, h⟩ => μ.integrable_inv_of_tendsto_stieltjesSelfEnergy_neg h,
    fun h => ⟨_, μ.tendsto_stieltjesSelfEnergy_neg_of_integrable h⟩⟩

/-! ## The inverse-moment boundary jets `eq:supp-dynamic-jet` -/

/-- `G_k(x) = ∫ (λ - x)^{-(k+1)} dμ(λ)` as an `H → H → ℂ`-valued function of `x`. -/
noncomputable def resolventPow (k : ℕ) (x : ℝ) : H → H → ℂ :=
  VectorMeasure.integral μ.toVectorMeasure
    (fun lam : ℝ => ((((lam - x) ^ (k + 1))⁻¹ : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)

theorem resolventPow_zero_eq (k : ℕ) : μ.resolventPow k 0 = Matrix.of.symm (μ.inverseMoment (k + 1)) := by
  unfold resolventPow inverseMoment
  simp only [sub_zero, Equiv.symm_apply_apply]

theorem stieltjesSelfEnergy_ofReal_eq_resolventPow (x : ℝ) :
    Matrix.of.symm (μ.stieltjesSelfEnergy (x : ℂ)) = μ.resolventPow 0 x := by
  unfold stieltjesSelfEnergy resolventPow
  simp only [Equiv.symm_apply_apply, zero_add, pow_one]
  congr 1
  funext lam
  push_cast
  rfl

/-- One-sided differentiability of `G_k` within `(-∞, 0]`, with `G_k' = (k+1) G_{k+1}`. -/
theorem hasDerivWithinAt_resolventPow (k : ℕ)
    (hk : Integrable (fun lam : ℝ => (lam ^ (k + 2))⁻¹) μ.traceMeasure) {x : ℝ} (hx : x ≤ 0) :
    HasDerivWithinAt (μ.resolventPow k) (((k : ℝ) + 1) • μ.resolventPow (k + 1) x) (Iic 0) x := by
  have hbound := μ.integrable_variation_of_traceMeasure hk
  have key := VectorMeasureCalculus.hasDerivWithinAt_integral_of_dominated (μ := μ.toVectorMeasure)
    (B := ContinuousLinearMap.lsmul ℝ ℂ) (convex_Iic (0 : ℝ))
    (Φ := fun x lam => ((((lam - x) ^ (k + 1))⁻¹ : ℝ) : ℂ))
    (Φ' := fun x lam => (((((k : ℝ) + 1) * ((lam - x) ^ (k + 2))⁻¹ : ℝ)) : ℂ))
    (bound := fun lam => ((k : ℝ) + 1) * (lam ^ (k + 2))⁻¹) hx ?_ ?_ ?_ (hbound.const_mul _) ?_
  · have heq : VectorMeasure.integral μ.toVectorMeasure
        (fun lam : ℝ => (((((k : ℝ) + 1) * ((lam - x) ^ (k + 2))⁻¹ : ℝ)) : ℂ))
        (ContinuousLinearMap.lsmul ℝ ℂ) = ((k : ℝ) + 1) • μ.resolventPow (k + 1) x := by
      unfold resolventPow
      rw [← VectorMeasure.integral_fun_smul]
      congr 1
      funext lam
      rw [Complex.real_smul]
      push_cast
      ring
    rw [heq] at key
    exact key
  · intro y _
    exact (by fun_prop : Measurable fun lam : ℝ => ((((lam - y) ^ (k + 1))⁻¹ : ℝ) : ℂ)).aestronglyMeasurable
  · refine Integrable.mono' (μ.integrable_inv_pow_variation hk (Nat.le_succ _))
      (by fun_prop : Measurable fun lam : ℝ => ((((lam - x) ^ (k + 1))⁻¹ : ℝ) : ℂ)).aestronglyMeasurable ?_
    filter_upwards [μ.ae_pos_variation] with lam hlam
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (by linarith) _))]
    exact inv_anti₀ (pow_pos hlam _) (pow_le_pow_left₀ hlam.le (by linarith) _)
  · filter_upwards [μ.ae_pos_variation] with lam hlam
    intro y hy
    have hy' : y ≤ 0 := hy
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (by linarith) _)))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact inv_anti₀ (pow_pos hlam _) (pow_le_pow_left₀ hlam.le (by linarith) _)
  · filter_upwards [μ.ae_pos_variation] with lam hlam
    intro y hy
    have hy' : y ≤ 0 := hy
    have hne : lam - y ≠ 0 := by linarith
    have h1 : HasDerivAt (fun y : ℝ => ((lam - y) ^ (k + 1))⁻¹)
        (((k : ℝ) + 1) * ((lam - y) ^ (k + 2))⁻¹) y := by
      have hc : HasDerivAt (fun y : ℝ => lam - y) (-1) y := (hasDerivAt_id y).const_sub lam
      have h2 : HasDerivAt (fun y : ℝ => ((lam - y) ^ (k + 1))⁻¹)
          (-(((k + 1 : ℕ) : ℝ) * (lam - y) ^ (k + 1 - 1) * -1) / ((lam - y) ^ (k + 1)) ^ 2) y :=
        (hc.pow (k + 1)).inv (pow_ne_zero _ hne)
      refine h2.congr_deriv ?_
      rw [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
    exact h1.ofReal_comp.hasDerivWithinAt

/-- The `k`-th one-sided derivative of `x ↦ Σ_μ(x)` on `(-∞, 0]` is `k! G_k`, for `k ≤ r`. -/
theorem iteratedDerivWithin_stieltjesSelfEnergy (r : ℕ)
    (hr : Integrable (fun lam : ℝ => (lam ^ (r + 1))⁻¹) μ.traceMeasure) :
    ∀ k ≤ r, EqOn (iteratedDerivWithin k
        (fun x : ℝ => Matrix.of.symm (μ.stieltjesSelfEnergy (x : ℂ))) (Iic 0))
      (fun x => (k.factorial : ℝ) • μ.resolventPow k x) (Iic 0) := by
  intro k
  induction k with
  | zero =>
    intro _ x _
    simp only [iteratedDerivWithin_zero, Nat.factorial_zero, Nat.cast_one, one_smul]
    exact μ.stieltjesSelfEnergy_ofReal_eq_resolventPow x
  | succ k ih =>
    intro hk x hx
    have ih' := ih (by omega)
    rw [iteratedDerivWithin_succ, derivWithin_congr ih' (ih' hx)]
    have hd : HasDerivWithinAt (fun x => (k.factorial : ℝ) • μ.resolventPow k x)
        ((k.factorial : ℝ) • (((k : ℝ) + 1) • μ.resolventPow (k + 1) x)) (Iic 0) x :=
      (μ.hasDerivWithinAt_resolventPow k
        (μ.integrable_inv_pow_traceMeasure hr (by omega)) hx).const_smul (k.factorial : ℝ)
    rw [hd.derivWithin (uniqueDiffOn_Iic 0 x hx)]
    show _ = ((k + 1).factorial : ℝ) • μ.resolventPow (k + 1) x
    rw [smul_smul, Nat.factorial_succ]
    push_cast
    ring_nf

/-- **`eq:supp-dynamic-jet`.**  If the inverse moment `∫ λ^{-(r+1)} dTr μ` is finite, the `r`-th
boundary jet of `Σ_μ` at `0` (one-sided derivative within `(-∞, 0]`, taken entrywise) is
`r! ∫ λ^{-(r+1)} dμ(λ)`. -/
theorem iteratedDerivWithin_stieltjesSelfEnergy_zero (r : ℕ)
    (hr : Integrable (fun lam : ℝ => (lam ^ (r + 1))⁻¹) μ.traceMeasure) :
    iteratedDerivWithin r (fun x : ℝ => Matrix.of.symm (μ.stieltjesSelfEnergy (x : ℂ))) (Iic 0) 0 =
      (r.factorial : ℝ) • Matrix.of.symm (μ.inverseMoment (r + 1)) := by
  rw [μ.iteratedDerivWithin_stieltjesSelfEnergy r hr r le_rfl (mem_Iic.mpr le_rfl)]
  show (r.factorial : ℝ) • μ.resolventPow r 0 = _
  rw [resolventPow_zero_eq]

/-! ## Positive Euclidean memory `eq:supp-Euclidean-memory` -/

theorem integrable_exp_neg_mul_traceMeasure {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun lam : ℝ => Real.exp (-t * lam)) μ.traceMeasure := by
  refine Integrable.mono' (integrable_const 1)
    (by fun_prop : Measurable fun lam : ℝ => Real.exp (-t * lam)).aestronglyMeasurable ?_
  filter_upwards [μ.ae_pos_traceMeasure] with lam hlam
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith)

theorem integrable_exp_neg_mul_variation {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun lam : ℝ => Real.exp (-t * lam)) μ.toVectorMeasure.variation :=
  μ.integrable_variation_of_traceMeasure (μ.integrable_exp_neg_mul_traceMeasure ht)

/-- **Positivity of the Euclidean memory kernel**: `K_μ(t) ⪰ 0` for `t ≥ 0`. -/
theorem posSemidef_euclideanMemoryKernel {t : ℝ} (ht : 0 ≤ t) :
    (μ.euclideanMemoryKernel t).PosSemidef :=
  μ.posSemidef_integral_ofReal_of_nonneg (μ.integrable_exp_neg_mul_variation ht)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)

/-- The memory kernel is bounded by the total trace mass: `‖K_μ(t)‖ ≤ Tr μ((0,∞))` (sup norm of
the entries). -/
theorem norm_euclideanMemoryKernel_le {t : ℝ} (ht : 0 ≤ t) :
    ‖Matrix.of.symm (μ.euclideanMemoryKernel t)‖ ≤ (μ.traceMeasure univ).toReal := by
  have hf := μ.integrable_exp_neg_mul_variation ht
  refine (posSemidef_norm_le_re_trace (μ.posSemidef_euclideanMemoryKernel ht)).trans ?_
  change (Matrix.of (VectorMeasure.integral μ.toVectorMeasure
    (fun lam : ℝ => ((Real.exp (-t * lam) : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ))).trace.re ≤ _
  rw [μ.re_trace_integral_ofReal hf]
  have hτ : ∀ᵐ lam ∂μ.traceMeasure, Real.exp (-t * lam) ≤ 1 := by
    filter_upwards [μ.ae_pos_traceMeasure] with lam hlam
    exact Real.exp_le_one_iff.2 (by nlinarith)
  calc ∫ lam, Real.exp (-t * lam) ∂μ.traceMeasure ≤ ∫ _, (1 : ℝ) ∂μ.traceMeasure :=
        integral_mono_ae (μ.integrable_exp_neg_mul_traceMeasure ht) (integrable_const 1) hτ
    _ = (μ.traceMeasure univ).toReal := by
        rw [integral_const, smul_eq_mul, mul_one, measureReal_def]

/-- Continuity of the memory kernel on `[0, ∞)`. -/
theorem continuousOn_euclideanMemoryKernel :
    ContinuousOn (fun t : ℝ => Matrix.of.symm (μ.euclideanMemoryKernel t)) (Ici 0) := by
  change ContinuousOn (fun t : ℝ => VectorMeasure.integral μ.toVectorMeasure
    (fun lam : ℝ => ((Real.exp (-t * lam) : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)) (Ici 0)
  refine VectorMeasure.continuousOn_of_dominated (bound := fun _ => (1 : ℝ)) (fun t _ =>
    (by fun_prop : Measurable fun lam : ℝ => ((Real.exp (-t * lam) : ℝ) : ℂ)).aestronglyMeasurable)
    (fun t ht => ?_) (integrable_const 1) (ae_of_all _ fun lam => by fun_prop)
  filter_upwards [μ.ae_pos_variation] with lam hlam
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith [mem_Ici.mp ht])

/-- **Laplace relation `Σ_μ(-s) = ∫_0^∞ e^{-st} K_μ(t) dt`** for `s > 0` (Bochner integral of the
entries). -/
theorem stieltjesSelfEnergy_neg_eq_integral_euclideanMemoryKernel {s : ℝ} (hs : 0 < s) :
    μ.stieltjesSelfEnergy (-(s : ℂ)) =
      Matrix.of (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) • Matrix.of.symm (μ.euclideanMemoryKernel t)) := by
  set Kraw : ℝ → H → H → ℂ := fun t => Matrix.of.symm (μ.euclideanMemoryKernel t) with hKraw
  have hKmeas : AEStronglyMeasurable Kraw ((volume : Measure ℝ).restrict (Ioi 0)) :=
    (μ.continuousOn_euclideanMemoryKernel.mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi
  have hint : Integrable (fun t => Real.exp (-s * t) • Kraw t) ((volume : Measure ℝ).restrict (Ioi 0)) := by
    refine Integrable.mono' ((StieltjesLaplace.integrable_exp_neg_mul_restrict_Ioi hs).mul_const
      (μ.traceMeasure univ).toReal)
      ((StieltjesLaplace.integrable_exp_neg_mul_restrict_Ioi hs).aestronglyMeasurable.smul hKmeas) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun t ht => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (μ.norm_euclideanMemoryKernel_le (le_of_lt ht)) (Real.exp_pos _).le
  -- polarisation: compare the quadratic forms
  have hq : ∀ ξ : H → ℂ, quadForm ξ (μ.stieltjesSelfEnergy (-(s : ℂ))) =
      quadForm ξ (Matrix.of (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) • Kraw t)) := by
    intro ξ
    -- left-hand side
    rw [stieltjesSelfEnergy_neg_real, μ.quadForm_integral_ofReal ξ (μ.integrable_inv_add_variation hs)]
    -- right-hand side through the sesquilinear functional
    change _ = sesqCLM ξ ξ (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) • Kraw t)
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    have hpt : ∀ t : ℝ, 0 ≤ t → sesqCLM ξ ξ (Real.exp (-s * t) • Kraw t) =
        ((Real.exp (-s * t) * ∫ lam, Real.exp (-t * lam) ∂(μ.formMeasure ξ) : ℝ) : ℂ) := by
      intro t ht
      rw [map_smul, hKraw]
      change Real.exp (-s * t) • quadForm ξ (μ.euclideanMemoryKernel t) = _
      change Real.exp (-s * t) • quadForm ξ (Matrix.of (VectorMeasure.integral μ.toVectorMeasure
        (fun lam : ℝ => ((Real.exp (-t * lam) : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ))) = _
      rw [μ.quadForm_integral_ofReal ξ (μ.integrable_exp_neg_mul_variation ht), Complex.real_smul]
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t (le_of_lt ht),
      integral_complex_ofReal]
    congr 1
    exact StieltjesLaplace.integral_inv_add_eq_integral_exp_laplace (μ.formMeasure_Iio ξ) hs
  have hzero : ∀ ξ : H → ℂ, quadForm ξ (μ.stieltjesSelfEnergy (-(s : ℂ)) -
      Matrix.of (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) • Kraw t)) = 0 := fun ξ => by
    rw [quadForm_sub, hq ξ, sub_self]
  exact sub_eq_zero.mp (matrix_eq_zero_of_forall_quadForm_eq_zero hzero)

/-- **`thm:supp-dynamic-jets` (Static shadows, inverse moments, and positive Euclidean memory).**
For a positive operator-valued tail measure `μ` (`def:supp-POVM`):
`Im Σ_μ(z) = (Im z) ∫ |λ - z|⁻² dμ ⪰ 0` for `Im z > 0`; the static shadow `lim_{s↓0} Σ_μ(-s)`
exists iff `∫ λ⁻¹ dTr μ < ∞`, and then equals `∫ λ⁻¹ dμ`; if `∫ λ^{-(r+1)} dTr μ < ∞` the `r`-th
boundary jet at `0` is `r! ∫ λ^{-(r+1)} dμ`; the Euclidean memory kernel `K_μ(t) = ∫ e^{-tλ} dμ`
is positive semidefinite for `t ≥ 0` and `Σ_μ(-s) = ∫_0^∞ e^{-st} K_μ(t) dt` for `s > 0`. -/
theorem dynamic_jets :
    (∀ z : ℂ, 0 < z.im → matrixIm (μ.stieltjesSelfEnergy z) =
      (z.im : ℂ) • Matrix.of (VectorMeasure.integral μ.toVectorMeasure
        (fun lam : ℝ => (((‖(lam : ℂ) - z‖ ^ 2)⁻¹ : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)) ∧
      (matrixIm (μ.stieltjesSelfEnergy z)).PosSemidef) ∧
    ((∃ L : Matrix H H ℂ, Tendsto (fun s : ℝ => μ.stieltjesSelfEnergy (-(s : ℂ))) (𝓝[>] 0) (𝓝 L)) ↔
      Integrable (fun lam : ℝ => lam⁻¹) μ.traceMeasure) ∧
    (Integrable (fun lam : ℝ => lam⁻¹) μ.traceMeasure →
      Tendsto (fun s : ℝ => μ.stieltjesSelfEnergy (-(s : ℂ))) (𝓝[>] 0) (𝓝 (μ.inverseMoment 1))) ∧
    (∀ r : ℕ, Integrable (fun lam : ℝ => (lam ^ (r + 1))⁻¹) μ.traceMeasure →
      iteratedDerivWithin r (fun x : ℝ => Matrix.of.symm (μ.stieltjesSelfEnergy (x : ℂ)))
        (Iic 0) 0 = (r.factorial : ℝ) • Matrix.of.symm (μ.inverseMoment (r + 1))) ∧
    (∀ t : ℝ, 0 ≤ t → (μ.euclideanMemoryKernel t).PosSemidef) ∧
    (∀ s : ℝ, 0 < s → μ.stieltjesSelfEnergy (-(s : ℂ)) =
      Matrix.of (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) • Matrix.of.symm (μ.euclideanMemoryKernel t))) :=
  ⟨fun z hz => ⟨μ.matrixIm_stieltjesSelfEnergy (fun h => by linarith [h.1]),
      μ.posSemidef_matrixIm_stieltjesSelfEnergy hz⟩,
    μ.tendsto_stieltjesSelfEnergy_neg_iff,
    fun h => μ.tendsto_stieltjesSelfEnergy_neg_of_integrable h,
    fun r hr => μ.iteratedDerivWithin_stieltjesSelfEnergy_zero r hr,
    fun _ ht => μ.posSemidef_euclideanMemoryKernel ht,
    fun _ hs => μ.stieltjesSelfEnergy_neg_eq_integral_euclideanMemoryKernel hs⟩

end PositiveTailMeasure

end OperatorTailMeasure
end RenewalGeometry
