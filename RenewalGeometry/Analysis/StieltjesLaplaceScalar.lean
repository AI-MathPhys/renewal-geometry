/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.OperatorTailMeasureDeterminacyExact
/-!
# Laplace and Stieltjes transforms of finite measures on `[0, ∞)`

Scalar infrastructure for `thm:supp-dynamic-jets` (the Laplace relation
`Σ_μ(-s) = ∫_0^∞ e^{-st} K_μ(t) dt`) and `cth:supp-moment-indeterminate` (injectivity of the
Stieltjes transform) of `papers/predictive_spectral_geometry`.

* `integral_exp_neg_mul_Ioi_zero`: `∫_0^∞ e^{-a t} dt = a⁻¹` for `a > 0`;
* `integral_inv_add_eq_integral_exp_laplace` (Tonelli/Fubini): for a finite measure `ν` on
  `[0, ∞)` and `s > 0`, `∫ (λ + s)⁻¹ dν(λ) = ∫_0^∞ e^{-st} (∫ e^{-tλ} dν(λ)) dt`;
* `continuousOn_laplace`: the Laplace transform `t ↦ ∫ e^{-tλ} dν(λ)` is continuous on `[0,∞)`;
* `measure_eq_of_forall_integral_exp_neg_nat_mul_eq`: two finite measures on `[0,∞)` whose
  Laplace transforms agree at the nonnegative integers coincide (push forward under
  `x ↦ e^{-x}` and use moment determinacy on `(0, 1]`);
* `measure_eq_of_forall_integral_inv_add_eq`: two finite measures on `[0,∞)` with the same
  Stieltjes transform on the negative real axis coincide — **injectivity of the Stieltjes
  transform** — obtained from the two previous items by two applications of Laplace uniqueness,
  exactly as in the paper's proof of `cth:supp-moment-indeterminate`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace RenewalGeometry
namespace StieltjesLaplace

/-- `∫_0^∞ e^{-a t} dt = a⁻¹` for `a > 0`. -/
theorem integral_exp_neg_mul_Ioi_zero {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) = a⁻¹ := by
  have h := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  rw [h]
  simp [neg_div_neg_eq, one_div]

/-- `e^{-a t}` is integrable on `(0, ∞)` for `a > 0`. -/
theorem integrable_exp_neg_mul_restrict_Ioi {a : ℝ} (ha : 0 < a) :
    Integrable (fun t => Real.exp (-a * t)) ((volume : Measure ℝ).restrict (Ioi 0)) :=
  exp_neg_integrableOn_Ioi 0 ha

/-- Lebesgue measure restricted to `(0, ∞)` vanishes on `(-∞, 0)`. -/
theorem restrict_Ioi_apply_Iio :
    ((volume : Measure ℝ).restrict (Ioi 0)) (Iio 0) = 0 := by
  rw [Measure.restrict_apply measurableSet_Iio, Set.Iio_inter_Ioi, Set.Ioo_self, measure_empty]

/-- A finite measure vanishing on `(-∞, 0)` is concentrated on `[0, ∞)`. -/
theorem ae_nonneg_of_measure_Iio {ν : Measure ℝ} (hν : ν (Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  exact measure_mono_null (fun x hx => not_le.mp hx) hν

/-- The Laplace transform `t ↦ ∫ e^{-tλ} dν(λ)` of a finite measure on `[0,∞)` is bounded by the
total mass for `t ≥ 0`. -/
theorem integrable_exp_neg_mul {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x => Real.exp (-t * x)) ν := by
  refine Integrable.mono' (integrable_const 1) (by fun_prop) ?_
  filter_upwards [ae_nonneg_of_measure_Iio hν] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith)

/-- The Laplace transform of a finite measure on `[0,∞)` is nonnegative. -/
theorem laplace_nonneg {ν : Measure ℝ} (t : ℝ) : 0 ≤ ∫ x, Real.exp (-t * x) ∂ν :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- The Laplace transform of a finite measure on `[0,∞)` is bounded by the total mass on
`[0, ∞)`. -/
theorem laplace_le_mass {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) {t : ℝ}
    (ht : 0 ≤ t) : ∫ x, Real.exp (-t * x) ∂ν ≤ (ν univ).toReal := by
  have h : ∫ x, Real.exp (-t * x) ∂ν ≤ ∫ _, (1 : ℝ) ∂ν := by
    refine integral_mono_ae (integrable_exp_neg_mul hν ht) (integrable_const 1) ?_
    filter_upwards [ae_nonneg_of_measure_Iio hν] with x hx
    exact Real.exp_le_one_iff.2 (by nlinarith)
  rwa [integral_const, smul_eq_mul, mul_one, measureReal_def] at h

/-- Continuity of the Laplace transform on `[0, ∞)`. -/
theorem continuousOn_laplace {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) :
    ContinuousOn (fun t : ℝ => ∫ x, Real.exp (-t * x) ∂ν) (Ici 0) := by
  refine continuousOn_of_dominated (bound := fun _ => (1 : ℝ)) (fun t _ => by fun_prop)
    (fun t ht => ?_) (integrable_const 1) (ae_of_all _ fun x => by fun_prop)
  filter_upwards [ae_nonneg_of_measure_Iio hν] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith [mem_Ici.mp ht])

/-- **Tonelli/Fubini for the Stieltjes transform.**  For a finite measure `ν` on `[0, ∞)` and
`s > 0`, `∫ (λ + s)⁻¹ dν(λ) = ∫_0^∞ e^{-st} (∫ e^{-tλ} dν(λ)) dt`. -/
theorem integral_inv_add_eq_integral_exp_laplace {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ν (Iio 0) = 0) {s : ℝ} (hs : 0 < s) :
    ∫ lam, (lam + s)⁻¹ ∂ν =
      ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * ∫ lam, Real.exp (-t * lam) ∂ν := by
  have hmem := ae_nonneg_of_measure_Iio hν
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ → ℝ, f = fun t lam => Real.exp (-s * t) * Real.exp (-t * lam) :=
    ⟨_, rfl⟩
  have hf_cont : Continuous (Function.uncurry f) := by
    simp only [hf, Function.uncurry_def]
    fun_prop
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by
    rw [integrable_prod_iff hf_cont.aestronglyMeasurable]
    constructor
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun t ht => ?_
      refine Integrable.mono' (integrable_const (Real.exp (-s * t))) (by fun_prop) ?_
      filter_upwards [hmem] with lam hlam
      simp only [Function.uncurry_apply_pair, hf]
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      have : Real.exp (-t * lam) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mem_Ioi.mp ht])
      nlinarith [Real.exp_pos (-s * t)]
    · refine Integrable.mono' (g := fun t => Real.exp (-s * t) * (ν univ).toReal) ?_ ?_ ?_
      · exact (integrable_exp_neg_mul_restrict_Ioi hs).mul_const _
      · exact hf_cont.norm.aestronglyMeasurable.integral_prod_right'
      · rw [ae_restrict_iff' measurableSet_Ioi]
        refine ae_of_all _ fun t ht => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        calc ∫ lam, ‖Function.uncurry f (t, lam)‖ ∂ν
            ≤ ∫ _, Real.exp (-s * t) ∂ν := by
              refine integral_mono_ae ?_ (integrable_const _) ?_
              · exact (Integrable.mono' (integrable_const (Real.exp (-s * t))) (by fun_prop)
                  (by
                    filter_upwards [hmem] with lam hlam
                    simp only [Function.uncurry_apply_pair, hf]
                    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
                    have : Real.exp (-t * lam) ≤ 1 :=
                      Real.exp_le_one_iff.2 (by nlinarith [mem_Ioi.mp ht])
                    nlinarith [Real.exp_pos (-s * t)])).norm
              · filter_upwards [hmem] with lam hlam
                simp only [Function.uncurry_apply_pair, hf]
                rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
                have : Real.exp (-t * lam) ≤ 1 :=
                  Real.exp_le_one_iff.2 (by nlinarith [mem_Ioi.mp ht])
                nlinarith [Real.exp_pos (-s * t)]
          _ = Real.exp (-s * t) * (ν univ).toReal := by
              rw [integral_const, smul_eq_mul, mul_comm, measureReal_def]
  have hswap : ∫ t in Ioi (0 : ℝ), (∫ lam, f t lam ∂ν) =
      ∫ lam, (∫ t in Ioi (0 : ℝ), f t lam) ∂ν :=
    integral_integral_swap hint
  have h1 : ∫ lam, (lam + s)⁻¹ ∂ν = ∫ lam, (∫ t in Ioi (0 : ℝ), f t lam) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hmem] with lam hlam
    have h1 : ∀ t : ℝ, f t lam = Real.exp (-(s + lam) * t) := fun t => by
      simp only [hf]
      rw [← Real.exp_add]
      ring_nf
    simp_rw [h1]
    rw [integral_exp_neg_mul_Ioi_zero (by linarith), add_comm]
  have h2 : ∫ t in Ioi (0 : ℝ), (∫ lam, f t lam ∂ν) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * ∫ lam, Real.exp (-t * lam) ∂ν := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hf]
    rw [integral_const_mul]
  rw [h1, ← hswap, h2]

/-- **Laplace uniqueness at the integers.**  Two finite measures on `[0,∞)` whose Laplace
transforms agree at every nonnegative integer coincide. -/
theorem measure_eq_of_forall_integral_exp_neg_nat_mul_eq {ν ν' : Measure ℝ} [IsFiniteMeasure ν]
    [IsFiniteMeasure ν'] (hν : ν (Iio 0) = 0) (hν' : ν' (Iio 0) = 0)
    (h : ∀ n : ℕ, ∫ x, Real.exp (-(n : ℝ) * x) ∂ν = ∫ x, Real.exp (-(n : ℝ) * x) ∂ν') :
    ν = ν' := by
  set φ : ℝ → ℝ := fun x => Real.exp (-x) with hφdef
  have hφm : Measurable φ := by fun_prop
  have hφ : MeasurableEmbedding φ :=
    hφm.measurableEmbedding fun x y hxy => by
      simpa [hφdef] using Real.exp_injective hxy
  have hsupp : ∀ {m : Measure ℝ}, m (Iio 0) = 0 → m.map φ (Ioc 0 1)ᶜ = 0 := by
    intro m hm
    rw [hφ.map_apply]
    refine measure_mono_null (fun x hx => ?_) hm
    simp only [mem_preimage, mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le, hφdef] at hx
    rcases hx with hx | hx
    · exact absurd hx (not_le.mpr (Real.exp_pos _))
    · rw [Real.one_lt_exp_iff] at hx
      exact mem_Iio.mpr (by linarith)
  have key : ν.map φ = ν'.map φ := by
    refine OperatorTailMeasure.measure_eq_of_forall_integral_pow_eq_of_compact (hsupp hν)
      (hsupp hν') fun n => ?_
    rw [hφ.integral_map, hφ.integral_map]
    have hpow : ∀ x : ℝ, φ x ^ n = Real.exp (-(n : ℝ) * x) := fun x => by
      rw [hφdef]
      simp only
      rw [← Real.exp_nat_mul]
      ring_nf
    simp_rw [hpow]
    exact h n
  refine Measure.ext fun s hs => ?_
  have := congrArg (fun m : Measure ℝ => m (φ '' s)) key
  simp only [hφ.map_apply, preimage_image_eq _ hφ.injective] at this
  exact this

/-- The Laplace transform of `ν` evaluated at the integer `n + 1` is the `n`-th Laplace value
of the exponentially weighted measure `e^{-λ} dν`. -/
theorem integral_exp_neg_nat_mul_withDensity {ν : Measure ℝ} (n : ℕ) :
    ∫ x, Real.exp (-(n : ℝ) * x) ∂(ν.withDensity fun x => ENNReal.ofReal (Real.exp (-x))) =
      ∫ x, Real.exp (-((n : ℝ) + 1) * x) ∂ν := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, ← Real.exp_add]
  ring_nf

/-- **Injectivity of the Stieltjes transform on the negative axis.**  Two finite measures on
`[0, ∞)` with `∫ (λ + s)⁻¹ dν = ∫ (λ + s)⁻¹ dν'` for every `s > 0` coincide.  Following the
paper's proof of `cth:supp-moment-indeterminate`: by the Fubini relation the Laplace transforms
of the (bounded continuous) Laplace transforms agree, so the latter agree on `(0,∞)` by Laplace
uniqueness, hence at the integers, and a second Laplace uniqueness gives `ν = ν'`. -/
theorem measure_eq_of_forall_integral_inv_add_eq {ν ν' : Measure ℝ} [IsFiniteMeasure ν]
    [IsFiniteMeasure ν'] (hν : ν (Iio 0) = 0) (hν' : ν' (Iio 0) = 0)
    (h : ∀ s : ℝ, 0 < s → ∫ lam, (lam + s)⁻¹ ∂ν = ∫ lam, (lam + s)⁻¹ ∂ν') : ν = ν' := by
  set vol := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)) with hvol
  have hvolIio : vol (Iio 0) = 0 := restrict_Ioi_apply_Iio
  -- the Laplace transforms `L`, `L'`, their exponential weights as measures on `(0,∞)`
  have hstep : ∀ {m : Measure ℝ} [IsFiniteMeasure m], m (Iio 0) = 0 →
      ∃ (L : ℝ → ℝ), (∀ t, L t = ∫ x, Real.exp (-t * x) ∂m) ∧ (∀ t, 0 ≤ L t) ∧
        ContinuousOn L (Ici 0) ∧ AEStronglyMeasurable L vol ∧
        (∀ t, 0 ≤ t → L t ≤ (m univ).toReal) ∧
        (∀ s : ℝ, 0 < s → ∫ lam, (lam + s)⁻¹ ∂m = ∫ t, Real.exp (-s * t) * L t ∂vol) ∧
        (∀ n : ℕ, ∫ t, Real.exp (-(n : ℝ) * t)
            ∂(vol.withDensity fun t => ENNReal.ofReal (Real.exp (-t) * L t)) =
          ∫ t, Real.exp (-((n : ℝ) + 1) * t) * L t ∂vol) := by
    intro m _ hm
    refine ⟨fun t => ∫ x, Real.exp (-t * x) ∂m, fun t => rfl, fun t => laplace_nonneg t,
      continuousOn_laplace hm, ?_, fun t ht => laplace_le_mass hm ht,
      fun s hs => integral_inv_add_eq_integral_exp_laplace hm hs, fun n => ?_⟩
    · have hc : Continuous (Function.uncurry fun (t x : ℝ) => Real.exp (-t * x)) := by
        simp only [Function.uncurry_def]
        fun_prop
      exact (hc.aestronglyMeasurable (μ := vol.prod m)).integral_prod_right'
    · have hmeas : AEMeasurable (fun t => ENNReal.ofReal (Real.exp (-t) *
          ∫ x, Real.exp (-t * x) ∂m)) vol := by
        have hc : Continuous (Function.uncurry fun (t x : ℝ) => Real.exp (-t * x)) := by
          simp only [Function.uncurry_def]
          fun_prop
        exact ENNReal.measurable_ofReal.comp_aemeasurable
          ((measurable_id.neg.exp.aemeasurable).mul
            (hc.aestronglyMeasurable (μ := vol.prod m)).integral_prod_right'.aemeasurable)
      rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      beta_reduce
      rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (laplace_nonneg _)), smul_eq_mul]
      have : Real.exp (-((n : ℝ) + 1) * t) = Real.exp (-t) * Real.exp (-(n : ℝ) * t) := by
        rw [← Real.exp_add]
        ring_nf
      rw [this]
      ring
  obtain ⟨L, hL, hL0, hLc, hLm, hLb, hLs, hLn⟩ := hstep hν
  obtain ⟨L', hL', hL'0, hL'c, hL'm, hL'b, hL's, hL'n⟩ := hstep hν'
  -- finiteness of the weighted measures
  have hfin : ∀ {M : ℝ → ℝ}, (∀ t, 0 ≤ M t) → AEStronglyMeasurable M vol →
      (∀ t, 0 ≤ t → M t ≤ (ν univ).toReal + (ν' univ).toReal) →
      ∫⁻ t, ENNReal.ofReal (Real.exp (-t) * M t) ∂vol ≠ ∞ := by
    intro M hM0 hMm hMb
    set C := (ν univ).toReal + (ν' univ).toReal
    have hint : Integrable (fun t => Real.exp (-t) * C) vol := by
      have := integrable_exp_neg_mul_restrict_Ioi (a := 1) one_pos
      simp only [neg_mul, one_mul] at this
      exact this.mul_const C
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∫ t, Real.exp (-t) * C ∂vol)) ?_
    calc ∫⁻ t, ENNReal.ofReal (Real.exp (-t) * M t) ∂vol
        ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (-t) * C) ∂vol := by
          refine lintegral_mono_ae ?_
          rw [hvol, ae_restrict_iff' measurableSet_Ioi]
          refine ae_of_all _ fun t ht => ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_left (hMb t (le_of_lt ht)) (Real.exp_pos _).le
      _ = ENNReal.ofReal (∫ t, Real.exp (-t) * C ∂vol) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint]
          refine ae_of_all _ fun t => ?_
          have : 0 ≤ C := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
          positivity
  -- the weighted measures coincide (Laplace uniqueness at the integers)
  set ρ := vol.withDensity fun t => ENNReal.ofReal (Real.exp (-t) * L t) with hρ
  set ρ' := vol.withDensity fun t => ENNReal.ofReal (Real.exp (-t) * L' t) with hρ'
  have hLm' : AEMeasurable (fun t => ENNReal.ofReal (Real.exp (-t) * L t)) vol :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (measurable_id.neg.exp.aemeasurable.mul hLm.aemeasurable)
  have hL'm' : AEMeasurable (fun t => ENNReal.ofReal (Real.exp (-t) * L' t)) vol :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (measurable_id.neg.exp.aemeasurable.mul hL'm.aemeasurable)
  have : IsFiniteMeasure ρ := isFiniteMeasure_withDensity
    (hfin hL0 hLm fun t ht => (hLb t ht).trans (le_add_of_nonneg_right ENNReal.toReal_nonneg))
  have : IsFiniteMeasure ρ' := isFiniteMeasure_withDensity
    (hfin hL'0 hL'm fun t ht => (hL'b t ht).trans (le_add_of_nonneg_left ENNReal.toReal_nonneg))
  have hρρ' : ρ = ρ' := by
    refine measure_eq_of_forall_integral_exp_neg_nat_mul_eq
      (withDensity_absolutelyContinuous vol _ hvolIio)
      (withDensity_absolutelyContinuous vol _ hvolIio) fun n => ?_
    rw [hρ, hρ', hLn n, hL'n n, ← hLs _ (by positivity), ← hL's _ (by positivity)]
    exact h _ (by positivity)
  -- hence the Laplace transforms agree on `(0, ∞)`
  have hae : (fun t => ENNReal.ofReal (Real.exp (-t) * L t)) =ᵐ[vol]
      fun t => ENNReal.ofReal (Real.exp (-t) * L' t) :=
    (withDensity_eq_iff_of_sigmaFinite hLm' hL'm').1 hρρ'
  have hLL' : EqOn L L' (Ioi 0) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioi
      (hLc.mono Ioi_subset_Ici_self) (hL'c.mono Ioi_subset_Ici_self)
    rw [← hvol]
    filter_upwards [hae] with t ht
    rw [ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (Real.exp_pos _).le (hL0 t))
      (mul_nonneg (Real.exp_pos _).le (hL'0 t))] at ht
    exact mul_left_cancel₀ (Real.exp_pos _).ne' ht
  -- and at `0` by continuity
  have hL0' : L 0 = L' 0 := by
    have h1 : Tendsto L (𝓝[>] 0) (𝓝 (L 0)) :=
      (hLc.continuousWithinAt (mem_Ici.mpr le_rfl)).mono_left
        (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h2 : Tendsto L' (𝓝[>] 0) (𝓝 (L' 0)) :=
      (hL'c.continuousWithinAt (mem_Ici.mpr le_rfl)).mono_left
        (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h3 : Tendsto L' (𝓝[>] 0) (𝓝 (L 0)) :=
      h1.congr' (eventually_nhdsWithin_of_forall fun t ht => hLL' ht)
    exact tendsto_nhds_unique h3 h2
  -- second Laplace uniqueness
  refine measure_eq_of_forall_integral_exp_neg_nat_mul_eq hν hν' fun n => ?_
  rw [← hL, ← hL']
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using hL0'
  · exact hLL' (mem_Ioi.mpr (by exact_mod_cast hn))

end StieltjesLaplace
end RenewalGeometry
