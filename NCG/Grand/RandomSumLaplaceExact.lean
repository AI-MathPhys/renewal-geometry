/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.IndependentExponentialCompletionTime
import NCG.Grand.CompletedPrivateRenewalExact

/-!
# Random sums of i.i.d. clocks and the continuous completion time

Machinery for `thm:renewal-continuous-completion`.  The Poisson-uniformized renewal instrument
applies one fresh instrument copy at each jump of a rate-`λ` Poisson clock; the physical time to
the next completion is therefore the random sum
`𝒯 = ∑_{i < W} E_i` of `W` i.i.d. `Exp(λ)` inter-opportunity clocks, where `W` is the discrete
completed-private interarrival count (law `wpmf`, `thm:completed-private-renewal`) and is
independent of the clock.

* `charFun_map_partialSum`: the characteristic function of a sum of `k` i.i.d. clocks is the
  `k`-th power;
* `charFun_map_randomSum`: **the substituted generating function**
  `E[e^{it𝒯}] = ∑_k P(W = k) φ(t)^k = F_W(φ(t))`, obtained by partitioning on `{W = k}` and using
  the independence of `W` from the clock;
* `charFun_expMeasure`: `φ_{Exp(r)}(t) = r/(r - it)`;
* `wpmf_pgf_complex`: the completed-private generating function over `ℂ`;
* `map_randomSum_eq_independentExponentialCompletionLaw`: **the boxed law**
  `𝒯 ≃ Exp(4λ/5) + Exp(2λ/3)` with independent summands (equality of laws via characteristic
  functions);
* `renewal_continuous_completion`: the three boxed clauses (law, Laplace transform, mean and
  intensity) for the random-sum completion time.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology

namespace NCG
namespace RandomSum

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The partial sum `∑_{i < k} E i` of a clock family, as a function on `Ω`. -/
noncomputable def partialSum (E : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ := ∑ i ∈ Finset.range k, E i

omit [MeasurableSpace Ω] in
theorem partialSum_apply (E : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    partialSum E k ω = ∑ i ∈ Finset.range k, E i ω := by
  simp [partialSum, Finset.sum_apply]

omit [MeasurableSpace Ω] in
theorem partialSum_succ (E : ℕ → Ω → ℝ) (k : ℕ) :
    partialSum E (k + 1) = partialSum E k + E k := by
  simp [partialSum, Finset.sum_range_succ]

/-- The random sum `∑_{i < W ω} E i ω`: the physical time consumed by `W` clock ticks. -/
noncomputable def randomSum (W : Ω → ℕ) (E : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (W ω), E i ω

omit [MeasurableSpace Ω] in
theorem randomSum_eq_partialSum (W : Ω → ℕ) (E : ℕ → Ω → ℝ) {k : ℕ} {ω : Ω} (h : W ω = k) :
    randomSum W E ω = partialSum E k ω := by
  simp [randomSum, partialSum_apply, h]

theorem measurable_partialSum {E : ℕ → Ω → ℝ} (hE : ∀ i, Measurable (E i)) (k : ℕ) :
    Measurable (partialSum E k) := by
  have : partialSum E k = fun ω => ∑ i ∈ Finset.range k, E i ω := funext (partialSum_apply E k)
  rw [this]
  exact Finset.measurable_sum _ fun i _ => hE i

theorem measurable_randomSum {W : Ω → ℕ} {E : ℕ → Ω → ℝ} (hW : Measurable W)
    (hE : ∀ i, Measurable (E i)) : Measurable (randomSum W E) := by
  have hg : Measurable (fun p : ℕ × (ℕ → ℝ) => ∑ i ∈ Finset.range p.1, p.2 i) :=
    measurable_from_prod_countable_right fun k => by
      change Measurable fun y : ℕ → ℝ => ∑ i ∈ Finset.range k, y i
      exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact hg.comp (hW.prodMk (measurable_pi_lambda _ hE))

/-- The characteristic function of a constant-zero map is `1`. -/
theorem charFun_map_zero [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (μ.map (fun _ : Ω => (0 : ℝ))) t = 1 := by
  rw [charFun_apply_real, integral_map measurable_const.aemeasurable (by fun_prop)]
  simp

/-- **Characteristic function of a sum of `k` i.i.d. clocks.** -/
theorem charFun_map_partialSum [IsProbabilityMeasure μ] {E : ℕ → Ω → ℝ} {ν : Measure ℝ}
    (hE : ∀ i, Measurable (E i)) (hind : iIndepFun E μ) (hlaw : ∀ i, μ.map (E i) = ν)
    (k : ℕ) (t : ℝ) : charFun (μ.map (partialSum E k)) t = charFun ν t ^ k := by
  induction k with
  | zero =>
    have : partialSum E 0 = fun _ => 0 := by funext ω; simp [partialSum_apply]
    rw [this, charFun_map_zero, pow_zero]
  | succ k ih =>
    have hindep : partialSum E k ⟂ᵢ[μ] E k :=
      hind.indepFun_finsetSum_of_notMem hE Finset.notMem_range_self
    rw [partialSum_succ, hindep.charFun_map_add_eq_mul (measurable_partialSum hE k).aemeasurable
      (hE k).aemeasurable, Pi.mul_apply, ih, hlaw k, pow_succ]

/-- **The substituted generating function.**  If `W` is independent of the i.i.d. clock
family `E` with common law `ν`, the characteristic function of the random sum
`∑_{i < W} E i` is `∑_k P(W = k) φ_ν(t)^k`. -/
theorem charFun_map_randomSum [IsProbabilityMeasure μ] {W : Ω → ℕ} {E : ℕ → Ω → ℝ}
    {ν : Measure ℝ} (hW : Measurable W) (hE : ∀ i, Measurable (E i)) (hind : iIndepFun E μ)
    (hlaw : ∀ i, μ.map (E i) = ν) (hWE : W ⟂ᵢ[μ] (fun ω i => E i ω)) (t : ℝ) :
    charFun (μ.map (randomSum W E)) t
      = ∑' k : ℕ, ((μ {ω | W ω = k}).toReal : ℂ) * charFun ν t ^ k := by
  have hT := measurable_randomSum hW hE
  rw [charFun_apply_real, integral_map hT.aemeasurable (by fun_prop)]
  -- partition the sample space according to the value of `W`
  have hset : ∀ k : ℕ, MeasurableSet {ω | W ω = k} := fun k =>
    hW (measurableSet_singleton k)
  have hunion : (⋃ k : ℕ, {ω | W ω = k}) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.mpr ⟨W ω, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun k : ℕ => {ω | W ω = k}) := by
    intro k l hkl
    refine Set.disjoint_left.mpr fun ω h1 h2 => hkl ?_
    simp only [Set.mem_setOf_eq] at h1 h2
    rw [← h1, ← h2]
  have hint : Integrable (fun ω => exp (t * (randomSum W E ω : ℂ) * I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => ?_)
    simp [Complex.norm_exp]
  rw [← setIntegral_univ, ← hunion, integral_iUnion hset hdisj hint.integrableOn]
  refine tsum_congr fun k => ?_
  -- on `{W = k}` the random sum is the `k`-th partial sum
  have hcongr : ∫ ω in {ω | W ω = k}, exp (t * (randomSum W E ω : ℂ) * I) ∂μ
      = ∫ ω in {ω | W ω = k}, exp (t * (partialSum E k ω : ℂ) * I) ∂μ := by
    refine setIntegral_congr_fun (hset k) fun ω hω => ?_
    simp only [Set.mem_setOf_eq] at hω
    rw [randomSum_eq_partialSum W E hω]
  rw [hcongr, ← integral_indicator (hset k)]
  -- the indicator is a function of `W`, the clock sum a function of the clock family
  set φ : ℕ → ℂ := fun n => if n = k then 1 else 0 with hφ
  set ψ : (ℕ → ℝ) → ℂ := fun e => exp (t * ((∑ i ∈ Finset.range k, e i : ℝ) : ℂ) * I) with hψ
  have hfun : {ω | W ω = k}.indicator (fun ω => exp (t * (partialSum E k ω : ℂ) * I))
      = (φ ∘ W) * (ψ ∘ fun ω i => E i ω) := by
    funext ω
    by_cases h : W ω = k
    · simp [Set.indicator, h, hφ, hψ, partialSum_apply]
    · simp [Set.indicator, h, hφ]
  have hφm : Measurable φ := measurable_from_nat
  have hψm : Measurable ψ := by
    have hsum : Measurable (fun e : ℕ → ℝ => ∑ i ∈ Finset.range k, e i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have hc : Measurable (fun e : ℕ → ℝ => ((∑ i ∈ Finset.range k, e i : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp hsum
    exact ((measurable_const.mul hc).mul_const I).cexp
  have hindep : (φ ∘ W) ⟂ᵢ[μ] (ψ ∘ fun ω i => E i ω) := hWE.comp hφm hψm
  rw [hfun, hindep.integral_mul_eq_mul_integral (hφm.comp hW).aestronglyMeasurable
    (hψm.comp (measurable_pi_lambda _ hE)).aestronglyMeasurable]
  congr 1
  · have : (φ ∘ W) = {ω | W ω = k}.indicator (fun _ => (1 : ℂ)) := by
      funext ω
      by_cases h : W ω = k <;> simp [Set.indicator, h, hφ]
    rw [this, integral_indicator_const _ (hset k), measureReal_def, Complex.real_smul, mul_one]
  · rw [← charFun_map_partialSum hE hind hlaw k t, charFun_apply_real,
      integral_map (measurable_partialSum hE k).aemeasurable (by fun_prop)]
    congr 1
    funext ω
    simp [hψ, partialSum_apply]

/-- **Characteristic function of the exponential law**: `r/(r - it)`. -/
theorem charFun_expMeasure {r : ℝ} (hr : 0 < r) (t : ℝ) :
    charFun (expMeasure r) t = r / (r - t * I) := by
  rw [charFun_apply_real, expMeasure, gammaMeasure]
  change (∫ x : ℝ, exp (t * x * I)
      ∂volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal 1 r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal 1 r).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr _)]
  have hfun :
      (fun x : ℝ ↦ gammaPDFReal 1 r x • exp (t * x * I)) =
        Set.indicator (Set.Ici 0)
          (fun x : ℝ ↦ (r : ℂ) * exp ((t * I - r) * x)) := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [gammaPDFReal, if_pos hx]
      simp only [Set.indicator, Set.mem_Ici, if_pos hx]
      norm_num
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    · simp [gammaPDFReal, hx, Set.indicator]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_exp_mul_complex_Ioi (by simp [hr]) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have h1 : (t : ℂ) * I - r ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : (r : ℂ) - t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  field_simp
  ring

/-- The completed-private generating function over `ℂ`: `E[z^W] = 8z²/((5-z)(3-z))` for
`‖z‖ < 3`. -/
theorem wpmf_pgf_complex (z : ℂ) (hz : ‖z‖ < 3) :
    ∑' n : ℕ, (CompletedPrivateRenewal.wpmf n : ℂ) * z ^ n
      = 8 * z ^ 2 / ((5 - z) * (3 - z)) := by
  have hz3 : ‖z / 3‖ < 1 := by
    rw [norm_div, Complex.norm_ofNat]
    exact (div_lt_one (by norm_num)).mpr hz
  have hz5 : ‖z / 5‖ < 1 := by
    rw [norm_div, Complex.norm_ofNat]
    exact (div_lt_one (by norm_num)).mpr (lt_trans hz (by norm_num))
  have h3ne : (3 : ℂ) - z ≠ 0 := by
    intro h
    have : ‖z‖ = 3 := by
      have hz' : z = 3 := (sub_eq_zero.mp h).symm
      rw [hz']; simp
    linarith
  have h5ne : (5 : ℂ) - z ≠ 0 := by
    intro h
    have : ‖z‖ = 5 := by
      have hz' : z = 5 := (sub_eq_zero.mp h).symm
      rw [hz']; simp
    linarith
  have h3' : (1 : ℂ) - z / 3 ≠ 0 := by
    intro h; apply h3ne
    have := congrArg (fun w : ℂ => 3 * w) h
    simp only [mul_sub, mul_one, mul_zero] at this
    rw [← this]; ring
  have h5' : (1 : ℂ) - z / 5 ≠ 0 := by
    intro h; apply h5ne
    have := congrArg (fun w : ℂ => 5 * w) h
    simp only [mul_sub, mul_one, mul_zero] at this
    rw [← this]; ring
  have h3 : HasSum (fun m : ℕ => (4 / 3 : ℂ) * z ^ 2 * (z / 3) ^ m)
      ((4 / 3) * z ^ 2 * (1 - z / 3)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hz3).mul_left _
  have h5 : HasSum (fun m : ℕ => (4 / 5 : ℂ) * z ^ 2 * (z / 5) ^ m)
      ((4 / 5) * z ^ 2 * (1 - z / 5)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hz5).mul_left _
  have hshift : HasSum (fun m : ℕ => (CompletedPrivateRenewal.wpmf (m + 2) : ℂ) * z ^ (m + 2))
      ((4 / 3) * z ^ 2 * (1 - z / 3)⁻¹ - (4 / 5) * z ^ 2 * (1 - z / 5)⁻¹) := by
    refine (h3.sub h5).congr_fun fun m => ?_
    rw [CompletedPrivateRenewal.wpmf_add_two]
    push_cast
    field_simp
    ring
  have hfull : HasSum (fun n : ℕ => (CompletedPrivateRenewal.wpmf n : ℂ) * z ^ n)
      ((4 / 3) * z ^ 2 * (1 - z / 3)⁻¹ - (4 / 5) * z ^ 2 * (1 - z / 5)⁻¹) := by
    have h02 : ∑ i ∈ Finset.range 2, (CompletedPrivateRenewal.wpmf i : ℂ) * z ^ i = 0 := by
      simp [Finset.sum_range_succ, CompletedPrivateRenewal.wpmf_zero,
        CompletedPrivateRenewal.wpmf_one]
    refine (hasSum_nat_add_iff' (f := fun n : ℕ => (CompletedPrivateRenewal.wpmf n : ℂ) * z ^ n)
      2).mp ?_
    rw [h02, sub_zero]
    exact hshift
  rw [hfull.tsum_eq]
  field_simp
  ring

/-- The characteristic function of the independent two-stage completion law. -/
theorem charFun_independentExponentialCompletionLaw {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (t : ℝ) :
    charFun (independentExponentialCompletionLaw a b) t
      = a / (a - t * I) * (b / (b - t * I)) := by
  letI : IsProbabilityMeasure (expMeasure a) := isProbabilityMeasure_expMeasure ha
  letI : IsProbabilityMeasure (expMeasure b) := isProbabilityMeasure_expMeasure hb
  have h := charFun_map_add_prod_eq_mul (μ := expMeasure a) (ν := expMeasure b)
  rw [independentExponentialCompletionLaw, independentExponentialStageMeasure]
  change charFun (((expMeasure a).prod (expMeasure b)).map (fun p => p.1 + p.2)) t = _
  rw [h, Pi.mul_apply, charFun_expMeasure ha, charFun_expMeasure hb]

/-- The norm of `λ/(λ - it)` is at most one. -/
theorem norm_exp_symbol_le {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    ‖(lam : ℂ) / (lam - t * I)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hlam.le]
  have hre : ((lam : ℂ) - t * I).re = lam := by simp
  have hle : lam ≤ ‖(lam : ℂ) - t * I‖ := by
    calc lam = |((lam : ℂ) - t * I).re| := by rw [hre, abs_of_pos hlam]
      _ ≤ ‖(lam : ℂ) - t * I‖ := Complex.abs_re_le_norm _
  exact div_le_one_of_le₀ hle (norm_nonneg _)

/-- **The boxed completion law.**  For a rate-`λ` clock family (i.i.d. `Exp(λ)` holding times)
independent of the completed-private interarrival count `W`, the random-sum completion time
`∑_{i < W} E i` has exactly the law of `Exp(4λ/5) + Exp(2λ/3)` with independent summands. -/
theorem map_randomSum_eq_independentExponentialCompletionLaw [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) {W : Ω → ℕ} {E : ℕ → Ω → ℝ}
    (hW : Measurable W) (hE : ∀ i, Measurable (E i)) (hind : iIndepFun E μ)
    (hlaw : ∀ i, μ.map (E i) = expMeasure lam) (hWE : W ⟂ᵢ[μ] (fun ω i => E i ω))
    (hWlaw : ∀ n, (μ {ω | W ω = n}).toReal = CompletedPrivateRenewal.wpmf n) :
    μ.map (randomSum W E) = independentExponentialCompletionLaw (4 * lam / 5) (2 * lam / 3) := by
  haveI : IsProbabilityMeasure (μ.map (randomSum W E)) :=
    Measure.isProbabilityMeasure_map (measurable_randomSum hW hE).aemeasurable
  haveI : IsProbabilityMeasure
      (independentExponentialCompletionLaw (4 * lam / 5) (2 * lam / 3)) := by
    haveI := isProbabilityMeasure_independentExponentialStageMeasure
      (firstRate := 4 * lam / 5) (secondRate := 2 * lam / 3) (by positivity) (by positivity)
    unfold independentExponentialCompletionLaw
    exact Measure.isProbabilityMeasure_map (measurable_fst.add measurable_snd).aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_randomSum hW hE hind hlaw hWE t, charFun_expMeasure hlam,
    charFun_independentExponentialCompletionLaw (by positivity) (by positivity)]
  simp_rw [hWlaw]
  rw [wpmf_pgf_complex _ (lt_of_le_of_lt (norm_exp_symbol_le hlam t) (by norm_num))]
  have hne : ∀ c : ℝ, 0 < c → (c : ℂ) - t * I ≠ 0 := by
    intro c hc h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h1 := hne lam hlam
  have h2 := hne (4 * lam / 5) (by positivity)
  have h3 := hne (2 * lam / 3) (by positivity)
  have h5 : (5 : ℂ) - lam / (lam - t * I) ≠ 0 := by
    intro h
    have : ‖(lam : ℂ) / (lam - t * I)‖ = 5 := by
      rw [(sub_eq_zero.mp h).symm]; simp
    linarith [norm_exp_symbol_le hlam t]
  have h4 : (3 : ℂ) - lam / (lam - t * I) ≠ 0 := by
    intro h
    have : ‖(lam : ℂ) / (lam - t * I)‖ = 3 := by
      rw [(sub_eq_zero.mp h).symm]; simp
    linarith [norm_exp_symbol_le hlam t]
  push_cast
  field_simp
  ring

/-- **`thm:renewal-continuous-completion`** for the random-sum completion time: the boxed law,
the boxed Laplace transform `8λ²/((4λ+5s)(2λ+3s))`, and the boxed mean `11/(4λ)` with physical
intensity `4λ/11`. -/
theorem renewal_continuous_completion [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) {W : Ω → ℕ} {E : ℕ → Ω → ℝ}
    (hW : Measurable W) (hE : ∀ i, Measurable (E i)) (hind : iIndepFun E μ)
    (hlaw : ∀ i, μ.map (E i) = expMeasure lam) (hWE : W ⟂ᵢ[μ] (fun ω i => E i ω))
    (hWlaw : ∀ n, (μ {ω | W ω = n}).toReal = CompletedPrivateRenewal.wpmf n) :
    μ.map (randomSum W E) = independentExponentialCompletionLaw (4 * lam / 5) (2 * lam / 3) ∧
      (∀ s : ℝ, 0 ≤ s → ∫ ω, Real.exp (-(s * randomSum W E ω)) ∂μ
        = 8 * lam ^ 2 / ((4 * lam + 5 * s) * (2 * lam + 3 * s))) ∧
      (∫ ω, randomSum W E ω ∂μ) = 11 / (4 * lam) ∧
      (∫ ω, randomSum W E ω ∂μ)⁻¹ = 4 * lam / 11 := by
  have hmap := map_randomSum_eq_independentExponentialCompletionLaw hlam hW hE hind hlaw hWE hWlaw
  have hT := measurable_randomSum hW hE
  have hstage : Measurable exponentialCompletionTime := measurable_fst.add measurable_snd
  have hpush : ∀ f : ℝ → ℝ, Measurable f →
      ∫ ω, f (randomSum W E ω) ∂μ
        = ∫ ω, f (exponentialCompletionTime ω)
            ∂independentExponentialStageMeasure (4 * lam / 5) (2 * lam / 3) := by
    intro f hf
    rw [← integral_map hT.aemeasurable hf.aestronglyMeasurable, hmap,
      independentExponentialCompletionLaw,
      integral_map hstage.aemeasurable hf.aestronglyMeasurable]
  have hmean := hpush id measurable_id
  simp only [id] at hmean
  refine ⟨hmap, fun s hs => ?_, ?_, ?_⟩
  · rw [hpush (fun x => Real.exp (-(s * x))) (by fun_prop)]
    exact renewalCompletionTime_laplace lam s hlam hs
  · rw [hmean]
    exact (renewalCompletionTime_mean_and_intensity lam hlam).1
  · rw [hmean]
    exact (renewalCompletionTime_mean_and_intensity lam hlam).2

end RandomSum
end NCG
