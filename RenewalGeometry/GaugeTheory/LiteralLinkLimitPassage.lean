/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LiteralLinkLimitFourier
import RenewalGeometry.Analysis.LpDualityWeakCompactness

/-!
# Weak–strong passage for grid pairings on the space-time cylinder
  (infrastructure for `thm:main-literal-link-compactness`; emergent-spacetime manuscript)

Space-time interpolants `field u (t, x) = 𝓘_h u(t)(x)` on the cylinder `(0,T] × 𝕋³`
(`GridAubinLions.cylMeasure`) of time-dependent grid arrays.

* `norm_integral_mul_le_L2`: Cauchy–Schwarz for complex `L²` functions.
* `WeakL2`: weak `L²` convergence tested against complex `L²` functions;
  `weakL2_of_strong`, `exists_subseq_weakL2` (weak sequential compactness of bounded families,
  from `LpDuality.exists_subseq_tendsto_weak_family_vec`), and `tendsto_integral_strong_weak`
  (strong × weak × bounded weight).
* `IsL2Grid`: time-measurable grid arrays with `∫₀ᵀ ‖u(t)‖_h² < ∞`; `memLp_field_of_isL2Grid`,
  `integral_norm_field_sq` (Parseval–Tonelli `‖field u‖²_{L²} = ∫₀ᵀ ‖u(t)‖_h²`).
* `integral_pairing_eq_field` (odd grids): `∫₀ᵀ χ(t) h³ Σ_x u g = ∫_cyl χ · field u · field g`.
* `tendsto_pairing_modChar`: **the weak–strong passage for tested grid products**: if
  `field u_m → U` strongly with `∫₀ᵀ Σ_i ‖D_i⁺u_m‖_h²` bounded, and `field g_m ⇀ G` weakly with
  bounded `L²` norms, then for every Fourier mode `e_k` and bounded weight `χ(t)`,
  `∫₀ᵀ χ(t) h³ Σ_x u_m(t,x) e_k(x) g_m(t,x) dt → ∫_cyl χ e_k U G` along odd grids `N_m → ∞`.
-/

open MeasureTheory Filter Topology UnitAddTorus
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.LiteralLinkLimit

open PeriodicGridSobolev LatticeTorusPlancherel GridAubinLions

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### Abstract `L²` facts -/

section L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integral_norm_mul_le_L2 {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ a, ‖f a‖ * ‖g a‖ ∂μ ≤ Real.sqrt (∫ a, ‖f a‖ ^ 2 ∂μ) * Real.sqrt (∫ a, ‖g a‖ ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h1 : MemLp (fun a => ‖f a‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]; exact hf.norm
  have h2 : MemLp (fun a => ‖g a‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]; exact hg.norm
  have := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun _ => norm_nonneg _)
    (ae_of_all _ fun _ => norm_nonneg _) h1 h2
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert this using 3 <;> norm_num

/-- Cauchy–Schwarz for complex `L²` functions. -/
theorem norm_integral_mul_le_L2 {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ a, f a * g a ∂μ‖ ≤ Real.sqrt (∫ a, ‖f a‖ ^ 2 ∂μ) * Real.sqrt (∫ a, ‖g a‖ ^ 2 ∂μ) := by
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [norm_mul]
  exact integral_norm_mul_le_L2 hf hg

/-- Weak `L²` convergence, tested against complex `L²` functions. -/
def WeakL2 (μ : Measure α) (f : ℕ → α → ℂ) (F : α → ℂ) : Prop :=
  ∀ ψ : α → ℂ, MemLp ψ 2 μ →
    Tendsto (fun m => ∫ a, ψ a * f m a ∂μ) atTop (𝓝 (∫ a, ψ a * F a ∂μ))

theorem WeakL2.comp {f : ℕ → α → ℂ} {F : α → ℂ} (h : WeakL2 μ f F) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : WeakL2 μ (fun m => f (φ m)) F := fun ψ hψ =>
  (h ψ hψ).comp hφ.tendsto_atTop

theorem integral_norm_sq_nonneg (f : α → ℂ) : 0 ≤ ∫ a, ‖f a‖ ^ 2 ∂μ :=
  integral_nonneg fun _ => by positivity

theorem integral_norm_sub_sq_le {f g h : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hh : MemLp h 2 μ) :
    ∫ a, ‖f a - h a‖ ^ 2 ∂μ ≤ 2 * ∫ a, ‖f a - g a‖ ^ 2 ∂μ + 2 * ∫ a, ‖g a - h a‖ ^ 2 ∂μ := by
  have i1 : Integrable (fun a => ‖f a - g a‖ ^ 2) μ := (hf.sub hg).norm.integrable_sq
  have i2 : Integrable (fun a => ‖g a - h a‖ ^ 2) μ := (hg.sub hh).norm.integrable_sq
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity)
    ((i1.const_mul 2).add (i2.const_mul 2)) (ae_of_all _ fun a => ?_)
  have e : f a - h a = (f a - g a) + (g a - h a) := by ring
  have h1 := norm_add_le (f a - g a) (g a - h a)
  rw [← e] at h1
  have h2 := mul_self_le_mul_self (norm_nonneg _) h1
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖f a - g a‖ - ‖g a - h a‖)]

/-- Strong `L²` convergence implies weak convergence. -/
theorem weakL2_of_strong {f : ℕ → α → ℂ} {F : α → ℂ} (hf : ∀ m, MemLp (f m) 2 μ)
    (hF : MemLp F 2 μ) (h : Tendsto (fun m => ∫ a, ‖f m a - F a‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    WeakL2 μ f F := by
  intro ψ hψ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ m, ‖∫ a, ψ a * f m a ∂μ - ∫ a, ψ a * F a ∂μ‖ ≤
      Real.sqrt (∫ a, ‖ψ a‖ ^ 2 ∂μ) * Real.sqrt (∫ a, ‖f m a - F a‖ ^ 2 ∂μ) := by
    intro m
    have i1 : Integrable (fun a => ψ a * f m a) μ := hψ.integrable_mul (hf m)
    have i2 : Integrable (fun a => ψ a * F a) μ := hψ.integrable_mul hF
    rw [← integral_sub i1 i2]
    simp only [← mul_sub]
    exact norm_integral_mul_le_L2 hψ ((hf m).sub hF)
  have hz : Tendsto (fun m => Real.sqrt (∫ a, ‖ψ a‖ ^ 2 ∂μ) *
      Real.sqrt (∫ a, ‖f m a - F a‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h
    simpa using this.const_mul (Real.sqrt (∫ a, ‖ψ a‖ ^ 2 ∂μ))
  exact squeeze_zero (fun _ => norm_nonneg _) hb hz

/-- **Strong × weak × bounded weight.**  If `f_m → F` strongly and `g_m ⇀ G` weakly in `L²`,
with `‖g_m‖²_{L²} ≤ B`, then `∫ ψ f_m g_m → ∫ ψ F G` for every bounded measurable `ψ`. -/
theorem tendsto_integral_strong_weak [IsFiniteMeasure μ] {ψ : α → ℂ}
    (hψm : AEStronglyMeasurable ψ μ) {C : ℝ} (hC : 0 ≤ C) (hψ : ∀ a, ‖ψ a‖ ≤ C)
    {f g : ℕ → α → ℂ} {F G : α → ℂ} (hf : ∀ m, MemLp (f m) 2 μ) (hF : MemLp F 2 μ)
    (hfF : Tendsto (fun m => ∫ a, ‖f m a - F a‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hg : ∀ m, MemLp (g m) 2 μ) (hgw : WeakL2 μ g G) {B : ℝ}
    (hgB : ∀ m, ∫ a, ‖g m a‖ ^ 2 ∂μ ≤ B) :
    Tendsto (fun m => ∫ a, ψ a * f m a * g m a ∂μ) atTop (𝓝 (∫ a, ψ a * F a * G a ∂μ)) := by
  have hψF : MemLp (fun a => ψ a * F a) 2 μ := by
    refine MemLp.of_le (hF.const_mul C) (hψm.mul hF.aestronglyMeasurable) ?_
    · exact ae_of_all _ fun a => by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (hψ a) (norm_nonneg _)
  have hψf : ∀ m, MemLp (fun a => ψ a * (f m a - F a)) 2 μ := by
    intro m
    refine MemLp.of_le (((hf m).sub hF).const_mul C)
      (hψm.mul ((hf m).sub hF).aestronglyMeasurable) ?_
    exact ae_of_all _ fun a => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hψ a) (norm_nonneg _)
  have hsplit : ∀ m, ∫ a, ψ a * f m a * g m a ∂μ =
      ∫ a, (ψ a * (f m a - F a)) * g m a ∂μ + ∫ a, (ψ a * F a) * g m a ∂μ := by
    intro m
    have i1 : Integrable (fun a => ψ a * (f m a - F a) * g m a) μ := (hψf m).integrable_mul (hg m)
    have i2 : Integrable (fun a => ψ a * F a * g m a) μ := hψF.integrable_mul (hg m)
    rw [← integral_add i1 i2]
    congr 1; funext a; ring
  simp only [hsplit]
  have h2 := hgw _ hψF
  have h1 : Tendsto (fun m => ∫ a, (ψ a * (f m a - F a)) * g m a ∂μ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ m, ‖∫ a, (ψ a * (f m a - F a)) * g m a ∂μ‖ ≤
        C * Real.sqrt (∫ a, ‖f m a - F a‖ ^ 2 ∂μ) * Real.sqrt B := by
      intro m
      refine (norm_integral_mul_le_L2 (hψf m) (hg m)).trans ?_
      have hB : 0 ≤ B := (integral_norm_sq_nonneg _).trans (hgB m)
      have e1 : Real.sqrt (∫ a, ‖ψ a * (f m a - F a)‖ ^ 2 ∂μ) ≤
          C * Real.sqrt (∫ a, ‖f m a - F a‖ ^ 2 ∂μ) := by
        rw [← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg _)]
        refine Real.sqrt_le_sqrt ?_
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity)
          (((hf m).sub hF).norm.integrable_sq.const_mul _) (ae_of_all _ fun a => ?_)
        show ‖ψ a * (f m a - F a)‖ ^ 2 ≤ C ^ 2 * ‖f m a - F a‖ ^ 2
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hψ a) 2)
          (sq_nonneg _)
      have e2 : Real.sqrt (∫ a, ‖g m a‖ ^ 2 ∂μ) ≤ Real.sqrt B := Real.sqrt_le_sqrt (hgB m)
      calc _ ≤ C * Real.sqrt (∫ a, ‖f m a - F a‖ ^ 2 ∂μ) * Real.sqrt (∫ a, ‖g m a‖ ^ 2 ∂μ) :=
            mul_le_mul_of_nonneg_right e1 (Real.sqrt_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
    have hz : Tendsto (fun m => C * Real.sqrt (∫ a, ‖f m a - F a‖ ^ 2 ∂μ) * Real.sqrt B)
        atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hfF
      simpa using (this.const_mul C).mul_const (Real.sqrt B)
    exact squeeze_zero (fun _ => norm_nonneg _) hb hz
  simpa using h1.add h2

/-- `∫ ψ f = ∫ Re ψ • f + i ∫ Im ψ • f`. -/
theorem integral_mul_eq_re_im {ψ f : α → ℂ} (hψ : MemLp ψ 2 μ) (hf : MemLp f 2 μ) :
    ∫ a, ψ a * f a ∂μ = ∫ a, (ψ a).re • f a ∂μ + Complex.I * ∫ a, (ψ a).im • f a ∂μ := by
  have hre : Integrable (fun a => (ψ a).re • f a) μ := by
    have := (hψ.re.norm).integrable_mul (hf.norm)
    refine Integrable.mono' this (hψ.re.aestronglyMeasurable.smul hf.aestronglyMeasurable)
      (ae_of_all _ fun a => ?_)
    rw [norm_smul]; rfl
  have him : Integrable (fun a => (ψ a).im • f a) μ := by
    have := (hψ.im.norm).integrable_mul (hf.norm)
    refine Integrable.mono' this (hψ.im.aestronglyMeasurable.smul hf.aestronglyMeasurable)
      (ae_of_all _ fun a => ?_)
    rw [norm_smul]; rfl
  rw [← integral_const_mul, ← integral_add hre (him.const_mul _)]
  congr 1; funext a
  conv_lhs => rw [← Complex.re_add_im (ψ a)]
  simp only [Complex.real_smul]
  ring

/-- **Weak sequential compactness** of finite families of `L²`-bounded complex sequences (finite
measure, countably generated σ-algebra), in the sense of `WeakL2`. -/
theorem exists_subseq_weakL2 [IsFiniteMeasure μ] [MeasurableSpace.CountablyGenerated α]
    {ι : Type*} [Fintype ι] (f : ι → ℕ → α → ℂ) (hf : ∀ i m, MemLp (f i m) 2 μ) {B : ℝ}
    (hB : ∀ i m, ∫ a, ‖f i m a‖ ^ 2 ∂μ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ι → α → ℂ, ∀ i,
      MemLp (F i) 2 μ ∧ WeakL2 μ (fun m => f i (φ m)) (F i) := by
  have hbd : ∀ i m, eLpNorm (f i m) 2 μ ≤ ENNReal.ofReal (Real.sqrt B) := by
    intro i m
    have h1 : ((eLpNorm (f i m) 2 μ).toReal) ^ 2 = ∫ a, ‖f i m a‖ ^ 2 ∂μ := by
      rw [← Lp.norm_toLp (f i m) (hf i m), norm_toLp_sq]
    rw [← ENNReal.ofReal_toReal (hf i m).eLpNorm_ne_top]
    refine ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le ?_)
    rw [h1]; exact hB i m
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  obtain ⟨φ, hφ, F, hF⟩ := LpDuality.exists_subseq_tendsto_weak_family_vec (μ := μ) (p := 2)
    (q := 2) (V := ℂ) ENNReal.ofNat_ne_top ENNReal.ofNat_ne_top f hf ENNReal.ofReal_ne_top hbd
  refine ⟨φ, hφ, F, fun i => ⟨(hF i).1, fun ψ hψ => ?_⟩⟩
  have h1 := (hF i).2 _ (hψ.re)
  have h2 := (hF i).2 _ (hψ.im)
  have e : ∀ m, ∫ a, ψ a * f i (φ m) a ∂μ =
      ∫ a, (ψ a).re • f i (φ m) a ∂μ + Complex.I * ∫ a, (ψ a).im • f i (φ m) a ∂μ :=
    fun m => integral_mul_eq_re_im hψ (hf i (φ m))
  simp only [e]
  rw [integral_mul_eq_re_im hψ (hF i).1]
  exact h1.add (h2.const_mul _)

end L2

/-! ### Space-time interpolants of `L²` grid arrays -/

section Grid

variable {N : ℕ} [NeZero N] {T : ℝ}

/-- A time-dependent grid array whose values are measurable in time on `(0,T]` and whose grid
`L²` norm is integrable: `u ∈ L²((0,T]; L²_h)`. -/
def IsL2Grid (T : ℝ) (u : ℝ → Grid N → ℂ) : Prop :=
  (∀ x, AEStronglyMeasurable (fun t => u t x) (volume.restrict (Set.Ioc 0 T))) ∧
    IntegrableOn (fun t => gridNormSq (u t)) (Set.Ioc 0 T)

theorem aestronglyMeasurable_dft {u : ℝ → Grid N → ℂ}
    (hu : ∀ x, AEStronglyMeasurable (fun t => u t x) (volume.restrict (Set.Ioc 0 T)))
    (k : Grid N) : AEStronglyMeasurable (fun t => dft (u t) k) (volume.restrict (Set.Ioc 0 T)) := by
  simp only [dft_eq_sum]
  exact Finset.aestronglyMeasurable_fun_sum _ fun x _ => (hu x).const_mul _

theorem aestronglyMeasurable_field {u : ℝ → Grid N → ℂ}
    (hu : ∀ x, AEStronglyMeasurable (fun t => u t x) (volume.restrict (Set.Ioc 0 T))) :
    AEStronglyMeasurable (field u) (cylMeasure T) := by
  have : field u = fun p => ∑ k, dft (u p.1) k * mFourier (freqVec k) p.2 :=
    funext (field_eq_sum u)
  rw [this]
  refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
  refine AEStronglyMeasurable.mul ?_ ?_
  · exact (aestronglyMeasurable_dft hu k).comp_fst
  · exact ((mFourier (freqVec k)).continuous.comp continuous_snd).aestronglyMeasurable

theorem integrable_norm_interp_sq (u : Grid N → ℂ) :
    Integrable (fun x : UnitAddTorus (Fin 3) => ‖interp u x‖ ^ 2) volume :=
  ((interp u).continuous.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_norm_field_sq {u : ℝ → Grid N → ℂ} (hu : IsL2Grid T u) :
    Integrable (fun p => ‖field u p‖ ^ 2) (cylMeasure T) := by
  have hm : AEStronglyMeasurable (fun p => ‖field u p‖ ^ 2) (cylMeasure T) :=
    (aestronglyMeasurable_field hu.1).norm.pow 2
  rw [cylMeasure, integrable_prod_iff hm]
  refine ⟨ae_of_all _ fun t => integrable_norm_interp_sq (u t), ?_⟩
  have e : ∀ t, ∫ x, ‖‖field u (t, x)‖ ^ 2‖ = gridNormSq (u t) := by
    intro t
    simp only [norm_pow, norm_norm]
    exact integral_norm_interp_sq (u t)
  simp only [e]
  exact hu.2

/-- **Parseval–Tonelli**: `‖field u‖²_{L²((0,T] × 𝕋³)} = ∫₀ᵀ ‖u(t)‖_h² dt`. -/
theorem integral_norm_field_sq {u : ℝ → Grid N → ℂ} (hu : IsL2Grid T u) :
    ∫ p, ‖field u p‖ ^ 2 ∂cylMeasure T = ∫ t in Set.Ioc 0 T, gridNormSq (u t) := by
  rw [cylMeasure, integral_prod _ (integrable_norm_field_sq hu)]
  exact integral_congr_ae (ae_of_all _ fun t => integral_norm_interp_sq (u t))

theorem memLp_field_of_isL2Grid {u : ℝ → Grid N → ℂ} (hu : IsL2Grid T u) :
    MemLp (field u) 2 (cylMeasure T) :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_field hu.1)).2
    (integrable_norm_field_sq hu)

theorem interp_sub (u v : Grid N → ℂ) : interp (u - v) = interp u - interp v := by
  unfold interp
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext x
  simp only [dft_sub, ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul, sub_mul]

theorem field_sub (u v : ℝ → Grid N → ℂ) :
    field (fun t => u t - v t) = fun p => field u p - field v p := by
  funext p
  simp only [field, interp_sub, ContinuousMap.sub_apply]

theorem IsL2Grid.sub {u v : ℝ → Grid N → ℂ} (hu : IsL2Grid T u) (hv : IsL2Grid T v) :
    IsL2Grid T (fun t => u t - v t) := by
  refine ⟨fun x => (hu.1 x).sub (hv.1 x), ?_⟩
  refine Integrable.mono' ((hu.2.const_mul 2).add (hv.2.const_mul 2)) ?_ (ae_of_all _ fun t => ?_)
  · have : (fun t => gridNormSq (u t - v t)) = fun t =>
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖u t x - v t x‖ ^ 2 := rfl
    rw [this]
    refine AEStronglyMeasurable.const_mul ?_ _
    exact Finset.aestronglyMeasurable_fun_sum _ fun x _ => ((hu.1 x).sub (hv.1 x)).norm.pow 2
  · rw [Real.norm_of_nonneg (gridNormSq_nonneg _)]
    show gridNormSq (u t - v t) ≤ 2 * gridNormSq (u t) + 2 * gridNormSq (v t)
    have hpt : ∀ x, ‖u t x - v t x‖ ^ 2 ≤ 2 * ‖u t x‖ ^ 2 + 2 * ‖v t x‖ ^ 2 := fun x => by
      have h1 := norm_sub_le (u t x) (v t x)
      have h2 := mul_self_le_mul_self (norm_nonneg _) h1
      nlinarith [sq_nonneg (‖u t x‖ - ‖v t x‖)]
    simp only [gridNormSq, Pi.sub_apply]
    calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖u t x - v t x‖ ^ 2
        ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, (2 * ‖u t x‖ ^ 2 + 2 * ‖v t x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpt x) (by positivity)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- The tested time–space pairing of two grid arrays equals the cylinder integral of the
interpolants (odd grid, bilinear Parseval + Fubini). -/
theorem integral_pairing_eq_field (hN : Odd N) {u g : ℝ → Grid N → ℂ} (hu : IsL2Grid T u)
    (hg : IsL2Grid T g) {χ : ℝ → ℂ} (hχm : AEStronglyMeasurable χ (volume.restrict (Set.Ioc 0 T)))
    {C : ℝ} (hχ : ∀ t, ‖χ t‖ ≤ C) :
    ∫ t in Set.Ioc 0 T, χ t * (((N : ℂ) ^ 3)⁻¹ * ∑ x, u t x * g t x) =
      ∫ p, χ p.1 * field u p * field g p ∂cylMeasure T := by
  have hint : Integrable (fun p => χ p.1 * field u p * field g p) (cylMeasure T) := by
    have h := (memLp_field_of_isL2Grid hu).integrable_mul (memLp_field_of_isL2Grid hg)
    have hb : Integrable (fun p => χ p.1 * (field u p * field g p)) (cylMeasure T) :=
      h.bdd_mul (c := C) hχm.comp_fst (ae_of_all _ fun p => hχ p.1)
    exact hb.congr (ae_of_all _ fun p => by simp only [Pi.mul_apply]; ring)
  rw [cylMeasure, integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [field]
  have e : ∀ x : UnitAddTorus (Fin 3), χ t * interp (u t) x * interp (g t) x =
      χ t * (interp (u t) x * interp (g t) x) := fun x => by ring
  simp only [e]
  rw [integral_const_mul, integral_interp_mul hN]

end Grid

/-! ### The weak–strong passage for tested grid products -/

section Passage

variable {Nm : ℕ → ℕ} [∀ m, NeZero (Nm m)] {T : ℝ}

theorem IsL2Grid.mul_modChar {N : ℕ} [NeZero N] {u : ℝ → Grid N → ℂ} (hu : IsL2Grid T u)
    (k : Fin 3 → ℤ) : IsL2Grid T (fun t x => u t x * modChar k x) := by
  refine ⟨fun x => (hu.1 x).mul_const _, ?_⟩
  have e : (fun t => gridNormSq (fun x => u t x * modChar k x)) = fun t => gridNormSq (u t) := by
    funext t
    simp only [gridNormSq, norm_mul, norm_modChar, mul_one]
  rw [e]; exact hu.2

/-- The squared `L²` distance between the modulated interpolant and the modulated limit. -/
theorem integral_norm_field_mul_modChar_sub_le {N : ℕ} [NeZero N] {u : ℝ → Grid N → ℂ}
    (hu : IsL2Grid T u) {k : Fin 3 → ℤ} {M : ℕ} (hM : ∀ i, |k i| ≤ M) (hMN : 2 * M < N)
    (hcf : IntegrableOn (fun t => coordForm (u t)) (Set.Ioc 0 T)) :
    ∫ p, ‖field (fun t x => u t x * modChar k x) p - mFourier k p.2 * field u p‖ ^ 2
        ∂cylMeasure T ≤
      (∫ t in Set.Ioc 0 T, coordForm (u t)) / ((N : ℝ) - 2 * M) ^ 2 := by
  have hD : 0 < ((N : ℝ) - 2 * M) ^ 2 := by
    have : ((2 * M : ℕ) : ℝ) < N := by exact_mod_cast hMN
    push_cast at this
    have : 0 < (N : ℝ) - 2 * M := by linarith
    positivity
  have hm1 := aestronglyMeasurable_field (hu.mul_modChar k).1
  have hm2 : AEStronglyMeasurable (fun p : ℝ × UnitAddTorus (Fin 3) => mFourier k p.2 * field u p)
      (cylMeasure T) :=
    ((mFourier k).continuous.comp continuous_snd).aestronglyMeasurable.mul
      (aestronglyMeasurable_field hu.1)
  have hmeas : AEStronglyMeasurable (fun p : ℝ × UnitAddTorus (Fin 3) =>
      ‖field (fun t x => u t x * modChar k x) p - mFourier k p.2 * field u p‖ ^ 2) (cylMeasure T) :=
    (hm1.sub hm2).norm.pow 2
  have hpt : ∀ t, ∫ x, ‖field (fun t x => u t x * modChar k x) (t, x) -
      mFourier k (t, x).2 * field u (t, x)‖ ^ 2 ≤ coordForm (u t) / ((N : ℝ) - 2 * M) ^ 2 :=
    fun t => integral_norm_interp_mul_modChar_sub_le (u t) hM hMN
  have hint : Integrable (fun p : ℝ × UnitAddTorus (Fin 3) =>
      ‖field (fun t x => u t x * modChar k x) p - mFourier k p.2 * field u p‖ ^ 2)
      (cylMeasure T) := by
    rw [cylMeasure, integrable_prod_iff hmeas]
    refine ⟨ae_of_all _ fun t => ?_, ?_⟩
    · have : Continuous fun x : UnitAddTorus (Fin 3) =>
          ‖field (fun t x => u t x * modChar k x) (t, x) - mFourier k (t, x).2 * field u (t, x)‖ ^ 2 := by
        simp only [field]; fun_prop
      exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · refine Integrable.mono' (hcf.div_const (((N : ℝ) - 2 * M) ^ 2)) ?_ (ae_of_all _ fun t => ?_)
      · exact (hmeas.norm.integral_prod_right' (μ := volume.restrict (Set.Ioc 0 T))
          (ν := volume))
      · rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        simp only [norm_pow, norm_norm]
        exact hpt t
  rw [cylMeasure, integral_prod _ hint, ← integral_div]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => integral_nonneg fun _ => by positivity)
    (hcf.div_const _) (ae_of_all _ hpt)

/-- A bound `|k_i| ≤ M` for a Fourier mode. -/
def modeBound (k : Fin 3 → ℤ) : ℕ := ∑ i, (k i).natAbs

theorem abs_le_modeBound (k : Fin 3 → ℤ) (i : Fin 3) : |k i| ≤ modeBound k := by
  have : (k i).natAbs ≤ modeBound k := Finset.single_le_sum (f := fun i => (k i).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [Int.abs_eq_natAbs]; exact_mod_cast this

theorem memLp_mFourier_mul {U : ℝ × UnitAddTorus (Fin 3) → ℂ} (hU : MemLp U 2 (cylMeasure T))
    (k : Fin 3 → ℤ) :
    MemLp (fun p : ℝ × UnitAddTorus (Fin 3) => mFourier k p.2 * U p) 2 (cylMeasure T) := by
  refine MemLp.of_le hU (((mFourier k).continuous.comp continuous_snd).aestronglyMeasurable.mul
    hU.aestronglyMeasurable) (ae_of_all _ fun p => ?_)
  rw [norm_mul, norm_mFourier_apply, one_mul]

/-- The modulated interpolants converge strongly to the modulated limit. -/
theorem tendsto_field_mul_modChar (hN : Tendsto Nm atTop atTop)
    (u : ∀ m, ℝ → Grid (Nm m) → ℂ) (hu : ∀ m, IsL2Grid T (u m))
    {U : ℝ × UnitAddTorus (Fin 3) → ℂ} (hU : MemLp U 2 (cylMeasure T))
    (huU : Tendsto (fun m => ∫ p, ‖field (u m) p - U p‖ ^ 2 ∂cylMeasure T) atTop (𝓝 0))
    {B : ℝ} (hcf : ∀ m, IntegrableOn (fun t => coordForm (u m t)) (Set.Ioc 0 T))
    (hcfB : ∀ m, ∫ t in Set.Ioc 0 T, coordForm (u m t) ≤ B) (k : Fin 3 → ℤ) :
    Tendsto (fun m => ∫ p, ‖field (fun t x => u m t x * modChar k x) p - mFourier k p.2 * U p‖ ^ 2
      ∂cylMeasure T) atTop (𝓝 0) := by
  have hD : Tendsto (fun m => ((Nm m : ℝ) - 2 * modeBound k) ^ 2) atTop atTop := by
    have h1 : Tendsto (fun m => (Nm m : ℝ) - 2 * modeBound k) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hN)
    exact (tendsto_pow_atTop two_ne_zero).comp h1
  have hB0 : Tendsto (fun m => 2 * (B / ((Nm m : ℝ) - 2 * modeBound k) ^ 2) +
      2 * ∫ p, ‖field (u m) p - U p‖ ^ 2 ∂cylMeasure T) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := B)).div_atTop hD).const_mul 2
    simpa using this.add (huU.const_mul 2)
  refine squeeze_zero' (Eventually.of_forall fun m => integral_nonneg fun _ => by positivity)
    ?_ hB0
  filter_upwards [hN.eventually_gt_atTop (2 * modeBound k)] with m hm
  have hfu := integral_norm_field_mul_modChar_sub_le (hu m) (abs_le_modeBound k) hm (hcf m)
  have hb : MemLp (fun p : ℝ × UnitAddTorus (Fin 3) => mFourier k p.2 * field (u m) p) 2
      (cylMeasure T) := memLp_mFourier_mul (memLp_field_of_isL2Grid (hu m)) k
  have htri := integral_norm_sub_sq_le (memLp_field_of_isL2Grid ((hu m).mul_modChar k)) hb
    (memLp_mFourier_mul hU k)
  have e2 : ∫ p, ‖mFourier k p.2 * field (u m) p - mFourier k p.2 * U p‖ ^ 2 ∂cylMeasure T =
      ∫ p, ‖field (u m) p - U p‖ ^ 2 ∂cylMeasure T := by
    congr 1; funext p
    rw [← mul_sub, norm_mul, norm_mFourier_apply, one_mul]
  rw [e2] at htri
  have hDm : 0 < ((Nm m : ℝ) - 2 * modeBound k) ^ 2 := by
    have h1 : ((2 * modeBound k : ℕ) : ℝ) < Nm m := by exact_mod_cast hm
    push_cast at h1
    have : 0 < (Nm m : ℝ) - 2 * modeBound k := by linarith
    positivity
  have h3 : (∫ t in Set.Ioc 0 T, coordForm (u m t)) / ((Nm m : ℝ) - 2 * modeBound k) ^ 2 ≤
      B / ((Nm m : ℝ) - 2 * modeBound k) ^ 2 := div_le_div_of_nonneg_right (hcfB m) hDm.le
  calc _ ≤ _ := htri
    _ ≤ _ := by gcongr; exact hfu.trans h3

set_option maxHeartbeats 1000000 in
/-- **Weak–strong passage for tested grid products.**  Along odd grids `N_m → ∞`, let `u_m` be
grid arrays whose interpolants converge strongly in `L²((0,T] × 𝕋³)` to `U`, with
`∫₀ᵀ Σ_i ‖D_i⁺u_m‖_h² ≤ B`, and `g_m` grid arrays whose interpolants converge weakly to `G`, with
`∫₀ᵀ ‖g_m‖_h² ≤ B`.  Then for every Fourier mode `k` and every bounded measurable weight `χ`,
`∫₀ᵀ χ(t) h³ Σ_x u_m(t,x) e_k(x/N_m) g_m(t,x) dt → ∫_cyl χ(t) e_k(x) U G`. -/
theorem tendsto_pairing_modChar (hodd : ∀ m, Odd (Nm m)) (hN : Tendsto Nm atTop atTop)
    (u g : ∀ m, ℝ → Grid (Nm m) → ℂ) (hu : ∀ m, IsL2Grid T (u m)) (hg : ∀ m, IsL2Grid T (g m))
    {U G : ℝ × UnitAddTorus (Fin 3) → ℂ} (hU : MemLp U 2 (cylMeasure T))
    (huU : Tendsto (fun m => ∫ p, ‖field (u m) p - U p‖ ^ 2 ∂cylMeasure T) atTop (𝓝 0))
    {B : ℝ} (hcf : ∀ m, IntegrableOn (fun t => coordForm (u m t)) (Set.Ioc 0 T))
    (hcfB : ∀ m, ∫ t in Set.Ioc 0 T, coordForm (u m t) ≤ B)
    (hgw : WeakL2 (cylMeasure T) (fun m => field (g m)) G)
    (hgB : ∀ m, ∫ t in Set.Ioc 0 T, gridNormSq (g m t) ≤ B)
    {χ : ℝ → ℂ} (hχm : AEStronglyMeasurable χ (volume.restrict (Set.Ioc 0 T))) {C : ℝ}
    (hC : 0 ≤ C) (hχ : ∀ t, ‖χ t‖ ≤ C) (k : Fin 3 → ℤ) :
    Tendsto (fun m => ∫ t in Set.Ioc 0 T,
        χ t * (((Nm m : ℂ) ^ 3)⁻¹ * ∑ x, u m t x * modChar k x * g m t x)) atTop
      (𝓝 (∫ p, χ p.1 * (mFourier k p.2 * U p) * G p ∂cylMeasure T)) := by
  have hfF := tendsto_field_mul_modChar hN u hu hU huU hcf hcfB k
  have heq : ∀ m, ∫ t in Set.Ioc 0 T,
        χ t * (((Nm m : ℂ) ^ 3)⁻¹ * ∑ x, u m t x * modChar k x * g m t x) =
      ∫ p, χ p.1 * field (fun t x => u m t x * modChar k x) p * field (g m) p ∂cylMeasure T :=
    fun m => integral_pairing_eq_field (hodd m) ((hu m).mul_modChar k) (hg m) hχm hχ
  refine Tendsto.congr (fun m => (heq m).symm) ?_
  refine tendsto_integral_strong_weak (ψ := fun p => χ p.1) hχm.comp_fst hC (fun p => hχ p.1)
    (fun m => memLp_field_of_isL2Grid ((hu m).mul_modChar k)) (memLp_mFourier_mul hU k)
    hfF (fun m => memLp_field_of_isL2Grid (hg m)) hgw (B := B) fun m => ?_
  rw [integral_norm_field_sq (hg m)]
  exact hgB m

end Passage

end RenewalGeometry.LiteralLinkLimit
