/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinSharpRate
import RenewalGeometry.Continuum.KatoSmoothness

/-!
# Slab-cell integrals on `[a, b] × 𝕋^d`

Generic infrastructure (no renewal notions) for the comparison action of `thm:generated-dynamics`
(Einstein–Standard-Model action-closure manuscript, `eq:generated-comparison-action`,
`eq:generated-stationarity`): the action of a record on a time cell `[a, b]` is the iterated
integral `∫_a^b ∫_{[0,1]^d} f(t, y) dy dt` (`cellInt`).

* `sint_eq_coef_zero`, `continuous_sint` — slice integrals are the zero Fourier coefficient;
* **`hasDerivAt_cellInt_param`** — differentiation under the cell integral for a jointly smooth
  family `F_ε(x)`;
* **`cellInt_pd_succ`** — spatial divergences integrate to zero (periodicity);
  **`cellInt_pd_zero`** — `∫_a^b ∫ ∂_t f = ∫ f(b) - ∫ f(a)`;
* `cellInt_add`, `cellInt_smul`, `cellInt_sum`, `cellInt_nonneg`, `cellInt_mono` — linearity and
  monotonicity; **`cellInt_mul_sq_le`** — Cauchy–Schwarz.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.GenCell

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg KatoGalerkin

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-- The integral of a space-time field over the cell `[a, b] × [0, 1]^d`. -/
def cellInt (a b : ℝ) (f : ST d → ℝ) : ℝ := ∫ t in a..b, sint f t

theorem sint_eq_coef_zero (f : ST d → ℝ) (t : ℝ) : sint f t = coef f t 0 := by
  unfold coef
  congr 1
  funext x
  rw [KatoRates.casS_zero, one_mul]

theorem continuous_sint {f : ST d → ℝ} (hf : Continuous f) : Continuous (sint f) := by
  have : sint f = fun t => coef f t 0 := funext fun t => sint_eq_coef_zero f t
  rw [this]
  exact continuous_coef hf 0

theorem intervalIntegrable_sint {f : ST d → ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (sint f) volume a b :=
  (continuous_sint hf).intervalIntegrable a b

theorem cellInt_add {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    cellInt a b (fun x => f x + g x) = cellInt a b f + cellInt a b g := by
  unfold cellInt
  rw [← intervalIntegral.integral_add (intervalIntegrable_sint hf a b)
    (intervalIntegrable_sint hg a b)]
  exact intervalIntegral.integral_congr fun t _ => sint_add hf hg t

theorem cellInt_sub {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    cellInt a b (fun x => f x - g x) = cellInt a b f - cellInt a b g := by
  unfold cellInt
  rw [← intervalIntegral.integral_sub (intervalIntegrable_sint hf a b)
    (intervalIntegrable_sint hg a b)]
  exact intervalIntegral.integral_congr fun t _ => sint_sub hf hg t

theorem cellInt_smul (c : ℝ) (f : ST d → ℝ) (a b : ℝ) :
    cellInt a b (fun x => c * f x) = c * cellInt a b f := by
  unfold cellInt
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => sint_const_mul c f t

theorem cellInt_sum {ι : Type*} (s : Finset ι) {f : ι → ST d → ℝ} (hf : ∀ i, Continuous (f i))
    (a b : ℝ) : cellInt a b (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cellInt a b (f i) := by
  unfold cellInt
  rw [← intervalIntegral.integral_finset_sum fun i _ => intervalIntegrable_sint (hf i) a b]
  exact intervalIntegral.integral_congr fun t _ => sint_sum s hf t

theorem cellInt_nonneg {f : ST d → ℝ} (hf : ∀ x, 0 ≤ f x) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ cellInt a b f :=
  intervalIntegral.integral_nonneg hab fun t _ => sint_nonneg hf t

theorem cellInt_mono {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, f x ≤ g x) {a b : ℝ} (hab : a ≤ b) : cellInt a b f ≤ cellInt a b g :=
  intervalIntegral.integral_mono_on hab (intervalIntegrable_sint hf a b)
    (intervalIntegrable_sint hg a b) fun t _ => sint_mono hf hg h t

/-- A slice-wise bound integrates over the cell. -/
theorem cellInt_le_of_slices {f : ST d → ℝ} (hf : Continuous f) {a b B : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Ioo a b, sint f t ≤ B) : cellInt a b f ≤ (b - a) * B := by
  unfold cellInt
  have h1 : ∫ t in a..b, sint f t ≤ ∫ t in a..b, B := by
    refine intervalIntegral.integral_mono_ae_restrict hab (intervalIntegrable_sint hf a b)
      intervalIntegrable_const ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    have hnull : volume ({a, b} : Set ℝ) = 0 :=
      (Set.toFinite _).measure_zero _
    have : ∀ᵐ t ∂volume, t ∉ ({a, b} : Set ℝ) := measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [this] with t ht htI
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    exact h t ⟨lt_of_le_of_ne htI.1 (Ne.symm ht.1), lt_of_le_of_ne htI.2 ht.2⟩
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  exact h1

/-! ### Divergences -/

theorem hasDerivAt_time_line {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (y : Fin d → ℝ) :
    HasDerivAt (fun s => f (Fin.cons s y)) (pd f 0 (Fin.cons t y)) t := by
  have h := KatoSmooth.hasDerivAt_line_at hf (Fin.cons 0 y) 0 t
  have e : ∀ s : ℝ, (Fin.cons 0 y : ST d) + s • ev (0 : Fin (d + 1)) = Fin.cons s y := by
    intro s; funext μ
    induction μ using Fin.cases with
    | zero => simp
    | succ i => simp [Fin.succ_ne_zero]
  simp only [e] at h
  exact h

/-- **Spatial divergences integrate to zero** over a cell (periodicity). -/
theorem cellInt_pd_succ {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsSPeriodic f) (i : Fin d)
    (a b : ℝ) : cellInt a b (pd f i.succ) = 0 := by
  unfold cellInt
  have : ∀ t, sint (pd f i.succ) t = 0 := fun t =>
    integral_slice_pd_eq_zero (hf.of_le (by exact_mod_cast le_top)) hp t i
  simp [this]

/-- **The time divergence integrates to the boundary slices.** -/
theorem cellInt_pd_zero {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    cellInt a b (pd f 0) = sint f b - sint f a := by
  unfold cellInt
  have hc := contDiff_pd_top hf 0
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (sint f) (sint (pd f 0) t) t := by
    intro t _
    have h := KatoSmooth.hasDerivAt_coef_of_time (a := t - 1) (b := t + 1) hf.continuous
      hc.continuous (fun t' _ y => hasDerivAt_time_line hf t' y) 0
      (show t ∈ Ioo (t - 1) (t + 1) from ⟨by linarith, by linarith⟩)
    have e1 : sint f = fun s => coef f s 0 := funext fun s => sint_eq_coef_zero f s
    rw [e1, sint_eq_coef_zero]
    exact h
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_sint hc.continuous a b)

/-! ### Differentiation under the cell integral -/

/-- The clamp of a point of `ℝ^d` into the unit cube. -/
def clampC (y : Fin d → ℝ) : Fin d → ℝ := fun i => max 0 (min 1 (y i))

theorem continuous_clampC : Continuous (clampC (d := d)) := by
  unfold clampC; fun_prop

theorem clampC_mem (y : Fin d → ℝ) : clampC y ∈ Icc (0 : Fin d → ℝ) 1 :=
  ⟨fun i => le_max_left _ _, fun i => max_le zero_le_one (min_le_left _ _)⟩

theorem clampC_of_mem {y : Fin d → ℝ} (hy : y ∈ Icc (0 : Fin d → ℝ) 1) : clampC y = y := by
  funext i
  unfold clampC
  have h1 : y i ≤ 1 := by simpa using hy.2 i
  have h2 : 0 ≤ y i := by simpa using hy.1 i
  rw [min_eq_right h1, max_eq_right h2]

/-- **Continuity of slice integrals** of a field continuous on `[a, b] × [0, 1]^d`. -/
theorem continuousOn_sint_of {G : ST d → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG : ContinuousOn G ((fun q : ℝ × (Fin d → ℝ) => (Fin.cons q.1 q.2 : ST d)) ''
      (Icc a b ×ˢ Icc 0 1))) :
    ContinuousOn (sint G) (Icc a b) := by
  set G' : ℝ → (Fin d → ℝ) → ℝ := fun t y => G (Fin.cons (projIcc a b hab t : ℝ) (clampC y))
    with hG'
  have hc : Continuous (Function.uncurry G') := by
    have hmap : Continuous (fun q : ℝ × (Fin d → ℝ) =>
        (Fin.cons (projIcc a b hab q.1 : ℝ) (clampC q.2) : ST d)) := by
      have h1 : Continuous (fun q : ℝ × (Fin d → ℝ) => ((projIcc a b hab q.1 : ℝ), clampC q.2)) :=
        (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
          (continuous_clampC.comp continuous_snd)
      exact continuous_cons2.comp h1
    refine hG.comp_continuous hmap fun q => ⟨((projIcc a b hab q.1 : ℝ), clampC q.2),
      ⟨(projIcc a b hab q.1).2, clampC_mem _⟩, rfl⟩
  have hcont := continuous_parametric_integral_of_continuous (μ := volume) hc
    (isCompact_Icc (a := (0 : Fin d → ℝ)) (b := 1))
  refine hcont.continuousOn.congr fun t ht => ?_
  unfold sint
  refine setIntegral_congr_fun measurableSet_Icc fun y hy => ?_
  simp only [hG']
  rw [projIcc_of_mem hab ht, clampC_of_mem hy]

theorem continuousOn_cons_cube {G : ℝ × ST d → ℝ} {O : Set (ℝ × ST d)}
    (hG : ContinuousOn G O) {ε t : ℝ}
    (hK : ∀ y ∈ Icc (0 : Fin d → ℝ) 1, (ε, (Fin.cons t y : ST d)) ∈ O) :
    ContinuousOn (fun y : Fin d → ℝ => G (ε, Fin.cons t y)) (Icc 0 1) :=
  hG.comp (Continuous.continuousOn (by fun_prop)) fun y hy => hK y hy

/-- **Differentiation under the cell integral.**  Let `F_ε(x)` be continuous on an open set
`O ⊆ ℝ × ST d` with an `ε`-derivative `F'_ε(x)` continuous on `O`, and let `O` contain
`[-r, r] × [a, b] × [0, 1]^d`.  Then `d/dε ∫_a^b ∫ F_ε = ∫_a^b ∫ F'_0` at `ε = 0`. -/
theorem hasDerivAt_cellInt_param {F F' : ℝ → ST d → ℝ} {O : Set (ℝ × ST d)} (hO : IsOpen O)
    (hFc : ContinuousOn (fun p : ℝ × ST d => F p.1 p.2) O)
    (hF'c : ContinuousOn (fun p : ℝ × ST d => F' p.1 p.2) O)
    (hd : ∀ p ∈ O, HasDerivAt (fun ε => F ε p.2) (F' p.1 p.2) p.1) {r a b : ℝ} (hr : 0 < r)
    (hab : a ≤ b)
    (hK : ∀ ε ∈ Icc (-r) r, ∀ t ∈ Icc a b, ∀ y ∈ Icc (0 : Fin d → ℝ) 1,
      (ε, (Fin.cons t y : ST d)) ∈ O) :
    HasDerivAt (fun ε => cellInt a b (F ε)) (cellInt a b (F' 0)) 0 := by
  -- the compact parameter set
  set K : Set (ℝ × ST d) := (fun q : ℝ × ℝ × (Fin d → ℝ) => (q.1, (Fin.cons q.2.1 q.2.2 : ST d))) ''
    (Icc (-r) r ×ˢ (Icc a b ×ˢ Icc 0 1)) with hKdef
  have hKc : IsCompact K :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image (by fun_prop)
  have hKO : K ⊆ O := by
    rintro _ ⟨q, ⟨h1, h2, h3⟩, rfl⟩
    exact hK q.1 h1 q.2.1 h2 q.2.2 h3
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hF'c.mono hKO)
  have hmemK : ∀ ε ∈ Icc (-r) r, ∀ t ∈ Icc a b, ∀ y ∈ Icc (0 : Fin d → ℝ) 1,
      (ε, (Fin.cons t y : ST d)) ∈ K := fun ε hε t ht y hy => ⟨(ε, t, y), ⟨hε, ht, hy⟩, rfl⟩
  have hbd : ∀ ε ∈ Icc (-r) r, ∀ t ∈ Icc a b, ∀ y ∈ Icc (0 : Fin d → ℝ) 1,
      |F' ε (Fin.cons t y)| ≤ C := fun ε hε t ht y hy => by
    have := hC _ (hmemK ε hε t ht y hy)
    rwa [Real.norm_eq_abs] at this
  have hs : Ioo (-r) r ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hr
  -- the inner integrals
  have hinner : ∀ t ∈ Icc a b, ∀ ε₀ ∈ Ioo (-r) r,
      HasDerivAt (fun ε => sint (F ε) t) (sint (F' ε₀) t) ε₀ := by
    intro t ht ε₀ hε₀
    have hs₀ : Ioo (-r) r ∈ 𝓝 ε₀ := Ioo_mem_nhds hε₀.1 hε₀.2
    have hmeas : ∀ ε ∈ Icc (-r) r, AEStronglyMeasurable (fun y : Fin d → ℝ => F ε (Fin.cons t y))
        (volume.restrict (Icc (0 : Fin d → ℝ) 1)) := fun ε hε =>
      (continuousOn_cons_cube hFc (fun y hy => hK ε hε t ht y hy)).aestronglyMeasurable
        measurableSet_Icc
    have hmeas' : AEStronglyMeasurable (fun y : Fin d → ℝ => F' ε₀ (Fin.cons t y))
        (volume.restrict (Icc (0 : Fin d → ℝ) 1)) :=
      (continuousOn_cons_cube hF'c (fun y hy => hK ε₀ (Ioo_subset_Icc_self hε₀) t ht y hy)
        ).aestronglyMeasurable measurableSet_Icc
    have hint : Integrable (fun y : Fin d → ℝ => F ε₀ (Fin.cons t y))
        (volume.restrict (Icc (0 : Fin d → ℝ) 1)) :=
      (continuousOn_cons_cube hFc (fun y hy => hK ε₀ (Ioo_subset_Icc_self hε₀) t ht y hy)
        ).integrableOn_compact isCompact_Icc
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict
      (Icc (0 : Fin d → ℝ) 1)) (F := fun ε (y : Fin d → ℝ) => F ε (Fin.cons t y))
      (F' := fun ε (y : Fin d → ℝ) => F' ε (Fin.cons t y)) (bound := fun _ => C) hs₀
      (Filter.eventually_of_mem hs₀ fun ε hε => hmeas ε (Ioo_subset_Icc_self hε)) hint hmeas'
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy ε hε => by
        rw [Real.norm_eq_abs]; exact hbd ε (Ioo_subset_Icc_self hε) t ht y hy))
      (integrable_const C)
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy ε hε =>
        hd (ε, Fin.cons t y) (hK ε (Ioo_subset_Icc_self hε) t ht y hy)))
    exact h.2
  -- the outer integral
  have hbdS : ∀ ε ∈ Icc (-r) r, ∀ t ∈ Icc a b, |sint (F' ε) t| ≤ C := by
    intro ε hε t ht
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : Fin d → ℝ) 1)
      (C := C) (f := fun y => F' ε (Fin.cons t y)) (by rw [volume_cube]; simp)
      (fun y hy => by rw [Real.norm_eq_abs]; exact hbd ε hε t ht y hy)
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    rw [Measure.real, volume_cube]; simp
  have hsc : ∀ {G : ℝ → ST d → ℝ}, ContinuousOn (fun p : ℝ × ST d => G p.1 p.2) O →
      ∀ ε ∈ Icc (-r) r, ContinuousOn (sint (G ε)) (Icc a b) := by
    intro G hG ε hε
    refine continuousOn_sint_of hab ?_
    refine hG.comp ((continuous_const.prodMk continuous_id).continuousOn
      (f := fun x : ST d => (ε, x))) ?_
    rintro _ ⟨q, ⟨h1, h2⟩, rfl⟩
    exact hK ε hε q.1 h1 q.2 h2
  have hIoc : Ioc a b ⊆ Icc a b := Ioc_subset_Icc_self
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioc a b))
    (F := fun ε t => sint (F ε) t) (F' := fun ε t => sint (F' ε) t) (bound := fun _ => C) hs
    (Filter.eventually_of_mem hs fun ε hε =>
      ((hsc hFc ε (Ioo_subset_Icc_self hε)).mono hIoc).aestronglyMeasurable measurableSet_Ioc)
    (((hsc hFc 0 ⟨by linarith, hr.le⟩).integrableOn_compact isCompact_Icc).mono_set hIoc)
    (((hsc hF'c 0 ⟨by linarith, hr.le⟩).mono hIoc).aestronglyMeasurable measurableSet_Ioc)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht ε hε => by
      rw [Real.norm_eq_abs]; exact hbdS ε (Ioo_subset_Icc_self hε) t (hIoc ht)))
    (integrable_const C)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht ε hε =>
      hinner t (hIoc ht) ε hε))
  unfold cellInt
  simp only [intervalIntegral.integral_of_le hab]
  exact h.2

/-- **Differentiation under the slice integral.** -/
theorem hasDerivAt_sint_param {F F' : ℝ → ST d → ℝ} {O : Set (ℝ × ST d)}
    (hFc : ContinuousOn (fun p : ℝ × ST d => F p.1 p.2) O)
    (hF'c : ContinuousOn (fun p : ℝ × ST d => F' p.1 p.2) O)
    (hd : ∀ p ∈ O, HasDerivAt (fun ε => F ε p.2) (F' p.1 p.2) p.1) {ε₀ r t : ℝ} (hr : 0 < r)
    (hK : ∀ ε ∈ Icc (ε₀ - r) (ε₀ + r), ∀ y ∈ Icc (0 : Fin d → ℝ) 1,
      (ε, (Fin.cons t y : ST d)) ∈ O) :
    HasDerivAt (fun ε => sint (F ε) t) (sint (F' ε₀) t) ε₀ := by
  set K : Set (ℝ × ST d) := (fun q : ℝ × (Fin d → ℝ) => (q.1, (Fin.cons t q.2 : ST d))) ''
    (Icc (ε₀ - r) (ε₀ + r) ×ˢ Icc 0 1) with hKdef
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hKO : K ⊆ O := by
    rintro _ ⟨q, ⟨h1, h2⟩, rfl⟩
    exact hK q.1 h1 q.2 h2
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hF'c.mono hKO)
  have hbd : ∀ ε ∈ Icc (ε₀ - r) (ε₀ + r), ∀ y ∈ Icc (0 : Fin d → ℝ) 1,
      |F' ε (Fin.cons t y)| ≤ C := fun ε hε y hy => by
    have := hC _ ⟨(ε, y), ⟨hε, hy⟩, rfl⟩
    rwa [Real.norm_eq_abs] at this
  have hs₀ : Ioo (ε₀ - r) (ε₀ + r) ∈ 𝓝 ε₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ ε ∈ Icc (ε₀ - r) (ε₀ + r), AEStronglyMeasurable
      (fun y : Fin d → ℝ => F ε (Fin.cons t y)) (volume.restrict (Icc (0 : Fin d → ℝ) 1)) :=
    fun ε hε => (continuousOn_cons_cube hFc (fun y hy => hK ε hε y hy)).aestronglyMeasurable
      measurableSet_Icc
  have hε₀ : ε₀ ∈ Icc (ε₀ - r) (ε₀ + r) := ⟨by linarith, by linarith⟩
  have hmeas' : AEStronglyMeasurable (fun y : Fin d → ℝ => F' ε₀ (Fin.cons t y))
      (volume.restrict (Icc (0 : Fin d → ℝ) 1)) :=
    (continuousOn_cons_cube hF'c (fun y hy => hK ε₀ hε₀ y hy)).aestronglyMeasurable
      measurableSet_Icc
  have hint : Integrable (fun y : Fin d → ℝ => F ε₀ (Fin.cons t y))
      (volume.restrict (Icc (0 : Fin d → ℝ) 1)) :=
    (continuousOn_cons_cube hFc (fun y hy => hK ε₀ hε₀ y hy)).integrableOn_compact isCompact_Icc
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict
    (Icc (0 : Fin d → ℝ) 1)) (F := fun ε (y : Fin d → ℝ) => F ε (Fin.cons t y))
    (F' := fun ε (y : Fin d → ℝ) => F' ε (Fin.cons t y)) (bound := fun _ => C) hs₀
    (Filter.eventually_of_mem hs₀ fun ε hε => hmeas ε (Ioo_subset_Icc_self hε)) hint hmeas'
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy ε hε => by
      rw [Real.norm_eq_abs]; exact hbd ε (Ioo_subset_Icc_self hε) y hy))
    (integrable_const C)
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy ε hε =>
      hd (ε, Fin.cons t y) (hK ε (Ioo_subset_Icc_self hε) y hy)))
  exact h.2

/-! ### Cauchy–Schwarz -/

/-- **Cauchy–Schwarz on a cell.** -/
theorem cellInt_mul_sq_le {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (hab : a ≤ b) :
    cellInt a b (fun x => f x * g x) ^ 2 ≤
      cellInt a b (fun x => f x ^ 2) * cellInt a b (fun x => g x ^ 2) := by
  set A := cellInt a b (fun x => f x ^ 2)
  set B := cellInt a b (fun x => f x * g x)
  set C := cellInt a b (fun x => g x ^ 2)
  have hq : ∀ l : ℝ, 0 ≤ C * (l * l) + 2 * B * l + A := by
    intro l
    have h0 := cellInt_nonneg (f := fun x => (f x + l * g x) ^ 2) (fun x => sq_nonneg _) hab
    have e : (fun x => (f x + l * g x) ^ 2) =
        fun x => (f x ^ 2 + (2 * l) * (f x * g x)) + (l * l) * g x ^ 2 := by
      funext x; ring
    rw [e, cellInt_add (f := fun x => f x ^ 2 + 2 * l * (f x * g x))
      (g := fun x => l * l * g x ^ 2) ((hf.pow 2).add (continuous_const.mul (hf.mul hg)))
      (continuous_const.mul (hg.pow 2)), cellInt_add (f := fun x => f x ^ 2)
      (g := fun x => 2 * l * (f x * g x)) (hf.pow 2) (continuous_const.mul (hf.mul hg)),
      cellInt_smul (2 * l) (fun x => f x * g x), cellInt_smul (l * l) (fun x => g x ^ 2)] at h0
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

end RenewalGeometry.GenCell
