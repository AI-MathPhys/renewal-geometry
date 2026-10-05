/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabCauchy

/-!
# `thm:hyperbolic`: the limits `g_h → g` in `C_tH^{s-1}` and `∂ₜg_h → ∂ₜg` in `C_tH^{s-2}`

(Einstein–Standard-Model action-closure manuscript, "Common-slab metric stability".)

The Cauchy property (`common_slab_cauchy`) is turned into convergence to a limit metric:

* `exists_uniform_limit` — uniformly Cauchy families into a complete space converge uniformly;
* `toL2`, `norm_toL2_sub_sq`, `continuous_toL2_slice` — slices as elements of `L²([0,1]³)`;
* **`common_slab_limit`** — under the hypotheses of `thm:hyperbolic` (`Σ = 𝕋³`, `s ≥ 5`, common
  constants, Cauchy initial data and sources) there are a limit metric `g` and a field `ġ` on the
  slab such that
  - `g_h → g` and `∂ₜg_h → ġ` uniformly on `[0, T] × ℝ³`, `g, ġ` continuous on the slab;
  - `ġ = ∂ₜg` on the slab (`g(t, y) = g(0, y) + ∫₀ᵗ ġ(s, y) ds`, `ġ` continuous);
  - **`g_h → g` in `C_tH^{s-1}`**: for every word `|w| ≤ s - 1` the slice derivatives
    `∂^w g_h(t)` converge in `L²([0,1]³)`, uniformly in `t ∈ [0, T]`, to `G_w(t)`, with
    `t ↦ G_w(t)` continuous on `[0, T]` and `G_∅(t)` the class of `g(t, ·)` (`G_w` are the weak
    derivatives of `g` in the completion sense);
  - **`∂ₜg_h → ∂ₜg` in `C_tH^{s-2}`**: the same for `∂ₜg_h`, words `|w| ≤ s - 2`, `G'_∅(t) = ġ(t, ·)`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveStab

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

/-! ### Uniform limits -/

theorem cauchy_N {P : ℕ → ℕ → ℝ → Prop}
    (h : ∀ ε > 0, ∀ᶠ p : ℕ × ℕ in atTop, P p.1 p.2 ε) :
    ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → P i j ε := by
  intro ε hε
  obtain ⟨⟨a, b⟩, hab⟩ := Filter.eventually_atTop.mp (h ε hε)
  exact ⟨max a b, fun i j hi hj => hab (i, j) ⟨le_trans (le_max_left _ _) hi,
    le_trans (le_max_right _ _) hj⟩⟩

/-- **Uniformly Cauchy families converge uniformly.** -/
theorem exists_uniform_limit {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (u : ℕ → α → E) (s : Set α)
    (hc : ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x ∈ s, ‖u i x - u j x‖ ≤ ε) :
    ∃ v : α → E, ∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ x ∈ s, ‖u i x - v x‖ ≤ ε := by
  have hcs : ∀ x ∈ s, CauchySeq fun i => u i x := by
    intro x hx
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (by positivity)
    exact ⟨N, fun i hi => by
      rw [dist_eq_norm]
      exact (hN i N hi le_rfl x hx).trans_lt (by linarith)⟩
  choose! v hv using fun x hx => cauchySeq_tendsto_of_complete (hcs x hx)
  refine ⟨v, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hc ε hε
  refine ⟨N, fun i hi x hx => ?_⟩
  have ht : Tendsto (fun j => ‖u i x - u j x‖) atTop (𝓝 ‖u i x - v x‖) :=
    ((tendsto_const_nhds.sub (hv x hx)).norm)
  exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨N, fun j hj => hN i j hi hj x hx⟩)

/-! ### Slices in `L²([0,1]³)` -/

/-- The measure of the unit cube. -/
abbrev μc : Measure (Fin 3 → ℝ) := (volume : Measure (Fin 3 → ℝ)).restrict (Icc 0 1)

/-- The `L²([0,1]³)` class of a function (zero if not square integrable). -/
def toL2 (F : (Fin 3 → ℝ) → ℝ) : Lp ℝ 2 μc := by
  classical exact if h : MemLp F 2 μc then h.toLp F else 0

theorem memLp_of_continuous {F : (Fin 3 → ℝ) → ℝ} (hF : Continuous F) : MemLp F 2 μc :=
  (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2
    (integrableOn_cube_of_continuousOn (hF.pow 2).continuousOn)

theorem toL2_eq {F : (Fin 3 → ℝ) → ℝ} (hF : Continuous F) :
    toL2 F = (memLp_of_continuous hF).toLp F := by
  unfold toL2; exact dif_pos (memLp_of_continuous hF)

theorem norm_toLp_sq {F : (Fin 3 → ℝ) → ℝ} (hF : MemLp F 2 μc) :
    ‖hF.toLp F‖ ^ 2 = ∫ y in Icc (0 : Fin 3 → ℝ) 1, F y ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with a ha
  rw [real_inner_self_eq_norm_sq, ha, Real.norm_eq_abs, sq_abs]

theorem norm_toL2_sub_sq {F F' : (Fin 3 → ℝ) → ℝ} (hF : Continuous F) (hF' : Continuous F') :
    ‖toL2 F - toL2 F'‖ ^ 2 = ∫ y in Icc (0 : Fin 3 → ℝ) 1, (F y - F' y) ^ 2 := by
  rw [toL2_eq hF, toL2_eq hF', ← MemLp.toLp_sub]
  exact norm_toLp_sq _

theorem norm_toL2_sub_le {F F' : (Fin 3 → ℝ) → ℝ} (hF : Continuous F) (hF' : Continuous F')
    {A : ℝ} (hA : ∫ y in Icc (0 : Fin 3 → ℝ) 1, (F y - F' y) ^ 2 ≤ A ^ 2) (hA0 : 0 ≤ A) :
    ‖toL2 F - toL2 F'‖ ≤ A := by
  have := norm_toL2_sub_sq hF hF'
  have h2 : ‖toL2 F - toL2 F'‖ ^ 2 ≤ A ^ 2 := by rw [this]; exact hA
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hA0 two_ne_zero).mp h2

theorem integral_sq_le_of_abs_le {F : (Fin 3 → ℝ) → ℝ} (hF : Continuous F) {ε : ℝ}
    (hε : ∀ y, |F y| ≤ ε) : ∫ y in Icc (0 : Fin 3 → ℝ) 1, F y ^ 2 ≤ ε ^ 2 := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0)
  calc ∫ y in Icc (0 : Fin 3 → ℝ) 1, F y ^ 2 ≤ ∫ _y in Icc (0 : Fin 3 → ℝ) 1, ε ^ 2 := by
        refine setIntegral_mono_on (integrableOn_cube_of_continuousOn (hF.pow 2).continuousOn)
          (integrableOn_const (by simp [Real.volume_Icc_pi]) (by simp)) measurableSet_Icc
          fun y _ => ?_
        have := pow_le_pow_left₀ (abs_nonneg _) (hε y) 2
        rwa [sq_abs] at this
    _ = ε ^ 2 := by simp [Measure.real, Real.volume_Icc_pi]

/-- The slice classes of a continuous space-time function depend continuously on time. -/
theorem continuous_toL2_slice {F : X → ℝ} (hF : Continuous F) :
    Continuous fun t => toL2 (fun y => F (Fin.cons t y)) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hc : ∀ t, Continuous fun y : Fin 3 → ℝ => F (Fin.cons t y) := fun t =>
    hF.comp (continuous_cons t)
  set φ : ℝ → ℝ := fun t => ∫ y in Icc (0 : Fin 3 → ℝ) 1,
    (F (Fin.cons t y) - F (Fin.cons t₀ y)) ^ 2
  have hφc : Continuous φ := by
    have := continuous_sliceInt (f := fun x : X => (F x - F (Fin.cons t₀ (Fin.tail x))) ^ 2)
      ((hF.sub (hF.comp ((continuous_cons t₀).comp
        (continuous_pi fun i => continuous_apply i.succ)))).pow 2)
    simpa [Fin.tail_cons] using this
  have hφ0 : φ t₀ = 0 := by simp [φ]
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ t, ‖toL2 (fun y => F (Fin.cons t y)) - toL2 (fun y => F (Fin.cons t₀ y))‖ =
      Real.sqrt (φ t) := fun t => by
    rw [show φ t = _ from (norm_toL2_sub_sq (hc t) (hc t₀)).symm, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [e]
  have := (hφc.sqrt).tendsto t₀
  rwa [hφ0, Real.sqrt_zero] at this

/-! ### Limits of uniformly Cauchy families of smooth periodic fields -/

theorem slab_mem_of {T : ℝ} {x : X} (hx : x 0 ∈ Icc 0 T) :
    (Fin.cons (x 0) (Fin.tail x) : X) = x := Fin.cons_self_tail x

/-- **Uniform limits on the slab**: an `L^∞_t H^m`-Cauchy family (`m ≥ 2`) of smooth periodic
fields converges uniformly on `[0, T] × ℝ³` to a field continuous on the slab. -/
theorem exists_slab_limit {T CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) {m : ℕ} (hm : 2 ≤ m) {F : ℕ → X → ℝ}
    (sF : ∀ i, ContDiff ℝ ∞ (F i)) (pF : ∀ i, IsSPeriodic (F i))
    (hc : ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q m (fun x => F i x - F j x) t ≤ ε) :
    ∃ v : X → ℝ, (∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ x : X, x 0 ∈ Icc 0 T → |F i x - v x| ≤ ε) ∧
      ContinuousOn v {x : X | x 0 ∈ Icc 0 T} := by
  have hu : ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x ∈ {x : X | x 0 ∈ Icc 0 T},
      ‖F i x - F j x‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε ^ 2 / (CS + 1)) (by positivity)
    refine ⟨N, fun i j hi hj x hx => ?_⟩
    have h1 := hsup _ ((sF i).sub (sF j)) (fun k x => by
      show F i _ - F j _ = _; rw [pF i k x, pF j k x]) (x 0) (Fin.tail x)
    rw [slab_mem_of hx] at h1
    have h2 := (Q_mono hm _ (x 0)).trans (hN i j hi hj (x 0) hx)
    have h3 : (F i x - F j x) ^ 2 ≤ ε ^ 2 := by
      calc (F i x - F j x) ^ 2 ≤ CS * (ε ^ 2 / (CS + 1)) := h1.trans
            (mul_le_mul_of_nonneg_left h2 hCS)
        _ ≤ ε ^ 2 := by
            rw [mul_div_assoc']
            rw [div_le_iff₀ (by positivity)]
            nlinarith [sq_nonneg ε]
    rw [Real.norm_eq_abs]
    exact abs_le_of_sq_le_sq' h3 hε.le |> fun h => abs_le.2 h
  obtain ⟨v, hv⟩ := exists_uniform_limit F _ hu
  refine ⟨v, fun ε hε => ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hv ε hε
    exact ⟨N, fun i hi x hx => by have := hN i hi x hx; rwa [Real.norm_eq_abs] at this⟩
  · refine TendstoUniformlyOn.continuousOn (F := F) (p := atTop) ?_
      (Frequently.of_forall fun i => (sF i).continuous.continuousOn)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hv (ε / 2) (by positivity)
    refine Filter.eventually_atTop.2 ⟨N, fun i hi x hx => ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact (hN i hi x hx).trans_lt (by linarith)

/-- **Limits in `C_tH^m`**: for an `L^∞_t H^m`-Cauchy family of smooth fields and a word
`|w| ≤ m`, the slice derivatives `∂^w F_i(t)` converge in `L²([0,1]³)` uniformly in
`t ∈ [0, T]`, to a limit continuous in `t`. -/
theorem exists_word_limit {T : ℝ} {m : ℕ} {F : ℕ → X → ℝ} (sF : ∀ i, ContDiff ℝ ∞ (F i))
    (hc : ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q m (fun x => F i x - F j x) t ≤ ε) (w : List (Fin 3)) (hw : w.length ≤ m) :
    ∃ G : ℝ → Lp ℝ 2 μc, (∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
      ‖toL2 (fun y => sd w (F i) (Fin.cons t y)) - G t‖ ≤ ε) ∧ ContinuousOn G (Icc 0 T) := by
  have hcs : ∀ i t, Continuous fun y : Fin 3 → ℝ => sd w (F i) (Fin.cons t y) := fun i t =>
    (contDiff_sd w (sF i)).continuous.comp (continuous_cons t)
  have hu : ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      ‖toL2 (fun y => sd w (F i) (Fin.cons t y)) - toL2 (fun y => sd w (F j) (Fin.cons t y))‖
        ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε ^ 2) (by positivity)
    refine ⟨N, fun i j hi hj t ht => norm_toL2_sub_le (hcs i t) (hcs j t) ?_ hε.le⟩
    have e : ∀ y, sd w (F i) (Fin.cons t y) - sd w (F j) (Fin.cons t y) =
        sd w (fun x => F i x - F j x) (Fin.cons t y) := fun y => by
      rw [sd_sub w (sF i) (sF j)]
    simp_rw [e]
    exact (term_le_Q hw _ t).trans (hN i j hi hj t ht)
  obtain ⟨G, hG⟩ := exists_uniform_limit (fun i t => toL2 (fun y => sd w (F i) (Fin.cons t y)))
    _ hu
  refine ⟨G, hG, ?_⟩
  refine TendstoUniformlyOn.continuousOn
    (F := fun i t => toL2 (fun y => sd w (F i) (Fin.cons t y))) (p := atTop) ?_
    (Frequently.of_forall fun i =>
      (continuous_toL2_slice (contDiff_sd w (sF i)).continuous).continuousOn)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hG (ε / 2) (by positivity)
  refine Filter.eventually_atTop.2 ⟨N, fun i hi t ht => ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact (hN i hi t ht).trans_lt (by linarith)

/-- **The time derivative of the limit**: if `F_i → v` and `∂ₜF_i → v'` uniformly on the slab
with `v'` continuous there, then `v(t, y) = v(0, y) + ∫₀ᵗ v'(σ, y) dσ` on the slab. -/
theorem ftc_limit {T : ℝ} {F : ℕ → X → ℝ} (sF : ∀ i, ContDiff ℝ ∞ (F i)) {v v' : X → ℝ}
    (hv : ∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ x : X, x 0 ∈ Icc 0 T → |F i x - v x| ≤ ε)
    (hv' : ∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ x : X, x 0 ∈ Icc 0 T → |pd (F i) 0 x - v' x| ≤ ε)
    (hc' : ContinuousOn v' {x : X | x 0 ∈ Icc 0 T}) (x : X) (hx : x 0 ∈ Icc 0 T) :
    v x = v (Fin.cons 0 (Fin.tail x)) + ∫ σ in (0)..(x 0), v' (Fin.cons σ (Fin.tail x)) := by
  set t := x 0
  set y := Fin.tail x
  have hx' : (Fin.cons t y : X) = x := Fin.cons_self_tail x
  have hmem : ∀ σ ∈ Icc 0 t, (Fin.cons σ y : X) 0 ∈ Icc 0 T := fun σ hσ =>
    ⟨hσ.1, hσ.2.trans hx.2⟩
  have hcl0 : Continuous fun σ : ℝ => (Fin.cons σ y : X) :=
    continuous_cons2.comp (continuous_id.prodMk continuous_const)
  have hcd : ∀ i, Continuous fun σ => pd (F i) 0 (Fin.cons σ y) := fun i =>
    (contDiff_pd_top (sF i) 0).continuous.comp hcl0
  -- the fundamental theorem for each smooth field
  have hftc : ∀ i, F i (Fin.cons t y) - F i (Fin.cons 0 y) =
      ∫ σ in (0)..t, pd (F i) 0 (Fin.cons σ y) := fun i => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ =>
      hasDerivAt_time y ((sF i).differentiable (by simp) _)) ((hcd i).intervalIntegrable _ _)]
  have hcl : ContinuousOn (fun σ => v' (Fin.cons σ y)) (Icc 0 t) :=
    hc'.comp hcl0.continuousOn fun σ hσ => hmem σ hσ
  -- limits of both sides
  have hL : Tendsto (fun i => F i (Fin.cons t y) - F i (Fin.cons 0 y)) atTop
      (𝓝 (v (Fin.cons t y) - v (Fin.cons 0 y))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hv (ε / 3) (by positivity)
    refine ⟨N, fun i hi => ?_⟩
    have h1 := hN i hi (Fin.cons t y) (by simpa using hx)
    have h2 := hN i hi (Fin.cons 0 y) (by simp [hx.1.trans hx.2])
    rw [Real.dist_eq]
    calc |F i (Fin.cons t y) - F i (Fin.cons 0 y) - (v (Fin.cons t y) - v (Fin.cons 0 y))|
        = |(F i (Fin.cons t y) - v (Fin.cons t y)) - (F i (Fin.cons 0 y) - v (Fin.cons 0 y))| := by
          ring_nf
      _ ≤ |F i (Fin.cons t y) - v (Fin.cons t y)| + |F i (Fin.cons 0 y) - v (Fin.cons 0 y)| :=
          abs_sub _ _
      _ < ε := by linarith
  have hR : Tendsto (fun i => ∫ σ in (0)..t, pd (F i) 0 (Fin.cons σ y)) atTop
      (𝓝 (∫ σ in (0)..t, v' (Fin.cons σ y))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hv' (ε / (T + 1)) (by have := hx.1.trans hx.2; positivity)
    refine ⟨N, fun i hi => ?_⟩
    rw [Real.dist_eq, ← intervalIntegral.integral_sub ((hcd i).intervalIntegrable _ _)
      (hcl.intervalIntegrable_of_Icc hx.1)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := ε / (T + 1)) (f := fun σ => pd (F i) 0 (Fin.cons σ y) - v' (Fin.cons σ y))
      (fun σ hσ => by
        rw [uIoc_of_le hx.1] at hσ
        exact hN i hi _ (hmem σ ⟨hσ.1.le, hσ.2⟩))
    rw [Real.norm_eq_abs] at hb
    refine hb.trans_lt ?_
    rw [sub_zero, abs_of_nonneg hx.1]
    have hT0 : 0 ≤ T := hx.1.trans hx.2
    calc ε / (T + 1) * t ≤ ε / (T + 1) * T := mul_le_mul_of_nonneg_left hx.2 (by positivity)
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  have := tendsto_nhds_unique (hL.congr fun i => hftc i) hR
  rw [hx'] at this
  linarith

/-- The `L²` limit of the slices is the slice of the uniform limit. -/
theorem toL2_limit_eq {T : ℝ} {F : ℕ → X → ℝ} (sF : ∀ i, ContDiff ℝ ∞ (F i)) {v : X → ℝ}
    (hv : ∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ x : X, x 0 ∈ Icc 0 T → |F i x - v x| ≤ ε)
    (hvc : ContinuousOn v {x : X | x 0 ∈ Icc 0 T}) {G : ℝ → Lp ℝ 2 μc}
    (hG : ∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
      ‖toL2 (fun y => sd [] (F i) (Fin.cons t y)) - G t‖ ≤ ε) {t : ℝ} (ht : t ∈ Icc 0 T) :
    G t = toL2 (fun y => v (Fin.cons t y)) := by
  have hcv : Continuous fun y : Fin 3 → ℝ => v (Fin.cons t y) :=
    hvc.comp_continuous (continuous_cons t) fun y => by simpa using ht
  have hcF : ∀ i, Continuous fun y : Fin 3 → ℝ => F i (Fin.cons t y) := fun i =>
    (sF i).continuous.comp (continuous_cons t)
  have h1 : Tendsto (fun i => toL2 (fun y => F i (Fin.cons t y))) atTop (𝓝 (G t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hG (ε / 2) (by positivity)
    exact ⟨N, fun i hi => by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact (hN i hi t ht).trans_lt (by linarith)⟩
  have h2 : Tendsto (fun i => toL2 (fun y => F i (Fin.cons t y))) atTop
      (𝓝 (toL2 (fun y => v (Fin.cons t y)))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hv (ε / 2) (by positivity)
    refine ⟨N, fun i hi => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    refine (norm_toL2_sub_le (hcF i) hcv (integral_sq_le_of_abs_le ((hcF i).sub hcv)
      fun y => hN i hi _ (by simpa using ht)) (by positivity)).trans_lt (by linarith)
  exact tendsto_nhds_unique h1 h2

variable {κ : Type} [Fintype κ]

/-- **`thm:hyperbolic`, the first two limits.** Under the hypotheses of `thm:hyperbolic`
(`Σ = 𝕋³`, `s ≥ 5`, common constants; initial data Cauchy in `H^{s-1} × H^{s-2}`, sources Cauchy
in `L¹_tH^{s-2}`) there are a limit metric `g` and its time derivative `ġ` on the slab with:
(i) `g_h → g`, `∂ₜg_h → ġ` uniformly on `[0, T] × ℝ³`; (ii) `g, ġ` continuous on the slab and
`g(t, y) = g(0, y) + ∫₀ᵗ ġ(s, y) ds` (so `ġ = ∂ₜg`); (iii) `g_h → g` in `C_tH^{s-1}`: the slice
derivatives `∂^w g_h(t)`, `|w| ≤ s - 1`, converge in `L²([0,1]³)` uniformly in `t ∈ [0, T]` to
`G_w(t)`, `t ↦ G_w(t)` continuous, `G_∅(t) = [g(t, ·)]`; (iv) `∂ₜg_h → ġ` in `C_tH^{s-2}` in the
same sense, `G'_∅(t) = [ġ(t, ·)]`. -/
theorem common_slab_limit {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ}
    {T a0 lam Λ K0 : ℝ} {s : ℕ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 < lam)
    {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ} {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHyp Np θ s T a0 lam Λ K0 (g h) (gi h) (S h))
    (hinit : Tendsto (fun p : ℕ × ℕ => ∑ c, (Q (s - 1) (fun x => g p.1 c x - g p.2 c x) 0 +
      Q (s - 2) (fun x => pd (g p.1 c) 0 x - pd (g p.2 c) 0 x) 0)) atTop (𝓝 0))
    (hsrc : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T,
      Real.sqrt (∑ c, Q (s - 2) (fun x => S p.1 c x - S p.2 c x) t)) atTop (𝓝 0)) :
    ∃ (gl gt : Idx → X → ℝ) (G G' : Idx → List (Fin 3) → ℝ → Lp ℝ 2 μc),
      (∀ ε > 0, ∃ N, ∀ h, N ≤ h → ∀ x : X, x 0 ∈ Icc 0 T → ∀ c,
        |g h c x - gl c x| ≤ ε ∧ |pd (g h c) 0 x - gt c x| ≤ ε) ∧
      (∀ c, ContinuousOn (gl c) {x : X | x 0 ∈ Icc 0 T} ∧
        ContinuousOn (gt c) {x : X | x 0 ∈ Icc 0 T}) ∧
      (∀ c (x : X), x 0 ∈ Icc 0 T → gl c x = gl c (Fin.cons 0 (Fin.tail x)) +
        ∫ σ in (0)..(x 0), gt c (Fin.cons σ (Fin.tail x))) ∧
      (∀ ε > 0, ∃ N, ∀ h, N ≤ h → ∀ t ∈ Icc 0 T, ∀ c (w : List (Fin 3)), w.length ≤ s - 1 →
        ‖toL2 (fun y => sd w (g h c) (Fin.cons t y)) - G c w t‖ ≤ ε) ∧
      (∀ ε > 0, ∃ N, ∀ h, N ≤ h → ∀ t ∈ Icc 0 T, ∀ c (w : List (Fin 3)), w.length ≤ s - 2 →
        ‖toL2 (fun y => sd w (pd (g h c) 0) (Fin.cons t y)) - G' c w t‖ ≤ ε) ∧
      (∀ c w, ContinuousOn (G c w) (Icc 0 T) ∧ ContinuousOn (G' c w) (Icc 0 T)) ∧
      (∀ c, ∀ t ∈ Icc 0 T, G c [] t = toL2 (fun y => gl c (Fin.cons t y)) ∧
        G' c [] t = toL2 (fun y => gt c (Fin.cons t y))) := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hcau := common_slab_cauchy hs hT ha hlam hg hinit hsrc
  have hN := cauchy_N (P := fun i j ε => ∀ t ∈ Icc 0 T, ∑ c, (Q (s - 1)
    (fun x => g i c x - g j c x) t + Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t) ≤ ε)
    hcau
  have hterm : ∀ i j t c, Q (s - 1) (fun x => g i c x - g j c x) t +
      Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t ≤ ∑ c, (Q (s - 1)
        (fun x => g i c x - g j c x) t + Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t) :=
    fun i j t c => Finset.single_le_sum (f := fun c => Q (s - 1) (fun x => g i c x - g j c x) t +
      Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t)
      (fun c _ => add_nonneg (Q_nonneg _ _ _) (Q_nonneg _ _ _)) (Finset.mem_univ c)
  have hc1 : ∀ c, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q (s - 1) (fun x => g i c x - g j c x) t ≤ ε := by
    intro c ε hε
    obtain ⟨N, hN'⟩ := hN ε hε
    refine ⟨N, fun i j hi hj t ht => ?_⟩
    have h1 := hterm i j t c
    have h2 := hN' i j hi hj t ht
    have h3 := Q_nonneg (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t
    linarith
  have hc2 : ∀ c, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t ≤ ε := by
    intro c ε hε
    obtain ⟨N, hN'⟩ := hN ε hε
    refine ⟨N, fun i j hi hj t ht => ?_⟩
    have h1 := hterm i j t c
    have h2 := hN' i j hi hj t ht
    have h3 := Q_nonneg (s - 1) (fun x => g i c x - g j c x) t
    linarith
  -- uniform limits on the slab
  choose gl hgl hglc using fun c => exists_slab_limit hCS hsup (m := s - 1) (by omega)
    (fun i => (hg i).sg c) (fun i => (hg i).pg c) (hc1 c)
  choose gt hgt hgtc using fun c => exists_slab_limit hCS hsup (m := s - 2) (by omega)
    (fun i => contDiff_pd_top ((hg i).sg c) 0) (fun i => isSPeriodic_pd ((hg i).pg c) 0) (hc2 c)
  -- limits of the slice derivatives
  have hG : ∀ c (w : List (Fin 3)), ∃ G : ℝ → Lp ℝ 2 μc, ContinuousOn G (Icc 0 T) ∧
      (w.length ≤ s - 1 → ∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
        ‖toL2 (fun y => sd w (g i c) (Fin.cons t y)) - G t‖ ≤ ε) := by
    intro c w
    by_cases hw : w.length ≤ s - 1
    · obtain ⟨G, h1, h2⟩ := exists_word_limit (fun i => (hg i).sg c) (hc1 c) w hw
      exact ⟨G, h2, fun _ => h1⟩
    · exact ⟨fun _ => 0, continuousOn_const, fun h => absurd h hw⟩
  choose G hGc hGl using hG
  have hG' : ∀ c (w : List (Fin 3)), ∃ G : ℝ → Lp ℝ 2 μc, ContinuousOn G (Icc 0 T) ∧
      (w.length ≤ s - 2 → ∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
        ‖toL2 (fun y => sd w (pd (g i c) 0) (Fin.cons t y)) - G t‖ ≤ ε) := by
    intro c w
    by_cases hw : w.length ≤ s - 2
    · obtain ⟨G, h1, h2⟩ := exists_word_limit (fun i => contDiff_pd_top ((hg i).sg c) 0) (hc2 c)
        w hw
      exact ⟨G, h2, fun _ => h1⟩
    · exact ⟨fun _ => 0, continuousOn_const, fun h => absurd h hw⟩
  choose G' hGc' hGl' using hG'
  refine ⟨gl, gt, G, G', ?_, fun c => ⟨hglc c, hgtc c⟩,
    fun c x hx => ftc_limit (fun i => (hg i).sg c) (hgl c) (hgt c) (hgtc c) x hx, ?_, ?_,
    fun c w => ⟨hGc c w, hGc' c w⟩, fun c t ht => ⟨?_, ?_⟩⟩
  · -- uniform convergence, uniformly in the components
    intro ε hε
    have h : ∀ c, ∃ N, ∀ i, N ≤ i → ∀ x : X, x 0 ∈ Icc 0 T →
        |g i c x - gl c x| ≤ ε ∧ |pd (g i c) 0 x - gt c x| ≤ ε := by
      intro c
      obtain ⟨N1, h1⟩ := hgl c ε hε
      obtain ⟨N2, h2⟩ := hgt c ε hε
      exact ⟨N1 + N2, fun i hi x hx => ⟨h1 i (by omega) x hx, h2 i (by omega) x hx⟩⟩
    choose Nc hNc using h
    refine ⟨∑ c, Nc c, fun i hi x hx c => hNc c i ?_ x hx⟩
    exact le_trans (Finset.single_le_sum (f := Nc) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ c)) hi
  · intro ε hε
    have h : ∀ c (w : List (Fin 3)), ∃ N, w.length ≤ s - 1 → ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
        ‖toL2 (fun y => sd w (g i c) (Fin.cons t y)) - G c w t‖ ≤ ε := by
      intro c w
      by_cases hw : w.length ≤ s - 1
      · obtain ⟨N, hN⟩ := hGl c w hw ε hε
        exact ⟨N, fun _ => hN⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose Nc hNc using h
    refine ⟨∑ c, ∑ w ∈ wordsLE 3 (s - 1), Nc c w, fun i hi t ht c w hw => hNc c w hw i ?_ t ht⟩
    have h1 := Finset.single_le_sum (f := fun w => Nc c w) (fun _ _ => Nat.zero_le _)
      (mem_wordsLE.mpr hw)
    have h2 := Finset.single_le_sum (f := fun c => ∑ w ∈ wordsLE 3 (s - 1), Nc c w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · intro ε hε
    have h : ∀ c (w : List (Fin 3)), ∃ N, w.length ≤ s - 2 → ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
        ‖toL2 (fun y => sd w (pd (g i c) 0) (Fin.cons t y)) - G' c w t‖ ≤ ε := by
      intro c w
      by_cases hw : w.length ≤ s - 2
      · obtain ⟨N, hN⟩ := hGl' c w hw ε hε
        exact ⟨N, fun _ => hN⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose Nc hNc using h
    refine ⟨∑ c, ∑ w ∈ wordsLE 3 (s - 2), Nc c w, fun i hi t ht c w hw => hNc c w hw i ?_ t ht⟩
    have h1 := Finset.single_le_sum (f := fun w => Nc c w) (fun _ _ => Nat.zero_le _)
      (mem_wordsLE.mpr hw)
    have h2 := Finset.single_le_sum (f := fun c => ∑ w ∈ wordsLE 3 (s - 2), Nc c w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · exact toL2_limit_eq (fun i => (hg i).sg c) (hgl c) (hglc c) (hGl c [] (by simp)) ht
  · exact toL2_limit_eq (fun i => contDiff_pd_top ((hg i).sg c) 0) (hgt c) (hgtc c)
      (hGl' c [] (by simp)) ht

end ReducedWaveStab

end RenewalGeometry
