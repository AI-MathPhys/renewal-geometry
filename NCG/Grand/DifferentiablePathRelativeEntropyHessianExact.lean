/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FaithfulAffineNeighborhoodExact
import NCG.Grand.AffineDataProcessingSecondDerivativeExact
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Relative-entropy Hessian along differentiable state paths

This file transports the exact affine BKM remainder to secant directions of
an arbitrary differentiable normalized faithful path.  All asymptotic
expressions use proof-independent algebraic BKM representatives.
-/

open Matrix Filter Topology MeasureTheory intervalIntegral
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Proof-independent unit-square BKM average for an affine chord. -/
noncomputable def algebraicChordBkmAverage
    (σ d : Matrix n n ℂ) (t : ℝ) : ℝ :=
  2 * ∫ x in (0 : ℝ)..1,
    x * ∫ y in (0 : ℝ)..1,
      algebraicBkmForm (σ + (t * x * y) • d) d

/-- A point of a chord between faithful endpoints is faithful. -/
theorem posDef_affine_unit_scale {σ d : Matrix n n ℂ}
    (hσ : σ.PosDef) {t r : ℝ} (hend : (σ + t • d).PosDef)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (σ + (t * r) • d).PosDef := by
  have hcombo : ((1 - r) • σ + r • (σ + t • d)).PosDef := by
    rcases eq_or_lt_of_le hr.2 with hr1 | hr1
    · rw [hr1]
      simpa using hend
    · exact (hσ.smul (sub_pos.mpr hr1)).add_posSemidef
        (hend.posSemidef.smul hr.1)
  have heq : (1 - r) • σ + r • (σ + t • d) =
      σ + (t * r) • d := by module
  rwa [heq] at hcombo

/-- The proof-dependent spectral average agrees with its proof-independent
algebraic representative whenever the chord endpoints are faithful. -/
theorem affineBkmQuadraticAverage_eq_algebraic
    {σ d : Matrix n n ℂ} (hσ : σ.PosDef) (hd : d.IsHermitian)
    {t : ℝ} (hend : (σ + t • d).PosDef) :
    affineBkmQuadraticAverage hσ.1 hd t =
      algebraicChordBkmAverage σ d t := by
  unfold affineBkmQuadraticAverage algebraicChordBkmAverage affineBkmForm
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  apply congrArg (fun z : ℝ => x * z)
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx hy
  have hr : x * y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hx.1 hy.1
    · have hxy := mul_le_mul_of_nonneg_right hx.2 hy.1
      simpa only [one_mul] using hxy.trans (by simpa only [one_mul] using hy.2)
  have hp : (σ + (t * x * y) • d).PosDef := by
    have hraw := posDef_affine_unit_scale hσ hend hr
    simpa only [mul_assoc] using hraw
  change bkmForm (affineMatrix_isHermitian hσ.1 hd (t * x * y)) d =
    algebraicBkmForm (σ + (t * x * y) • d) d
  simpa only using (algebraicBkmForm_eq_bkmForm hp).symm

/-- Exact normalized entropy remainder written using the proof-independent
algebraic BKM average. -/
theorem two_mul_inv_sq_mul_affineRelativeEntropy_eq_algebraicAverage
    {σ d : Matrix n n ℂ} (hσ : σ.PosDef) (hd : d.IsHermitian)
    (htrace : d.trace.re = 0) {t : ℝ} (ht : t ≠ 0)
    (hend : (σ + t • d).PosDef) :
    2 * t⁻¹ ^ 2 * affineRelativeEntropy hσ.1 hd t =
      algebraicChordBkmAverage σ d t := by
  rw [two_mul_inv_sq_mul_affineRelativeEntropy_eq_bkmAverage_of_endpoints
    hσ hd htrace ht hend]
  exact affineBkmQuadraticAverage_eq_algebraic hσ hd hend

/-- Secant direction of a path through a chosen base point. -/
noncomputable def pathSecant (ρ : ℝ → Matrix n n ℂ)
    (σ : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  t⁻¹ • (ρ t - σ)

theorem base_add_time_smul_pathSecant {ρ : ℝ → Matrix n n ℂ}
    {σ : Matrix n n ℂ} {t : ℝ} (ht : t ≠ 0) :
    σ + t • pathSecant ρ σ t = ρ t := by
  unfold pathSecant
  rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
  module

/-- Chord base/tangent pairs converge uniformly on the unit square when the
time parameter tends to zero and the chord directions converge. -/
theorem tendstoUniformlyOn_chordPairs
    {ι : Type*} {l : Filter ι} {τ : ι → ℝ}
    {d : ι → Matrix n n ℂ} {v : Matrix n n ℂ}
    (hτ : Tendsto τ l (𝓝 0)) (hd : Tendsto d l (𝓝 v)) :
    TendstoUniformlyOn
      (fun i (p : ℝ × ℝ) =>
        (σ + (τ i * p.1 * p.2) • d i, d i))
      (fun _ => (σ, v)) l (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hprod : Tendsto (fun i => |τ i| * ‖d i‖) l (𝓝 0) := by
    simpa only [abs_zero, zero_mul] using hτ.abs.mul hd.norm
  have heventProd : ∀ᶠ i in l, |τ i| * ‖d i‖ < ε :=
    (Metric.tendsto_nhds.mp hprod ε hε).mono fun i hi => by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg
        (mul_nonneg (abs_nonneg _) (norm_nonneg _))] using hi
  have heventDir : ∀ᶠ i in l, dist (d i) v < ε :=
    Metric.tendsto_nhds.mp hd ε hε
  filter_upwards [heventProd, heventDir] with i hiProd hiDir
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  change x ∈ Set.Icc (0 : ℝ) 1 at hx
  change y ∈ Set.Icc (0 : ℝ) 1 at hy
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · have hcoef : |τ i * x * y| ≤ |τ i| := by
      have hxy : x * y ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right hx.2 hy.1
        have h' : x * y ≤ y := by simpa only [one_mul] using h
        exact h'.trans hy.2
      rw [abs_mul, abs_mul, abs_of_nonneg hx.1, abs_of_nonneg hy.1]
      calc
        |τ i| * x * y = |τ i| * (x * y) := by ring
        _ ≤ |τ i| * 1 := mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
        _ = |τ i| := by ring
    calc
      dist σ (σ + (τ i * x * y) • d i)
          = |τ i * x * y| * ‖d i‖ := by
              simp only [dist_eq_norm, sub_add_cancel_left, norm_neg,
                norm_smul, Real.norm_eq_abs]
      _ ≤ |τ i| * ‖d i‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ < ε := hiProd
  · simpa only [dist_comm] using hiDir

/-- A function continuous at the common limit preserves uniform convergence
of a family to that constant limit. -/
theorem ContinuousAt.comp_tendstoUniformlyOn_const
    {ι α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace γ]
    {l : Filter ι} {s : Set β} {g : ι → β → α} {a : α} {F : α → γ}
    (hF : ContinuousAt F a)
    (hg : TendstoUniformlyOn g (fun _ => a) l s) :
    TendstoUniformlyOn (fun i x => F (g i x)) (fun _ => F a) l s := by
  rw [Metric.tendstoUniformlyOn_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hmap⟩ := (Metric.continuousAt_iff.mp hF) ε hε
  filter_upwards [hg δ hδ] with i hi
  intro x hx
  simpa only [dist_comm] using
    hmap (by simpa only [dist_comm] using hi x hx)

/-- Integrating the second coordinate of a jointly continuous real function
on the unit square gives a continuous function of the first coordinate. -/
theorem ContinuousOn.intervalIntegral_prod_right
    {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun x : ℝ => ∫ y in (0 : ℝ)..1, F (x, y))
      (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod isCompact_Icc).bddAbove_image hF.norm
  intro x hx
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (F := fun x y => F (x, y)) (bound := fun _ => C)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hslice : ContinuousOn (fun y : ℝ => F (z, y))
        (Set.Icc (0 : ℝ) 1) := by
      exact hF.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy => ⟨hz, hy⟩)
    have hsub : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (Set.uIoc_subset_uIcc : Set.uIoc (0 : ℝ) 1 ⊆ Set.uIcc 0 1)
    exact (hslice.mono hsub).aestronglyMeasurable
      measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with z hz
    filter_upwards with y
    intro hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        Set.uIoc_subset_uIcc hy
    exact hC ⟨(z, y), ⟨hz, hy'⟩, rfl⟩
  · exact intervalIntegrable_const
  · filter_upwards with y
    intro hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        Set.uIoc_subset_uIcc hy
    have hpair : ContinuousWithinAt (fun z : ℝ => (z, y))
        (Set.Icc (0 : ℝ) 1) x :=
      continuousWithinAt_id.prodMk continuousWithinAt_const
    change ContinuousWithinAt (fun z : ℝ => F (z, y))
      (Set.Icc (0 : ℝ) 1) x
    have hc := ContinuousWithinAt.comp
      (f := fun z : ℝ => (z, y)) (g := F)
      (s := Set.Icc (0 : ℝ) 1)
      (t := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
      (hF (x, y) ⟨hx, hy'⟩) hpair (fun z hz => ⟨hz, hy'⟩)
    exact hc

/-- Uniform convergence on the unit square is preserved when the second
coordinate is integrated out, provided the approximating and limiting
integrands are continuous there. -/
theorem TendstoUniformlyOn.intervalIntegral_prod_right
    {ι : Type*} {l : Filter ι} {F : ι → ℝ × ℝ → ℝ}
    {f : ℝ × ℝ → ℝ}
    (hF : TendstoUniformlyOn F f l
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hFc : ∀ᶠ i in l, ContinuousOn (F i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hfc : ContinuousOn f
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    TendstoUniformlyOn
      (fun i x => ∫ y in (0 : ℝ)..1, F i (x, y))
      (fun x => ∫ y in (0 : ℝ)..1, f (x, y)) l
      (Set.Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [hF (ε / 2) hhalf, hFc] with i hi hci
  intro x hx
  have hFi : IntervalIntegrable (fun y : ℝ => F i (x, y)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply hci.comp (continuousOn_const.prodMk continuousOn_id)
    intro y hy
    exact ⟨hx, by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy⟩
  have hfi : IntervalIntegrable (fun y : ℝ => f (x, y)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply hfc.comp (continuousOn_const.prodMk continuousOn_id)
    intro y hy
    exact ⟨hx, by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy⟩
  rw [Real.dist_eq, ← intervalIntegral.integral_sub hfi hFi]
  calc
    |∫ y in (0 : ℝ)..1, f (x, y) - F i (x, y)| =
        ‖∫ y in (0 : ℝ)..1, f (x, y) - F i (x, y)‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ (ε / 2) * |(1 : ℝ) - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
          Set.uIoc_subset_uIcc hy
      have hdist := hi (x, y) ⟨hx, hy'⟩
      simpa only [Real.norm_eq_abs, Real.dist_eq] using hdist.le
    _ < ε := by simpa using half_lt_self hε

/-- The proof-independent BKM chord average converges to the BKM quadratic
form when chord times vanish and chord directions converge. -/
theorem tendsto_algebraicChordBkmAverage
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {σ v : Matrix n n ℂ} (hσ : σ.PosDef)
    {τ : ι → ℝ} {d : ι → Matrix n n ℂ}
    (hτ : Tendsto τ l (𝓝 0)) (hd : Tendsto d l (𝓝 v))
    (hend : ∀ᶠ i in l, (σ + τ i • d i).PosDef) :
    Tendsto (fun i => algebraicChordBkmAverage σ (d i) (τ i)) l
      (𝓝 (bkmForm hσ.1 v)) := by
  let H : ι → ℝ × ℝ → ℝ := fun i p =>
    algebraicBkmForm (σ + (τ i * p.1 * p.2) • d i) (d i)
  let q : ℝ := algebraicBkmForm σ v
  have hHunif : TendstoUniformlyOn H (fun _ => q) l
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hpairs := tendstoUniformlyOn_chordPairs
      (σ := σ) hτ hd
    have hcomp := ContinuousAt.comp_tendstoUniformlyOn_const
      (continuousAt_algebraicBkmForm hσ) hpairs
    simpa only [H, q] using hcomp
  have hHcont : ∀ᶠ i in l, ContinuousOn (H i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    filter_upwards [hend] with i hi
    intro p hp
    have hr : p.1 * p.2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact mul_nonneg hp.1.1 hp.2.1
      · have hle := mul_le_mul_of_nonneg_right hp.1.2 hp.2.1
        have hle' : p.1 * p.2 ≤ p.2 := by simpa only [one_mul] using hle
        exact hle'.trans hp.2.2
    have hbase : (σ + (τ i * p.1 * p.2) • d i).PosDef := by
      simpa only [mul_assoc] using posDef_affine_unit_scale hσ hi hr
    have hmap : ContinuousAt
        (fun z : ℝ × ℝ =>
          (σ + (τ i * z.1 * z.2) • d i, d i)) p := by
      fun_prop
    have hc := ContinuousAt.comp'
      (f := fun z : ℝ × ℝ =>
        (σ + (τ i * z.1 * z.2) • d i, d i))
      (continuousAt_algebraicBkmForm hbase) hmap
    exact hc.continuousWithinAt
  have hinnerRaw := TendstoUniformlyOn.intervalIntegral_prod_right
    hHunif hHcont
    (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => q)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
  have hinner : TendstoUniformlyOn
      (fun i x => ∫ y in (0 : ℝ)..1, H i (x, y))
      (fun _ => q) l (Set.Icc (0 : ℝ) 1) := by
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul]
      using hinnerRaw
  have hweighted : TendstoUniformlyOn
      (fun i x => x * ∫ y in (0 : ℝ)..1, H i (x, y))
      (fun x => x * q) l (Set.Icc (0 : ℝ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hinner ⊢
    intro ε hε
    filter_upwards [hinner ε hε] with i hi
    intro x hx
    have hdist := hi x hx
    rw [Real.dist_eq] at hdist ⊢
    calc
      |x * q - x * ∫ y in (0 : ℝ)..1, H i (x, y)| =
          x * |q - ∫ y in (0 : ℝ)..1, H i (x, y)| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hx.1]
      _ ≤ |q - ∫ y in (0 : ℝ)..1, H i (x, y)| := by
            exact mul_le_of_le_one_left (abs_nonneg _) hx.2
      _ < ε := hdist
  have hweightedCont : ∀ᶠ i in l, ContinuousOn
      (fun x => x * ∫ y in (0 : ℝ)..1, H i (x, y))
      (Set.Icc (0 : ℝ) 1) := by
    filter_upwards [hHcont] with i hi
    exact continuousOn_id.mul
      (ContinuousOn.intervalIntegral_prod_right hi)
  have hweighted' : TendstoUniformlyOn
      (fun i x => x * ∫ y in (0 : ℝ)..1, H i (x, y))
      (fun x => x * q) l (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hweighted
  have hweightedCont' : ∀ᶠ i in l, ContinuousOn
      (fun x => x * ∫ y in (0 : ℝ)..1, H i (x, y))
      (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hweightedCont
  have houter := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    hweightedCont' hweighted'
  have hscaled := houter.const_mul 2
  dsimp [q] at hscaled
  rw [algebraicBkmForm_eq_bkmForm hσ] at hscaled
  have hid : (∫ x : ℝ in (0 : ℝ)..1, x) = 1 / 2 := by
    simpa using (integral_id (a := (0 : ℝ)) (b := 1))
  rw [intervalIntegral.integral_mul_const, hid] at hscaled
  have hhalf : 2 * (1 / 2 * bkmForm hσ.1 v) = bkmForm hσ.1 v := by
    ring
  rw [hhalf] at hscaled
  simpa only [algebraicChordBkmAverage, H, q] using hscaled

/-- Along any differentiable normalized faithful state path through `σ`, the
normalized second-order relative-entropy remainder converges to the BKM
quadratic form of the tangent.  This is the path-level Hessian statement: it
depends only on the first derivative of the path, not on its acceleration. -/
theorem differentiablePath_relativeEntropy_secondOrder
    {ρ : ℝ → Matrix n n ℂ} {σ v : Matrix n n ℂ}
    (hσ : σ.PosDef) (hρ0 : ρ 0 = σ)
    (hρHerm : ∀ t, (ρ t).IsHermitian)
    (htrace : ∀ t, (ρ t).trace = σ.trace)
    (hderiv : HasDerivAt ρ v 0)
    (hpos : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (ρ t).PosDef) :
    Tendsto
      (fun t => 2 * t⁻¹ ^ 2 * relEntropy (hρHerm t) hσ.1)
      (𝓝[≠] (0 : ℝ)) (𝓝 (bkmForm hσ.1 v)) := by
  have htend : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hsec : Tendsto (pathSecant ρ σ) (𝓝[≠] (0 : ℝ)) (𝓝 v) := by
    apply hderiv.tendsto_slope.congr'
    filter_upwards with t
    unfold pathSecant slope
    rw [hρ0, sub_zero, vsub_eq_sub]
  have hend : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      (σ + t • pathSecant ρ σ t).PosDef := by
    filter_upwards [hpos, self_mem_nhdsWithin] with t htpos ht
    have ht0 : t ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    rw [base_add_time_smul_pathSecant ht0]
    exact htpos
  have haverage := tendsto_algebraicChordBkmAverage
    (l := 𝓝[≠] (0 : ℝ)) hσ htend hsec hend
  apply haverage.congr'
  filter_upwards [hpos, self_mem_nhdsWithin] with t htpos ht
  have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  have hdHerm : (pathSecant ρ σ t).IsHermitian := by
    exact real_smul_isHermitian' t⁻¹ ((hρHerm t).sub hσ.1)
  have hdTrace : (pathSecant ρ σ t).trace.re = 0 := by
    unfold pathSecant
    rw [Matrix.trace_smul, Matrix.trace_sub, htrace t, sub_self, smul_zero]
    rfl
  have hrel : affineRelativeEntropy hσ.1 hdHerm t =
      relEntropy (hρHerm t) hσ.1 := by
    exact Petz.relEntropy_congr
      (base_add_time_smul_pathSecant ht0) rfl
      (affineMatrix_isHermitian hσ.1 hdHerm t) hσ.1 (hρHerm t) hσ.1
  have hendpos : (σ + t • pathSecant ρ σ t).PosDef := by
    rw [base_add_time_smul_pathSecant ht0]
    exact htpos
  symm
  rw [← hrel,
    two_mul_inv_sq_mul_affineRelativeEntropy_eq_algebraicAverage
      hσ hdHerm hdTrace ht0 hendpos]

end QRE

namespace Petz

open QRE BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A finite Kraus map preserves subtraction. -/
theorem kraus_sub {κ : Type*} [Fintype κ] (K : κ → Matrix m n ℂ)
    (A B : Matrix n n ℂ) :
    kraus K (A - B) = kraus K A - kraus K B := by
  have hneg := kraus_smul K (-1 : ℂ) B
  have hneg' : kraus K (-B) = -kraus K B := by
    simpa only [neg_smul, one_smul] using hneg
  rw [sub_eq_add_neg, kraus_add, hneg', sub_eq_add_neg]

/-- Kraus maps preserve convergence.  This finite-sum formulation avoids
introducing a separate bundled channel operator. -/
theorem tendsto_kraus {κ ι : Type*} [Fintype κ]
    (K : κ → Matrix m n ℂ) {l : Filter ι}
    {A : ι → Matrix n n ℂ} {B : Matrix n n ℂ}
    (hA : Tendsto A l (𝓝 B)) :
    Tendsto (fun i => kraus K (A i)) l (𝓝 (kraus K B)) := by
  have hc : Continuous (fun X : Matrix n n ℂ => kraus K X) := by
    unfold kraus
    fun_prop
  exact hc.continuousAt.tendsto.comp hA

/-- Differentiability is transported by a finite Kraus map, with derivative
given by the same channel applied to the tangent. -/
theorem kraus_hasDerivAt {κ : Type*} [Fintype κ]
    (K : κ → Matrix m n ℂ) {ρ : ℝ → Matrix n n ℂ}
    {v : Matrix n n ℂ} {t₀ : ℝ} (hρ : HasDerivAt ρ v t₀) :
    HasDerivAt (fun t => kraus K (ρ t)) (kraus K v) t₀ := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hmap := tendsto_kraus K hρ.tendsto_slope
  apply hmap.congr'
  filter_upwards with t
  unfold slope
  rw [vsub_eq_sub, vsub_eq_sub]
  calc
    kraus K ((t - t₀)⁻¹ • (ρ t - ρ t₀)) =
        (((t - t₀)⁻¹ : ℝ) : ℂ) • kraus K (ρ t - ρ t₀) := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
          exact kraus_smul K (((t - t₀)⁻¹ : ℝ) : ℂ) (ρ t - ρ t₀)
    _ = (t - t₀)⁻¹ • (kraus K (ρ t) - kraus K (ρ t₀)) := by
          rw [kraus_sub]
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
          rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **QS.5, path-level form.**  For an arbitrary differentiable normalized
faithful state path, the normalized data-processing loss converges to the
input BKM form minus the output BKM form.  Faithfulness of the output path is
derived from faithfulness of its base using determinant continuity. -/
theorem differentiablePath_dataProcessingLoss_secondOrder
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (K : κ → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ : ℝ → Matrix n n ℂ} {σ v : Matrix n n ℂ}
    (hσ : σ.PosDef) (hbσ : (kraus K σ).PosDef)
    (hρ0 : ρ 0 = σ) (hρHerm : ∀ t, (ρ t).IsHermitian)
    (htrace : ∀ t, (ρ t).trace = σ.trace)
    (hderiv : HasDerivAt ρ v 0)
    (hpos : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (ρ t).PosDef) :
    Tendsto
      (fun t => 2 * t⁻¹ ^ 2 *
        (relEntropy (hρHerm t) hσ.1 -
          relEntropy (kraus_isHermitian K (hρHerm t))
            (kraus_isHermitian K hσ.1)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (bkmForm hσ.1 v -
        bkmForm (kraus_isHermitian K hσ.1) (kraus K v))) := by
  have hin := differentiablePath_relativeEntropy_secondOrder
    hσ hρ0 hρHerm htrace hderiv hpos
  let barρ : ℝ → Matrix m m ℂ := fun t => kraus K (ρ t)
  have hbar0 : barρ 0 = kraus K σ := by
    dsimp [barρ]
    rw [hρ0]
  have hbarHerm : ∀ t, (barρ t).IsHermitian := fun t =>
    kraus_isHermitian K (hρHerm t)
  have hbarTrace : ∀ t, (barρ t).trace = (kraus K σ).trace := by
    intro t
    dsimp [barρ]
    rw [kraus_trace K hK, kraus_trace K hK, htrace t]
  have hbarDeriv : HasDerivAt barρ (kraus K v) 0 := by
    simpa only [barρ] using kraus_hasDerivAt K hderiv
  have hρtend : Tendsto ρ (𝓝[≠] (0 : ℝ)) (𝓝 σ) := by
    have hc := hderiv.continuousAt.tendsto.mono_left
      (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    rwa [hρ0] at hc
  have hbarTend : Tendsto barρ (𝓝[≠] (0 : ℝ)) (𝓝 (kraus K σ)) := by
    simpa only [barρ] using tendsto_kraus K hρtend
  have hdetTend : Tendsto (fun t => (barρ t).det)
      (𝓝[≠] (0 : ℝ)) (𝓝 (kraus K σ).det) :=
    (continuous_id.matrix_det.tendsto _).comp hbarTend
  have hdetNe : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (barρ t).det ≠ 0 :=
    hdetTend.eventually_ne (ne_of_gt hbσ.det_pos)
  have hbarPos : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (barρ t).PosDef := by
    filter_upwards [hpos, hdetNe] with t htpos htdet
    have hpsd : (barρ t).PosSemidef := by
      dsimp [barρ]
      exact kraus_posSemidef K htpos.posSemidef
    exact hpsd.posDef_iff_det_ne_zero.mpr htdet
  have hout := differentiablePath_relativeEntropy_secondOrder
    hbσ hbar0 hbarHerm hbarTrace hbarDeriv hbarPos
  have hloss := hin.sub hout
  convert hloss using 1
  funext t
  ring

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The path-level BKM Hessian of the data-processing loss is nonnegative. -/
theorem differentiablePath_dataProcessingLoss_bkm_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (K : κ → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    {σ v : Matrix n n ℂ} (hσ : σ.PosDef)
    (hbσ : (kraus K σ).PosDef) :
    0 ≤ bkmForm hσ.1 v -
      bkmForm (kraus_isHermitian K hσ.1) (kraus K v) :=
  bkmLoss_nonneg K hK hσ hbσ v

end Petz
end NCG
