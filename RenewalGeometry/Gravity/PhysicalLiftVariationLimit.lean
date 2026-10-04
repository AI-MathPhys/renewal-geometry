/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.MollifierLpConvergence
import RenewalGeometry.Continuum.CoframeStrongInterpolationExact
import RenewalGeometry.Gravity.LimitEinsteinInsertion

/-!
# Regulator-to-limit passage of the physical metric-test variations
  (the `(E1)` lift step of `thm:supp-renewal-palatini`; emergent-spacetime manuscript)

In the proof of `thm:supp-renewal-palatini` the realized metric first variations of the three
classified densities (`eq:main-phv-densities`) are passed to the limit:
"the same argument applies to their physical coframe variations: their coefficient tensors are
uniformly bounded and converge, so multiplying the strong `L²` bivectors by these tensors
preserves strong convergence.  The four-coframe volume term and its test insertions converge in
`L¹`".  This file formalizes that step.

The physical coframe lift of a metric test is encoded by its coefficient tensor `H_X` relative to
the coframe, `δe_X = e_X H_X` (the form of the inverse-metric test lift
`δe = e H`, `H = -½ k g`, `PalatiniEinsteinAlgebra.metricTestGenerator`).  The realized
variations are then
* Holst:    `∫_K δ_{e_X H_X} L_H (e_X, R_X)`  (`holstVariation`),
* Palatini: `∫_K δ_{e_X H_X} L_P (e_X, R_X)`  (`palatiniVariation`),
* volume:   `∫_K det e_X · tr H_X`  (the Jacobi variation of `L_vol = det e`).

General analytic lemmas (no renewal notions):
* `LpTendsto.clm_comp`, `LpTendsto.finset_sum`: strong `L^p` convergence is preserved by
  continuous linear maps and finite sums;
* `unifIntegrable_of_dominated`: a family dominated by one `L^p` function is uniformly integrable;
* `LpTendsto.bilin_of_bounded_ae`: **bounded multipliers** — if `h_n` is uniformly bounded and
  converges almost everywhere and `u_n → u` in `L^p` (`p < ∞`), then `B(h_n, u_n) → B(h, u)` in
  `L^p` for every continuous bilinear `B` (dominated convergence through Vitali's theorem);
* `tendsto_integral_apply_weak_strong`: for a finite-dimensional target, an `L²`-bounded sequence
  converging weakly (tested by scalar `L²` functions through every linear functional), paired
  with a strongly `L²`-convergent sequence of dual-valued fields, has convergent integrals.

Concrete part:
* `tens`, `holstTri`, `palTri`, `detTwo`: the bivector tensor `(e ⊗ e)^{I}{}_{μ}{}^{J}{}_{ν}` and the
  trilinear/bilinear forms with `holstVariation η e (e H) R = holstTri η H (e ⊗ e) R`
  (`holstVariation_mul_eq_holstTri`), the same for Palatini (`palatiniVariation_mul_eq_palTri`),
  and `det e = detTwo (e ⊗ e) (e ⊗ e)` (`det_eq_detTwo`);
* `tendsto_liftVariations`: **the `(E1)` passage**.  On a compact `K`, let `e_X → e` strongly in
  `L²(K)` with a uniform `L⁶(K)` bound (`eq:supp-coframe-l2-l6`), let the curvature records be
  bounded in `L²(K)` and converge weakly in `L²(K)`, and let the lift coefficient tensors `H_X` be
  uniformly bounded and converge almost everywhere to `H`.  Then the three realized variations
  converge to the corresponding variations of the limit `(e, H, R)`.
-/

open MeasureTheory Filter Topology ENNReal
open scoped NNReal

noncomputable section

namespace RenewalGeometry

set_option linter.unusedSectionVars false

/-! ### General strong-convergence calculus -/

section Calculus

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W]

namespace LpTendsto

/-- Continuous linear maps preserve strong `L^p` convergence. -/
theorem clm_comp {p : ℝ≥0∞} (L : E →L[ℝ] F) {u : ℕ → X → E} {u' : X → E}
    (hu : LpTendsto ν p u u') : LpTendsto ν p (fun n x => L (u n x)) (fun x => L (u' x)) := by
  refine ⟨fun n => L.comp_memLp' (hu.memLp n), L.comp_memLp' hu.memLp_lim, ?_⟩
  have hb : ∀ n, eLpNorm ((fun x => L (u n x)) - fun x => L (u' x)) p ν ≤
      ENNReal.ofReal ‖L‖ * eLpNorm (u n - u') p ν := fun n => by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) p
    simp only [Pi.sub_apply, ← map_sub]
    exact L.le_opNorm _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hb
  have h := ENNReal.Tendsto.const_mul hu.tendsto (a := ENNReal.ofReal ‖L‖)
    (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at h
  exact h

/-- Finite sums preserve strong `L^p` convergence. -/
theorem finset_sum {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type*} (s : Finset ι) {u : ι → ℕ → X → E}
    {u' : ι → X → E} (hu : ∀ i ∈ s, LpTendsto ν p (u i) (u' i)) :
    LpTendsto ν p (fun n x => ∑ i ∈ s, u i n x) (fun x => ∑ i ∈ s, u' i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using LpTendsto.const (ν := ν) (p := p) (u := fun _ : X => (0 : E)) MemLp.zero'
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hu a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

end LpTendsto

/-- A family dominated almost everywhere by a single `L^p` function (`1 ≤ p < ∞`) is uniformly
integrable. -/
theorem unifIntegrable_of_dominated {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {g : X → ℝ}
    (hg : MemLp g p ν) {f : ℕ → X → E} (hf : ∀ n, ∀ᵐ x ∂ν, ‖f n x‖ ≤ ‖g x‖) :
    UnifIntegrable f p ν := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := unifIntegrable_const (ι := ℕ) hp hp' hg hε
  refine ⟨δ, hδ, fun n s hs hμs => (eLpNorm_mono_ae ?_).trans (h n s hs hμs)⟩
  filter_upwards [hf n] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]; exact hx
  · simp [Set.indicator_of_notMem hxs]

/-- **Bounded almost-everywhere convergent multipliers preserve strong `L^p` convergence**
(`1 ≤ p < ∞`, finite measure): if `‖h_n‖ ≤ M` almost everywhere, `h_n → h` almost everywhere
and `u_n → u` in `L^p`, then `B(h_n, u_n) → B(h, u)` in `L^p` for every continuous bilinear `B`.
The term `B(h_n - h, u)` is handled by Vitali's convergence theorem with the dominating function
`2 M ‖B‖ ‖u‖`. -/
theorem LpTendsto.bilin_of_bounded_ae [IsFiniteMeasure ν] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (B : E →L[ℝ] F →L[ℝ] W) {h : ℕ → X → E} {h' : X → E}
    (hm : ∀ n, AEStronglyMeasurable (h n) ν) {M : ℝ} (hb : ∀ n, ∀ᵐ x ∂ν, ‖h n x‖ ≤ M)
    (hae : ∀ᵐ x ∂ν, Tendsto (fun n => h n x) atTop (𝓝 (h' x))) {u : ℕ → X → F} {u' : X → F}
    (hu : LpTendsto ν p u u') :
    LpTendsto ν p (fun n x => B (h n x) (u n x)) (fun x => B (h' x) (u' x)) := by
  have hp1 : 1 ≤ p := Fact.out
  have hm' : AEStronglyMeasurable h' ν := aestronglyMeasurable_of_tendsto_ae atTop hm hae
  have hb' : ∀ᵐ x ∂ν, ‖h' x‖ ≤ M := by
    have : ∀ᵐ x ∂ν, ∀ n, ‖h n x‖ ≤ M := ae_all_iff.2 hb
    filter_upwards [hae, this] with x hx hxb
    exact le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp hx) hxb
  set M' := max M 0
  have hbM : ∀ n, ∀ᵐ x ∂ν, ‖h n x‖ ≤ M' := fun n => by
    filter_upwards [hb n] with x hx using hx.trans (le_max_left _ _)
  have hbM' : ∀ᵐ x ∂ν, ‖h' x‖ ≤ M' := by
    filter_upwards [hb'] with x hx using hx.trans (le_max_left _ _)
  have hM'0 : 0 ≤ M' := le_max_right _ _
  -- pointwise bound for the product
  have hprod : ∀ (a : X → E) (b : X → F), (∀ᵐ x ∂ν, ‖a x‖ ≤ M') →
      ∀ᵐ x ∂ν, ‖B (a x) (b x)‖ ≤ (‖B‖ * M') * ‖b x‖ := fun a b ha => by
    filter_upwards [ha] with x hx
    calc ‖B (a x) (b x)‖ ≤ ‖B‖ * ‖a x‖ * ‖b x‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * M' * ‖b x‖ := by gcongr
  have hmem : ∀ (a : X → E) (b : X → F), AEStronglyMeasurable a ν → (∀ᵐ x ∂ν, ‖a x‖ ≤ M') →
      MemLp b p ν → MemLp (fun x => B (a x) (b x)) p ν := fun a b ha hab hbm =>
    MemLp.of_le_mul hbm (B.aestronglyMeasurable_comp₂ ha hbm.1) (hprod a b hab)
  refine ⟨fun n => hmem _ _ (hm n) (hbM n) (hu.memLp n), hmem _ _ hm' hbM' hu.memLp_lim, ?_⟩
  -- splitting
  have hsplit : ∀ n, (fun x => B (h n x) (u n x)) - (fun x => B (h' x) (u' x)) =
      (fun x => B (h n x) (u n x - u' x)) + fun x => B (h n x - h' x) (u' x) := by
    intro n; funext x
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, ContinuousLinearMap.sub_apply']
    abel
  -- first term
  have h1 : Tendsto (fun n => eLpNorm (fun x => B (h n x) (u n x - u' x)) p ν) atTop (𝓝 0) := by
    have hle : ∀ n, eLpNorm (fun x => B (h n x) (u n x - u' x)) p ν ≤
        ENNReal.ofReal (‖B‖ * M') * eLpNorm (u n - u') p ν := fun n =>
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hprod _ (fun x => u n x - u' x) (hbM n)) p
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hle
    have h := ENNReal.Tendsto.const_mul hu.tendsto (a := ENNReal.ofReal (‖B‖ * M'))
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h
    exact h
  -- second term: Vitali
  have h2 : Tendsto (fun n => eLpNorm (fun x => B (h n x - h' x) (u' x)) p ν) atTop (𝓝 0) := by
    have hg : MemLp (fun x => (‖B‖ * (2 * M')) * ‖u' x‖) p ν := hu.memLp_lim.norm.const_mul _
    have hdom : ∀ n, ∀ᵐ x ∂ν, ‖B (h n x - h' x) (u' x)‖ ≤
        ‖(‖B‖ * (2 * M')) * ‖u' x‖‖ := fun n => by
      filter_upwards [hbM n, hbM'] with x hx hx'
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖B (h n x - h' x) (u' x)‖ ≤ ‖B‖ * ‖h n x - h' x‖ * ‖u' x‖ := B.le_opNorm₂ _ _
        _ ≤ ‖B‖ * (2 * M') * ‖u' x‖ := by
          gcongr
          calc ‖h n x - h' x‖ ≤ ‖h n x‖ + ‖h' x‖ := norm_sub_le _ _
            _ ≤ 2 * M' := by linarith
    have hui := unifIntegrable_of_dominated hp1 hp hg hdom
    have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => B (h n x - h' x) (u' x)) atTop (𝓝 0) := by
      filter_upwards [hae] with x hx
      have : Tendsto (fun n => h n x - h' x) atTop (𝓝 0) := by
        simpa using hx.sub_const (h' x)
      have hc := ((B.flip (u' x)).continuous.tendsto 0).comp this
      simp only [Function.comp_def, ContinuousLinearMap.flip_apply, map_zero] at hc
      exact hc
    have := tendsto_Lp_finite_of_tendsto_ae hp1 hp
      (fun n => B.aestronglyMeasurable_comp₂ ((hm n).sub hm') hu.memLp_lim.1) MemLp.zero' hui
      hlim
    refine this.congr fun n => ?_
    congr 1
    funext x
    simp
  have h12 := h1.add h2
  rw [add_zero] at h12
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12
    (fun n => bot_le) fun n => ?_
  rw [hsplit n]
  exact eLpNorm_add_le (B.aestronglyMeasurable_comp₂ (hm n)
    ((hu.memLp n).1.sub hu.memLp_lim.1)) (B.aestronglyMeasurable_comp₂ ((hm n).sub hm')
    hu.memLp_lim.1) hp1

end Calculus

end RenewalGeometry
