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
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, ContinuousLinearMap.sub_apply]
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

/-- Expansion of a dual-valued field in a basis of the (finite-dimensional) dual space:
`v(x)(w) = Σ_i c_i(x) b_i(w)`, with `c_i = b.coord i ∘ v`. -/
theorem apply_eq_sum_basis {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] (f : G →L[ℝ] ℝ) (w : G) :
    f w = ∑ i, (Module.finBasis ℝ (G →L[ℝ] ℝ)).repr f i *
      (Module.finBasis ℝ (G →L[ℝ] ℝ) i) w := by
  have h := congrArg (fun g : G →L[ℝ] ℝ => g w) ((Module.finBasis ℝ (G →L[ℝ] ℝ)).sum_repr f).symm
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  exact h

/-- **Weak–strong passage for dual-valued pairings.**  Let `G` be finite dimensional, `u_n`
bounded in `L²(ν; G)` and weakly convergent to `u` in the scalar sense
(`∫ g ℓ(u_n) → ∫ g ℓ(u)` for every `ℓ ∈ G*` and scalar `g ∈ L²`), and let `v_n → v` strongly in
`L²(ν; G*)`.  Then `∫ v_n(u_n) → ∫ v(u)`. -/
theorem tendsto_integral_apply_weak_strong [IsFiniteMeasure ν] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {u : ℕ → X → G}
    {u' : X → G} (hu : ∀ n, MemLp (u n) 2 ν) (hu' : MemLp u' 2 ν) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hub : ∀ n, eLpNorm (u n) 2 ν ≤ C)
    (hw : ∀ (ℓ : G →L[ℝ] ℝ) (g : X → ℝ), MemLp g 2 ν →
      Tendsto (fun n => ∫ x, g x * ℓ (u n x) ∂ν) atTop (𝓝 (∫ x, g x * ℓ (u' x) ∂ν)))
    {v : ℕ → X → (G →L[ℝ] ℝ)} {v' : X → (G →L[ℝ] ℝ)} (hv : LpTendsto ν 2 v v') :
    Tendsto (fun n => ∫ x, v n x (u n x) ∂ν) atTop (𝓝 (∫ x, v' x (u' x) ∂ν)) := by
  set b := Module.finBasis ℝ (G →L[ℝ] ℝ)
  set c : Fin (Module.finrank ℝ (G →L[ℝ] ℝ)) → (G →L[ℝ] ℝ) →L[ℝ] ℝ := fun i =>
    LinearMap.toContinuousLinearMap (b.coord i)
  have hc : ∀ i x, c i (v' x) = b.repr (v' x) i := fun i x => rfl
  have hcm : ∀ i, MemLp (fun x => c i (v' x)) 2 ν := fun i => (c i).comp_memLp' hv.memLp_lim
  have hbm : ∀ i (w : X → G), MemLp w 2 ν → MemLp (fun x => b i (w x)) 2 ν := fun i w hw =>
    (b i).comp_memLp' hw
  have hint : ∀ i (w : X → G), MemLp w 2 ν →
      Integrable (fun x => c i (v' x) * b i (w x)) ν := fun i w hw =>
    (hcm i).integrable_mul (hbm i w hw)
  have hexp : ∀ (w : X → G), MemLp w 2 ν →
      ∫ x, (1 : ℝ) • (ContinuousLinearMap.apply ℝ ℝ (w x)) (v' x) ∂ν =
        ∑ i, ∫ x, c i (v' x) * b i (w x) ∂ν := fun w hw => by
    rw [← integral_finsetSum _ fun i _ => hint i w hw]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [one_smul, ContinuousLinearMap.apply_apply, hc]
    exact apply_eq_sum_basis (v' x) (w x)
  have hw' : Tendsto (fun n => ∫ x, (1 : ℝ) • (ContinuousLinearMap.apply ℝ ℝ (u n x)) (v' x) ∂ν)
      atTop (𝓝 (∫ x, (1 : ℝ) • (ContinuousLinearMap.apply ℝ ℝ (u' x)) (v' x) ∂ν)) := by
    simp only [hexp _ (hu _), hexp _ hu']
    exact tendsto_finsetSum _ fun i _ => hw (b i) _ (hcm i)
  have h := DistributionalBianchi.tendsto_integral_smul_bilin_weak_strong
    (ContinuousLinearMap.apply ℝ ℝ : G →L[ℝ] (G →L[ℝ] ℝ) →L[ℝ] ℝ)
    (ψ := fun _ => (1 : ℝ)) aestronglyMeasurable_const (M := 1) (fun _ => by simp) hu
    hv.memLp hv.memLp_lim hC hub hv.tendsto hw'
  have e1 : ∀ n, ∫ x, (1 : ℝ) • (ContinuousLinearMap.apply ℝ ℝ (u n x)) (v n x) ∂ν =
      ∫ x, v n x (u n x) ∂ν := fun n => by simp
  have e2 : ∫ x, (1 : ℝ) • (ContinuousLinearMap.apply ℝ ℝ (u' x)) (v' x) ∂ν =
      ∫ x, v' x (u' x) ∂ν := by simp
  rw [e2] at h
  exact h.congr e1

/-- Membership of a finite sum of continuous linear images. -/
theorem memLp_sum_clm {p : ℝ≥0∞} {ι : Type*} [Fintype ι] (L : ι → E →L[ℝ] F)
    {S : ι → X → E} (hS : ∀ i, MemLp (S i) p ν) :
    MemLp (fun x => ∑ i, L i (S i x)) p ν :=
  memLp_finsetSum _ fun i _ => (L i).comp_memLp' (hS i)

/-- A uniform bound for a finite sum of continuous linear images. -/
theorem exists_eLpNorm_sum_clm_le {p : ℝ≥0∞} (hp : 1 ≤ p) {ι : Type*} [Fintype ι]
    (L : ι → E →L[ℝ] F) {B : ℝ≥0∞} (hB : B ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ S : ι → X → E, (∀ i, AEStronglyMeasurable (S i) ν) →
      (∀ i, eLpNorm (S i) p ν ≤ B) → eLpNorm (fun x => ∑ i, L i (S i x)) p ν ≤ C := by
  refine ⟨∑ i, ENNReal.ofReal ‖L i‖ * B,
    ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB,
    fun S hSm hSb => ?_⟩
  have : (fun x => ∑ i, L i (S i x)) = ∑ i, fun x => L i (S i x) := by
    funext x; rw [Finset.sum_apply]
  rw [this]
  refine (eLpNorm_sum_le (fun i _ => (L i).continuous.comp_aestronglyMeasurable (hSm i))
    hp).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x =>
    (L i).le_opNorm (S i x)) p).trans ?_
  gcongr
  exact hSb i

/-- Weak `L²` convergence of finitely many components (tested by scalar `L²` functions) passes
to every linear functional of a finite sum of continuous linear images of them. -/
theorem tendsto_integral_sum_clm [IsFiniteMeasure ν] [CompleteSpace E] {ι : Type*} [Fintype ι]
    (L : ι → E →L[ℝ] F) {S : ℕ → ι → X → E} {S' : ι → X → E} (hS : ∀ n i, MemLp (S n i) 2 ν)
    (hS' : ∀ i, MemLp (S' i) 2 ν)
    (hw : ∀ i (g : X → ℝ), MemLp g 2 ν →
      Tendsto (fun n => ∫ x, g x • S n i x ∂ν) atTop (𝓝 (∫ x, g x • S' i x ∂ν)))
    (ℓ : F →L[ℝ] ℝ) (g : X → ℝ) (hg : MemLp g 2 ν) :
    Tendsto (fun n => ∫ x, g x * ℓ (∑ i, L i (S n i x)) ∂ν) atTop
      (𝓝 (∫ x, g x * ℓ (∑ i, L i (S' i x)) ∂ν)) := by
  have hint : ∀ (T : X → E), MemLp T 2 ν → Integrable (fun x => g x • T x) ν :=
    fun T hT => (hT.smul hg (r := 1)).integrable le_rfl
  have hexp : ∀ (T : ι → X → E), (∀ i, MemLp (T i) 2 ν) →
      ∫ x, g x * ℓ (∑ i, L i (T i x)) ∂ν = ∑ i, (ℓ.comp (L i)) (∫ x, g x • T i x ∂ν) := by
    intro T hT
    have hT' : ∀ i, Integrable (fun x => (ℓ.comp (L i)) (g x • T i x)) ν :=
      fun i => (ℓ.comp (L i)).integrable_comp (hint _ (hT i))
    have e1 : ∀ i, (ℓ.comp (L i)) (∫ x, g x • T i x ∂ν) =
        ∫ x, (ℓ.comp (L i)) (g x • T i x) ∂ν := fun i =>
      ((ℓ.comp (L i)).integral_comp_comm (hint _ (hT i))).symm
    simp only [e1]
    rw [← integral_finsetSum _ fun i _ => hT' i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [map_sum, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  simp only [hexp _ (hS _), hexp _ hS']
  exact tendsto_finsetSum _ fun i _ =>
    ((ℓ.comp (L i)).continuous.tendsto _).comp (hw i g hg)

end Calculus

/-! ### Finite-dimensional multilinear packaging -/

section Packaging

variable {E F Z G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A bilinear map out of finite-dimensional spaces, as a continuous bilinear map. -/
def bilinCLM (f : E →ₗ[ℝ] F →ₗ[ℝ] G) : E →L[ℝ] F →L[ℝ] G :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] G) ≃ₗ[ℝ] (F →L[ℝ] G)).toLinearMap ∘ₗ f)

theorem bilinCLM_apply (f : E →ₗ[ℝ] F →ₗ[ℝ] G) (x : E) (y : F) : bilinCLM f x y = f x y := rfl

/-- A real-valued trilinear form on finite-dimensional spaces, as a continuous bilinear map into
the dual of the third space. -/
def triCLM (f : E → F → Z → ℝ) (h1 : ∀ x x' y z, f (x + x') y z = f x y z + f x' y z)
    (h2 : ∀ (c : ℝ) x y z, f (c • x) y z = c * f x y z)
    (h3 : ∀ x y y' z, f x (y + y') z = f x y z + f x y' z)
    (h4 : ∀ (c : ℝ) x y z, f x (c • y) z = c * f x y z)
    (h5 : ∀ x y z z', f x y (z + z') = f x y z + f x y z')
    (h6 : ∀ (c : ℝ) x y z, f x y (c • z) = c * f x y z) : E →L[ℝ] F →L[ℝ] (Z →L[ℝ] ℝ) :=
  bilinCLM (LinearMap.mk₂ ℝ (fun x y => LinearMap.toContinuousLinearMap
      { toFun := f x y, map_add' := h5 x y, map_smul' := fun c z => by simp [h6] })
    (fun x x' y => by ext z; simp [h1]) (fun c x y => by ext z; simp [h2])
    (fun x y y' => by ext z; simp [h3]) (fun c x y => by ext z; simp [h4]))

theorem triCLM_apply (f : E → F → Z → ℝ) (h1 h2 h3 h4 h5 h6) (x : E) (y : F) (z : Z) :
    triCLM f h1 h2 h3 h4 h5 h6 x y z = f x y z := rfl

end Packaging

/-! ### The coframe bivector tensor and the classified variation forms -/

section Forms

open PalatiniEinsteinAlgebra LimitEinsteinInsertion

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Four-index real arrays (coframe bivector tensors `P^I{}_μ{}^J{}_ν`, curvature arrays
`R^{KL}{}_{ρσ}`). -/
abbrev Arr4 : Type := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- The tensor product `(E ⊗ F)^I{}_μ{}^J{}_ν = E^I_μ F^J_ν` of two coframe matrices. -/
def tens : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] Arr4 :=
  bilinCLM (LinearMap.mk₂ ℝ (fun E F => fun I μ J ν => E I μ * F J ν)
    (fun _ _ _ => by funext I μ J ν; simp [add_mul])
    (fun _ _ _ => by funext I μ J ν; simp [mul_assoc])
    (fun _ _ _ => by funext I μ J ν; simp [mul_add])
    (fun _ _ _ => by funext I μ J ν; simp; ring))

theorem tens_apply (E F : Matrix (Fin 4) (Fin 4) ℝ) (I μ J ν : Fin 4) :
    tens E F I μ J ν = E I μ * F J ν := rfl

/-- `P^I{}_a{}^J{}_b Q_{IJ}` (the Holst contraction read on the bivector tensor). -/
def hol2P (P : Arr4) (a b : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ I, ∑ J, P I a J b * Q I J

/-- `ε_{IJKL} P^I{}_a{}^J{}_b Q^{KL}` (the Palatini contraction read on the bivector tensor). -/
def pal4P (P : Arr4) (a b : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ I, ∑ J, ∑ K, ∑ L, epsR I J K L * P I a J b * Q K L

theorem hol2P_add (P P' : Arr4) (a b : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) :
    hol2P (P + P') a b Q = hol2P P a b Q + hol2P P' a b Q := by
  simp only [hol2P, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hol2P_smul (c : ℝ) (P : Arr4) (a b : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) :
    hol2P (c • P) a b Q = c * hol2P P a b Q := by
  simp only [hol2P, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hol2P_add_right (P : Arr4) (a b : Fin 4) (Q Q' : Fin 4 → Fin 4 → ℝ) :
    hol2P P a b (Q + Q') = hol2P P a b Q + hol2P P a b Q' := by
  simp only [hol2P, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hol2P_smul_right (c : ℝ) (P : Arr4) (a b : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) :
    hol2P P a b (c • Q) = c * hol2P P a b Q := by
  simp only [hol2P, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => by ring

theorem pal4P_add (P P' : Arr4) (a b : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) :
    pal4P (P + P') a b Q = pal4P P a b Q + pal4P P' a b Q := by
  simp only [pal4P, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem pal4P_smul (c : ℝ) (P : Arr4) (a b : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) :
    pal4P (c • P) a b Q = c * pal4P P a b Q := by
  simp only [pal4P, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
    Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => by ring

theorem pal4P_add_right (P : Arr4) (a b : Fin 4) (Q Q' : Fin 4 → Fin 4 → ℝ) :
    pal4P P a b (Q + Q') = pal4P P a b Q + pal4P P a b Q' := by
  simp only [pal4P, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pal4P_smul_right (c : ℝ) (P : Arr4) (a b : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) :
    pal4P P a b (c • Q) = c * pal4P P a b Q := by
  simp only [pal4P, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
    Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => by ring

theorem lowerInternal_add (η : Matrix (Fin 4) (Fin 4) ℝ) (R R' : Arr4) (ρ σ : Fin 4) :
    (fun I J => lowerInternal η (R + R') I J ρ σ) =
      (fun I J => lowerInternal η R I J ρ σ) + fun I J => lowerInternal η R' I J ρ σ := by
  funext I J
  simp only [lowerInternal, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem lowerInternal_smul (η : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) (R : Arr4) (ρ σ : Fin 4) :
    (fun I J => lowerInternal η (c • R) I J ρ σ) = c • fun I J => lowerInternal η R I J ρ σ := by
  funext I J
  simp only [lowerInternal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => by ring

theorem curvSlice_add (R R' : Arr4) (ρ σ : Fin 4) :
    (fun K L => (R + R') K L ρ σ) = (fun K L => R K L ρ σ) + fun K L => R' K L ρ σ := rfl

theorem curvSlice_smul (c : ℝ) (R : Arr4) (ρ σ : Fin 4) :
    (fun K L => (c • R) K L ρ σ) = c • fun K L => R K L ρ σ := rfl

/-- The Holst coframe variation along `δe = e H`, read as a trilinear form in
`(H, e ⊗ e, R)`. -/
def holstTri (η H : Matrix (Fin 4) (Fin 4) ℝ) (P R : Arr4) : ℝ :=
  (1 / 2) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ *
    (∑ γ, H γ μ * hol2P P γ ν (fun I J => lowerInternal η R I J ρ σ) +
      ∑ γ, H γ ν * hol2P P μ γ (fun I J => lowerInternal η R I J ρ σ))

/-- The Palatini coframe variation along `δe = e H`, read as a trilinear form in
`(H, e ⊗ e, R)`. -/
def palTri (H : Matrix (Fin 4) (Fin 4) ℝ) (P R : Arr4) : ℝ :=
  (1 / 4) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ *
    (∑ γ, H γ μ * pal4P P γ ν (fun K L => R K L ρ σ) +
      ∑ γ, H γ ν * pal4P P μ γ (fun K L => R K L ρ σ))

theorem hol2_mul_left (e H : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) :
    hol2 (fun I => (e * H) I μ) (fun J => e J ν) Q = ∑ γ, H γ μ * hol2P (tens e e) γ ν Q := by
  unfold hol2 hol2P
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, tens_apply]
  rw [sum_move_out2 (fun γ I J => e I γ * H γ μ * e J ν * Q I J)]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun I _ =>
    Finset.sum_congr rfl fun J _ => by ring

theorem hol2_mul_second (e H : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4)
    (Q : Fin 4 → Fin 4 → ℝ) :
    hol2 (fun I => e I μ) (fun J => (e * H) J ν) Q = ∑ γ, H γ ν * hol2P (tens e e) μ γ Q := by
  unfold hol2 hol2P
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, tens_apply]
  rw [sum_move_out2 (fun γ I J => e I μ * (e J γ * H γ ν) * Q I J)]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun I _ =>
    Finset.sum_congr rfl fun J _ => by ring

theorem pal4_mul_left (e H : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) (Q : Fin 4 → Fin 4 → ℝ) :
    pal4 (fun I => (e * H) I μ) (fun J => e J ν) Q = ∑ γ, H γ μ * pal4P (tens e e) γ ν Q := by
  unfold pal4 pal4P
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, tens_apply]
  rw [sum_move_out4 (fun γ I J K L => epsR I J K L * (e I γ * H γ μ) * e J ν * Q K L)]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun I _ =>
    Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun K _ =>
      Finset.sum_congr rfl fun L _ => by ring

theorem pal4_mul_right (e H : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4)
    (Q : Fin 4 → Fin 4 → ℝ) :
    pal4 (fun I => e I μ) (fun J => (e * H) J ν) Q = ∑ γ, H γ ν * pal4P (tens e e) μ γ Q := by
  unfold pal4 pal4P
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, tens_apply]
  rw [sum_move_out4 (fun γ I J K L => epsR I J K L * e I μ * (e J γ * H γ ν) * Q K L)]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun I _ =>
    Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun K _ =>
      Finset.sum_congr rfl fun L _ => by ring

/-- `δ_{eH} L_H(e, R) = holstTri η H (e ⊗ e) R`. -/
theorem holstVariation_mul_eq_holstTri (η e H : Matrix (Fin 4) (Fin 4) ℝ) (R : Arr4) :
    holstVariation η e (e * H) R = holstTri η H (tens e e) R := by
  unfold holstVariation holstTri
  simp only [hol2_mul_left, hol2_mul_second]

/-- `δ_{eH} L_P(e, R) = palTri H (e ⊗ e) R`. -/
theorem palatiniVariation_mul_eq_palTri (e H : Matrix (Fin 4) (Fin 4) ℝ) (R : Arr4) :
    palatiniVariation e (e * H) R = palTri H (tens e e) R := by
  unfold palatiniVariation palTri
  simp only [pal4_mul_left, pal4_mul_right]

end Forms

/-! ### The forms as continuous multilinear maps -/

section CLMs

open PalatiniEinsteinAlgebra LimitEinsteinInsertion

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem pal4P_add_slice (P : Arr4) (a b ρ σ : Fin 4) (R R' : Arr4) :
    pal4P P a b (fun K L => (R + R') K L ρ σ) =
      pal4P P a b (fun K L => R K L ρ σ) + pal4P P a b (fun K L => R' K L ρ σ) :=
  pal4P_add_right P a b _ _

theorem pal4P_smul_slice (c : ℝ) (P : Arr4) (a b ρ σ : Fin 4) (R : Arr4) :
    pal4P P a b (fun K L => (c • R) K L ρ σ) = c * pal4P P a b (fun K L => R K L ρ σ) :=
  pal4P_smul_right c P a b _

theorem hol2P_lower_add (η : Matrix (Fin 4) (Fin 4) ℝ) (P : Arr4) (a b ρ σ : Fin 4)
    (R R' : Arr4) :
    hol2P P a b (fun I J => lowerInternal η (R + R') I J ρ σ) =
      hol2P P a b (fun I J => lowerInternal η R I J ρ σ) +
        hol2P P a b (fun I J => lowerInternal η R' I J ρ σ) := by
  rw [lowerInternal_add, hol2P_add_right]

theorem hol2P_lower_smul (η : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) (P : Arr4) (a b ρ σ : Fin 4)
    (R : Arr4) :
    hol2P P a b (fun I J => lowerInternal η (c • R) I J ρ σ) =
      c * hol2P P a b (fun I J => lowerInternal η R I J ρ σ) := by
  rw [lowerInternal_smul, hol2P_smul_right]

/-- The Holst variation form as a continuous map `H ↦ P ↦ (R ↦ holstTri η H P R)`. -/
def holstCLM (η : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] Arr4 →L[ℝ] (Arr4 →L[ℝ] ℝ) :=
  triCLM (holstTri η)
    (fun H H' P R => by
      simp only [holstTri, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add]; ring)
    (fun c H P R => by
      simp only [holstTri, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
      simp only [mul_left_comm, mul_assoc])
    (fun H P P' R => by
      simp only [holstTri, hol2P_add, mul_add, Finset.sum_add_distrib]; ring)
    (fun c H P R => by
      simp only [holstTri, hol2P_smul, Finset.mul_sum, mul_add]
      simp only [mul_left_comm, mul_assoc])
    (fun H P R R' => by
      simp only [holstTri, hol2P_lower_add, mul_add, Finset.sum_add_distrib]; ring)
    (fun c H P R => by
      simp only [holstTri, hol2P_lower_smul, Finset.mul_sum, mul_add]
      simp only [mul_left_comm, mul_assoc])

theorem holstCLM_apply (η H : Matrix (Fin 4) (Fin 4) ℝ) (P R : Arr4) :
    holstCLM η H P R = holstTri η H P R := rfl

/-- The Palatini variation form as a continuous map `H ↦ P ↦ (R ↦ palTri H P R)`. -/
def palCLM : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] Arr4 →L[ℝ] (Arr4 →L[ℝ] ℝ) :=
  triCLM palTri
    (fun H H' P R => by
      simp only [palTri, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add]; ring)
    (fun c H P R => by
      simp only [palTri, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
      simp only [mul_left_comm, mul_assoc])
    (fun H P P' R => by
      simp only [palTri, pal4P_add, mul_add, Finset.sum_add_distrib]; ring)
    (fun c H P R => by
      simp only [palTri, pal4P_smul, Finset.mul_sum, mul_add]
      simp only [mul_left_comm, mul_assoc])
    (fun H P R R' => by
      simp only [palTri, pal4P_add_slice, mul_add, Finset.sum_add_distrib]; ring)
    (fun c H P R => by
      simp only [palTri, pal4P_smul_slice, Finset.mul_sum, mul_add]
      simp only [mul_left_comm, mul_assoc])

theorem palCLM_apply (H : Matrix (Fin 4) (Fin 4) ℝ) (P R : Arr4) :
    palCLM H P R = palTri H P R := rfl

/-- The determinant read on two bivector tensors:
`detTwo P P' = ε_{IJKL} P^0{}_I{}^1{}_J P'^2{}_K{}^3{}_L`. -/
def detTwo : Arr4 →L[ℝ] Arr4 →L[ℝ] ℝ :=
  bilinCLM (LinearMap.mk₂ ℝ
    (fun P P' => ∑ I, ∑ J, ∑ K, ∑ L, epsR I J K L * P 0 I 1 J * P' 2 K 3 L)
    (fun P P' Q => by simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib])
    (fun c P Q => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
        Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => by ring)
    (fun P Q Q' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c P Q => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
        Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => by ring))

theorem detTwo_apply (P P' : Arr4) :
    detTwo P P' = ∑ I, ∑ J, ∑ K, ∑ L, epsR I J K L * P 0 I 1 J * P' 2 K 3 L := rfl

/-- `det e = detTwo (e ⊗ e) (e ⊗ e)`. -/
theorem det_eq_detTwo (e : Matrix (Fin 4) (Fin 4) ℝ) : e.det = detTwo (tens e e) (tens e e) := by
  rw [det_eq_sum_eps, detTwo_apply]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
    Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
  simp only [tens_apply]; ring

/-- `(H, s) ↦ tr H · s`. -/
def traceMul : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).comp
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 4) ℝ ℝ))

theorem traceMul_apply (H : Matrix (Fin 4) (Fin 4) ℝ) (s : ℝ) :
    traceMul H s = Matrix.trace H * s := rfl

/-- The `μ`-th column embedding `v ↦ (e^I_ν = δ_{νμ} v^I)`. -/
def colEmbed (μ : Fin 4) : (Fin 4 → ℝ) →L[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Matrix.of fun I ν => if ν = μ then v I else 0
      map_add' := fun v w => by
        ext I ν; simp only [Matrix.of_apply, Pi.add_apply, Matrix.add_apply]; split_ifs <;> simp
      map_smul' := fun c v => by
        ext I ν; simp only [Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
          RingHom.id_apply]; split_ifs <;> simp }

theorem coframeMatrix_eq_sum (v : Fin 4 → (Fin 4 → ℝ)) :
    coframeMatrix v = ∑ μ, colEmbed μ (v μ) := by
  ext I ν
  simp [coframeMatrix, colEmbed, Matrix.sum_apply]

/-- The `(ρ, σ)` embedding of a mixed-index curvature component into the raised curvature
array: `M ↦ (R^{KL}{}_{ρ'σ'} = δ_{ρ'ρ} δ_{σ'σ} M^K{}_{M'} η^{M'L})`. -/
def raiseEmbed (q : Fin 4 × Fin 4) : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] Arr4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M K L ρ σ => if (ρ, σ) = q then ∑ N, M K N * minkowski N L else 0
      map_add' := fun M M' => by
        funext K L ρ σ; simp only [Pi.add_apply, Matrix.add_apply, add_mul,
          Finset.sum_add_distrib]; split_ifs <;> simp
      map_smul' := fun c M => by
        funext K L ρ σ
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun N _ => ?_
          rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
        · simp }

theorem raisedCurvature_eq_sum (Rm : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) :
    raisedCurvature Rm = ∑ q : Fin 4 × Fin 4, raiseEmbed q (Rm q.1 q.2) := by
  funext K L ρ σ
  simp only [raisedCurvature, Finset.sum_apply]
  rw [Finset.sum_eq_single (ρ, σ)]
  · simp [raiseEmbed]
  · intro q _ hq
    simp [raiseEmbed, Ne.symm hq]
  · simp

end CLMs

/-! ### The `(E1)` passage of the realized metric-test variations -/

section Passage

open PalatiniEinsteinAlgebra LimitEinsteinInsertion

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem fact_one_le_four : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

theorem holderTriple_four_four_two : HolderTriple (4 : ℝ≥0∞) 4 2 := by
  have := holderTriple_ofReal (p := 4) (q := 4) (r := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using this

attribute [local instance] fact_one_le_four holderTriple_four_four_two

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- **`L²` convergence with a uniform `L⁶` bound gives `L⁴` convergence**
(`lem:supp-coframe-interpolation` at `q = 4`, in the `LpTendsto` calculus). -/
theorem lpTendsto_four_of_two_six [IsFiniteMeasure ν] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {u : ℕ → X → V} {u' : X → V} (hu : LpTendsto ν 2 u u') {M6 : ℝ≥0∞}
    (hM6 : M6 ≠ ∞) (h6 : ∀ n, eLpNorm (u n) 6 ν ≤ M6) :
    LpTendsto ν 4 u u' ∧ MemLp u' 6 ν := by
  have m6 : ∀ n, MemLp (u n) 6 ν := fun n => ⟨(hu.memLp n).1, (h6 n).trans_lt hM6.lt_top⟩
  have m6' : MemLp u' 6 ν := hu.memLp_of_bound two_ne_zero hM6 h6
  have e2 : ∀ f : X → V, eLpNorm f 2 ν = eLpNorm' f 2 ν := fun f => by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]; norm_num
  have e4 : ∀ f : X → V, eLpNorm f 4 ν = eLpNorm' f 4 ν := fun f => by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]; norm_num
  have e6 : ∀ f : X → V, eLpNorm f 6 ν = eLpNorm' f 6 ν := fun f => by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]; norm_num
  have hL2 : Tendsto (fun n => eLpNorm' (u n - u') 2 ν) atTop (𝓝 0) := by
    simpa only [e2] using hu.tendsto
  have h := (CoframeInterpolation.coframe_interpolation (F := ℝ) u u' (fun n => (hu.memLp n).1)
    hu.memLp_lim.1 hL2 hM6 (fun n => (e6 _).symm ▸ h6 n)).2.2.1 4 (by norm_num) (by norm_num)
  refine ⟨⟨fun n => (m6 n).mono_exponent (by norm_num), m6'.mono_exponent (by norm_num), ?_⟩, m6'⟩
  simpa only [e4] using h

/-- The coframe matrix field `x ↦ e^I_μ(x)` of a one-form field `e_μ(x) ∈ ℝ⁴`. -/
abbrev cfm (e : Fin 4 → X → (Fin 4 → ℝ)) (x : X) : Matrix (Fin 4) (Fin 4) ℝ :=
  coframeMatrix fun μ => e μ x

/-- The raised curvature array field of a mixed-index curvature two-form field. -/
abbrev rcf (R : Fin 4 → Fin 4 → X → Matrix (Fin 4) (Fin 4) ℝ) (x : X) : Arr4 :=
  raisedCurvature fun ρ σ => R ρ σ x

theorem rcf_eq_sum (R : Fin 4 → Fin 4 → X → Matrix (Fin 4) (Fin 4) ℝ) (x : X) :
    rcf R x = ∑ q : Fin 4 × Fin 4, raiseEmbed q (R q.1 q.2 x) :=
  raisedCurvature_eq_sum _

theorem cfm_eq_sum (e : Fin 4 → X → (Fin 4 → ℝ)) (x : X) :
    cfm e x = ∑ μ, colEmbed μ (e μ x) :=
  coframeMatrix_eq_sum _

/-- **The `(E1)` passage of the realized metric-test variations** (`thm:supp-renewal-palatini`,
the step "the same argument applies to their physical coframe variations: their coefficient
tensors are uniformly bounded and converge").  On a finite measure space (a compact cylinder
`K` with Lebesgue measure), let
* `e_X → e` strongly in `L²` with `sup_X ‖e_X‖_{L⁶} < ∞` (`eq:supp-coframe-l2-l6`),
* the lift coefficient tensors `H_X` (`δe_X = e_X H_X`) be uniformly bounded and converge almost
  everywhere to `H`,
* the curvature records `R_X` be bounded in `L²` and converge weakly in `L²` to `R`.
Then the realized Holst, Palatini and volume variations
`∫ δ_{e_X H_X} L_H(e_X, R_X)`, `∫ δ_{e_X H_X} L_P(e_X, R_X)`, `∫ det e_X · tr H_X`
converge to the corresponding variations of `(e, H, R)`, whose integrands are integrable. -/
theorem tendsto_liftVariations [IsFiniteMeasure ν] (η : Matrix (Fin 4) (Fin 4) ℝ)
    {e : ℕ → Fin 4 → X → (Fin 4 → ℝ)} {e' : Fin 4 → X → (Fin 4 → ℝ)}
    (he : ∀ μ, LpTendsto ν 2 (fun n => e n μ) (e' μ)) {M6 : ℝ≥0∞} (hM6 : M6 ≠ ∞)
    (he6 : ∀ n μ, eLpNorm (e n μ) 6 ν ≤ M6)
    {H : ℕ → X → Matrix (Fin 4) (Fin 4) ℝ} {H' : X → Matrix (Fin 4) (Fin 4) ℝ}
    (hHm : ∀ n, AEStronglyMeasurable (H n) ν) {M : ℝ} (hHb : ∀ n, ∀ᵐ x ∂ν, ‖H n x‖ ≤ M)
    (hHae : ∀ᵐ x ∂ν, Tendsto (fun n => H n x) atTop (𝓝 (H' x)))
    {R : ℕ → Fin 4 → Fin 4 → X → Matrix (Fin 4) (Fin 4) ℝ}
    {R' : Fin 4 → Fin 4 → X → Matrix (Fin 4) (Fin 4) ℝ} (hR : ∀ n ρ σ, MemLp (R n ρ σ) 2 ν)
    (hR' : ∀ ρ σ, MemLp (R' ρ σ) 2 ν) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hRb : ∀ n ρ σ, eLpNorm (R n ρ σ) 2 ν ≤ B)
    (hRw : ∀ ρ σ (g : X → ℝ), MemLp g 2 ν →
      Tendsto (fun n => ∫ x, g x • R n ρ σ x ∂ν) atTop (𝓝 (∫ x, g x • R' ρ σ x ∂ν))) :
    Tendsto (fun n => ∫ x, holstVariation η (cfm (e n) x) (cfm (e n) x * H n x) (rcf (R n) x) ∂ν)
        atTop (𝓝 (∫ x, holstVariation η (cfm e' x) (cfm e' x * H' x) (rcf R' x) ∂ν)) ∧
      Tendsto (fun n => ∫ x, palatiniVariation (cfm (e n) x) (cfm (e n) x * H n x)
          (rcf (R n) x) ∂ν) atTop
        (𝓝 (∫ x, palatiniVariation (cfm e' x) (cfm e' x * H' x) (rcf R' x) ∂ν)) ∧
      Tendsto (fun n => ∫ x, (cfm (e n) x).det * Matrix.trace (H n x) ∂ν) atTop
        (𝓝 (∫ x, (cfm e' x).det * Matrix.trace (H' x) ∂ν)) ∧
      Integrable (fun x => holstVariation η (cfm e' x) (cfm e' x * H' x) (rcf R' x)) ν ∧
      Integrable (fun x => palatiniVariation (cfm e' x) (cfm e' x * H' x) (rcf R' x)) ν ∧
      Integrable (fun x => (cfm e' x).det * Matrix.trace (H' x)) ν := by
  -- coframe matrices converge in `L⁴`
  have hc4 : ∀ μ, LpTendsto ν 4 (fun n => e n μ) (e' μ) := fun μ =>
    (lpTendsto_four_of_two_six (he μ) hM6 fun n => he6 n μ).1
  have hE4 : LpTendsto ν 4 (fun n => cfm (e n)) (cfm e') := by
    have := LpTendsto.finset_sum Finset.univ fun μ _ => (hc4 μ).clm_comp (colEmbed μ)
    refine this.congr (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact (cfm_eq_sum (e n) x).symm
    · exact (cfm_eq_sum e' x).symm
  -- bivector tensors converge in `L²`
  have hP : LpTendsto ν 2 (fun n x => tens (cfm (e n) x) (cfm (e n) x))
      (fun x => tens (cfm e' x) (cfm e' x)) := hE4.bilin tens hE4
  -- the curvature arrays
  have hRr : ∀ n, MemLp (rcf (R n)) 2 ν := fun n => by
    have := memLp_sum_clm (ν := ν) (p := 2) raiseEmbed (S := fun q => R n q.1 q.2)
      fun q => hR n q.1 q.2
    exact this.ae_eq (Eventually.of_forall fun x => (rcf_eq_sum (R n) x).symm)
  have hRr' : MemLp (rcf R') 2 ν := by
    have := memLp_sum_clm (ν := ν) (p := 2) raiseEmbed (S := fun q => R' q.1 q.2)
      fun q => hR' q.1 q.2
    exact this.ae_eq (Eventually.of_forall fun x => (rcf_eq_sum R' x).symm)
  obtain ⟨C, hC, hCb⟩ := exists_eLpNorm_sum_clm_le (X := X) (ν := ν) (p := 2) (by norm_num)
    raiseEmbed hB
  have hRrb : ∀ n, eLpNorm (rcf (R n)) 2 ν ≤ C := fun n => by
    have := hCb (fun q => R n q.1 q.2) (fun q => (hR n q.1 q.2).1) fun q => hRb n q.1 q.2
    refine (le_of_eq (eLpNorm_congr_ae ?_)).trans this
    exact Eventually.of_forall fun x => rcf_eq_sum (R n) x
  have hRw' : ∀ (ℓ : Arr4 →L[ℝ] ℝ) (g : X → ℝ), MemLp g 2 ν →
      Tendsto (fun n => ∫ x, g x * ℓ (rcf (R n) x) ∂ν) atTop
        (𝓝 (∫ x, g x * ℓ (rcf R' x) ∂ν)) := fun ℓ g hg => by
    have := tendsto_integral_sum_clm (ν := ν) raiseEmbed (S := fun n q => R n q.1 q.2)
      (S' := fun q => R' q.1 q.2) (fun n q => hR n q.1 q.2) (fun q => hR' q.1 q.2)
      (fun q g hg => hRw q.1 q.2 g hg) ℓ g hg
    refine (this.congr fun n => ?_).mono_right (le_of_eq (congrArg 𝓝 ?_))
    · exact integral_congr_ae (Eventually.of_forall fun x =>
        congrArg (fun y => g x * ℓ y) (rcf_eq_sum (R n) x).symm)
    · exact integral_congr_ae (Eventually.of_forall fun x =>
        congrArg (fun y => g x * ℓ y) (rcf_eq_sum R' x).symm)
  -- rewriting the integrands
  have iH : ∀ (E H0 : Matrix (Fin 4) (Fin 4) ℝ) (Rr : Arr4),
      holstCLM η H0 (tens E E) Rr = holstVariation η E (E * H0) Rr := fun E H0 Rr => by
    rw [holstCLM_apply, holstVariation_mul_eq_holstTri]
  have iP : ∀ (E H0 : Matrix (Fin 4) (Fin 4) ℝ) (Rr : Arr4),
      palCLM H0 (tens E E) Rr = palatiniVariation E (E * H0) Rr := fun E H0 Rr => by
    rw [palCLM_apply, palatiniVariation_mul_eq_palTri]
  have iV : ∀ (E H0 : Matrix (Fin 4) (Fin 4) ℝ),
      traceMul H0 (detTwo (tens E E) (tens E E)) = E.det * Matrix.trace H0 := fun E H0 => by
    rw [traceMul_apply, ← det_eq_detTwo, mul_comm]
  -- Holst
  have hGH : LpTendsto ν 2 (fun n x => holstCLM η (H n x) (tens (cfm (e n) x) (cfm (e n) x)))
      (fun x => holstCLM η (H' x) (tens (cfm e' x) (cfm e' x))) :=
    hP.bilin_of_bounded_ae (by norm_num) (holstCLM η) hHm hHb hHae
  have tH : Tendsto (fun n => ∫ x, holstCLM η (H n x) (tens (cfm (e n) x) (cfm (e n) x))
      (rcf (R n) x) ∂ν) atTop (𝓝 (∫ x, holstCLM η (H' x) (tens (cfm e' x) (cfm e' x))
      (rcf R' x) ∂ν)) := tendsto_integral_apply_weak_strong hRr hRr' hC hRrb hRw' hGH
  -- Palatini
  have hGP : LpTendsto ν 2 (fun n x => palCLM (H n x) (tens (cfm (e n) x) (cfm (e n) x)))
      (fun x => palCLM (H' x) (tens (cfm e' x) (cfm e' x))) :=
    hP.bilin_of_bounded_ae (by norm_num) palCLM hHm hHb hHae
  have tP : Tendsto (fun n => ∫ x, palCLM (H n x) (tens (cfm (e n) x) (cfm (e n) x))
      (rcf (R n) x) ∂ν) atTop (𝓝 (∫ x, palCLM (H' x) (tens (cfm e' x) (cfm e' x))
      (rcf R' x) ∂ν)) := tendsto_integral_apply_weak_strong hRr hRr' hC hRrb hRw' hGP
  -- volume
  have hQ : LpTendsto ν 1 (fun n x => detTwo (tens (cfm (e n) x) (cfm (e n) x))
      (tens (cfm (e n) x) (cfm (e n) x))) (fun x => detTwo (tens (cfm e' x) (cfm e' x))
      (tens (cfm e' x) (cfm e' x))) := hP.bilin detTwo hP
  have hV := hQ.bilin_of_bounded_ae (by norm_num) traceMul hHm hHb hHae
  have tV := hV.tendsto_integral
  have cH : ∀ (n : ℕ), (∫ x, holstCLM η (H n x) (tens (cfm (e n) x) (cfm (e n) x))
      (rcf (R n) x) ∂ν) = ∫ x, holstVariation η (cfm (e n) x) (cfm (e n) x * H n x)
      (rcf (R n) x) ∂ν := fun n => integral_congr_ae (Eventually.of_forall fun x => iH _ _ _)
  have cH' : (∫ x, holstCLM η (H' x) (tens (cfm e' x) (cfm e' x)) (rcf R' x) ∂ν) =
      ∫ x, holstVariation η (cfm e' x) (cfm e' x * H' x) (rcf R' x) ∂ν :=
    integral_congr_ae (Eventually.of_forall fun x => iH _ _ _)
  have cP : ∀ (n : ℕ), (∫ x, palCLM (H n x) (tens (cfm (e n) x) (cfm (e n) x))
      (rcf (R n) x) ∂ν) = ∫ x, palatiniVariation (cfm (e n) x) (cfm (e n) x * H n x)
      (rcf (R n) x) ∂ν := fun n => integral_congr_ae (Eventually.of_forall fun x => iP _ _ _)
  have cP' : (∫ x, palCLM (H' x) (tens (cfm e' x) (cfm e' x)) (rcf R' x) ∂ν) =
      ∫ x, palatiniVariation (cfm e' x) (cfm e' x * H' x) (rcf R' x) ∂ν :=
    integral_congr_ae (Eventually.of_forall fun x => iP _ _ _)
  have cV : ∀ (n : ℕ), (∫ x, traceMul (H n x) (detTwo (tens (cfm (e n) x) (cfm (e n) x))
      (tens (cfm (e n) x) (cfm (e n) x))) ∂ν) =
      ∫ x, (cfm (e n) x).det * Matrix.trace (H n x) ∂ν := fun n =>
    integral_congr_ae (Eventually.of_forall fun x => iV _ _)
  have cV' : (∫ x, traceMul (H' x) (detTwo (tens (cfm e' x) (cfm e' x))
      (tens (cfm e' x) (cfm e' x))) ∂ν) = ∫ x, (cfm e' x).det * Matrix.trace (H' x) ∂ν :=
    integral_congr_ae (Eventually.of_forall fun x => iV _ _)
  refine ⟨(tH.congr cH).mono_right (le_of_eq (congrArg 𝓝 cH')),
    (tP.congr cP).mono_right (le_of_eq (congrArg 𝓝 cP')),
    (tV.congr cV).mono_right (le_of_eq (congrArg 𝓝 cV')), ?_, ?_, ?_⟩
  · have := ((ContinuousLinearMap.apply ℝ ℝ : Arr4 →L[ℝ] (Arr4 →L[ℝ] ℝ) →L[ℝ] ℝ).memLp_of_bilin 1
      hRr' hGH.memLp_lim).integrable le_rfl
    exact this.congr (Eventually.of_forall fun x => iH _ _ _)
  · have := ((ContinuousLinearMap.apply ℝ ℝ : Arr4 →L[ℝ] (Arr4 →L[ℝ] ℝ) →L[ℝ] ℝ).memLp_of_bilin 1
      hRr' hGP.memLp_lim).integrable le_rfl
    exact this.congr (Eventually.of_forall fun x => iP _ _ _)
  · have := hV.memLp_lim.integrable le_rfl
    exact this.congr (Eventually.of_forall fun x => iV _ _)

end Passage

end RenewalGeometry
