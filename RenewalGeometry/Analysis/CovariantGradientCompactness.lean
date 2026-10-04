/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevBoxCompactness
import RenewalGeometry.Analysis.LpProductContinuity

/-!
# Covariant-gradient compactness (`prop:covariant-higgs-endpoint`)

Generic infrastructure (no renewal notions) for `prop:covariant-higgs-endpoint` of the
Einstein–SM action-closure manuscript.

**Multipliers by `L⁴` coefficients** (any measure space):
* `eLpNorm_mul_le_L4`: Hölder `‖α w‖_2 ≤ ‖α‖_4 ‖w‖_4`;
* `exists_relative_multiplier`: the **relative multiplier estimate** `eq:relative-multiplier`
  in the form `‖α w‖_2 ≤ ε ‖w‖_4 + C_ε ‖w‖_2` for a fixed `α ∈ L⁴` (truncate `α` at a level `M`);
  combined with the critical Sobolev embedding `H¹(Q) ↪ L⁴(Q)` this is
  `‖α w‖_2 ≤ ε C_S ‖w‖_{H¹} + C_ε ‖w‖_2`;
* `tendsto_eLpNorm_mul_of_L4`: multiplication by a fixed `L⁴` coefficient maps `L⁴`-bounded,
  `L²`-null sequences to `L²`-null sequences (compactness of `H¹ → L²`, `w ↦ α w`).

**Weak derivatives**: `HasWeakPartial.sub`, `MemW12.sub`, `hasWeakPartial_of_tendsto`
(weak partials pass to `L²(Ω)` limits).

**The proposition** (box rendering of the bounded chart `K`, `Q = Π (a_i, b_i) ⊂ ℝ⁴`, fields with
`m` complex components, connection through the matrix entries `A μ c e = ρ_H(A_μ)_{ce}`,
`D_A H = ∂H + A H` (`covD`)):
* `covariant_eventually_bounded`: the graph estimate with absorption — `A_h → A₀` in `L⁴(Q)`,
  `sup ‖H_h‖_{L²(Q)} < ∞`, `D_{A_h} H_h → Y` in `L²(Q)` give an eventual uniform `H¹(Q)` bound
  (relative multiplier estimate + critical Sobolev `H¹(Q) ↪ L⁴(Q)`);
* `covariant_core`: identification `Y = D_{A₀} H₀` (`covGrad`) and strong `H¹(Q)`, `L⁴(Q)`
  convergence once `L²(Q)` convergence is known;
* `covariant_higgs_endpoint_box` (main statement: convergent subsequence, `Y = D_{A₀} H₀`, strong
  `H¹` and `L⁴` convergence), `covariant_higgs_endpoint_box_precompact` (every subsequence),
  `covariant_higgs_endpoint_box_of_L2` (whole sequence when `H_h → H₀` in `L²(Q)`);
* `higgs_densities_tendsto`: quadratic, quartic and covariant-kinetic Higgs densities converge in
  `L²`/`L¹` (the potential and the stress are fixed linear combinations of these).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

/-! ### Multipliers by `L⁴` coefficients -/

section Multiplier

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

instance holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  have := holderTriple_ofReal (p := 4) (q := 4) (r := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using this

/-- Hölder: `‖α w‖_{L²} ≤ ‖α‖_{L⁴} ‖w‖_{L⁴}`. -/
theorem eLpNorm_mul_le_L4 {α w : X → ℂ} (hα : AEStronglyMeasurable α μ)
    (hw : AEStronglyMeasurable w μ) :
    eLpNorm (fun x => α x * w x) 2 μ ≤ eLpNorm α 4 μ * eLpNorm w 4 μ := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hw hα
  have e : (α • w) = fun x => α x * w x := by funext x; simp [smul_eq_mul]
  rwa [e] at h

/-- **Relative multiplier estimate** (`eq:relative-multiplier`): for a fixed `α ∈ L⁴` and every
`ε > 0` there is `C_ε` with `‖α w‖_2 ≤ ε ‖w‖_4 + C_ε ‖w‖_2` for all `w`. -/
theorem exists_relative_multiplier {α : X → ℂ} (hα : MemLp α 4 μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : ℝ≥0, ∀ w : X → ℂ, AEStronglyMeasurable w μ →
      eLpNorm (fun x => α x * w x) 2 μ ≤ ε * eLpNorm w 4 μ + C * eLpNorm w 2 μ := by
  set α' := hα.1.mk α
  have hα'm : StronglyMeasurable α' := hα.1.stronglyMeasurable_mk
  have hαe : α =ᵐ[μ] α' := hα.1.ae_eq_mk
  -- the tails `1_{‖α'‖ > n} α'` tend to zero in `L⁴`
  set T : ℕ → X → ℂ := fun n => {x | (n : ℝ) < ‖α' x‖}.indicator α'
  have hTm : ∀ n, MeasurableSet {x | (n : ℝ) < ‖α' x‖} := fun n =>
    measurableSet_lt measurable_const hα'm.measurable.norm
  have hT : Tendsto (fun n => eLpNorm (T n) 4 μ) atTop (𝓝 0) := by
    refine LpProductContinuity.tendsto_eLpNorm_of_dominated_ae (by norm_num) (by norm_num)
      (fun n => hα'm.aestronglyMeasurable.indicator (hTm n)) (g := fun x => ‖α' x‖)
      ((hα.ae_eq hαe).norm) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact norm_indicator_le_norm_self α' x
    · obtain ⟨N, hN⟩ := exists_nat_ge ‖α' x‖
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have : ¬ (n : ℝ) < ‖α' x‖ := not_lt.mpr (hN.trans (by exact_mod_cast hn))
      simp [T, this]
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp hT ε (pos_iff_ne_zero.mpr hε)).exists
  refine ⟨n, fun w hw => ?_⟩
  -- split `α = T n + (α - T n)` with `|α - T n| ≤ n` a.e.
  have hsplit : (fun x => α x * w x) =ᵐ[μ]
      fun x => T n x * w x + (α' x - T n x) * w x := by
    filter_upwards [hαe] with x hx
    rw [hx]; ring
  rw [eLpNorm_congr_ae hsplit]
  have hTnm : AEStronglyMeasurable (T n) μ := hα'm.aestronglyMeasurable.indicator (hTm n)
  refine (eLpNorm_add_le (hTnm.mul hw) ((hα'm.aestronglyMeasurable.sub hTnm).mul hw)
    (by norm_num)).trans (add_le_add ?_ ?_)
  · exact (eLpNorm_mul_le_L4 hTnm hw).trans (by gcongr)
  · refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
    simp only [Pi.mul_apply, Pi.sub_apply]
    rw [nnnorm_mul]
    gcongr
    by_cases hx : (n : ℝ) < ‖α' x‖
    · simp [T, hx]
    · have : T n x = 0 := by simp [T, hx]
      rw [this, sub_zero, ← NNReal.coe_le_coe, coe_nnnorm]
      push_cast
      exact not_lt.mp hx

/-- **Compact multiplication by a fixed `L⁴` coefficient**: if `w_k` is bounded in `L⁴` and
`w_k → 0` in `L²`, then `α w_k → 0` in `L²` for every `α ∈ L⁴`. -/
theorem tendsto_eLpNorm_mul_of_L4 {α : X → ℂ} (hα : MemLp α 4 μ) {w : ℕ → X → ℂ}
    (hw : ∀ k, AEStronglyMeasurable (w k) μ) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hwK : ∀ k, eLpNorm (w k) 4 μ ≤ K) (hw2 : Tendsto (fun k => eLpNorm (w k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => α x * w k x) 2 μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- choose `δ` with `δ K ≤ ε / 2`
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ δ * K ≤ ε / 2 := by
    by_cases hK0 : K = 0
    · exact ⟨1, one_ne_zero, by simp [hK0]⟩
    · refine ⟨ε / 2 / K, ?_, ?_⟩
      · exact ENNReal.div_pos_iff.mpr ⟨(ENNReal.half_pos hε.ne').ne', hK⟩ |>.ne'
      · exact ENNReal.div_mul_cancel hK0 hK |>.le
  obtain ⟨C, hC⟩ := exists_relative_multiplier hα hδ0
  have hlim : Tendsto (fun k => (C : ℝ≥0∞) * eLpNorm (w k) 2 μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hw2 (Or.inr ENNReal.coe_ne_top)
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hlim) (ε / 2)
    (ENNReal.half_pos hε.ne')] with k hk
  calc eLpNorm (fun x => α x * w k x) 2 μ ≤ δ * eLpNorm (w k) 4 μ + C * eLpNorm (w k) 2 μ :=
        hC _ (hw k)
    _ ≤ δ * K + ε / 2 := by gcongr; exact hwK k
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

end Multiplier

/-! ### Weak derivatives: differences and limits -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem HasWeakPartial.sub {Ω : Set (ι → ℝ)} {i : ι} {u g u' g' : (ι → ℝ) → ℂ}
    (h : HasWeakPartial Ω i u g) (h' : HasWeakPartial Ω i u' g')
    (hu : LocallyIntegrableOn u Ω) (hu' : LocallyIntegrableOn u' Ω)
    (hg : LocallyIntegrableOn g Ω) (hg' : LocallyIntegrableOn g' Ω) :
    HasWeakPartial Ω i (fun x => u x - u' x) (fun x => g x - g' x) := by
  intro φ hφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hpdt : tsupport (fun x => ((pd φ i x : ℝ) : ℂ)) ⊆ Ω :=
    (tsupport_comp_subset Complex.ofReal_zero _).trans
      ((tsupport_pd_subset φ i).trans hφ.subset)
  have hpdc : HasCompactSupport (fun x => ((pd φ i x : ℝ) : ℂ)) :=
    (hasCompactSupport_pd hφ.compact i).comp_left Complex.ofReal_zero
  have hpdcont : Continuous (fun x => ((pd φ i x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_pd hφ1 i)
  have hφt : tsupport (fun x => ((φ x : ℝ) : ℂ)) ⊆ Ω :=
    (tsupport_comp_subset Complex.ofReal_zero _).trans hφ.subset
  have hφc : HasCompactSupport (fun x => ((φ x : ℝ) : ℂ)) :=
    hφ.compact.comp_left Complex.ofReal_zero
  have hφcont : Continuous (fun x => ((φ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hφ1.continuous
  simp only [mul_sub]
  rw [integral_sub (integrable_mul_of_locallyIntegrableOn hu hpdcont hpdc hpdt)
    (integrable_mul_of_locallyIntegrableOn hu' hpdcont hpdc hpdt),
    integral_sub (integrable_mul_of_locallyIntegrableOn hg hφcont hφc hφt)
    (integrable_mul_of_locallyIntegrableOn hg' hφcont hφc hφt), h φ hφ, h' φ hφ]
  ring

theorem MemW12.sub {Ω : Set (ι → ℝ)} {u u' : (ι → ℝ) → ℂ} {g g' : ι → (ι → ℝ) → ℂ}
    (hW : MemW12 Ω u g) (hW' : MemW12 Ω u' g') :
    MemW12 Ω (fun x => u x - u' x) (fun i x => g i x - g' i x) :=
  ⟨hW.memLp.sub hW'.memLp, fun i => (hW.memLp_grad i).sub (hW'.memLp_grad i), fun i =>
    (hW.weak i).sub (hW'.weak i) (locallyIntegrableOn_of_memLp hW.memLp)
      (locallyIntegrableOn_of_memLp hW'.memLp) (locallyIntegrableOn_of_memLp (hW.memLp_grad i))
      (locallyIntegrableOn_of_memLp (hW'.memLp_grad i))⟩

/-- Test functions differentiate into test functions. -/
theorem IsTest.pd {Ω : Set (ι → ℝ)} {φ : (ι → ℝ) → ℝ} (hφ : IsTest Ω φ) (i : ι) :
    IsTest Ω (pd φ i) :=
  ⟨contDiff_pd hφ.smooth i, hasCompactSupport_pd hφ.compact i,
    (tsupport_pd_subset φ i).trans hφ.subset⟩

/-- **Weak derivatives pass to `L²` limits** (on `Ω` of finite measure): if `u_k → u` and
`g_k → g` in `L²(Ω)` and `g_k` is the weak `i`-th partial of `u_k`, then `g` is that of `u`. -/
theorem hasWeakPartial_of_tendsto {Ω : Set (ι → ℝ)} (hΩm : MeasurableSet Ω) (hΩf : volume Ω ≠ ⊤)
    {i : ι} {u g : ℕ → (ι → ℝ) → ℂ} {u' g' : (ι → ℝ) → ℂ}
    (hw : ∀ k, HasWeakPartial Ω i (u k) (g k)) (hu : ∀ k, MemLp (u k) 2 (volume.restrict Ω))
    (hg : ∀ k, MemLp (g k) 2 (volume.restrict Ω)) (hu' : MemLp u' 2 (volume.restrict Ω))
    (hg' : MemLp g' 2 (volume.restrict Ω))
    (hul : Tendsto (fun k => eLpNorm (u k - u') 2 (volume.restrict Ω)) atTop (𝓝 0))
    (hgl : Tendsto (fun k => eLpNorm (g k - g') 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    HasWeakPartial Ω i u' g' := by
  intro φ hφ
  have h1 := tendsto_integral_test_of_L2 hΩm hΩf (hφ.pd i) hu hu' hul
  have h2 := (tendsto_integral_test_of_L2 hΩm hΩf hφ hg hg' hgl).neg
  exact tendsto_nhds_unique (h1.congr fun k => hw k φ hφ) h2


/-! ### The covariant gradient on a box -/

/-- The covariant derivative `(D_A H)^c_μ = ∂_μ H^c + Σ_e (ρ(A_μ))_{ce} H^e` of an `m`-component
field with weak gradient `dH`, for a connection given by its matrix entries
`A μ c e = (ρ_H(A_μ))_{ce}`. -/
def covD {m : ℕ} (dH : Fin m → ι → (ι → ℝ) → ℂ) (A : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (H : Fin m → (ι → ℝ) → ℂ) (c : Fin m) (μ : ι) (x : ι → ℝ) : ℂ :=
  dH c μ x + ∑ e, A μ c e x * H e x

theorem covD_def {m : ℕ} (dH : Fin m → ι → (ι → ℝ) → ℂ) (A : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (H : Fin m → (ι → ℝ) → ℂ) (c : Fin m) (μ : ι) :
    covD dH A H c μ = fun x => dH c μ x + ∑ e, A μ c e x * H e x := rfl

theorem aestronglyMeasurable_covD {m : ℕ} {ν : Measure (ι → ℝ)}
    {dH : Fin m → ι → (ι → ℝ) → ℂ} {A : ι → Fin m → Fin m → (ι → ℝ) → ℂ}
    {H : Fin m → (ι → ℝ) → ℂ} (hdH : ∀ c μ, AEStronglyMeasurable (dH c μ) ν)
    (hA : ∀ μ c e, AEStronglyMeasurable (A μ c e) ν) (hH : ∀ e, AEStronglyMeasurable (H e) ν)
    (c : Fin m) (μ : ι) : AEStronglyMeasurable (covD dH A H c μ) ν := by
  unfold covD
  refine (hdH c μ).add ?_
  have : AEStronglyMeasurable (∑ e, fun x => A μ c e x * H e x) ν :=
    Finset.aestronglyMeasurable_sum _ fun e _ => (hA μ c e).mul (hH e)
  convert this using 1
  funext x; simp [Finset.sum_apply]

/-- `∂_μ H^c = D_μ H^c - Σ_e A_{μce} H^e`, hence
`‖∂_μ H^c‖_2 ≤ ‖D_μ H^c‖_2 + Σ_e ‖A_{μce} H^e‖_2`. -/
theorem eLpNorm_grad_le_covD {m : ℕ} {ν : Measure (ι → ℝ)}
    {dH : Fin m → ι → (ι → ℝ) → ℂ} {A : ι → Fin m → Fin m → (ι → ℝ) → ℂ}
    {H : Fin m → (ι → ℝ) → ℂ} (hdH : ∀ c μ, AEStronglyMeasurable (dH c μ) ν)
    (hA : ∀ μ c e, AEStronglyMeasurable (A μ c e) ν) (hH : ∀ e, AEStronglyMeasurable (H e) ν)
    (c : Fin m) (μ : ι) :
    eLpNorm (dH c μ) 2 ν ≤ eLpNorm (covD dH A H c μ) 2 ν +
      ∑ e, eLpNorm (fun x => A μ c e x * H e x) 2 ν := by
  have e1 : dH c μ = covD dH A H c μ - ∑ e, fun x => A μ c e x * H e x := by
    funext x; simp [covD, Finset.sum_apply]
  rw [e1]
  refine (eLpNorm_sub_le (aestronglyMeasurable_covD hdH hA hH c μ)
    (Finset.aestronglyMeasurable_sum _ fun e _ => (hA μ c e).mul (hH e)) (by norm_num)).trans ?_
  gcongr
  exact eLpNorm_sum_le (fun e _ => (hA μ c e).mul (hH e)) (by norm_num)

/-- Critical Sobolev constant `H¹(Q) ↪ L⁴(Q)` in four dimensions. -/
theorem exists_sobolev_L4_box (hd : Fintype.card ι = 4) {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    ∃ C : ℝ≥0, ∀ (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ), MemW12 (box a b) u g →
      eLpNorm u 4 (volume.restrict (box a b)) ≤ C * w12Norm (box a b) u g := by
  have := eLpNorm_le_box hab (by rw [hd]; norm_num) (p' := 4) (by rw [hd]; norm_num)
  simpa using this

/-- **Uniform `H¹(Q)` bound from covariant control** (graph estimate with absorption): under
`A_h → A₀` in `L⁴(Q)`, `sup_h ‖H_h‖_{L²(Q)} ≤ B` and `D_{A_h} H_h → Y` in `L²(Q)`, the
`W^{1,2}(Q)` norms of `H_h` are eventually uniformly bounded. -/
theorem covariant_eventually_bounded (hd : Fintype.card ι = 4) {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) {m : ℕ} (H : ℕ → Fin m → (ι → ℝ) → ℂ)
    (dH : ℕ → Fin m → ι → (ι → ℝ) → ℂ) (A : ℕ → ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (A₀ : ι → Fin m → Fin m → (ι → ℝ) → ℂ) (Y : Fin m → ι → (ι → ℝ) → ℂ)
    (hW : ∀ h c, MemW12 (box a b) (H h c) (dH h c))
    (hA : ∀ h μ c e, MemLp (A h μ c e) 4 (volume.restrict (box a b)))
    (hA₀ : ∀ μ c e, MemLp (A₀ μ c e) 4 (volume.restrict (box a b)))
    (hAlim : ∀ μ c e, Tendsto (fun h => eLpNorm (A h μ c e - A₀ μ c e) 4
      (volume.restrict (box a b))) atTop (𝓝 0))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤) (hHB : ∀ h c, eLpNorm (H h c) 2 (volume.restrict (box a b)) ≤ B)
    (hY : ∀ c μ, MemLp (Y c μ) 2 (volume.restrict (box a b)))
    (hYlim : ∀ c μ, Tendsto (fun h => eLpNorm (covD (dH h) (A h) (H h) c μ - Y c μ) 2
      (volume.restrict (box a b))) atTop (𝓝 0)) :
    ∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ᶠ h in atTop, ∀ c, w12Norm (box a b) (H h c) (dH h c) ≤ N := by
  set ν := volume.restrict (box a b)
  obtain ⟨CS, hCS⟩ := exists_sobolev_L4_box hd hab
  -- choose `δ` with `m d m δ CS ≤ 1/4`
  set κ : ℝ≥0 := (m : ℝ≥0) * (Fintype.card ι : ℝ≥0) * m * CS
  set δ : ℝ≥0 := (4 * (κ + 1))⁻¹
  have hδ0 : δ ≠ 0 := by simp [δ]
  have hκδ : κ * δ ≤ 4⁻¹ := by
    simp only [δ]
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have : (4 : ℝ≥0)⁻¹ * (4 * (κ + 1)) = κ + 1 := by
      rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (4 : ℝ≥0) ≠ 0), one_mul]
    rw [this]
    exact le_add_of_nonneg_right zero_le_one
  choose C hC using fun (t : ι × Fin m × Fin m) =>
    exists_relative_multiplier (hA₀ t.1 t.2.1 t.2.2) (ε := (δ : ℝ≥0∞)) (by exact_mod_cast hδ0)
  set Ctot : ℝ≥0 := ∑ t : ι × Fin m × Fin m, C t
  -- `Θ_h = Σ ‖A_h - A₀‖_4 → 0`
  set Θ : ℕ → ℝ≥0∞ := fun h => ∑ t : ι × Fin m × Fin m,
    eLpNorm (A h t.1 t.2.1 t.2.2 - A₀ t.1 t.2.1 t.2.2) 4 ν
  have hΘ : Tendsto Θ atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (ι × Fin m × Fin m))
      fun t _ => hAlim t.1 t.2.1 t.2.2
    simpa using this
  have hΘev : ∀ᶠ h in atTop,
      (m : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞) * Θ h * CS ≤ 4⁻¹ := by
    have hlim : Tendsto (fun h => (m : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞) * Θ h * CS) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun h => Θ h * (CS : ℝ≥0∞)) atTop (𝓝 (0 * CS)) :=
        ENNReal.Tendsto.mul_const hΘ (Or.inr ENNReal.coe_ne_top)
      have h2 := ENNReal.Tendsto.const_mul h1 (a := (m : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞))
        (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (ENNReal.natCast_ne_top _)))
      simpa [mul_assoc] using h2
    exact (ENNReal.tendsto_nhds_zero.mp hlim) 4⁻¹ (by norm_num)
  -- eventually `‖D_h‖ ≤ ‖Y‖ + 1`
  have hDev : ∀ᶠ h in atTop, ∀ c μ, eLpNorm (covD (dH h) (A h) (H h) c μ) 2 ν ≤
      eLpNorm (Y c μ) 2 ν + 1 := by
    have : ∀ c μ, ∀ᶠ h in atTop, eLpNorm (covD (dH h) (A h) (H h) c μ) 2 ν ≤
        eLpNorm (Y c μ) 2 ν + 1 := by
      intro c μ
      filter_upwards [(ENNReal.tendsto_nhds_zero.mp (hYlim c μ)) 1 one_pos] with h hh
      have hm := aestronglyMeasurable_covD (fun c μ => ((hW h c).memLp_grad μ).1)
        (fun μ c e => (hA h μ c e).1) (fun e => (hW h e).memLp.1) c μ
      calc eLpNorm (covD (dH h) (A h) (H h) c μ) 2 ν
          = eLpNorm (Y c μ + (covD (dH h) (A h) (H h) c μ - Y c μ)) 2 ν := by
            congr 1; abel
        _ ≤ eLpNorm (Y c μ) 2 ν + eLpNorm (covD (dH h) (A h) (H h) c μ - Y c μ) 2 ν :=
            eLpNorm_add_le (hY c μ).1 (hm.sub (hY c μ).1) (by norm_num)
        _ ≤ eLpNorm (Y c μ) 2 ν + 1 := by gcongr
    exact Filter.eventually_all.mpr fun c => Filter.eventually_all.mpr fun μ => this c μ
  set c₀ : ℝ≥0∞ := m * B + (∑ c, ∑ μ, (eLpNorm (Y c μ) 2 ν + 1)) +
    m * (Fintype.card ι : ℝ≥0∞) * (Ctot * B)
  have hc₀ : c₀ ≠ ⊤ := by
    have hY' : ∀ c μ, eLpNorm (Y c μ) 2 ν + 1 ≠ ⊤ := fun c μ =>
      ENNReal.add_ne_top.mpr ⟨(hY c μ).eLpNorm_ne_top, ENNReal.one_ne_top⟩
    simp only [c₀]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) hBt,
      ENNReal.sum_ne_top.mpr fun c _ => ENNReal.sum_ne_top.mpr fun μ _ => hY' c μ⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m)
        (ENNReal.natCast_ne_top _)) (ENNReal.mul_ne_top ENNReal.coe_ne_top hBt)⟩
  refine ⟨2 * c₀, ENNReal.mul_ne_top (by norm_num) hc₀, ?_⟩
  filter_upwards [hΘev, hDev] with h hΘh hDh
  -- the total norm `S_h`
  set S := ∑ c, w12Norm (box a b) (H h c) (dH h c) with hSdef
  have hSt : S ≠ ⊤ := ENNReal.sum_ne_top.mpr fun c _ => by
    unfold w12Norm
    exact ENNReal.add_ne_top.mpr ⟨(hW h c).memLp.eLpNorm_ne_top,
      ENNReal.sum_ne_top.mpr fun μ _ => ((hW h c).memLp_grad μ).eLpNorm_ne_top⟩
  have hSe : ∀ e, w12Norm (box a b) (H h e) (dH h e) ≤ S := fun e =>
    Finset.single_le_sum (f := fun c => w12Norm (box a b) (H h c) (dH h c))
      (fun _ _ => zero_le) (Finset.mem_univ e)
  have hL4 : ∀ e, eLpNorm (H h e) 4 ν ≤ CS * S := fun e =>
    (hCS _ _ (hW h e)).trans (by gcongr; exact hSe e)
  -- the product bound for one entry
  have hAH : ∀ μ c e, eLpNorm (fun x => A h μ c e x * H h e x) 2 ν ≤
      (eLpNorm (A h μ c e - A₀ μ c e) 4 ν + δ) * (CS * S) + C (μ, c, e) * B := by
    intro μ c e
    have hm := (hW h e).memLp.1
    have hsplit : (fun x => A h μ c e x * H h e x) =
        fun x => (A h μ c e - A₀ μ c e) x * H h e x + A₀ μ c e x * H h e x := by
      funext x; simp only [Pi.sub_apply]; ring
    rw [hsplit]
    refine (eLpNorm_add_le (((hA h μ c e).1.sub (hA₀ μ c e).1).mul hm) ((hA₀ μ c e).1.mul hm)
      (by norm_num)).trans ?_
    have h1 := eLpNorm_mul_le_L4 ((hA h μ c e).1.sub (hA₀ μ c e).1) hm
    have h2 := hC (μ, c, e) (H h e) hm
    calc eLpNorm (fun x => (A h μ c e - A₀ μ c e) x * H h e x) 2 ν +
          eLpNorm (fun x => A₀ μ c e x * H h e x) 2 ν
        ≤ eLpNorm (A h μ c e - A₀ μ c e) 4 ν * eLpNorm (H h e) 4 ν +
          (δ * eLpNorm (H h e) 4 ν + C (μ, c, e) * eLpNorm (H h e) 2 ν) := add_le_add h1 h2
      _ ≤ eLpNorm (A h μ c e - A₀ μ c e) 4 ν * (CS * S) +
          (δ * (CS * S) + C (μ, c, e) * B) := by
          gcongr
          · exact hL4 e
          · exact hL4 e
          · exact hHB h e
      _ = (eLpNorm (A h μ c e - A₀ μ c e) 4 ν + δ) * (CS * S) + C (μ, c, e) * B := by ring
  -- the gradient bound
  have hgrad : ∀ c μ, eLpNorm (dH h c μ) 2 ν ≤ eLpNorm (Y c μ) 2 ν + 1 +
      (Θ h + m * δ) * (CS * S) + Ctot * B := by
    intro c μ
    refine (eLpNorm_grad_le_covD (fun c μ => ((hW h c).memLp_grad μ).1)
      (fun μ c e => (hA h μ c e).1) (fun e => (hW h e).memLp.1) c μ).trans ?_
    have hsum : ∑ e, eLpNorm (fun x => A h μ c e x * H h e x) 2 ν ≤
        (Θ h + m * δ) * (CS * S) + Ctot * B := by
      refine (Finset.sum_le_sum fun e _ => hAH μ c e).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have hθ : ∑ e, (eLpNorm (A h μ c e - A₀ μ c e) 4 ν + (δ : ℝ≥0∞)) ≤ Θ h + m * δ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        gcongr
        exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun t : ι × Fin m × Fin m =>
          eLpNorm (A h t.1 t.2.1 t.2.2 - A₀ t.1 t.2.1 t.2.2) 4 ν)
          (s := Finset.univ.image fun e => (μ, c, e)) (t := Finset.univ) (Finset.subset_univ _)
          (fun _ _ _ => zero_le) |>.trans_eq' (by
            rw [Finset.sum_image (fun e _ e' _ h => by simpa using h)])
      have hC' : ∑ e, (C (μ, c, e) : ℝ≥0∞) * B ≤ Ctot * B := by
        rw [← Finset.sum_mul]
        gcongr
        have : ∑ e, (C (μ, c, e) : ℝ≥0∞) = ((∑ e, C (μ, c, e) : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
        rw [this]
        exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg (f := fun t : ι × Fin m × Fin m => C t)
          (s := Finset.univ.image fun e => (μ, c, e)) (t := Finset.univ) (Finset.subset_univ _)
          (fun _ _ _ => zero_le) |>.trans_eq' (by
            rw [Finset.sum_image (fun e _ e' _ h => by simpa using h)])
      exact add_le_add (by gcongr) hC'
    calc eLpNorm (covD (dH h) (A h) (H h) c μ) 2 ν +
          ∑ e, eLpNorm (fun x => A h μ c e x * H h e x) 2 ν
        ≤ (eLpNorm (Y c μ) 2 ν + 1) + ((Θ h + m * δ) * (CS * S) + Ctot * B) :=
          add_le_add (hDh c μ) hsum
      _ = _ := by ring
  -- absorption
  have h4 : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ = 2⁻¹ := by
    have : (4 : ℝ≥0∞)⁻¹ = 2⁻¹ * 2⁻¹ := by
      rw [← ENNReal.mul_inv (by simp) (by simp)]; norm_num
    rw [this, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  have hq : (m : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞) * (Θ h + m * δ) * CS ≤ 2⁻¹ := by
    have e2 : (m : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞) * (Θ h + m * δ) * CS =
        m * (Fintype.card ι : ℝ≥0∞) * Θ h * CS + ((κ * δ : ℝ≥0) : ℝ≥0∞) := by
      simp only [κ]; push_cast; ring
    rw [e2, ← h4]
    gcongr
    have : ((κ * δ : ℝ≥0) : ℝ≥0∞) ≤ ((4⁻¹ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hκδ
    simpa using this
  have hSle : S ≤ c₀ + 2⁻¹ * S := by
    have h1 : S ≤ ∑ c, (B + ∑ μ, (eLpNorm (Y c μ) 2 ν + 1 +
        (Θ h + m * δ) * (CS * S) + Ctot * B)) := by
      refine Finset.sum_le_sum fun c _ => ?_
      unfold w12Norm
      exact add_le_add (hHB h c) (Finset.sum_le_sum fun μ _ => hgrad c μ)
    have h2 : ∑ c, (B + ∑ μ, (eLpNorm (Y c μ) 2 ν + 1 +
        (Θ h + m * δ) * (CS * S) + Ctot * B)) =
        c₀ + ((m : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞) * (Θ h + m * δ) * CS) * S := by
      simp only [c₀, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    calc S ≤ _ := h1
      _ = _ := h2
      _ ≤ c₀ + 2⁻¹ * S := by gcongr
  have hS2 : S = 2⁻¹ * S + 2⁻¹ * S := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  have hhalf : 2⁻¹ * S ≤ c₀ := by
    have hne : 2⁻¹ * S ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hSt
    have h3 : 2⁻¹ * S + 2⁻¹ * S ≤ c₀ + 2⁻¹ * S := by rw [← hS2]; exact hSle
    exact (ENNReal.add_le_add_iff_right hne).mp h3
  intro c
  calc w12Norm (box a b) (H h c) (dH h c) ≤ S := hSe c
    _ = 2⁻¹ * S + 2⁻¹ * S := hS2
    _ ≤ c₀ + c₀ := add_le_add hhalf hhalf
    _ = 2 * c₀ := (two_mul c₀).symm


/-- The gradient forced by the covariant limit: `∂_μ H^c = Y^c_μ - Σ_e A_{μce} H^e`. -/
def covGrad {m : ℕ} (Y : Fin m → ι → (ι → ℝ) → ℂ) (A₀ : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (H₀ : Fin m → (ι → ℝ) → ℂ) (c : Fin m) (μ : ι) (x : ι → ℝ) : ℂ :=
  Y c μ x - ∑ e, A₀ μ c e x * H₀ e x

theorem covD_covGrad {m : ℕ} (Y : Fin m → ι → (ι → ℝ) → ℂ)
    (A₀ : ι → Fin m → Fin m → (ι → ℝ) → ℂ) (H₀ : Fin m → (ι → ℝ) → ℂ) (c : Fin m) (μ : ι)
    (x : ι → ℝ) : covD (covGrad Y A₀ H₀) A₀ H₀ c μ x = Y c μ x := by
  simp [covD, covGrad]

/-- **Core of `prop:covariant-higgs-endpoint`**: if in addition to the covariant hypotheses the
fields are uniformly bounded in `W^{1,2}(Q)` and converge in `L²(Q)` to `H₀`, then `H₀ ∈ H¹(Q)`
with weak gradient `Y - A₀ H₀` (i.e. `Y = D_{A₀} H₀`), and the convergence is strong in `H¹(Q)` and
in `L⁴(Q)`. -/
theorem covariant_core (hd : Fintype.card ι = 4) {a b : ι → ℝ} (hab : ∀ i, a i < b i) {m : ℕ}
    (H : ℕ → Fin m → (ι → ℝ) → ℂ) (dH : ℕ → Fin m → ι → (ι → ℝ) → ℂ)
    (A : ℕ → ι → Fin m → Fin m → (ι → ℝ) → ℂ) (A₀ : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (Y : Fin m → ι → (ι → ℝ) → ℂ) (hW : ∀ h c, MemW12 (box a b) (H h c) (dH h c))
    (hA : ∀ h μ c e, MemLp (A h μ c e) 4 (volume.restrict (box a b)))
    (hA₀ : ∀ μ c e, MemLp (A₀ μ c e) 4 (volume.restrict (box a b)))
    (hAlim : ∀ μ c e, Tendsto (fun h => eLpNorm (A h μ c e - A₀ μ c e) 4
      (volume.restrict (box a b))) atTop (𝓝 0))
    (hY : ∀ c μ, MemLp (Y c μ) 2 (volume.restrict (box a b)))
    (hYlim : ∀ c μ, Tendsto (fun h => eLpNorm (covD (dH h) (A h) (H h) c μ - Y c μ) 2
      (volume.restrict (box a b))) atTop (𝓝 0))
    {N : ℝ≥0∞} (hNt : N ≠ ⊤) (hN : ∀ h c, w12Norm (box a b) (H h c) (dH h c) ≤ N)
    (H₀ : Fin m → (ι → ℝ) → ℂ) (hH₀ : ∀ c, MemLp (H₀ c) 2 (volume.restrict (box a b)))
    (hL2 : ∀ c, Tendsto (fun h => eLpNorm (H h c - H₀ c) 2 (volume.restrict (box a b))) atTop
      (𝓝 0)) :
    (∀ c, MemW12 (box a b) (H₀ c) (covGrad Y A₀ H₀ c)) ∧
      (∀ c μ, Tendsto (fun h => eLpNorm (dH h c μ - covGrad Y A₀ H₀ c μ) 2
        (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      (∀ c, Tendsto (fun h => eLpNorm (H h c - H₀ c) 4 (volume.restrict (box a b))) atTop
        (𝓝 0)) := by
  set ν := volume.restrict (box a b)
  have hQm : MeasurableSet (box a b) := (isOpen_box a b).measurableSet
  have hQf : volume (box a b) ≠ ⊤ := volume_box_ne_top a b
  obtain ⟨CS, hCS⟩ := exists_sobolev_L4_box hd hab
  set K4 : ℝ≥0∞ := CS * N
  have hK4 : K4 ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hNt
  have hH4 : ∀ h c, eLpNorm (H h c) 4 ν ≤ K4 := fun h c =>
    (hCS _ _ (hW h c)).trans (mul_le_mul_of_nonneg_left (hN h c) zero_le)
  have hLT : ∀ c, LpTendsto ν 2 (fun h => H h c) (H₀ c) := fun c =>
    ⟨fun h => (hW h c).memLp, hH₀ c, hL2 c⟩
  have hH₀4 : ∀ c, eLpNorm (H₀ c) 4 ν ≤ K4 := fun c =>
    (hLT c).eLpNorm_le_of_bound (by norm_num) (fun h => hH4 h c)
  have hH₀L4 : ∀ c, MemLp (H₀ c) 4 ν := fun c => ⟨(hH₀ c).1, (hH₀4 c).trans_lt hK4.lt_top⟩
  -- products converge in `L²`
  have hprod : ∀ μ c e, Tendsto (fun h => eLpNorm (fun x => A h μ c e x * H h e x -
      A₀ μ c e x * H₀ e x) 2 ν) atTop (𝓝 0) := by
    intro μ c e
    have hsplit : ∀ h, (fun x => A h μ c e x * H h e x - A₀ μ c e x * H₀ e x) =
        fun x => (A h μ c e - A₀ μ c e) x * H h e x + A₀ μ c e x * (H h e - H₀ e) x := by
      intro h; funext x; simp only [Pi.sub_apply]; ring
    have t1 : Tendsto (fun h => eLpNorm (A h μ c e - A₀ μ c e) 4 ν * K4) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const (hAlim μ c e) (Or.inr hK4)
    have t2 := tendsto_eLpNorm_mul_of_L4 (hA₀ μ c e) (w := fun h => H h e - H₀ e)
      (fun h => (hW h e).memLp.1.sub (hH₀ e).1) (K := K4 + K4) (ENNReal.add_ne_top.mpr ⟨hK4, hK4⟩)
      (fun h => (eLpNorm_sub_le (hW h e).memLp.1 (hH₀ e).1 (by norm_num)).trans
        (add_le_add (hH4 h e) (hH₀4 e))) (hL2 e)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using t1.add t2) (fun h => zero_le) (fun h => ?_)
    rw [hsplit h]
    refine (eLpNorm_add_le (((hA h μ c e).1.sub (hA₀ μ c e).1).mul (hW h e).memLp.1)
      ((hA₀ μ c e).1.mul ((hW h e).memLp.1.sub (hH₀ e).1)) (by norm_num)).trans
      (add_le_add ?_ le_rfl)
    exact (eLpNorm_mul_le_L4 ((hA h μ c e).1.sub (hA₀ μ c e).1) (hW h e).memLp.1).trans
      (mul_le_mul_of_nonneg_left (hH4 h e) zero_le)
  -- gradients converge in `L²`
  have hgrad : ∀ c μ, Tendsto (fun h => eLpNorm (dH h c μ - covGrad Y A₀ H₀ c μ) 2 ν) atTop
      (𝓝 0) := by
    intro c μ
    have hdec : ∀ h, dH h c μ - covGrad Y A₀ H₀ c μ =
        (covD (dH h) (A h) (H h) c μ - Y c μ) -
          ∑ e, fun x => A h μ c e x * H h e x - A₀ μ c e x * H₀ e x := by
      intro h; funext x
      simp only [Pi.sub_apply, covD, covGrad, Finset.sum_apply, Finset.sum_sub_distrib]
      ring
    have hmD : ∀ h, AEStronglyMeasurable (covD (dH h) (A h) (H h) c μ) ν := fun h =>
      aestronglyMeasurable_covD (fun c μ => ((hW h c).memLp_grad μ).1)
        (fun μ c e => (hA h μ c e).1) (fun e => (hW h e).memLp.1) c μ
    have hmP : ∀ h e, AEStronglyMeasurable
        (fun x => A h μ c e x * H h e x - A₀ μ c e x * H₀ e x) ν := fun h e =>
      ((hA h μ c e).1.mul (hW h e).memLp.1).sub ((hA₀ μ c e).1.mul (hH₀ e).1)
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun e _ => hprod μ c e
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (hYlim c μ).add hsum) (fun h => zero_le) (fun h => ?_)
    rw [hdec h]
    refine (eLpNorm_sub_le ((hmD h).sub (hY c μ).1)
      (Finset.aestronglyMeasurable_sum _ fun e _ => hmP h e) (by norm_num)).trans ?_
    gcongr
    exact eLpNorm_sum_le (fun e _ => hmP h e) (by norm_num)
  -- the limit gradient is in `L²`
  have hGmem : ∀ c μ, MemLp (covGrad Y A₀ H₀ c μ) 2 ν := by
    intro c μ
    have : MemLp (∑ e, fun x => A₀ μ c e x * H₀ e x) 2 ν :=
      memLp_finsetSum' _ fun e _ => (hH₀L4 e).mul' (hA₀ μ c e)
    have h2 := (hY c μ).sub this
    convert h2 using 1
    funext x; simp [covGrad, Finset.sum_apply]
  -- weak derivatives pass to the limit
  have hW₀ : ∀ c, MemW12 (box a b) (H₀ c) (covGrad Y A₀ H₀ c) := fun c =>
    ⟨hH₀ c, fun μ => hGmem c μ, fun μ => hasWeakPartial_of_tendsto hQm hQf
      (fun h => (hW h c).weak μ) (fun h => (hW h c).memLp) (fun h => (hW h c).memLp_grad μ)
      (hH₀ c) (hGmem c μ) (hL2 c) (hgrad c μ)⟩
  refine ⟨hW₀, hgrad, fun c => ?_⟩
  -- `L⁴` through the Sobolev embedding of the differences
  have hdiff := fun h => (hW h c).sub (hW₀ c)
  have hb : ∀ h, eLpNorm (H h c - H₀ c) 4 ν ≤ CS * (eLpNorm (H h c - H₀ c) 2 ν +
      ∑ μ, eLpNorm (dH h c μ - covGrad Y A₀ H₀ c μ) 2 ν) := fun h => hCS _ _ (hdiff h)
  have hlim : Tendsto (fun h => (CS : ℝ≥0∞) * (eLpNorm (H h c - H₀ c) 2 ν +
      ∑ μ, eLpNorm (dH h c μ - covGrad Y A₀ H₀ c μ) 2 ν)) atTop (𝓝 0) := by
    have hs := tendsto_finsetSum (Finset.univ : Finset ι) fun μ _ => hgrad c μ
    have := ENNReal.Tendsto.const_mul ((hL2 c).add hs) (a := (CS : ℝ≥0∞))
      (Or.inr ENNReal.coe_ne_top)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun h => zero_le) hb

/-- Rellich on a box for finitely many component sequences at once (common subsequence). -/
theorem rellich_box_family {a b : ι → ℝ} (hab : ∀ i, a i < b i) {m : ℕ}
    (u : ℕ → Fin m → (ι → ℝ) → ℂ) (g : ℕ → Fin m → ι → (ι → ℝ) → ℂ)
    (hW : ∀ k c, MemW12 (box a b) (u k c) (g k c)) {B : ℝ≥0∞} (hBt : B ≠ ⊤)
    (hB : ∀ k c, w12Norm (box a b) (u k c) (g k c) ≤ B) :
    ∃ (φ : ℕ → ℕ) (v : Fin m → (ι → ℝ) → ℂ), StrictMono φ ∧ (∀ c, MemLp (v c) 2 volume) ∧
      ∀ c, Tendsto (fun k => eLpNorm (u (φ k) c - v c) 2 (volume.restrict (box a b))) atTop
        (𝓝 0) := by
  have key : ∀ n : ℕ, ∃ (φ : ℕ → ℕ) (v : Fin m → (ι → ℝ) → ℂ), StrictMono φ ∧
      ∀ c : Fin m, (c : ℕ) < n → MemLp (v c) 2 volume ∧
        Tendsto (fun k => eLpNorm (u (φ k) c - v c) 2 (volume.restrict (box a b))) atTop
          (𝓝 0) := by
    intro n
    induction n with
    | zero => exact ⟨id, fun _ => 0, strictMono_id, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨φ, v, hφ, hv⟩ := ih
      by_cases hn : n < m
      · obtain ⟨ψ, w, hψ, hw, hlim⟩ := rellich_box hab (fun k => u (φ k) ⟨n, hn⟩)
          (fun k => g (φ k) ⟨n, hn⟩) (fun k => hW _ _) hBt (fun k => hB _ _)
        refine ⟨φ ∘ ψ, Function.update v ⟨n, hn⟩ w, hφ.comp hψ, fun c hc => ?_⟩
        by_cases hcn : (c : ℕ) = n
        · have hc' : c = ⟨n, hn⟩ := Fin.ext hcn
          subst hc'
          simp only [Function.update_self]
          exact ⟨hw, hlim⟩
        · have hlt : (c : ℕ) < n := by omega
          have hne : c ≠ ⟨n, hn⟩ := fun h => hcn (by rw [h])
          simp only [Function.update_of_ne hne]
          exact ⟨(hv c hlt).1, (hv c hlt).2.comp hψ.tendsto_atTop⟩
      · refine ⟨φ, v, hφ, fun c hc => hv c (by have := c.isLt; omega)⟩
  obtain ⟨φ, v, hφ, hv⟩ := key m
  exact ⟨φ, v, hφ, fun c => (hv c c.isLt).1, fun c => (hv c c.isLt).2⟩

/-- **`prop:covariant-higgs-endpoint` (covariant-gradient compactness), box rendering.**
Let `Q = Π(a_i, b_i)` be a coordinate box in a four-dimensional chart, `H_h = (H_h^c)_{c<m}`
fields in `H¹(Q)` (the smooth reconstructed Higgs fields; weak gradients `dH_h`), and
`A_h = (ρ_H(A_{h,μ})_{ce})` the matrix entries of the connections.  Suppose
`A_h → A₀` in `L⁴(Q)`, `sup_h ‖H_h‖_{L²(Q)} < ∞` and `D_{A_h} H_h → Y` in `L²(Q)`.  Then a
subsequence converges to some `H₀` with `H₀ ∈ H¹(Q)`, `Y = D_{A₀} H₀` (the weak gradient of `H₀` is
`Y - A₀ H₀`), **strongly in `H¹(Q)`** (values and weak gradients in `L²(Q)`) and **strongly in
`L⁴(Q)`**.  Applied to subsequences this is precompactness in `H¹(Q)`. -/
theorem covariant_higgs_endpoint_box (hd : Fintype.card ι = 4) {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) {m : ℕ} (H : ℕ → Fin m → (ι → ℝ) → ℂ)
    (dH : ℕ → Fin m → ι → (ι → ℝ) → ℂ) (A : ℕ → ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (A₀ : ι → Fin m → Fin m → (ι → ℝ) → ℂ) (Y : Fin m → ι → (ι → ℝ) → ℂ)
    (hW : ∀ h c, MemW12 (box a b) (H h c) (dH h c))
    (hA : ∀ h μ c e, MemLp (A h μ c e) 4 (volume.restrict (box a b)))
    (hA₀ : ∀ μ c e, MemLp (A₀ μ c e) 4 (volume.restrict (box a b)))
    (hAlim : ∀ μ c e, Tendsto (fun h => eLpNorm (A h μ c e - A₀ μ c e) 4
      (volume.restrict (box a b))) atTop (𝓝 0))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤) (hHB : ∀ h c, eLpNorm (H h c) 2 (volume.restrict (box a b)) ≤ B)
    (hY : ∀ c μ, MemLp (Y c μ) 2 (volume.restrict (box a b)))
    (hYlim : ∀ c μ, Tendsto (fun h => eLpNorm (covD (dH h) (A h) (H h) c μ - Y c μ) 2
      (volume.restrict (box a b))) atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (H₀ : Fin m → (ι → ℝ) → ℂ), StrictMono φ ∧
      (∀ c, MemW12 (box a b) (H₀ c) (covGrad Y A₀ H₀ c)) ∧
      (∀ c μ x, covD (covGrad Y A₀ H₀) A₀ H₀ c μ x = Y c μ x) ∧
      (∀ c, Tendsto (fun k => eLpNorm (H (φ k) c - H₀ c) 2 (volume.restrict (box a b))) atTop
        (𝓝 0)) ∧
      (∀ c μ, Tendsto (fun k => eLpNorm (dH (φ k) c μ - covGrad Y A₀ H₀ c μ) 2
        (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      (∀ c, Tendsto (fun k => eLpNorm (H (φ k) c - H₀ c) 4 (volume.restrict (box a b))) atTop
        (𝓝 0)) := by
  obtain ⟨N, hNt, hev⟩ := covariant_eventually_bounded hd hab H dH A A₀ Y hW hA hA₀ hAlim hBt
    hHB hY hYlim
  obtain ⟨h₀, hh₀⟩ := eventually_atTop.mp hev
  obtain ⟨φ, v, hφ, hv, hlim⟩ := rellich_box_family hab (fun k => H (h₀ + k))
    (fun k => dH (h₀ + k)) (fun k c => hW _ c) hNt (fun k c => hh₀ _ (by omega) c)
  set σ : ℕ → ℕ := fun k => h₀ + φ k
  have hσ : StrictMono σ := fun i j hij => by simp only [σ]; have := hφ hij; omega
  have hσt : Tendsto σ atTop atTop := hσ.tendsto_atTop
  have hvQ : ∀ c, MemLp (v c) 2 (volume.restrict (box a b)) := fun c => (hv c).restrict _
  obtain ⟨h1, h2, h3⟩ := covariant_core hd hab (fun k => H (σ k)) (fun k => dH (σ k))
    (fun k => A (σ k)) A₀ Y (fun k c => hW _ c) (fun k => hA _) hA₀
    (fun μ c e => (hAlim μ c e).comp hσt) hY (fun c μ => (hYlim c μ).comp hσt) hNt
    (fun k c => hh₀ _ (Nat.le_add_right _ _) c) v hvQ hlim
  exact ⟨σ, v, hσ, h1, covD_covGrad Y A₀ v, hlim, h2, h3⟩


/-- **`prop:covariant-higgs-endpoint`, whole-sequence clause**: if moreover `H_h → H₀` in
`L²(Q)` is already known, the whole sequence converges strongly in `H¹(Q)` and in `L⁴(Q)`, and
`Y = D_{A₀} H₀`. -/
theorem covariant_higgs_endpoint_box_of_L2 (hd : Fintype.card ι = 4) {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) {m : ℕ} (H : ℕ → Fin m → (ι → ℝ) → ℂ)
    (dH : ℕ → Fin m → ι → (ι → ℝ) → ℂ) (A : ℕ → ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (A₀ : ι → Fin m → Fin m → (ι → ℝ) → ℂ) (Y : Fin m → ι → (ι → ℝ) → ℂ)
    (hW : ∀ h c, MemW12 (box a b) (H h c) (dH h c))
    (hA : ∀ h μ c e, MemLp (A h μ c e) 4 (volume.restrict (box a b)))
    (hA₀ : ∀ μ c e, MemLp (A₀ μ c e) 4 (volume.restrict (box a b)))
    (hAlim : ∀ μ c e, Tendsto (fun h => eLpNorm (A h μ c e - A₀ μ c e) 4
      (volume.restrict (box a b))) atTop (𝓝 0))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤) (hHB : ∀ h c, eLpNorm (H h c) 2 (volume.restrict (box a b)) ≤ B)
    (hY : ∀ c μ, MemLp (Y c μ) 2 (volume.restrict (box a b)))
    (hYlim : ∀ c μ, Tendsto (fun h => eLpNorm (covD (dH h) (A h) (H h) c μ - Y c μ) 2
      (volume.restrict (box a b))) atTop (𝓝 0))
    (H₀ : Fin m → (ι → ℝ) → ℂ) (hH₀ : ∀ c, MemLp (H₀ c) 2 (volume.restrict (box a b)))
    (hL2 : ∀ c, Tendsto (fun h => eLpNorm (H h c - H₀ c) 2 (volume.restrict (box a b))) atTop
      (𝓝 0)) :
    (∀ c, MemW12 (box a b) (H₀ c) (covGrad Y A₀ H₀ c)) ∧
      (∀ c μ, Tendsto (fun h => eLpNorm (dH h c μ - covGrad Y A₀ H₀ c μ) 2
        (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      (∀ c, Tendsto (fun h => eLpNorm (H h c - H₀ c) 4 (volume.restrict (box a b))) atTop
        (𝓝 0)) := by
  obtain ⟨N, hNt, hev⟩ := covariant_eventually_bounded hd hab H dH A A₀ Y hW hA hA₀ hAlim hBt
    hHB hY hYlim
  obtain ⟨h₀, hh₀⟩ := eventually_atTop.mp hev
  have hsh : Tendsto (fun k : ℕ => k + h₀) atTop atTop := tendsto_add_atTop_nat h₀
  obtain ⟨h1, h2, h3⟩ := covariant_core hd hab (fun k => H (k + h₀)) (fun k => dH (k + h₀))
    (fun k => A (k + h₀)) A₀ Y (fun k c => hW _ c) (fun k => hA _) hA₀
    (fun μ c e => (hAlim μ c e).comp hsh) hY (fun c μ => (hYlim c μ).comp hsh) hNt
    (fun k c => hh₀ _ (Nat.le_add_left _ _) c) H₀ hH₀ (fun c => (hL2 c).comp hsh)
  exact ⟨h1, fun c μ => (tendsto_add_atTop_iff_nat h₀).mp (h2 c μ),
    fun c => (tendsto_add_atTop_iff_nat h₀).mp (h3 c)⟩

/-- **Precompactness in `H¹(Q)`** (`prop:covariant-higgs-endpoint`, first assertion): under the
hypotheses of `covariant_higgs_endpoint_box`, every subsequence `H_{ns k}` has a further
subsequence converging strongly in `H¹(Q)` and in `L⁴(Q)` to a limit `H₀` with `Y = D_{A₀} H₀`. -/
theorem covariant_higgs_endpoint_box_precompact (hd : Fintype.card ι = 4) {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) {m : ℕ} (H : ℕ → Fin m → (ι → ℝ) → ℂ)
    (dH : ℕ → Fin m → ι → (ι → ℝ) → ℂ) (A : ℕ → ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (A₀ : ι → Fin m → Fin m → (ι → ℝ) → ℂ) (Y : Fin m → ι → (ι → ℝ) → ℂ)
    (hW : ∀ h c, MemW12 (box a b) (H h c) (dH h c))
    (hA : ∀ h μ c e, MemLp (A h μ c e) 4 (volume.restrict (box a b)))
    (hA₀ : ∀ μ c e, MemLp (A₀ μ c e) 4 (volume.restrict (box a b)))
    (hAlim : ∀ μ c e, Tendsto (fun h => eLpNorm (A h μ c e - A₀ μ c e) 4
      (volume.restrict (box a b))) atTop (𝓝 0))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤) (hHB : ∀ h c, eLpNorm (H h c) 2 (volume.restrict (box a b)) ≤ B)
    (hY : ∀ c μ, MemLp (Y c μ) 2 (volume.restrict (box a b)))
    (hYlim : ∀ c μ, Tendsto (fun h => eLpNorm (covD (dH h) (A h) (H h) c μ - Y c μ) 2
      (volume.restrict (box a b))) atTop (𝓝 0))
    (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ (φ : ℕ → ℕ) (H₀ : Fin m → (ι → ℝ) → ℂ), StrictMono φ ∧
      (∀ c, MemW12 (box a b) (H₀ c) (covGrad Y A₀ H₀ c)) ∧
      (∀ c, Tendsto (fun k => eLpNorm (H (ns (φ k)) c - H₀ c) 2 (volume.restrict (box a b)))
        atTop (𝓝 0)) ∧
      (∀ c μ, Tendsto (fun k => eLpNorm (dH (ns (φ k)) c μ - covGrad Y A₀ H₀ c μ) 2
        (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      (∀ c, Tendsto (fun k => eLpNorm (H (ns (φ k)) c - H₀ c) 4 (volume.restrict (box a b)))
        atTop (𝓝 0)) := by
  have hnt := hns.tendsto_atTop
  obtain ⟨φ, H₀, hφ, h1, -, h3, h4, h5⟩ := covariant_higgs_endpoint_box hd hab (fun k => H (ns k))
    (fun k => dH (ns k)) (fun k => A (ns k)) A₀ Y (fun k c => hW _ c) (fun k => hA _) hA₀
    (fun μ c e => (hAlim μ c e).comp hnt) hBt (fun k c => hHB _ c) hY
    (fun c μ => (hYlim c μ).comp hnt)
  exact ⟨φ, H₀, hφ, h1, h3, h4, h5⟩

/-! ### Quadratic and quartic Higgs densities -/

/-- The bounded real-bilinear map `(z, w) ↦ conj z · w` on `ℂ`. -/
def conjMul : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem conjMul_apply (z w : ℂ) : conjMul z w = conj z * w := by
  simp [conjMul]

instance fact_one_le_four_ennreal : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- **The Higgs quadratic, quartic and covariant-kinetic densities converge** (the
"quartic potential and complete Higgs stress converge in `L¹`" clause): if `H_k → H₀` in `L⁴` and
`D_k → Y` in `L²` (componentwise), then `conj(H^c) H^e → conj(H₀^c) H₀^e` in `L²`,
`conj(H^c) H^e · conj(H^{c'}) H^{e'}` converges in `L¹` (the quartic potential
`λ(|H|² - v²)²` is a fixed linear combination of these and of the quadratic terms), and
`conj(D^c_μ) D^e_ν → conj(Y^c_μ) Y^e_ν` in `L¹` (the Higgs stress is a fixed linear combination of
these densities, the potential and its coefficients). -/
theorem higgs_densities_tendsto {X : Type*} [MeasurableSpace X] {ν : Measure X} {m : ℕ}
    {D₀ : Type*} {H : ℕ → Fin m → X → ℂ} {H₀ : Fin m → X → ℂ} {D : ℕ → Fin m → D₀ → X → ℂ}
    {Y : Fin m → D₀ → X → ℂ} (hH : ∀ c, LpTendsto ν 4 (fun k => H k c) (H₀ c))
    (hD : ∀ c μ, LpTendsto ν 2 (fun k => D k c μ) (Y c μ)) :
    (∀ c e, LpTendsto ν 2 (fun k x => conj (H k c x) * H k e x)
      (fun x => conj (H₀ c x) * H₀ e x)) ∧
    (∀ c e c' e', LpTendsto ν 1
      (fun k x => (conj (H k c x) * H k e x) * (conj (H k c' x) * H k e' x))
      (fun x => (conj (H₀ c x) * H₀ e x) * (conj (H₀ c' x) * H₀ e' x))) ∧
    (∀ c e μ μ', LpTendsto ν 1 (fun k x => conj (D k c μ x) * D k e μ' x)
      (fun x => conj (Y c μ x) * Y e μ' x)) := by
  have hq : ∀ c e, LpTendsto ν 2 (fun k x => conj (H k c x) * H k e x)
      (fun x => conj (H₀ c x) * H₀ e x) := by
    intro c e
    have := (hH c).bilin (p := 4) (q := 4) (r := 2) conjMul (hH e)
    simpa [conjMul_apply] using this
  refine ⟨hq, fun c e c' e' => ?_, fun c e μ μ' => ?_⟩
  · have := (hq c e).bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℂ) (hq c' e')
    simpa using this
  · have := (hD c μ).bilin (p := 2) (q := 2) (r := 1) conjMul (hD e μ')
    simpa [conjMul_apply] using this

/-! ### Non-vacuity -/

/-- Non-vacuity of `covariant_higgs_endpoint_box`: constant Higgs field `H = 1`, vanishing
connection and covariant limit `Y = 0`, on the unit box of `ℝ⁴`. -/
example : ∃ (φ : ℕ → ℕ) (H₀ : Fin 1 → (Fin 4 → ℝ) → ℂ), StrictMono φ ∧
    (∀ c, MemW12 (box 0 1) (H₀ c) (covGrad (fun _ _ _ => 0) (fun _ _ _ _ => 0) H₀ c)) ∧
    (∀ c μ x, covD (covGrad (fun _ _ _ => 0) (fun _ _ _ _ => 0) H₀) (fun _ _ _ _ => 0) H₀ c μ x =
      0) ∧
    (∀ c, Tendsto (fun k => eLpNorm ((fun _ _ => 1 : ℕ → Fin 1 → (Fin 4 → ℝ) → ℂ) (φ k) c - H₀ c)
      2 (volume.restrict (box 0 1))) atTop (𝓝 0)) ∧
    (∀ c μ, Tendsto (fun k => eLpNorm ((fun _ _ _ _ => 0 : ℕ → Fin 1 → Fin 4 → (Fin 4 → ℝ) → ℂ)
      (φ k) c μ - covGrad (fun _ _ _ => 0) (fun _ _ _ _ => 0) H₀ c μ) 2
        (volume.restrict (box 0 1))) atTop (𝓝 0)) ∧
    (∀ c, Tendsto (fun k => eLpNorm ((fun _ _ => 1 : ℕ → Fin 1 → (Fin 4 → ℝ) → ℂ) (φ k) c - H₀ c)
      4 (volume.restrict (box 0 1))) atTop (𝓝 0)) := by
  have : IsFiniteMeasure (volume.restrict (box (0 : Fin 4 → ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (volume_box_ne_top 0 1)
  refine covariant_higgs_endpoint_box (ι := Fin 4) (by simp) (fun _ => zero_lt_one)
    (fun _ _ => fun _ => (1 : ℂ)) (fun _ _ _ _ => 0) (fun _ _ _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun _ _ _ => 0) (fun _ _ => memW12_const_box 0 1 1) (fun _ _ _ _ => memLp_const 0)
    (fun _ _ _ => memLp_const 0) (fun _ _ _ => by simp) (B := eLpNorm (fun _ => (1 : ℂ)) 2
      (volume.restrict (box (0 : Fin 4 → ℝ) 1))) (memLp_const 1).eLpNorm_ne_top
    (fun _ _ => le_rfl) (fun _ _ => memLp_const 0) (fun _ _ => by simp [covD_def])

end RenewalGeometry.SobolevOpen
