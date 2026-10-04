/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMReducedClosure
import RenewalGeometry.Analysis.TorusSobolevDerivatives

/-!
# Stress and uniqueness consequences of the reduced closure
  (`cor:reduced-stress`, `prop:reduced-unique`, Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMReducedClosure.lean` (slab charts `(t₀,t₁) × (0,1)³`, trivialised
bundles, `𝒱_K^r` dual norms rendered as the uniform estimate on the unit ball / `ε ‖v‖`).

## Stress densities (`cor:reduced-stress`)

With the Hilbert-stress convention `eq:stress-definition`, `D_g𝒮_SM[k] = -½ ∫ T^SM k dV_g`, the
stress density `T dV_g` of a sector is `-2` times the metric part of its first-variation
covector.  For Yang–Mills and Higgs the metric variation involves only the value `k` of the metric
test (no derivative), so the stress densities are the covector fields
`ymStress θ R = -2 Σ_j g_j^{-2} (D_e ymCoeff_j)(e)[ė(k)](F, F)` and
`higgsStress θ R = -2 [(D_e higgsCoeff)(e)[ė(k)](D_AH, D_AH) + λ_H(-(|H|²-v_H²)² D√|g|[ė(k)])]`
(`k ↦ ...` linear, values in `(Fin 4 → Fin 4 → ℝ)^*`), `ė(k)` the symmetric coframe lift.
`bosonCov_metric` checks that on metric tests the bosonic covector is exactly
`-½ (ymStress + higgsStress)(k)`.

* `ymStress_tendsto`, `higgsStress_tendsto`: **strong `L¹` convergence** of the Yang–Mills and
  Higgs stress densities under reduced convergence;
* `matterMetricVariation_dual_tendsto`: the complete matter metric first variation converges in
  the dual `C^r` test norm (`r ≥ 1`; manuscript `r ≥ 2`);
* `dual_transfer`: convergence in the dual of any weaker test seminorm (`‖v‖_{C^r} ≤ C q(v)`,
  e.g. `q = ‖·‖_{H^m_0}`, `m > r + 2`) — the `H^{-m}` clause **modulo** the chart Sobolev
  embedding `H^m_0(K) ↪ C^r(K)` (proved on the torus: `TorusSobolev.crNorm_le`,
  `TorusSobolev.dual_Cr_to_negSobolev`);
* `operationalStress_tendsto`: the operational stress `⟨T_h, k⟩ = -2 D𝒮_{SM,h}[𝓘_h(k,0,0,0,0)]`
  converges to `T^SM dV_g` (`stressDistribution`) in `(𝒱_K^{r₀})^*`, using sectorwise consistency;
* `reduced_stress`: the assembled corollary along the subsequence of `reduced_closure`.

## Uniqueness (`prop:reduced-unique`)

* `ReducedConvergence.of_subseq`: whole-sequence reduced convergence from subsequential reduced
  convergence to one fixed limit (every Tendsto clause by the subsequence principle);
* `reduced_unique`: under the hypotheses of `reduced_closure` for the full family with one
  limiting bank, if every accumulation point lies in a solution class in which the limiting
  Cauchy data determine a unique solution `z_*`, and the Cauchy traces of the accumulation points
  are the prescribed ones, the whole family converges to `z_*` in reduced action convergence.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Stress densities -/

section StressDensities

variable {C : Type} [Fintype C]

/-- The embedding `k ↦ (k, 0, …, 0)` of metric-test values into the jet space. -/
def metricEmb (C : Type) [Fintype C] : CoframeFibre →L[ℝ] RJet C :=
  ContinuousLinearMap.inl ℝ CoframeFibre _

/-- Precomposition with `metricEmb`. -/
def metricRestr (C : Type) [Fintype C] : (RJet C →L[ℝ] ℝ) →L[ℝ] (CoframeFibre →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ CoframeFibre (RJet C) ℝ).flip (metricEmb C)

/-- **Yang–Mills stress density** `T^YM dV_g` (as a covector on metric-test values `k`):
`-2` times the metric part of the Yang–Mills first-variation covector. -/
def ymStress {Y : Type} (θ : CoefficientBank Y) (R : RJet C) : CoframeFibre →L[ℝ] ℝ :=
  (-2 : ℝ) • metricRestr C (∑ j, gaugeScalars θ j • ymMetCoeff (C := C) j R.e R.F R.F)

/-- **Higgs stress density** `T^H dV_g` (kinetic and potential parts). -/
def higgsStress {Y : Type} (θ : CoefficientBank Y) (R : RJet C) : CoframeFibre →L[ℝ] ℝ :=
  (-2 : ℝ) • metricRestr C (higgsMetCoeff (C := C) R.e R.K R.K +
    θ.lambdaH • potVCoeff (C := C) R.e ((higgsQuad R.H - θ.vH ^ 2) ^ 2))

/-- **The stress densities are the Hilbert stresses** (`eq:stress-definition`): on a metric test
jet `(k, ∂k, 0, …, 0)` the bosonic (Yang–Mills + Higgs) first-variation covector equals
`-½ (T^YM + T^H) dV_g (k)`. -/
theorem bosonCov_metric {Y : Type} (θ : CoefficientBank Y) (R : RJet C) (k : CoframeFibre)
    (dk : CoframeJet) :
    bosonCov θ R (RJet.mk k dk 0 0 0 0 0 0 0 0) = -(1 / 2) * (ymStress θ R k + higgsStress θ R k) := by
  have h1 : (metricEmb C k).e = k := rfl
  simp [bosonCov, ymMetCoeff, ymDaCoeff, ymACoeff, higgsMetCoeff, higgsDCoeff, higgsHCoeff,
    higgsACoeff, potHCoeff, potVCoeff, h1, ymStress, higgsStress, metricRestr, Finset.sum_apply]
  ring

end StressDensities

section StressConv

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- **`cor:reduced-stress`, Yang–Mills stress**: under reduced convergence on a slab chart the
Yang–Mills stress densities converge strongly in `L¹`. -/
theorem ymStress_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C}
    {θ₀ : CoefficientBank Ysec}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀) :
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 1
      (fun n x => ymStress (θ n) (redJet (z n).z x)) (fun x => ymStress θ₀ (limitJet L x)) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have hcl := Q.isCompact_closure
  have hsub := Q.closure_subset_cylSlab
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hRC.coframe_chart
  obtain ⟨-, -, he⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hRC.coframe_mem
    hRC.coframe_tendsto
  have hF : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => (redJet (z n).z x).F)
      (fun x => (limitJet L x).F) :=
    ⟨fun n => memLp_of_continuousOn_closure Q.isOpen hcl
      ((continuousOn_curvatureF (z n).smooth_A).mono hsub) 2, hRC.curv_mem, hRC.curv_tendsto⟩
  obtain ⟨hs, -, -⟩ := bank_couplings_tendsto hRC.bank_compact hRC.bank_tendsto
  have hsum := FirstVariationCalculus.LpTendsto.finset_sum (μ := Q.μ) (p := 1) Finset.univ fun j _ =>
    FirstVariationCalculus.LpTendsto.smul_seq (hs j) (he.bilin (continuousOn_ymMetCoeff (C := C) j) hF hF)
  have h2 := FirstVariationCalculus.LpTendsto.clm_comp (μ := Q.μ) (p := 1) (by norm_num)
    ((-2 : ℝ) • metricRestr C) hsum
  exact h2

/-- **`cor:reduced-stress`, Higgs stress** (kinetic and quartic potential parts): under reduced
convergence on a slab chart the Higgs stress densities converge strongly in `L¹` (the potential
through the strong `L⁴` Higgs convergence of `prop:covariant-higgs-endpoint`). -/
theorem higgsStress_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C}
    {θ₀ : CoefficientBank Ysec}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀) :
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 1
      (fun n x => higgsStress (θ n) (redJet (z n).z x))
      (fun x => higgsStress θ₀ (limitJet L x)) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have hcl := Q.isCompact_closure
  have hsub := Q.closure_subset_cylSlab
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hRC.coframe_chart
  obtain ⟨-, -, he⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hRC.coframe_mem
    hRC.coframe_tendsto
  have hK : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => (redJet (z n).z x).K)
      (fun x => (limitJet L x).K) :=
    ⟨fun n => memLp_of_continuousOn_closure Q.isOpen hcl
      ((continuousOn_covDerivHiggs (z n).smooth_A (z n).smooth_H).mono hsub) 2, hRC.covgrad_mem,
      hRC.covgrad_tendsto⟩
  obtain ⟨-, -, -, hH4⟩ := hRC.higgs_strong
  have hH : RenewalGeometry.LpTendsto Q.μ 4 (fun n x => (redJet (z n).z x).H)
      (fun x => (limitJet L x).H) :=
    ⟨fun n => memLp_of_continuousOn_closure Q.isOpen hcl ((z n).smooth_H.continuousOn.mono hsub) 4,
      hRC.higgs_strong.2.2.1, hH4⟩
  obtain ⟨-, hl, hv⟩ := bank_couplings_tendsto hRC.bank_compact hRC.bank_tendsto
  have h442 : ENNReal.HolderTriple 4 4 2 := SobolevOpen.holderTriple_four_four_two
  have h14 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  have hq : RenewalGeometry.LpTendsto Q.μ 2
      (fun n x => higgsQuad ((redJet (z n).z x).H) - (θ n).vH ^ 2)
      (fun x => higgsQuad ((limitJet L x).H) - θ₀.vH ^ 2) :=
    (RenewalGeometry.LpTendsto.bilin (p := 4) (q := 4) (r := 2) hInnerReL hH hH).sub
      (FirstVariationCalculus.LpTendsto.const_seq (μ := Q.μ) (p := 2) (X := E4) (hv.pow 2))
  have hS : RenewalGeometry.LpTendsto Q.μ 1
      (fun n x => (higgsQuad ((redJet (z n).z x).H) - (θ n).vH ^ 2) ^ 2)
      (fun x => (higgsQuad ((limitJet L x).H) - θ₀.vH ^ 2) ^ 2) := by
    have := RenewalGeometry.LpTendsto.bilin (p := 2) (q := 2) (r := 1)
      (ContinuousLinearMap.mul ℝ ℝ) hq hq
    exact this.congr (fun n => Eventually.of_forall fun x => by
      simp only [ContinuousLinearMap.mul_apply', sq]) (Eventually.of_forall fun x => by
      simp only [ContinuousLinearMap.mul_apply', sq])
  have hkin := he.bilin (continuousOn_higgsMetCoeff (C := C)) hK hK
  have hpot := FirstVariationCalculus.LpTendsto.smul_seq hl (he.apply (continuousOn_potVCoeff (C := C)) (p := 1)
    (by norm_num) hS)
  have h2 := FirstVariationCalculus.LpTendsto.clm_comp (μ := Q.μ) (p := 1) (by norm_num)
    ((-2 : ℝ) • metricRestr C) (hkin.add hpot)
  exact h2

end StressConv

/-! ### The matter metric first variation and the operational stress -/

section MatterMetric

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec) {r : ℕ} {K : CylRegion T}

theorem crNorm_zero_fun {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (r : ℕ) :
    crNorm r (0 : E4 → F) = 0 := by
  simp [crNorm, iteratedFDeriv_fun_zero]

theorem norm_metricTest_le (v : CrTest FC.left r K) : ‖metricTest FC v‖ ≤ ‖v‖ := by
  rw [CrTest.norm_def, CrTest.norm_def]
  change crNorm r v.val.e + crNorm r (0 : E4 → ConnFibre) + crNorm r (0 : E4 → HiggsFibre) +
    crNorm r (0 : E4 → SpinorFibre FC.C) + crNorm r (0 : E4 → SpinorFibre FC.C) ≤ _
  simp only [crNorm_zero_fun, add_zero, testNorm]
  have := crNorm_nonneg r v.val.A; have := crNorm_nonneg r v.val.H
  have := crNorm_nonneg r v.val.Ψ; have := crNorm_nonneg r v.val.Ψb
  linarith

/-- **`cor:reduced-stress`, dual clause**: under reduced convergence on a slab chart (containing
the time support of `K`) and convergence of the Yukawa coefficients, the complete matter metric
first variation (`T^SM dV_g` = `stressDistribution`) converges in the dual `C^r` test norm. -/
theorem matterMetricVariation_dual_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁)
    (h1 : t₁ < T) (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T FC.left} {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    {L : LimitFields FC.C}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest FC.left r K,
      |-2 * firstVariation T FC (θ n) .standardModel (z n).z (metricTest FC v).val -
        stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  filter_upwards [smVariation_dual_tendsto FC h0 h01 h1 (fun p hp => Ioo_subset_Icc_self (hK p hp))
    hr hRC hyL hy0 (half_pos hε)] with n hn v
  have h := (hn (metricTest FC v)).trans
    (mul_le_mul_of_nonneg_left (norm_metricTest_le FC v) (half_pos hε).le)
  unfold stressDistribution
  rw [show -2 * firstVariation T FC (θ n) .standardModel (z n).z (metricTest FC v).val -
      -2 * smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L (metricTest FC v) =
      -2 * (firstVariation T FC (θ n) .standardModel (z n).z (metricTest FC v).val -
        smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L (metricTest FC v)) by ring,
    abs_mul]
  norm_num
  linarith

/-- **Dual comparison** (the `H^{-m}` clause of `cor:reduced-stress`, abstract form): convergence
`|ℓ_n v - ℓ v| ≤ ε ‖v‖_{C^r}` transfers to every test seminorm `q` dominating the `C^r` norm,
`‖v‖_{C^r} ≤ C q(v)` (for `q` the `H^m_0` norm, `m > r + 2`, by the Sobolev embedding). -/
theorem dual_transfer (q : CrTest FC.left r K → ℝ) (hq0 : ∀ v, 0 ≤ q v) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hq : ∀ v, ‖v‖ ≤ Cq * q v) (ℓ : ℕ → CrTest FC.left r K → ℝ) (ℓ₀ : CrTest FC.left r K → ℝ)
    (h : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v, |ℓ n v - ℓ₀ v| ≤ ε * ‖v‖) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v, |ℓ n v - ℓ₀ v| ≤ ε * q v := by
  intro ε hε
  filter_upwards [h (ε / (Cq + 1)) (by positivity)] with n hn v
  have hq0 := hq0 v
  calc |ℓ n v - ℓ₀ v| ≤ ε / (Cq + 1) * ‖v‖ := hn v
    _ ≤ ε / (Cq + 1) * (Cq * q v) := mul_le_mul_of_nonneg_left (hq v) (by positivity)
    _ ≤ ε * q v := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hq0
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

/-- **`cor:reduced-stress`, operational stress**: if along a subsequence the matter metric first
variations converge in the dual test norm and the consistency defect `c_h(K) → 0` (sectorwise
consistency, `eq:C1-consistency`), the operational stress
`⟨T_h, k⟩ = -2 D𝒮_{SM,h}(z_h^d)[𝓘_h(k,0,0,0,0)]` converges to `T^SM dV_g` in `(𝒱_K^{r₀})^*`:
uniformly on the unit ball. -/
theorem operationalStress_tendsto (reg : RegulatorSequence T FC) {σ : ℕ → ℕ}
    (hσ : Tendsto σ atTop atTop) (hcons : reg.FirstVariationConsistent) (Q : ChartBox T)
    (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec)
    (hconv : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
      |-2 * firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
          (metricTest FC v).val - stressDistribution FC θ₀ Q L v| ≤ ε * ‖v‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K, ‖v‖ ≤ 1 →
      |-2 * reg.finiteSectorVariation (σ k) .standardModel (reg.lift (σ k) K (metricTest FC v)) -
        stressDistribution FC θ₀ Q L v| ≤ ε := by
  have hc := ((hcons K).comp hσ).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr
    (by positivity : 0 < ε / 4)))
  filter_upwards [hconv (ε / 2) (half_pos hε), hc] with k hk hck v hv
  have hmv : ‖metricTest FC v‖ ≤ 1 := (norm_metricTest_le FC v).trans hv
  have hmv' : testNorm reg.r0 (metricTest FC v : ↥(testSubmodule FC.left K)).1 ≤ 1 := hmv
  have hb : ENNReal.ofReal |reg.finiteSectorVariation (σ k) .standardModel
      (reg.lift (σ k) K (metricTest FC v)) - firstVariation T FC (reg.bank (σ k)) .standardModel
        (reg.fields (σ k)).z (metricTest FC v).val| ≤ reg.consistencyDefect (σ k) K := by
    unfold RegulatorSequence.consistencyDefect
    refine le_trans ?_ (Finset.single_le_sum (f := fun b : Sector => ⨆ (w : ↥(testSubmodule
      FC.left K)) (_ : testNorm reg.r0 w.1 ≤ 1), ENNReal.ofReal |reg.finiteSectorVariation (σ k) b
        (reg.lift (σ k) K w) - firstVariation T FC (reg.bank (σ k)) b (reg.fields (σ k)).z w.1|)
      (fun _ _ => zero_le) (Finset.mem_univ Sector.standardModel))
    exact le_iSup₂ (f := fun (w : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 w.1 ≤ 1) =>
      ENNReal.ofReal |reg.finiteSectorVariation (σ k) .standardModel (reg.lift (σ k) K w) -
        firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z w.1|)
      (metricTest FC v : ↥(testSubmodule FC.left K)) hmv'
  have e1 := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < ε / 4)).mp (hb.trans_lt hck)
  have e2 := (hk v).trans (mul_le_of_le_one_right (half_pos hε).le hv)
  have := abs_sub_le (-2 * reg.finiteSectorVariation (σ k) .standardModel
      (reg.lift (σ k) K (metricTest FC v)))
    (-2 * firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
      (metricTest FC v).val) (stressDistribution FC θ₀ Q L v)
  have e3 : |-2 * reg.finiteSectorVariation (σ k) .standardModel
      (reg.lift (σ k) K (metricTest FC v)) - -2 * firstVariation T FC (reg.bank (σ k))
        .standardModel (reg.fields (σ k)).z (metricTest FC v).val| =
      2 * |reg.finiteSectorVariation (σ k) .standardModel (reg.lift (σ k) K (metricTest FC v)) -
        firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
          (metricTest FC v).val| := by
    rw [show -2 * reg.finiteSectorVariation (σ k) .standardModel
        (reg.lift (σ k) K (metricTest FC v)) - -2 * firstVariation T FC (reg.bank (σ k))
          .standardModel (reg.fields (σ k)).z (metricTest FC v).val =
        -2 * (reg.finiteSectorVariation (σ k) .standardModel (reg.lift (σ k) K (metricTest FC v)) -
          firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
            (metricTest FC v).val) by ring, abs_mul]
    norm_num
  linarith

end MatterMetric

/-! ### `cor:reduced-stress`, assembled -/

section ReducedStress

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **`cor:reduced-stress`.**  Under the hypotheses of `reduced_closure`, along a subsequence of
`thm:reduced-closure` (same limit `z = L`, bank `θ₀`): (i) the Yang–Mills and Higgs stress
densities converge strongly in `L¹` on every slab chart; (ii) the complete matter metric first
variation `T^SM dV_g` converges in the dual `C^{r₀}` test norm; (iii) it converges in the dual of
every test seminorm dominating the `C^{r₀}` norm (the `H^{-m}` clause, given the Sobolev
embedding); (iv) the operational stress converges to `T^SM dV_g` in `(𝒱_K^{r₀})^*`. -/
theorem reduced_stress (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesReducedCertificate Q)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ns (ψ k)))
          (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
        RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 1
          (fun k x => ymStress (reg.bank (ns (ψ k))) (redJet (reg.fields (ns (ψ k))).z x))
          (fun x => ymStress θ₀ (limitJet L x)) ∧
        RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 1
          (fun k x => higgsStress (reg.bank (ns (ψ k))) (redJet (reg.fields (ns (ψ k))).z x))
          (fun x => higgsStress θ₀ (limitJet L x))) ∧
      (∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) →
        (∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
          |-2 * firstVariation T FC (reg.bank (ns (ψ k))) .standardModel
              (reg.fields (ns (ψ k))).z (metricTest FC v).val -
            stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v| ≤ ε * ‖v‖) ∧
        (∀ (q : CrTest FC.left reg.r0 K → ℝ), (∀ v, 0 ≤ q v) → ∀ (Cq : ℝ), 0 ≤ Cq →
          (∀ v, ‖v‖ ≤ Cq * q v) →
          ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
            |-2 * firstVariation T FC (reg.bank (ns (ψ k))) .standardModel
                (reg.fields (ns (ψ k))).z (metricTest FC v).val -
              stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v| ≤ ε * q v) ∧
        (∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K, ‖v‖ ≤ 1 →
          |-2 * reg.finiteSectorVariation (ns (ψ k)) .standardModel
              (reg.lift (ns (ψ k)) K (metricTest FC v)) -
            stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v| ≤ ε)) := by
  obtain ⟨ψ, hψ, L, θ₀, -, hRC, -, -, -⟩ := reduced_closure hT reg hcert hcons hstat hyuk ns hns
  have hr : 1 ≤ reg.r0 := le_trans (by norm_num) reg.four_le_r0
  refine ⟨ψ, hψ, L, θ₀, fun t₀ t₁ h0 h01 h1 => ⟨(hRC t₀ t₁ h0 h01 h1).1,
    ymStress_tendsto h0 h01 h1 (hRC t₀ t₁ h0 h01 h1).1,
    higgsStress_tendsto h0 h01 h1 (hRC t₀ t₁ h0 h01 h1).1⟩, fun K t₀ t₁ h0 h01 h1 hK => ?_⟩
  obtain ⟨hyL, hy0⟩ := hyuk _ _ (hRC t₀ t₁ h0 h01 h1).1.bank_tendsto
  have hdual : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
      |-2 * firstVariation T FC (reg.bank (ns (ψ k))) .standardModel
          (reg.fields (ns (ψ k))).z (metricTest FC v).val -
        stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v| ≤ ε * ‖v‖ :=
    fun ε hε => matterMetricVariation_dual_tendsto FC h0 h01 h1 hK hr (hRC t₀ t₁ h0 h01 h1).1
      hyL hy0 hε
  exact ⟨hdual, fun q hq0 Cq hCq hq => dual_transfer FC q hq0 hCq hq _ _ hdual,
    fun ε hε => operationalStress_tendsto FC reg (hns.comp hψ).tendsto_atTop hcons _ L θ₀ hdual hε⟩

end ReducedStress

/-! ### `prop:reduced-unique` -/

section Unique

/-- Subsequence principle with strictly increasing subsequences. -/
theorem tendsto_of_strictMono_subseq {α : Type*} {f : ℕ → α} {l : Filter α}
    (h : ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ψ : ℕ → ℕ, Tendsto (fun k => f (ns (ψ k))) atTop l) :
    Tendsto f atTop l := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, hφ, hmono⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ψ, hψ⟩ := h (ns ∘ φ) hmono
  exact ⟨φ ∘ ψ, hψ⟩

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- **Whole-sequence reduced convergence from subsequences**: if every subsequence has a further
subsequence converging in the reduced topology to one fixed limit `(L, θ₀)`, and the reduced
certificate holds, the whole sequence converges in the reduced topology to `(L, θ₀)`. -/
theorem ReducedConvergence.of_subseq {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ : CoefficientBank Ysec}
    (hcert : ReducedCertificate Q z θ)
    (h : ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ψ : ℕ → ℕ,
      ReducedConvergence Q (fun k => z (ns (ψ k))) (fun k => θ (ns (ψ k))) L θ₀) :
    ReducedConvergence Q z θ L θ₀ := by
  obtain ⟨ψ₀, h₀⟩ := h id strictMono_id
  obtain ⟨Ke, hKe, -, hKL⟩ := h₀.coframe_chart
  obtain ⟨Ke', hKe', hKn'⟩ := hcert.coframe_chart
  have sub : ∀ {f : ℕ → ℝ≥0∞}, (∀ {z' : ℕ → SmoothFields T left} {θ' : ℕ → CoefficientBank Ysec},
      ReducedConvergence Q z' θ' L θ₀ → ∀ (ns ψ : ℕ → ℕ), z' = (fun k => z (ns (ψ k))) →
        Tendsto (fun k => f (ns (ψ k))) atTop (𝓝 0)) → Tendsto f atTop (𝓝 0) := by
    intro f hf
    refine tendsto_of_strictMono_subseq fun ns hns => ?_
    obtain ⟨ψ, hψ⟩ := h ns hns
    exact ⟨ψ, hf hψ ns ψ rfl⟩
  refine
    { coframe_chart := ⟨Ke ∪ Ke', hKe.union hKe', fun n => (hKn' n).mono fun x hx => Or.inr hx,
        hKL.mono fun x hx => Or.inl hx⟩
      coframe_mem := h₀.coframe_mem
      coframe_tendsto := sub fun hR ns ψ hz => by subst hz; exact hR.coframe_tendsto
      conn_lie := h₀.conn_lie
      conn_mem := h₀.conn_mem
      conn_tendsto := sub fun hR ns ψ hz => by subst hz; exact hR.conn_tendsto
      curv_mem := h₀.curv_mem
      curv_weak := h₀.curv_weak
      curv_tendsto := sub fun hR ns ψ hz => by subst hz; exact hR.curv_tendsto
      higgs_mem := h₀.higgs_mem
      higgs_tendsto := sub fun hR ns ψ hz => by subst hz; exact hR.higgs_tendsto
      covgrad_mem := h₀.covgrad_mem
      covgrad_weak := h₀.covgrad_weak
      covgrad_tendsto := sub fun hR ns ψ hz => by subst hz; exact hR.covgrad_tendsto
      spinor_weak := ⟨fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψ, h₀.spinor_weak.2.1,
        hcert.spinor_bounded, fun φ hφ c => ?_, fun φ hφ i c => ?_⟩
      cospinor_weak := ⟨fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψb, h₀.cospinor_weak.2.1,
        hcert.cospinor_bounded, fun φ hφ c => ?_, fun φ hφ i c => ?_⟩
      bank_compact := hcert.bank_compact
      bank_tendsto := tendsto_of_strictMono_subseq fun ns hns => by
        obtain ⟨ψ, hψ⟩ := h ns hns
        exact ⟨ψ, hψ.bank_tendsto⟩ }
  all_goals refine tendsto_of_strictMono_subseq fun ns hns => ?_
  all_goals obtain ⟨ψ, hψ⟩ := h ns hns
  · exact ⟨ψ, hψ.spinor_weak.2.2.2.1 φ hφ c⟩
  · exact ⟨ψ, hψ.spinor_weak.2.2.2.2 φ hφ i c⟩
  · exact ⟨ψ, hψ.cospinor_weak.2.2.2.1 φ hφ c⟩
  · exact ⟨ψ, hψ.cospinor_weak.2.2.2.2 φ hφ i c⟩

variable {FC : FermionCarrier Ysec}

/-- **`prop:reduced-unique` (uniqueness without summable adjacent-cutoff transport).**  Suppose the
hypotheses of `thm:reduced-closure` hold for the full regulator family with one limiting
coefficient bank `θ₀`.  Suppose that every accumulation point (every limit, in the reduced
topology on all slab charts, of a subsequence) belongs to a solution class `Sol` in which the
limiting Cauchy data `trace` determine a unique solution `z_*` (`huniq`: a solution with the data
`d₀` equals `z_*` a.e. on every slab chart, in the fixed gauge and frame identifications), and
that the Cauchy traces converge separately in that class (`htrace`: accumulation points carry the
data `d₀`).  Then the entire family converges to `z_*` in reduced action convergence on every slab
chart.  No summability of adjacent-cutoff errors is used. -/
theorem reduced_unique (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesReducedCertificate Q)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) {θ₀ : CoefficientBank Ysec} (hbank : BankTendsto reg.bank θ₀)
    {D : Type*} (Sol : LimitFields FC.C → Prop) (trace : LimitFields FC.C → D) (d₀ : D)
    (zstar : LimitFields FC.C)
    (hsol : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (L : LimitFields FC.C) (θ : CoefficientBank Ysec),
      (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ψ k))
          (fun k => reg.bank (ψ k)) L θ) → Sol L)
    (htrace : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (L : LimitFields FC.C) (θ : CoefficientBank Ysec),
      (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ψ k))
          (fun k => reg.bank (ψ k)) L θ) → trace L = d₀)
    (huniq : ∀ L, Sol L → trace L = d₀ → ∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      LimitFields.AEEqOn (slabChart t₀ t₁ h0 h01 h1 (T := T)) L zstar) :
    ∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) reg.fields reg.bank zstar θ₀ := by
  intro t₀ t₁ h0 h01 h1
  refine ReducedConvergence.of_subseq (hcert _) fun ns hns => ?_
  obtain ⟨ψ, hψ, L, θ', -, hRC, -, -, -⟩ := reduced_closure hT reg hcert hcons hstat hyuk ns hns
  have hacc : ∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields ((ns ∘ ψ) k))
        (fun k => reg.bank ((ns ∘ ψ) k)) L θ' := fun t₀ t₁ h0 h01 h1 => (hRC t₀ t₁ h0 h01 h1).1
  have hL := huniq L (hsol _ (hns.comp hψ) L θ' hacc) (htrace _ (hns.comp hψ) L θ' hacc)
    t₀ t₁ h0 h01 h1
  exact ⟨ψ, ((hRC t₀ t₁ h0 h01 h1).1.with_bank
    (hbank.comp (hns.comp hψ).tendsto_atTop)).congr_ae hL⟩

/-- **Non-vacuity of `prop:reduced-unique`**: for the flat regulator, with the solution class of
fields a.e. equal to the flat limit and trivial Cauchy data, every hypothesis holds and the whole
family converges to the flat limit. -/
example (hT : 0 < T) :
    ∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (flatRegulator T).fields
        (flatRegulator T).bank flatLimit physicalBank := by
  refine reduced_unique hT (flatRegulator T) (fun Q => flatRegulator_reducedCertificate T Q)
    (flatRegulator_consistent hT) flatRegulator_stationary (trivialCarrier_yukawaContinuous Unit)
    tendsto_const_nhds (fun L => ∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      LimitFields.AEEqOn (slabChart t₀ t₁ h0 h01 h1 (T := T)) L flatLimit) (fun _ => ()) ()
    flatLimit ?_ (fun _ _ _ _ _ => rfl) (fun L hL _ => hL)
  intro ψ hψ L θ hRC t₀ t₁ h0 h01 h1
  exact (hRC t₀ t₁ h0 h01 h1).unique
    ((flatRegulator_reducedActionConvergence T _).comp hψ.tendsto_atTop)

end Unique

end EinsteinSM
end RenewalGeometry
