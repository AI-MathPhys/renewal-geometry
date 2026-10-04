/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevBoxExtension
import RenewalGeometry.Analysis.SuperlinearVitaliConvergence

/-!
# Rellich, critical Sobolev and the quartic compactness certificate on coordinate boxes

Generic infrastructure (no renewal notions) for `prop:orlicz` and
`prop:covariant-higgs-endpoint` of the Einstein–SM action-closure manuscript, on a bounded
four-dimensional region rendered as a coordinate box `Q = Π_i (a_i, b_i)` of the chart, with the
standard Sobolev space `H¹(Q) = W^{1,2}(Q)` of `SobolevOpenSet.lean` (weak derivatives in
`L²(Q)`, no boundary condition).  All statements are consequences of the reflection extension
operator `exists_extension_box` (`SobolevBoxExtension.lean`):

* `rellich_box` (**Rellich–Kondrachov `H¹(Q) ⋐ L²(Q)`**);
* `eLpNorm_le_box` (**critical Sobolev `H¹(Q) ↪ L^{2d/(d-2)}(Q)`**, `L⁴` in four dimensions);
* `tendsto_integral_test_of_L2`, `ae_eq_of_integral_test`: passage of `L²(Q)` limits to test
  pairings and identification of limits from test pairings;
* `tendsto_L2_box_of_weak`: a sequence bounded in `H¹(Q)` whose test pairings converge to those
  of `H₀` converges to `H₀` **strongly in `L²(Q)`** (full sequence);
* `orlicz_box`, `orlicz_box_of_Lp_bound` (**`prop:orlicz` on `Q`**).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Rellich–Kondrachov on a box**: a sequence bounded in `W^{1,2}(Q)` has a subsequence
converging strongly in `L²(Q)`. -/
theorem rellich_box {a b : ι → ℝ} (hab : ∀ i, a i < b i) (u : ℕ → (ι → ℝ) → ℂ)
    (g : ℕ → ι → (ι → ℝ) → ℂ) (hW : ∀ k, MemW12 (box a b) (u k) (g k)) {B : ℝ≥0∞}
    (hBt : B ≠ ⊤) (hB : ∀ k, w12Norm (box a b) (u k) (g k) ≤ B) :
    ∃ (φ : ℕ → ℕ) (v : (ι → ℝ) → ℂ), StrictMono φ ∧ MemLp v 2 volume ∧
      Tendsto (fun k => eLpNorm (u (φ k) - v) 2 (volume.restrict (box a b))) atTop (𝓝 0) := by
  obtain ⟨R, C, hR, hext⟩ := exists_extension_box hab
  choose U G hU hUa hU0 hG0 hUn using fun k => hext (u k) (g k) (hW k)
  obtain ⟨φ, v, hφ, hv, hlim⟩ := rellich_ball hR U G hU hU0 hG0
    (B := C * B) (ENNReal.mul_ne_top ENNReal.coe_ne_top hBt)
    (fun k => (hUn k).trans (by gcongr; exact hB k))
  refine ⟨φ, v, hφ, hv, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le)
    (fun k => ?_)
  have e : eLpNorm (u (φ k) - v) 2 (volume.restrict (box a b)) =
      eLpNorm (U (φ k) - v) 2 (volume.restrict (box a b)) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' (isOpen_box a b).measurableSet).mpr
      (Eventually.of_forall fun x hx => ?_))
    simp [(hUa (φ k) x hx).1]
  rw [e]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **Critical Sobolev embedding on a box**: for `d = card ι ≥ 3` and `1/p' = 1/2 - 1/d`
(`p' = 4` for `d = 4`), `‖u‖_{L^{p'}(Q)} ≤ C_Q ‖u‖_{W^{1,2}(Q)}`. -/
theorem eLpNorm_le_box {a b : ι → ℝ} (hab : ∀ i, a i < b i) (hn : 2 < Fintype.card ι)
    {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (Fintype.card ι : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ), MemW12 (box a b) u g →
      eLpNorm u p' (volume.restrict (box a b)) ≤ C * w12Norm (box a b) u g := by
  obtain ⟨R, C, hR, hext⟩ := exists_extension_box hab
  refine ⟨SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 * C, fun u g hW => ?_⟩
  obtain ⟨U, G, hU, hUa, hU0, -, hUn⟩ := hext u g hW
  have e : eLpNorm u p' (volume.restrict (box a b)) =
      eLpNorm U p' (volume.restrict (box a b)) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' (isOpen_box a b).measurableSet).mpr
      (Eventually.of_forall fun x hx => ?_))
    exact (hUa x hx).1.symm
  rw [e]
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
  refine (eLpNorm_le_sum_grad_of_ball hU hU0 hn hp').trans ?_
  have hsum : ∑ i, eLpNorm (G i) 2 volume ≤ w12Norm univ U G := by
    unfold w12Norm; rw [Measure.restrict_univ]; exact le_add_self
  calc (SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 : ℝ≥0∞) *
        ∑ i, eLpNorm (G i) 2 volume
      ≤ SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 * (C * w12Norm (box a b) u g) := by
        gcongr; exact hsum.trans hUn
    _ = ((SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 * C : ℝ≥0) : ℝ≥0∞) *
          w12Norm (box a b) u g := by push_cast; ring

/-! ### Test pairings -/

/-- `L²(Ω)` convergence (`Ω` of finite measure) passes to pairings with test functions. -/
theorem tendsto_integral_test_of_L2 {Ω : Set (ι → ℝ)} (hΩm : MeasurableSet Ω)
    (hΩf : volume Ω ≠ ⊤) {φ : (ι → ℝ) → ℝ} (hφ : IsTest Ω φ) {f : ℕ → (ι → ℝ) → ℂ}
    {v : (ι → ℝ) → ℂ} (hf : ∀ k, MemLp (f k) 2 (volume.restrict Ω))
    (hv : MemLp v 2 (volume.restrict Ω))
    (hlim : Tendsto (fun k => eLpNorm (f k - v) 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ((φ x : ℝ) : ℂ) * f k x) atTop
      (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * v x)) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩf
  have h0 : ∀ x, x ∉ Ω → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.subset h)
  have hset : ∀ w : (ι → ℝ) → ℂ, ∫ x, ((φ x : ℝ) : ℂ) * w x =
      ∫ x in Ω, ((φ x : ℝ) : ℂ) * w x := fun w =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [h0 x hx]).symm
  simp only [hset]
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφ.compact
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  have hbd : ∀ w : (ι → ℝ) → ℂ, MemLp w 2 (volume.restrict Ω) →
      Integrable (fun x => ((φ x : ℝ) : ℂ) * w x) (volume.restrict Ω) := fun w hw =>
    (hw.integrable (by norm_num)).bdd_mul
      (Complex.continuous_ofReal.comp hφ.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Complex.norm_real]; exact hMφ x)
  refine tendsto_integral_of_L1 _ (hbd v hv).1 (Eventually.of_forall fun k => hbd _ (hf k)) ?_
  -- `∫ |φ| |f_k - v| ≤ M ‖f_k - v‖_1 ≤ M C ‖f_k - v‖_2`
  set c := (volume.restrict Ω) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hc : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hle : ∀ k, ∫⁻ x, ‖((φ x : ℝ) : ℂ) * f k x - ((φ x : ℝ) : ℂ) * v x‖ₑ
      ∂(volume.restrict Ω) ≤ ENNReal.ofReal Mφ * (eLpNorm (f k - v) 2 (volume.restrict Ω) * c) := by
    intro k
    calc ∫⁻ x, ‖((φ x : ℝ) : ℂ) * f k x - ((φ x : ℝ) : ℂ) * v x‖ₑ ∂(volume.restrict Ω)
        ≤ ∫⁻ x, ENNReal.ofReal Mφ * ‖(f k - v) x‖ₑ ∂(volume.restrict Ω) := by
          refine lintegral_mono fun x => ?_
          rw [← mul_sub, enorm_mul, Pi.sub_apply]
          gcongr
          rw [← ofReal_norm_eq_enorm, Complex.norm_real]
          exact ENNReal.ofReal_le_ofReal (hMφ x)
      _ = ENNReal.ofReal Mφ * eLpNorm (f k - v) 1 (volume.restrict Ω) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ENNReal.ofReal Mφ * (eLpNorm (f k - v) 2 (volume.restrict Ω) * c) := by
          gcongr
          exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) ((hf k).1.sub hv.1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => zero_le) hle
  have := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const hlim (Or.inr hc))
    (a := ENNReal.ofReal Mφ) (Or.inr ENNReal.ofReal_ne_top)
  simpa using this

/-- **Identification of limits from test pairings**: locally integrable functions on an open set
with the same pairings against all real test functions agree a.e. on the set. -/
theorem ae_eq_of_integral_test {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) {v w : (ι → ℝ) → ℂ}
    (hv : LocallyIntegrableOn v Ω) (hw : LocallyIntegrableOn w Ω)
    (h : ∀ φ : (ι → ℝ) → ℝ, IsTest Ω φ →
      ∫ x, ((φ x : ℝ) : ℂ) * v x = ∫ x, ((φ x : ℝ) : ℂ) * w x) :
    ∀ᵐ x, x ∈ Ω → v x = w x := by
  have := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (hv.sub hw) ?_
  · filter_upwards [this] with x hx hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  intro φ hφs hφc hφΩ
  have ht : IsTest Ω φ := ⟨hφs, hφc, hφΩ⟩
  have i1 : Integrable fun x => ((φ x : ℝ) : ℂ) * v x :=
    integrable_mul_of_locallyIntegrableOn hv (Complex.continuous_ofReal.comp hφs.continuous)
      (hφc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero φ).trans hφΩ)
  have i2 : Integrable fun x => ((φ x : ℝ) : ℂ) * w x :=
    integrable_mul_of_locallyIntegrableOn hw (Complex.continuous_ofReal.comp hφs.continuous)
      (hφc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero φ).trans hφΩ)
  simp only [Complex.real_smul, Pi.sub_apply, mul_sub]
  rw [integral_sub i1 i2, h φ ht, sub_self]

/-- **Strong `L²(Q)` convergence of `H¹(Q)`-bounded, test-convergent sequences** (Rellich for the
full sequence): if `H_k` is bounded in `W^{1,2}(Q)` and `∫ φ H_k → ∫ φ H₀` for every test function
`φ ∈ C_c^∞(Q)` (in particular if `H_k ⇀ H₀` weakly in `H¹(Q)`), then `H_k → H₀` in `L²(Q)`. -/
theorem tendsto_L2_box_of_weak {a b : ι → ℝ} (hab : ∀ i, a i < b i) (H : ℕ → (ι → ℝ) → ℂ)
    (gH : ℕ → ι → (ι → ℝ) → ℂ) (H₀ : (ι → ℝ) → ℂ) (hW : ∀ k, MemW12 (box a b) (H k) (gH k))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤) (hB : ∀ k, w12Norm (box a b) (H k) (gH k) ≤ B)
    (hH₀ : MemLp H₀ 2 (volume.restrict (box a b)))
    (hweak : ∀ φ : (ι → ℝ) → ℝ, IsTest (box a b) φ →
      Tendsto (fun k => ∫ x, ((φ x : ℝ) : ℂ) * H k x) atTop (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * H₀ x))) :
    Tendsto (fun k => eLpNorm (H k - H₀) 2 (volume.restrict (box a b))) atTop (𝓝 0) := by
  set Q := box a b
  have hQ : IsOpen Q := isOpen_box a b
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, v, hφ, hv, hlim⟩ := rellich_box hab (fun k => H (ns k)) (fun k => gH (ns k))
    (fun k => hW (ns k)) hBt (fun k => hB (ns k))
  -- identification of the limit
  have hvQ : MemLp v 2 (volume.restrict Q) := hv.restrict Q
  have hpair : ∀ ψ : (ι → ℝ) → ℝ, IsTest Q ψ →
      ∫ x, ((ψ x : ℝ) : ℂ) * v x = ∫ x, ((ψ x : ℝ) : ℂ) * H₀ x := by
    intro ψ hψ
    have h1 := tendsto_integral_test_of_L2 hQ.measurableSet (volume_box_ne_top a b) hψ
      (fun k => (hW (ns (φ k))).memLp) hvQ hlim
    have h2 := (hweak ψ hψ).comp (hns.comp hφ.tendsto_atTop)
    exact tendsto_nhds_unique h1 h2
  have hae := ae_eq_of_integral_test hQ (locallyIntegrableOn_of_memLp hvQ)
    (locallyIntegrableOn_of_memLp hH₀) hpair
  refine ⟨φ, hlim.congr fun k => ?_⟩
  refine eLpNorm_congr_ae ((ae_restrict_iff' hQ.measurableSet).mpr ?_)
  filter_upwards [hae] with x hx hxQ
  simp [hx hxQ]

/-! ### `prop:orlicz` on a box -/

/-- **`prop:orlicz` (a local quartic compactness certificate), box rendering.**  Let
`Q = Π (a_i, b_i)`, `H_k ⇀ H₀` in `H¹(Q)` — encoded by the uniform `W^{1,2}(Q)` bound and
convergence of all test pairings, both implied by weak `H¹(Q)` convergence — and let `Φ` be
superlinear (`Φ(t)/t → ∞`; monotonicity is not needed) with `sup_k ∫_Q Φ(|H_k|⁴) < ∞`.  Then
`H₀ ∈ L⁴(Q)` and `H_k → H₀` strongly in `L⁴(Q)`.  Proof as in the manuscript: Rellich (via the
reflection extension) gives strong `L²(Q)` convergence, hence convergence in measure; the de la
Vallée-Poussin bound gives uniform integrability of `|H_k|⁴`; Vitali concludes. -/
theorem orlicz_box {a b : ι → ℝ} (hab : ∀ i, a i < b i) (H : ℕ → (ι → ℝ) → ℂ)
    (gH : ℕ → ι → (ι → ℝ) → ℂ) (H₀ : (ι → ℝ) → ℂ) (hW : ∀ k, MemW12 (box a b) (H k) (gH k))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤) (hB : ∀ k, w12Norm (box a b) (H k) (gH k) ≤ B)
    (hH₀ : MemLp H₀ 2 (volume.restrict (box a b)))
    (hweak : ∀ φ : (ι → ℝ) → ℝ, IsTest (box a b) φ →
      Tendsto (fun k => ∫ x, ((φ x : ℝ) : ℂ) * H k x) atTop (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * H₀ x)))
    {Φ : ℝ → ℝ} (hΦ : Tendsto (fun t => Φ t / t) atTop atTop) {M : ℝ}
    (hM : ∀ k, ∫⁻ x in box a b, ENNReal.ofReal (Φ (‖H k x‖ ^ 4)) ≤ ENNReal.ofReal M) :
    MemLp H₀ 4 (volume.restrict (box a b)) ∧
      Tendsto (fun k => eLpNorm (H k - H₀) 4 (volume.restrict (box a b))) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict (box a b)) :=
    isFiniteMeasure_restrict.mpr (volume_box_ne_top a b)
  have hL2 := tendsto_L2_box_of_weak hab H gH H₀ hW hBt hB hH₀ hweak
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
    (fun k => (hW k).memLp.1) hH₀.1 hL2
  refine SuperlinearVitali.tendsto_Lp_of_tendstoInMeasure_of_superlinear (p := 4) (by norm_num)
    (by norm_num) (fun k => (hW k).memLp.1) hmeas hΦ (M := M) fun k => ?_
  have e : ((4 : ℝ≥0∞)).toReal = ((4 : ℕ) : ℝ) := by norm_num
  simp_rw [e, Real.rpow_natCast]
  exact hM k

/-- **`prop:orlicz`, last assertion, box rendering**: a uniform `L^{4+δ}(Q)` bound (`δ > 0`)
suffices (`Φ(t) = t^{1+δ/4}`). -/
theorem orlicz_box_of_Lp_bound {a b : ι → ℝ} (hab : ∀ i, a i < b i) (H : ℕ → (ι → ℝ) → ℂ)
    (gH : ℕ → ι → (ι → ℝ) → ℂ) (H₀ : (ι → ℝ) → ℂ) (hW : ∀ k, MemW12 (box a b) (H k) (gH k))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤) (hB : ∀ k, w12Norm (box a b) (H k) (gH k) ≤ B)
    (hH₀ : MemLp H₀ 2 (volume.restrict (box a b)))
    (hweak : ∀ φ : (ι → ℝ) → ℝ, IsTest (box a b) φ →
      Tendsto (fun k => ∫ x, ((φ x : ℝ) : ℂ) * H k x) atTop (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * H₀ x)))
    {δ : ℝ} (hδ : 0 < δ) {M : ℝ}
    (hM : ∀ k, ∫⁻ x in box a b, ENNReal.ofReal (‖H k x‖ ^ (4 + δ)) ≤ ENNReal.ofReal M) :
    MemLp H₀ 4 (volume.restrict (box a b)) ∧
      Tendsto (fun k => eLpNorm (H k - H₀) 4 (volume.restrict (box a b))) atTop (𝓝 0) := by
  have hΦ : Tendsto (fun t : ℝ => t ^ (1 + δ / 4) / t) atTop atTop := by
    refine (tendsto_rpow_atTop (by positivity : 0 < δ / 4)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.rpow_add ht, Real.rpow_one, mul_div_cancel_left₀ _ ht.ne']
  refine orlicz_box hab H gH H₀ hW hBt hB hH₀ hweak hΦ (M := M) fun k => ?_
  have e : ∀ x, (‖H k x‖ ^ 4) ^ (1 + δ / 4) = ‖H k x‖ ^ (4 + δ) := by
    intro x
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1; push_cast; ring
  simp_rw [e]
  exact hM k

/-- **`prop:orlicz` for multi-component fields** (e.g. a Higgs doublet, box rendering): if each
component `H_k^c` satisfies the hypotheses of `orlicz_box` except the Orlicz bound, and the bound
holds for a pointwise norm `N_k(x) ≥ |H_k^c(x)|` (e.g. the Hermitian norm `|H_k(x)|`) with `Φ`
monotone on `[0, ∞)`, then every component converges strongly in `L⁴(Q)`. -/
theorem orlicz_box_components {a b : ι → ℝ} (hab : ∀ i, a i < b i) {m : ℕ}
    (H : ℕ → Fin m → (ι → ℝ) → ℂ) (gH : ℕ → Fin m → ι → (ι → ℝ) → ℂ)
    (H₀ : Fin m → (ι → ℝ) → ℂ) (hW : ∀ k c, MemW12 (box a b) (H k c) (gH k c))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤) (hB : ∀ k c, w12Norm (box a b) (H k c) (gH k c) ≤ B)
    (hH₀ : ∀ c, MemLp (H₀ c) 2 (volume.restrict (box a b)))
    (hweak : ∀ c, ∀ φ : (ι → ℝ) → ℝ, IsTest (box a b) φ →
      Tendsto (fun k => ∫ x, ((φ x : ℝ) : ℂ) * H k c x) atTop
        (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * H₀ c x)))
    (Nk : ℕ → (ι → ℝ) → ℝ) (hN : ∀ k c x, ‖H k c x‖ ≤ Nk k x)
    {Φ : ℝ → ℝ} (hΦm : MonotoneOn Φ (Ici 0)) (hΦ : Tendsto (fun t => Φ t / t) atTop atTop)
    {M : ℝ} (hM : ∀ k, ∫⁻ x in box a b, ENNReal.ofReal (Φ (Nk k x ^ 4)) ≤ ENNReal.ofReal M) :
    ∀ c, MemLp (H₀ c) 4 (volume.restrict (box a b)) ∧
      Tendsto (fun k => eLpNorm (H k c - H₀ c) 4 (volume.restrict (box a b))) atTop (𝓝 0) := by
  intro c
  refine orlicz_box hab (fun k => H k c) (fun k => gH k c) (H₀ c) (fun k => hW k c) hBt
    (fun k => hB k c) (hH₀ c) (hweak c) hΦ (M := M) fun k => (lintegral_mono fun x => ?_).trans
    (hM k)
  refine ENNReal.ofReal_le_ofReal (hΦm (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr ?_) ?_)
  · exact (by positivity : (0 : ℝ) ≤ ‖H k c x‖ ^ 4).trans
      (pow_le_pow_left₀ (norm_nonneg _) (hN k c x) 4)
  · exact pow_le_pow_left₀ (norm_nonneg _) (hN k c x) 4

/-! ### Non-vacuity -/

theorem pd_const (z : ℂ) (i : ι) : pd (fun _ : ι → ℝ => z) i = fun _ => 0 := by
  funext x; simp [pd]

/-- Constant functions lie in `W^{1,2}` of a box, with zero weak gradient. -/
theorem memW12_const_box (a b : ι → ℝ) (z : ℂ) :
    MemW12 (box a b) (fun _ => z) (fun _ _ => 0) := by
  have : IsFiniteMeasure (volume.restrict (box a b)) :=
    isFiniteMeasure_restrict.mpr (volume_box_ne_top a b)
  refine ⟨memLp_const z, fun _ => memLp_const 0, fun i => ?_⟩
  have := hasWeakPartial_of_contDiff (box a b) (u := fun _ : ι → ℝ => z) contDiff_const i
  rwa [pd_const] at this

/-- Non-vacuity of `orlicz_box_of_Lp_bound` (hence of `orlicz_box`): the constant sequence
`H_k = 1` on the unit box of `ℝ⁴`. -/
example : MemLp (fun _ : Fin 4 → ℝ => (1 : ℂ)) 4 (volume.restrict (box 0 1)) ∧
    Tendsto (fun _ : ℕ => eLpNorm ((fun _ : Fin 4 → ℝ => (1 : ℂ)) - fun _ => 1) 4
      (volume.restrict (box 0 1))) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict (box (0 : Fin 4 → ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (volume_box_ne_top 0 1)
  refine orlicz_box_of_Lp_bound (ι := Fin 4) (fun _ => zero_lt_one) (fun _ => fun _ => (1 : ℂ))
    (fun _ _ _ => 0) (fun _ => 1) (fun _ => memW12_const_box 0 1 1)
    (B := w12Norm (box 0 1) (fun _ => (1 : ℂ)) (fun _ _ => 0)) ?_ (fun _ => le_rfl)
    (memLp_const 1) (fun φ _ => tendsto_const_nhds) (δ := 1) one_pos
    (M := (volume (box (0 : Fin 4 → ℝ) 1)).toReal) fun _ => ?_
  · unfold w12Norm
    exact ENNReal.add_ne_top.mpr ⟨(memLp_const (1 : ℂ)).eLpNorm_ne_top, by simp⟩
  · simp only [norm_one, Real.one_rpow, ENNReal.ofReal_one, lintegral_const, one_mul,
      Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [ENNReal.ofReal_toReal (volume_box_ne_top 0 1)]
    exact le_rfl

end RenewalGeometry.SobolevOpen
