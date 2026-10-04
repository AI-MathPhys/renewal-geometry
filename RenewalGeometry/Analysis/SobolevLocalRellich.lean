/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevTorusBridge

/-!
# Rellich–Kondrachov compactness on `ℝ^d`: compact support and interior versions

Generic infrastructure (no renewal notions).

* `eLpNorm_eq_torus`: `L²` norms of functions carried by the cube `c + L (0,1]^ι` are rescaled
  `L²(𝕋^ι)` norms of their periodisations.
* `rellich_ball` (**Rellich, compact support**): a sequence bounded in `W^{1,2}(ℝ^ι)` whose
  members (and weak gradients) vanish off a fixed ball has a subsequence converging strongly in
  `L²(ℝ^ι)`.  Proof: periodisation (`SobolevTorusBridge.lean`) and the torus Rellich theorem
  `TorusSobolev.rellich_L2`.
* `exists_cutoff`, `cutoff_ball`: smooth cutoffs `χ ∈ C_c^∞(Ω)`, `χ = 1` near a compact `K`, and
  the resulting `W^{1,2}(Ω) → W^{1,2}_c(ℝ^ι)` map `u ↦ χ u` with its bound;
* `rellich_interior` (**interior Rellich**): a sequence bounded in `W^{1,2}(Ω)`, `Ω ⊂ ℝ^ι` open,
  has, for every compact `K ⊂ Ω`, a subsequence converging strongly in `L²(K)` (cutoff
  `χ ∈ C_c^∞(Ω)`, `χ = 1` on `K`, and `rellich_ball`).
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal ContDiff Real Manifold

noncomputable section

namespace RenewalGeometry.SobolevOpen

open TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurableEmbedding_affine (c : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    MeasurableEmbedding (fun y : ι → ℝ => c + L • y) := by
  have h := ((Homeomorph.smulOfNeZero L hL.ne').trans (Homeomorph.addLeft c)).measurableEmbedding
  convert h using 1
  funext y
  simp [Homeomorph.trans_apply]

/-- `∫⁻ F(c + L y) dy = L^{-d} ∫⁻ F`. -/
theorem lintegral_comp_affine (F : (ι → ℝ) → ℝ≥0∞) (c : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    ∫⁻ y, F (c + L • y) = ENNReal.ofReal ((L ^ Fintype.card ι)⁻¹) * ∫⁻ x, F x := by
  rw [(measurePreserving_affine c hL).lintegral_comp_emb (measurableEmbedding_affine c hL),
    lintegral_smul_measure, smul_eq_mul]

theorem torusRep_mem (t : UnitAddTorus ι) : torusRep t ∈ unitCube := by
  intro i
  have := (AddCircle.equivIoc 1 0 (t i)).2
  simpa [torusRep] using this

/-- `‖w‖_{L²(ℝ^ι)} = L^{d/2} ‖w(c + L rep ·)‖_{L²(𝕋^ι)}` for `w` vanishing on `c + L y`,
`y ∉ (0,1]^ι`. -/
theorem eLpNorm_eq_torus (w : (ι → ℝ) → ℂ) (c : ι → ℝ) {L : ℝ} (hL : 0 < L)
    (hw : ∀ y, y ∉ unitCube → w (c + L • y) = 0) :
    eLpNorm w 2 volume = ENNReal.ofReal (L ^ Fintype.card ι) ^ (1 / 2 : ℝ) *
      eLpNorm (fun t => w (c + L • torusRep t)) 2 volume := by
  have hl : ∫⁻ x, ‖w x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (L ^ Fintype.card ι) *
      ∫⁻ t, ‖w (c + L • torusRep t)‖ₑ ^ (2 : ℝ) := by
    rw [lintegral_torus_eq_unitCube]
    have e1 : ∫⁻ y in unitCube, ‖w (c + L • torusRep fun i => (y i : UnitAddCircle))‖ₑ ^ (2 : ℝ) =
        ∫⁻ y in unitCube, ‖w (c + L • y)‖ₑ ^ (2 : ℝ) :=
      setLIntegral_congr_fun measurableSet_unitCube fun y hy => by rw [torusRep_mk hy]
    rw [e1, setLIntegral_eq_of_support_subset (fun y hy => by
      by_contra hn; exact hy (by simp [hw y hn])),
      lintegral_comp_affine (fun x => ‖w x‖ₑ ^ (2 : ℝ)) c hL, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
      one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [hl, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

/-- `∫ ‖f‖² ≤ B²` from `‖f‖_{L²} ≤ B`. -/
theorem integral_norm_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) {B : ℝ≥0∞} (hB : eLpNorm f 2 μ ≤ B) (hBt : B ≠ (⊤ : ℝ≥0∞)) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ B.toReal ^ 2 := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  simp only [ENNReal.toReal_ofNat] at h
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun x => by positivity
  have h2 : (eLpNorm f 2 μ).toReal = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by
    rw [h, ENNReal.toReal_ofReal (by positivity)]
  have h3 : (eLpNorm f 2 μ).toReal ≤ B.toReal := ENNReal.toReal_mono hBt hB
  have h4 : ∫ x, ‖f x‖ ^ 2 ∂μ = ((eLpNorm f 2 μ).toReal) ^ 2 := by
    rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul hI]
    norm_num
  rw [h4]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg h3 2


/-- The function on `ℝ^ι` carried by the cube `c + L(0,1]^ι` whose periodisation is the torus
function `G` (inverse of `periodize`). -/
def unperiodize (R : ℝ) (G : UnitAddTorus ι → ℂ) (x : ι → ℝ) : ℂ :=
  unitCube.indicator (fun y => G (fun i => (y i : UnitAddCircle)))
    ((cubeSide R)⁻¹ • (x - cubeCorner R))

theorem unperiodize_affine {R : ℝ} (hR : 0 ≤ R) (G : UnitAddTorus ι → ℂ) (y : ι → ℝ) :
    unperiodize R G (cubeCorner R + cubeSide R • y) =
      unitCube.indicator (fun y => G (fun i => (y i : UnitAddCircle))) y := by
  unfold unperiodize
  congr 1
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (cubeSide_pos hR).ne', one_smul]

theorem unperiodize_rep {R : ℝ} (hR : 0 ≤ R) (G : UnitAddTorus ι → ℂ) (t : UnitAddTorus ι) :
    unperiodize R G (cubeCorner R + cubeSide R • torusRep t) = G t := by
  rw [unperiodize_affine hR, indicator_of_mem (torusRep_mem t), mk_torusRep]

theorem stronglyMeasurable_unperiodize (R : ℝ) {G : UnitAddTorus ι → ℂ}
    (hG : StronglyMeasurable G) : StronglyMeasurable (unperiodize R G) := by
  have hmk : Measurable fun y : ι → ℝ => (fun i => (y i : UnitAddCircle)) :=
    measurable_pi_lambda _ fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i)
  have h1 : StronglyMeasurable
      (unitCube.indicator fun y : ι → ℝ => G (fun i => (y i : UnitAddCircle))) :=
    (hG.comp_measurable hmk).indicator measurableSet_unitCube
  have hm : Measurable fun x : ι → ℝ => (cubeSide R)⁻¹ • (x - cubeCorner R) := by fun_prop
  exact h1.comp_measurable hm

/-- **Rellich–Kondrachov for compactly supported `W^{1,2}` functions.**  A sequence `u_k`
bounded in `W^{1,2}(ℝ^ι)` (`‖u_k‖_{W^{1,2}} ≤ B < ∞`) with `u_k` and its weak gradient
vanishing outside the ball of radius `R` has a subsequence converging **strongly in `L²(ℝ^ι)`**
to some `v ∈ L²`. -/
theorem rellich_ball {R : ℝ} (hR : 0 ≤ R) (u : ℕ → (ι → ℝ) → ℂ) (g : ℕ → ι → (ι → ℝ) → ℂ)
    (hW : ∀ k, MemW12 univ (u k) (g k)) (hu0 : ∀ k x, R < ‖x‖ → u k x = 0)
    (hg0 : ∀ k i x, R < ‖x‖ → g k i x = 0) {B : ℝ≥0∞} (hBt : B ≠ ⊤)
    (hB : ∀ k, w12Norm univ (u k) (g k) ≤ B) :
    ∃ (φ : ℕ → ℕ) (v : (ι → ℝ) → ℂ), StrictMono φ ∧ MemLp v 2 volume ∧
      Tendsto (fun k => eLpNorm (u (φ k) - v) 2 volume) atTop (𝓝 0) := by
  set L := cubeSide R
  set c := cubeCorner (ι := ι) R
  have hL : 0 < L := cubeSide_pos hR
  have hu2 : ∀ k, MemLp (u k) 2 volume := fun k => by simpa using (hW k).memLp
  have hg2 : ∀ k i, MemLp (g k i) 2 volume := fun k i => by simpa using (hW k).memLp_grad i
  set f : ℕ → L²(UnitAddTorus ι) := fun k => (memLp_periodize hR (hu2 k)).toLp _
  have hf_ae : ∀ k, ⇑(f k) =ᵐ[volume] periodize R (u k) := fun k =>
    (memLp_periodize hR (hu2 k)).coeFn_toLp
  have hcoef : ∀ k, mFourierCoeff ⇑(f k) = mFourierCoeff (periodize R (u k)) := by
    intro k; funext n; unfold mFourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hf_ae k] with t ht
    rw [ht]
  have hb := fun k => sobSq_one_periodize hR (hW k) (hu0 k) (hg0 k)
  have hMem : ∀ k, MemH 1 ⇑(f k) := fun k => by
    unfold MemH; rw [hcoef]; exact (hb k).1
  -- uniform `H¹(𝕋^ι)` bound
  have hBu : ∀ k, ∫ x, ‖u k x‖ ^ 2 ≤ B.toReal ^ 2 := fun k => by
    refine integral_norm_sq_le (hu2 k) ((le_trans ?_ (hB k))) hBt
    unfold w12Norm; rw [Measure.restrict_univ]; exact le_self_add
  have hBg : ∀ k i, ∫ x, ‖g k i x‖ ^ 2 ≤ B.toReal ^ 2 := fun k i => by
    refine integral_norm_sq_le (hg2 k i) ((le_trans ?_ (hB k))) hBt
    unfold w12Norm; rw [Measure.restrict_univ]
    exact le_add_left (Finset.single_le_sum (f := fun i => eLpNorm (g k i) 2 volume)
      (fun _ _ => zero_le) (Finset.mem_univ i))
  set B' : ℝ := (L ^ Fintype.card ι)⁻¹ *
    (B.toReal ^ 2 + L ^ 2 * (Fintype.card ι * B.toReal ^ 2))
  have hbound : ∀ k, sobSq 1 ⇑(f k) ≤ B' := by
    intro k
    have e : sobSq 1 ⇑(f k) = sobSq 1 (periodize R (u k)) := by unfold sobSq; rw [hcoef]
    rw [e, (hb k).2]
    refine mul_le_mul_of_nonneg_left (add_le_add (hBu k) ?_) (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ i, ∫ x, ‖g k i x‖ ^ 2 ≤ ∑ _i : ι, B.toReal ^ 2 := Finset.sum_le_sum fun i _ => hBg k i
      _ = Fintype.card ι * B.toReal ^ 2 := by simp
  obtain ⟨φ, G, hφ, -, -, -, hlim⟩ :=
    rellich_L2 (t := 0) (s := 1) one_pos zero_le_one f hMem hbound
  -- `L²(𝕋^ι)` convergence of the periodisations
  have hn : Tendsto (fun k => ‖f (φ k) - G‖) atTop (𝓝 0) := by
    have e : ∀ k, ‖f (φ k) - G‖ = Real.sqrt (sobSq 0 ⇑(f (φ k) - G)) := fun k =>
      (sobNorm_zero_eq_norm _).symm
    simp_rw [e]
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hlim
  have htor : Tendsto (fun k => eLpNorm (fun t => periodize R (u (φ k)) t - G t) 2 volume)
      atTop (𝓝 0) := by
    have e : ∀ k, eLpNorm (fun t => periodize R (u (φ k)) t - G t) 2 volume =
        ENNReal.ofReal ‖f (φ k) - G‖ := by
      intro k
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      refine eLpNorm_congr_ae ?_
      filter_upwards [hf_ae (φ k), Lp.coeFn_sub (f (φ k)) G] with t h1 h2
      rw [h2, Pi.sub_apply, h1]
    simp_rw [e]
    simpa using ENNReal.tendsto_ofReal hn
  set v := unperiodize R ⇑G
  have hvm : AEStronglyMeasurable v volume :=
    (stronglyMeasurable_unperiodize R (Lp.stronglyMeasurable G)).aestronglyMeasurable
  have hv0 : ∀ y, y ∉ unitCube → v (c + L • y) = 0 := fun y hy => by
    simp only [v]; rw [unperiodize_affine hR, indicator_of_notMem hy]
  have hconst : ENNReal.ofReal (L ^ Fintype.card ι) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  refine ⟨φ, v, hφ, ⟨hvm, ?_⟩, ?_⟩
  · rw [eLpNorm_eq_torus v c hL hv0]
    have e : (fun t => v (c + L • torusRep t)) = ⇑G := funext fun t => unperiodize_rep hR _ t
    rw [e]
    exact ENNReal.mul_lt_top hconst.lt_top (Lp.eLpNorm_lt_top G)
  · have e : ∀ k, eLpNorm (u (φ k) - v) 2 volume = ENNReal.ofReal (L ^ Fintype.card ι) ^
        (1 / 2 : ℝ) * eLpNorm (fun t => periodize R (u (φ k)) t - G t) 2 volume := by
      intro k
      rw [eLpNorm_eq_torus (u (φ k) - v) c hL (fun y hy => by
        rw [Pi.sub_apply, hv0 y hy, hu0 _ _ (lt_norm_affine_of_notMem hR hy), sub_zero])]
      congr 2
      funext t
      simp only [Pi.sub_apply, periodize, v]
      exact congrArg (u (φ k) (c + L • torusRep t) - ·) (unperiodize_rep hR _ t)
    simp_rw [e]
    simpa using ENNReal.Tendsto.const_mul htor (Or.inr hconst)


/-! ### Cutoffs and interior Rellich -/

/-- **Smooth cutoff**: for a compact `K` inside an open `Ω` there is `χ ∈ C_c^∞(Ω)` with
`0 ≤ χ ≤ 1` and `χ = 1` on a neighbourhood of `K`. -/
theorem exists_cutoff {Ω K : Set (ι → ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : (ι → ℝ) → ℝ, IsTest Ω χ ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨t, ht, hKt, htΩ⟩ := exists_compact_between hK hΩ hKΩ
  obtain ⟨f, h1, h0, hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, ι → ℝ)) hK.isClosed hKt (n := (⊤ : ℕ∞))
  have hcs : HasCompactSupport (f : (ι → ℝ) → ℝ) := HasCompactSupport.intro ht h0
  have hts : tsupport (f : (ι → ℝ) → ℝ) ⊆ t :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (h0 x hn)) ht.isClosed
  exact ⟨f, ⟨contMDiff_iff_contDiff.mp f.contMDiff, hcs, hts.trans htΩ⟩, h1, hf⟩

theorem IsTest.exists_bound {Ω : Set (ι → ℝ)} {χ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ) :
    ∃ M : ℝ≥0, ∀ x, ‖χ x‖ ≤ M := by
  obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hχ.compact
  exact ⟨C.toNNReal, fun x => (hC x).trans (Real.le_coe_toNNReal C)⟩

theorem IsTest.exists_bound_pd {Ω : Set (ι → ℝ)} {χ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ) :
    ∃ M : ℝ≥0, ∀ i x, ‖pd χ i x‖ ≤ M := by
  have h1 : ContDiff ℝ 1 χ := hχ.smooth.of_le (by simp)
  have hb : ∀ i, ∃ C : ℝ, ∀ x, ‖pd χ i x‖ ≤ C := fun i =>
    (continuous_pd h1 i).bounded_above_of_compact_support (hasCompactSupport_pd hχ.compact i)
  choose C hC using hb
  refine ⟨(∑ i, (C i).toNNReal), fun i x => (hC i x).trans ?_⟩
  refine (Real.le_coe_toNNReal (C i)).trans ?_
  push_cast
  exact Finset.single_le_sum (f := fun i => ((C i).toNNReal : ℝ)) (fun _ _ => by positivity)
    (Finset.mem_univ i)

/-- The cutoff data: `χ u ∈ W^{1,2}(ℝ^ι)`, vanishing (with its gradient) outside a ball,
with `‖χ u‖_{W^{1,2}(ℝ^ι)} ≤ C ‖u‖_{W^{1,2}(Ω)}`. -/
theorem cutoff_ball {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) {χ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ) :
    ∃ (R : ℝ) (C : ℝ≥0), 0 ≤ R ∧ (∀ x, R < ‖x‖ → χ x = 0) ∧ (∀ i x, R < ‖x‖ → pd χ i x = 0) ∧
      ∀ (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ), MemW12 Ω u g →
        MemW12 univ (fun x => ((χ x : ℝ) : ℂ) * u x)
          (fun i x => ((χ x : ℝ) : ℂ) * g i x + ((pd χ i x : ℝ) : ℂ) * u x) ∧
        w12Norm univ (fun x => ((χ x : ℝ) : ℂ) * u x)
          (fun i x => ((χ x : ℝ) : ℂ) * g i x + ((pd χ i x : ℝ) : ℂ) * u x) ≤
          C * w12Norm Ω u g := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  obtain ⟨M', hM'⟩ := hχ.exists_bound_pd
  obtain ⟨R, hR⟩ := hχ.compact.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, M + Fintype.card ι * M', le_max_right _ _, fun x hx => ?_, fun i x hx => ?_,
    fun u g hu => ?_⟩
  · refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have := hR h
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt (le_max_left _ _) hx)) (lt_irrefl _)
  · refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have := hR (tsupport_pd_subset χ i h)
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt (le_max_left _ _) hx)) (lt_irrefl _)
  · obtain ⟨h1, h2⟩ := hu.mul_test hΩ hχ hM hM'
    exact ⟨h1, by simpa using h2⟩

/-- **Interior Rellich–Kondrachov.**  Let `Ω ⊂ ℝ^ι` be open, `K ⊂ Ω` compact, and `u_k` bounded
in `W^{1,2}(Ω)`.  Then a subsequence converges **strongly in `L²(K)`**. -/
theorem rellich_interior {Ω K : Set (ι → ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (u : ℕ → (ι → ℝ) → ℂ) (g : ℕ → ι → (ι → ℝ) → ℂ) (hW : ∀ k, MemW12 Ω (u k) (g k))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤) (hB : ∀ k, w12Norm Ω (u k) (g k) ≤ B) :
    ∃ (φ : ℕ → ℕ) (v : (ι → ℝ) → ℂ), StrictMono φ ∧ MemLp v 2 volume ∧
      Tendsto (fun k => eLpNorm (u (φ k) - v) 2 (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨χ, hχ, hχ1, -⟩ := exists_cutoff hΩ hK hKΩ
  obtain ⟨R, C, hR, hχ0, hpd0, hcut⟩ := cutoff_ball hΩ hχ
  have hW' := fun k => (hcut (u k) (g k) (hW k)).1
  have hB' := fun k => (hcut (u k) (g k) (hW k)).2
  obtain ⟨φ, v, hφ, hv, hlim⟩ := rellich_ball hR (fun k x => ((χ x : ℝ) : ℂ) * u k x)
    (fun k i x => ((χ x : ℝ) : ℂ) * g k i x + ((pd χ i x : ℝ) : ℂ) * u k x) hW'
    (fun k x hx => by simp [hχ0 x hx])
    (fun k i x hx => by simp [hχ0 x hx, hpd0 i x hx])
    (B := C * B) (ENNReal.mul_ne_top ENNReal.coe_ne_top hBt)
    (fun k => (hB' k).trans (by gcongr; exact hB k))
  refine ⟨φ, v, hφ, hv, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le)
    (fun k => ?_)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have e : eLpNorm (u (φ k) - v) 2 (volume.restrict K) =
      eLpNorm ((fun x => ((χ x : ℝ) : ℂ) * u (φ k) x) - v) 2 (volume.restrict K) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' hKm).mpr (Eventually.of_forall fun x hx => ?_))
    simp [hχ1.self_of_nhdsSet x hx]
  rw [e]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

end RenewalGeometry.SobolevOpen
