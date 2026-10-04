/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TorusSobolevEmbedding

/-!
# De la Vallée-Poussin uniform integrability, Vitali, and strong `L^p` convergence

Generic measure theory (no renewal notions) for `prop:orlicz` of the Einstein–Standard-Model
action-closure manuscript ("a local quartic compactness certificate").

* `unifIntegrable_of_superlinear` (**de la Vallée-Poussin**): if `Φ(t)/t → ∞` and
  `sup_i ∫ Φ(|f_i|^p) < ∞`, then `{f_i}` is uniformly integrable in `L^p` (on the set
  `{|f_i| ≥ C}` one has `|f_i|^p ≤ η Φ(|f_i|^p)` with `η → 0` as `C → ∞`).
* `tendsto_Lp_of_tendstoInMeasure_of_superlinear` (**Vitali step**): on a finite measure space,
  convergence in measure plus the superlinear bound give `g ∈ L^p` and `‖f_n - g‖_p → 0`.
  The limit's integrability comes from Fatou along an a.e. convergent subsequence.
* `orlicz_torus` (`prop:orlicz`, periodic rendering): on `𝕋^d`, `H_h ⇀ H` weakly in `H¹`
  (bounded in `H¹` with converging Fourier coefficients) and `sup_h ∫ Φ(|H_h|⁴) < ∞` give
  `H_h → H` strongly in `L⁴`; `orlicz_torus_of_Lp_bound` is the `L^{4+δ}` case `Φ(t) = t^{1+δ/4}`.
  The full sequence converges in `L²` (`tendsto_L2_of_weak_H1`: Rellich on `𝕋^d` plus
  identification of all subsequential limits through the Fourier coefficients).
-/

open Filter Topology MeasureTheory UnitAddTorus
open scoped BigOperators Real ENNReal NNReal

namespace RenewalGeometry.SuperlinearVitali

set_option linter.unusedSectionVars false

noncomputable section

section General

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/-- A superlinear `Φ` eventually dominates any multiple of the identity:
for `η > 0` there is `B > 0` with `t ≤ η Φ(t)` for `t ≥ B`. -/
theorem exists_le_mul_of_superlinear {Φ : ℝ → ℝ} (hΦ : Tendsto (fun t => Φ t / t) atTop atTop)
    {η : ℝ} (hη : 0 < η) : ∃ B : ℝ, 0 < B ∧ ∀ t, B ≤ t → t ≤ η * Φ t := by
  obtain ⟨B, hB⟩ := (hΦ.eventually (eventually_ge_atTop η⁻¹)).exists_forall_of_atTop
  refine ⟨max B 1, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have h := hB t (le_trans (le_max_left _ _) ht)
  rw [le_div_iff₀ ht0] at h
  have := mul_le_mul_of_nonneg_left h hη.le
  rwa [← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul] at this

/-- **De la Vallée-Poussin tail estimate** (`prop:orlicz`): if `Φ(t)/t → ∞` and
`∫ Φ(|f_i|^p) ≤ M` for all `i`, then `‖1_{|f_i| ≥ C} f_i‖_{L^p} ≤ ε` uniformly in `i` for `C`
large (`0 < p < ∞`). -/
theorem exists_tail_le_of_superlinear {ι : Type*} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {f : ι → α → E} {Φ : ℝ → ℝ}
    (hΦ : Tendsto (fun t => Φ t / t) atTop atTop) {M : ℝ}
    (hM : ∀ i, ∫⁻ x, ENNReal.ofReal (Φ (‖f i x‖ ^ p.toReal)) ∂μ ≤ ENNReal.ofReal M)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({x | C ≤ ‖f i x‖₊}.indicator (f i)) p μ ≤ ENNReal.ofReal ε := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set M' : ℝ := max M 0 + 1
  have hM' : 0 < M' := by positivity
  set η : ℝ := ε ^ p.toReal / M'
  have hη : 0 < η := by positivity
  obtain ⟨B, hB0, hB⟩ := exists_le_mul_of_superlinear hΦ hη
  set C : ℝ≥0 := Real.toNNReal (B ^ p.toReal⁻¹) with hCdef
  refine ⟨C, fun i => ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  -- pointwise domination on the large-value set
  have hpt : ∀ x, ‖({x | C ≤ ‖f i x‖₊}.indicator (f i) x)‖ₑ
      ^ p.toReal ≤ ENNReal.ofReal η * ENNReal.ofReal (Φ (‖f i x‖ ^ p.toReal)) := by
    intro x
    by_cases hx : x ∈ {x | C ≤ ‖f i x‖₊}
    · rw [Set.indicator_of_mem hx]
      simp only [Set.mem_setOf_eq] at hx
      have hx' : B ^ p.toReal⁻¹ ≤ ‖f i x‖ := by
        have := NNReal.coe_le_coe.mpr hx
        rwa [hCdef, Real.coe_toNNReal _ (by positivity), coe_nnnorm] at this
      have hBt : B ≤ ‖f i x‖ ^ p.toReal := by
        have := Real.rpow_le_rpow (by positivity) hx' hpr.le
        rwa [← Real.rpow_mul hB0.le, inv_mul_cancel₀ hpr.ne', Real.rpow_one] at this
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpr.le,
        ← ENNReal.ofReal_mul hη.le]
      exact ENNReal.ofReal_le_ofReal (hB _ hBt)
    · rw [Set.indicator_of_notMem hx, enorm_zero, ENNReal.zero_rpow_of_pos hpr]
      exact zero_le
  have hint : ∫⁻ x, ‖({x | C ≤ ‖f i x‖₊}.indicator
      (f i) x)‖ₑ ^ p.toReal ∂μ ≤ ENNReal.ofReal (ε ^ p.toReal) := by
    calc _ ≤ ∫⁻ x, ENNReal.ofReal η * ENNReal.ofReal (Φ (‖f i x‖ ^ p.toReal)) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal η * ∫⁻ x, ENNReal.ofReal (Φ (‖f i x‖ ^ p.toReal)) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal η * ENNReal.ofReal M' := by
          gcongr
          exact (hM i).trans (ENNReal.ofReal_le_ofReal (by
            have := le_max_left M 0; simp only [M']; linarith))
      _ = ENNReal.ofReal (ε ^ p.toReal) := by
          rw [← ENNReal.ofReal_mul hη.le]
          congr 1
          simp only [η]
          field_simp
  calc (∫⁻ x, ‖({x | C ≤ ‖f i x‖₊}.indicator
      (f i) x)‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal (ε ^ p.toReal)) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← Real.rpow_mul hε.le, mul_one_div_cancel hpr.ne', Real.rpow_one]

/-- **De la Vallée-Poussin criterion** (`prop:orlicz`): if `Φ(t)/t → ∞` and
`∫ Φ(|f_i|^p) ≤ M` for all `i`, then the family `f_i` is uniformly integrable in `L^p`
(`1 ≤ p < ∞`). -/
theorem unifIntegrable_of_superlinear {ι : Type*} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : ι → α → E} (hf : ∀ i, AEStronglyMeasurable (f i) μ) {Φ : ℝ → ℝ}
    (hΦ : Tendsto (fun t => Φ t / t) atTop atTop) {M : ℝ}
    (hM : ∀ i, ∫⁻ x, ENNReal.ofReal (Φ (‖f i x‖ ^ p.toReal)) ∂μ ≤ ENNReal.ofReal M) :
    UnifIntegrable f p μ :=
  unifIntegrable_of hp1 hp hf
    (exists_tail_le_of_superlinear (lt_of_lt_of_le one_pos hp1).ne' hp hΦ hM)

/-- **Uniform integrability in the probability sense** (with a uniform `L^p` bound) under the
superlinear bound, on a finite measure space. -/
theorem uniformIntegrable_of_superlinear [IsFiniteMeasure μ] {ι : Type*} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : ι → α → E} (hf : ∀ i, AEStronglyMeasurable (f i) μ) {Φ : ℝ → ℝ}
    (hΦ : Tendsto (fun t => Φ t / t) atTop atTop) {M : ℝ}
    (hM : ∀ i, ∫⁻ x, ENNReal.ofReal (Φ (‖f i x‖ ^ p.toReal)) ∂μ ≤ ENNReal.ofReal M) :
    UniformIntegrable f p μ :=
  uniformIntegrable_of hp1 hp hf
    (exists_tail_le_of_superlinear (lt_of_lt_of_le one_pos hp1).ne' hp hΦ hM)

/-- **Vitali step with a superlinear bound** (`prop:orlicz`): on a finite measure space, if
`f_n → g` in measure and `∫ Φ(|f_n|^p) ≤ M` with `Φ(t)/t → ∞`, `1 ≤ p < ∞`, then `g ∈ L^p` and
`‖f_n - g‖_{L^p} → 0`. -/
theorem tendsto_Lp_of_tendstoInMeasure_of_superlinear [IsFiniteMeasure μ] {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℕ → α → E} {g : α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hfg : TendstoInMeasure μ f atTop g)
    {Φ : ℝ → ℝ} (hΦ : Tendsto (fun t => Φ t / t) atTop atTop) {M : ℝ}
    (hM : ∀ n, ∫⁻ x, ENNReal.ofReal (Φ (‖f n x‖ ^ p.toReal)) ∂μ ≤ ENNReal.ofReal M) :
    MemLp g p μ ∧ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  obtain ⟨-, hui, C, hC⟩ := uniformIntegrable_of_superlinear hp1 hp hf hΦ hM
  obtain ⟨ns, -, hae⟩ := hfg.exists_seq_tendsto_ae
  have hg : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (ns n)) hae
  have hgp : eLpNorm g p μ ≤ C := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => hf (ns n)) g hae).trans ?_
    exact liminf_le_of_frequently_le' (Frequently.of_forall fun n => hC (ns n))
  have hmem : MemLp g p μ := ⟨hg, lt_of_le_of_lt hgp ENNReal.coe_lt_top⟩
  exact ⟨hmem, tendsto_Lp_finite_of_tendstoInMeasure hp1 hp hf hmem hui hfg⟩

end General

section Torus

open RenewalGeometry.TorusSobolev

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-- **Weak `H^s` convergence implies strong `L²` convergence on `𝕋^d`** (`s > 0`; Rellich for the
full sequence).  Weak convergence `H_k ⇀ H₀` in `H^s` is encoded by its standard equivalent for
sequences in a Hilbert space: a uniform `H^s` bound together with convergence of every Fourier
coefficient (the monomials span a dense subspace).  Every subsequence has, by `rellich_coeff`, a
further subsequence converging in `L²`, whose limit is identified as `H₀` by its coefficients. -/
theorem tendsto_L2_of_weak_H1 {s : ℝ} (hs : 0 < s) (H : ℕ → L²(UnitAddTorus d))
    (H₀ : L²(UnitAddTorus d)) {B : ℝ} (hH : ∀ k, MemH s (H k)) (hB : ∀ k, sobSq s (H k) ≤ B)
    (hcoef : ∀ n, Tendsto (fun k => mFourierCoeff (H k) n) atTop (𝓝 (mFourierCoeff H₀ n))) :
    Tendsto H atTop (𝓝 H₀) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, cl, hφ, h1, -, -, -, h5⟩ := rellich_coeff (t := 0) hs
    (fun k => mFourierCoeff (H (ns k))) (fun k => hH (ns k)) (fun k => hB (ns k))
  have hcl : cl = mFourierCoeff H₀ := funext fun n =>
    tendsto_nhds_unique (h1 n) ((hcoef n).comp (hns.comp hφ.tendsto_atTop))
  refine ⟨φ, ?_⟩
  have e : ∀ k, ‖H (ns (φ k)) - H₀‖ =
      Real.sqrt (coeffSobSq 0 (mFourierCoeff (H (ns (φ k))) - cl)) := by
    intro k
    rw [← sobNorm_zero_eq_norm, sobNorm, sobSq, hcl]
    congr 2
    funext n
    exact mFourierCoeff_Lp_sub _ _ n
  have := (Real.continuous_sqrt.tendsto 0).comp h5
  simp only [Real.sqrt_zero] at this
  refine this.congr fun k => ?_
  simp only [Function.comp_apply]
  exact (e k).symm

/-- **`prop:orlicz` on the torus `𝕋^d`** (periodic rendering of "a local quartic compactness
certificate"): let `H_k ⇀ H₀` weakly in `H¹(𝕋^d)` (uniform `H¹` bound and convergence of all
Fourier coefficients), and let `Φ` be superlinear (`Φ(t)/t → ∞`) with
`sup_k ∫ Φ(|H_k|⁴) < ∞`.  Then `H₀ ∈ L⁴` and `H_k → H₀` strongly in `L⁴(𝕋^d)`.
Proof as in the manuscript: Rellich gives strong `L²` convergence, hence convergence in measure;
de la Vallée-Poussin gives uniform integrability of `|H_k|⁴`; Vitali concludes. -/
theorem orlicz_torus (H : ℕ → L²(UnitAddTorus d)) (H₀ : L²(UnitAddTorus d)) {B : ℝ}
    (hH : ∀ k, MemH 1 (H k)) (hB : ∀ k, sobSq 1 (H k) ≤ B)
    (hcoef : ∀ n, Tendsto (fun k => mFourierCoeff (H k) n) atTop (𝓝 (mFourierCoeff H₀ n)))
    {Φ : ℝ → ℝ} (hΦ : Tendsto (fun t => Φ t / t) atTop atTop) {M : ℝ}
    (hM : ∀ k, ∫⁻ x, ENNReal.ofReal (Φ (‖H k x‖ ^ 4)) ≤ ENNReal.ofReal M) :
    MemLp (⇑H₀) 4 volume ∧
      Tendsto (fun k => eLpNorm (⇑(H k) - ⇑H₀) 4 volume) atTop (𝓝 0) := by
  have hL2 := tendsto_L2_of_weak_H1 one_pos H H₀ hH hB hcoef
  have hmeas := tendstoInMeasure_of_tendsto_Lp hL2
  refine tendsto_Lp_of_tendstoInMeasure_of_superlinear (p := 4) (by norm_num) (by norm_num)
    (fun k => Lp.aestronglyMeasurable (H k)) hmeas hΦ (M := M) fun k => ?_
  have e : ((4 : ℝ≥0∞)).toReal = ((4 : ℕ) : ℝ) := by norm_num
  simp_rw [e, Real.rpow_natCast]
  exact hM k

/-- **`prop:orlicz`, last assertion, on `𝕋^d`**: a uniform `L^{4+δ}` bound (`δ > 0`) suffices
(take `Φ(t) = t^{1+δ/4}`). -/
theorem orlicz_torus_of_Lp_bound (H : ℕ → L²(UnitAddTorus d)) (H₀ : L²(UnitAddTorus d)) {B : ℝ}
    (hH : ∀ k, MemH 1 (H k)) (hB : ∀ k, sobSq 1 (H k) ≤ B)
    (hcoef : ∀ n, Tendsto (fun k => mFourierCoeff (H k) n) atTop (𝓝 (mFourierCoeff H₀ n)))
    {δ : ℝ} (hδ : 0 < δ) {M : ℝ}
    (hM : ∀ k, ∫⁻ x, ENNReal.ofReal (‖H k x‖ ^ (4 + δ)) ≤ ENNReal.ofReal M) :
    MemLp (⇑H₀) 4 volume ∧
      Tendsto (fun k => eLpNorm (⇑(H k) - ⇑H₀) 4 volume) atTop (𝓝 0) := by
  have hΦ : Tendsto (fun t : ℝ => t ^ (1 + δ / 4) / t) atTop atTop := by
    refine (tendsto_rpow_atTop (by positivity : 0 < δ / 4)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.rpow_add ht, Real.rpow_one, mul_div_cancel_left₀ _ ht.ne']
  refine orlicz_torus H H₀ hH hB hcoef hΦ (M := M) fun k => ?_
  have e : ∀ x, (‖H k x‖ ^ 4) ^ (1 + δ / 4) = ‖H k x‖ ^ (4 + δ) := by
    intro x
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1; push_cast; ring
  simp_rw [e]
  exact hM k

/-- Non-vacuity of `orlicz_torus_of_Lp_bound`: the constant sequence of a monomial. -/
example (m : d → ℤ) :
    MemLp (⇑((mFourier m).toLp 2 volume ℂ)) 4 volume ∧
      Tendsto (fun _ : ℕ => eLpNorm (⇑((mFourier m).toLp 2 volume ℂ) -
        ⇑((mFourier m).toLp 2 volume ℂ)) 4 volume) atTop (𝓝 0) := by
  have hmem : MemH 1 (⇑((mFourier m).toLp 2 volume ℂ)) := by
    have := memH_mFourier (d := d) 1 m
    unfold MemH CoeffMemH at this ⊢
    simp_rw [mFourierCoeff_toLp]
    exact this
  refine orlicz_torus_of_Lp_bound (fun _ => (mFourier m).toLp 2 volume ℂ)
    ((mFourier m).toLp 2 volume ℂ) (B := sobSq 1 (⇑((mFourier m).toLp 2 volume ℂ)))
    (fun _ => hmem) (fun _ => le_rfl) (fun n => tendsto_const_nhds) (δ := 1) one_pos
    (M := 1) fun _ => ?_
  have hae := ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (mFourier m)
  calc ∫⁻ x, ENNReal.ofReal (‖((mFourier m).toLp 2 volume ℂ) x‖ ^ (4 + (1 : ℝ)))
      = ∫⁻ _x, ENNReal.ofReal 1 := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hx, norm_mFourier_apply, Real.one_rpow]
    _ = ENNReal.ofReal 1 := by simp [measure_univ]
    _ ≤ ENNReal.ofReal 1 := le_rfl

end Torus

end

end RenewalGeometry.SuperlinearVitali
