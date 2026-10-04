/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.MollifierLpConvergence

/-!
# Local product and bounded-coefficient continuity in `L^p`

The `L^p` clauses of `lem:products` of the Einstein–SM action-closure manuscript
(`papers/einstein_sm_action_closure`), on an arbitrary measure space (the manuscript works on a
compact region `K`) with values in real normed spaces (finite-dimensional fibres in the
manuscript).

* Products: `u_h → u` in `L^p`, `v_h → v` in `L^q`, `1/p + 1/q = 1/r ≤ 1` give
  `B(u_h, v_h) → B(u, v)` in `L^r` for every bounded bilinear `B`; this is
  `RenewalGeometry.LpTendsto.bilin` (`Analysis/MollifierLpConvergence.lean`).
* `eLpNorm_quadratic_sub_le`, `eLpNorm_quadratic_sub_le_of_norm_le_one`: the explicit bound
  `eq:quadratic-product`, `‖B(Y_h,Y_h) - B(Y,Y)‖_1 ≤ ‖B‖ ‖Y_h - Y‖_2 (‖Y_h‖_2 + ‖Y‖_2)`
  (constant `C = 1` for a contraction).
* `tendsto_eLpNorm_of_dominated_ae`: dominated convergence in `L^p`, `p < ∞`.
* `tendsto_eLpNorm_of_tendstoInMeasure_dominated`: the subsequence criterion behind the
  coefficient clause: if `‖F_h‖ ≤ |β_h - β| g` with `β_h → β` in measure, `|β_h - β| ≤ K`
  and `g ∈ L^p`, then `F_h → 0` in `L^p`.
* `LpTendsto.coeff`: **`eq:bounded-coefficient-product`**: `B_h` uniformly bounded,
  `B_h → B` in measure, `u_h → u` in `L^p` (`1 ≤ p < ∞`) give `B_h u_h → B u` in `L^p`.
* `LpTendsto.coeff_bilin`: the tensor clause: `u_h → u`, `v_h → v` in `L²` give
  `B_h(u_h ⊗ v_h) → B(u ⊗ v)` in `L¹` (coefficients `B_h(x)` bilinear, uniformly bounded,
  converging in measure).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RenewalGeometry.LpProductContinuity

open Mollifier

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W]

instance holderTriple_two_two_one : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

/-! ### The quadratic bound `eq:quadratic-product` -/

/-- Hölder for a bounded bilinear map, `L² × L² → L¹`. -/
theorem eLpNorm_bilin_le (B : E →L[ℝ] F →L[ℝ] W) {f : X → E} {g : X → F}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => B (f x) (g x)) 1 μ ≤ ‖B‖₊ * eLpNorm f 2 μ * eLpNorm g 2 μ :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg (fun a b => B a b) ‖B‖₊
    (Eventually.of_forall fun x => by
      rw [← NNReal.coe_le_coe]; push_cast; exact B.le_opNorm₂ (f x) (g x))

/-- **`eq:quadratic-product`.**  For a bounded bilinear `B`,
`‖B(Y_h,Y_h) - B(Y,Y)‖_1 ≤ ‖B‖ ‖Y_h - Y‖_2 (‖Y_h‖_2 + ‖Y‖_2)`. -/
theorem eLpNorm_quadratic_sub_le (B : E →L[ℝ] E →L[ℝ] W) {Yh Y : X → E}
    (hYh : AEStronglyMeasurable Yh μ) (hY : AEStronglyMeasurable Y μ) :
    eLpNorm (fun x => B (Yh x) (Yh x) - B (Y x) (Y x)) 1 μ ≤
      ‖B‖₊ * eLpNorm (Yh - Y) 2 μ * (eLpNorm Yh 2 μ + eLpNorm Y 2 μ) := by
  have hsplit : (fun x => B (Yh x) (Yh x) - B (Y x) (Y x)) =
      (fun x => B ((Yh - Y) x) (Yh x)) + fun x => B (Y x) ((Yh - Y) x) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [hsplit]
  have hm1 : AEStronglyMeasurable (fun x => B ((Yh - Y) x) (Yh x)) μ :=
    (B.continuous₂.comp_aestronglyMeasurable₂ (hYh.sub hY) hYh)
  have hm2 : AEStronglyMeasurable (fun x => B (Y x) ((Yh - Y) x)) μ :=
    (B.continuous₂.comp_aestronglyMeasurable₂ hY (hYh.sub hY))
  refine (eLpNorm_add_le hm1 hm2 le_rfl).trans ?_
  rw [mul_add]
  refine add_le_add (eLpNorm_bilin_le B (hYh.sub hY) hYh) ?_
  calc eLpNorm (fun x => B (Y x) ((Yh - Y) x)) 1 μ
      ≤ ‖B‖₊ * eLpNorm Y 2 μ * eLpNorm (Yh - Y) 2 μ := eLpNorm_bilin_le B hY (hYh.sub hY)
    _ = ‖B‖₊ * eLpNorm (Yh - Y) 2 μ * eLpNorm Y 2 μ := by ring

/-- `eq:quadratic-product` with `C = 1` for a bilinear contraction `‖B‖ ≤ 1`. -/
theorem eLpNorm_quadratic_sub_le_of_norm_le_one (B : E →L[ℝ] E →L[ℝ] W) (hB : ‖B‖ ≤ 1)
    {Yh Y : X → E} (hYh : AEStronglyMeasurable Yh μ) (hY : AEStronglyMeasurable Y μ) :
    eLpNorm (fun x => B (Yh x) (Yh x) - B (Y x) (Y x)) 1 μ ≤
      eLpNorm (Yh - Y) 2 μ * (eLpNorm Yh 2 μ + eLpNorm Y 2 μ) := by
  refine (eLpNorm_quadratic_sub_le B hYh hY).trans ?_
  have h1 : (‖B‖₊ : ℝ≥0∞) ≤ 1 := by
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]; exact hB
  calc (‖B‖₊ : ℝ≥0∞) * eLpNorm (Yh - Y) 2 μ * (eLpNorm Yh 2 μ + eLpNorm Y 2 μ)
      ≤ 1 * eLpNorm (Yh - Y) 2 μ * (eLpNorm Yh 2 μ + eLpNorm Y 2 μ) := by gcongr
    _ = _ := by rw [one_mul]

/-! ### Dominated convergence in `L^p` and the subsequence criterion -/

/-- **Dominated convergence in `L^p`, `0 < p < ∞`.** -/
theorem tendsto_eLpNorm_of_dominated_ae {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {G : ℕ → X → W} (hGm : ∀ n, AEStronglyMeasurable (G n) μ) {g : X → ℝ} (hg : MemLp g p μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ‖G n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (G n) p μ) atTop (𝓝 0) := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hint : Tendsto (fun n => ∫⁻ x, ‖G n x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 (∫⁻ _x, 0 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖g x‖ₑ ^ p.toReal)
      (fun n => ((hGm n).enorm.pow_const _)) (fun n => ?_) ?_ ?_
    · filter_upwards [hdom n] with x hx
      refine ENNReal.rpow_le_rpow ?_ hpos.le
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self _))
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hg.eLpNorm_lt_top).ne
    · filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun n => ‖G n x‖ₑ) atTop (𝓝 0) := by
        have := (continuous_enorm.tendsto (0 : W)).comp hx
        rw [enorm_zero] at this
        exact this
      have h2 := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0 |>.comp h1
      rw [ENNReal.zero_rpow_of_pos hpos] at h2
      exact h2
  rw [lintegral_zero] at hint
  have h3 := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp hint
  rw [ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / p.toReal)] at h3
  exact h3

/-- **Subsequence criterion.**  If `‖F_n‖ ≤ ‖β_n - β‖ g` a.e. with `β_n → β` in measure,
`‖β_n - β‖ ≤ K` a.e. and `0 ≤ g ∈ L^p` (`0 < p < ∞`), then `F_n → 0` in `L^p`. -/
theorem tendsto_eLpNorm_of_tendstoInMeasure_dominated {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {Z : Type*} [NormedAddCommGroup Z] {β : ℕ → X → Z} {β' : X → Z}
    (hβ : TendstoInMeasure μ β atTop β') {K : ℝ} (hK : ∀ n, ∀ᵐ x ∂μ, ‖β n x - β' x‖ ≤ K)
    {G : ℕ → X → W} (hGm : ∀ n, AEStronglyMeasurable (G n) μ) {g : X → ℝ}
    (hg : MemLp g p μ) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hG : ∀ n, ∀ᵐ x ∂μ, ‖G n x‖ ≤ ‖β n x - β' x‖ * g x) :
    Tendsto (fun n => eLpNorm (G n) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, -, hms⟩ := (hβ.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, tendsto_eLpNorm_of_dominated_ae hp0 hp (fun n => hGm _)
    (hg.const_mul (max K 0)) (fun n => ?_) ?_⟩
  · filter_upwards [hG (ns (ms n)), hK (ns (ms n)), hg0] with x h1 h2 h3
    exact h1.trans (mul_le_mul_of_nonneg_right (h2.trans (le_max_left _ _)) h3)
  · filter_upwards [hms, hg0, ae_all_iff.2 fun n => hG (ns (ms n))] with x hx hx0 hxG
    have h1 : Tendsto (fun n => ‖β (ns (ms n)) x - β' x‖ * g x) atTop (𝓝 (0 * g x)) := by
      refine (Tendsto.mul_const _ ?_)
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hx)
      simpa [Function.comp] using this
    rw [zero_mul] at h1
    exact squeeze_zero_norm (fun n => hxG n) h1

/-! ### The bounded-coefficient clause `eq:bounded-coefficient-product` -/

theorem aestronglyMeasurable_apply {β : X → E →L[ℝ] F} {u : X → E}
    (hβ : AEStronglyMeasurable β μ) (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => β x (u x)) μ :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.comp_aestronglyMeasurable
    (hβ.prodMk hu)

/-- A limit in measure of coefficients bounded by `K` is bounded by `K`. -/
theorem ae_norm_le_of_tendstoInMeasure {Z : Type*} [NormedAddCommGroup Z] {β : ℕ → X → Z}
    {β' : X → Z} (hβ : TendstoInMeasure μ β atTop β') {K : ℝ}
    (hK : ∀ n, ∀ᵐ x ∂μ, ‖β n x‖ ≤ K) : ∀ᵐ x ∂μ, ‖β' x‖ ≤ K := by
  obtain ⟨ns, -, hns⟩ := hβ.exists_seq_tendsto_ae
  filter_upwards [hns, ae_all_iff.2 fun n => hK (ns n)] with x hx hxK
  exact le_of_tendsto (continuous_norm.tendsto _ |>.comp hx) (Eventually.of_forall hxK)

/-- **`eq:bounded-coefficient-product`.**  Let `B_n` be (operator-valued) coefficients with
`sup_n ‖B_n‖_∞ ≤ K` and `B_n → B` in measure, and `u_n → u` in `L^p`, `1 ≤ p < ∞`.  Then
`B_n u_n → B u` in `L^p`. -/
theorem LpTendsto.coeff {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {β : ℕ → X → E →L[ℝ] F}
    {β' : X → E →L[ℝ] F} (hβm : ∀ n, AEStronglyMeasurable (β n) μ)
    (hβ : TendstoInMeasure μ β atTop β') {K : ℝ} (hK : ∀ n, ∀ᵐ x ∂μ, ‖β n x‖ ≤ K)
    {u : ℕ → X → E} {u' : X → E} (hu : LpTendsto μ p u u') :
    LpTendsto μ p (fun n x => β n x (u n x)) (fun x => β' x (u' x)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hβ'm : AEStronglyMeasurable β' μ := hβ.aestronglyMeasurable hβm
  have hK' := ae_norm_le_of_tendstoInMeasure hβ hK
  have hmem : ∀ (b : X → E →L[ℝ] F) (w : X → E), AEStronglyMeasurable b μ →
      (∀ᵐ x ∂μ, ‖b x‖ ≤ K) → MemLp w p μ → MemLp (fun x => b x (w x)) p μ := by
    intro b w hb hbK hw
    refine hw.of_le_mul (c := K) (aestronglyMeasurable_apply hb hw.1) ?_
    filter_upwards [hbK] with x hx
    exact ((b x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  refine ⟨fun n => hmem _ _ (hβm n) (hK n) (hu.memLp n), hmem _ _ hβ'm hK' hu.memLp_lim, ?_⟩
  -- split `B_n u_n - B u = B_n (u_n - u) + (B_n - B) u`
  have h1 : Tendsto (fun n => eLpNorm (fun x => β n x (u n x - u' x)) p μ) atTop (𝓝 0) := by
    have hb : ∀ n, eLpNorm (fun x => β n x (u n x - u' x)) p μ ≤
        ENNReal.ofReal K * eLpNorm (u n - u') p μ := fun n => by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ p
      filter_upwards [hK n] with x hx
      exact ((β n x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hb
    simpa using ENNReal.Tendsto.const_mul hu.tendsto (Or.inr ENNReal.ofReal_ne_top)
  have h2 : Tendsto (fun n => eLpNorm (fun x => (β n x - β' x) (u' x)) p μ) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_of_tendstoInMeasure_dominated hp0 hp hβ (K := K + K)
      (fun n => ?_) (fun n => aestronglyMeasurable_apply ((hβm n).sub hβ'm) hu.memLp_lim.1)
      hu.memLp_lim.norm (Eventually.of_forall fun x => norm_nonneg _) (fun n => ?_)
    · filter_upwards [hK n, hK'] with x h1 h2
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    · exact Eventually.of_forall fun x => (β n x - β' x).le_opNorm _
  have h12 := h1.add h2
  rw [add_zero] at h12
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12 (fun n => bot_le)
    fun n => ?_
  have hsplit : (fun x => β n x (u n x)) - (fun x => β' x (u' x)) =
      (fun x => β n x (u n x - u' x)) + fun x => (β n x - β' x) (u' x) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [hsplit]
  exact eLpNorm_add_le (aestronglyMeasurable_apply (hβm n) ((hu.memLp n).1.sub hu.memLp_lim.1))
    (aestronglyMeasurable_apply ((hβm n).sub hβ'm) hu.memLp_lim.1) Fact.out

/-- **Tensor clause of `lem:products`.**  If `u_n → u` and `v_n → v` in `L²` and the bilinear
coefficients `B_n(x)` are uniformly bounded and converge in measure to `B`, then
`B_n(u_n ⊗ v_n) → B(u ⊗ v)` in `L¹`. -/
theorem LpTendsto.coeff_bilin {β : ℕ → X → E →L[ℝ] F →L[ℝ] W} {β' : X → E →L[ℝ] F →L[ℝ] W}
    (hβm : ∀ n, AEStronglyMeasurable (β n) μ) (hβ : TendstoInMeasure μ β atTop β') {K : ℝ}
    (hK : ∀ n, ∀ᵐ x ∂μ, ‖β n x‖ ≤ K) {u : ℕ → X → E} {u' : X → E} {v : ℕ → X → F}
    {v' : X → F} (hu : LpTendsto μ 2 u u') (hv : LpTendsto μ 2 v v') :
    LpTendsto μ 1 (fun n x => β n x (u n x) (v n x)) (fun x => β' x (u' x) (v' x)) := by
  have hC : LpTendsto μ 2 (fun n x => β n x (u n x)) (fun x => β' x (u' x)) :=
    LpTendsto.coeff (by norm_num) hβm hβ hK hu
  have := LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.id ℝ (F →L[ℝ] W)) hC hv
  simpa using this


/-! ### Bounded chart compositions (the `L^p` core of `eq:bounded-chart-composition`) -/

/-- Composition with a function continuous on a compact chart preserves convergence in
measure: if `e_n, e ∈ K` a.e. and `e_n → e` in measure, then `Φ(e_n) → Φ(e)` in measure. -/
theorem tendstoInMeasure_comp_of_continuousOn {Z : Type*} [NormedAddCommGroup Z] {K : Set Z}
    (hK : IsCompact K) {Φ : Z → W} (hΦ : ContinuousOn Φ K) {e : ℕ → X → Z} {e' : X → Z}
    (hin : ∀ n, ∀ᵐ x ∂μ, e n x ∈ K) (hin' : ∀ᵐ x ∂μ, e' x ∈ K)
    (he : TendstoInMeasure μ e atTop e') :
    TendstoInMeasure μ (fun n x => Φ (e n x)) atTop (fun x => Φ (e' x)) := by
  rw [tendstoInMeasure_iff_dist] at he ⊢
  intro ε hε
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hΦ) ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (he δ hδ)
    (fun n => bot_le) fun n => measure_mono_ae ?_
  filter_upwards [hin n, hin'] with x h1 h2 hx
  by_contra hlt
  exact absurd hx (not_le.2 (hunif _ h1 _ h2 (not_le.1 hlt)))

/-- **Chart compositions converge in every finite `L^p`.**  On a finite measure space, if
`e_n, e` take values a.e. in a compact set `K`, `e_n → e` in measure (e.g. strongly in `L²` or
`H¹`) and `Φ` is continuous on `K` (e.g. a smooth algebraic coefficient `F(e, e^{-1})` on a
compact subset of a nondegenerate coframe chart), then `Φ(e_n)` is uniformly bounded and
`Φ(e_n) → Φ(e)` in `L^p` for every `1 ≤ p < ∞`. -/
theorem LpTendsto.comp_of_continuousOn [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {Z : Type*} [NormedAddCommGroup Z] {K : Set Z} (hK : IsCompact K)
    {Φ : Z → W} (hΦ : ContinuousOn Φ K) {e : ℕ → X → Z} {e' : X → Z}
    (hin : ∀ n, ∀ᵐ x ∂μ, e n x ∈ K) (hin' : ∀ᵐ x ∂μ, e' x ∈ K)
    (he : TendstoInMeasure μ e atTop e')
    (hΦm : ∀ n, AEStronglyMeasurable (fun x => Φ (e n x)) μ) :
    (∃ M, ∀ n, ∀ᵐ x ∂μ, ‖Φ (e n x)‖ ≤ M) ∧
      LpTendsto μ p (fun n x => Φ (e n x)) (fun x => Φ (e' x)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn hΦ).isBounded.exists_norm_le
  have hbd : ∀ n, ∀ᵐ x ∂μ, ‖Φ (e n x)‖ ≤ M := fun n => by
    filter_upwards [hin n] with x hx using hM _ ⟨_, hx, rfl⟩
  have hbd' : ∀ᵐ x ∂μ, ‖Φ (e' x)‖ ≤ M := by
    filter_upwards [hin'] with x hx using hM _ ⟨_, hx, rfl⟩
  have hc := tendstoInMeasure_comp_of_continuousOn hK hΦ hin hin' he
  have hm' : AEStronglyMeasurable (fun x => Φ (e' x)) μ := hc.aestronglyMeasurable hΦm
  have hmem : ∀ f : X → W, AEStronglyMeasurable f μ → (∀ᵐ x ∂μ, ‖f x‖ ≤ M) → MemLp f p μ :=
    fun f hf hfM => MemLp.of_bound hf M hfM
  refine ⟨⟨M, hbd⟩, fun n => hmem _ (hΦm n) (hbd n), hmem _ hm' hbd', ?_⟩
  refine tendsto_eLpNorm_of_tendstoInMeasure_dominated hp0 hp hc (K := M + M)
    (fun n => ?_) (fun n => (hΦm n).sub hm') (memLp_const (1 : ℝ))
    (Eventually.of_forall fun _ => zero_le_one) (fun n => ?_)
  · filter_upwards [hbd n, hbd'] with x h1 h2
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  · exact Eventually.of_forall fun x => by simp

/-- **Chain-rule term of `eq:bounded-chart-composition`.**  Under the hypotheses of
`LpTendsto.comp_of_continuousOn`, with `DΦ` continuous on the compact chart `K` and
`∂e_n → ∂e` in `L²`, the chain-rule expressions converge:
`DΦ(e_n) ∂e_n → DΦ(e) ∂e` in `L²`.  (Identifying them with `∂(Φ ∘ e_n)` is the Sobolev chain
rule, not formalised here.) -/
theorem LpTendsto.chainRule_term [IsFiniteMeasure μ] {Z : Type*} [NormedAddCommGroup Z]
    {K : Set Z} (hK : IsCompact K) {DΦ : Z → E →L[ℝ] F} (hDΦ : ContinuousOn DΦ K)
    {e : ℕ → X → Z} {e' : X → Z} (hin : ∀ n, ∀ᵐ x ∂μ, e n x ∈ K) (hin' : ∀ᵐ x ∂μ, e' x ∈ K)
    (he : TendstoInMeasure μ e atTop e')
    (hDm : ∀ n, AEStronglyMeasurable (fun x => DΦ (e n x)) μ) {de : ℕ → X → E} {de' : X → E}
    (hde : LpTendsto μ 2 de de') :
    LpTendsto μ 2 (fun n x => DΦ (e n x) (de n x)) (fun x => DΦ (e' x) (de' x)) := by
  obtain ⟨⟨M, hM⟩, -⟩ := LpTendsto.comp_of_continuousOn (p := 2) (by norm_num) hK hDΦ hin hin'
    he hDm
  exact LpTendsto.coeff (by norm_num) hDm (tendstoInMeasure_comp_of_continuousOn hK hDΦ hin hin'
    he) hM hde

end

end RenewalGeometry.LpProductContinuity

/-! ### Non-vacuity -/

namespace RenewalGeometry.LpProductContinuity

open MeasureTheory Filter Mollifier

/-- Non-vacuity of `LpTendsto.coeff`: a constant coefficient and a constant `L²` sequence. -/
example {X : Type*} [MeasurableSpace X] {μ : Measure X} {u : X → ℝ} (hu : MemLp u 2 μ) :
    LpTendsto μ 2 (fun _ x => (ContinuousLinearMap.id ℝ ℝ) (u x))
      (fun x => (ContinuousLinearMap.id ℝ ℝ) (u x)) := by
  refine LpTendsto.coeff (β := fun _ _ => ContinuousLinearMap.id ℝ ℝ) (K := 1) (by norm_num)
    (fun _ => aestronglyMeasurable_const) ?_ (fun _ => Eventually.of_forall fun _ =>
      ContinuousLinearMap.norm_id_le) (LpTendsto.const hu)
  intro ε hε
  simp [edist_self, not_le.2 hε]

end RenewalGeometry.LpProductContinuity
