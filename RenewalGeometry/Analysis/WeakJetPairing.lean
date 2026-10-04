/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.MollifierLpConvergence
import RenewalGeometry.Continuum.NativeGridLpCalculus
import RenewalGeometry.Analysis.LpProductContinuity

/-!
# Weak–strong pairings of first-variation covectors, uniformly on `C¹`-bounded tests

Generic infrastructure (no renewal notions) for the passage to the limit in first variations of
lattice actions whose fields converge only **weakly** in their first differences (the spinor
sector of `prop:native-spinor-variation` of the Einstein–SM action-closure manuscript: "derivative
terms use weak–strong `L²` pairing, while link and Yukawa terms pair strongly convergent `L²`
coefficients with weakly convergent `L²` bilinears … uniform `C¹` bounds and a finite `C¹` net
inside the `C^r` unit ball complete the proof").

Setting: the unit torus `𝕋⁴ = UnitAddTorus (Fin 4)` with its Haar probability measure.

* `lpTendsto_bilin_two_one` (**strong `L²` × (strong `L¹` + bounded `L²`) → strong `L¹`**): if
  `u_k → u` in `L²`, `v_k → v` in `L¹` and `sup_k ‖v_k‖_{L²} < ∞`, then `B(u_k, v_k) → B(u, v)` in
  `L¹` for every bounded bilinear `B` (bounded-continuous approximation of the fixed factor).
  This is how strongly convergent link coefficients pass against spinor bilinears that converge
  strongly in `L¹` and stay bounded in `L²`.
* `tendsto_integral_bilin_weak` (**weak–strong pairing**): if `c_k → c` strongly in `L²`, `u_k`
  is bounded in `L²` and `∫ B(g, u_k) → ∫ B(g, u)` for every `g ∈ L²`, then
  `∫ B(c_k, u_k) → ∫ B(c, u)`.
* `totallyBounded_lipschitz` (Arzelà–Ascoli): bounded, uniformly Lipschitz maps `𝕋⁴ → T` (`T`
  finite dimensional) form a totally bounded set of bounded continuous functions.
* `eventually_forall_le_of_totallyBounded`: pointwise convergence to `0` of uniformly Lipschitz
  functionals is uniform on totally bounded sets (the finite-net argument).
* `weak_jet_variation` (**the main theorem**): first variations of the form
  `∫ G_k[J_k] + ∫ Λ_k[J_k](u_k)` with `G_k → G` strongly in `L¹`, `Λ_k → Λ` strongly in `L²`
  (operator-valued), `u_k ⇀ u` weakly and boundedly in `L²`, and test jets `J_k` that converge
  uniformly to continuous jets `J` with Lipschitz bounds, converge to `∫ G[J] + ∫ Λ[J](u)`
  **uniformly on the test family**: for every `ε > 0`, eventually
  `|… - …| ≤ ε ‖τ‖` for all tests `τ` simultaneously.
* `tendsto_integral_of_weak_coord`: weak convergence of each real coordinate of an
  `EuclideanSpace`-valued sequence gives the weak convergence hypothesis for every bilinear
  pairing.
-/

open MeasureTheory Set Finset Filter Topology Metric
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

namespace RenewalGeometry.WeakJetPairing

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_wj : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder221_wj : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### Hölder bounds for real integrals -/

section Holder

theorem memLp_bilin_two_two (B : E →L[ℝ] F →L[ℝ] W) {f : 𝕋 → E} {g : 𝕋 → F}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    MemLp (fun y => B (f y) (g y)) 1 volume :=
  (LpTendsto.bilin (p := 2) (q := 2) (r := 1) B (LpTendsto.const hf)
    (LpTendsto.const hg)).memLp_lim

theorem integrable_bilin_two_two (B : E →L[ℝ] F →L[ℝ] W) {f : 𝕋 → E} {g : 𝕋 → F}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => B (f y) (g y)) volume :=
  memLp_one_iff_integrable.1 (memLp_bilin_two_two B hf hg)

/-- `|∫ f| ≤ ‖f‖_{L¹}` as real numbers. -/
theorem abs_integral_le_toReal {f : 𝕋 → ℝ} (hf : Integrable f volume) :
    |∫ y, f y| ≤ (eLpNorm f 1 volume).toReal := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm f).trans (le_of_eq ?_)
  rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hf.1]

theorem eLpNorm_bilin_two_two_le (B : E →L[ℝ] F →L[ℝ] W) {f : 𝕋 → E} {g : 𝕋 → F}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun y => B (f y) (g y)) 1 volume ≤
      ‖B‖₊ * eLpNorm f 2 volume * eLpNorm g 2 volume :=
  NativeGridLp.eLpNorm_bilin_le' (p := 2) (q := 2) B hf hg

/-- Hölder for a real bilinear pairing: `|∫ B(f, g)| ≤ ‖B‖ ‖f‖₂ ‖g‖₂`. -/
theorem abs_integral_bilin_le (B : E →L[ℝ] F →L[ℝ] ℝ) {f : 𝕋 → E} {g : 𝕋 → F}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ y, B (f y) (g y)| ≤
      ‖B‖ * (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  refine (abs_integral_le_toReal (integrable_bilin_two_two B hf hg)).trans ?_
  have h := eLpNorm_bilin_two_two_le B hf.1 hg.1
  have hne : (‖B‖₊ : ℝ≥0∞) * eLpNorm f 2 volume * eLpNorm g 2 volume ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hf.2.ne) hg.2.ne
  refine (ENNReal.toReal_mono hne h).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  rfl

/-- `|∫ L(y)(f y)| ≤ ‖L‖_{L¹} sup ‖f‖` for a pointwise bounded `f`. -/
theorem abs_integral_clm_le {L : 𝕋 → F →L[ℝ] ℝ} (hL : MemLp L 1 volume) {f : 𝕋 → F}
    (hf : AEStronglyMeasurable f volume) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) :
    |∫ y, L y (f y)| ≤ (eLpNorm L 1 volume).toReal * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0 : 𝕋))
  have hint : Integrable (fun y => L y (f y)) volume := by
    refine Integrable.mono' ((memLp_one_iff_integrable.1 hL).norm.mul_const M)
      (LpProductContinuity.aestronglyMeasurable_apply hL.1 hf) (Eventually.of_forall fun y => ?_)
    exact ((L y).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _))
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ y, ‖L y (f y)‖ ≤ ∫ y, ‖L y‖ * M := integral_mono hint.norm
        ((memLp_one_iff_integrable.1 hL).norm.mul_const M) fun y =>
          ((L y).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _))
    _ = (∫ y, ‖L y‖) * M := integral_mul_const _ _
    _ = (eLpNorm L 1 volume).toReal * M := by
        rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hL.1]

end Holder

/-! ### Strong `L²` × (strong `L¹` + bounded `L²`) -/

section BilinTwoOne

/-- **Strong `L²` × (strong `L¹` + bounded `L²`) → strong `L¹`.**  If `u_k → u` in `L²`,
`v_k → v` in `L¹` with `‖v_k‖_{L²} ≤ C`, then `B(u_k, v_k) → B(u, v)` in `L¹`. -/
theorem lpTendsto_bilin_two_one (B : E →L[ℝ] F →L[ℝ] W) {u : ℕ → 𝕋 → E} {u₀ : 𝕋 → E}
    (hu : LpTendsto volume 2 u u₀) {v : ℕ → 𝕋 → F} {v₀ : 𝕋 → F} (hv : LpTendsto volume 1 v v₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hv2 : ∀ k, eLpNorm (v k) 2 volume ≤ C) :
    LpTendsto volume 1 (fun k y => B (u k y) (v k y)) (fun y => B (u₀ y) (v₀ y)) := by
  have hvk : ∀ k, MemLp (v k) 2 volume := fun k => ⟨(hv.memLp k).1, (hv2 k).trans_lt hC.lt_top⟩
  have hv₀ : MemLp v₀ 2 volume := hv.memLp_of_bound one_ne_zero hC hv2
  have hv₀C : eLpNorm v₀ 2 volume ≤ C := hv.eLpNorm_le_of_bound one_ne_zero hv2
  refine ⟨fun k => memLp_bilin_two_two B (hu.memLp k) (hvk k),
    memLp_bilin_two_two B hu.memLp_lim hv₀, ?_⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  set D : ℝ≥0∞ := (‖B‖₊ : ℝ≥0∞) * (C + C) + 1
  have hD : D ≠ ∞ := by
    simp only [D]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.add_ne_top.2 ⟨hC, hC⟩), ENNReal.one_ne_top⟩
  have hD0 : D ≠ 0 := by simp [D]
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨G', hG', -⟩ := hu.memLp_lim.exists_boundedContinuous_eLpNorm_sub_le (by norm_num)
    (ε := ε / 3 / D) (ENNReal.div_pos hε3.ne' hD).ne'
  set M : ℝ := ‖G'‖
  -- the three small terms
  have t1 : Tendsto (fun k => (‖B‖₊ : ℝ≥0∞) * eLpNorm (u k - u₀) 2 volume * C) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul (a := (‖B‖₊ : ℝ≥0∞))
      hu.tendsto (Or.inr ENNReal.coe_ne_top)) (Or.inr hC)
    simpa using this
  have t2 : Tendsto (fun k => (‖B‖₊ : ℝ≥0∞) * ENNReal.ofReal M * eLpNorm (v k - v₀) 1 volume)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hv.tendsto (Or.inr (ENNReal.mul_ne_top
      ENNReal.coe_ne_top ENNReal.ofReal_ne_top))
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 t1) (ε / 3) hε3,
    (ENNReal.tendsto_nhds_zero.1 t2) (ε / 3) hε3] with k hk1 hk2
  have hsplit : (fun y => B (u k y) (v k y)) - (fun y => B (u₀ y) (v₀ y)) =
      ((fun y => B (u k y - u₀ y) (v k y)) + fun y => B (u₀ y - G' y) (v k y - v₀ y)) +
        fun y => B (G' y) (v k y - v₀ y) := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [hsplit]
  have hm1 : AEStronglyMeasurable (fun y => B (u k y - u₀ y) (v k y)) volume :=
    B.continuous₂.comp_aestronglyMeasurable₂ ((hu.memLp k).1.sub hu.memLp_lim.1) (hvk k).1
  have hm2 : AEStronglyMeasurable (fun y => B (u₀ y - G' y) (v k y - v₀ y)) volume :=
    B.continuous₂.comp_aestronglyMeasurable₂
      (hu.memLp_lim.1.sub G'.continuous.aestronglyMeasurable) ((hvk k).1.sub hv₀.1)
  have hm3 : AEStronglyMeasurable (fun y => B (G' y) (v k y - v₀ y)) volume :=
    B.continuous₂.comp_aestronglyMeasurable₂ G'.continuous.aestronglyMeasurable
      ((hvk k).1.sub hv₀.1)
  refine (eLpNorm_add_le (hm1.add hm2) hm3 le_rfl).trans ?_
  refine (add_le_add (eLpNorm_add_le hm1 hm2 le_rfl) le_rfl).trans ?_
  have h1 : eLpNorm (fun y => B (u k y - u₀ y) (v k y)) 1 volume ≤ ε / 3 := by
    refine (eLpNorm_bilin_two_two_le B ((hu.memLp k).1.sub hu.memLp_lim.1) (hvk k).1).trans ?_
    refine le_trans ?_ hk1
    exact mul_le_mul_of_nonneg_left (hv2 k) (by positivity)
  have h2 : eLpNorm (fun y => B (u₀ y - G' y) (v k y - v₀ y)) 1 volume ≤ ε / 3 := by
    refine (eLpNorm_bilin_two_two_le B (hu.memLp_lim.1.sub G'.continuous.aestronglyMeasurable)
      ((hvk k).1.sub hv₀.1)).trans ?_
    have hvk' : eLpNorm (fun y => v k y - v₀ y) 2 volume ≤ C + C :=
      (eLpNorm_sub_le (hvk k).1 hv₀.1 (by norm_num)).trans (add_le_add (hv2 k) hv₀C)
    calc (‖B‖₊ : ℝ≥0∞) * eLpNorm (fun y => u₀ y - G' y) 2 volume *
          eLpNorm (fun y => v k y - v₀ y) 2 volume
        ≤ (‖B‖₊ : ℝ≥0∞) * (ε / 3 / D) * (C + C) := by gcongr; exact hG'
      _ = ε / 3 / D * ((‖B‖₊ : ℝ≥0∞) * (C + C)) := by ring
      _ ≤ ε / 3 / D * D := by gcongr; exact le_self_add
      _ = ε / 3 := ENNReal.div_mul_cancel hD0 hD
  have h3 : eLpNorm (fun y => B (G' y) (v k y - v₀ y)) 1 volume ≤ ε / 3 := by
    refine le_trans ?_ hk2
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := ‖B‖ * M) (g := v k - v₀)
      (Eventually.of_forall fun y => ?_) 1).trans (le_of_eq ?_)
    · calc ‖B (G' y) (v k y - v₀ y)‖ ≤ ‖B‖ * ‖G' y‖ * ‖v k y - v₀ y‖ := B.le_opNorm₂ _ _
        _ ≤ ‖B‖ * M * ‖(v k - v₀) y‖ := by
            gcongr
            · exact G'.norm_coe_le_norm y
            · exact le_rfl
    · rw [ENNReal.ofReal_mul (norm_nonneg B), ofReal_norm]
      rfl
  calc _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add h1 h2) h3
    _ = ε := ENNReal.add_thirds ε

end BilinTwoOne

/-! ### The weak–strong pairing -/

section WeakStrong

/-- **Weak–strong pairing.**  If `c_k → c` strongly in `L²`, `‖u_k‖_{L²} ≤ C` and
`∫ B(g, u_k) → ∫ B(g, u)` for every `g ∈ L²`, then `∫ B(c_k, u_k) → ∫ B(c, u)`. -/
theorem tendsto_integral_bilin_weak (B : E →L[ℝ] F →L[ℝ] ℝ) {c : ℕ → 𝕋 → E} {c₀ : 𝕋 → E}
    (hc : LpTendsto volume 2 c c₀) {u : ℕ → 𝕋 → F} {u₀ : 𝕋 → F}
    (hu : ∀ k, MemLp (u k) 2 volume) {C : ℝ} (hub : ∀ k, (eLpNorm (u k) 2 volume).toReal ≤ C)
    (hw : ∀ g : 𝕋 → E, MemLp g 2 volume →
      Tendsto (fun k => ∫ y, B (g y) (u k y)) atTop (𝓝 (∫ y, B (g y) (u₀ y)))) :
    Tendsto (fun k => ∫ y, B (c k y) (u k y)) atTop (𝓝 (∫ y, B (c₀ y) (u₀ y))) := by
  have hsplit : ∀ k, ∫ y, B (c k y) (u k y) =
      (∫ y, B (c k y - c₀ y) (u k y)) + ∫ y, B (c₀ y) (u k y) := by
    intro k
    have i1 : Integrable (fun y => B (c k y - c₀ y) (u k y)) volume :=
      integrable_bilin_two_two B ((hc.memLp k).sub hc.memLp_lim) (hu k)
    have i2 : Integrable (fun y => B (c₀ y) (u k y)) volume :=
      integrable_bilin_two_two B hc.memLp_lim (hu k)
    calc ∫ y, B (c k y) (u k y) = ∫ y, (B (c k y - c₀ y) (u k y) + B (c₀ y) (u k y)) := by
          congr 1; funext y; simp only [map_sub, ContinuousLinearMap.sub_apply]; abel
      _ = _ := integral_add i1 i2
  simp_rw [hsplit]
  rw [← zero_add (∫ y, B (c₀ y) (u₀ y))]
  refine Tendsto.add ?_ (hw c₀ hc.memLp_lim)
  -- the first term is small
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg.trans (hub 0)
  have hbd : ∀ k, |∫ y, B (c k y - c₀ y) (u k y)| ≤
      ‖B‖ * (eLpNorm (c k - c₀) 2 volume).toReal * C := by
    intro k
    refine (abs_integral_bilin_le B ((hc.memLp k).sub hc.memLp_lim) (hu k)).trans ?_
    have := hub k
    have h0 : 0 ≤ ‖B‖ * (eLpNorm (c k - c₀) 2 volume).toReal := by positivity
    calc _ = ‖B‖ * (eLpNorm (c k - c₀) 2 volume).toReal * (eLpNorm (u k) 2 volume).toReal := rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left this h0
  have ht : Tendsto (fun k => ‖B‖ * (eLpNorm (c k - c₀) 2 volume).toReal * C) atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc.tendsto).const_mul ‖B‖
    simpa using this.mul_const C
  exact squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact hbd k) ht

end WeakStrong

/-! ### Uniformity on totally bounded test sets -/

section Uniform

/-- **Arzelà–Ascoli**: bounded, uniformly Lipschitz maps `𝕋⁴ → T` (finite-dimensional `T`) form a
totally bounded set of bounded continuous functions. -/
theorem totallyBounded_lipschitz {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    [FiniteDimensional ℝ T] (M L : ℝ) :
    TotallyBounded {φ : 𝕋 →ᵇ T | (∀ y, ‖φ y‖ ≤ M) ∧ ∀ y y', ‖φ y - φ y'‖ ≤ L * dist y y'} := by
  set A := {φ : 𝕋 →ᵇ T | (∀ y, ‖φ y‖ ≤ M) ∧ ∀ y y', ‖φ y - φ y'‖ ≤ L * dist y y'}
  have hc : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall (0 : T) M)
      (isCompact_closedBall 0 M) A (fun f y hf => ?_) ?_
    · simpa [mem_closedBall, dist_zero_right] using hf.1 y
    · have hu : UniformEquicontinuous ((↑) : A → 𝕋 → T) := by
        refine LipschitzWith.uniformEquicontinuous _ (Real.toNNReal L) fun φ => ?_
        refine LipschitzWith.of_dist_le_mul fun y y' => ?_
        rw [dist_eq_norm]
        exact (φ.2.2 y y').trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L)
          dist_nonneg)
      exact hu.equicontinuous
  exact hc.totallyBounded.subset subset_closure

/-- **Finite-net argument**: functionals that are uniformly Lipschitz and converge pointwise to
`0` converge uniformly on every totally bounded set. -/
theorem eventually_forall_le_of_totallyBounded {Y : Type*} [PseudoMetricSpace Y]
    (ℓ : ℕ → Y → ℝ) {L : ℝ} (hlip : ∀ k φ ψ, |ℓ k φ - ℓ k ψ| ≤ L * dist φ ψ)
    (hpt : ∀ φ, Tendsto (fun k => ℓ k φ) atTop (𝓝 0)) {S : Set Y} (hS : TotallyBounded S) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ φ ∈ S, |ℓ k φ| ≤ ε := by
  intro ε hε
  set L' := |L| + 1
  have hL' : 0 < L' := by positivity
  obtain ⟨t, ht, hSt⟩ := Metric.totallyBounded_iff.1 hS (ε / (2 * L')) (by positivity)
  have hev : ∀ᶠ k in atTop, ∀ z ∈ t, |ℓ k z| ≤ ε / 2 := by
    refine (ht.eventually_all).2 fun z _ => ?_
    have := (hpt z).abs
    rw [abs_zero] at this
    exact (tendsto_order.1 this).2 (ε / 2) (by positivity) |>.mono fun k hk => hk.le
  filter_upwards [hev] with k hk
  intro φ hφ
  obtain ⟨z, hz, hφz⟩ := mem_iUnion₂.1 (hSt hφ)
  rw [mem_ball] at hφz
  have h1 := hlip k φ z
  have h2 : L * dist φ z ≤ L' * dist φ z :=
    mul_le_mul_of_nonneg_right ((le_abs_self L).trans (by simp [L'])) dist_nonneg
  have h3 : L' * dist φ z ≤ ε / 2 := by
    have := mul_lt_mul_of_pos_left hφz hL'
    rw [mul_div_assoc', mul_comm 2 L', ← div_div, mul_div_cancel_left₀ _ hL'.ne'] at this
    exact this.le
  have h4 := hk z hz
  calc |ℓ k φ| ≤ |ℓ k φ - ℓ k z| + |ℓ k z| := by
        have := abs_sub_abs_le_abs_sub (ℓ k φ) (ℓ k z)
        linarith
    _ ≤ ε := by linarith

end Uniform

/-! ### The weak jet-variation theorem -/

section Main

variable {T U : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Pointwise application of an `L^p` operator field to a bounded field stays in `L^p`. -/
theorem memLp_apply_of_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : ℝ≥0∞}
    {L : 𝕋 → T →L[ℝ] V} (hL : MemLp L p volume) {f : 𝕋 → T}
    (hf : AEStronglyMeasurable f volume) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) :
    MemLp (fun y => L y (f y)) p volume :=
  hL.of_le_mul (c := M) (LpProductContinuity.aestronglyMeasurable_apply hL.1 hf)
    (Eventually.of_forall fun y => ((L y).le_opNorm _).trans (by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)))

theorem eLpNorm_apply_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : ℝ≥0∞}
    (L : 𝕋 → T →L[ℝ] V) (f : 𝕋 → T) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) :
    eLpNorm (fun y => L y (f y)) p volume ≤ ENNReal.ofReal M * eLpNorm L p volume :=
  eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun y =>
    ((L y).le_opNorm _).trans (by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _))) p

theorem toReal_eLpNorm_apply_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p : ℝ≥0∞} {L : 𝕋 → T →L[ℝ] V} (hL : MemLp L p volume) (f : 𝕋 → T) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, ‖f y‖ ≤ M) :
    (eLpNorm (fun y => L y (f y)) p volume).toReal ≤ M * (eLpNorm L p volume).toReal := by
  have hne : ENNReal.ofReal M * eLpNorm L p volume ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.2.ne
  refine (ENNReal.toReal_mono hne (eLpNorm_apply_le L f hM)).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0]

/-- **Weak jet-variation limit, uniformly on the test family.**  Let `G_k → G` strongly in `L¹`
(`T →L ℝ`-valued), `Λ_k → Λ` strongly in `L²` (`T →L U →L ℝ`-valued), `u_k` bounded in `L²` with
`∫ g(u_k) → ∫ g(u)` for every `g ∈ L²(𝕋⁴; U →L ℝ)`.  Let the tests `τ ∈ Θ` have continuous jets
`J τ` and sampled jets `J_k τ` with `‖J τ‖ ≤ ‖τ‖`, `J τ` `‖τ‖`-Lipschitz and
`‖J_k τ - J τ‖ ≤ δ_k ‖τ‖`, `δ_k → 0`.  Then for every `ε > 0`, eventually for all tests
`|∫ (G_k[J_k τ] + Λ_k[J_k τ](u_k)) - ∫ (G[J τ] + Λ[J τ](u))| ≤ ε ‖τ‖`. -/
theorem weak_jet_variation {G : ℕ → 𝕋 → T →L[ℝ] ℝ} {G₀ : 𝕋 → T →L[ℝ] ℝ}
    (hG : LpTendsto volume 1 G G₀) {Λ : ℕ → 𝕋 → T →L[ℝ] U →L[ℝ] ℝ}
    {Λ₀ : 𝕋 → T →L[ℝ] U →L[ℝ] ℝ} (hΛ : LpTendsto volume 2 Λ Λ₀)
    {u : ℕ → 𝕋 → U} {u₀ : 𝕋 → U} (hu : ∀ k, MemLp (u k) 2 volume) (hu₀ : MemLp u₀ 2 volume)
    {C : ℝ} (hub : ∀ k, (eLpNorm (u k) 2 volume).toReal ≤ C)
    (hw : ∀ g : 𝕋 → U →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ y, g y (u k y)) atTop (𝓝 (∫ y, g y (u₀ y))))
    {Θ : Type*} (nrm : Θ → ℝ) (J : Θ → 𝕋 → T) (hJc : ∀ τ, Continuous (J τ))
    (hJb : ∀ τ y, ‖J τ y‖ ≤ nrm τ) (hJl : ∀ τ y y', ‖J τ y - J τ y'‖ ≤ nrm τ * dist y y')
    (Jk : ℕ → Θ → 𝕋 → T) (hJkm : ∀ k τ, AEStronglyMeasurable (Jk k τ) volume)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hδ0 : ∀ k, 0 ≤ δ k)
    (hJk : ∀ k τ y, ‖Jk k τ y - J τ y‖ ≤ δ k * nrm τ) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ,
      |(∫ y, (G k y (Jk k τ y) + Λ k y (Jk k τ y) (u k y))) -
        ∫ y, (G₀ y (J τ y) + Λ₀ y (J τ y) (u₀ y))| ≤ ε * nrm τ := by
  intro ε hε
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg.trans (hub 0)
  have hnrm : ∀ τ, 0 ≤ nrm τ := fun τ => (norm_nonneg _).trans (hJb τ 0)
  set g1 : ℝ := (eLpNorm G₀ 1 volume).toReal
  set l2 : ℝ := (eLpNorm Λ₀ 2 volume).toReal
  set c₀ : ℝ := (eLpNorm u₀ 2 volume).toReal
  have hl20 : 0 ≤ l2 := ENNReal.toReal_nonneg
  have hc00 : 0 ≤ c₀ := ENNReal.toReal_nonneg
  set Id : (U →L[ℝ] ℝ) →L[ℝ] U →L[ℝ] ℝ := ContinuousLinearMap.id ℝ (U →L[ℝ] ℝ)
  have hId : ‖Id‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  -- integrability tools
  have mΛ : ∀ (L : 𝕋 → T →L[ℝ] U →L[ℝ] ℝ), MemLp L 2 volume → ∀ (f : 𝕋 → T),
      AEStronglyMeasurable f volume → ∀ M, (∀ y, ‖f y‖ ≤ M) →
      MemLp (fun y => L y (f y)) 2 volume := fun L hL f hf M hM =>
    memLp_apply_of_bound hL hf hM
  have iΛ : ∀ (L : 𝕋 → T →L[ℝ] U →L[ℝ] ℝ), MemLp L 2 volume → ∀ (f : 𝕋 → T),
      AEStronglyMeasurable f volume → ∀ M, (∀ y, ‖f y‖ ≤ M) → ∀ w : 𝕋 → U, MemLp w 2 volume →
      Integrable (fun y => L y (f y) (w y)) volume := fun L hL f hf M hM w hw' =>
    integrable_bilin_two_two Id (mΛ L hL f hf M hM) hw'
  have bΛ' : ∀ (L : 𝕋 → T →L[ℝ] U →L[ℝ] ℝ), MemLp L 2 volume → ∀ (f : 𝕋 → T),
      AEStronglyMeasurable f volume → ∀ M, 0 ≤ M → (∀ y, ‖f y‖ ≤ M) → ∀ w : 𝕋 → U,
      MemLp w 2 volume →
      |∫ y, L y (f y) (w y)| ≤ M * (eLpNorm L 2 volume).toReal * (eLpNorm w 2 volume).toReal := by
    intro L hL f hf M hM0 hM w hw'
    refine (abs_integral_bilin_le Id (mΛ L hL f hf M hM) hw').trans ?_
    have h1 := toReal_eLpNorm_apply_le hL f hM0 hM
    calc ‖Id‖ * (eLpNorm (fun y => L y (f y)) 2 volume).toReal * (eLpNorm w 2 volume).toReal
        ≤ 1 * (M * (eLpNorm L 2 volume).toReal) * (eLpNorm w 2 volume).toReal := by
          gcongr
      _ = _ := by ring
  -- the weak functional on normalized jets
  set S := {φ : 𝕋 →ᵇ T | (∀ y, ‖φ y‖ ≤ 1) ∧ ∀ y y', ‖φ y - φ y'‖ ≤ 1 * dist y y'}
  have hS : TotallyBounded S := totallyBounded_lipschitz 1 1
  set ℓ : ℕ → (𝕋 →ᵇ T) → ℝ := fun k φ =>
    (∫ y, Λ₀ y (φ y) (u k y)) - ∫ y, Λ₀ y (φ y) (u₀ y)
  have hφb : ∀ φ : 𝕋 →ᵇ T, ∀ y, ‖φ y‖ ≤ ‖φ‖ := fun φ y => φ.norm_coe_le_norm y
  have hℓpt : ∀ φ, Tendsto (fun k => ℓ k φ) atTop (𝓝 0) := by
    intro φ
    have := hw (fun y => Λ₀ y (φ y))
      (mΛ _ hΛ.memLp_lim _ φ.continuous.aestronglyMeasurable _ (hφb φ))
    simpa [ℓ, sub_self] using this.sub_const (∫ y, Λ₀ y (φ y) (u₀ y))
  have hℓlip : ∀ k φ ψ, |ℓ k φ - ℓ k ψ| ≤ (l2 * (C + c₀)) * dist φ ψ := by
    intro k φ ψ
    have hφm := φ.continuous.aestronglyMeasurable (μ := (volume : Measure 𝕋))
    have hψm := ψ.continuous.aestronglyMeasurable (μ := (volume : Measure 𝕋))
    have j1 := iΛ _ hΛ.memLp_lim _ hφm _ (hφb φ) _ (hu k)
    have j2 := iΛ _ hΛ.memLp_lim _ hφm _ (hφb φ) _ hu₀
    have j3 := iΛ _ hΛ.memLp_lim _ hψm _ (hφb ψ) _ (hu k)
    have j4 := iΛ _ hΛ.memLp_lim _ hψm _ (hφb ψ) _ hu₀
    have hdφψ : ∀ y, ‖φ y - ψ y‖ ≤ dist φ ψ := fun y => by
      rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist y
    have e : ℓ k φ - ℓ k ψ = ∫ y, Λ₀ y (φ y - ψ y) (u k y - u₀ y) := by
      calc ℓ k φ - ℓ k ψ = (∫ y, (Λ₀ y (φ y) (u k y) - Λ₀ y (φ y) (u₀ y))) -
            ∫ y, (Λ₀ y (ψ y) (u k y) - Λ₀ y (ψ y) (u₀ y)) := by
            simp only [ℓ]; rw [integral_sub j1 j2, integral_sub j3 j4]
        _ = ∫ y, (Λ₀ y (φ y) (u k y) - Λ₀ y (φ y) (u₀ y) -
            (Λ₀ y (ψ y) (u k y) - Λ₀ y (ψ y) (u₀ y))) :=
            (integral_sub (j1.sub j2) (j3.sub j4)).symm
        _ = _ := by
            congr 1; funext y
            simp only [map_sub, ContinuousLinearMap.sub_apply]; abel
    rw [e]
    refine (bΛ' _ hΛ.memLp_lim _ (hφm.sub hψm) _ dist_nonneg hdφψ _ ((hu k).sub hu₀)).trans ?_
    have h2 : (eLpNorm (u k - u₀) 2 volume).toReal ≤ C + c₀ := by
      have hle := eLpNorm_sub_le (hu k).1 hu₀.1 (p := 2) (by norm_num)
      have hne : eLpNorm (u k) 2 volume + eLpNorm u₀ 2 volume ≠ ∞ :=
        ENNReal.add_ne_top.2 ⟨(hu k).2.ne, hu₀.2.ne⟩
      refine (ENNReal.toReal_mono hne hle).trans ?_
      rw [ENNReal.toReal_add (hu k).2.ne hu₀.2.ne]
      exact add_le_add (hub k) le_rfl
    calc dist φ ψ * l2 * (eLpNorm (fun y => u k y - u₀ y) 2 volume).toReal
        ≤ dist φ ψ * l2 * (C + c₀) := by
          gcongr
          exact h2
      _ = l2 * (C + c₀) * dist φ ψ := by ring
  have hunif := eventually_forall_le_of_totallyBounded ℓ hℓlip hℓpt hS (ε / 4) (by positivity)
  -- the strong terms
  have hG1 : Tendsto (fun k => (eLpNorm (G k - G₀) 1 volume).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG.tendsto
    rw [ENNReal.toReal_zero] at h
    exact h
  have hΛ2 : Tendsto (fun k => (eLpNorm (Λ k - Λ₀) 2 volume).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hΛ.tendsto
    rw [ENNReal.toReal_zero] at h
    exact h
  have hsmall : Tendsto (fun k => (eLpNorm (G k - G₀) 1 volume).toReal * (1 + δ k) +
      g1 * δ k + (1 + δ k) * (eLpNorm (Λ k - Λ₀) 2 volume).toReal * C + δ k * l2 * C)
      atTop (𝓝 0) := by
    have h1 := hG1.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hδ)
    have h2 := hδ.const_mul g1
    have h3 := (((tendsto_const_nhds (x := (1 : ℝ))).add hδ).mul hΛ2).mul_const C
    have h4 := (hδ.mul_const l2).mul_const C
    simpa using ((h1.add h2).add h3).add h4
  filter_upwards [hunif, (tendsto_order.1 hsmall).2 (ε / 2) (by positivity)] with k hk hks
  intro τ
  rcases (hnrm τ).eq_or_lt with h0 | hpos
  · -- zero test norm: everything vanishes
    have hJ0 : ∀ y, J τ y = 0 := fun y => norm_le_zero_iff.1 (by rw [h0]; exact hJb τ y)
    have hJk0 : ∀ y, Jk k τ y = 0 := fun y => by
      have := hJk k τ y
      rw [← h0, mul_zero, hJ0, sub_zero] at this
      exact norm_le_zero_iff.1 this
    simp [hJ0, hJk0, ← h0]
  -- normalised jet
  set φ : 𝕋 →ᵇ T := BoundedContinuousFunction.mkOfCompact
    ⟨fun y => (nrm τ)⁻¹ • J τ y, (hJc τ).const_smul _⟩
  have hφv : ∀ y, φ y = (nrm τ)⁻¹ • J τ y := fun y => rfl
  have hφ : φ ∈ S := by
    refine ⟨fun y => ?_, fun y y' => ?_⟩
    · rw [hφv, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos, mul_one]
      exact hJb τ y
    · rw [hφv, hφv, ← smul_sub, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, one_mul,
        inv_mul_le_iff₀ hpos]
      exact hJl τ y y'
  have hφJ : ∀ y, J τ y = nrm τ • φ y := fun y => by
    rw [hφv, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have hℓk := hk φ hφ
  -- bounds on the jets
  have hJkb : ∀ y, ‖Jk k τ y‖ ≤ (1 + δ k) * nrm τ := fun y => by
    have := norm_le_insert' (Jk k τ y) (J τ y)
    nlinarith [hJk k τ y, hJb τ y]
  have hJm : AEStronglyMeasurable (J τ) volume := (hJc τ).aestronglyMeasurable
  have iG : ∀ (L : 𝕋 → T →L[ℝ] ℝ), MemLp L 1 volume → ∀ (f : 𝕋 → T),
      AEStronglyMeasurable f volume → ∀ M, (∀ y, ‖f y‖ ≤ M) →
      Integrable (fun y => L y (f y)) volume := fun L hL f hf M hM =>
    memLp_one_iff_integrable.1 (memLp_apply_of_bound hL hf hM)
  -- decomposition of the difference
  have i1 : Integrable (fun y => (G k y - G₀ y) (Jk k τ y)) volume :=
    iG _ ((hG.memLp k).sub hG.memLp_lim) _ (hJkm k τ) _ hJkb
  have i2 : Integrable (fun y => G₀ y (Jk k τ y - J τ y)) volume :=
    iG _ hG.memLp_lim _ ((hJkm k τ).sub hJm) _ (hJk k τ)
  have i3 : Integrable (fun y => (Λ k y - Λ₀ y) (Jk k τ y) (u k y)) volume :=
    iΛ _ ((hΛ.memLp k).sub hΛ.memLp_lim) _ (hJkm k τ) _ hJkb _ (hu k)
  have i4 : Integrable (fun y => Λ₀ y (Jk k τ y - J τ y) (u k y)) volume :=
    iΛ _ hΛ.memLp_lim _ ((hJkm k τ).sub hJm) _ (hJk k τ) _ (hu k)
  have i5 := iΛ _ hΛ.memLp_lim _ hJm _ (hJb τ) _ (hu k)
  have i6 := iΛ _ hΛ.memLp_lim _ hJm _ (hJb τ) _ hu₀
  have iGk := iG _ (hG.memLp k) _ (hJkm k τ) _ hJkb
  have iG0 := iG _ hG.memLp_lim _ hJm _ (hJb τ)
  have iΛk := iΛ _ (hΛ.memLp k) _ (hJkm k τ) _ hJkb _ (hu k)
  have hl : nrm τ * ℓ k φ = (∫ y, Λ₀ y (J τ y) (u k y)) - ∫ y, Λ₀ y (J τ y) (u₀ y) := by
    simp only [ℓ, hφJ, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, mul_sub]
  have a1 : ∫ y, G k y (Jk k τ y) = (∫ y, (G k y - G₀ y) (Jk k τ y)) +
      (∫ y, G₀ y (Jk k τ y - J τ y)) + ∫ y, G₀ y (J τ y) := by
    calc ∫ y, G k y (Jk k τ y) = ∫ y, ((G k y - G₀ y) (Jk k τ y) + G₀ y (Jk k τ y - J τ y) +
          G₀ y (J τ y)) := by
          congr 1; funext y; simp only [ContinuousLinearMap.sub_apply, map_sub]; abel
      _ = (∫ y, ((G k y - G₀ y) (Jk k τ y) + G₀ y (Jk k τ y - J τ y))) +
          ∫ y, G₀ y (J τ y) := integral_add (i1.add i2) iG0
      _ = _ := by rw [integral_add i1 i2]
  have a2 : ∫ y, Λ k y (Jk k τ y) (u k y) = (∫ y, (Λ k y - Λ₀ y) (Jk k τ y) (u k y)) +
      (∫ y, Λ₀ y (Jk k τ y - J τ y) (u k y)) + ∫ y, Λ₀ y (J τ y) (u k y) := by
    calc ∫ y, Λ k y (Jk k τ y) (u k y) = ∫ y, ((Λ k y - Λ₀ y) (Jk k τ y) (u k y) +
          Λ₀ y (Jk k τ y - J τ y) (u k y) + Λ₀ y (J τ y) (u k y)) := by
          congr 1; funext y
          simp only [ContinuousLinearMap.sub_apply, map_sub]; abel
      _ = (∫ y, ((Λ k y - Λ₀ y) (Jk k τ y) (u k y) + Λ₀ y (Jk k τ y - J τ y) (u k y))) +
          ∫ y, Λ₀ y (J τ y) (u k y) := integral_add (i3.add i4) i5
      _ = _ := by rw [integral_add i3 i4]
  have e : (∫ y, (G k y (Jk k τ y) + Λ k y (Jk k τ y) (u k y))) -
      ∫ y, (G₀ y (J τ y) + Λ₀ y (J τ y) (u₀ y)) =
      (∫ y, (G k y - G₀ y) (Jk k τ y)) + (∫ y, G₀ y (Jk k τ y - J τ y)) +
      (∫ y, (Λ k y - Λ₀ y) (Jk k τ y) (u k y)) + (∫ y, Λ₀ y (Jk k τ y - J τ y) (u k y)) +
      nrm τ * ℓ k φ := by
    rw [hl, integral_add iGk iΛk, integral_add iG0 i6, a1, a2]
    ring
  rw [e]
  -- bound each term
  have b1 : |∫ y, (G k y - G₀ y) (Jk k τ y)| ≤
      (eLpNorm (G k - G₀) 1 volume).toReal * ((1 + δ k) * nrm τ) :=
    abs_integral_clm_le ((hG.memLp k).sub hG.memLp_lim) (hJkm k τ) hJkb
  have b2 : |∫ y, G₀ y (Jk k τ y - J τ y)| ≤ g1 * (δ k * nrm τ) :=
    abs_integral_clm_le hG.memLp_lim ((hJkm k τ).sub hJm) (hJk k τ)
  have hδk := hδ0 k
  have hnt := hnrm τ
  have b3 := bΛ' _ ((hΛ.memLp k).sub hΛ.memLp_lim) _ (hJkm k τ) _
    (mul_nonneg (by linarith) hnt) hJkb _ (hu k)
  have b4 := bΛ' _ hΛ.memLp_lim _ ((hJkm k τ).sub hJm) _ (mul_nonneg hδk hnt) (hJk k τ) _ (hu k)
  have b3' : |∫ y, (Λ k y - Λ₀ y) (Jk k τ y) (u k y)| ≤
      (1 + δ k) * nrm τ * (eLpNorm (Λ k - Λ₀) 2 volume).toReal * C := by
    refine b3.trans (mul_le_mul_of_nonneg_left (hub k) ?_)
    exact mul_nonneg (mul_nonneg (by linarith) hnt) ENNReal.toReal_nonneg
  have b4' : |∫ y, Λ₀ y (Jk k τ y - J τ y) (u k y)| ≤ δ k * nrm τ * l2 * C := by
    refine b4.trans (mul_le_mul_of_nonneg_left (hub k) ?_)
    exact mul_nonneg (mul_nonneg hδk hnt) ENNReal.toReal_nonneg
  have b5 : |nrm τ * ℓ k φ| ≤ nrm τ * (ε / 4) := by
    rw [abs_mul, abs_of_nonneg hpos.le]
    exact mul_le_mul_of_nonneg_left hℓk hpos.le
  have hsum : (eLpNorm (G k - G₀) 1 volume).toReal * ((1 + δ k) * nrm τ) + g1 * (δ k * nrm τ) +
      (1 + δ k) * nrm τ * (eLpNorm (Λ k - Λ₀) 2 volume).toReal * C +
      δ k * nrm τ * l2 * C ≤ ε / 2 * nrm τ := by
    have := mul_le_mul_of_nonneg_right hks.le hpos.le
    nlinarith
  calc _ ≤ |∫ y, (G k y - G₀ y) (Jk k τ y)| + |∫ y, G₀ y (Jk k τ y - J τ y)| +
        |∫ y, (Λ k y - Λ₀ y) (Jk k τ y) (u k y)| + |∫ y, Λ₀ y (Jk k τ y - J τ y) (u k y)| +
        |nrm τ * ℓ k φ| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ ε / 2 * nrm τ + nrm τ * (ε / 4) := by
        have := add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3') b4') b5
        linarith
    _ ≤ ε * nrm τ := by nlinarith

end Main

/-! ### Weak convergence from real coordinates -/

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- If every real coordinate of an `EuclideanSpace`-valued sequence converges weakly in `L²`, then
the weak convergence hypothesis of `weak_jet_variation` holds for every `L²` dual-valued
coefficient. -/
theorem tendsto_integral_of_weak_coord {u : ℕ → 𝕋 → EuclideanSpace ℝ ι}
    {u₀ : 𝕋 → EuclideanSpace ℝ ι} (hu : ∀ k, MemLp (u k) 2 volume) (hu₀ : MemLp u₀ 2 volume)
    (hw : ∀ i (φ : 𝕋 → ℝ), MemLp φ 2 volume →
      Tendsto (fun k => ∫ y, φ y * u k y i) atTop (𝓝 (∫ y, φ y * u₀ y i)))
    (g : 𝕋 → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hg : MemLp g 2 volume) :
    Tendsto (fun k => ∫ y, g y (u k y)) atTop (𝓝 (∫ y, g y (u₀ y))) := by
  classical
  set b := EuclideanSpace.basisFun ι ℝ
  have hdec : ∀ (w : 𝕋 → EuclideanSpace ℝ ι) (y : 𝕋),
      g y (w y) = ∑ i, g y (b i) * w y i := by
    intro w y
    conv_lhs => rw [← b.sum_repr (w y)]
    simp only [map_sum, map_smul, smul_eq_mul, b, EuclideanSpace.basisFun_repr]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hφ : ∀ i, MemLp (fun y => g y (b i)) 2 volume := fun i =>
    hg.of_le_mul (c := ‖b i‖) (LpProductContinuity.aestronglyMeasurable_apply hg.1
      aestronglyMeasurable_const) (Eventually.of_forall fun y => by
        rw [mul_comm]; exact (g y).le_opNorm _)
  have hint : ∀ (w : 𝕋 → EuclideanSpace ℝ ι), MemLp w 2 volume → ∀ i,
      Integrable (fun y => g y (b i) * w y i) volume := by
    intro w hw' i
    have hwi : MemLp (fun y => w y i) 2 volume :=
      hw'.of_le_mul (c := 1) ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous
        |>.comp_aestronglyMeasurable hw'.1) (Eventually.of_forall fun y => by
          rw [one_mul]; exact PiLp.norm_apply_le (w y) i)
    exact integrable_bilin_two_two (ContinuousLinearMap.mul ℝ ℝ) (hφ i) hwi
  simp_rw [hdec]
  rw [integral_finset_sum _ fun i _ => hint u₀ hu₀ i]
  have : (fun k => ∫ y, ∑ i, g y (b i) * u k y i) = fun k => ∑ i, ∫ y, g y (b i) * u k y i := by
    funext k
    rw [integral_finset_sum _ fun i _ => hint (u k) (hu k) i]
  rw [this]
  exact tendsto_finset_sum _ fun i _ => hw i _ (hφ i)

end Coordinates

/-- Finite sums of strongly convergent sequences. -/
theorem lpTendsto_finset_sum_aux {X V : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ι' : Type*} (s : Finset ι') {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {f : ι' → ℕ → X → V} {f₀ : ι' → X → V}
    (hf : ∀ i ∈ s, LpTendsto ν p (f i) (f₀ i)) :
    LpTendsto ν p (fun k x => ∑ i ∈ s, f i k x) (fun x => ∑ i ∈ s, f₀ i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LpTendsto.const (ν := ν) (p := p) (u := fun _ : X => (0 : V)) MemLp.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-! ### Operator-valued strong convergence from convergence on each vector -/

section Basis

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {T F : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map on a finite-dimensional space is the sum of its values on a basis. -/
theorem clm_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ T) (L : T →L[ℝ] F) :
    L = ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (L (b i)) := by
  ext t
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  conv_lhs => rw [← b.sum_repr t]
  rw [map_sum]
  simp only [map_smul]

/-- **Operator-valued strong convergence from vectorwise convergence** (`T` finite
dimensional): if `G_k(·) t → G(·) t` in `L^p` for every `t`, then `G_k → G` in `L^p` in operator
norm. -/
theorem lpTendsto_clm_of_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] {G : ℕ → X → T →L[ℝ] F}
    {G₀ : X → T →L[ℝ] F} (h : ∀ t, LpTendsto ν p (fun k x => G k x t) (fun x => G₀ x t)) :
    LpTendsto ν p G G₀ := by
  classical
  set b := Module.finBasis ℝ T
  set c : Fin (Module.finrank ℝ T) → F →L[ℝ] (T →L[ℝ] F) := fun i =>
    ContinuousLinearMap.smulRightL ℝ T F (LinearMap.toContinuousLinearMap (b.coord i))
  have hrep : ∀ L : T →L[ℝ] F, L = ∑ i, c i (L (b i)) := fun L =>
    (clm_eq_sum_basis b L).trans rfl
  have hs := lpTendsto_finset_sum_aux (Finset.univ) fun i _ => (h (b i)).clm
    (ContinuousLinearMap.smulRightL ℝ T F (LinearMap.toContinuousLinearMap (b.coord i)))
  refine hs.congr (fun k => Eventually.of_forall fun x => (hrep (G k x)).symm)
    (Eventually.of_forall fun x => (hrep (G₀ x)).symm)

end Basis

end

end RenewalGeometry.WeakJetPairing
