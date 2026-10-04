/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LpProductContinuity
import RenewalGeometry.Analysis.SobolevBoxCompactness

/-!
# Calculus for first variations of local actions: differentiation under the integral, the
  critical product, and uniform weak–strong pairings

Generic infrastructure (no renewal notions) for `prop:reduced-continuity`,
`prop:weak-fermion` and `prop:variation-continuity` of the Einstein–Standard-Model
action-closure manuscript.

* `aestronglyMeasurable_comp_of_continuousOn'`: composition with a function continuous on an open
  set containing the essential range.
* `hasDerivAt_integral_curve` (**first variation of a local action**): for a density `G` that is
  `C¹` on an open set `U` of a finite-dimensional jet space, jets `J` with values in a compact
  `K ⊂ U` and bounded directions `J₁, J₂`,
  `d/dε|₀ ∫ (G(J + εJ₁ + ε²J₂) - G(J)) = ∫ DG(J)[J₁]` on a finite measure space.
* `LpTendsto.trilin_critical` (**the critical product**): `f_h → f` in `L²`, `u_h → u`,
  `v_h → v` in `L²` with a uniform `L⁴` bound give `B(f_h, u_h, v_h) → B(f, u, v)` in `L¹` for a
  bounded trilinear `B` (the spin-connection term `ω ψ̄ ψ` of the Dirac action, which is
  Hölder-critical in four dimensions).
* `abs_integral_sub_le_of_opNorm` (dual estimates): the pairing of an operator-valued density with
  a test field of norm `≤ 1` moves by at most the `L¹` operator distance.
* `exists_isTest_eLpNorm_sub_le` (density of `C_c^∞(Ω)` in `L²(Ω)` for a box `Ω`),
  `tendsto_integral_of_weak` (test pairings plus an `L²` bound give pairings with every `L²`
  function), and `uniform_weak_strong` (**finite-net upgrade**): for `S_h → S` strongly in `L²`
  and `W_h ⇀ W` weakly in `L²`, `∫ S_h τ W_h → ∫ S τ W` uniformly over all test values `τ` with
  `|τ| ≤ 1` and Lipschitz constant `≤ L` (a cell partition of mesh `δ` replaces `τ` by
  finitely many cell constants).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Convolution

noncomputable section

namespace RenewalGeometry.FirstVariationCalculus

/-! ### Measurability -/

/-- A function continuous on an open set `s`, composed with an a.e.-measurable map with values a.e.
in `s`, is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_comp_of_continuousOn' {X Z W : Type*} [MeasurableSpace X]
    {μ : Measure X} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [NormedAddCommGroup W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    {s : Set Z} (hs : IsOpen s) {Φ : Z → W} (hΦ : ContinuousOn Φ s) {f : X → Z}
    (hf : AEMeasurable f μ) (hin : ∀ᵐ x ∂μ, f x ∈ s) :
    AEStronglyMeasurable (fun x => Φ (f x)) μ := by
  classical
  have hm : Measurable (s.piecewise Φ fun _ => 0) :=
    ContinuousOn.measurable_piecewise hΦ continuousOn_const hs.measurableSet
  refine (hm.comp_aemeasurable hf).aestronglyMeasurable.congr ?_
  filter_upwards [hin] with x hx
  simp [Function.comp, Set.piecewise, hx]

/-! ### Differentiation under the integral sign along polynomial curves -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **First variation of a local action.**  Let `G` be `C¹` on an open set `U` of a
finite-dimensional space, `J` a measurable jet with values in a compact `K ⊂ U`, and `J₁, J₂`
bounded measurable directions.  On a finite measure space,
`ε ↦ ∫ (G(J + εJ₁ + ε²J₂) - G(J))` has derivative `∫ DG(J)[J₁]` at `0`. -/
theorem hasDerivAt_integral_curve [IsFiniteMeasure μ] {G : V → ℝ} {U : Set V} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) {J J₁ J₂ : X → V}
    (hJm : AEMeasurable J μ) (hJ₁m : AEMeasurable J₁ μ) (hJ₂m : AEMeasurable J₂ μ)
    (hJK : ∀ᵐ x ∂μ, J x ∈ K) {C₁ C₂ : ℝ} (hJ₁ : ∀ᵐ x ∂μ, ‖J₁ x‖ ≤ C₁)
    (hJ₂ : ∀ᵐ x ∂μ, ‖J₂ x‖ ≤ C₂) :
    HasDerivAt (fun ε : ℝ => ∫ x, (G (J x + ε • J₁ x + ε ^ 2 • J₂ x) - G (J x)) ∂μ)
      (∫ x, fderiv ℝ G (J x) (J₁ x) ∂μ) 0 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (Metric.cthickening δ K) := hK.cthickening
  have hDc : ContinuousOn (fderiv ℝ G) U := hG.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨L, hL⟩ := (hK'.image_of_continuousOn (hDc.mono hδU)).isBounded.exists_norm_le
  set c₁ := max C₁ 0
  set c₂ := max C₂ 0
  have hc₁ : 0 ≤ c₁ := le_max_right _ _
  have hc₂ : 0 ≤ c₂ := le_max_right _ _
  have hgood : ∀ᵐ x ∂μ, J x ∈ K ∧ ‖J₁ x‖ ≤ c₁ ∧ ‖J₂ x‖ ≤ c₂ := by
    filter_upwards [hJK, hJ₁, hJ₂] with x h1 h2 h3
    exact ⟨h1, h2.trans (le_max_left _ _), h3.trans (le_max_left _ _)⟩
  set ε₀ := min 1 (δ / (c₁ + c₂ + 1))
  have hε₀ : 0 < ε₀ := lt_min one_pos (div_pos hδ (by positivity))
  set curve : ℝ → X → V := fun ε x => J x + ε • J₁ x + ε ^ 2 • J₂ x
  have hmemK : ∀ ε ∈ Metric.ball (0 : ℝ) ε₀, ∀ x, J x ∈ K ∧ ‖J₁ x‖ ≤ c₁ ∧ ‖J₂ x‖ ≤ c₂ →
      curve ε x ∈ Metric.cthickening δ K := by
    intro ε hε x ⟨hJx, hJ₁', hJ₂'⟩
    have hε' : |ε| < ε₀ := by simpa [Real.dist_eq] using hε
    have hε1 : |ε| ≤ 1 := (hε'.le).trans (min_le_left _ _)
    have hεδ : |ε| * (c₁ + c₂ + 1) ≤ δ := by
      have := (hε'.le).trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at this
    refine Metric.mem_cthickening_of_dist_le _ (J x) δ K hJx ?_
    rw [dist_eq_norm]
    have : curve ε x - J x = ε • J₁ x + ε ^ 2 • J₂ x := by simp only [curve]; abel
    rw [this]
    calc ‖ε • J₁ x + ε ^ 2 • J₂ x‖ ≤ |ε| * c₁ + |ε| ^ 2 * c₂ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hJ₁' (abs_nonneg _)
          · rw [norm_smul, Real.norm_eq_abs, abs_pow]
            exact mul_le_mul_of_nonneg_left hJ₂' (by positivity)
      _ ≤ |ε| * c₁ + |ε| * c₂ := by
          gcongr
          calc |ε| ^ 2 = |ε| * |ε| := sq _
            _ ≤ |ε| * 1 := mul_le_mul_of_nonneg_left hε1 (abs_nonneg _)
            _ = |ε| := mul_one _
      _ ≤ |ε| * (c₁ + c₂ + 1) := by nlinarith [abs_nonneg ε]
      _ ≤ δ := hεδ
  have hmemU : ∀ ε ∈ Metric.ball (0 : ℝ) ε₀, ∀ᵐ x ∂μ, curve ε x ∈ U := fun ε hε => by
    filter_upwards [hgood] with x hx using hδU (hmemK ε hε x hx)
  have hcurvem : ∀ ε : ℝ, AEMeasurable (curve ε) μ := fun ε =>
    (show Continuous fun v : V × V × V => v.1 + ε • v.2.1 + ε ^ 2 • v.2.2 by fun_prop).measurable
      |>.comp_aemeasurable (hJm.prodMk (hJ₁m.prodMk hJ₂m))
  set F : ℝ → X → ℝ := fun ε x => G (curve ε x) - G (J x)
  set F' : ℝ → X → ℝ := fun ε x => fderiv ℝ G (curve ε x) (J₁ x + (2 * ε) • J₂ x)
  have h0mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε₀ := Metric.mem_ball_self hε₀
  have hGJm : AEStronglyMeasurable (fun x => G (J x)) μ :=
    aestronglyMeasurable_comp_of_continuousOn' hU hG.continuousOn hJm
      (by filter_upwards [hJK] with x hx using hKU hx)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F') (x₀ := 0)
    (bound := fun _ => L * (c₁ + 2 * c₂)) (Metric.ball_mem_nhds 0 hε₀)
    (by
      filter_upwards [Metric.ball_mem_nhds 0 hε₀] with ε hε
      exact (aestronglyMeasurable_comp_of_continuousOn' hU hG.continuousOn (hcurvem ε)
        (hmemU ε hε)).sub hGJm)
    (by simp [F, curve])
    (by
      have hD : AEStronglyMeasurable (fun x => fderiv ℝ G (curve 0 x)) μ :=
        aestronglyMeasurable_comp_of_continuousOn' hU hDc (hcurvem 0) (hmemU 0 h0mem)
      exact LpProductContinuity.aestronglyMeasurable_apply hD
        ((show Continuous fun v : V × V => v.1 + (2 * (0 : ℝ)) • v.2 by fun_prop).measurable
          |>.comp_aemeasurable (hJ₁m.prodMk hJ₂m)).aestronglyMeasurable)
    (by
      filter_upwards [hgood] with x hx
      intro ε hε
      have hp := hL _ ⟨_, hmemK ε hε x hx, rfl⟩
      have hε1 : |ε| ≤ 1 := by
        have : |ε| < ε₀ := by simpa [Real.dist_eq] using hε
        exact this.le.trans (min_le_left _ _)
      refine ((fderiv ℝ G (curve ε x)).le_opNorm _).trans ?_
      refine mul_le_mul hp ?_ (norm_nonneg _) ((norm_nonneg _).trans hp)
      refine (norm_add_le _ _).trans (add_le_add hx.2.1 ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
      calc 2 * |ε| * ‖J₂ x‖ ≤ 2 * 1 * c₂ := by gcongr; exact hx.2.2
        _ = 2 * c₂ := by ring)
    (integrable_const _)
    (by
      filter_upwards [hgood] with x hx
      intro ε hε
      have hU' : curve ε x ∈ U := hδU (hmemK ε hε x hx)
      have hGd : HasFDerivAt G (fderiv ℝ G (curve ε x)) (curve ε x) :=
        ((hG.differentiableOn one_ne_zero _ hU').differentiableAt
          (hU.mem_nhds hU')).hasFDerivAt
      have hc : HasDerivAt (fun ε => curve ε x) (J₁ x + (2 * ε) • J₂ x) ε := by
        have h1 : HasDerivAt (fun ε : ℝ => ε • J₁ x) ((1 : ℝ) • J₁ x) ε :=
          (hasDerivAt_id ε).smul_const (J₁ x)
        have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 • J₂ x) (((2 : ℕ) * ε ^ (2 - 1)) • J₂ x) ε :=
          (hasDerivAt_pow 2 ε).smul_const (J₂ x)
        exact ((h1.const_add (J x)).add h2).congr_deriv (by simp)
      exact (hGd.comp_hasDerivAt ε hc).sub_const _)
  refine key.2.congr_deriv ?_
  congr 1
  funext x
  simp [F', curve]

/-! ### Hölder for trilinear maps and the critical product -/

section Critical

variable {E F G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

theorem holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 :=
  ⟨by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
      ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩

theorem aestronglyMeasurable_trilin (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] W) {a : X → E} {b : X → F}
    {c : X → G} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) : AEStronglyMeasurable (fun x => B (a x) (b x) (c x)) μ :=
  LpProductContinuity.aestronglyMeasurable_apply
    (LpProductContinuity.aestronglyMeasurable_apply (B.continuous.comp_aestronglyMeasurable ha)
      hb) hc

/-- Hölder for a bounded trilinear map, `L² × L⁴ × L⁴ → L¹`. -/
theorem eLpNorm_trilin_le (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] W) {f : X → E} {u : X → F} {v : X → G}
    (hf : AEStronglyMeasurable f μ) (hu : AEStronglyMeasurable u μ)
    (hv : AEStronglyMeasurable v μ) :
    eLpNorm (fun x => B (f x) (u x) (v x)) 1 μ ≤
      ‖B‖₊ * eLpNorm f 2 μ * (eLpNorm u 4 μ * eLpNorm v 4 μ) := by
  have h1 : eLpNorm (fun x => ‖u x‖ * ‖v x‖) 2 μ ≤ 1 * eLpNorm u 4 μ * eLpNorm v 4 μ := by
    have := holderTriple_four_four_two
    exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (r := 2) hu hv (fun a b => ‖a‖ * ‖b‖) 1
      (Eventually.of_forall fun x => by simp [nnnorm_mul])
  have h2 : eLpNorm (fun x => ‖B (f x)‖ * (‖u x‖ * ‖v x‖)) 1 μ ≤
      ‖B‖₊ * eLpNorm f 2 μ * eLpNorm (fun x => ‖u x‖ * ‖v x‖) 2 μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (r := 1) (p := 2) (q := 2) hf
      (hu.norm.mul hv.norm) (fun a (b : ℝ) => ‖B a‖ * b) ‖B‖₊
      (Eventually.of_forall fun x => by
        rw [← NNReal.coe_le_coe]
        push_cast
        simp only [norm_mul, norm_norm]
        exact mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _))
  have h3 : eLpNorm (fun x => B (f x) (u x) (v x)) 1 μ ≤
      eLpNorm (fun x => ‖B (f x)‖ * (‖u x‖ * ‖v x‖)) 1 μ := by
    refine eLpNorm_mono fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖B (f x) (u x) (v x)‖ ≤ ‖B (f x) (u x)‖ * ‖v x‖ := (B (f x) (u x)).le_opNorm _
      _ ≤ ‖B (f x)‖ * ‖u x‖ * ‖v x‖ := by gcongr; exact (B (f x)).le_opNorm _
      _ = ‖B (f x)‖ * (‖u x‖ * ‖v x‖) := by ring
  refine (h3.trans h2).trans ?_
  calc (‖B‖₊ : ℝ≥0∞) * eLpNorm f 2 μ * eLpNorm (fun x => ‖u x‖ * ‖v x‖) 2 μ
      ≤ ‖B‖₊ * eLpNorm f 2 μ * (1 * eLpNorm u 4 μ * eLpNorm v 4 μ) := by gcongr
    _ = ‖B‖₊ * eLpNorm f 2 μ * (eLpNorm u 4 μ * eLpNorm v 4 μ) := by rw [one_mul]

/-- The bilinear part of the critical product, for a fixed `L²` coefficient that is strongly
measurable: truncation. -/
theorem tendsto_trilin_fixed [IsFiniteMeasure μ] (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] W)
    {f : X → E} (hfs : StronglyMeasurable f) (hf : MemLp f 2 μ)
    {u : ℕ → X → F} {u₀ : X → F} {v : ℕ → X → G} {v₀ : X → G}
    (hu : RenewalGeometry.LpTendsto μ 2 u u₀) (hv : RenewalGeometry.LpTendsto μ 2 v v₀)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hu4 : ∀ n, eLpNorm (u n) 4 μ ≤ M)
    (hv4 : ∀ n, eLpNorm (v n) 4 μ ≤ M) (hu04 : eLpNorm u₀ 4 μ ≤ M)
    (hv04 : eLpNorm v₀ 4 μ ≤ M) :
    Tendsto (fun n => eLpNorm (fun x => B (f x) (u n x) (v n x) - B (f x) (u₀ x) (v₀ x)) 1 μ)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set s : ℕ → Set X := fun R => {x | ‖f x‖ ≤ R}
  have hs : ∀ R, MeasurableSet (s R) := fun R =>
    measurableSet_le hfs.norm.measurable measurable_const
  set g : ℕ → X → E := fun R => (s R).indicator f
  set t : ℕ → X → E := fun R => (s R)ᶜ.indicator f
  have hgt : ∀ R x, f x = g R x + t R x := fun R x => by
    by_cases hx : x ∈ s R <;> simp [g, t, hx]
  have hgm : ∀ R, AEStronglyMeasurable (g R) μ := fun R =>
    (hfs.indicator (hs R)).aestronglyMeasurable
  have htm : ∀ R, AEStronglyMeasurable (t R) μ := fun R =>
    (hfs.indicator (hs R).compl).aestronglyMeasurable
  have hum := fun n => (hu.memLp n).1
  have hvm := fun n => (hv.memLp n).1
  -- the tail of `f`
  have htail : Tendsto (fun R => eLpNorm (t R) 2 μ) atTop (𝓝 0) := by
    refine LpProductContinuity.tendsto_eLpNorm_of_dominated_ae (by norm_num) (by norm_num) htm
      hf.norm (fun R => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · by_cases hx : x ∈ s R <;> simp [t, hx]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖f x‖⌉₊] with R hR
      have : x ∈ s R := by
        show ‖f x‖ ≤ R
        exact (Nat.le_ceil _).trans (by exact_mod_cast hR)
      simp [t, this]
  set K := (‖B‖₊ : ℝ≥0∞) * (M * M)
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top hM hM)
  have htail' : Tendsto (fun R => eLpNorm (t R) 2 μ * K) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const htail (Or.inr hK)
  obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.mp htail') (ε / 3)
    (ENNReal.div_pos hε.ne' (by norm_num))).exists
  -- the truncated part converges by the bounded-coefficient clause
  have hbil : RenewalGeometry.LpTendsto μ 1 (fun n x => (B (g R x)) (u n x) (v n x))
      (fun x => (B (g R x)) (u₀ x) (v₀ x)) := by
    refine LpProductContinuity.LpTendsto.coeff_bilin (β := fun _ x => B (g R x))
      (K := ‖B‖ * R) (fun _ => B.continuous.comp_aestronglyMeasurable (hgm R)) ?_
      (fun _ => Eventually.of_forall fun x => ?_) hu hv
    · intro δ hδ; simp [edist_self, not_le.2 hδ]
    · refine (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      by_cases hx : x ∈ s R
      · simp only [g, Set.indicator_of_mem hx]; exact hx
      · simp [g, hx]
  obtain ⟨N, hN⟩ := ((ENNReal.tendsto_nhds_zero.mp hbil.tendsto) (ε / 3)
    (ENNReal.div_pos hε.ne' (by norm_num))).exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsplit : (fun x => B (f x) (u n x) (v n x) - B (f x) (u₀ x) (v₀ x)) =
      ((fun x => B (g R x) (u n x) (v n x)) - fun x => B (g R x) (u₀ x) (v₀ x)) +
        (fun x => B (t R x) (u n x) (v n x)) - fun x => B (t R x) (u₀ x) (v₀ x) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, hgt R x, map_add, ContinuousLinearMap.add_apply]
    abel
  rw [hsplit]
  have m1 := (aestronglyMeasurable_trilin B (hgm R) (hum n) (hvm n)).sub
    (aestronglyMeasurable_trilin B (hgm R) hu.memLp_lim.1 hv.memLp_lim.1)
  have m2 := aestronglyMeasurable_trilin B (htm R) (hum n) (hvm n)
  have m3 := aestronglyMeasurable_trilin B (htm R) hu.memLp_lim.1 hv.memLp_lim.1
  refine (eLpNorm_sub_le (m1.add m2) m3 le_rfl).trans ?_
  refine (add_le_add (eLpNorm_add_le m1 m2 le_rfl) le_rfl).trans ?_
  have b1 : eLpNorm ((fun x => B (g R x) (u n x) (v n x)) - fun x => B (g R x) (u₀ x) (v₀ x)) 1 μ
      ≤ ε / 3 := hN n hn
  have b2 : eLpNorm (fun x => B (t R x) (u n x) (v n x)) 1 μ ≤ ε / 3 := by
    refine (eLpNorm_trilin_le B (htm R) (hum n) (hvm n)).trans (le_trans ?_ hR)
    calc (‖B‖₊ : ℝ≥0∞) * eLpNorm (t R) 2 μ * (eLpNorm (u n) 4 μ * eLpNorm (v n) 4 μ)
        ≤ ‖B‖₊ * eLpNorm (t R) 2 μ * (M * M) := by gcongr; exacts [hu4 n, hv4 n]
      _ = eLpNorm (t R) 2 μ * K := by ring
  have b3 : eLpNorm (fun x => B (t R x) (u₀ x) (v₀ x)) 1 μ ≤ ε / 3 := by
    refine (eLpNorm_trilin_le B (htm R) hu.memLp_lim.1 hv.memLp_lim.1).trans (le_trans ?_ hR)
    calc (‖B‖₊ : ℝ≥0∞) * eLpNorm (t R) 2 μ * (eLpNorm u₀ 4 μ * eLpNorm v₀ 4 μ)
        ≤ ‖B‖₊ * eLpNorm (t R) 2 μ * (M * M) := by gcongr
      _ = eLpNorm (t R) 2 μ * K := by ring
  calc _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add b1 b2) b3
    _ = ε := ENNReal.add_thirds ε

/-- **The critical product.**  On a finite measure space, if `f_h → f` in `L²` and `u_h → u`,
`v_h → v` in `L²` with `‖u_h‖_{L⁴}, ‖v_h‖_{L⁴} ≤ M`, then `B(f_h, u_h, v_h) → B(f, u, v)` in `L¹`
for every bounded trilinear `B`.  The exponents `(2, 4, 4)` are Hölder-critical; the proof
splits off `B(f_h - f, u_h, v_h)` (Hölder) and truncates the fixed coefficient `f`. -/
theorem tendsto_trilin_critical [IsFiniteMeasure μ] (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] W)
    {f : ℕ → X → E} {f₀ : X → E} {u : ℕ → X → F} {u₀ : X → F} {v : ℕ → X → G} {v₀ : X → G}
    (hf : RenewalGeometry.LpTendsto μ 2 f f₀) (hu : RenewalGeometry.LpTendsto μ 2 u u₀)
    (hv : RenewalGeometry.LpTendsto μ 2 v v₀) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hu4 : ∀ n, eLpNorm (u n) 4 μ ≤ M) (hv4 : ∀ n, eLpNorm (v n) 4 μ ≤ M) :
    RenewalGeometry.LpTendsto μ 1 (fun n x => B (f n x) (u n x) (v n x))
      (fun x => B (f₀ x) (u₀ x) (v₀ x)) := by
  have hu04 : eLpNorm u₀ 4 μ ≤ M := hu.eLpNorm_le_of_bound (by norm_num) hu4
  have hv04 : eLpNorm v₀ 4 μ ≤ M := hv.eLpNorm_le_of_bound (by norm_num) hv4
  have hum := fun n => (hu.memLp n).1
  have hvm := fun n => (hv.memLp n).1
  have hfm := fun n => (hf.memLp n).1
  set K := (‖B‖₊ : ℝ≥0∞) * (M * M)
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top hM hM)
  have hmem : ∀ {a : X → E} {b : X → F} {c : X → G}, MemLp a 2 μ → MemLp b 2 μ →
      eLpNorm b 4 μ ≤ M → MemLp c 2 μ → eLpNorm c 4 μ ≤ M →
      MemLp (fun x => B (a x) (b x) (c x)) 1 μ := fun ha hb hb4 hc hc4 =>
    ⟨aestronglyMeasurable_trilin B ha.1 hb.1 hc.1, (eLpNorm_trilin_le B ha.1 hb.1 hc.1).trans_lt
      (by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ha.eLpNorm_lt_top) ?_
        exact ENNReal.mul_lt_top (hb4.trans_lt hM.lt_top) (hc4.trans_lt hM.lt_top))⟩
  refine ⟨fun n => hmem (hf.memLp n) (hu.memLp n) (hu4 n) (hv.memLp n) (hv4 n),
    hmem hf.memLp_lim hu.memLp_lim hu04 hv.memLp_lim hv04, ?_⟩
  -- strongly measurable modification of the limit coefficient
  obtain ⟨f', hf's, hff'⟩ := hf.memLp_lim.1
  have hf'L : MemLp f' 2 μ := hf.memLp_lim.ae_eq hff'
  have hT2 := tendsto_trilin_fixed B hf's hf'L hu hv hM hu4 hv4 hu04 hv04
  have hT1 : Tendsto (fun n => eLpNorm (fun x => B (f n x - f₀ x) (u n x) (v n x)) 1 μ) atTop
      (𝓝 0) := by
    have hb : ∀ n, eLpNorm (fun x => B (f n x - f₀ x) (u n x) (v n x)) 1 μ ≤
        eLpNorm (f n - f₀) 2 μ * K := by
      intro n
      refine (eLpNorm_trilin_le B ((hfm n).sub hf.memLp_lim.1) (hum n) (hvm n)).trans ?_
      calc (‖B‖₊ : ℝ≥0∞) * eLpNorm (fun x => f n x - f₀ x) 2 μ *
            (eLpNorm (u n) 4 μ * eLpNorm (v n) 4 μ)
          ≤ ‖B‖₊ * eLpNorm (fun x => f n x - f₀ x) 2 μ * (M * M) := by
            gcongr; exacts [hu4 n, hv4 n]
        _ = eLpNorm (f n - f₀) 2 μ * K := by
            simp only [K]; rw [show (fun x => f n x - f₀ x) = f n - f₀ from rfl]; ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
    simpa using ENNReal.Tendsto.mul_const hf.tendsto (Or.inr hK)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by rw [← add_zero (0 : ℝ≥0∞)]; exact hT1.add hT2) (fun n => zero_le) fun n => ?_
  have hsplit : (fun x => B (f n x) (u n x) (v n x)) - (fun x => B (f₀ x) (u₀ x) (v₀ x)) =ᵐ[μ]
      (fun x => B (f n x - f₀ x) (u n x) (v n x)) +
        fun x => B (f' x) (u n x) (v n x) - B (f' x) (u₀ x) (v₀ x) := by
    filter_upwards [hff'] with x hx
    simp only [Pi.add_apply, Pi.sub_apply, map_sub, ContinuousLinearMap.sub_apply, hx]
    abel
  rw [eLpNorm_congr_ae hsplit]
  exact eLpNorm_add_le (aestronglyMeasurable_trilin B ((hfm n).sub hf.memLp_lim.1) (hum n)
    (hvm n)) ((aestronglyMeasurable_trilin B hf's.aestronglyMeasurable (hum n) (hvm n)).sub
      (aestronglyMeasurable_trilin B hf's.aestronglyMeasurable hu.memLp_lim.1 hv.memLp_lim.1))
    le_rfl

end Critical

/-! ### Dual estimates -/

/-- **Dual estimate**: pairing operator-valued densities with a test field bounded by `1` moves by
at most the `L¹` operator distance. -/
theorem abs_integral_sub_le_of_opNorm {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {Λ Λ' : X → T →L[ℝ] ℝ} (hΛ : Integrable Λ μ) (hΛ' : Integrable Λ' μ) {τ : X → T}
    (hτ : AEStronglyMeasurable τ μ) {c : ℝ} (hτc : ∀ᵐ x ∂μ, ‖τ x‖ ≤ c) :
    |∫ x, Λ x (τ x) ∂μ - ∫ x, Λ' x (τ x) ∂μ| ≤ c * ∫ x, ‖Λ x - Λ' x‖ ∂μ := by
  have hc : 0 ≤ c ∨ ∀ᵐ x ∂μ, False := by
    by_cases h : 0 ≤ c
    · exact Or.inl h
    · right; filter_upwards [hτc] with x hx; exact h ((norm_nonneg _).trans hx)
  have i1 : Integrable (fun x => Λ x (τ x)) μ := by
    rcases hc with hc | hc
    · refine (hΛ.norm.mul_const c).mono' (LpProductContinuity.aestronglyMeasurable_apply hΛ.1 hτ)
        ?_
      filter_upwards [hτc] with x hx
      exact ((Λ x).le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    · have : μ = 0 := ae_eq_bot.mp (eventually_false_iff_eq_bot.mp hc)
      simp [this]
  have i2 : Integrable (fun x => Λ' x (τ x)) μ := by
    rcases hc with hc | hc
    · refine (hΛ'.norm.mul_const c).mono' (LpProductContinuity.aestronglyMeasurable_apply hΛ'.1 hτ)
        ?_
      filter_upwards [hτc] with x hx
      exact ((Λ' x).le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    · have : μ = 0 := ae_eq_bot.mp (eventually_false_iff_eq_bot.mp hc)
      simp [this]
  rw [← integral_sub i1 i2, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_ae (i1.sub i2).norm ((hΛ.sub hΛ').norm.const_mul c) ?_
  filter_upwards [hτc] with x hx
  rw [← ContinuousLinearMap.sub_apply]
  calc ‖(Λ x - Λ' x) (τ x)‖ ≤ ‖Λ x - Λ' x‖ * ‖τ x‖ := (Λ x - Λ' x).le_opNorm _
    _ ≤ ‖Λ x - Λ' x‖ * c := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = c * ‖(Λ - Λ') x‖ := by rw [mul_comm]; rfl

/-! ### Hölder for complex pairings -/

theorem norm_integral_le_eLpNorm_one {F : X → ℂ} :
    ‖∫ x, F x ∂μ‖ ≤ (eLpNorm F 1 μ).toReal := by
  refine (norm_integral_le_lintegral_norm F).trans (le_of_eq ?_)
  rw [eLpNorm_one_eq_lintegral_enorm]
  congr 1
  refine lintegral_congr fun x => ?_
  exact ofReal_norm_eq_enorm (F x)

/-- `|∫ h W| ≤ ‖h‖₂ ‖W‖₂`. -/
theorem norm_integral_mul_le {h W : X → ℂ} (hh : MemLp h 2 μ) (hW : MemLp W 2 μ) :
    ‖∫ x, h x * W x ∂μ‖ ≤ (eLpNorm h 2 μ).toReal * (eLpNorm W 2 μ).toReal := by
  refine norm_integral_le_eLpNorm_one.trans ?_
  rw [← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hh.eLpNorm_ne_top hW.eLpNorm_ne_top) ?_
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (r := 1) (p := 2) (q := 2) hh.1 hW.1
    (fun a b : ℂ => a * b) 1 (Eventually.of_forall fun x => by simp [nnnorm_mul])
  simpa using this

/-- An approximation principle: if `b_j(n) → b_j` for each `j` and `a_n`, `a` are within `c_j` of
`b_j(n)`, `b_j` uniformly in `n`, with `c_j → 0`, then `a_n → a`. -/
theorem tendsto_of_approx {a : ℕ → ℂ} {a₀ : ℂ} {b : ℕ → ℕ → ℂ} {b₀ : ℕ → ℂ} {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) (hb : ∀ j, Tendsto (b j) atTop (𝓝 (b₀ j)))
    (h1 : ∀ j n, ‖a n - b j n‖ ≤ c j) (h2 : ∀ j, ‖a₀ - b₀ j‖ ≤ c j) :
    Tendsto a atTop (𝓝 a₀) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ := ((hc.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)))).exists
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hb j) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  calc ‖a n - a₀‖ = ‖(a n - b j n) + (b j n - b₀ j) - (a₀ - b₀ j)‖ := by congr 1; ring
    _ ≤ ‖a n - b j n‖ + ‖b j n - b₀ j‖ + ‖a₀ - b₀ j‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have := hN n hn; rw [dist_eq_norm] at this
        linarith [h1 j n, h2 j]
    _ = ε := by ring

/-! ### Density of test functions in `L²` of a box -/

section Density

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open SobolevOpen (box IsTest)

/-- The closed box shrunk by `r`. -/
def innerBox (a b : ι → ℝ) (r : ℝ) : Set (ι → ℝ) := Set.pi univ fun i => Icc (a i + r) (b i - r)

theorem innerBox_subset_box {a b : ι → ℝ} {r : ℝ} (hr : 0 < r) : innerBox a b r ⊆ box a b := by
  intro x hx i _
  have := hx i (mem_univ i)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

theorem isCompact_innerBox (a b : ι → ℝ) (r : ℝ) : IsCompact (innerBox a b r) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem isClosed_innerBox (a b : ι → ℝ) (r : ℝ) : IsClosed (innerBox a b r) :=
  isClosed_set_pi fun _ _ => isClosed_Icc

theorem add_mem_innerBox {a b : ι → ℝ} {r s : ℝ} {y z : ι → ℝ} (hy : ‖y‖ ≤ s)
    (hz : z ∈ innerBox a b r) : y + z ∈ innerBox a b (r - s) := by
  intro i _
  have h1 := hz i (mem_univ i)
  have h2 : |y i| ≤ s := by
    have := (norm_le_pi_norm y i).trans hy; rwa [Real.norm_eq_abs] at this
  rw [abs_le] at h2
  simp only [Pi.add_apply, mem_Icc]
  constructor <;> linarith [h1.1, h1.2]

/-- **Density of `C_c^∞(Q)` in `L²(Q)`** for an open box `Q`: every real `f ∈ L²(Q)` is an
`L²(Q)`-limit of test functions (shrunken-box truncation and mollification). -/
theorem exists_isTest_eLpNorm_sub_le {a b : ι → ℝ} {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict (box a b))) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ φ, IsTest (box a b) φ ∧ eLpNorm (f - φ) 2 (volume.restrict (box a b)) ≤ ε := by
  set μΩ := volume.restrict (box a b)
  have hbox : MeasurableSet (box a b) := (SobolevOpen.isOpen_box a b).measurableSet
  have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  -- step 1: truncation to a shrunken box
  set r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr0 : ∀ n, 0 < r n := fun n => by positivity
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set t : ℕ → (ι → ℝ) → ℝ := fun n => f - (innerBox a b (r n)).indicator f
  have htm : ∀ n, AEStronglyMeasurable (t n) μΩ := fun n =>
    hf.1.sub (hf.1.indicator (isClosed_innerBox a b (r n)).measurableSet)
  have htail : Tendsto (fun n => eLpNorm (t n) 2 μΩ) atTop (𝓝 0) := by
    refine LpProductContinuity.tendsto_eLpNorm_of_dominated_ae (by norm_num) (by norm_num) htm
      hf.norm (fun n => Eventually.of_forall fun x => ?_) ?_
    · by_cases hx : x ∈ innerBox a b (r n) <;> simp [t, hx]
    · rw [ae_restrict_iff' hbox]
      refine Eventually.of_forall fun x hx => ?_
      have hev : ∀ᶠ n in atTop, x ∈ innerBox a b (r n) := by
        have : ∀ i, ∀ᶠ n in atTop, r n ≤ x i - a i ∧ r n ≤ b i - x i := fun i => by
          have h1 := hx i (mem_univ i)
          exact (hrt.eventually (ge_mem_nhds (sub_pos.mpr h1.1))).and
            (hrt.eventually (ge_mem_nhds (sub_pos.mpr h1.2)))
        filter_upwards [eventually_all.mpr this] with n hn
        intro i _
        exact ⟨by linarith [(hn i).1], by linarith [(hn i).2]⟩
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      simp [t, hn]
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.mp htail) (ε / 2) hε2).exists
  -- step 2: mollification of the truncated function
  set F := (innerBox a b (r n)).indicator f
  have hFm : MeasurableSet (innerBox a b (r n)) := (isClosed_innerBox a b (r n)).measurableSet
  have hF2 : MemLp F 2 volume := by
    refine (memLp_indicator_iff_restrict hFm).mpr ?_
    have := hf.restrict (innerBox a b (r n))
    rwa [Measure.restrict_restrict hFm, inter_eq_left.mpr (innerBox_subset_box (hr0 n))] at this
  have hFc : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_innerBox a b (r n)) fun x hx => by simp [F, hx]
  let φk : ℕ → ContDiffBump (0 : ι → ℝ) := fun k =>
    ⟨1 / ((k : ℝ) + 2), 2 / ((k : ℝ) + 2), by positivity,
      by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  have hrO : Tendsto (fun k => (φk k).rOut) atTop (𝓝 0) := by
    show Tendsto (fun k : ℕ => 2 / ((k : ℝ) + 2)) atTop (𝓝 0)
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
    simpa using this.const_div_atTop 2
  have hmol := Mollifier.tendsto_eLpNorm_normed_bump_convolution_sub (μ := volume) hrO
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hF2
  obtain ⟨k, hk1, hk2⟩ := (((ENNReal.tendsto_nhds_zero.mp hmol) (ε / 2) hε2).and
    (hrO.eventually (gt_mem_nhds (hr0 n)))).exists
  set ρ := (φk k).normed volume
  set φ : (ι → ℝ) → ℝ := ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
  have hφs : ContDiff ℝ ∞ φ :=
    (φk k).hasCompactSupport_normed.contDiff_convolution_left _ (φk k).contDiff_normed
      (hF2.locallyIntegrable (by norm_num))
  have hφc : HasCompactSupport φ := (φk k).hasCompactSupport_normed.convolution _ hFc
  have hφsupp : tsupport φ ⊆ box a b := by
    refine (closure_minimal ?_ (isClosed_innerBox a b (r n - (φk k).rOut))).trans
      (innerBox_subset_box (sub_pos.mpr hk2))
    refine (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)).trans ?_
    rintro _ ⟨y, hy, z, hz, rfl⟩
    refine add_mem_innerBox (r := r n) ?_ ?_
    · rw [(φk k).support_normed_eq, Metric.mem_ball, dist_zero_right] at hy
      exact hy.le
    · by_contra hz'
      exact hz (by simp [F, hz'])
  refine ⟨φ, ⟨hφs, hφc, hφsupp⟩, ?_⟩
  -- step 3: the triangle inequality
  have h1 : eLpNorm (f - F) 2 μΩ ≤ ε / 2 := hn
  have h2 : eLpNorm (F - φ) 2 μΩ ≤ ε / 2 := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    rw [eLpNorm_sub_comm]; exact hk1
  calc eLpNorm (f - φ) 2 μΩ = eLpNorm ((f - F) + (F - φ)) 2 μΩ := by congr 1; abel
    _ ≤ eLpNorm (f - F) 2 μΩ + eLpNorm (F - φ) 2 μΩ :=
        eLpNorm_add_le (htm n) (hF2.1.restrict.sub hφs.continuous.aestronglyMeasurable)
          (by norm_num)
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

/-- Complex `L²(Q)` functions are `L²(Q)`-limits of complex combinations `φ + i ψ` of real test
functions, with error `≤ 2/(j+1)`. -/
theorem exists_test_pair_approx {a b : ι → ℝ} {g : (ι → ℝ) → ℂ}
    (hg : MemLp g 2 (volume.restrict (box a b))) (j : ℕ) :
    ∃ φr φi : (ι → ℝ) → ℝ, IsTest (box a b) φr ∧ IsTest (box a b) φi ∧
      (eLpNorm (g - fun x => ((φr x : ℝ) : ℂ) + Complex.I * ((φi x : ℝ) : ℂ)) 2
        (volume.restrict (box a b))).toReal ≤ 2 / ((j : ℝ) + 1) := by
  set μΩ := volume.restrict (box a b)
  have hre : MemLp (fun x => (g x).re) 2 μΩ := hg.re
  have him : MemLp (fun x => (g x).im) 2 μΩ := hg.im
  have hj : (0 : ℝ≥0∞) < 1 / ((j : ℝ≥0∞) + 1) := by simp
  obtain ⟨φr, hφr, hφr'⟩ := exists_isTest_eLpNorm_sub_le hre hj
  obtain ⟨φi, hφi, hφi'⟩ := exists_isTest_eLpNorm_sub_le him hj
  refine ⟨φr, φi, hφr, hφi, ?_⟩
  have hdecomp : (g - fun x => ((φr x : ℝ) : ℂ) + Complex.I * ((φi x : ℝ) : ℂ)) =
      (fun x => (((g x).re - φr x : ℝ) : ℂ)) +
        fun x => Complex.I * (((g x).im - φi x : ℝ) : ℂ) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    push_cast
    conv_lhs => rw [← Complex.re_add_im (g x)]
    ring
  have e1 : eLpNorm (fun x => (((g x).re - φr x : ℝ) : ℂ)) 2 μΩ ≤ 1 / ((j : ℝ≥0∞) + 1) := by
    refine le_trans (le_of_eq ?_) hφr'
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real]; rfl
  have e2 : eLpNorm (fun x => Complex.I * (((g x).im - φi x : ℝ) : ℂ)) 2 μΩ ≤
      1 / ((j : ℝ≥0∞) + 1) := by
    refine le_trans (le_of_eq ?_) hφi'
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]; rfl
  have hm1 : AEStronglyMeasurable (fun x => (((g x).re - φr x : ℝ) : ℂ)) μΩ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hre.1.sub hφr.smooth.continuous.aestronglyMeasurable)
  have hm2 : AEStronglyMeasurable (fun x => Complex.I * (((g x).im - φi x : ℝ) : ℂ)) μΩ :=
    aestronglyMeasurable_const.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (him.1.sub hφi.smooth.continuous.aestronglyMeasurable))
  rw [hdecomp]
  have hle := (eLpNorm_add_le hm1 hm2 (by norm_num)).trans (add_le_add e1 e2)
  have hne : (1 / ((j : ℝ≥0∞) + 1)) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne, hne⟩) hle).trans (le_of_eq ?_)
  rw [ENNReal.toReal_add hne hne, ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)]
  simp only [ENNReal.toReal_one, ENNReal.toReal_natCast]
  ring

theorem memLp_test_restrict {a b : ι → ℝ} {φ : (ι → ℝ) → ℝ} (hφ : IsTest (box a b) φ) :
    MemLp (fun x => ((φ x : ℝ) : ℂ)) 2 (volume.restrict (box a b)) :=
  ((hφ.smooth.continuous.memLp_of_hasCompactSupport hφ.compact).restrict _).ofReal

/-- **Weak `L²(Q)` convergence from test pairings**: a sequence bounded in `L²(Q)` whose pairings
with all test functions converge has convergent pairings with every `g ∈ L²(Q)`. -/
theorem tendsto_integral_of_weak {a b : ι → ℝ} {W : ℕ → (ι → ℝ) → ℂ} {W₀ : (ι → ℝ) → ℂ}
    (hW : ∀ n, MemLp (W n) 2 (volume.restrict (box a b)))
    (hW₀ : MemLp W₀ 2 (volume.restrict (box a b))) {B : ℝ}
    (hWB : ∀ n, (eLpNorm (W n) 2 (volume.restrict (box a b))).toReal ≤ B)
    (htest : ∀ φ, IsTest (box a b) φ →
      Tendsto (fun n => ∫ x, ((φ x : ℝ) : ℂ) * W n x) atTop (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * W₀ x)))
    {g : (ι → ℝ) → ℂ} (hg : MemLp g 2 (volume.restrict (box a b))) :
    Tendsto (fun n => ∫ x, g x * W n x ∂(volume.restrict (box a b))) atTop
      (𝓝 (∫ x, g x * W₀ x ∂(volume.restrict (box a b)))) := by
  set μΩ := volume.restrict (box a b)
  have hset : ∀ (φ : (ι → ℝ) → ℝ), IsTest (box a b) φ → ∀ w : (ι → ℝ) → ℂ,
      ∫ x, ((φ x : ℝ) : ℂ) * w x = ∫ x, ((φ x : ℝ) : ℂ) * w x ∂μΩ := fun φ hφ w =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.subset h))]).symm
  choose φr φi hφr hφi herr using fun j => exists_test_pair_approx hg j
  set ψ : ℕ → (ι → ℝ) → ℂ := fun j x => ((φr j x : ℝ) : ℂ) + Complex.I * ((φi j x : ℝ) : ℂ)
  have hψL2 : ∀ j, MemLp (ψ j) 2 μΩ := fun j =>
    (memLp_test_restrict (hφr j)).add ((memLp_test_restrict (hφi j)).const_mul Complex.I)
  have hψconv : ∀ j, Tendsto (fun n => ∫ x, ψ j x * W n x ∂μΩ) atTop
      (𝓝 (∫ x, ψ j x * W₀ x ∂μΩ)) := by
    intro j
    have hint : ∀ w : (ι → ℝ) → ℂ, MemLp w 2 μΩ → ∫ x, ψ j x * w x ∂μΩ =
        ∫ x, ((φr j x : ℝ) : ℂ) * w x ∂μΩ + Complex.I * ∫ x, ((φi j x : ℝ) : ℂ) * w x ∂μΩ := by
      intro w hw
      have i1 : Integrable (fun x => ((φr j x : ℝ) : ℂ) * w x) μΩ :=
        (memLp_test_restrict (hφr j)).integrable_mul hw
      have i2 : Integrable (fun x => ((φi j x : ℝ) : ℂ) * w x) μΩ :=
        (memLp_test_restrict (hφi j)).integrable_mul hw
      rw [← integral_const_mul, ← integral_add i1 (i2.const_mul _)]
      congr 1; funext x; simp only [ψ]; ring
    have h1 := (htest _ (hφr j)).add ((htest _ (hφi j)).const_mul Complex.I)
    rw [hset _ (hφr j), hset _ (hφi j)] at h1
    simp only [hset _ (hφr j), hset _ (hφi j)] at h1
    rw [hint _ hW₀]
    exact h1.congr fun n => (hint _ (hW n)).symm
  set c : ℕ → ℝ := fun j => 2 / ((j : ℝ) + 1) * (max B 0 + (eLpNorm W₀ 2 μΩ).toReal)
  have hc : Tendsto c atTop (𝓝 0) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)).mul_const
      (max B 0 + (eLpNorm W₀ 2 μΩ).toReal)
    refine (by simpa using h : Tendsto (fun j : ℕ => 2 * (1 / ((j : ℝ) + 1)) *
      (max B 0 + (eLpNorm W₀ 2 μΩ).toReal)) atTop (𝓝 0)).congr fun j => ?_
    simp only [c]; ring
  have hgW : ∀ w : (ι → ℝ) → ℂ, MemLp w 2 μΩ → ∀ j,
      ‖∫ x, g x * w x ∂μΩ - ∫ x, ψ j x * w x ∂μΩ‖ ≤
        2 / ((j : ℝ) + 1) * (eLpNorm w 2 μΩ).toReal := by
    intro w hw j
    rw [← integral_sub (f := fun x => g x * w x) (g := fun x => ψ j x * w x)
      (hg.integrable_mul hw) ((hψL2 j).integrable_mul hw)]
    have : (fun x => g x * w x - ψ j x * w x) = fun x => (g - ψ j) x * w x := by
      funext x; simp only [Pi.sub_apply]; ring
    rw [this]
    exact (norm_integral_mul_le (hg.sub (hψL2 j)) hw).trans
      (mul_le_mul_of_nonneg_right (herr j) ENNReal.toReal_nonneg)
  refine tendsto_of_approx hc hψconv (fun j n => ?_) (fun j => ?_)
  · refine (hgW _ (hW n) j).trans ?_
    simp only [c]
    gcongr
    exact ((hWB n).trans (le_max_left _ _)).trans (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  · refine (hgW _ hW₀ j).trans ?_
    simp only [c]
    gcongr
    exact le_add_of_nonneg_left (le_max_right _ _)

end Density

/-! ### The finite-net upgrade: uniform weak–strong pairings over Lipschitz test values -/

section FiniteNet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open SobolevOpen (box IsTest)

/-- The integer cell index `⌊x/δ⌋` of a point. -/
def cellIdx (δ : ℝ) (x : ι → ℝ) : ι → ℤ := fun i => ⌊x i / δ⌋

/-- The corner `δ ⌊x/δ⌋` of the cell containing `x`. -/
def cellPt (δ : ℝ) (m : ι → ℤ) : ι → ℝ := fun i => δ * m i

theorem norm_sub_cellPt_le {δ : ℝ} (hδ : 0 < δ) (x : ι → ℝ) :
    ‖x - cellPt δ (cellIdx δ x)‖ ≤ δ := by
  refine (pi_norm_le_iff_of_nonneg hδ.le).mpr fun i => ?_
  simp only [Pi.sub_apply, cellPt, cellIdx, Real.norm_eq_abs]
  have h1 := Int.floor_le (x i / δ)
  have h2 := Int.lt_floor_add_one (x i / δ)
  have h1' : δ * ⌊x i / δ⌋ ≤ x i := by
    have := mul_le_mul_of_nonneg_left h1 hδ.le
    rwa [mul_div_cancel₀ _ hδ.ne'] at this
  have h2' : x i < δ * ⌊x i / δ⌋ + δ := by
    have := mul_lt_mul_of_pos_left h2 hδ
    rw [mul_div_cancel₀ _ hδ.ne', mul_add, mul_one] at this
    exact this
  rw [abs_le]
  constructor <;> linarith

theorem measurable_cellIdx (δ : ℝ) : Measurable (cellIdx (ι := ι) δ) :=
  measurable_pi_lambda _ fun i => Int.measurable_floor.comp
    (by fun_prop : Measurable fun x : ι → ℝ => x i / δ)

/-- The finite set of cells meeting the box. -/
def boxCells (a b : ι → ℝ) (δ : ℝ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌊a i / δ⌋ ⌊b i / δ⌋

theorem cellIdx_mem_boxCells {a b : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) {x : ι → ℝ}
    (hx : x ∈ box a b) : cellIdx δ x ∈ boxCells a b δ := by
  refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · exact Int.floor_mono (div_le_div_of_nonneg_right (hx i (mem_univ i)).1.le hδ.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (hx i (mem_univ i)).2.le hδ.le)

/-- **Finite-net upgrade.**  Let `S_h → S` strongly in `L²(Q)` and `W_h ⇀ W` weakly in `L²(Q)`
(bounded, with convergent pairings against every `L²(Q)` function).  Then
`∫ S_h τ W_h → ∫ S τ W` **uniformly** over all continuous test values `τ` with `|τ| ≤ 1` and
Lipschitz constant `≤ L`. -/
theorem uniform_weak_strong {a b : ι → ℝ} {S : ℕ → (ι → ℝ) → ℂ} {S₀ : (ι → ℝ) → ℂ}
    (hS : RenewalGeometry.LpTendsto (volume.restrict (box a b)) 2 S S₀)
    {W : ℕ → (ι → ℝ) → ℂ} {W₀ : (ι → ℝ) → ℂ}
    (hW : ∀ n, MemLp (W n) 2 (volume.restrict (box a b)))
    (hW₀ : MemLp W₀ 2 (volume.restrict (box a b))) {B : ℝ}
    (hWB : ∀ n, (eLpNorm (W n) 2 (volume.restrict (box a b))).toReal ≤ B)
    (hweak : ∀ g : (ι → ℝ) → ℂ, MemLp g 2 (volume.restrict (box a b)) →
      Tendsto (fun n => ∫ x, g x * W n x ∂(volume.restrict (box a b))) atTop
        (𝓝 (∫ x, g x * W₀ x ∂(volume.restrict (box a b)))))
    (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ τ : (ι → ℝ) → ℂ, Continuous τ → (∀ x, ‖τ x‖ ≤ 1) →
      (∀ x y, ‖τ x - τ y‖ ≤ L * ‖x - y‖) →
      ‖∫ x, S n x * τ x * W n x ∂(volume.restrict (box a b)) -
        ∫ x, S₀ x * τ x * W₀ x ∂(volume.restrict (box a b))‖ ≤ ε := by
  set μΩ := volume.restrict (box a b)
  have hbox : MeasurableSet (box a b) := (SobolevOpen.isOpen_box a b).measurableSet
  set B' := max B 0
  set A₀ := (eLpNorm S₀ 2 μΩ).toReal
  set C₀ := (eLpNorm W₀ 2 μΩ).toReal
  set L' := max L 0
  have hWB' : ∀ n, (eLpNorm (W n) 2 μΩ).toReal ≤ B' := fun n => (hWB n).trans (le_max_left _ _)
  -- choice of the mesh
  set δ : ℝ := ε / (3 * (L' * A₀ * (B' + C₀) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδbound : L' * δ * A₀ * (B' + C₀) ≤ ε / 3 := by
    have hpos : 0 < 3 * (L' * A₀ * (B' + C₀) + 1) := by positivity
    have : L' * δ * A₀ * (B' + C₀) = (L' * A₀ * (B' + C₀)) * ε / (3 * (L' * A₀ * (B' + C₀) + 1)) := by
      simp only [δ]; ring
    have hX : 0 ≤ L' * A₀ * (B' + C₀) := by
      have : (0 : ℝ) ≤ A₀ := ENNReal.toReal_nonneg
      have : (0 : ℝ) ≤ C₀ := ENNReal.toReal_nonneg
      have : (0 : ℝ) ≤ L' := le_max_right _ _
      have : (0 : ℝ) ≤ B' := le_max_right _ _
      positivity
    rw [this, div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hX, hε]
  -- the cell functions
  set M := boxCells a b δ
  set cell : (ι → ℤ) → Set (ι → ℝ) := fun m => cellIdx δ ⁻¹' {m}
  have hcell : ∀ m, MeasurableSet (cell m) := fun m =>
    measurable_cellIdx δ (measurableSet_singleton m)
  set g : (ι → ℤ) → (ι → ℝ) → ℂ := fun m => (cell m).indicator S₀
  have hg : ∀ m, MemLp (g m) 2 μΩ := fun m => hS.memLp_lim.indicator (hcell m)
  -- term (i): strong convergence of `S`
  have hSt : Tendsto (fun n => (eLpNorm (S n - S₀) 2 μΩ).toReal * B') atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hS.tendsto
    simpa using this.mul_const B'
  -- term (ii): finitely many weak pairings
  have hcells : Tendsto (fun n => ∑ m ∈ M, ‖∫ x, g m x * W n x ∂μΩ - ∫ x, g m x * W₀ x ∂μΩ‖)
      atTop (𝓝 0) := by
    have := tendsto_finsetSum M fun m _ => ((hweak (g m) (hg m)).sub
      (tendsto_const_nhds (x := ∫ x, g m x * W₀ x ∂μΩ))).norm
    simpa using this
  filter_upwards [hSt.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε / 3)),
    hcells.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε / 3))] with n hn1 hn2
  intro τ hτc hτ1 hτL
  have hτm : AEStronglyMeasurable τ μΩ := hτc.aestronglyMeasurable
  have hτL2 : ∀ {f : (ι → ℝ) → ℂ}, MemLp f 2 μΩ → MemLp (fun x => f x * τ x) 2 μΩ := fun hf =>
    hf.of_le (hf.1.mul hτm) (Eventually.of_forall fun x => by
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hτ1 x))
  set τδ : (ι → ℝ) → ℂ := fun x => τ (cellPt δ (cellIdx δ x))
  have hτδ : ∀ x, ‖τ x - τδ x‖ ≤ L' * δ := fun x =>
    (hτL _ _).trans (by
      calc L * ‖x - cellPt δ (cellIdx δ x)‖ ≤ L' * ‖x - cellPt δ (cellIdx δ x)‖ := by
            gcongr; exact le_max_left _ _
        _ ≤ L' * δ := mul_le_mul_of_nonneg_left (norm_sub_cellPt_le hδ x) (le_max_right _ _))
  have hτδm : AEStronglyMeasurable τδ μΩ :=
    (hτc.measurable.comp ((measurable_of_countable (cellPt (ι := ι) δ)).comp
      (measurable_cellIdx δ))).aestronglyMeasurable
  have hS₀ := hS.memLp_lim
  have hWsub : MemLp (fun x => W n x - W₀ x) 2 μΩ := (hW n).sub hW₀
  have hWsubB : (eLpNorm (fun x => W n x - W₀ x) 2 μΩ).toReal ≤ B' + C₀ := by
    have h := eLpNorm_sub_le (hW n).1 hW₀.1 (p := 2) (by norm_num)
    refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(hW n).eLpNorm_ne_top,
      hW₀.eLpNorm_ne_top⟩) h).trans ?_
    rw [ENNReal.toReal_add (hW n).eLpNorm_ne_top hW₀.eLpNorm_ne_top]
    exact add_le_add (hWB' n) le_rfl
  -- (i) the strong factor
  have b1 : ‖∫ x, (S n x - S₀ x) * τ x * W n x ∂μΩ‖ ≤ ε / 3 := by
    have hm : MemLp (fun x => (S n x - S₀ x) * τ x) 2 μΩ := hτL2 ((hS.memLp n).sub hS₀)
    refine (norm_integral_mul_le hm (hW n)).trans (le_trans ?_ hn1)
    refine mul_le_mul ?_ (hWB' n) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    refine ENNReal.toReal_mono ((hS.memLp n).sub hS₀).eLpNorm_ne_top (eLpNorm_mono fun x => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hτ1 x)
  -- (ii) the mesh error
  have hmesh : eLpNorm (fun x => S₀ x * (τ x - τδ x)) 2 μΩ ≤
      ENNReal.ofReal (L' * δ) * eLpNorm S₀ 2 μΩ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hτδ x) (norm_nonneg _)
  have hmeshL : MemLp (fun x => S₀ x * (τ x - τδ x)) 2 μΩ :=
    ⟨hS₀.1.mul (hτm.sub hτδm), hmesh.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      hS₀.eLpNorm_lt_top)⟩
  have b2 : ‖∫ x, S₀ x * (τ x - τδ x) * (W n x - W₀ x) ∂μΩ‖ ≤ ε / 3 := by
    refine (norm_integral_mul_le hmeshL hWsub).trans (le_trans ?_ hδbound)
    have h1 : (eLpNorm (fun x => S₀ x * (τ x - τδ x)) 2 μΩ).toReal ≤ L' * δ * A₀ := by
      refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        hS₀.eLpNorm_ne_top) hmesh).trans (le_of_eq ?_)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    calc (eLpNorm (fun x => S₀ x * (τ x - τδ x)) 2 μΩ).toReal *
          (eLpNorm (fun x => W n x - W₀ x) 2 μΩ).toReal
        ≤ (L' * δ * A₀) * (B' + C₀) :=
          mul_le_mul h1 hWsubB ENNReal.toReal_nonneg (by positivity)
      _ = L' * δ * A₀ * (B' + C₀) := by ring
  -- (iii) the cell constants
  have hdecomp : ∀ᵐ x ∂μΩ, S₀ x * τδ x * (W n x - W₀ x) =
      ∑ m ∈ M, τ (cellPt δ m) * (g m x * W n x - g m x * W₀ x) := by
    filter_upwards [ae_restrict_mem hbox] with x hx
    rw [Finset.sum_eq_single (cellIdx δ x)]
    · simp only [g, cell, Set.indicator_of_mem (show x ∈ cellIdx δ ⁻¹' {cellIdx δ x} from rfl), τδ]
      ring
    · intro m _ hm
      have : x ∉ cell m := fun h => hm (h.symm ▸ rfl : m = cellIdx δ x) |>.elim
      simp [g, this]
    · intro h; exact absurd (cellIdx_mem_boxCells hδ hx) h
  have hgint : ∀ m, Integrable (fun x => g m x * W n x) μΩ := fun m => (hg m).integrable_mul (hW n)
  have hgint₀ : ∀ m, Integrable (fun x => g m x * W₀ x) μΩ := fun m => (hg m).integrable_mul hW₀
  have b3 : ‖∫ x, S₀ x * τδ x * (W n x - W₀ x) ∂μΩ‖ ≤ ε / 3 := by
    rw [integral_congr_ae hdecomp, integral_finsetSum (f := fun m x => τ (cellPt δ m) *
      (g m x * W n x - g m x * W₀ x)) _ (fun m _ => ((hgint m).sub (hgint₀ m)).const_mul _)]
    refine (norm_sum_le _ _).trans (le_trans ?_ hn2)
    refine Finset.sum_le_sum fun m _ => ?_
    rw [integral_const_mul, norm_mul, integral_sub (hgint m) (hgint₀ m)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hτ1 _)
  -- assembly
  have hint1 : Integrable (fun x => S n x * τ x * W n x) μΩ := (hτL2 (hS.memLp n)).integrable_mul (hW n)
  have hint2 : Integrable (fun x => S₀ x * τ x * W₀ x) μΩ := (hτL2 hS₀).integrable_mul hW₀
  have hint3 : Integrable (fun x => (S n x - S₀ x) * τ x * W n x) μΩ :=
    (hτL2 ((hS.memLp n).sub hS₀)).integrable_mul (hW n)
  have hint4 : Integrable (fun x => S₀ x * (τ x - τδ x) * (W n x - W₀ x)) μΩ :=
    hmeshL.integrable_mul hWsub
  have hτδL : MemLp (fun x => S₀ x * τδ x) 2 μΩ :=
    hS₀.of_le (hS₀.1.mul hτδm) (Eventually.of_forall fun x => by
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hτ1 _))
  have hint5 : Integrable (fun x => S₀ x * τδ x * (W n x - W₀ x)) μΩ := hτδL.integrable_mul hWsub
  have hsplit : ∫ x, S n x * τ x * W n x ∂μΩ - ∫ x, S₀ x * τ x * W₀ x ∂μΩ =
      ∫ x, (S n x - S₀ x) * τ x * W n x ∂μΩ +
        ∫ x, S₀ x * (τ x - τδ x) * (W n x - W₀ x) ∂μΩ +
          ∫ x, S₀ x * τδ x * (W n x - W₀ x) ∂μΩ := by
    calc ∫ x, S n x * τ x * W n x ∂μΩ - ∫ x, S₀ x * τ x * W₀ x ∂μΩ
        = ∫ x, (S n x * τ x * W n x - S₀ x * τ x * W₀ x) ∂μΩ := (integral_sub hint1 hint2).symm
      _ = ∫ x, (((S n x - S₀ x) * τ x * W n x + S₀ x * (τ x - τδ x) * (W n x - W₀ x)) +
            S₀ x * τδ x * (W n x - W₀ x)) ∂μΩ :=
          integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = ∫ x, ((S n x - S₀ x) * τ x * W n x + S₀ x * (τ x - τδ x) * (W n x - W₀ x)) ∂μΩ +
            ∫ x, S₀ x * τδ x * (W n x - W₀ x) ∂μΩ := integral_add (hint3.add hint4) hint5
      _ = _ := by rw [integral_add hint3 hint4]
  rw [hsplit]
  calc _ ≤ ‖∫ x, (S n x - S₀ x) * τ x * W n x ∂μΩ‖ +
        ‖∫ x, S₀ x * (τ x - τδ x) * (W n x - W₀ x) ∂μΩ‖ +
          ‖∫ x, S₀ x * τδ x * (W n x - W₀ x) ∂μΩ‖ := norm_add₃_le
    _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add b1 b2) b3
    _ = ε := by ring

end FiniteNet

/-! ### The finite-net upgrade for operator-valued strong factors -/

section FiniteNetVector

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open SobolevOpen (box IsTest)

variable {TV WV : Type*} [NormedAddCommGroup TV] [NormedSpace ℝ TV] [FiniteDimensional ℝ TV]
  [NormedAddCommGroup WV] [NormedSpace ℝ WV] [FiniteDimensional ℝ WV]

/-- Weak convergence in `L²(Q; WV)`: all pairings `∫ g ℓ(W_h)` with real `g ∈ L²(Q)` and real
linear functionals `ℓ` converge. -/
def WeakL2Tendsto (a b : ι → ℝ) (W : ℕ → (ι → ℝ) → WV) (W₀ : (ι → ℝ) → WV) : Prop :=
  ∀ ℓ : WV →L[ℝ] ℝ, ∀ g : (ι → ℝ) → ℝ, MemLp g 2 (volume.restrict (box a b)) →
    Tendsto (fun n => ∫ x, g x * ℓ (W n x) ∂(volume.restrict (box a b))) atTop
      (𝓝 (∫ x, g x * ℓ (W₀ x) ∂(volume.restrict (box a b))))

/-- Bilinear expansion in bases. -/
theorem bilin_basis_expand (Ω : TV →L[ℝ] WV →L[ℝ] ℝ) (t : TV) (w : WV) :
    Ω t w = ∑ j, ∑ k, (Module.finBasis ℝ TV).repr t j * (Module.finBasis ℝ WV).repr w k *
      Ω (Module.finBasis ℝ TV j) (Module.finBasis ℝ WV k) := by
  set bT := Module.finBasis ℝ TV
  set bW := Module.finBasis ℝ WV
  calc Ω t w = Ω (∑ j, bT.repr t j • bT j) w := by rw [bT.sum_repr]
    _ = ∑ j, bT.repr t j * Ω (bT j) w := by
        rw [map_sum, ContinuousLinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = ∑ j, bT.repr t j * Ω (bT j) (∑ k, bW.repr w k • bW k) := by rw [bW.sum_repr]
    _ = ∑ j, ∑ k, bT.repr t j * bW.repr w k * Ω (bT j) (bW k) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, smul_eq_mul]; ring

/-- A coordinate functional of a finite basis, as a continuous linear map. -/
def coordL {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (j : Fin (Module.finrank ℝ V)) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ V).coord j)

theorem coordL_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (j : Fin (Module.finrank ℝ V)) (v : V) : coordL j v = (Module.finBasis ℝ V).repr v j := rfl

/-- **Finite-net upgrade, operator version.**  If `Ω_h → Ω` strongly in `L²(Q)` (operator norm,
`Ω_h(x) : TV × WV → ℝ` bilinear) and `W_h ⇀ W` weakly in `L²(Q; WV)` with a uniform bound, then
`∫ Ω_h(τ, W_h) → ∫ Ω(τ, W)` uniformly over continuous test values `τ` with `‖τ‖ ≤ 1` and
Lipschitz constant `≤ L`. -/
theorem uniform_weak_strong_op {a b : ι → ℝ} {Ω : ℕ → (ι → ℝ) → TV →L[ℝ] WV →L[ℝ] ℝ}
    {Ω₀ : (ι → ℝ) → TV →L[ℝ] WV →L[ℝ] ℝ}
    (hΩ : RenewalGeometry.LpTendsto (volume.restrict (box a b)) 2 Ω Ω₀)
    {W : ℕ → (ι → ℝ) → WV} {W₀ : (ι → ℝ) → WV}
    (hW : ∀ n, MemLp (W n) 2 (volume.restrict (box a b)))
    (hW₀ : MemLp W₀ 2 (volume.restrict (box a b))) {B : ℝ}
    (hWB : ∀ n, (eLpNorm (W n) 2 (volume.restrict (box a b))).toReal ≤ B)
    (hweak : WeakL2Tendsto a b W W₀) (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ τ : (ι → ℝ) → TV, Continuous τ → (∀ x, ‖τ x‖ ≤ 1) →
      (∀ x y, ‖τ x - τ y‖ ≤ L * ‖x - y‖) →
      |∫ x, Ω n x (τ x) (W n x) ∂(volume.restrict (box a b)) -
        ∫ x, Ω₀ x (τ x) (W₀ x) ∂(volume.restrict (box a b))| ≤ ε := by
  set μΩ := volume.restrict (box a b)
  set nT := Module.finrank ℝ TV
  set nW := Module.finrank ℝ WV
  set bT := Module.finBasis ℝ TV
  set bW := Module.finBasis ℝ WV
  -- scaling constants for the coordinates of `τ`
  set c : Fin nT → ℝ := fun j => ‖coordL (V := TV) j‖ + 1
  have hc : ∀ j, 0 < c j := fun j => by positivity
  set N : ℝ := (nW : ℝ) * (∑ j, c j) + 1
  have hN : 0 < N := by positivity
  -- the scalar data
  set S : Fin nT → Fin nW → ℕ → (ι → ℝ) → ℂ := fun j k n x => ((Ω n x (bT j) (bW k) : ℝ) : ℂ)
  set S₀ : Fin nT → Fin nW → (ι → ℝ) → ℂ := fun j k x => ((Ω₀ x (bT j) (bW k) : ℝ) : ℂ)
  set w : Fin nW → ℕ → (ι → ℝ) → ℂ := fun k n x => ((coordL k (W n x) : ℝ) : ℂ)
  set w₀ : Fin nW → (ι → ℝ) → ℂ := fun k x => ((coordL k (W₀ x) : ℝ) : ℂ)
  have hS : ∀ j k, RenewalGeometry.LpTendsto μΩ 2 (S j k) (S₀ j k) := by
    intro j k
    have h1 : RenewalGeometry.LpTendsto μΩ 2 (fun n x => (Ω n x (bT j) (bW k) : ℝ))
        (fun x => Ω₀ x (bT j) (bW k)) := by
      let e : (TV →L[ℝ] WV →L[ℝ] ℝ) →L[ℝ] ℝ :=
        (ContinuousLinearMap.apply ℝ ℝ (bW k)).comp (ContinuousLinearMap.apply ℝ _ (bT j))
      have := LpProductContinuity.LpTendsto.coeff (p := 2) (by norm_num)
        (β := fun _ _ => e) (β' := fun _ => e) (K := ‖e‖) (fun _ => aestronglyMeasurable_const)
        (by intro δ hδ; simp [edist_self, not_le.2 hδ]) (fun _ => Eventually.of_forall
          fun _ => le_rfl) hΩ
      exact this
    refine ⟨fun n => (h1.memLp n).ofReal, h1.memLp_lim.ofReal, ?_⟩
    refine h1.tendsto.congr fun n => eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    simp only [S, S₀, Pi.sub_apply]
    rw [← Complex.ofReal_sub, Complex.norm_real]
  have hwm : ∀ k n, MemLp (w k n) 2 μΩ := fun k n => ((coordL k).comp_memLp' (hW n)).ofReal
  have hwm₀ : ∀ k, MemLp (w₀ k) 2 μΩ := fun k => ((coordL k).comp_memLp' hW₀).ofReal
  set Bk : Fin nW → ℝ := fun k => ‖coordL (V := WV) k‖ * max B 0
  have hwB : ∀ k n, (eLpNorm (w k n) 2 μΩ).toReal ≤ Bk k := by
    intro k n
    have h1 : eLpNorm (w k n) 2 μΩ ≤ ENNReal.ofReal ‖coordL (V := WV) k‖ * eLpNorm (W n) 2 μΩ := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
      simp only [w, Complex.norm_real]
      exact (coordL k).le_opNorm _
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hW n).eLpNorm_ne_top) h1).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left ((hWB n).trans (le_max_left _ _)) (norm_nonneg _)
  have hwweak : ∀ k (g : (ι → ℝ) → ℂ), MemLp g 2 μΩ →
      Tendsto (fun n => ∫ x, g x * w k n x ∂μΩ) atTop (𝓝 (∫ x, g x * w₀ k x ∂μΩ)) := by
    intro k g hg
    have hre := hweak (coordL k) (fun x => (g x).re) hg.re
    have him := hweak (coordL k) (fun x => (g x).im) hg.im
    have key : ∀ (v : (ι → ℝ) → WV), MemLp v 2 μΩ →
        ∫ x, g x * ((coordL k (v x) : ℝ) : ℂ) ∂μΩ =
          ((∫ x, (g x).re * coordL k (v x) ∂μΩ : ℝ) : ℂ) +
            Complex.I * ((∫ x, (g x).im * coordL k (v x) ∂μΩ : ℝ) : ℂ) := by
      intro v hv
      have hcv : MemLp (fun x => coordL k (v x)) 2 μΩ := (coordL k).comp_memLp' hv
      have i1 : Integrable (fun x => (g x).re * coordL k (v x)) μΩ := hg.re.integrable_mul hcv
      have i2 : Integrable (fun x => (g x).im * coordL k (v x)) μΩ := hg.im.integrable_mul hcv
      rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_const_mul,
        ← integral_add i1.ofReal (i2.ofReal.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      conv_lhs => rw [← Complex.re_add_im (g x)]
      push_cast; ring
    simp only [w, w₀]
    rw [key _ hW₀]
    refine Tendsto.congr (fun n => (key _ (hW n)).symm) ?_
    exact ((Complex.continuous_ofReal.tendsto _).comp hre).add
      (((Complex.continuous_ofReal.tendsto _).comp him).const_mul _)
  -- apply the scalar lemma to every pair of coordinates
  have hev : ∀ j k, ∀ᶠ n in atTop, ∀ τ : (ι → ℝ) → ℂ, Continuous τ → (∀ x, ‖τ x‖ ≤ 1) →
      (∀ x y, ‖τ x - τ y‖ ≤ L * ‖x - y‖) →
      ‖∫ x, S j k n x * τ x * w k n x ∂μΩ - ∫ x, S₀ j k x * τ x * w₀ k x ∂μΩ‖ ≤ ε / N :=
    fun j k => uniform_weak_strong (hS j k) (hwm k) (hwm₀ k) (hwB k) (hwweak k) L
      (div_pos hε hN)
  filter_upwards [eventually_all.mpr fun j => eventually_all.mpr fun k => hev j k] with n hn
  intro τ hτc hτ1 hτL
  -- the scaled coordinates of the test value
  set τj : Fin nT → (ι → ℝ) → ℂ := fun j x => ((coordL j (τ x) / c j : ℝ) : ℂ)
  have hτjc : ∀ j, Continuous (τj j) := fun j =>
    Complex.continuous_ofReal.comp (((coordL j).continuous.comp hτc).div_const _)
  have hτj1 : ∀ j x, ‖τj j x‖ ≤ 1 := fun j x => by
    simp only [τj, Complex.norm_real, norm_div, Real.norm_eq_abs, abs_of_pos (hc j)]
    rw [div_le_one (hc j), ← Real.norm_eq_abs]
    exact ((coordL j).le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) (hτ1 x)).trans
      (le_add_of_nonneg_right zero_le_one))
  have hτjL : ∀ j x y, ‖τj j x - τj j y‖ ≤ L * ‖x - y‖ := fun j x y => by
    simp only [τj, ← Complex.ofReal_sub, Complex.norm_real, ← sub_div, norm_div,
      Real.norm_eq_abs (c j), abs_of_pos (hc j), ← map_sub]
    rw [div_le_iff₀ (hc j)]
    calc ‖coordL j (τ x - τ y)‖ ≤ ‖coordL (V := TV) j‖ * ‖τ x - τ y‖ := (coordL j).le_opNorm _
      _ ≤ c j * (L * ‖x - y‖) := mul_le_mul (le_add_of_nonneg_right zero_le_one) (hτL x y)
          (norm_nonneg _) (hc j).le
      _ = L * ‖x - y‖ * c j := by ring
  -- the expansion in coordinates
  have hexp : ∀ (Ω' : (ι → ℝ) → TV →L[ℝ] WV →L[ℝ] ℝ) (W' : (ι → ℝ) → WV) (x : ι → ℝ),
      Ω' x (τ x) (W' x) = ∑ j, ∑ k, c j * (((Ω' x (bT j) (bW k) : ℝ) : ℂ) * τj j x *
        ((coordL k (W' x) : ℝ) : ℂ)).re := by
    intro Ω' W' x
    rw [bilin_basis_expand]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [τj, ← Complex.ofReal_mul, Complex.ofReal_re, coordL_apply]
    field_simp [(hc j).ne']
    ring
  have hintS : ∀ j k (Ω' : (ι → ℝ) → TV →L[ℝ] WV →L[ℝ] ℝ) (W' : (ι → ℝ) → WV),
      MemLp (fun x => ((Ω' x (bT j) (bW k) : ℝ) : ℂ)) 2 μΩ → MemLp W' 2 μΩ →
      Integrable (fun x => ((Ω' x (bT j) (bW k) : ℝ) : ℂ) * τj j x *
        ((coordL k (W' x) : ℝ) : ℂ)) μΩ := by
    intro j k Ω' W' hΩ' hW'
    have h1 : MemLp (fun x => ((Ω' x (bT j) (bW k) : ℝ) : ℂ) * τj j x) 2 μΩ :=
      hΩ'.of_le (hΩ'.1.mul (hτjc j).aestronglyMeasurable) (Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hτj1 j x))
    exact h1.integrable_mul ((coordL k).comp_memLp' hW').ofReal
  have hintegral : ∀ (Ω' : (ι → ℝ) → TV →L[ℝ] WV →L[ℝ] ℝ) (W' : (ι → ℝ) → WV),
      (∀ j k, MemLp (fun x => ((Ω' x (bT j) (bW k) : ℝ) : ℂ)) 2 μΩ) → MemLp W' 2 μΩ →
      ∫ x, Ω' x (τ x) (W' x) ∂μΩ = ∑ j, ∑ k, c j * (∫ x, ((Ω' x (bT j) (bW k) : ℝ) : ℂ) *
        τj j x * ((coordL k (W' x) : ℝ) : ℂ) ∂μΩ).re := by
    intro Ω' W' hΩ' hW'
    simp_rw [hexp Ω' W']
    have hI : ∀ j k, Integrable (fun x => c j * (((Ω' x (bT j) (bW k) : ℝ) : ℂ) * τj j x *
        ((coordL k (W' x) : ℝ) : ℂ)).re) μΩ := fun j k =>
      ((hintS j k Ω' W' (hΩ' j k) hW').re).const_mul _
    rw [integral_finsetSum (f := fun j x => ∑ k, c j * (((Ω' x (bT j) (bW k) : ℝ) : ℂ) *
      τj j x * ((coordL k (W' x) : ℝ) : ℂ)).re) _ fun j _ => integrable_finsetSum _ fun k _ =>
        hI j k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum (f := fun k x => c j * (((Ω' x (bT j) (bW k) : ℝ) : ℂ) *
      τj j x * ((coordL k (W' x) : ℝ) : ℂ)).re) _ fun k _ => hI j k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    exact integral_re (hintS j k Ω' W' (hΩ' j k) hW')
  rw [hintegral _ _ (fun j k => (hS j k).memLp n) (hW n),
    hintegral _ _ (fun j k => (hS j k).memLp_lim) hW₀, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |∑ k, c j * (∫ x, S j k n x * τj j x * w k n x ∂μΩ).re -
        ∑ k, c j * (∫ x, S₀ j k x * τj j x * w₀ k x ∂μΩ).re|
      ≤ ∑ j, ∑ k, c j * (ε / N) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [← mul_sub, abs_mul, abs_of_pos (hc j), ← Complex.sub_re]
        exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
          (hn j k (τj j) (hτjc j) (hτj1 j) (hτjL j))) (hc j).le
    _ = (nW : ℝ) * (∑ j, c j) * (ε / N) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hN]
        have : 0 ≤ (nW : ℝ) * (∑ j, c j) := by positivity
        nlinarith

end FiniteNetVector

/-! ### Coefficient–multilinear convergence -/

section Coefficients

variable [IsFiniteMeasure μ] {Z : Type*} [NormedAddCommGroup Z]
variable {V₁ V₂ V₃ W : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂]
  [NormedSpace ℝ V₂] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **Coefficient times one factor.**  `Φ` continuous on a compact `K`, `z_h, z ∈ K` a.e.,
`z_h → z` in measure, `y_h → y` in `L^p` (`1 ≤ p < ∞`): `Φ(z_h) y_h → Φ(z) y` in `L^p`. -/
theorem tendsto_coeff_apply {K : Set Z} (hK : IsCompact K) {Φ : Z → V₁ →L[ℝ] W}
    (hΦ : ContinuousOn Φ K) {z : ℕ → X → Z} {z₀ : X → Z} (hin : ∀ n, ∀ᵐ x ∂μ, z n x ∈ K)
    (hin₀ : ∀ᵐ x ∂μ, z₀ x ∈ K) (hz : TendstoInMeasure μ z atTop z₀)
    (hΦm : ∀ n, AEStronglyMeasurable (fun x => Φ (z n x)) μ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {y : ℕ → X → V₁} {y₀ : X → V₁} (hy : RenewalGeometry.LpTendsto μ p y y₀) :
    RenewalGeometry.LpTendsto μ p (fun n x => Φ (z n x) (y n x)) (fun x => Φ (z₀ x) (y₀ x)) := by
  obtain ⟨⟨M, hM⟩, -⟩ := LpProductContinuity.LpTendsto.comp_of_continuousOn (p := 2) (by norm_num)
    hK hΦ hin hin₀ hz hΦm
  exact LpProductContinuity.LpTendsto.coeff hp hΦm
    (LpProductContinuity.tendstoInMeasure_comp_of_continuousOn hK hΦ hin hin₀ hz) hM hy

/-- **Coefficient times two factors** (Hölder exponents `1/p + 1/q = 1/r`). -/
theorem tendsto_coeff_bilin {K : Set Z} (hK : IsCompact K) {Φ : Z → V₁ →L[ℝ] V₂ →L[ℝ] W}
    (hΦ : ContinuousOn Φ K) {z : ℕ → X → Z} {z₀ : X → Z} (hin : ∀ n, ∀ᵐ x ∂μ, z n x ∈ K)
    (hin₀ : ∀ᵐ x ∂μ, z₀ x ∈ K) (hz : TendstoInMeasure μ z atTop z₀)
    (hΦm : ∀ n, AEStronglyMeasurable (fun x => Φ (z n x)) μ) {p q r : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] [Fact (1 ≤ r)] [ENNReal.HolderTriple p q r] (hp : p ≠ ⊤)
    {y₁ : ℕ → X → V₁} {y₁₀ : X → V₁} (hy₁ : RenewalGeometry.LpTendsto μ p y₁ y₁₀)
    {y₂ : ℕ → X → V₂} {y₂₀ : X → V₂} (hy₂ : RenewalGeometry.LpTendsto μ q y₂ y₂₀) :
    RenewalGeometry.LpTendsto μ r (fun n x => Φ (z n x) (y₁ n x) (y₂ n x))
      (fun x => Φ (z₀ x) (y₁₀ x) (y₂₀ x)) := by
  have h1 := tendsto_coeff_apply hK hΦ hin hin₀ hz hΦm hp hy₁
  have := RenewalGeometry.LpTendsto.bilin (p := p) (q := q) (r := r)
    (ContinuousLinearMap.id ℝ (V₂ →L[ℝ] W)) h1 hy₂
  simpa using this

/-- **Coefficient times three factors at the critical exponents** `(2, 4, 4)`. -/
theorem tendsto_coeff_trilin_critical {K : Set Z} (hK : IsCompact K)
    {Φ : Z → V₁ →L[ℝ] V₂ →L[ℝ] V₃ →L[ℝ] W} (hΦ : ContinuousOn Φ K) {z : ℕ → X → Z}
    {z₀ : X → Z} (hin : ∀ n, ∀ᵐ x ∂μ, z n x ∈ K) (hin₀ : ∀ᵐ x ∂μ, z₀ x ∈ K)
    (hz : TendstoInMeasure μ z atTop z₀) (hΦm : ∀ n, AEStronglyMeasurable (fun x => Φ (z n x)) μ)
    {y₁ : ℕ → X → V₁} {y₁₀ : X → V₁} (hy₁ : RenewalGeometry.LpTendsto μ 2 y₁ y₁₀)
    {y₂ : ℕ → X → V₂} {y₂₀ : X → V₂} (hy₂ : RenewalGeometry.LpTendsto μ 2 y₂ y₂₀)
    {y₃ : ℕ → X → V₃} {y₃₀ : X → V₃} (hy₃ : RenewalGeometry.LpTendsto μ 2 y₃ y₃₀)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hy₂4 : ∀ n, eLpNorm (y₂ n) 4 μ ≤ M)
    (hy₃4 : ∀ n, eLpNorm (y₃ n) 4 μ ≤ M) :
    RenewalGeometry.LpTendsto μ 1 (fun n x => Φ (z n x) (y₁ n x) (y₂ n x) (y₃ n x))
      (fun x => Φ (z₀ x) (y₁₀ x) (y₂₀ x) (y₃₀ x)) := by
  have h1 := tendsto_coeff_apply hK hΦ hin hin₀ hz hΦm (by norm_num) hy₁
  exact tendsto_trilin_critical (ContinuousLinearMap.id ℝ (V₂ →L[ℝ] V₃ →L[ℝ] W)) h1 hy₂ hy₃ hM
    hy₂4 hy₃4

/-- Composition with a fixed continuous linear map preserves strong convergence. -/
theorem LpTendsto.clm_comp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (L : V₁ →L[ℝ] V₂)
    {y : ℕ → X → V₁} {y₀ : X → V₁} (hy : RenewalGeometry.LpTendsto μ p y y₀) :
    RenewalGeometry.LpTendsto μ p (fun n x => L (y n x)) (fun x => L (y₀ x)) :=
  LpProductContinuity.LpTendsto.coeff hp (β := fun _ _ => L) (β' := fun _ => L) (K := ‖L‖)
    (fun _ => aestronglyMeasurable_const) (by intro δ hδ; simp [edist_self, not_le.2 hδ])
    (fun _ => Eventually.of_forall fun _ => le_rfl) hy

end Coefficients

/-- **Uniform dual estimate from `L¹` operator convergence.** -/
theorem uniform_of_L1_op {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {Λ : ℕ → X → T →L[ℝ] ℝ} {Λ₀ : X → T →L[ℝ] ℝ} (hΛ : RenewalGeometry.LpTendsto μ 1 Λ Λ₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ τ : X → T, AEStronglyMeasurable τ μ → (∀ᵐ x ∂μ, ‖τ x‖ ≤ 1) →
      |∫ x, Λ n x (τ x) ∂μ - ∫ x, Λ₀ x (τ x) ∂μ| ≤ ε := by
  have hT := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hΛ.tendsto
  simp only [ENNReal.toReal_zero] at hT
  filter_upwards [hT.eventually (ge_mem_nhds hε)] with n hn
  intro τ hτ hτ1
  have h := abs_integral_sub_le_of_opNorm (memLp_one_iff_integrable.mp (hΛ.memLp n))
    (memLp_one_iff_integrable.mp hΛ.memLp_lim) hτ hτ1
  refine h.trans ?_
  rw [one_mul]
  refine le_trans (le_of_eq ?_) hn
  rw [Function.comp_apply, eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
    (((hΛ.memLp n).1.sub hΛ.memLp_lim.1))]
  rfl

/-! ### Further closure properties of strong convergence -/

section MoreClosure

variable {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

/-- Scalar sequences times strongly convergent sequences. -/
theorem LpTendsto.smul_seq {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) {f : ℕ → X → V₁} {f₀ : X → V₁}
    (hf : RenewalGeometry.LpTendsto μ p f f₀) :
    RenewalGeometry.LpTendsto μ p (fun n x => c n • f n x) (fun x => c₀ • f₀ x) := by
  refine ⟨fun n => (hf.memLp n).const_smul _, hf.memLp_lim.const_smul _, ?_⟩
  have hb : ∀ n, eLpNorm ((fun x => c n • f n x) - fun x => c₀ • f₀ x) p μ ≤
      ‖c n‖ₑ * eLpNorm (f n - f₀) p μ + ‖c n - c₀‖ₑ * eLpNorm f₀ p μ := by
    intro n
    have hsplit : ((fun x => c n • f n x) - fun x => c₀ • f₀ x) =
        c n • (f n - f₀) + (c n - c₀) • f₀ := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_sub, sub_smul]; abel
    rw [hsplit]
    refine (eLpNorm_add_le (((hf.memLp n).1.sub hf.memLp_lim.1).const_smul _)
      (hf.memLp_lim.1.const_smul _) Fact.out).trans ?_
    rw [eLpNorm_const_smul, eLpNorm_const_smul]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
  have h1 : Tendsto (fun n => ‖c n‖ₑ) atTop (𝓝 ‖c₀‖ₑ) :=
    (continuous_enorm.tendsto _).comp hc
  have h2 : Tendsto (fun n => ‖c n - c₀‖ₑ) atTop (𝓝 0) := by
    have := (continuous_enorm.tendsto (0 : ℝ)).comp (by simpa using hc.sub_const c₀ :
      Tendsto (fun n => c n - c₀) atTop (𝓝 0))
    simpa [Function.comp_def] using this
  have := (ENNReal.Tendsto.mul h1 (Or.inr ENNReal.zero_ne_top) hf.tendsto
    (Or.inr enorm_ne_top)).add
    (ENNReal.Tendsto.mul_const h2 (Or.inr hf.memLp_lim.eLpNorm_ne_top))
  simpa using this

/-- Constant functions with convergent values converge in every `L^p` of a finite measure. -/
theorem LpTendsto.const_seq [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℕ → V₁} {c₀ : V₁}
    (hc : Tendsto c atTop (𝓝 c₀)) :
    RenewalGeometry.LpTendsto μ p (fun n (_ : X) => c n) (fun _ => c₀) := by
  refine ⟨fun n => memLp_const _, memLp_const _, ?_⟩
  have hb : ∀ n, eLpNorm ((fun _ : X => c n) - fun _ => c₀) p μ ≤
      ENNReal.ofReal ‖c n - c₀‖ * eLpNorm (fun _ : X => (1 : ℝ)) p μ := fun n =>
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => by simp) p
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
  have h1 : Tendsto (fun n => ENNReal.ofReal ‖c n - c₀‖) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => c n - c₀) atTop (𝓝 0) := by simpa using hc.sub_const c₀
    have := (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_norm.tendsto _).comp h0)
    simpa [Function.comp_def] using this
  simpa using ENNReal.Tendsto.mul_const h1 (Or.inr (memLp_const (1 : ℝ)).eLpNorm_ne_top)

/-- Finite sums of strongly convergent sequences. -/
theorem LpTendsto.finset_sum {ι' : Type*} (s : Finset ι') {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : ι' → ℕ → X → V₁} {f₀ : ι' → X → V₁}
    (hf : ∀ i ∈ s, RenewalGeometry.LpTendsto μ p (f i) (f₀ i)) :
    RenewalGeometry.LpTendsto μ p (fun n x => ∑ i ∈ s, f i n x) (fun x => ∑ i ∈ s, f₀ i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using RenewalGeometry.LpTendsto.const (ν := μ) (p := p) (u := fun _ : X => (0 : V₁))
      MemLp.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have h1 := hf i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    exact h1.add h2

end MoreClosure

end RenewalGeometry.FirstVariationCalculus
