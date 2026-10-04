/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeYangMillsIdentification
import RenewalGeometry.GaugeTheory.PlaquetteLogDerivative
import RenewalGeometry.OperatorLimits.VariableTorusDiracEstimates

/-!
# The literal first variation of the logarithmic curvature (`eq:native-YM-variation`)
  (second assertion of `prop:native-YM-identification`, Einstein–SM action closure)

Setting: as in `Continuum/NativeYangMillsIdentification.lean` (unit-torus rendering of the
paper's periodic box, grid `(ℤ/N)⁴`, mesh `h = 1/N`, links `e^{hA_μ(x)}`, literal curvature
`F^h_{μν} = h⁻² Log(U_μ(x) U_ν(x+e_μ) U_μ(x+e_ν)⁻¹ U_ν(x)⁻¹)` = `curvLog`), with the gauge
potentials in a complete normed **complex** algebra `𝔸` with `‖1‖ = 1` (the compact gauge Lie
algebras are real subspaces of complex matrix algebras; complex scalars are used only to apply
Cauchy's estimate to the analytic plaquette remainder).

* `curvVar N A w = d/dt F^h(A + t w)|_{t=0}` — the literal first variation `D_A F_h[w]`.
* `hasDerivAt_curvLog`, `norm_curvVar_sub_le` (**the analytic expansion after one physical
  variation**): on the chart `h |W(A)| ≤ 1/32`,
  `D_A F_h[w] = (D⁺_μ w_ν - D⁺_ν w_μ) + D(½ Σ_{i<j}[W_i, W_j])[W(w)] + O(h |W(A)|² |W(w)|)`
  with the explicit constant `48` (Cauchy estimate `PlaquetteLogDerivative.norm_deriv_bchRem_le`
  for the BCH remainder).
* `C1Test`: gauge tests `a_ν ∈ C(𝕋⁴, 𝔸)` with continuous partial derivatives `∂_μ a_ν`
  (every smooth test is one); `sampleTest N a = 𝒮_h a`.
* `native_YM_variation` (**`eq:native-YM-variation`**): if `R_h^0 A_h → A` strongly in `L⁴`, then
  for every `C¹` gauge test `a`, `R_h^0 (D_A F_h[𝒮_h a]) → da + [A, a]` strongly in `L²`, i.e.
  `(D_A F_h[𝒮_h a])_{μν} → ∂_μ a_ν - ∂_ν a_μ + [A_μ, a_ν] + [a_μ, A_ν]`.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.NativeYMVariation

open TorusTrigReconstruction NativeCriticalGrid TorusPiecewiseConstantTranslation LogBCH
  NativeYMIdentification PlaquetteLogDerivative

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)


/-! ### The literal first variation and its expansion -/

section Variation

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {N : ℕ}

/-- **The literal first variation** `D_A F_h[w] = d/dt F^h(A + t w)|_{t=0}` of the logarithmic
plaquette curvature. -/
def curvVar (N : ℕ) (A w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) : 𝔸 :=
  deriv (fun t : ℝ => curvLog N (A + t • w) x μ ν) 0

theorem lineList_ofReal (L W : List 𝔸) (t : ℝ) : lineList L W (t : ℂ) = lineListR L W t := by
  simp only [lineList, lineListR, real_smul_eq]

theorem slots_scaled_add (A w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) (t : ℝ) :
    (slots (A + t • w) x μ ν).map (fun v => (N : ℝ)⁻¹ • v) =
      lineListR ((slots A x μ ν).map fun v => (N : ℝ)⁻¹ • v)
        ((slots w x μ ν).map fun v => (N : ℝ)⁻¹ • v) t := by
  simp only [slots, List.map_cons, List.map_nil, lineListR, List.zipWith_cons_cons,
    List.zipWith_nil_right, Pi.add_apply, Pi.smul_apply, smul_add, smul_neg, neg_add,
    smul_comm (N : ℝ)⁻¹ t, smul_neg]

theorem length_scaled_slots (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    ((slots A x μ ν).map fun v => (N : ℝ)⁻¹ • v).length = 4 := by
  simp [slots]

theorem logOnePlus_expProd_eq (L : List 𝔸) :
    logOnePlus (expProd L - 1) = L.sum + commTerm L + bchRem L := by
  rw [bchRem]; abel

/-- **The analytic expansion after one physical variation** (`eq:native-YM-variation`, pointwise):
on the scaled chart `h Σ|W(A)| ≤ 1/32`, `t ↦ F^h(A + t w)` is differentiable at `0` with
derivative `(D⁺_μ w_ν - D⁺_ν w_μ) + D(½Σ[W_i,W_j])(W(A))[W(w)] + R`, `‖R‖ ≤ 48 h |W(A)|² |W(w)|`. -/
theorem hasDerivAt_curvLog [NeZero N] (A w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4)
    (hs : (N : ℝ)⁻¹ * normSum (slots A x μ ν) ≤ 1 / 32) :
    ∃ R : 𝔸, HasDerivAt (fun t : ℝ => curvLog N (A + t • w) x μ ν)
        (linCurl w x μ ν + commPol (slots A x μ ν) (slots w x μ ν) + R) 0 ∧
      ‖R‖ ≤ 48 * (N : ℝ)⁻¹ * normSum (slots A x μ ν) ^ 2 * normSum (slots w x μ ν) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨L', hL'def⟩ : ∃ L', L' = (slots A x μ ν).map fun v => (N : ℝ)⁻¹ • v := ⟨_, rfl⟩
  obtain ⟨W', hW'def⟩ : ∃ W', W' = (slots w x μ ν).map fun v => (N : ℝ)⁻¹ • v := ⟨_, rfl⟩
  have hlen : L'.length = W'.length := by
    rw [hL'def, hW'def, length_scaled_slots, length_scaled_slots]
  have hL' : normSum L' ≤ 1 / 32 := by
    rw [hL'def, normSum_map_smul, abs_of_pos (inv_pos.2 hN)]; exact hs
  set D := deriv (fun z => bchRem (lineList L' W' z)) 0
  have hD := (norm_deriv_bchRem_le L' W' hL').2
  have hDr := hasDerivAt_real_bchRem L' W' hL'
  simp_rw [lineList_ofReal] at hDr
  -- the function
  have hf : (fun t : ℝ => curvLog N (A + t • w) x μ ν) = fun t : ℝ =>
      ((N : ℝ) ^ 2) • ((lineListR L' W' t).sum + commTerm (lineListR L' W' t) +
        bchRem (lineListR L' W' t)) := by
    funext t
    rw [curvLog, slots_scaled_add, logOnePlus_expProd_eq, ← hL'def, ← hW'def]
  have hder := (((hasDerivAt_sum_lineListR L' W' hlen).add
    (hasDerivAt_commTerm_lineListR L' W' hlen)).add hDr).const_smul ((N : ℝ) ^ 2)
  refine ⟨((N : ℝ) ^ 2) • D, ?_, ?_⟩
  · rw [hf]
    refine hder.congr_deriv ?_
    have e1 : ((N : ℝ) ^ 2) • W'.sum = linCurl w x μ ν := by
      rw [hW'def, sum_map_smul', smul_smul, show (N : ℝ) ^ 2 * (N : ℝ)⁻¹ = N by field_simp,
        slots_sum]
    have e2 : ((N : ℝ) ^ 2) • commPol L' W' = commPol (slots A x μ ν) (slots w x μ ν) := by
      rw [hL'def, hW'def, commPol_map_smul, smul_smul,
        show (N : ℝ) ^ 2 * (N : ℝ)⁻¹ ^ 2 = 1 by field_simp, one_smul]
    rw [smul_add, smul_add, e1, e2]
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hW' : normSum W' = (N : ℝ)⁻¹ * normSum (slots w x μ ν) := by
      rw [hW'def, normSum_map_smul, abs_of_pos (inv_pos.2 hN)]
    have hL'' : normSum L' = (N : ℝ)⁻¹ * normSum (slots A x μ ν) := by
      rw [hL'def, normSum_map_smul, abs_of_pos (inv_pos.2 hN)]
    rw [hW', hL''] at hD
    calc (N : ℝ) ^ 2 * ‖D‖ ≤ (N : ℝ) ^ 2 * (48 * ((N : ℝ)⁻¹ * normSum (slots A x μ ν)) ^ 2 *
          ((N : ℝ)⁻¹ * normSum (slots w x μ ν))) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = 48 * (N : ℝ)⁻¹ * normSum (slots A x μ ν) ^ 2 * normSum (slots w x μ ν) := by
          field_simp

/-- The expansion of `D_A F_h[w]` with its remainder bound. -/
theorem norm_curvVar_sub_le [NeZero N] (A w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4)
    (hs : (N : ℝ)⁻¹ * normSum (slots A x μ ν) ≤ 1 / 32) :
    ‖curvVar N A w x μ ν - linCurl w x μ ν - commPol (slots A x μ ν) (slots w x μ ν)‖ ≤
      48 * (N : ℝ)⁻¹ * normSum (slots A x μ ν) ^ 2 * normSum (slots w x μ ν) := by
  obtain ⟨R, hR, hRb⟩ := hasDerivAt_curvLog A w x μ ν hs
  rw [curvVar, hR.deriv]
  convert hRb using 2
  abel

end Variation

/-! ### `C¹` gauge tests and their samples -/

section Tests

variable {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]

/-- A `C¹` gauge test one-form on `𝕋⁴`: continuous components `a_ν` with continuous partial
derivatives `∂_μ a_ν` (every smooth gauge test is one). -/
structure C1Test (𝔸 : Type*) [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸] where
  /-- The components `a_ν`. -/
  a : Fin 4 → C(UnitAddTorus (Fin 4), 𝔸)
  /-- The partial derivatives `da μ ν = ∂_μ a_ν`. -/
  da : Fin 4 → Fin 4 → C(UnitAddTorus (Fin 4), 𝔸)
  hasDerivAt : ∀ μ ν y, HasDerivAt (fun s : ℝ => a ν (y + KolmogorovRieszTorus.coordPt μ s))
    (da μ ν y) 0

/-- The nodal samples `𝒮_h a (x) = a(x/N)`. -/
def sampleTest (N : ℕ) (a : C1Test 𝔸) : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸 :=
  fun x ν => a.a ν (TorusCellEmbedding.samplePt x)

theorem coordPt_zero (μ : Fin 4) : KolmogorovRieszTorus.coordPt μ 0 = 0 := by
  simp [KolmogorovRieszTorus.coordPt]

theorem dist_add_coordPt_le (y : UnitAddTorus (Fin 4)) (μ : Fin 4) (s : ℝ) :
    dist (y + KolmogorovRieszTorus.coordPt μ s) y ≤ |s| :=
  VariableTorusDirac.dist_add_lineVec_le y μ s

theorem hasDerivAt_line (a : C1Test 𝔸) (μ ν : Fin 4) (y : UnitAddTorus (Fin 4)) (s : ℝ) :
    HasDerivAt (fun u : ℝ => a.a ν (y + KolmogorovRieszTorus.coordPt μ u))
      (a.da μ ν (y + KolmogorovRieszTorus.coordPt μ s)) s := by
  have h := a.hasDerivAt μ ν (y + KolmogorovRieszTorus.coordPt μ s)
  have h' : HasDerivAt (fun r : ℝ => a.a ν (y + KolmogorovRieszTorus.coordPt μ (s + r)))
      (a.da μ ν (y + KolmogorovRieszTorus.coordPt μ s)) (s - s) := by
    rw [sub_self]
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    simp only [add_assoc, TorusPiecewiseConstantTranslation.coordPt_add]
  have := h'.comp_sub_const s s
  simpa only [add_sub_cancel] using this

/-- **Uniform finite-difference consistency** of a `C¹` test along a coordinate line:
`‖N (a(y + e_μ/N) - a(y)) - ∂_μ a(y)‖ ≤ ε` for all `y` once `1/N < δ(ε)`. -/
theorem exists_fd_bound (a : C1Test 𝔸) (μ ν : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (s : ℝ), 0 < s → s < δ → ∀ y,
      ‖s⁻¹ • (a.a ν (y + KolmogorovRieszTorus.coordPt μ s) - a.a ν y) - a.da μ ν y‖ ≤ ε := by
  have huc := CompactSpace.uniformContinuous_of_continuous (a.da μ ν).continuous
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδ, hδε⟩ := huc ε hε
  refine ⟨δ, hδ, fun s hs0 hsδ y => ?_⟩
  set g : ℝ → 𝔸 := fun u => a.a ν (y + KolmogorovRieszTorus.coordPt μ u) - u • a.da μ ν y
  have hg : ∀ u ∈ Icc (0 : ℝ) s, HasDerivWithinAt g
      (a.da μ ν (y + KolmogorovRieszTorus.coordPt μ u) - a.da μ ν y) (Icc 0 s) u := by
    intro u _
    have := (hasDerivAt_line a μ ν y u).sub ((hasDerivAt_id u).smul_const (a.da μ ν y))
    exact (this.congr_deriv (by simp)).hasDerivWithinAt
  have hb : ∀ u ∈ Ico (0 : ℝ) s,
      ‖a.da μ ν (y + KolmogorovRieszTorus.coordPt μ u) - a.da μ ν y‖ ≤ ε := by
    intro u hu
    have hd : dist (y + KolmogorovRieszTorus.coordPt μ u) y < δ := by
      refine (dist_add_coordPt_le y μ u).trans_lt ?_
      rw [abs_of_nonneg hu.1]; linarith [hu.2]
    have := hδε hd
    rw [dist_eq_norm] at this
    exact this.le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hg hb s ⟨hs0.le, le_rfl⟩
  have e : s⁻¹ • (a.a ν (y + KolmogorovRieszTorus.coordPt μ s) - a.a ν y) - a.da μ ν y =
      s⁻¹ • (g s - g 0) := by
    simp only [g, coordPt_zero, add_zero, zero_smul, sub_zero, smul_sub, smul_smul,
      inv_mul_cancel₀ hs0.ne', one_smul]
    abel
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs0.le)]
  calc s⁻¹ * ‖g s - g 0‖ ≤ s⁻¹ * (ε * (s - 0)) := mul_le_mul_of_nonneg_left hmv (by positivity)
    _ = ε := by rw [sub_zero]; field_simp

end Tests

/-! ### Uniform convergence gives strong `L^p` convergence on `𝕋⁴` -/

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem memLp_continuousMap (f : C(UnitAddTorus (Fin 4), E)) (p : ℝ≥0∞) :
    MemLp f p (volume : Measure (UnitAddTorus (Fin 4))) :=
  MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall fun y => f.norm_coe_le_norm y)

/-- Uniform convergence of `L^p` functions to an `L^p` limit on the probability space `𝕋⁴` gives
strong `L^p` convergence. -/
theorem lpTendsto_of_unif {p : ℝ≥0∞} {g : ℕ → UnitAddTorus (Fin 4) → E}
    {g₀ : UnitAddTorus (Fin 4) → E} (hg : ∀ k, MemLp (g k) p volume) (hg₀ : MemLp g₀ p volume)
    (hu : ∀ ε > 0, ∀ᶠ k in atTop, ∀ y, ‖g k y - g₀ y‖ ≤ ε) :
    LpTendsto volume p g g₀ := by
  refine ⟨hg, hg₀, ?_⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  filter_upwards [hu _ hε'] with k hk
  refine (eLpNorm_le_of_ae_bound (Eventually.of_forall fun y => hk y)).trans (le_of_eq ?_)
  rw [measure_univ, ENNReal.one_rpow, one_mul, ENNReal.ofReal_toReal hεt]

end Uniform

/-! ### Convergence of sampled tests -/

section Samples

variable {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem dist_samplePt_index_add_le {N : ℕ} [NeZero N] (y : UnitAddTorus (Fin 4)) (μ : Fin 4)
    (m : ℕ) (hm : m ≤ 1) :
    dist (TorusCellEmbedding.samplePt
      (TorusPiecewiseConstantTranslation.index N y + m • Pi.single μ 1)) y ≤ 2 * (N : ℝ)⁻¹ := by
  have h0 : dist y (TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y)) ≤ (N : ℝ)⁻¹ :=
    VariableTorusDirac.dist_samplePt_index_le y
  have hidx : TorusPiecewiseConstantTranslation.index N y = TorusCellEmbedding.index N y := rfl
  interval_cases m
  · simp only [zero_smul, add_zero, hidx]
    rw [dist_comm]; linarith [inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) N)]
  · simp only [one_smul, hidx]
    rw [VariableTorusDirac.samplePt_add_single]
    calc dist (TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y) +
          VariableTorusDirac.lineVec μ (N : ℝ)⁻¹) y
        ≤ dist (TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y) +
            VariableTorusDirac.lineVec μ (N : ℝ)⁻¹)
            (TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y)) +
          dist (TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y)) y :=
          dist_triangle _ _ _
      _ ≤ |(N : ℝ)⁻¹| + (N : ℝ)⁻¹ := by
          gcongr
          · exact VariableTorusDirac.dist_add_lineVec_le _ μ _
          · rw [dist_comm]; exact h0
      _ = 2 * (N : ℝ)⁻¹ := by rw [abs_of_nonneg (by positivity)]; ring

theorem tendsto_inv_n (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => ((n k : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn)

/-- Uniform convergence of (once-shifted) samples of a continuous field. -/
theorem eventually_unif_sample (hn : Tendsto n atTop atTop) (f : C(UnitAddTorus (Fin 4), 𝔸))
    (m : ℕ) (hm : m ≤ 1) (μ : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ y, ‖f (TorusCellEmbedding.samplePt
      (TorusPiecewiseConstantTranslation.index (n k) y + m • Pi.single μ 1)) - f y‖ ≤ ε := by
  have huc := CompactSpace.uniformContinuous_of_continuous f.continuous
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδ, hδε⟩ := huc ε hε
  filter_upwards [(tendsto_order.1 ((tendsto_inv_n hn).const_mul 2)).2 δ (by simpa using hδ)]
    with k hk y
  have := hδε ((dist_samplePt_index_add_le y μ m hm).trans_lt (by simpa using hk))
  rw [dist_eq_norm] at this
  exact this.le

theorem lpTendsto_sample (hn : Tendsto n atTop atTop) (a : C1Test 𝔸) (ν : Fin 4) (p : ℝ≥0∞) :
    LpTendsto volume p (fun k => pc (fun x => sampleTest (n k) a x ν)) (a.a ν) := by
  refine lpTendsto_of_unif (fun k => memLp_pc_gen _ p) (memLp_continuousMap _ p) fun ε hε => ?_
  filter_upwards [eventually_unif_sample hn (a.a ν) 0 (by norm_num) 0 hε] with k hk y
  simpa [pc, sampleTest] using hk y

theorem lpTendsto_sample_T (hn : Tendsto n atTop atTop) (a : C1Test 𝔸) (μ ν : Fin 4)
    (p : ℝ≥0∞) :
    LpTendsto volume p (fun k => pc (T μ (fun x => sampleTest (n k) a x ν))) (a.a ν) := by
  refine lpTendsto_of_unif (fun k => memLp_pc_gen _ p) (memLp_continuousMap _ p) fun ε hε => ?_
  filter_upwards [eventually_unif_sample hn (a.a ν) 1 le_rfl μ hε] with k hk y
  simpa [pc, sampleTest, T] using hk y

end Samples

section SampleDiff

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- `R_h^0 D⁺_μ 𝒮_h a_ν → ∂_μ a_ν` uniformly, hence strongly in every `L^p`. -/
theorem lpTendsto_Dp_sample (hn : Tendsto n atTop atTop) (a : C1Test 𝔸) (μ ν : Fin 4)
    (p : ℝ≥0∞) :
    LpTendsto volume p (fun k => pc (DpA μ (fun x => sampleTest (n k) a x ν))) (a.da μ ν) := by
  refine lpTendsto_of_unif (fun k => memLp_pc_gen _ p) (memLp_continuousMap _ p) fun ε hε => ?_
  obtain ⟨δ, hδ, hfd⟩ := exists_fd_bound a μ ν (ε := ε / 2) (by positivity)
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  filter_upwards [(tendsto_order.1 (tendsto_inv_n hn)).2 δ hδ,
    eventually_unif_sample hn (a.da μ ν) 0 (by norm_num) 0 (ε := ε / 2) (by positivity)]
    with k hk hk2 y
  have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
  set x := TorusPiecewiseConstantTranslation.index (n k) y
  set y₀ := TorusCellEmbedding.samplePt x
  have hpc : pc (DpA μ (fun x => sampleTest (n k) a x ν)) y =
      ((n k : ℝ)⁻¹)⁻¹ • (a.a ν (y₀ + KolmogorovRieszTorus.coordPt μ ((n k : ℝ)⁻¹)) - a.a ν y₀) := by
    simp only [pc, DpA, sampleTest, inv_inv]
    rw [VariableTorusDirac.samplePt_add_single]
    rfl
  have h1 := hfd ((n k : ℝ)⁻¹) (by positivity) hk y₀
  have h2 : ‖a.da μ ν y₀ - a.da μ ν y‖ ≤ ε / 2 := by simpa [x, y₀] using hk2 y
  rw [hpc]
  calc ‖((n k : ℝ)⁻¹)⁻¹ • (a.a ν (y₀ + KolmogorovRieszTorus.coordPt μ ((n k : ℝ)⁻¹)) -
        a.a ν y₀) - a.da μ ν y‖
      = ‖(((n k : ℝ)⁻¹)⁻¹ • (a.a ν (y₀ + KolmogorovRieszTorus.coordPt μ ((n k : ℝ)⁻¹)) -
          a.a ν y₀) - a.da μ ν y₀) + (a.da μ ν y₀ - a.da μ ν y)‖ := by congr 1; abel
    _ ≤ ε / 2 + ε / 2 := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = ε := by ring

/-- `R_h^0 (D⁺_μ 𝒮_h a_ν - D⁺_ν 𝒮_h a_μ) → ∂_μ a_ν - ∂_ν a_μ` strongly in `L^p`. -/
theorem lpTendsto_linCurl_sample [Fact (1 ≤ (2 : ℝ≥0∞))] (hn : Tendsto n atTop atTop)
    (a : C1Test 𝔸) (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => linCurl (sampleTest (n k) a) x μ ν))
      (fun y => a.da μ ν y - a.da ν μ y) := by
  refine ((lpTendsto_Dp_sample hn a μ ν 2).sub (lpTendsto_Dp_sample hn a ν μ 2)).congr
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => rfl)
  rfl

end SampleDiff

/-! ### `eq:native-YM-variation` -/

section Main

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

local instance fact_one_le_four''' : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two''' : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder442' : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two

/-- The polarised commutator term converges strongly in `L²` to `[A_μ, a_ν] + [a_μ, A_ν]`. -/
theorem tendsto_commPol (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ)) (a : C1Test 𝔸)
    (μ ν : Fin 4) :
    LpTendsto volume 2
      (fun k => pc (fun x => commPol (slots (A k) x μ ν) (slots (sampleTest (n k) a) x μ ν)))
      (fun y => (A₀ μ y * a.a ν y - a.a ν y * A₀ μ y) + (a.a μ y * A₀ ν y - A₀ ν y * a.a μ y)) := by
  set M := ContinuousLinearMap.mul ℝ 𝔸
  -- the four connection slots
  have h1 := hA μ
  have h2 := (hA ν).shift hn (by norm_num) μ
  have h3 := ((hA μ).shift hn (by norm_num) ν).neg
  have h4 := (hA ν).neg
  -- the four test slots
  have g1 := lpTendsto_sample hn a μ 4
  have g2 := lpTendsto_sample_T hn a μ ν 4
  have g3 := (lpTendsto_sample_T hn a ν μ 4).neg
  have g4 := (lpTendsto_sample hn a ν 4).neg
  have hb := fun {u u' v v'} (hu : LpTendsto volume 4 u u') (hv : LpTendsto volume 4 v v') =>
    LpTendsto.bilin (ν := (volume : Measure (UnitAddTorus (Fin 4)))) (r := 2) M hu hv
  have t1 := (((hb h1 ((g2.add g3).add g4)).add (hb g1 ((h2.add h3).add h4))).sub
    (hb ((h2.add h3).add h4) g1)).sub (hb ((g2.add g3).add g4) h1)
  have t2 := (((hb h2 (g3.add g4)).add (hb g2 (h3.add h4))).sub (hb (h3.add h4) g2)).sub
    (hb (g3.add g4) h2)
  have t3 := (((hb h3 g4).add (hb g3 h4)).sub (hb h4 g3)).sub (hb g4 h3)
  have hsum := (t1.const_smul (1 / 2)).add ((t2.const_smul (1 / 2)).add (t3.const_smul (1 / 2)))
  refine hsum.congr (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, M,
      ContinuousLinearMap.mul_apply']
    rw [show pc (fun x => commPol (slots (A k) x μ ν) (slots (sampleTest (n k) a) x μ ν)) y =
        commPol (slots (A k) (TorusPiecewiseConstantTranslation.index (n k) y) μ ν)
          (slots (sampleTest (n k) a) (TorusPiecewiseConstantTranslation.index (n k) y) μ ν)
        from rfl, slots, slots, commPol_four]
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, M,
      ContinuousLinearMap.mul_apply']
    simp only [mul_add, add_mul, mul_neg, neg_mul, neg_neg, smul_sub, smul_add, smul_neg]
    module

theorem normSum_slots_sample_le {N : ℕ} (a : C1Test 𝔸) (x : LatticeTorusPlancherel.Grid 4 N)
    (μ ν : Fin 4) : normSum (slots (sampleTest N a) x μ ν) ≤ 4 * ∑ κ, ‖a.a κ‖ := by
  have hb : ∀ κ g, ‖sampleTest N a g κ‖ ≤ ∑ κ, ‖a.a κ‖ := fun κ g =>
    ((a.a κ).norm_coe_le_norm _).trans (Finset.single_le_sum (f := fun κ => ‖a.a κ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ κ))
  rw [normSum_slots]
  linarith [hb μ x, hb ν (x + Pi.single μ 1), hb μ (x + Pi.single ν 1), hb ν x]

/-- The remainder of the expanded variation tends to zero strongly in `L²`. -/
theorem tendsto_variation_remainder (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ)) (a : C1Test 𝔸)
    (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => curvVar (n k) (A k) (sampleTest (n k) a) x μ ν -
      linCurl (sampleTest (n k) a) x μ ν -
        commPol (slots (A k) x μ ν) (slots (sampleTest (n k) a) x μ ν))) 0 := by
  set Ma := ∑ κ, ‖a.a κ‖
  have hMa : 0 ≤ Ma := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hms : ∀ κ, Tendsto (fun k => meshSup (fun x => A k x κ)) atTop (𝓝 0) := fun κ =>
    tendsto_meshSup hn (hA κ).memLp_lim (hA κ).tendsto
  set σ : ℕ → ℝ := fun k => 2 * (meshSup (fun x => A k x μ) + meshSup (fun x => A k x ν))
  have hσ : Tendsto σ atTop (𝓝 0) := by simpa using ((hms μ).add (hms ν)).const_mul 2
  have hslot : ∀ k x, ((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν) ≤ σ k := by
    intro k x
    rw [normSum_slots]
    have h1 := le_meshSup (fun x => A k x μ) x
    have h2 := le_meshSup (fun x => A k x ν) (x + Pi.single μ 1)
    have h3 := le_meshSup (fun x => A k x μ) (x + Pi.single ν 1)
    have h4 := le_meshSup (fun x => A k x ν) x
    simp only [σ]
    nlinarith
  -- the slot sums and their `L²` bound
  set S : ℕ → UnitAddTorus (Fin 4) → ℝ := fun k y =>
    ‖pc (fun x => A k x μ) y‖ + ‖pc (T μ (fun x => A k x ν)) y‖ +
      ‖pc (T ν (fun x => A k x μ)) y‖ + ‖pc (fun x => A k x ν) y‖
  have hS : LpTendsto volume 4 S (fun y => ‖A₀ μ y‖ + ‖A₀ ν y‖ + ‖A₀ μ y‖ + ‖A₀ ν y‖) :=
    ((((hA μ).norm.add ((hA ν).shift hn (by norm_num) μ).norm).add
      ((hA μ).shift hn (by norm_num) ν).norm).add (hA ν).norm)
  have hS2 : LpTendsto volume 2 S (fun y => ‖A₀ μ y‖ + ‖A₀ ν y‖ + ‖A₀ μ y‖ + ‖A₀ ν y‖) :=
    hS.mono (by norm_num) (by norm_num)
  set Sinf : UnitAddTorus (Fin 4) → ℝ := fun y => ‖A₀ μ y‖ + ‖A₀ ν y‖ + ‖A₀ μ y‖ + ‖A₀ ν y‖
  have hfin : eLpNorm Sinf 2 volume ≠ ∞ := hS2.memLp_lim.2.ne
  -- the pointwise envelope
  have hpt : ∀ᶠ k in atTop, ∀ y, ‖pc (fun x => curvVar (n k) (A k) (sampleTest (n k) a) x μ ν -
      linCurl (sampleTest (n k) a) x μ ν -
        commPol (slots (A k) x μ ν) (slots (sampleTest (n k) a) x μ ν)) y‖ ≤
        (192 * Ma * σ k) * ‖S k y‖ := by
    filter_upwards [(tendsto_order.1 hσ).2 (1 / 32) (by norm_num)] with k hk y
    set x := TorusPiecewiseConstantTranslation.index (n k) y
    have hsmall : ((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν) ≤ 1 / 32 :=
      (hslot k x).trans hk.le
    have hb := norm_curvVar_sub_le (A k) (sampleTest (n k) a) x μ ν hsmall
    have hSy : S k y = normSum (slots (A k) x μ ν) := by rw [normSum_slots]; rfl
    have hs0 := normSum_nonneg (slots (A k) x μ ν)
    have hw := normSum_slots_sample_le (N := n k) a x μ ν
    rw [hSy, Real.norm_of_nonneg hs0]
    calc ‖curvVar (n k) (A k) (sampleTest (n k) a) x μ ν - linCurl (sampleTest (n k) a) x μ ν -
          commPol (slots (A k) x μ ν) (slots (sampleTest (n k) a) x μ ν)‖
        ≤ 48 * ((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν) ^ 2 *
            normSum (slots (sampleTest (n k) a) x μ ν) := hb
      _ = 48 * (((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν)) * normSum (slots (A k) x μ ν) *
            normSum (slots (sampleTest (n k) a) x μ ν) := by ring
      _ ≤ 48 * σ k * normSum (slots (A k) x μ ν) * (4 * Ma) := by
          have hσ0 : 0 ≤ σ k := (by positivity : (0 : ℝ) ≤ ((n k : ℝ))⁻¹ *
            normSum (slots (A k) x μ ν)).trans (hslot k x)
          gcongr
          all_goals first | exact hslot k x | exact normSum_nonneg _
      _ = 192 * Ma * σ k * normSum (slots (A k) x μ ν) := by ring
  have hbound : ∀ᶠ k in atTop, eLpNorm (pc (fun x => curvVar (n k) (A k) (sampleTest (n k) a) x μ ν -
      linCurl (sampleTest (n k) a) x μ ν -
        commPol (slots (A k) x μ ν) (slots (sampleTest (n k) a) x μ ν)) - 0) 2 volume ≤
      ENNReal.ofReal (192 * Ma * σ k) * (eLpNorm (S k - Sinf) 2 volume + eLpNorm Sinf 2 volume) := by
    filter_upwards [hpt] with k hk
    rw [sub_zero]
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall hk) 2).trans ?_
    gcongr
    have e : S k = (S k - Sinf) + Sinf := by funext y; simp
    conv_lhs => rw [e]
    exact eLpNorm_add_le ((hS2.memLp k).1.sub hS2.memLp_lim.1) hS2.memLp_lim.1 (by norm_num)
  have hup : Tendsto (fun k => ENNReal.ofReal (192 * Ma * σ k) *
      (eLpNorm (S k - Sinf) 2 volume + eLpNorm Sinf 2 volume)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ENNReal.ofReal (192 * Ma * σ k)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (hσ.const_mul (192 * Ma))
    have h2 := hS2.tendsto.add (tendsto_const_nhds (x := eLpNorm Sinf 2 volume))
    rw [zero_add] at h2
    have := ENNReal.Tendsto.mul h1 (Or.inr hfin) h2 (Or.inr ENNReal.zero_ne_top)
    simpa using this
  refine ⟨fun k => memLp_pc_gen _ 2, MemLp.zero, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun k => zero_le) hbound

/-- **`eq:native-YM-variation`** (`prop:native-YM-identification`, variation clause; unit-torus
rendering).  If `R_h^0 A_h → A` strongly in `L⁴(𝕋⁴; 𝔸)`, then for every `C¹` gauge test `a`
the literal first variation of the logarithmic curvature in the nodal direction `𝒮_h a`
satisfies `R_h^0 (D_A F_h[𝒮_h a]) → da + [A, a]` strongly in `L²`:
`(D_A F_h[𝒮_h a])_{μν} → (∂_μ a_ν - ∂_ν a_μ) + [A_μ, a_ν] + [a_μ, A_ν]`. -/
theorem native_YM_variation (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ)) (a : C1Test 𝔸)
    (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => curvVar (n k) (A k) (sampleTest (n k) a) x μ ν))
      (fun y => (a.da μ ν y - a.da ν μ y) +
        ((A₀ μ y * a.a ν y - a.a ν y * A₀ μ y) + (a.a μ y * A₀ ν y - A₀ ν y * a.a μ y))) := by
  have h := ((lpTendsto_linCurl_sample hn a μ ν).add (tendsto_commPol hn hA a μ ν)).add
    (tendsto_variation_remainder hn hA a μ ν)
  refine h.congr (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · simp only [Pi.add_apply, pc]; abel
  · simp

end Main

/-! ### Non-vacuity -/

section NonVacuity

/-- The zero test. -/
def zeroTest : C1Test ℂ where
  a := fun _ => 0
  da := fun _ _ => 0
  hasDerivAt := fun _ _ _ => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)

/-- Non-vacuity of `native_YM_variation`: the zero connections in `𝔸 = ℂ` and the zero test. -/
example (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => curvVar (k + 1) (fun _ _ => (0 : ℂ))
      (sampleTest (k + 1) zeroTest) x μ ν))
      (fun y => (zeroTest.da μ ν y - zeroTest.da ν μ y) +
        (((0 : ℂ) * zeroTest.a ν y - zeroTest.a ν y * 0) +
          (zeroTest.a μ y * 0 - 0 * zeroTest.a μ y))) :=
  native_YM_variation (n := fun k => k + 1) (tendsto_add_atTop_nat 1)
    (A := fun k _ _ => (0 : ℂ)) (A₀ := fun _ _ => 0)
    (fun _ => by
      have : (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4 (k + 1) => (0 : ℂ))) =
          fun _ => (0 : UnitAddTorus (Fin 4) → ℂ) := by funext k y; rfl
      rw [this]; exact LpTendsto.const MemLp.zero) zeroTest μ ν

end NonVacuity

end

end RenewalGeometry.NativeYMVariation
