/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeCriticalGridCompactness
import RenewalGeometry.Analysis.MollifierLpConvergence

/-!
# Identification of the literal logarithmic curvature: `F = dA + A ∧ A`
  (first assertion of `prop:native-YM-identification`, Einstein–SM action closure)

Setting (unit-torus rendering of the paper's box, see `Continuum/TorusTrigReconstruction.lean`):
the grid `(ℤ/N)⁴`, mesh `h = 1/N`, gauge potentials `A_μ(x) ∈ 𝔸` in a complete normed real
algebra with `‖1‖ = 1` (e.g. matrices with an operator norm), links `U_μ(x) = e^{h A_μ(x)}`,
the plaquette `U_{μν} = U_μ(x) U_ν(x+e_μ) U_μ(x+e_ν)⁻¹ U_ν(x)⁻¹` and the literal logarithmic
curvature `F^h_{μν} = h⁻² Log U_{μν}` (`curvLog`, `Log` the principal (Mercator) logarithm,
`LogBCH.logOnePlus`).

* `transl_tendsto` (generic): translation is continuous in `L^p(𝕋^d)`, `p < ∞` (density of bounded
  continuous functions and uniform continuity).
* `norm_curvLog_sub_le` (`eq:native-YM-split`, `eq:native-YM-envelope`): on the admissible chart
  `h Σ|W| ≤ 1/4`, `F^h = (D⁺_μ A_ν - D⁺_ν A_μ) + ½ Σ_{i<j}[W_i, W_j] + O(h |W|³)` with the four
  slots `W = (A_μ, T_μ A_ν, -T_ν A_μ, -A_ν)` (second-order BCH, `LogBCH.norm_log_expProd_sub_bch_le`).
* `tendsto_nonlinear`: if `R_h^0 A_h → A` strongly in `L⁴`, then `R_h^0 𝒩_h(A_h) → A ∧ A`
  (`[A_μ, A_ν]`) strongly in `L²`, where `𝒩_h = F^h - (D⁺_μA_ν - D⁺_νA_μ)`.
* `native_YM_curvature_identification` (**`F = F_A`**): if moreover `R_h^0 F^h → F` strongly in
  `L²`, then for every coordinate functional `ℓ : 𝔸 →L[ℝ] ℂ` and every frequency `m`,
  `(ℓF_{μν} - ℓ[A_μ,A_ν])^(m) = 2πi m_μ (ℓA_ν)^(m) - 2πi m_ν (ℓA_μ)^(m)`, i.e.
  `F = dA + A ∧ A` in the sense of distributions on `𝕋⁴`; equivalently
  `R_h^0(D⁺_μA_ν - D⁺_νA_μ) → F - [A_μ, A_ν]` in `L²` and the limit is the distributional curl.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.NativeYMIdentification

open TorusTrigReconstruction NativeCriticalGrid TorusPiecewiseConstantTranslation TorusSobolev
  LogBCH NormedSpace

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-! ### Continuity of translations in `L^p(𝕋^d)` -/

section Translation

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eLpNorm_comp_add (g : UnitAddTorus d → E) (hg : AEStronglyMeasurable g volume)
    (z : UnitAddTorus d) (p : ℝ≥0∞) :
    eLpNorm (fun y => g (y + z)) p volume = eLpNorm g p volume :=
  eLpNorm_comp_measurePreserving hg (measurePreserving_add_right volume z)

/-- **Translations are continuous in `L^p(𝕋^d)`, `p < ∞`.** -/
theorem transl_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {g : UnitAddTorus d → E}
    (hg : MemLp g p volume) :
    Tendsto (fun z => eLpNorm (fun y => g (y + z) - g y) p volume) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  obtain ⟨g', hg', hg'm⟩ := hg.exists_boundedContinuous_eLpNorm_sub_le hp
    (ε := ε / 3) (by simp [hε.ne'])
  have huc := CompactSpace.uniformContinuous_of_continuous g'.continuous
  rw [Metric.uniformContinuous_iff] at huc
  have hε3t : ε / 3 ≠ ∞ := ENNReal.div_ne_top hεt (by norm_num)
  have hε3 : 0 < (ε / 3).toReal := ENNReal.toReal_pos (by simp [hε.ne']) hε3t
  obtain ⟨δ, hδ, hδg⟩ := huc _ hε3
  filter_upwards [Metric.ball_mem_nhds (0 : UnitAddTorus d) hδ] with z hz
  have hm1 : AEStronglyMeasurable (fun y => (g - ⇑g') (y + z)) volume :=
    (hg.1.sub g'.continuous.aestronglyMeasurable).comp_measurePreserving
      (measurePreserving_add_right volume z)
  have hm2 : AEStronglyMeasurable (fun y => g' (y + z) - g' y) volume :=
    (g'.continuous.comp (continuous_add_right z)).aestronglyMeasurable.sub
      g'.continuous.aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun y => (⇑g' - g) y) volume :=
    g'.continuous.aestronglyMeasurable.sub hg.1
  have hsplit : (fun y => g (y + z) - g y) = ((fun y => (g - ⇑g') (y + z)) +
      fun y => g' (y + z) - g' y) + fun y => (⇑g' - g) y := by
    funext y; simp only [Pi.add_apply, Pi.sub_apply]; abel
  rw [hsplit]
  have h1 : eLpNorm (fun y => (g - ⇑g') (y + z)) p volume ≤ ε / 3 := by
    rw [eLpNorm_comp_add _ (hg.1.sub g'.continuous.aestronglyMeasurable)]; exact hg'
  have h2 : eLpNorm (fun y => g' (y + z) - g' y) p volume ≤ ε / 3 := by
    refine (eLpNorm_le_of_ae_bound (C := (ε / 3).toReal) (Eventually.of_forall fun y => ?_)).trans ?_
    · have := hδg (a := y + z) (b := y) (by
        rw [dist_eq_norm, add_sub_cancel_left]; simpa [dist_eq_norm] using hz)
      rw [dist_eq_norm] at this; exact this.le
    · rw [measure_univ, ENNReal.one_rpow, one_mul, ENNReal.ofReal_toReal hε3t]
  have h3 : eLpNorm (fun y => (⇑g' - g) y) p volume ≤ ε / 3 := by
    rw [show (fun y => (⇑g' - g) y) = -(g - ⇑g') by funext y; simp, eLpNorm_neg]; exact hg'
  calc eLpNorm (((fun y => (g - ⇑g') (y + z)) + fun y => g' (y + z) - g' y) +
        fun y => (⇑g' - g) y) p volume
      ≤ eLpNorm ((fun y => (g - ⇑g') (y + z)) + fun y => g' (y + z) - g' y) p volume +
          eLpNorm (fun y => (⇑g' - g) y) p volume :=
        eLpNorm_add_le (hm1.add hm2) hm3 Fact.out
    _ ≤ (eLpNorm (fun y => (g - ⇑g') (y + z)) p volume +
          eLpNorm (fun y => g' (y + z) - g' y) p volume) + eLpNorm (fun y => (⇑g' - g) y) p volume :=
        add_le_add (eLpNorm_add_le hm1 hm2 Fact.out) le_rfl
    _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add h1 h2) h3
    _ = ε := ENNReal.add_thirds ε

end Translation

/-! ### Small `L^p` calculus -/

section Calculus

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem _root_.RenewalGeometry.LpTendsto.const_smul {p : ℝ≥0∞} (c : ℝ) {u : ℕ → X → E} {u' : X → E}
    (hu : LpTendsto ν p u u') : LpTendsto ν p (fun k => c • u k) (c • u') := by
  refine ⟨fun k => (hu.memLp k).const_smul c, hu.memLp_lim.const_smul c, ?_⟩
  have h := ENNReal.Tendsto.const_mul hu.tendsto (Or.inr ENNReal.coe_ne_top) (a := ‖c‖₊)
  rw [mul_zero] at h
  refine h.congr fun k => ?_
  rw [← smul_sub, eLpNorm_const_smul]
  rfl

theorem _root_.RenewalGeometry.LpTendsto.clm {p : ℝ≥0∞} (L : E →L[ℝ] F) {u : ℕ → X → E} {u' : X → E}
    (hu : LpTendsto ν p u u') : LpTendsto ν p (fun k x => L (u k x)) (fun x => L (u' x)) := by
  refine ⟨fun k => L.comp_memLp' (hu.memLp k), L.comp_memLp' hu.memLp_lim, ?_⟩
  have h := ENNReal.Tendsto.const_mul hu.tendsto (Or.inr ENNReal.ofReal_ne_top)
    (a := ENNReal.ofReal ‖L‖)
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    fun k => eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) p
  simp only [Pi.sub_apply, ← map_sub]
  exact L.le_opNorm _

theorem _root_.RenewalGeometry.LpTendsto.norm {p : ℝ≥0∞} {u : ℕ → X → E} {u' : X → E} (hu : LpTendsto ν p u u') :
    LpTendsto ν p (fun k x => ‖u k x‖) (fun x => ‖u' x‖) := by
  refine ⟨fun k => (hu.memLp k).norm, hu.memLp_lim.norm, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu.tendsto (fun k => zero_le)
    fun k => eLpNorm_mono fun x => ?_
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_norm_sub_norm_le _ _

end Calculus

/-! ### Unit shifts of raw reconstructions -/

section Shifts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unit shift `T_μ v (x) = v(x + e_μ)`. -/
def T (μ : Fin 4) {N : ℕ} (v : LatticeTorusPlancherel.Grid 4 N → E) :
    LatticeTorusPlancherel.Grid 4 N → E := fun x => v (x + Pi.single μ 1)

theorem pc_T {N : ℕ} [NeZero N] (μ : Fin 4) (v : LatticeTorusPlancherel.Grid 4 N → E)
    (y : UnitAddTorus (Fin 4)) :
    pc (T μ v) y = pc v (y + KolmogorovRieszTorus.coordPt μ (1 / N)) := by
  have h := pc_add_coordPt_int v y μ 1
  simp only [Int.cast_one] at h
  rw [h]
  simp [T, TorusPiecewiseConstantTranslation.shift, pc]

theorem memLp_pc_gen {N : ℕ} [NeZero N] (v : LatticeTorusPlancherel.Grid 4 N → E) (p : ℝ≥0∞) :
    MemLp (pc v) p (volume : Measure (UnitAddTorus (Fin 4))) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ g, ‖v g‖ ≤ C :=
    ⟨∑ g, ‖v g‖, fun g => Finset.single_le_sum (f := fun g => ‖v g‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ g)⟩
  exact MemLp.of_bound (stronglyMeasurable_pc v).aestronglyMeasurable C
    (Eventually.of_forall fun y => hC _)

theorem tendsto_coordPt {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (μ : Fin 4) :
    Tendsto (fun k => KolmogorovRieszTorus.coordPt μ (1 / (n k : ℝ))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k => (1 / (n k : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hn)
  have hc : Continuous fun s : ℝ => (Pi.single μ (s : UnitAddCircle) : UnitAddTorus (Fin 4)) :=
    continuous_pi fun i => by
      by_cases h : i = μ
      · subst h; simpa using QuotientAddGroup.continuous_mk
      · simp only [Pi.single_eq_of_ne h]; exact continuous_const
  have := (hc.tendsto 0).comp h0
  have h1 : (Pi.single μ ((0 : ℝ) : UnitAddCircle) : UnitAddTorus (Fin 4)) = 0 := by simp
  rw [h1] at this
  exact this

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- One-step shifts of an `L^p`-convergent sequence of raw reconstructions have the same limit. -/
theorem _root_.RenewalGeometry.LpTendsto.shift (hn : Tendsto n atTop atTop) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {v : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → E} {g : UnitAddTorus (Fin 4) → E}
    (hv : LpTendsto volume p (fun k => pc (v k)) g) (μ : Fin 4) :
    LpTendsto volume p (fun k => pc (T μ (v k))) g := by
  refine ⟨fun k => memLp_pc_gen _ p, hv.memLp_lim, ?_⟩
  have htr := (transl_tendsto hp hv.memLp_lim).comp (tendsto_coordPt hn μ)
  have hup := hv.tendsto.add htr
  rw [zero_add] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
    fun k => ?_
  set z := KolmogorovRieszTorus.coordPt μ (1 / (n k : ℝ))
  have hsplit : pc (T μ (v k)) - g = (fun y => (pc (v k) - g) (y + z)) +
      fun y => g (y + z) - g y := by
    funext y; simp only [Pi.sub_apply, Pi.add_apply, pc_T]; abel
  rw [hsplit]
  have hm := (hv.memLp k).1.sub hv.memLp_lim.1
  refine (eLpNorm_add_le (hm.comp_measurePreserving (measurePreserving_add_right volume z))
    ((hv.memLp_lim.1.comp_measurePreserving (measurePreserving_add_right volume z)).sub
      hv.memLp_lim.1) Fact.out).trans (le_of_eq ?_)
  congr 1
  exact eLpNorm_comp_measurePreserving hm (measurePreserving_add_right volume z)

end Shifts

/-! ### The literal logarithmic curvature and its second-order expansion -/

section Expansion

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {N : ℕ}

/-- The four slots `W = (A_μ, T_μ A_ν, -T_ν A_μ, -A_ν)` of the plaquette. -/
def slots (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (x : LatticeTorusPlancherel.Grid 4 N)
    (μ ν : Fin 4) : List 𝔸 :=
  [A x μ, A (x + Pi.single μ 1) ν, -A (x + Pi.single ν 1) μ, -A x ν]

/-- **The literal logarithmic curvature** `F^h_{μν} = h⁻² Log(e^{hA_μ} e^{hT_μA_ν} e^{-hT_νA_μ}
e^{-hA_ν})`, `h = 1/N`, with the principal (Mercator) logarithm. -/
def curvLog (N : ℕ) (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) : 𝔸 :=
  ((N : ℝ) ^ 2) • logOnePlus (expProd ((slots A x μ ν).map fun w => (N : ℝ)⁻¹ • w) - 1)

/-- The scaled forward difference of an `𝔸`-valued grid function. -/
def DpA (μ : Fin 4) (v : LatticeTorusPlancherel.Grid 4 N → 𝔸) (x : LatticeTorusPlancherel.Grid 4 N) :
    𝔸 := (N : ℝ) • (v (x + Pi.single μ 1) - v x)

/-- The linear part `D⁺_μ A_ν - D⁺_ν A_μ` of the split `eq:native-YM-split`. -/
def linCurl (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (x : LatticeTorusPlancherel.Grid 4 N)
    (μ ν : Fin 4) : 𝔸 :=
  DpA μ (fun x => A x ν) x - DpA ν (fun x => A x μ) x

theorem sum_map_smul (c : ℝ) (L : List 𝔸) : (L.map fun w => c • w).sum = c • L.sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, smul_add]

theorem commTerm_map_smul (c : ℝ) (L : List 𝔸) :
    commTerm (L.map fun w => c • w) = (c ^ 2) • commTerm L := by
  induction L with
  | nil => simp [commTerm]
  | cons x L ih =>
      simp only [List.map_cons, commTerm, ih, sum_map_smul, smul_mul_smul_comm, smul_add,
        smul_sub, smul_smul]
      congr 1
      rw [show (1 / 2 * (c * c) : ℝ) = c ^ 2 * (1 / 2) by ring]

theorem normSum_map_smul (c : ℝ) (L : List 𝔸) :
    normSum (L.map fun w => c • w) = |c| * normSum L := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, norm_smul, mul_add]

theorem slots_sum (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    (N : ℝ) • (slots A x μ ν).sum = linCurl A x μ ν := by
  simp only [slots, List.sum_cons, List.sum_nil, linCurl, DpA]
  module

theorem normSum_slots (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    normSum (slots A x μ ν) = ‖A x μ‖ + ‖A (x + Pi.single μ 1) ν‖ +
      ‖A (x + Pi.single ν 1) μ‖ + ‖A x ν‖ := by
  simp [slots, normSum_cons, norm_neg]
  ring

/-- **`eq:native-YM-split` with the quadratic envelope**: on the admissible chart
`h Σ|W| ≤ 1/4`, `‖F^h - (D⁺_μA_ν - D⁺_νA_μ) - ½ Σ_{i<j}[W_i,W_j]‖ ≤ 6 h (Σ|W|)³`. -/
theorem norm_curvLog_sub_le [NeZero N] (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4)
    (hs : (N : ℝ)⁻¹ * normSum (slots A x μ ν) ≤ 1 / 4) :
    ‖curvLog N A x μ ν - linCurl A x μ ν - commTerm (slots A x μ ν)‖ ≤
      6 * (N : ℝ)⁻¹ * normSum (slots A x μ ν) ^ 3 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set L := slots A x μ ν
  set L' := L.map fun w => (N : ℝ)⁻¹ • w
  have hs' : normSum L' ≤ 1 / 4 := by
    rw [normSum_map_smul, abs_of_pos (inv_pos.2 hN)]; exact hs
  have hb := norm_log_expProd_sub_bch_le L' hs'
  have e : curvLog N A x μ ν - linCurl A x μ ν - commTerm L =
      ((N : ℝ) ^ 2) • (logOnePlus (expProd L' - 1) - (L'.sum + commTerm L')) := by
    rw [curvLog, ← slots_sum, sum_map_smul, commTerm_map_smul]
    simp only [smul_sub, smul_add, smul_smul]
    rw [show (N : ℝ) ^ 2 * (N : ℝ)⁻¹ = N by field_simp,
      show (N : ℝ) ^ 2 * (N : ℝ)⁻¹ ^ 2 = 1 by field_simp, one_smul]
    abel
  rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [normSum_map_smul, abs_of_pos (inv_pos.2 hN)] at hb
  calc (N : ℝ) ^ 2 * ‖logOnePlus (expProd L' - 1) - (L'.sum + commTerm L')‖
      ≤ (N : ℝ) ^ 2 * (6 * ((N : ℝ)⁻¹ * normSum L) ^ 3) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 6 * (N : ℝ)⁻¹ * normSum L ^ 3 := by field_simp

/-- `½ Σ_{i<j}[W_i, W_j]` for `W = (a, b, -a, -b)` is `[a, b]`. -/
theorem commTerm_limit (a b : 𝔸) : commTerm [a, b, -a, -b] = a * b - b * a := by
  simp only [commTerm, List.sum_cons, List.sum_nil, add_zero, mul_zero, zero_mul, sub_zero]
  simp only [mul_add, add_mul, mul_neg, neg_mul, neg_neg, smul_sub, smul_add, smul_neg]
  module

/-- The explicit form of the commutator term of four slots. -/
theorem commTerm_four (a b c e : 𝔸) :
    commTerm [a, b, c, e] = (1 / 2 : ℝ) • (a * (b + c + e) - (b + c + e) * a) +
      ((1 / 2 : ℝ) • (b * (c + e) - (c + e) * b) + (1 / 2 : ℝ) • (c * e - e * c)) := by
  simp only [commTerm, List.sum_cons, List.sum_nil, add_zero, mul_zero, zero_mul, sub_zero,
    smul_zero]
  congr 2; abel

end Expansion

/-! ### Passage to the limit -/

section Convergence

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

local instance fact_one_le_four' : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two' : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder442 : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two

/-- The commutator term of the four slots converges to `A ∧ A = [A_μ, A_ν]` strongly in `L²`. -/
theorem tendsto_commTerm (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ)) (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => commTerm (slots (A k) x μ ν)))
      (fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) := by
  set M := ContinuousLinearMap.mul ℝ 𝔸
  have ha := hA μ
  have hb := (hA ν).shift hn (by norm_num) μ
  have hc := ((hA μ).shift hn (by norm_num) ν).neg
  have he := (hA ν).neg
  have hbce := (hb.add hc).add he
  have hce := hc.add he
  have h1 := (LpTendsto.bilin (r := 2) M ha hbce).sub (LpTendsto.bilin (r := 2) M hbce ha)
  have h2 := (LpTendsto.bilin (r := 2) M hb hce).sub (LpTendsto.bilin (r := 2) M hce hb)
  have h3 := (LpTendsto.bilin (r := 2) M hc he).sub (LpTendsto.bilin (r := 2) M he hc)
  have hsum := (h1.const_smul (1 / 2)).add ((h2.const_smul (1 / 2)).add (h3.const_smul (1 / 2)))
  refine hsum.congr (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, M,
      ContinuousLinearMap.mul_apply']
    rw [show pc (fun x => commTerm (slots (A k) x μ ν)) y =
        commTerm (slots (A k) (TorusPiecewiseConstantTranslation.index (n k) y) μ ν) from rfl,
      slots, commTerm_four]
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, M,
      ContinuousLinearMap.mul_apply']
    simp only [mul_add, add_mul, mul_neg, neg_mul, neg_neg, smul_sub, smul_add, smul_neg]
    module

/-- The cubic remainder of the second-order expansion tends to zero strongly in `L²`. -/
theorem tendsto_remainder (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ)) (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (A k) x μ ν - linCurl (A k) x μ ν -
      commTerm (slots (A k) x μ ν))) 0 := by
  -- uniform smallness of the scaled slots
  have hms : ∀ κ, Tendsto (fun k => meshSup (fun x => A k x κ)) atTop (𝓝 0) := fun κ =>
    tendsto_meshSup hn (hA κ).memLp_lim (hA κ).tendsto
  set σ : ℕ → ℝ := fun k => 2 * (meshSup (fun x => A k x μ) + meshSup (fun x => A k x ν))
  have hσ : Tendsto σ atTop (𝓝 0) := by simpa using ((hms μ).add (hms ν)).const_mul 2
  have hσ0 : ∀ k, 0 ≤ σ k := fun k =>
    mul_nonneg zero_le_two (add_nonneg (meshSup_nonneg _) (meshSup_nonneg _))
  have hslot : ∀ k x, ((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν) ≤ σ k := by
    intro k x
    rw [normSum_slots]
    have h1 := le_meshSup (fun x => A k x μ) x
    have h2 := le_meshSup (fun x => A k x ν) (x + Pi.single μ 1)
    have h3 := le_meshSup (fun x => A k x μ) (x + Pi.single ν 1)
    have h4 := le_meshSup (fun x => A k x ν) x
    simp only [σ]
    nlinarith
  -- the `L⁴` sum of slot norms and its square
  set S : ℕ → UnitAddTorus (Fin 4) → ℝ := fun k y =>
    ‖pc (fun x => A k x μ) y‖ + ‖pc (T μ (fun x => A k x ν)) y‖ +
      ‖pc (T ν (fun x => A k x μ)) y‖ + ‖pc (fun x => A k x ν) y‖
  have hS : LpTendsto volume 4 S (fun y => ‖A₀ μ y‖ + ‖A₀ ν y‖ + ‖A₀ μ y‖ + ‖A₀ ν y‖) :=
    ((((hA μ).norm.add ((hA ν).shift hn (by norm_num) μ).norm).add
      ((hA μ).shift hn (by norm_num) ν).norm).add (hA ν).norm)
  have hS2 := LpTendsto.bilin (r := 2) (ContinuousLinearMap.mul ℝ ℝ) hS hS
  set Sinf2 : UnitAddTorus (Fin 4) → ℝ := fun y => ContinuousLinearMap.mul ℝ ℝ
    (‖A₀ μ y‖ + ‖A₀ ν y‖ + ‖A₀ μ y‖ + ‖A₀ ν y‖) (‖A₀ μ y‖ + ‖A₀ ν y‖ + ‖A₀ μ y‖ + ‖A₀ ν y‖)
  have hfin : eLpNorm Sinf2 2 volume ≠ ∞ := hS2.memLp_lim.2.ne
  -- the pointwise envelope
  have hpt : ∀ᶠ k in atTop, ∀ y, ‖pc (fun x => curvLog (n k) (A k) x μ ν - linCurl (A k) x μ ν -
      commTerm (slots (A k) x μ ν)) y‖ ≤ 6 * σ k * ‖ContinuousLinearMap.mul ℝ ℝ (S k y) (S k y)‖ := by
    filter_upwards [(tendsto_order.1 hσ).2 (1 / 4) (by norm_num)] with k hk y
    set x := TorusPiecewiseConstantTranslation.index (n k) y
    have hsmall : ((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν) ≤ 1 / 4 := (hslot k x).trans hk.le
    have hb := norm_curvLog_sub_le (A k) x μ ν hsmall
    have hSy : S k y = normSum (slots (A k) x μ ν) := by
      rw [normSum_slots]; rfl
    have hs0 := normSum_nonneg (slots (A k) x μ ν)
    rw [ContinuousLinearMap.mul_apply', Real.norm_of_nonneg (mul_self_nonneg _), hSy]
    calc ‖pc (fun x => curvLog (n k) (A k) x μ ν - linCurl (A k) x μ ν -
          commTerm (slots (A k) x μ ν)) y‖
        = ‖curvLog (n k) (A k) x μ ν - linCurl (A k) x μ ν - commTerm (slots (A k) x μ ν)‖ := rfl
      _ ≤ 6 * ((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν) ^ 3 := hb
      _ = 6 * (((n k : ℝ))⁻¹ * normSum (slots (A k) x μ ν)) *
            (normSum (slots (A k) x μ ν) * normSum (slots (A k) x μ ν)) := by ring
      _ ≤ 6 * σ k * (normSum (slots (A k) x μ ν) * normSum (slots (A k) x μ ν)) := by
          gcongr; exact hslot k x
  have hbound : ∀ᶠ k in atTop, eLpNorm (pc (fun x => curvLog (n k) (A k) x μ ν -
      linCurl (A k) x μ ν - commTerm (slots (A k) x μ ν)) - 0) 2 volume ≤
      ENNReal.ofReal (6 * σ k) * (eLpNorm ((fun y => ContinuousLinearMap.mul ℝ ℝ (S k y) (S k y)) -
        Sinf2) 2 volume + eLpNorm Sinf2 2 volume) := by
    filter_upwards [hpt] with k hk
    rw [sub_zero]
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall hk) 2).trans ?_
    gcongr
    have e : (fun y => ContinuousLinearMap.mul ℝ ℝ (S k y) (S k y)) =
        ((fun y => ContinuousLinearMap.mul ℝ ℝ (S k y) (S k y)) - Sinf2) + Sinf2 := by
      funext y; simp
    conv_lhs => rw [e]
    exact eLpNorm_add_le ((hS2.memLp k).1.sub hS2.memLp_lim.1) hS2.memLp_lim.1 (by norm_num)
  have hup : Tendsto (fun k => ENNReal.ofReal (6 * σ k) *
      (eLpNorm ((fun y => ContinuousLinearMap.mul ℝ ℝ (S k y) (S k y)) - Sinf2) 2 volume +
        eLpNorm Sinf2 2 volume)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ENNReal.ofReal (6 * σ k)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (hσ.const_mul 6)
    have h2 := hS2.tendsto.add (tendsto_const_nhds (x := eLpNorm Sinf2 2 volume))
    rw [zero_add] at h2
    have := ENNReal.Tendsto.mul h1 (Or.inr hfin) h2 (Or.inr ENNReal.zero_ne_top)
    simpa using this
  refine ⟨fun k => memLp_pc_gen _ 2, MemLp.zero, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun k => zero_le) hbound

/-- **`R_h^0 𝒩_h(A_h) → A ∧ A` strongly in `L²`** (the step of the paper's proof of
`prop:native-YM-identification`), `𝒩_h = F^h - (D⁺_μA_ν - D⁺_νA_μ)`. -/
theorem tendsto_nonlinear (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ)) (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (A k) x μ ν - linCurl (A k) x μ ν))
      (fun y => A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y) := by
  refine ((tendsto_remainder hn hA μ ν).add (tendsto_commTerm hn hA μ ν)).congr
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · simp only [Pi.add_apply, pc]; abel
  · simp

end Convergence

/-! ### `F = F_A`: identification of the limit curvature -/

section Identification

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

local instance fact_one_le_four'' : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two'' : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem coord_linCurl (ℓ : 𝔸 →L[ℝ] ℂ) {N : ℕ} [NeZero N]
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (μ ν : Fin 4) :
    (fun x => ℓ (linCurl A x μ ν)) = Dp μ (fun x => ℓ (A x ν)) - Dp ν (fun x => ℓ (A x μ)) := by
  funext x
  simp only [linCurl, DpA, Pi.sub_apply, Dp_apply, map_sub, map_smul, Complex.real_smul,
    Complex.ofReal_natCast]

theorem tendsto_norm_pcLp_sub_toLp {u : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → ℂ}
    {g : UnitAddTorus (Fin 4) → ℂ} (h : LpTendsto volume 2 (fun k => pc (u k)) g) :
    Tendsto (fun k => ‖pcLp (u k) - h.memLp_lim.toLp g‖) atTop (𝓝 0) := by
  have e : ∀ k, ‖pcLp (u k) - h.memLp_lim.toLp g‖ = (eLpNorm (pc (u k) - g) 2 volume).toReal := by
    intro k
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (pcLp (u k)) (h.memLp_lim.toLp g), coeFn_pcLp (u k),
      h.memLp_lim.coeFn_toLp] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    rfl
  simp only [e]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.tendsto
  rw [ENNReal.toReal_zero] at this
  exact this

theorem mFourierCoeff_toLp_eq {g : UnitAddTorus (Fin 4) → ℂ} (hg : MemLp g 2 volume)
    (m : Fin 4 → ℤ) : mFourierCoeff (hg.toLp g) m = mFourierCoeff g m :=
  integral_congr_ae (hg.coeFn_toLp.mono fun y hy => by simp only [hy])

theorem mFourierCoeff_sub' {f g : UnitAddTorus (Fin 4) → ℂ} (hf : Integrable f volume)
    (hg : Integrable g volume) (m : Fin 4 → ℤ) :
    mFourierCoeff (fun y => f y - g y) m = mFourierCoeff f m - mFourierCoeff g m := by
  have hint : ∀ {u : UnitAddTorus (Fin 4) → ℂ}, Integrable u volume →
      Integrable (fun t => mFourier (-m) t • u t) volume := fun hu =>
    hu.bdd_mul (c := 1) (mFourier (-m)).continuous.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [TorusSobolev.norm_mFourier_apply])
  simp only [mFourierCoeff, smul_sub]
  exact integral_sub (hint hf) (hint hg)

/-- **`prop:native-YM-identification`, first assertion (`F = F_A`).**  Let `R_h^0 A_h → A`
strongly in `L⁴(𝕋⁴; 𝔸)` and let the literal logarithmic curvature satisfy `R_h^0 F^h → F` strongly
in `L²`.  Then `R_h^0 (D⁺_μ A_ν - D⁺_ν A_μ) → F_{μν} - [A_μ, A_ν]` strongly in `L²`, and for every
coordinate functional `ℓ : 𝔸 →L[ℝ] ℂ` and every frequency `m`,
`(ℓ F_{μν})^(m) - (ℓ [A_μ, A_ν])^(m) = 2πi m_μ (ℓ A_ν)^(m) - 2πi m_ν (ℓ A_μ)^(m)`:
`F = dA + A ∧ A` in the sense of distributions on `𝕋⁴`. -/
theorem native_YM_curvature_identification (hn : Tendsto n atTop atTop)
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → 𝔸}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    {F : Fin 4 → Fin 4 → UnitAddTorus (Fin 4) → 𝔸}
    (hF : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x => curvLog (n k) (A k) x μ ν)) (F μ ν))
    (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => linCurl (A k) x μ ν))
      (fun y => F μ ν y - (A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y)) ∧
    ∀ (ℓ : 𝔸 →L[ℝ] ℂ) (m : Fin 4 → ℤ),
      mFourierCoeff (fun y => ℓ (F μ ν y)) m -
          mFourierCoeff (fun y => ℓ (A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y)) m =
        2 * π * Complex.I * m μ * mFourierCoeff (fun y => ℓ (A₀ ν y)) m -
          2 * π * Complex.I * m ν * mFourierCoeff (fun y => ℓ (A₀ μ y)) m := by
  have hlin : LpTendsto volume 2 (fun k => pc (fun x => linCurl (A k) x μ ν))
      (fun y => F μ ν y - (A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y)) :=
    ((hF μ ν).sub (tendsto_nonlinear hn hA μ ν)).congr
      (fun k => Eventually.of_forall fun y => by simp only [Pi.sub_apply, pc]; abel)
      (Eventually.of_forall fun y => rfl)
  refine ⟨hlin, fun ℓ m => ?_⟩
  -- coordinates
  have hℓ := hlin.clm ℓ
  have hℓ' : LpTendsto volume 2 (fun k => pc (Dp μ (fun x => ℓ (A k x ν)) -
      Dp ν (fun x => ℓ (A k x μ)))) (fun y => ℓ (F μ ν y - (A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y))) :=
    hℓ.congr (fun k => Eventually.of_forall fun y => by
      rw [← coord_linCurl]; rfl) (Eventually.of_forall fun y => rfl)
  have hc1 := tendsto_coef_of_tendsto_pcLp hn (tendsto_norm_pcLp_sub_toLp hℓ') m
  rw [mFourierCoeff_toLp_eq] at hc1
  have hu : ∀ κ, LpTendsto volume 2 (fun k => pc (fun x => ℓ (A k x κ))) (fun y => ℓ (A₀ κ y)) :=
    fun κ => ((hA κ).mono (by norm_num) (by norm_num)).clm ℓ
  have hcκ : ∀ κ, Tendsto (fun k => coef (fun x => ℓ (A k x κ)) m) atTop
      (𝓝 (mFourierCoeff (fun y => ℓ (A₀ κ y)) m)) := by
    intro κ
    have := tendsto_coef_of_tendsto_pcLp hn (tendsto_norm_pcLp_sub_toLp (hu κ)) m
    rwa [mFourierCoeff_toLp_eq] at this
  have hc2 : Tendsto (fun k => coef (Dp μ (fun x => ℓ (A k x ν)) - Dp ν (fun x => ℓ (A k x μ))) m)
      atTop (𝓝 (2 * π * Complex.I * m μ * mFourierCoeff (fun y => ℓ (A₀ ν y)) m -
        2 * π * Complex.I * m ν * mFourierCoeff (fun y => ℓ (A₀ μ y)) m)) := by
    simp only [coef_sub, coef_Dp]
    exact ((tendsto_sym hn μ m).mul (hcκ ν)).sub ((tendsto_sym hn ν m).mul (hcκ μ))
  have huniq := tendsto_nhds_unique hc1 hc2
  rw [← huniq]
  have hFi : Integrable (fun y => ℓ (F μ ν y)) volume :=
    (ℓ.comp_memLp' (hF μ ν).memLp_lim).integrable (by norm_num)
  have hXi : Integrable (fun y => ℓ (A₀ μ y * A₀ ν y - A₀ ν y * A₀ μ y)) volume :=
    (ℓ.comp_memLp' (tendsto_commTerm hn hA μ ν).memLp_lim).integrable (by norm_num)
  rw [← mFourierCoeff_sub' hFi hXi]
  congr 1
  funext y
  simp only [map_sub]

end Identification

/-! ### Non-vacuity -/

section NonVacuity

/-- The literal curvature of the zero connection vanishes. -/
theorem curvLog_zero {N : ℕ} (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    curvLog (𝔸 := ℝ) N (fun _ _ => 0) x μ ν = 0 := by
  simp [curvLog, slots, expProd, logOnePlus, logTerm]

theorem pc_zero_real {N : ℕ} [NeZero N] :
    pc (fun _ : LatticeTorusPlancherel.Grid 4 N => (0 : ℝ)) = 0 := by
  funext y; rfl

theorem lpTendsto_zero_conn (p : ℝ≥0∞) :
    LpTendsto volume p (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4 (k + 1) => (0 : ℝ)))
      (fun _ : UnitAddTorus (Fin 4) => (0 : ℝ)) := by
  simp only [pc_zero_real]
  exact LpTendsto.const MemLp.zero

theorem curvLog_zero_fun (k : ℕ) (μ ν : Fin 4) :
    (fun x : LatticeTorusPlancherel.Grid 4 (k + 1) => curvLog (k + 1) (fun _ _ => (0 : ℝ)) x μ ν) =
      fun _ => 0 :=
  funext fun x => curvLog_zero x μ ν

/-- Non-vacuity of `native_YM_curvature_identification`: the zero connections (in `𝔸 = ℝ`) satisfy
its hypotheses with `A = 0`, `F = 0`. -/
example (μ ν : Fin 4) : LpTendsto volume 2 (fun k => pc (fun x => linCurl (𝔸 := ℝ) (N := k + 1)
    (fun _ _ => (0 : ℝ)) x μ ν)) (fun y => (0 : ℝ) - ((0 : ℝ) * 0 - 0 * 0)) :=
  (native_YM_curvature_identification (n := fun k => k + 1) (tendsto_add_atTop_nat 1)
    (A := fun k _ _ => (0 : ℝ)) (A₀ := fun _ _ => 0) (fun _ => lpTendsto_zero_conn 4)
    (F := fun _ _ _ => 0) (fun μ ν => by
      simp only [curvLog_zero_fun]
      exact lpTendsto_zero_conn 2) μ ν).1

end NonVacuity

end

end RenewalGeometry.NativeYMIdentification
