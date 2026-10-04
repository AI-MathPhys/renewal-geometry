/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeYangMillsIdentification

/-!
# `L^p` calculus for raw reconstructions of vector-valued grid fields on `𝕋⁴`

Generic infrastructure (no renewal notions) for the native compactness clauses of the
Einstein–SM action-closure manuscript (`prop:native-Higgs-compactness`,
`thm:native-discrete-Coulomb`, `prop:native-spinor-variation`), in the unit-torus rendering of
`Continuum/TorusTrigReconstruction.lean` (grid `(ℤ/N)⁴`, mesh `h = 1/N`).

* `gridL2Norm_inv_eq_gridNorm`, `eLpNorm_pc_four_eq` : the nodal norms `‖·‖_{2,h}`, `‖·‖_{4,h}` of
  `GridSobolev` at mesh `1/N` are the `L²`, `L⁴` norms of the raw reconstruction, for fields with
  values in any real normed space.
* `eLpNorm_pc_T` : one-step shifts preserve every `L^p` norm of raw reconstructions.
* `exists_bound_of_lpTendsto` : strongly convergent sequences are bounded.
* `lpTendsto_apply_of_bdd` (**critical coefficient product**): if `G ∈ L⁴` (operator-valued),
  `f_k → f` strongly in `L²` and `sup_k ‖f_k‖_{L⁴} < ∞`, then `G f_k → G f` strongly in `L²`
  (approximation of `G` in `L⁴` by bounded continuous coefficients).
* `lpTendsto_of_coord` : strong convergence of all coordinates of `EuclideanSpace ℝ (Fin r)`-valued
  functions gives strong convergence of the vectors.
* `lpTendsto_iff_norm_pcLp` : the two formulations of strong `L²` convergence of raw
  reconstructions (`LpTendsto` and convergence in `Lp`).
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.NativeGridLp

open TorusTrigReconstruction NativeCriticalGrid TorusPiecewiseConstantTranslation
  NativeYMIdentification

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-! ### Nodal norms and raw reconstructions -/

section Norms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ} [NeZero N]

theorem gridL2Norm_inv_eq_gridNorm (w : LatticeTorusPlancherel.Grid 4 N → E) :
    GridSobolev.gridL2Norm ((N : ℝ)⁻¹) w = gridNorm w := by
  have hN : (0 : ℝ) < (N : ℝ)⁻¹ := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  rw [GridSobolev.gridL2Norm_eq hN, gridNorm, Real.sqrt_mul (by positivity), one_div]

/-- The raw reconstruction is an isometry `L⁴_h → L⁴` (any normed fibre). -/
theorem eLpNorm_pc_four_eq (w : LatticeTorusPlancherel.Grid 4 N → E) :
    eLpNorm (pc w) 4 (volume : Measure (UnitAddTorus (Fin 4))) =
      ENNReal.ofReal (GridSobolev.gridL4Norm ((N : ℝ)⁻¹) w) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top]
  have h := lintegral_comp_index (d := Fin 4) (N := N) fun g => ‖w g‖ₑ ^ ((4 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat] at h ⊢
  change (∫⁻ y, ‖w (TorusPiecewiseConstantTranslation.index N y)‖ₑ ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) = _
  rw [h, GridSobolev.gridL4Norm, Fintype.card_fin]
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have hS : ∀ g, ‖w g‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (‖w g‖ ^ 4) := by
    intro g
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  simp_rw [hS]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => by positivity),
    ← ENNReal.ofReal_pow hN, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), one_div (N : ℝ), inv_pow]

theorem eLpNorm_pc_two_eq (w : LatticeTorusPlancherel.Grid 4 N → E) :
    eLpNorm (pc w) 2 (volume : Measure (UnitAddTorus (Fin 4))) = ENNReal.ofReal (gridNorm w) :=
  eLpNorm_pc w

/-- One-step shifts preserve the `L^p` norms of raw reconstructions. -/
theorem eLpNorm_pc_T (μ : Fin 4) (v : LatticeTorusPlancherel.Grid 4 N → E) (p : ℝ≥0∞) :
    eLpNorm (pc (T μ v)) p (volume : Measure (UnitAddTorus (Fin 4))) =
      eLpNorm (pc v) p volume := by
  have e : pc (T μ v) = fun y => pc v (y + KolmogorovRieszTorus.coordPt μ (1 / N)) :=
    funext fun y => pc_T μ v y
  rw [e]
  exact eLpNorm_comp_add (pc v) (stronglyMeasurable_pc v).aestronglyMeasurable _ p

end Norms

/-! ### Bounds and products -/

section Products

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A strongly convergent sequence is bounded in norm. -/
theorem exists_bound_of_lpTendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : ℕ → X → E} {u' : X → E}
    (hu : LpTendsto ν p u u') : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ k, eLpNorm (u k) p ν ≤ C := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hu.tendsto) 1 one_pos)
  refine ⟨(∑ k ∈ Finset.range K, eLpNorm (u k) p ν) + (1 + eLpNorm u' p ν), ?_, fun k => ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨?_, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      hu.memLp_lim.2.ne⟩⟩
    exact (ENNReal.sum_lt_top.2 fun k _ => (hu.memLp k).2).ne
  · by_cases hk : k < K
    · exact le_add_right (Finset.single_le_sum (f := fun k => eLpNorm (u k) p ν)
        (fun _ _ => zero_le) (Finset.mem_range.2 hk))
    · refine le_add_left ?_
      have h1 := hK k (not_lt.1 hk)
      calc eLpNorm (u k) p ν = eLpNorm ((u k - u') + u') p ν := by rw [sub_add_cancel]
        _ ≤ eLpNorm (u k - u') p ν + eLpNorm u' p ν :=
            eLpNorm_add_le ((hu.memLp k).1.sub hu.memLp_lim.1) hu.memLp_lim.1 Fact.out
        _ ≤ 1 + eLpNorm u' p ν := add_le_add h1 le_rfl

theorem eLpNorm_bilin_le' {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r] (B : E →L[ℝ] F →L[ℝ] W)
    {f : X → E} {g : X → F} (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) :
    eLpNorm (fun x => B (f x) (g x)) r ν ≤ ‖B‖₊ * eLpNorm f p ν * eLpNorm g q ν :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg (fun a b => B a b) ‖B‖₊
    (Eventually.of_forall fun x => by
      rw [← NNReal.coe_le_coe]; push_cast; exact B.le_opNorm₂ (f x) (g x))

end Products

section Critical

variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W]

local instance fact_one_le_four_gl : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two_gl : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder442_gl : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two
local instance holder_top22 : ENNReal.HolderTriple ∞ 2 2 := ⟨by simp⟩

/-- **The critical coefficient product**: if `G ∈ L⁴(𝕋⁴)`, `f_k → f` strongly in `L²` and
`‖f_k‖_{L⁴} ≤ C`, then `B(G, f_k) → B(G, f)` strongly in `L²` for every bounded bilinear `B`
(the limit `f` is in `L⁴` with `‖f‖_{L⁴} ≤ C`). -/
theorem lpTendsto_bilin_of_bdd (B : E →L[ℝ] F →L[ℝ] W) {G : UnitAddTorus (Fin 4) → E}
    (hG : MemLp G 4 volume) {f : ℕ → UnitAddTorus (Fin 4) → F} {f₀ : UnitAddTorus (Fin 4) → F}
    (hf : LpTendsto volume 2 f f₀) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfC : ∀ k, eLpNorm (f k) 4 volume ≤ C) (hf4 : ∀ k, MemLp (f k) 4 volume) :
    LpTendsto volume 2 (fun k y => B (G y) (f k y)) (fun y => B (G y) (f₀ y)) := by
  have hf₀ : MemLp f₀ 4 volume := hf.memLp_of_bound (by norm_num) hC hfC
  have hf₀C : eLpNorm f₀ 4 volume ≤ C := hf.eLpNorm_le_of_bound (by norm_num) hfC
  have hmem : ∀ (g : UnitAddTorus (Fin 4) → F), MemLp g 4 volume →
      MemLp (fun y => B (G y) (g y)) 2 volume := fun g hg =>
    (LpTendsto.bilin (r := 2) B (LpTendsto.const hG) (LpTendsto.const hg)).memLp_lim
  refine ⟨fun k => hmem _ (hf4 k), hmem _ hf₀, ?_⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  -- approximate `G` by a bounded continuous coefficient
  set D : ℝ≥0∞ := (‖B‖₊ : ℝ≥0∞) * (C + C) + 1
  have hD : D ≠ ∞ := by
    simp only [D]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.add_ne_top.2 ⟨hC, hC⟩), ENNReal.one_ne_top⟩
  have hD0 : D ≠ 0 := by simp [D]
  obtain ⟨G', hG', -⟩ := hG.exists_boundedContinuous_eLpNorm_sub_le (by norm_num)
    (ε := ε / 2 / D) (ENNReal.div_pos (ENNReal.half_pos hε.ne').ne' hD).ne'
  set M : ℝ := ‖G'‖
  -- the bounded part
  have hconv := hf.tendsto
  have hbd : Tendsto (fun k => (‖B‖₊ : ℝ≥0∞) * ENNReal.ofReal M * eLpNorm (f k - f₀) 2 volume)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hconv (Or.inr (ENNReal.mul_ne_top ENNReal.coe_ne_top
      ENNReal.ofReal_ne_top))
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hbd) (ε / 2) (ENNReal.half_pos hε.ne')]
    with k hk
  have hsplit : (fun y => B (G y) (f k y)) - (fun y => B (G y) (f₀ y)) =
      (fun y => B (G y - G' y) (f k y - f₀ y)) + fun y => B (G' y) (f k y - f₀ y) := by
    funext y; simp only [Pi.sub_apply, Pi.add_apply, map_sub, sub_apply]
    abel
  rw [hsplit]
  have hm1 : AEStronglyMeasurable (fun y => B (G y - G' y) (f k y - f₀ y)) volume :=
    B.continuous₂.comp_aestronglyMeasurable₂ (hG.1.sub G'.continuous.aestronglyMeasurable)
      ((hf4 k).1.sub hf₀.1)
  have hm2 : AEStronglyMeasurable (fun y => B (G' y) (f k y - f₀ y)) volume :=
    B.continuous₂.comp_aestronglyMeasurable₂ G'.continuous.aestronglyMeasurable
      ((hf4 k).1.sub hf₀.1)
  refine (eLpNorm_add_le hm1 hm2 (by norm_num)).trans ?_
  have h1 : eLpNorm (fun y => B (G y - G' y) (f k y - f₀ y)) 2 volume ≤ ε / 2 := by
    refine (eLpNorm_bilin_le' (p := 4) (q := 4) B (hG.1.sub G'.continuous.aestronglyMeasurable)
      ((hf4 k).1.sub hf₀.1)).trans ?_
    have hfk : eLpNorm (fun y => f k y - f₀ y) 4 volume ≤ C + C :=
      (eLpNorm_sub_le (hf4 k).1 hf₀.1 (by norm_num)).trans (add_le_add (hfC k) hf₀C)
    calc (‖B‖₊ : ℝ≥0∞) * eLpNorm (fun y => G y - G' y) 4 volume *
          eLpNorm (fun y => f k y - f₀ y) 4 volume
        ≤ (‖B‖₊ : ℝ≥0∞) * (ε / 2 / D) * (C + C) := by gcongr; exact hG'
      _ = ε / 2 / D * ((‖B‖₊ : ℝ≥0∞) * (C + C)) := by ring
      _ ≤ ε / 2 / D * D := by gcongr; exact le_self_add
      _ = ε / 2 := ENNReal.div_mul_cancel hD0 hD
  have h2 : eLpNorm (fun y => B (G' y) (f k y - f₀ y)) 2 volume ≤ ε / 2 := by
    refine le_trans ?_ hk
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := ‖B‖ * M) (g := f k - f₀) (Eventually.of_forall
      fun y => ?_) 2).trans (le_of_eq ?_)
    · calc ‖B (G' y) (f k y - f₀ y)‖ ≤ ‖B‖ * ‖G' y‖ * ‖f k y - f₀ y‖ := B.le_opNorm₂ _ _
        _ ≤ ‖B‖ * M * ‖(f k - f₀) y‖ := by
            gcongr
            · exact G'.norm_coe_le_norm y
            · exact le_rfl
    · rw [ENNReal.ofReal_mul (norm_nonneg B), ofReal_norm]
      rfl
  calc eLpNorm (fun y => B (G y - G' y) (f k y - f₀ y)) 2 volume +
        eLpNorm (fun y => B (G' y) (f k y - f₀ y)) 2 volume ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

end Critical

/-! ### Coordinates -/

section Coordinates

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {r : ℕ}

theorem norm_le_sum_coord (v : EuclideanSpace ℝ (Fin r)) : ‖v‖ ≤ ∑ j, ‖v j‖ := by
  rw [EuclideanSpace.norm_eq]
  refine (Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 ?_
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => ‖v i‖ * ‖v j‖)
    (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)

theorem norm_coord_le (v : EuclideanSpace ℝ (Fin r)) (j : Fin r) : ‖v j‖ ≤ ‖v‖ := by
  have := EuclideanSpace.proj (𝕜 := ℝ) j |>.le_opNorm v
  refine this.trans ?_
  have hp : ‖(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      rw [one_mul]
      simpa using (PiLp.norm_apply_le w j)
  nlinarith [norm_nonneg v]

/-- Strong convergence of all coordinates gives strong convergence of the vectors. -/
theorem lpTendsto_of_coord {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : ℕ → X → EuclideanSpace ℝ (Fin r)}
    {g₀ : X → EuclideanSpace ℝ (Fin r)} (hg : ∀ k, MemLp (g k) p ν) (hg₀ : MemLp g₀ p ν)
    (hc : ∀ j, LpTendsto ν p (fun k y => g k y j) (fun y => g₀ y j)) :
    LpTendsto ν p g g₀ := by
  refine ⟨hg, hg₀, ?_⟩
  have hsum : Tendsto (fun k => ∑ j, eLpNorm ((fun y => g k y j) - fun y => g₀ y j) p ν) atTop
      (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin r)) fun j _ => (hc j).tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun k => zero_le)
    fun k => ?_
  have hm : ∀ j, AEStronglyMeasurable ((fun y => g k y j) - fun y => g₀ y j) ν := fun j =>
    ((hc j).memLp k).1.sub (hc j).memLp_lim.1
  calc eLpNorm (g k - g₀) p ν ≤ eLpNorm (fun y => ∑ j, ‖g k y j - g₀ y j‖) p ν := by
        refine eLpNorm_mono fun y => ?_
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        refine (norm_le_sum_coord _).trans (le_of_eq ?_)
        simp only [Pi.sub_apply, PiLp.sub_apply]
    _ = eLpNorm (∑ j, fun y => ‖((fun y => g k y j) - fun y => g₀ y j) y‖) p ν := by
        congr 1; funext y; simp only [Finset.sum_apply, Pi.sub_apply]
    _ ≤ ∑ j, eLpNorm (fun y => ‖((fun y => g k y j) - fun y => g₀ y j) y‖) p ν :=
        eLpNorm_sum_le (fun j _ => (hm j).norm) Fact.out
    _ = ∑ j, eLpNorm ((fun y => g k y j) - fun y => g₀ y j) p ν := by
        refine Finset.sum_congr rfl fun j _ => eLpNorm_norm _

end Coordinates

/-! ### `LpTendsto` versus convergence in `Lp` -/

section Conversion

variable {d : ℕ} {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem lpTendsto_of_norm_pcLp {u : ∀ k, LatticeTorusPlancherel.Grid d (n k) → ℂ}
    {f : L²(UnitAddTorus (Fin d))} (h : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0)) :
    LpTendsto volume 2 (fun k => pc (u k)) (f : UnitAddTorus (Fin d) → ℂ) := by
  refine ⟨fun k => memLp_pc (u k), Lp.memLp f, ?_⟩
  have e : ∀ k, eLpNorm (pc (u k) - (f : UnitAddTorus (Fin d) → ℂ)) 2 volume =
      ENNReal.ofReal ‖pcLp (u k) - f‖ := by
    intro k
    rw [← TorusSobolev.eLpNorm_coe_sub_eq]
    refine eLpNorm_congr_ae ?_
    filter_upwards [coeFn_pcLp (u k)] with y h1
    rw [Pi.sub_apply, Pi.sub_apply, h1]
  simp only [e]
  simpa using ENNReal.tendsto_ofReal h

theorem norm_pcLp_of_lpTendsto {u : ∀ k, LatticeTorusPlancherel.Grid d (n k) → ℂ}
    {g : UnitAddTorus (Fin d) → ℂ} (h : LpTendsto volume 2 (fun k => pc (u k)) g) :
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

end Conversion

end

end RenewalGeometry.NativeGridLp
