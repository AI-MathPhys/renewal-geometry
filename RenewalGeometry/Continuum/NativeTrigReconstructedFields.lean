/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeReconstructedConsistency

/-!
# The trigonometric reconstructions of the native fields and their first jets

Generic infrastructure for the last paragraph of `thm:native-firstvariation-no-band` (Einstein–SM
action closure): the "complete unfiltered reconstructed fields" are the trigonometric interpolants
`𝓘_h^trig` (`TorusTrigReconstruction.trigInterp`) of the records and their classical derivatives.

Scalar layer (`ℂ`-valued grid functions on `(ℤ/N)⁴`, mesh `1/N`):
* `dTrig μ u` — the classical derivative `∂_μ 𝓘_h u = Σ_k 2πi k̃_μ û(k) e_{k̃}`;
* `tendsto_trigLp`, `tendsto_dTrigLp`, `tendsto_eLpNorm_four_trig`
  (`lem:native-reconstruction-identification`, reconstruction side): if `R^0 u_h → f` and
  `R^0 D⁺u_h → v` strongly in `L²`, then `𝓘_h u_h → f` in `L²` and in `L⁴` and
  `∂_μ 𝓘_h u_h → v_μ` in `L²`;
* `norm_trigLp_eq`, `norm_dTrigLp_le`, `eLpNorm_four_trig_le`: the uniform `L²`, `H¹` and critical
  `L⁴` bounds of the interpolant in terms of `‖u‖_{2,h}`, `‖D⁺u‖_{2,h}`;
* `weak_dTrig_sub_pc`: under uniform bounds of `u_h`, `D⁺u_h`, `∂_μ 𝓘_h u_h - R^0 D⁺_μ u_h ⇀ 0`
  weakly in `L²` (`eq:native-reconstruction-comparison` at the level of first jets).
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal NNReal RealInnerProductSpace
open NormedSpace (exp)

namespace RenewalGeometry.NativeTrigRec

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

open TorusTrigReconstruction TorusPiecewiseConstantTranslation LatticeTorusPlancherel TorusSobolev
  TorusCellEmbedding

/-! ### Scalar layer -/

section Scalar

variable {N : ℕ} [NeZero N]

/-- The represented frequencies `{k̃}`. -/
def freqs (N : ℕ) [NeZero N] : Finset (Fin 4 → ℤ) := (univ : Finset (Grid 4 N)).image signedRep

theorem coef_eq_zero_of_not_freqs (u : Grid 4 N → ℂ) {m : Fin 4 → ℤ} (hm : m ∉ freqs N) :
    coef u m = 0 := coef_eq_zero_of_not_mem u hm

theorem trigInterp_eq_trigPoly (u : Grid 4 N → ℂ) : trigInterp u = trigPoly (freqs N) (coef u) := by
  unfold trigInterp trigPoly freqs
  rw [Finset.sum_image (fun k _ k' _ h => signedRep_injective h)]
  exact Finset.sum_congr rfl fun k _ => by rw [coef_signedRep]

/-- The coefficients `2πi m_μ coef u m` of the derivative of the interpolant. -/
def dCoef (μ : Fin 4) (u : Grid 4 N → ℂ) (m : Fin 4 → ℤ) : ℂ :=
  2 * π * Complex.I * m μ * coef u m

/-- **The classical derivative `∂_μ 𝓘_h u` of the trigonometric interpolant.** -/
def dTrig (μ : Fin 4) (u : Grid 4 N → ℂ) : C(𝕋, ℂ) := trigPoly (freqs N) (dCoef μ u)

def dTrigLp (μ : Fin 4) (u : Grid 4 N → ℂ) : L²(𝕋) := ContinuousMap.toLp 2 volume ℂ (dTrig μ u)

theorem mFourierCoeff_dTrigLp (μ : Fin 4) (u : Grid 4 N → ℂ) (m : Fin 4 → ℤ) :
    mFourierCoeff (dTrigLp μ u) m = dCoef μ u m := by
  rw [dTrigLp, mFourierCoeff_toLp, dTrig, mFourierCoeff_trigPoly]
  split_ifs with h
  · rfl
  · simp [dCoef, coef_eq_zero_of_not_freqs u h]

theorem coeFn_dTrigLp (μ : Fin 4) (u : Grid 4 N → ℂ) :
    ((dTrigLp μ u : L²(𝕋)) : 𝕋 → ℂ) =ᵐ[volume] dTrig μ u :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (dTrig μ u)

theorem norm_Lp_sub_sq (f g : L²(𝕋)) :
    ‖f - g‖ ^ 2 = ∑' m, ‖mFourierCoeff f m - mFourierCoeff g m‖ ^ 2 := by
  have h := KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (f - g)
  rw [← h.tsum_eq]
  congr 1
  funext m
  rw [TorusSobolev.mFourierCoeff_Lp_sub]

/-- `𝓘_h u_h → f` in `L²`. -/
theorem tendsto_trigLp {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → ℂ} {f : L²(𝕋)}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0)) :
    Tendsto (fun k => ‖trigLp (u k) - f‖) atTop (𝓝 0) := by
  have h := tendsto_tsum_coef_sub_sq hn hu
  have h2 : Tendsto (fun k => ‖trigLp (u k) - f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_trigLp_sub_sq] using h
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h3

/-- `∂_μ 𝓘_h u_h → v_μ` in `L²` when `R^0 D⁺_μ u_h → v_μ`. -/
theorem tendsto_dTrigLp {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → ℂ} {f : L²(𝕋)} {v : Fin 4 → L²(𝕋)}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0))
    (hv : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (u k)) - v μ‖) atTop (𝓝 0)) (μ : Fin 4) :
    Tendsto (fun k => ‖dTrigLp μ (u k) - v μ‖) atTop (𝓝 0) := by
  have hvs : Summable fun m => ‖mFourierCoeff (v μ) m‖ ^ 2 :=
    (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (v μ)).summable
  have h1 := tendsto_tsum_coef_sub_sq hn (hv μ)
  have h2 := tendsto_tsum_sq_mul_sub (x := fun k => coef (Dp μ (u k)))
    (x₀ := fun m => mFourierCoeff (v μ) m) (m := fun k => symRatio (n k) μ)
    (m₀ := fun m => if m μ = 0 then 0 else 1) (M := π / 2)
    (fun k => summable_norm_sub_sq (summable_coef_sq _) hvs) hvs h1
    (fun k m => norm_symRatio_le _ _ _) (fun m => tendsto_symRatio hn μ m)
  have h3 : Tendsto (fun k => ‖dTrigLp μ (u k) - v μ‖ ^ 2) atTop (𝓝 0) := by
    refine h2.congr fun k => ?_
    rw [norm_Lp_sub_sq]
    refine tsum_congr fun m => ?_
    rw [mFourierCoeff_dTrigLp, symRatio_mul_coef_Dp, dCoef,
      mFourierCoeff_eq_of_tendsto hn hu (hv μ)]
    congr 2
    split_ifs with h0
    · simp [h0]
    · ring
  have h4 := (Real.continuous_sqrt.tendsto 0).comp h3
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h4

/-- Parseval: `‖𝓘_h u‖_{L²} = ‖u‖_{2,h}`. -/
theorem norm_trigLp_eq (u : Grid 4 N → ℂ) : ‖trigLp u‖ = gridNorm u := by
  have h := KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (trigLp u)
  simp only [mFourierCoeff_trigLp] at h
  have h2 := h.unique (hasSum_coef_sq u)
  have := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (gridNorm_nonneg _)] at this

/-- `‖∂_μ 𝓘_h u‖_{L²} ≤ (π/2) ‖D⁺_μ u‖_{2,h}`. -/
theorem norm_dTrigLp_le (μ : Fin 4) (u : Grid 4 N → ℂ) :
    ‖dTrigLp μ u‖ ≤ π / 2 * gridNorm (Dp μ u) := by
  have h := KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (dTrigLp μ u)
  simp only [mFourierCoeff_dTrigLp] at h
  have hle : ∀ m, ‖dCoef μ u m‖ ^ 2 ≤ (π / 2) ^ 2 * ‖coef (Dp μ u) m‖ ^ 2 := by
    intro m
    rw [dCoef, ← symRatio_mul_coef_Dp, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_symRatio_le _ _ _) 2)
      (sq_nonneg _)
  have hs := ((hasSum_coef_sq (Dp μ u)).mul_left ((π / 2) ^ 2))
  have hsq : ‖dTrigLp μ u‖ ^ 2 ≤ (π / 2) ^ 2 * gridNorm (Dp μ u) ^ 2 :=
    hasSum_le hle h hs
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    Real.sqrt_sq (gridNorm_nonneg _)] at this

/-- **The critical `L⁴` bound of the interpolant**:
`‖𝓘_h u‖_{L⁴} ≤ 3 (π/2) Σ_μ ‖D⁺_μ u‖_{2,h} + 4 ‖u‖_{2,h}`. -/
theorem eLpNorm_four_trig_le (u : Grid 4 N → ℂ) :
    eLpNorm (trigInterp u) 4 volume ≤
      ENNReal.ofReal (3 * ∑ μ, π / 2 * gridNorm (Dp μ u) + 4 * gridNorm u) := by
  rw [trigInterp_eq_trigPoly]
  refine (NativeCoulomb.eLpNorm_four_trigPoly_le (freqs N) (coef u)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h1 : ∀ μ, ‖ContinuousMap.toLp 2 volume ℂ
      (trigPoly (freqs N) (fun m => 2 * π * Complex.I * m μ * coef u m))‖ ≤
        π / 2 * gridNorm (Dp μ u) := fun μ => norm_dTrigLp_le μ u
  have h2 : ‖ContinuousMap.toLp 2 volume ℂ (trigPoly (freqs N) (coef u))‖ = gridNorm u := by
    rw [← trigInterp_eq_trigPoly]; exact norm_trigLp_eq u
  rw [h2]
  gcongr with μ
  exact h1 μ

end Scalar

/-! ### Strong `L⁴` convergence of the interpolants -/

section L4

variable {N : ℕ} [NeZero N]

theorem trigPoly_sub' (S : Finset (Fin 4 → ℤ)) (c c' : (Fin 4 → ℤ) → ℂ) :
    trigPoly S (fun m => c m - c' m) = trigPoly S c - trigPoly S c' := by
  unfold trigPoly
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => sub_smul _ _ _

theorem trigPoly_subset {S T : Finset (Fin 4 → ℤ)} (hST : S ⊆ T) (c : (Fin 4 → ℤ) → ℂ)
    (hc : ∀ m ∈ T, m ∉ S → c m = 0) : trigPoly S c = trigPoly T c := by
  unfold trigPoly
  refine Finset.sum_subset hST fun m hT hS => ?_
  rw [hc m hT hS, zero_smul]

/-- The interpolant minus a truncation is a trigonometric polynomial on `freqs ∪ box R`. -/
theorem trig_sub_trunc (u : Grid 4 N → ℂ) (R : ℕ) (a : (Fin 4 → ℤ) → ℂ) :
    trigInterp u - trigPoly (TorusSobolev.box R) a =
      trigPoly (freqs N ∪ TorusSobolev.box R)
        (fun m => coef u m - if m ∈ TorusSobolev.box R then a m else 0) := by
  have h1 : trigInterp u = trigPoly (freqs N ∪ TorusSobolev.box R) (coef u) := by
    rw [trigInterp_eq_trigPoly]
    exact trigPoly_subset Finset.subset_union_left _ fun m _ hm => coef_eq_zero_of_not_freqs u hm
  have h2 : trigPoly (TorusSobolev.box R) a = trigPoly (freqs N ∪ TorusSobolev.box R)
      (fun m => if m ∈ TorusSobolev.box R then a m else 0) := by
    rw [← trigPoly_subset Finset.subset_union_right _ fun m _ hm => if_neg hm]
    unfold trigPoly
    exact Finset.sum_congr rfl fun m hm => by simp only [if_pos hm]
  rw [h1, h2, ← trigPoly_sub']

theorem dTrig_sub_trunc (μ : Fin 4) (u : Grid 4 N → ℂ) (R : ℕ) (a : (Fin 4 → ℤ) → ℂ) :
    dTrig μ u - trigPoly (TorusSobolev.box R) (fun m => 2 * π * Complex.I * m μ * a m) =
      trigPoly (freqs N ∪ TorusSobolev.box R) (fun m => 2 * π * Complex.I * m μ *
        (coef u m - if m ∈ TorusSobolev.box R then a m else 0)) := by
  have e : (fun m : Fin 4 → ℤ => 2 * π * Complex.I * m μ *
      (coef u m - if m ∈ TorusSobolev.box R then a m else 0)) =
      fun m => dCoef μ u m - if m ∈ TorusSobolev.box R then 2 * π * Complex.I * m μ * a m
        else 0 := by
    funext m; simp only [dCoef]; split_ifs <;> ring
  have h1 : dTrig μ u = trigPoly (freqs N ∪ TorusSobolev.box R) (dCoef μ u) := by
    rw [dTrig]
    exact trigPoly_subset Finset.subset_union_left _ fun m _ hm => by
      simp [dCoef, coef_eq_zero_of_not_freqs u hm]
  have h2 : trigPoly (TorusSobolev.box R) (fun m => 2 * π * Complex.I * m μ * a m) =
      trigPoly (freqs N ∪ TorusSobolev.box R)
        (fun m => if m ∈ TorusSobolev.box R then 2 * π * Complex.I * m μ * a m else 0) := by
    rw [← trigPoly_subset Finset.subset_union_right _ fun m _ hm => if_neg hm]
    unfold trigPoly
    exact Finset.sum_congr rfl fun m hm => by simp only [if_pos hm]
  rw [e, h1, h2, ← trigPoly_sub']

local instance fact_one_le_four_tr : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- **`𝓘_h u_h → f` strongly in `L⁴`** (critical Sobolev on trigonometric polynomials plus the
critical embedding of the limit). -/
theorem tendsto_eLpNorm_four_trig {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → ℂ} {f : L²(𝕋)} {v : Fin 4 → L²(𝕋)}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0))
    (hv : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (u k)) - v μ‖) atTop (𝓝 0)) :
    MemLp (f : 𝕋 → ℂ) 4 volume ∧
      Tendsto (fun k => eLpNorm (fun y => trigInterp (u k) y - f y) 4 volume) atTop (𝓝 0) := by
  have hf := memH_one_of_tendsto hn hu hv
  obtain ⟨hf4, htr⟩ := NativeCoulomb.tendsto_eLpNorm_four_trunc hf
  refine ⟨hf4, ?_⟩
  have hvc : ∀ μ m, mFourierCoeff (v μ) m = 2 * π * Complex.I * m μ * mFourierCoeff f m :=
    fun μ m => mFourierCoeff_eq_of_tendsto hn hu (hv μ) m
  set P : ℕ → C(𝕋, ℂ) := fun R => trigPoly (TorusSobolev.box R) (mFourierCoeff f) with hP
  -- the pointwise bound
  have hbound : ∀ k R, eLpNorm (fun y => trigInterp (u k) y - f y) 4 volume ≤
      ENNReal.ofReal (3 * ∑ μ, (‖dTrigLp μ (u k) - v μ‖ + ‖v μ - ContinuousMap.toLp 2 volume ℂ
          (trigPoly (TorusSobolev.box R) (mFourierCoeff (v μ)))‖) +
        4 * (‖trigLp (u k) - f‖ + ‖f - ContinuousMap.toLp 2 volume ℂ (P R)‖)) +
      eLpNorm (fun y => P R y - f y) 4 volume := by
    intro k R
    have hsplit : (fun y => trigInterp (u k) y - f y) =
        (fun y => (trigInterp (u k) - P R) y) + fun y => P R y - f y := by
      funext y; simp
    rw [hsplit]
    refine (eLpNorm_add_le ((trigInterp (u k) - P R).continuous.aestronglyMeasurable)
      ((P R).continuous.aestronglyMeasurable.sub (Lp.aestronglyMeasurable f)) (by norm_num)).trans
      (add_le_add ?_ le_rfl)
    have heq := trig_sub_trunc (u k) R (mFourierCoeff f)
    rw [heq]
    refine (NativeCoulomb.eLpNorm_four_trigPoly_le _ _).trans (ENNReal.ofReal_le_ofReal ?_)
    have e1 : ContinuousMap.toLp 2 volume ℂ (trigPoly (freqs (n k) ∪ TorusSobolev.box R)
        (fun m => coef (u k) m - if m ∈ TorusSobolev.box R then mFourierCoeff f m else 0)) =
        trigLp (u k) - ContinuousMap.toLp 2 volume ℂ (P R) := by
      rw [← heq, map_sub]; rfl
    have e2 : ∀ μ, ContinuousMap.toLp 2 volume ℂ (trigPoly (freqs (n k) ∪ TorusSobolev.box R)
        (fun m => 2 * π * Complex.I * m μ * (coef (u k) m -
          if m ∈ TorusSobolev.box R then mFourierCoeff f m else 0))) =
        dTrigLp μ (u k) - ContinuousMap.toLp 2 volume ℂ
          (trigPoly (TorusSobolev.box R) (mFourierCoeff (v μ))) := by
      intro μ
      have : trigPoly (TorusSobolev.box R) (mFourierCoeff (v μ)) =
          trigPoly (TorusSobolev.box R) (fun m => 2 * π * Complex.I * m μ * mFourierCoeff f m) := by
        unfold trigPoly; exact Finset.sum_congr rfl fun m _ => by rw [hvc]
      rw [this, ← dTrig_sub_trunc, map_sub]; rfl
    simp only [e1, e2]
    have n1 : ‖trigLp (u k) - ContinuousMap.toLp 2 volume ℂ (P R)‖ ≤
        ‖trigLp (u k) - f‖ + ‖f - ContinuousMap.toLp 2 volume ℂ (P R)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have n2 : ∀ μ, ‖dTrigLp μ (u k) - ContinuousMap.toLp 2 volume ℂ
        (trigPoly (TorusSobolev.box R) (mFourierCoeff (v μ)))‖ ≤
        ‖dTrigLp μ (u k) - v μ‖ + ‖v μ - ContinuousMap.toLp 2 volume ℂ
          (trigPoly (TorusSobolev.box R) (mFourierCoeff (v μ)))‖ :=
      fun μ => norm_sub_le_norm_sub_add_norm_sub _ _ _
    gcongr with μ
    exact n2 μ
  -- the limit
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  set δ := ε.toReal / 4
  have hδ : 0 < δ := by positivity
  -- choose `R`
  have hα := TorusTrigReconstruction.tendsto_norm_sub_trigPoly_box f
  have hβ := fun μ => TorusTrigReconstruction.tendsto_norm_sub_trigPoly_box (v μ)
  have hγ : Tendsto (fun R => (eLpNorm (fun y => P R y - f y) 4 volume).toReal) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htr
  have hRall : Tendsto (fun R => 3 * ∑ μ, ‖v μ - ContinuousMap.toLp 2 volume ℂ
      (trigPoly (TorusSobolev.box R) (mFourierCoeff (v μ)))‖ +
      4 * ‖f - ContinuousMap.toLp 2 volume ℂ (P R)‖ +
      (eLpNorm (fun y => P R y - f y) 4 volume).toReal) atTop (𝓝 0) := by
    have h1 := ((tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun μ _ => hβ μ).const_mul 3)
    have h2 := hα.const_mul 4
    simpa using (h1.add h2).add hγ
  obtain ⟨R, hR⟩ := ((tendsto_order.1 hRall).2 δ hδ).exists
  have hk : Tendsto (fun k => 3 * ∑ μ, ‖dTrigLp μ (u k) - v μ‖ + 4 * ‖trigLp (u k) - f‖) atTop
      (𝓝 0) := by
    have h1 := (tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun μ _ =>
      tendsto_dTrigLp hn hu hv μ).const_mul 3
    have h2 := (tendsto_trigLp hn hu).const_mul 4
    simpa using h1.add h2
  filter_upwards [(tendsto_order.1 hk).2 δ hδ] with k hk'
  have hPm : MemLp (fun y => P R y) 4 (volume : Measure 𝕋) :=
    MemLp.of_bound (P R).continuous.aestronglyMeasurable ‖P R‖
      (Eventually.of_forall fun y => (P R).norm_coe_le_norm y)
  have hfin : eLpNorm (fun y => P R y - f y) 4 volume ≠ ⊤ := (hPm.sub hf4).eLpNorm_ne_top
  refine (hbound k R).trans ?_
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg]
  refine (ENNReal.ofReal_le_ofReal (show _ ≤ 2 * δ from ?_)).trans ?_
  · rw [Finset.sum_add_distrib]
    linarith
  · refine ENNReal.ofReal_le_of_le_toReal ?_
    simp only [δ]
    linarith

end L4

/-! ### Weak comparison of the first jets -/

section Weak

theorem mFourierCoeff_congr {f g : 𝕋 → ℂ} (h : f =ᵐ[volume] g) (m : Fin 4 → ℤ) :
    mFourierCoeff f m = mFourierCoeff g m := by
  unfold mFourierCoeff
  exact integral_congr_ae (h.mono fun y hy => by simp only [hy])

theorem norm_coef_le {N : ℕ} [NeZero N] (u : Grid 4 N → ℂ) (m : Fin 4 → ℤ) :
    ‖coef u m‖ ≤ gridNorm u := by
  have h := (hasSum_coef_sq u).summable.le_tsum m (fun j _ => sq_nonneg _)
  rw [tsum_coef_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (gridNorm_nonneg _) two_ne_zero).1 h

theorem pc_Dp_eq_DpV {N : ℕ} [NeZero N] (μ : Fin 4) (u : Grid 4 N → ℂ) :
    pc (Dp μ u) = pc (NativeHiggs.DpV μ u) := by
  funext y
  simp only [pc, Dp_apply, NativeHiggs.DpV, Complex.real_smul]
  push_cast
  ring

theorem mFourierCoeff_pcLp_Dp {N : ℕ} [NeZero N] (μ : Fin 4) (u : Grid 4 N → ℂ)
    (m : Fin 4 → ℤ) :
    mFourierCoeff (pcLp (Dp μ u)) m = sym N μ m * mFourierCoeff (pcLp u) m := by
  rw [mFourierCoeff_congr (coeFn_pcLp _), mFourierCoeff_congr (coeFn_pcLp _), pc_Dp_eq_DpV,
    NativeCoulomb.mFourierCoeff_pc_DpV, smul_eq_mul]

/-- Each Fourier coefficient of `∂_μ 𝓘_h u_h - R^0 D⁺_μ u_h` tends to zero under a uniform bound. -/
theorem tendsto_coef_jet_diff {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → ℂ} {B : ℝ} (hu : ∀ k, gridNorm (u k) ≤ B) (μ : Fin 4)
    (m : Fin 4 → ℤ) :
    Tendsto (fun k => mFourierCoeff (dTrigLp μ (u k) - pcLp (Dp μ (u k))) m) atTop (𝓝 0) := by
  have e : ∀ k, mFourierCoeff (dTrigLp μ (u k) - pcLp (Dp μ (u k))) m =
      (2 * π * Complex.I * m μ - sym (n k) μ m) * coef (u k) m +
        sym (n k) μ m * (coef (u k) m - mFourierCoeff (pcLp (u k)) m) := by
    intro k
    rw [TorusSobolev.mFourierCoeff_Lp_sub, mFourierCoeff_dTrigLp, mFourierCoeff_pcLp_Dp, dCoef]
    ring
  simp only [e]
  have hs := tendsto_sym hn μ m
  -- the coefficient comparison
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hc : Tendsto (fun k => coef (u k) m - mFourierCoeff (pcLp (u k)) m) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    set c := 2 * π * (∑ i, |(m i : ℝ)|)
    have hlim : Tendsto (fun k => c / (n k : ℝ) * B) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop hn').mul_const B
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_two_abs_lt hn m] with k hk
    rw [coef_eq, if_pos (TorusTrigReconstruction.signedRep_zcast hk)]
    refine (norm_dft_sub_mFourierCoeff_le (u k) (pcLp (u k)) m).trans ?_
    rw [sub_self, norm_zero, add_zero]
    exact mul_le_mul_of_nonneg_left (hu k) (by positivity)
  -- the first term
  have hB : ∀ k, ‖coef (u k) m‖ ≤ B := fun k => (norm_coef_le _ _).trans (hu k)
  have h1 : Tendsto (fun k => (2 * π * Complex.I * m μ - sym (n k) μ m) * coef (u k) m) atTop
      (𝓝 0) := by
    have h0 : Tendsto (fun k => 2 * π * Complex.I * m μ - sym (n k) μ m) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 2 * π * Complex.I * (m μ : ℂ))).sub hs
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, norm_mul]
    have h0' := (h0.norm).mul_const B
    simp only [norm_zero, zero_mul] at h0'
    exact squeeze_zero (fun k => by positivity)
      (fun k => mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _)) h0'
  simpa using h1.add (hs.mul hc)

/-- **Weak comparison of the first jets**: under uniform bounds of `u_h` and `D⁺_μ u_h`,
`∂_μ 𝓘_h u_h - R^0 D⁺_μ u_h ⇀ 0` weakly in `L²`. -/
theorem weak_dTrig_sub_pc {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → ℂ} {B : ℝ} (μ : Fin 4) (hu : ∀ k, gridNorm (u k) ≤ B)
    (hDu : ∀ k, gridNorm (Dp μ (u k)) ≤ B) (g : L²(𝕋)) :
    Tendsto (fun k => inner ℂ g (dTrigLp μ (u k) - pcLp (Dp μ (u k)))) atTop (𝓝 0) := by
  set h : ℕ → L²(𝕋) := fun k => dTrigLp μ (u k) - pcLp (Dp μ (u k)) with hh
  have hB : ∀ k, ‖h k‖ ≤ (π / 2 + 1) * B := by
    intro k
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pcLp]
    have := norm_dTrigLp_le μ (u k)
    nlinarith [hDu k, Real.pi_pos]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C := (π / 2 + 1) * |B| + 1 with hC
  have hC0 : 0 < C := by positivity
  obtain ⟨R, hR⟩ := ((tendsto_order.1 (tendsto_norm_sub_trigPoly_box g)).2 (ε / (2 * C))
    (by positivity)).exists
  set P : L²(𝕋) := ContinuousMap.toLp 2 volume ℂ (trigPoly (TorusSobolev.box R) (mFourierCoeff g))
  have hPform : ∀ k, inner ℂ P (h k) = ∑ m ∈ TorusSobolev.box R,
      (starRingEnd ℂ) (mFourierCoeff g m) * mFourierCoeff (h k) m := by
    intro k
    have : P = ∑ m ∈ TorusSobolev.box R, mFourierCoeff g m • mFourierLp 2 m := by
      simp only [P, trigPoly, map_sum, map_smul]
    rw [this, sum_inner]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_smul_left, ← mFourierCoeff_eq_inner']
  have hfin : Tendsto (fun k => inner ℂ P (h k)) atTop (𝓝 0) := by
    simp only [hPform]
    have := tendsto_finsetSum (TorusSobolev.box R) fun m (_ : m ∈ TorusSobolev.box R) =>
      (tendsto_const_nhds (x := (starRingEnd ℂ) (mFourierCoeff g m))).mul
        (tendsto_coef_jet_diff hn hu μ m)
    simp only [mul_zero, Finset.sum_const_zero] at this
    exact this
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hfin) (ε / 2) (by positivity)
  refine ⟨K, fun k hk => ?_⟩
  rw [dist_zero_right]
  have hsplit : inner ℂ g (h k) = inner ℂ (g - P) (h k) + inner ℂ P (h k) := by
    rw [inner_sub_left]; ring
  rw [hsplit]
  have h1 : ‖inner ℂ (g - P) (h k)‖ ≤ ε / (2 * C) * C := by
    refine (norm_inner_le_norm _ _).trans ?_
    refine mul_le_mul hR.le ((hB k).trans ?_) (norm_nonneg _) (by positivity)
    rw [hC]
    nlinarith [le_abs_self B, Real.pi_pos]
  have h2 := hK k hk
  rw [dist_zero_right] at h2
  calc _ ≤ ‖inner ℂ (g - P) (h k)‖ + ‖inner ℂ P (h k)‖ := norm_add_le _ _
    _ < ε / (2 * C) * C + ε / 2 := by linarith
    _ = ε := by field_simp; ring

end Weak

/-! ### Conversions between `Lp` norms and strong convergence -/

section Conv

local instance fact_one_le_two_cv : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_cv : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

theorem norm_tendsto_of_lpTendsto {n : ℕ → ℕ} [∀ k, NeZero (n k)] {w : ∀ k, Grid 4 (n k) → ℂ}
    {g : 𝕋 → ℂ} (h : LpTendsto volume 2 (fun k => pc (w k)) g) :
    Tendsto (fun k => ‖pcLp (w k) - h.memLp_lim.toLp g‖) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.1
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun k => memLp_pc (w k)) g h.memLp_lim).2 h.tendsto)

theorem lpTendsto_of_norm {F : ℕ → L²(𝕋)} {g : L²(𝕋)}
    (h : Tendsto (fun k => ‖F k - g‖) atTop (𝓝 0)) :
    LpTendsto volume 2 (fun k => ⇑(F k)) ⇑g := by
  refine ⟨fun k => Lp.memLp _, Lp.memLp _, ?_⟩
  simp only [TorusSobolev.eLpNorm_coe_sub_eq]
  simpa using ENNReal.tendsto_ofReal h

end Conv

/-! ### Vector-valued reconstructions -/

section Vector


local instance fact_one_le_two_vc : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_vc : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {N : ℕ} [NeZero N]

/-- The `i`-th complexified coordinate of a `V`-valued grid field (fixed basis
`Module.finBasis ℝ V`). -/
def comp (i : Fin (Module.finrank ℝ V)) (u : Grid 4 N → V) : Grid 4 N → ℂ :=
  fun x => ((Module.finBasis ℝ V).coord i (u x) : ℂ)

/-- **The trigonometric reconstruction `𝓘_h u` of a `V`-valued grid field** (componentwise, real
parts of the scalar interpolants). -/
def recon (u : Grid 4 N → V) (z : 𝕋) : V :=
  ∑ i, (trigInterp (comp i u) z).re • (Module.finBasis ℝ V) i

/-- **Its classical first jet `∂_μ 𝓘_h u`.** -/
def drecon (μ : Fin 4) (u : Grid 4 N → V) (z : 𝕋) : V :=
  ∑ i, (dTrig μ (comp i u) z).re • (Module.finBasis ℝ V) i

/-- The coordinate functional as a continuous linear map to `ℂ`. -/
def coordC (i : Fin (Module.finrank ℝ V)) : V →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ V).coord i))

theorem coordC_apply (i : Fin (Module.finrank ℝ V)) (v : V) :
    coordC i v = ((Module.finBasis ℝ V).coord i v : ℂ) := rfl

theorem Dp_comp (μ : Fin 4) (i : Fin (Module.finrank ℝ V)) (u : Grid 4 N → V) :
    Dp μ (comp i u) = comp i (ShiftedJetAction.fwdDiff (N : ℝ)⁻¹ μ u) := by
  funext x
  simp only [Dp_apply, comp, ShiftedJetAction.fwdDiff, ShiftedJetAction.unitVec, map_smul,
    map_sub, inv_inv, smul_eq_mul]
  push_cast
  ring

theorem sum_coord_smul (v : V) : ∑ i, (Module.finBasis ℝ V).coord i v • (Module.finBasis ℝ V) i = v :=
  (Module.finBasis ℝ V).sum_repr v

/-- Componentwise assembly of strong convergence. -/
theorem lpTendsto_assemble {p : ℝ≥0∞} [Fact (1 ≤ p)] {w : Fin (Module.finrank ℝ V) → ℕ → 𝕋 → ℂ}
    {f : 𝕋 → V} (hw : ∀ i, LpTendsto volume p (w i) (fun z => coordC i (f z))) :
    LpTendsto volume p (fun k z => ∑ i, (w i k z).re • (Module.finBasis ℝ V) i) f := by
  have h := NativeDiracConv.lpTendsto_finset_sum (p := p) Finset.univ fun i _ =>
    (hw i).clm ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((Module.finBasis ℝ V) i)).comp
      Complex.reCLM)
  refine h.congr (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · simp
  · simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, coordC_apply,
      Complex.ofReal_re, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
    exact sum_coord_smul (f z)

/-- **Strong convergence of the reconstructions and their jets** (`V`-valued
`lem:native-reconstruction-identification`): if `R^0 u_h → f` and `R^0 D⁺_μ u_h → v_μ` strongly in
`L²`, then `𝓘_h u_h → f` in `L²` and `L⁴`, and `∂_μ 𝓘_h u_h → v_μ` in `L²`. -/
theorem recon_tendsto {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → V} {f : 𝕋 → V} {v : Fin 4 → 𝕋 → V}
    (hu : LpTendsto volume 2 (fun k => pc (u k)) f)
    (hv : ∀ μ, LpTendsto volume 2 (fun k => pc (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (u k))) (v μ)) :
    LpTendsto volume 2 (fun k => recon (u k)) f ∧ LpTendsto volume 4 (fun k => recon (u k)) f ∧
      ∀ μ, LpTendsto volume 2 (fun k => drecon μ (u k)) (v μ) := by
  -- scalar components
  have hci : ∀ i, LpTendsto volume 2 (fun k => pc (comp i (u k))) (fun z => coordC i (f z)) :=
    fun i => hu.clm (coordC i)
  have hdi : ∀ i μ, LpTendsto volume 2 (fun k => pc (Dp μ (comp i (u k))))
      (fun z => coordC i (v μ z)) := fun i μ => by
    have := (hv μ).clm (coordC i)
    refine this.congr (fun k => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    rw [Dp_comp]; rfl
  have nci := fun i => norm_tendsto_of_lpTendsto (hci i)
  have ndi := fun i μ => norm_tendsto_of_lpTendsto (hdi i μ)
  refine ⟨?_, ?_, fun μ => ?_⟩
  · refine lpTendsto_assemble fun i => ?_
    refine (lpTendsto_of_norm (tendsto_trigLp hn (nci i))).congr
      (fun k => coeFn_trigLp _) ?_
    exact (hci i).memLp_lim.coeFn_toLp
  · refine lpTendsto_assemble fun i => ?_
    obtain ⟨h4, ht⟩ := tendsto_eLpNorm_four_trig hn (nci i) (fun μ => ndi i μ)
    refine ⟨fun k => ?_, h4.ae_eq (hci i).memLp_lim.coeFn_toLp, ?_⟩
    · exact MemLp.of_bound (trigInterp _).continuous.aestronglyMeasurable ‖trigInterp (comp i (u k))‖
        (Eventually.of_forall fun y => (trigInterp _).norm_coe_le_norm y)
    · refine ht.congr fun k => eLpNorm_congr_ae ?_
      filter_upwards [(hci i).memLp_lim.coeFn_toLp] with y hy
      simp only [Pi.sub_apply, hy]
  · refine lpTendsto_assemble fun i => ?_
    refine (lpTendsto_of_norm (tendsto_dTrigLp hn (nci i) (fun μ => ndi i μ) μ)).congr
      (fun k => coeFn_dTrigLp _ _) ?_
    exact (hdi i μ).memLp_lim.coeFn_toLp

theorem gridNorm_comp_le (i : Fin (Module.finrank ℝ V)) (u : Grid 4 N → V) :
    gridNorm (comp i u) ≤ ‖coordC (V := V) i‖ * gridNorm u := by
  have h := gridNorm_mono (u := comp i u) (v := fun x => ‖coordC (V := V) i‖ * ‖u x‖)
    fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact (coordC i).le_opNorm (u x)
  refine h.trans (le_of_eq ?_)
  rw [gridNorm_const_mul (fun x => ‖u x‖) (norm_nonneg _)]
  congr 1
  unfold gridNorm; simp

/-- **Uniform critical `L⁴` bound of the reconstructions** from uniform discrete `H¹` bounds. -/
theorem recon_eLpNorm_four_bounded {n : ℕ → ℕ} [∀ k, NeZero (n k)] {u : ∀ k, Grid 4 (n k) → V}
    {B : ℝ} (hu : ∀ k, gridNorm (u k) ≤ B)
    (hDu : ∀ k μ, gridNorm (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (u k)) ≤ B) :
    ∃ B4 : ℝ≥0∞, B4 ≠ ⊤ ∧ ∀ k, eLpNorm (recon (u k)) 4 volume ≤ B4 := by
  set K : ℝ := ∑ i, ‖(Module.finBasis ℝ V) i‖ * (3 * ∑ _μ : Fin 4, π / 2 *
    (‖coordC (V := V) i‖ * |B|) + 4 * (‖coordC (V := V) i‖ * |B|))
  refine ⟨ENNReal.ofReal K, ENNReal.ofReal_ne_top, fun k => ?_⟩
  have hsum : eLpNorm (recon (u k)) 4 volume ≤ ∑ i, eLpNorm (fun z =>
      (trigInterp (comp i (u k)) z).re • (Module.finBasis ℝ V) i) 4 volume := by
    have := eLpNorm_sum_le (μ := (volume : Measure 𝕋)) (s := Finset.univ) (f := fun i z =>
      (trigInterp (comp i (u k)) z).re • (Module.finBasis ℝ V) i)
      (fun i _ => ((Complex.continuous_re.comp (trigInterp _).continuous).smul
        continuous_const).aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
    refine le_of_eq_of_le ?_ this
    congr 1; funext z; simp [recon]
  refine hsum.trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : eLpNorm (fun z => (trigInterp (comp i (u k)) z).re • (Module.finBasis ℝ V) i) 4 volume ≤
      ENNReal.ofReal ‖(Module.finBasis ℝ V) i‖ * eLpNorm (trigInterp (comp i (u k))) 4 volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => by
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)) 4
  refine h1.trans ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _)]
  refine mul_le_mul' le_rfl ((eLpNorm_four_trig_le _).trans (ENNReal.ofReal_le_ofReal ?_))
  have hc := gridNorm_comp_le i (u k)
  have hd : ∀ μ, gridNorm (Dp μ (comp i (u k))) ≤ ‖coordC (V := V) i‖ * |B| := fun μ => by
    rw [Dp_comp]
    exact (gridNorm_comp_le i _).trans (mul_le_mul_of_nonneg_left ((hDu k μ).trans
      (le_abs_self B)) (norm_nonneg _))
  have hc' : gridNorm (comp i (u k)) ≤ ‖coordC (V := V) i‖ * |B| :=
    hc.trans (mul_le_mul_of_nonneg_left ((hu k).trans (le_abs_self B)) (norm_nonneg _))
  gcongr with μ
  exact hd μ

/-- **Weak comparison of the reconstructed jets** (`V`-valued): under uniform discrete `H¹`
bounds, `∂_μ 𝓘_h u_h - R^0 D⁺_μ u_h ⇀ 0` weakly in `L²`, tested against `L²` covector fields. -/
theorem drecon_weak {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → V} {B : ℝ} (hu : ∀ k, gridNorm (u k) ≤ B)
    (hDu : ∀ k μ, gridNorm (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (u k)) ≤ B) (μ : Fin 4)
    (G : 𝕋 → V →L[ℝ] ℝ) (hG : MemLp G 2 volume) :
    Tendsto (fun k => ∫ z, G z (drecon μ (u k) z - pc (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (u k)) z)) atTop
      (𝓝 0) := by
  set b := Module.finBasis ℝ V
  have hpt : ∀ k z, drecon μ (u k) z - pc (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (u k)) z =
      ∑ i, (dTrig μ (comp i (u k)) z - pc (Dp μ (comp i (u k))) z).re • b i := by
    intro k z
    conv_lhs => rw [← sum_coord_smul (pc (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (u k)) z)]
    rw [drecon, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, Complex.sub_re, Dp_comp]
    rfl
  have hφC : ∀ i, MemLp (fun z => ((G z (b i) : ℝ) : ℂ)) 2 volume := fun i =>
    (hG.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℝ (b i))).continuousLinearMap_comp
      Complex.ofRealCLM
  have hφ : ∀ i, MemLp (fun z => G z (b i)) 2 volume := fun i =>
    hG.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℝ (b i))
  have hbnd : ∀ i k, gridNorm (comp i (u k)) ≤ ‖coordC (V := V) i‖ * B := fun i k =>
    (gridNorm_comp_le i (u k)).trans (mul_le_mul_of_nonneg_left (hu k) (norm_nonneg _))
  have hbndD : ∀ i k, gridNorm (Dp μ (comp i (u k))) ≤ ‖coordC (V := V) i‖ * B := fun i k => by
    rw [Dp_comp]
    exact (gridNorm_comp_le i _).trans (mul_le_mul_of_nonneg_left (hDu k μ) (norm_nonneg _))
  have hmax : ∀ i k, gridNorm (comp i (u k)) ≤ ‖coordC (V := V) i‖ * |B| ∧
      gridNorm (Dp μ (comp i (u k))) ≤ ‖coordC (V := V) i‖ * |B| := fun i k =>
    ⟨(hbnd i k).trans (mul_le_mul_of_nonneg_left (le_abs_self B) (norm_nonneg _)),
      (hbndD i k).trans (mul_le_mul_of_nonneg_left (le_abs_self B) (norm_nonneg _))⟩
  -- each component pairing tends to zero
  have hcomp : ∀ i, Tendsto (fun k => ∫ z, G z (b i) *
      (dTrig μ (comp i (u k)) z - pc (Dp μ (comp i (u k))) z).re) atTop (𝓝 0) := by
    intro i
    have hw := weak_dTrig_sub_pc hn (u := fun k => comp i (u k)) μ (fun k => (hmax i k).1)
      (fun k => (hmax i k).2) ((hφC i).toLp _)
    have hre := (Complex.continuous_re.tendsto 0).comp hw
    simp only [Complex.zero_re] at hre
    refine hre.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [MeasureTheory.L2.inner_def, ← Complex.reCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm _ (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [(hφC i).coeFn_toLp, Lp.coeFn_sub (dTrigLp μ (comp i (u k)))
      (pcLp (Dp μ (comp i (u k)))), coeFn_dTrigLp μ (comp i (u k)),
      coeFn_pcLp (Dp μ (comp i (u k)))] with z h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, h3, h4]
    simp [Complex.mul_re]
    ring
  have hint : ∀ i k, Integrable (fun z => G z (b i) *
      (dTrig μ (comp i (u k)) z - pc (Dp μ (comp i (u k))) z).re) volume := by
    intro i k
    have hh : MemLp (fun z => (dTrig μ (comp i (u k)) z - pc (Dp μ (comp i (u k))) z).re) 2
        volume := by
      have h1 : MemLp (fun z => dTrig μ (comp i (u k)) z) 2 volume :=
        MemLp.of_bound (dTrig μ _).continuous.aestronglyMeasurable ‖dTrig μ (comp i (u k))‖
          (Eventually.of_forall fun y => (dTrig μ _).norm_coe_le_norm y)
      exact (h1.sub (memLp_pc _)).continuousLinearMap_comp Complex.reCLM
    exact (hφ i).integrable_mul hh
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ V)))
    fun i _ => hcomp i
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr fun k => ?_
  rw [← integral_finsetSum _ fun i _ => hint i k]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hpt, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Vector

/-! ### Further properties of the vector reconstructions -/

section Vector2

local instance fact_one_le_two_v2 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {N : ℕ} [NeZero N]

theorem continuous_recon (u : Grid 4 N → V) : Continuous (recon u) :=
  continuous_finset_sum _ fun i _ =>
    (Complex.continuous_re.comp (trigInterp _).continuous).smul continuous_const

theorem continuous_drecon (μ : Fin 4) (u : Grid 4 N → V) : Continuous (drecon μ u) :=
  continuous_finset_sum _ fun i _ =>
    (Complex.continuous_re.comp (dTrig μ _).continuous).smul continuous_const

theorem memLp_drecon (μ : Fin 4) (u : Grid 4 N → V) {p : ℝ≥0∞} :
    MemLp (drecon μ u) p (volume : Measure 𝕋) := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image (continuous_drecon μ u)).isBounded.exists_norm_le
  exact MemLp.of_bound (continuous_drecon μ u).aestronglyMeasurable C
    (Eventually.of_forall fun z => hC _ ⟨z, trivial, rfl⟩)

theorem fwdDiff_eq_DpV (μ : Fin 4) (u : Grid 4 N → V) :
    ShiftedJetAction.fwdDiff (N : ℝ)⁻¹ μ u = NativeHiggs.DpV μ u := by
  funext x
  simp [ShiftedJetAction.fwdDiff, NativeHiggs.DpV, ShiftedJetAction.unitVec]

/-- **`L²` convergence of the reconstructions from raw convergence and a discrete `H¹` bound**
(first half of `eq:native-reconstruction-comparison`). -/
theorem recon_tendsto_of_bounded {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → V} {f : 𝕋 → V} (hu : LpTendsto volume 2 (fun k => pc (u k)) f)
    {B : ℝ} (hDu : ∀ k μ, gridNorm (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (u k)) ≤ B) :
    LpTendsto volume 2 (fun k => recon (u k)) f := by
  refine lpTendsto_assemble fun i => ?_
  have hci : LpTendsto volume 2 (fun k => pc (comp i (u k))) (fun z => coordC i (f z)) :=
    hu.clm (coordC i)
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hdiff : LpTendsto volume 2 (fun k z => trigInterp (comp i (u k)) z - pc (comp i (u k)) z)
      0 := by
    refine ⟨fun k => ?_, MemLp.zero, ?_⟩
    · exact (MemLp.of_bound (trigInterp _).continuous.aestronglyMeasurable
        ‖trigInterp (comp i (u k))‖ (Eventually.of_forall fun y =>
          (trigInterp _).norm_coe_le_norm y)).sub (memLp_pc _)
    · set c : ℝ := π / 2 * Real.sqrt 4 * Real.sqrt (∑ _μ : Fin 4, (‖coordC (V := V) i‖ * |B|) ^ 2)
      have hb : ∀ k, eLpNorm ((fun z => trigInterp (comp i (u k)) z - pc (comp i (u k)) z) - 0) 2
          volume ≤ ENNReal.ofReal (c * (1 / (n k : ℝ))) := by
        intro k
        rw [sub_zero]
        refine (eLpNorm_trigInterp_sub_pc_le_grad _).trans (ENNReal.ofReal_le_ofReal ?_)
        have hd : ∀ μ, gridNorm (Dp μ (comp i (u k))) ≤ ‖coordC (V := V) i‖ * |B| := fun μ => by
          rw [Dp_comp]
          exact (gridNorm_comp_le i _).trans (mul_le_mul_of_nonneg_left ((hDu k μ).trans
            (le_abs_self B)) (norm_nonneg _))
        have hs : Real.sqrt (∑ μ, gridNorm (Dp μ (comp i (u k))) ^ 2) ≤
            Real.sqrt (∑ _μ : Fin 4, (‖coordC (V := V) i‖ * |B|) ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
          exact pow_le_pow_left₀ (gridNorm_nonneg _) (hd μ) 2
        simp only [Nat.cast_ofNat, c]
        have h1 : 0 ≤ π / 2 * Real.sqrt 4 * (1 / (n k : ℝ)) := by positivity
        calc π / 2 * Real.sqrt 4 * (1 / (n k : ℝ)) * Real.sqrt (∑ μ, gridNorm (Dp μ (comp i (u k))) ^ 2)
            ≤ π / 2 * Real.sqrt 4 * (1 / (n k : ℝ)) *
              Real.sqrt (∑ _μ : Fin 4, (‖coordC (V := V) i‖ * |B|) ^ 2) :=
              mul_le_mul_of_nonneg_left hs h1
          _ = _ := by ring
      have hlim : Tendsto (fun k => ENNReal.ofReal (c * (1 / (n k : ℝ)))) atTop (𝓝 0) := by
        have : Tendsto (fun k => c * (1 / (n k : ℝ))) atTop (𝓝 0) := by
          simpa using ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hn').const_mul c
        simpa using ENNReal.tendsto_ofReal this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le) hb
  exact (hdiff.add hci).congr (fun k => Eventually.of_forall fun z => by simp)
    (Eventually.of_forall fun z => by simp)

/-- A uniform `L²` bound of the reconstructed jets. -/
theorem drecon_bounded {n : ℕ → ℕ} [∀ k, NeZero (n k)] {u : ∀ k, Grid 4 (n k) → V} {B : ℝ}
    (hDu : ∀ k μ, gridNorm (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (u k)) ≤ B) (μ : Fin 4) :
    ∃ C : ℝ, ∀ k, (eLpNorm (drecon μ (u k)) 2 volume).toReal ≤ C := by
  refine ⟨∑ i, ‖(Module.finBasis ℝ V) i‖ * (π / 2 * (‖coordC (V := V) i‖ * |B|)), fun k => ?_⟩
  have hsum : eLpNorm (drecon μ (u k)) 2 volume ≤ ∑ i, eLpNorm (fun z =>
      (dTrig μ (comp i (u k)) z).re • (Module.finBasis ℝ V) i) 2 volume := by
    have := eLpNorm_sum_le (μ := (volume : Measure 𝕋)) (s := Finset.univ) (f := fun i z =>
      (dTrig μ (comp i (u k)) z).re • (Module.finBasis ℝ V) i)
      (fun i _ => ((Complex.continuous_re.comp (dTrig μ _).continuous).smul
        continuous_const).aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    refine le_of_eq_of_le ?_ this
    congr 1; funext z; simp [drecon]
  have hterm : ∀ i, eLpNorm (fun z => (dTrig μ (comp i (u k)) z).re • (Module.finBasis ℝ V) i) 2
      volume ≤ ENNReal.ofReal (‖(Module.finBasis ℝ V) i‖ * (π / 2 * (‖coordC (V := V) i‖ * |B|))) := by
    intro i
    have h1 : eLpNorm (fun z => (dTrig μ (comp i (u k)) z).re • (Module.finBasis ℝ V) i) 2 volume ≤
        ENNReal.ofReal ‖(Module.finBasis ℝ V) i‖ * eLpNorm (dTrig μ (comp i (u k))) 2 volume :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => by
        rw [norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)) 2
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (norm_nonneg _)]
    refine mul_le_mul' le_rfl ?_
    have he : eLpNorm (dTrig μ (comp i (u k))) 2 volume = ENNReal.ofReal ‖dTrigLp μ (comp i (u k))‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      exact (eLpNorm_congr_ae (coeFn_dTrigLp μ _)).symm
    rw [he]
    refine ENNReal.ofReal_le_ofReal ((norm_dTrigLp_le μ _).trans ?_)
    rw [Dp_comp]
    exact mul_le_mul_of_nonneg_left ((gridNorm_comp_le i _).trans (mul_le_mul_of_nonneg_left
      ((hDu k μ).trans (le_abs_self B)) (norm_nonneg _))) (by positivity)
  have htot := hsum.trans (Finset.sum_le_sum fun i _ => hterm i)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)] at htot
  exact ENNReal.toReal_le_of_le_ofReal (Finset.sum_nonneg fun i _ => by positivity) htot

end Vector2

/-! ### Weak convergence of tuples -/

section WeakPair

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
  [NormedSpace ℝ B]

/-- Weak convergence of the two `Fin 4`-tuple components gives weak convergence of the pair. -/
theorem weak_pair {a : ℕ → 𝕋 → Fin 4 → A} {b : ℕ → 𝕋 → Fin 4 → B}
    (hamem : ∀ k μ, MemLp (fun z => a k z μ) 2 volume)
    (hbmem : ∀ k μ, MemLp (fun z => b k z μ) 2 volume)
    (ha : ∀ μ (G : 𝕋 → A →L[ℝ] ℝ), MemLp G 2 volume →
      Tendsto (fun k => ∫ z, G z (a k z μ)) atTop (𝓝 0))
    (hb : ∀ μ (G : 𝕋 → B →L[ℝ] ℝ), MemLp G 2 volume →
      Tendsto (fun k => ∫ z, G z (b k z μ)) atTop (𝓝 0))
    (G : 𝕋 → (Fin 4 → A) × (Fin 4 → B) →L[ℝ] ℝ) (hG : MemLp G 2 volume) :
    Tendsto (fun k => ∫ z, G z (a k z, b k z)) atTop (𝓝 0) := by
  set La : Fin 4 → A →L[ℝ] (Fin 4 → A) × (Fin 4 → B) := fun μ =>
    (ContinuousLinearMap.inl ℝ (Fin 4 → A) (Fin 4 → B)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => A) μ)
  set Lb : Fin 4 → B →L[ℝ] (Fin 4 → A) × (Fin 4 → B) := fun μ =>
    (ContinuousLinearMap.inr ℝ (Fin 4 → A) (Fin 4 → B)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => B) μ)
  have hGa : ∀ μ, MemLp (fun z => (G z).comp (La μ)) 2 volume := fun μ =>
    hG.continuousLinearMap_comp
      ((ContinuousLinearMap.compL ℝ A ((Fin 4 → A) × (Fin 4 → B)) ℝ).flip (La μ))
  have hGb : ∀ μ, MemLp (fun z => (G z).comp (Lb μ)) 2 volume := fun μ =>
    hG.continuousLinearMap_comp
      ((ContinuousLinearMap.compL ℝ B ((Fin 4 → A) × (Fin 4 → B)) ℝ).flip (Lb μ))
  have hdec : ∀ k z, G z (a k z, b k z) =
      ∑ μ, (G z).comp (La μ) (a k z μ) + ∑ μ, (G z).comp (Lb μ) (b k z μ) := by
    intro k z
    have e : (a k z, b k z) = ∑ μ, La μ (a k z μ) + ∑ μ, Lb μ (b k z μ) := by
      simp only [La, Lb, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply, ContinuousLinearMap.single_apply]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.univ_sum_single]
    rw [e, map_add, map_sum, map_sum]
    rfl
  have ia : ∀ k μ, Integrable (fun z => (G z).comp (La μ) (a k z μ)) volume := fun k μ =>
    WeakJetPairing.integrable_bilin_two_two (ContinuousLinearMap.id ℝ (A →L[ℝ] ℝ)) (hGa μ)
      (hamem k μ)
  have ib : ∀ k μ, Integrable (fun z => (G z).comp (Lb μ) (b k z μ)) volume := fun k μ =>
    WeakJetPairing.integrable_bilin_two_two (ContinuousLinearMap.id ℝ (B →L[ℝ] ℝ)) (hGb μ)
      (hbmem k μ)
  have h := (tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun μ _ => ha μ _ (hGa μ)).add
    (tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun μ _ => hb μ _ (hGb μ))
  simp only [Finset.sum_const_zero, add_zero] at h
  refine h.congr fun k => ?_
  simp only [hdec]
  rw [integral_add (integrable_finsetSum _ fun μ _ => ia k μ)
    (integrable_finsetSum _ fun μ _ => ib k μ), integral_finsetSum _ fun μ _ => ia k μ,
    integral_finsetSum _ fun μ _ => ib k μ]

end WeakPair

/-! ### The trigonometric reconstructions of the native records -/

section Records

open NativeDensity NativeHiggsVar NativeDiracLimit NativeDiracConvergence
open NativeDiracConv (CoHyp qM)
open NativeScaling (Mat)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)
open NativeGravityFirstJet (M4 coframeM)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {r r' : ℕ} [NeZero r] [NeZero r']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- The reconstructed spinor jets `(∂Ψ^rec, ∂Ψ̄^rec)`. -/
def recJets {N : ℕ} [NeZero N] (y : Grid 4 N → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢) (z : 𝕋) :
    Dif 𝓢 (CoSpinor 𝓢) :=
  (fun μ => drecon μ (psi y) z, fun μ => drecon μ (psiBar y) z)

theorem gridNorm_fwd_le_difs {N : ℕ} [NeZero N]
    (y : Grid 4 N → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢) (μ : Fin 4) :
    gridNorm (ShiftedJetAction.fwdDiff (N : ℝ)⁻¹ μ (psi y)) ≤ gridNorm (difs y (psiBar y)) ∧
      gridNorm (ShiftedJetAction.fwdDiff (N : ℝ)⁻¹ μ (psiBar y)) ≤
        gridNorm (difs y (psiBar y)) := by
  constructor
  · refine gridNorm_mono fun x => ?_
    exact (norm_le_pi_norm (fun μ => ShiftedJetAction.fwdDiff (N : ℝ)⁻¹ μ (psi y) x) μ).trans
      (norm_fst_le (difs y (psiBar y) x))
  · refine gridNorm_mono fun x => ?_
    exact (norm_le_pi_norm (fun μ => ShiftedJetAction.fwdDiff (N : ℝ)⁻¹ μ (psiBar y) x) μ).trans
      (norm_snd_le (difs y (psiBar y) x))

theorem memLp_recJets {N : ℕ} [NeZero N]
    (y : Grid 4 N → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢) : MemLp (recJets y) 2 volume := by
  have hc : Continuous (recJets y) := continuous_prodMk.2
    ⟨continuous_pi fun μ => continuous_drecon μ _, continuous_pi fun μ => continuous_drecon μ _⟩
  obtain ⟨C, hC⟩ := (isCompact_univ.image hc).isBounded.exists_norm_le
  exact MemLp.of_bound hc.aestronglyMeasurable C (Eventually.of_forall fun z => hC _ ⟨z, trivial, rfl⟩)

end Records

/-! ### The reconstructed spinor data along an extraction -/

section SpinorData

open NativeDensity NativeHiggsVar NativeDiracLimit NativeDiracConvergence
open NativeDiracConv (CoHyp)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

local instance fact_one_le_two_sd : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- **The reconstructed spinor data**: along records whose spinors and dual spinors converge
strongly in `L²` (`SpinHyp`), are bounded in `L²_h`, and whose first differences are bounded and
converge weakly to `u₀`, the trigonometric reconstructions `𝓘_hΨ_h`, `𝓘_hΨ̄_h` satisfy the
hypotheses of the Dirac sector (`RecDirac` spinor fields, uniform `L⁴` bounds) and their jets
converge weakly and boundedly to the same `u₀`. -/
theorem spinor_rec_data (hn : Tendsto n atTop atTop)
    {y : ∀ k, Grid 4 (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢}
    (S : SpinHyp (NativeSpinorGraph.κid 𝓢) y) {u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢)} {B C : ℝ}
    (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B) (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hub : ∀ k, (eLpNorm (pc (difs (y k) (S.χ k))) 2 volume).toReal ≤ C)
    (hw : ∀ g : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (pc (difs (y k) (S.χ k)) z)) atTop (𝓝 (∫ z, g z (u₀ z)))) :
    LpTendsto volume 2 (fun k => recon (psi (y k))) S.Ψ₀ ∧
      LpTendsto volume 2 (fun k => recon (psiBar (y k))) S.χ₀ ∧
      (∃ B4 : ℝ≥0∞, B4 ≠ ⊤ ∧ (∀ k, eLpNorm (recon (psi (y k))) 4 volume ≤ B4) ∧
        ∀ k, eLpNorm (recon (psiBar (y k))) 4 volume ≤ B4) ∧
      (∃ Cr : ℝ, ∀ k, (eLpNorm (recJets (y k)) 2 volume).toReal ≤ Cr) ∧
      ∀ g : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp g 2 volume →
        Tendsto (fun k => ∫ z, g z (recJets (y k) z)) atTop (𝓝 (∫ z, g z (u₀ z))) := by
  have hχeq : ∀ k, S.χ k = psiBar (y k) := fun k => funext fun x => (congrFun (S.hχ k) x).symm
  have hdb : ∀ k, gridNorm (difs (y k) (psiBar (y k))) ≤ C := by
    intro k
    have h := hub k
    rw [hχeq k, eLpNorm_pc, ENNReal.toReal_ofReal (gridNorm_nonneg _)] at h
    exact h
  have hf1 : ∀ k μ, gridNorm (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (psi (y k))) ≤ C :=
    fun k μ => (gridNorm_fwd_le_difs (y k) μ).1.trans (hdb k)
  have hf2 : ∀ k μ, gridNorm (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (psiBar (y k))) ≤ C :=
    fun k μ => (gridNorm_fwd_le_difs (y k) μ).2.trans (hdb k)
  have hχ₀ : LpTendsto volume 2 (fun k => pc (psiBar (y k))) S.χ₀ :=
    S.hχ₀.congr (fun k => Eventually.of_forall fun z => by rw [hχeq k])
      (Eventually.of_forall fun z => rfl)
  -- common bounds
  set M := max B C
  have hΨM : ∀ k, gridNorm (psi (y k)) ≤ M := fun k => (hΨ k).trans (le_max_left _ _)
  have hΨbM : ∀ k, gridNorm (psiBar (y k)) ≤ M := fun k => (hΨb k).trans (le_max_left _ _)
  have hf1M : ∀ k μ, gridNorm (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (psi (y k))) ≤ M :=
    fun k μ => (hf1 k μ).trans (le_max_right _ _)
  have hf2M : ∀ k μ, gridNorm (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (psiBar (y k))) ≤ M :=
    fun k μ => (hf2 k μ).trans (le_max_right _ _)
  obtain ⟨Ba, hBa, hBa'⟩ := recon_eLpNorm_four_bounded hΨM hf1M
  obtain ⟨Bb, hBb, hBb'⟩ := recon_eLpNorm_four_bounded hΨbM hf2M
  -- jets
  have hCa := fun μ => drecon_bounded (u := fun k => psi (y k)) hf1 μ
  have hCb := fun μ => drecon_bounded (u := fun k => psiBar (y k)) hf2 μ
  choose Ca hCa using hCa
  choose Cb hCb using hCb
  have hjet : ∀ k, (eLpNorm (recJets (y k)) 2 volume).toReal ≤ ∑ μ, Ca μ + ∑ μ, Cb μ := by
    intro k
    have hpt : ∀ z, ‖recJets (y k) z‖ ≤ ‖(∑ μ, ‖drecon μ (psi (y k)) z‖) +
        ∑ μ, ‖drecon μ (psiBar (y k)) z‖‖ := by
      intro z
      rw [Real.norm_of_nonneg (by positivity)]
      refine norm_prod_le_iff.2 ⟨?_, ?_⟩
      · refine ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ =>
          Finset.single_le_sum (f := fun μ => ‖drecon μ (psi (y k)) z‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ μ)).trans ?_
        exact le_add_of_nonneg_right (by positivity)
      · refine ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ =>
          Finset.single_le_sum (f := fun μ => ‖drecon μ (psiBar (y k)) z‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ μ)).trans ?_
        exact le_add_of_nonneg_left (by positivity)
    have ha : ∀ μ, MemLp (fun z => ‖drecon μ (psi (y k)) z‖) 2 volume := fun μ =>
      (memLp_drecon μ _).norm
    have hb : ∀ μ, MemLp (fun z => ‖drecon μ (psiBar (y k)) z‖) 2 volume := fun μ =>
      (memLp_drecon μ _).norm
    have hsa : MemLp (fun z => ∑ μ, ‖drecon μ (psi (y k)) z‖) 2 volume :=
      memLp_finsetSum _ fun μ _ => ha μ
    have hsb : MemLp (fun z => ∑ μ, ‖drecon μ (psiBar (y k)) z‖) 2 volume :=
      memLp_finsetSum _ fun μ _ => hb μ
    refine (ENNReal.toReal_mono (hsa.add hsb).2.ne (eLpNorm_mono hpt)).trans ?_
    refine (ENNReal.toReal_mono (by
      exact ENNReal.add_ne_top.2 ⟨hsa.2.ne, hsb.2.ne⟩) (eLpNorm_add_le hsa.1 hsb.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2))).trans ?_
    rw [ENNReal.toReal_add hsa.2.ne hsb.2.ne]
    have hS : ∀ (F : Fin 4 → 𝕋 → ℝ), (∀ μ, MemLp (F μ) 2 volume) →
        (eLpNorm (fun z => ∑ μ, F μ z) 2 volume).toReal ≤ ∑ μ, (eLpNorm (F μ) 2 volume).toReal := by
      intro F hF
      have h := eLpNorm_sum_le (μ := (volume : Measure 𝕋)) (s := Finset.univ) (f := F)
        (fun μ _ => (hF μ).1) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      rw [← ENNReal.toReal_sum fun μ _ => (hF μ).2.ne]
      refine ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun μ _ => (hF μ).2.ne) (le_of_eq_of_le ?_ h)
      congr 1
    refine add_le_add ((hS _ ha).trans (Finset.sum_le_sum fun μ _ => ?_))
      ((hS _ hb).trans (Finset.sum_le_sum fun μ _ => ?_))
    · rw [eLpNorm_norm]; exact hCa μ k
    · rw [eLpNorm_norm]; exact hCb μ k
  refine ⟨recon_tendsto_of_bounded hn S.hΨ hf1, recon_tendsto_of_bounded hn hχ₀ hf2,
    ⟨max Ba Bb, (max_lt hBa.lt_top hBb.lt_top).ne, fun k => (hBa' k).trans (le_max_left _ _),
      fun k => (hBb' k).trans (le_max_right _ _)⟩, ⟨_, hjet⟩, ?_⟩
  refine NativeReconstructed.weak_of_sub (fun k => memLp_recJets (y k))
    (fun k => TorusPiecewiseConstantTranslation.memLp_pc _) hw fun G hG => ?_
  have h := weak_pair (a := fun k z μ => drecon μ (psi (y k)) z -
      pc (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (psi (y k))) z)
    (b := fun k z μ => drecon μ (psiBar (y k)) z -
      pc (ShiftedJetAction.fwdDiff (n k : ℝ)⁻¹ μ (psiBar (y k))) z)
    (fun k μ => (memLp_drecon μ _).sub (TorusPiecewiseConstantTranslation.memLp_pc _))
    (fun k μ => (memLp_drecon μ _).sub (TorusPiecewiseConstantTranslation.memLp_pc _))
    (fun μ G' hG' => drecon_weak hn hΨM hf1M μ G' hG')
    (fun μ G' hG' => drecon_weak hn hΨbM hf2M μ G' hG') G hG
  refine h.congr fun k => ?_
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hχeq k]
  rfl

end SpinorData

/-! ### The final paragraph of `thm:native-firstvariation-no-band` with `𝓘_h^trig` -/

section ClosureTrig

open NativeDensity NativeHiggsVar NativeDiracLimit NativeDiracConvergence NativeReconstructed
open NativeDiracConv (CoHyp qM)
open NativeScaling (Mat)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)
open NativeGravityFirstJet (M4 coframeM)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {r r' : ℕ} [NeZero r] [NeZero r']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

local instance fact_one_le_two_ct : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The reconstruction data along an extraction: from the coframe/connection hypotheses, the
strong ordinary connection first differences, the Higgs conclusions and the spinor extraction, the
trigonometric reconstructions satisfy every hypothesis of the sector continuity theorems. -/
theorem trig_rec_data {y : ∀ k, Grid 4 (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢}
    (D : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢) (H : CoHyp n y)
    (hfK : ∀ k z, recon (coframeM (y k)) z ∈ H.Ke)
    {Pc : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hPc : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y k) ν))) (Pc μ ν))
    (P : HiggsHyp D y) (hDH : ∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y k))))
      (fun z => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z)))
    (S : SpinHyp (κid 𝓢) y) (hSH : S.H₀ = P.H₀) {u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢)} {B C : ℝ}
    (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B) (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hub : ∀ k, (eLpNorm (pc (difs (y k) (S.χ k))) 2 volume).toReal ≤ C)
    (hw : ∀ g : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (pc (difs (y k) (S.χ k)) z)) atTop (𝓝 (∫ z, g z (u₀ z)))) :
    ∃ R : RecDirac (W' := CoSpinor 𝓢) H.Ke H.e₀ H.p H.A₀ S.H₀ S.Ψ₀ S.χ₀,
      (∀ k, R.f k = recon (coframeM (y k))) ∧ (∀ k lam, R.g k lam = drecon lam (coframeM (y k))) ∧
      (∀ k μ, R.A k μ = recon (gauge (y k) μ)) ∧ (∀ k, R.Hr k = recon (higgs (y k))) ∧
      (∀ k, R.Ψ k = recon (psi (y k))) ∧ (∀ k, R.χ k = recon (psiBar (y k))) ∧
      LpTendsto volume 4 (fun k => recon (higgs (y k))) P.H₀ ∧
      (∀ μ ν, LpTendsto volume 2 (fun k => drecon μ (gauge (y k) ν)) (Pc μ ν)) ∧
      (∀ μ, LpTendsto volume 2 (fun k => drecon μ (higgs (y k)))
        (fun z => P.K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∃ Cr : ℝ, ∀ k, (eLpNorm (recJets (y k)) 2 volume).toReal ≤ Cr) ∧
      ∀ g : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp g 2 volume →
        Tendsto (fun k => ∫ z, g z (recJets (y k) z)) atTop (𝓝 (∫ z, g z (u₀ z))) := by
  have hcf := recon_tendsto H.hn (u := fun k => coframeM (y k)) H.he
    (fun lam => (H.hp lam).congr (fun k => Eventually.of_forall fun z => rfl)
      (Eventually.of_forall fun z => rfl))
  have hga : ∀ μ, LpTendsto volume 2 (fun k => recon (gauge (y k) μ)) (H.A₀ μ) ∧
      LpTendsto volume 4 (fun k => recon (gauge (y k) μ)) (H.A₀ μ) ∧
      ∀ ν, LpTendsto volume 2 (fun k => drecon ν (gauge (y k) μ)) (Pc ν μ) := fun μ =>
    recon_tendsto H.hn ((H.hA μ).mono two_ne_zero (by norm_num)) fun ν =>
      (hPc ν μ).congr (fun k => Eventually.of_forall fun z => by
        simp only [pc, fwdDiff_eq_DpV]) (Eventually.of_forall fun z => rfl)
  have hhi := recon_tendsto H.hn (u := fun k => higgs (y k))
    (P.hH.mono two_ne_zero (by norm_num)) fun μ =>
      (hDH μ).congr (fun k => Eventually.of_forall fun z => by
        simp only [pc, fwdDiff_eq_DpV]) (Eventually.of_forall fun z => rfl)
  obtain ⟨hΨr, hχr, ⟨B4, hB4, hΨ4, hχ4⟩, hjb, hjw⟩ := spinor_rec_data H.hn S hΨ hΨb hub hw
  let R : RecDirac (W' := CoSpinor 𝓢) H.Ke H.e₀ H.p H.A₀ S.H₀ S.Ψ₀ S.χ₀ :=
    { hKe := H.hKe
      hKdet := H.hKdet
      f := fun k => recon (coframeM (y k))
      hfK := hfK
      hf := hcf.1
      g := fun k lam => drecon lam (coframeM (y k))
      hg := hcf.2.2
      A := fun k μ => recon (gauge (y k) μ)
      hA := fun μ => (hga μ).2.1
      Hr := fun k => recon (higgs (y k))
      hH := by rw [hSH]; exact hhi.1
      Ψ := fun k => recon (psi (y k))
      hΨ := hΨr
      χ := fun k => recon (psiBar (y k))
      hχ := hχr
      B4 := B4
      hB4 := hB4
      hΨ4 := hΨ4
      hχ4 := hχ4 }
  refine ⟨R, fun k => rfl, fun k lam => rfl,
    fun k μ => rfl, fun k => rfl, fun k => rfl, fun k => rfl, hhi.2.1,
    fun μ ν => (hga ν).2.2 μ, hhi.2.2, hjb, hjw⟩

set_option maxHeartbeats 3200000 in
-- the statement assembles the four sector theorems along one extraction
/-- **`thm:native-firstvariation-no-band`, final paragraph, with the trigonometric
reconstructions** (fixed coefficient bank; unit-torus rendering; Higgs fibre `ℝ^{r_H}`; co-spinors
read with `κ = id`).  Under the hypotheses `(N1)–(N4)` of
`NativeAllSectorGraph.native_all_sector_closure` and the two hypotheses of the paragraph — the
**complete unfiltered reconstructed coframes `𝓘_h e_h` stay in the same compact chart** and the
**ordinary connection first differences converge strongly**, `R^0 D⁺_μ A_{ν,h} → P_{μν}` — along
one extraction: `eq:native-all-sector-limit`; `F = P - Pᵀ + [A, A]`; and the sectorwise
consistency errors relative to the reconstructed fields `𝓘_h z_h` (with their classical first jets
`∂𝓘_h`) tend to zero: gravity at `(𝓘_he_h, ∂𝓘_he_h)`, Yang–Mills at
`(𝓘_he_h, 𝓘_hA_h, F(𝓘_hA_h))`, Higgs at `(𝓘_he_h, 𝓘_hA_h, 𝓘_hH_h, ∂𝓘_hH_h)`, Dirac–Yukawa at the
reconstructed spinors with jets `(∂𝓘_hΨ_h, ∂𝓘_hΨ̄_h)`, and the total error. -/
theorem native_reconstructed_closure_trig (D : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (T : 𝔄 →L[ℝ] E) (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    {y : ∀ k, Grid 4 (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢} (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (hUH : ∀ k x μ (v : EuclideanSpace ℝ (Fin rH)),
      ‖exp ((n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)) v‖ = ‖v‖)
    {BH : ℝ} (hHb : ∀ k, gridNorm (higgs (y k)) ≤ BH)
    {K₀ : Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH)}
    (hK : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => higgsLink D (n k : ℝ)⁻¹ (y k) x μ))
      (K₀ μ))
    (hU : ∀ k x μ (v : 𝓢), ‖D.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖)
    {B : ℝ} (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B)
    (hKs : ∀ k μ, gridNorm (fun x => spinGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hKb : ∀ k μ, gridNorm (fun x => dualGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    -- the two hypotheses of the final paragraph
    (hfK : ∀ k z, recon (coframeM (y k)) z ∈ H.Ke)
    {Pc : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hPc : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y k) ν)))
      (Pc μ ν)) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ, ∃ P : HiggsHyp D (fun k => y (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar D (n (φ k)) (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeAllSector.contAllVar D (κid 𝓢) T (coHypSubseq H hφ) F P S u₀ τ| ≤ ε) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] recCurv H.A₀ Pc μ ν) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τk : TorusC2Tests.C2Test M4,
        |NativeGravityFirstJet.gravVariation D (n (φ k)) (y (φ k)) τk -
          NativeGravityFirstJet.contGravVariation D.κ D.Λ (recon (coframeM (y (φ k))))
            (fun lam => drecon lam (coframeM (y (φ k)))) τk| ≤ ε * τk.norm) ∧
      (∀ M : NNReal, ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeYMBridge.ymVar D (n (φ k)) (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeYMMetric.firstVarCont T (recon (coframeM (y (φ k))))
            (fun μ => recon (gauge (y (φ k)) μ))
            (recCurv (fun μ => recon (gauge (y (φ k)) μ))
              (fun μ ν => drecon μ (gauge (y (φ k)) ν))) τ.k.f (NativeYMBridge.toC1 τ.a)| ≤ β k) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        |higgsVar D (n (φ k)) (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          higgsRecVar D (recon (coframeM (y (φ k)))) (fun μ => recon (gauge (y (φ k)) μ))
            (recon (higgs (y (φ k)))) (fun μ => drecon μ (higgs (y (φ k)))) τ| ≤ ε * τ.norm) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        |NativeDirac.dVar D (n (φ k) : ℝ)⁻¹ (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          diracRecVar D (κid 𝓢) (recon (coframeM (y (φ k))))
            (fun lam => drecon lam (coframeM (y (φ k)))) (fun μ => recon (gauge (y (φ k)) μ))
            (recon (higgs (y (φ k)))) (recon (psi (y (φ k)))) (recon (psiBar (y (φ k))))
            (recJets (y (φ k))) τ| ≤ ε * τ.norm) ∧
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar D (n (φ k)) (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          recAllVar D (κid 𝓢) T (recon (coframeM (y (φ k))))
            (fun lam => drecon lam (coframeM (y (φ k)))) (fun μ => recon (gauge (y (φ k)) μ))
            (fun μ ν => drecon μ (gauge (y (φ k)) ν)) (recon (higgs (y (φ k))))
            (fun μ => drecon μ (higgs (y (φ k)))) (recon (psi (y (φ k))))
            (recon (psiBar (y (φ k)))) (recJets (y (φ k))) τ| ≤ ε) := by
  obtain ⟨φ₁, hφ₁, P₁, hP₁, hDH⟩ := NativeHiggsVar.exists_higgsHyp D H.hn H.hA hUH hHb hK
  have hn₁ : Tendsto (fun k => n (φ₁ k)) atTop atTop := H.hn.comp hφ₁.tendsto_atTop
  obtain ⟨φ₂, hφ₂, S, u₀, hSH, hu₀, ⟨C, hub⟩, hw, -, -⟩ :=
    NativeSpinorGraph.native_spinor_extraction D Θ Θ' hn₁
      (fun μ => (H.hA μ).comp_strictMono hφ₁) (P₁.hH.mono (by norm_num) (by norm_num))
      (fun k => hU (φ₁ k)) (fun k => hΨ (φ₁ k)) (fun k => hKs (φ₁ k)) (fun k => hΨb (φ₁ k))
      (fun k => hKb (φ₁ k))
  have hφ : StrictMono (fun k => φ₁ (φ₂ k)) := hφ₁.comp hφ₂
  set φ : ℕ → ℕ := fun k => φ₁ (φ₂ k) with hφdef
  set P := NativeAllSectorGraph.higgsHypSubseq P₁ hφ₂ with hPdef
  set H' := coHypSubseq H hφ with hH'
  have hF' : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (gauge (y (φ k))) x μ ν)) (F μ ν) :=
    fun μ ν => (hF μ ν).comp_strictMono hφ
  have hPc' : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (NativeHiggs.DpV μ (gauge (y (φ k)) ν))) (Pc μ ν) :=
    fun μ ν => (hPc μ ν).comp_strictMono hφ
  have hlim := NativeAllSector.native_all_sector_limit D (κid 𝓢) T hip H' hpos hc hF' P S hu₀
    hub hw
  have hDH' : ∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y (φ k)))))
      (fun z => P.K₀ μ z - D.ρHL (H'.A₀ μ z) (P.H₀ z)) := by
    intro μ
    have hK₀ : P.K₀ = K₀ := hP₁
    rw [hK₀]
    exact (hDH μ).comp_strictMono hφ₂
  have hcf := recon_tendsto H'.hn (u := fun k => coframeM (y (φ k))) H'.he
    (fun lam => (H'.hp lam).congr (fun k => Eventually.of_forall fun z => rfl)
      (Eventually.of_forall fun z => rfl))
  have hga : ∀ μ, LpTendsto volume 2 (fun k => recon (gauge (y (φ k)) μ)) (H.A₀ μ) ∧
      LpTendsto volume 4 (fun k => recon (gauge (y (φ k)) μ)) (H.A₀ μ) ∧
      ∀ ν, LpTendsto volume 2 (fun k => drecon ν (gauge (y (φ k)) μ)) (Pc ν μ) := fun μ =>
    recon_tendsto H'.hn ((H'.hA μ).mono two_ne_zero (by norm_num)) fun ν =>
      (hPc' ν μ).congr (fun k => Eventually.of_forall fun z => by
        simp only [pc, fwdDiff_eq_DpV]) (Eventually.of_forall fun z => rfl)
  have hhi := recon_tendsto H'.hn (u := fun k => higgs (y (φ k)))
    (P.hH.mono two_ne_zero (by norm_num)) fun μ =>
      (hDH' μ).congr (fun k => Eventually.of_forall fun z => by
        simp only [pc, fwdDiff_eq_DpV]) (Eventually.of_forall fun z => rfl)
  obtain ⟨hΨr, hχr, ⟨B4, hB4, hΨ4, hχ4⟩, ⟨Cr, hurb⟩, hurw⟩ :=
    spinor_rec_data H'.hn S (fun k => hΨ (φ k)) (fun k => hΨb (φ k)) hub hw
  let R : RecDirac (W' := CoSpinor 𝓢) H'.Ke H'.e₀ H'.p H'.A₀ S.H₀ S.Ψ₀ S.χ₀ :=
    { hKe := H.hKe
      hKdet := H.hKdet
      f := fun k => recon (coframeM (y (φ k)))
      hfK := fun k => hfK (φ k)
      hf := hcf.1
      g := fun k lam => drecon lam (coframeM (y (φ k)))
      hg := hcf.2.2
      A := fun k μ => recon (gauge (y (φ k)) μ)
      hA := fun μ => (hga μ).2.1
      Hr := fun k => recon (higgs (y (φ k)))
      hH := by rw [hSH]; exact hhi.1
      Ψ := fun k => recon (psi (y (φ k)))
      hΨ := hΨr
      χ := fun k => recon (psiBar (y (φ k)))
      hχ := hχr
      B4 := B4
      hB4 := hB4
      hΨ4 := hΨ4
      hχ4 := hχ4 }
  have hHr4 := hhi.2.1
  have hdAr' : ∀ μ ν, LpTendsto volume 2 (fun k => drecon μ (gauge (y (φ k)) ν)) (Pc μ ν) :=
    fun μ ν => (hga ν).2.2 μ
  have hdH' := hhi.2.2
  refine ⟨φ, hφ, P, S, u₀, hlim, curvature_identification H hF hPc, ?_, ?_, ?_, ?_, ?_⟩
  · exact NativeGravityFirstJet.native_gravity_firstjet_reconstructed D H'.hn (fun k => y (φ k))
      H.e₀ H.p (Ke := (H.Ke : Set Mat)) H.hKe hpos H'.hval hc H'.hmar H'.he H'.hp
      R.f R.g R.hfK R.hf R.hg
  · exact fun M => native_YM_reconstructed D (κid 𝓢) T hip H' hF' hPc' R.hfK R.hf R.hA hdAr' M
  · exact native_Higgs_reconstructed D (κid 𝓢) H' P R.hfK R.hf R.hA hHr4 hdH'
  · exact native_Dirac_reconstructed D (κid 𝓢) H' S hu₀ hub hw R (fun k => memLp_recJets _)
      hurb hurw
  · intro M ε hε
    have h1 := hlim M (ε / 2) (by positivity)
    have h2 := all_rec_close D (κid 𝓢) T H' hpos hF' hPc' P S hu₀ R hHr4 hdAr' hdH'
      (fun k => memLp_recJets _) hurb hurw M (ε / 2) (by positivity)
    filter_upwards [h1, h2] with k hk1 hk2 τ hτ
    have := abs_sub_le (NativeAllSector.nativeVar D (n (φ k)) (y (φ k))
      (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ))
      (NativeAllSector.contAllVar D (κid 𝓢) T H' F P S u₀ τ)
      (recAllVar D (κid 𝓢) T (R.f k) (R.g k) (R.A k) (fun μ ν => drecon μ (gauge (y (φ k)) ν))
        (R.Hr k) (fun μ => drecon μ (higgs (y (φ k)))) (R.Ψ k) (R.χ k) (recJets (y (φ k))) τ)
    linarith [hk1 τ hτ, hk2 τ hτ]

end ClosureTrig

/-! ### The bank version with `𝓘_h^trig` -/

section ClosureTrigBank

open NativeDensity NativeHiggsVar NativeDiracLimit NativeDiracConvergence NativeReconstructed NativeBank
open ShiftedJetAction (Grid)
open NativeDiracConv (CoHyp qM)
open NativeScaling (Mat)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)
open NativeGravityFirstJet (M4 coframeM)
open TorusPiecewiseConstantTranslation (gridNorm)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {r r' : ℕ} [NeZero r] [NeZero r']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {J : ℕ}

local instance fact_one_le_two_ctb : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

set_option maxHeartbeats 3200000 in
-- the statement assembles the bank limit and the reconstructed continuity along one extraction
/-- **`thm:native-firstvariation-no-band`, final paragraph, with varying coefficient banks
`(N5)`.**  Hypotheses of `NativeBank.native_all_sector_closure_bank` (cutoff banks `θ_h → θ`,
`κ ≠ 0`, nonnegative limit gauge weights), the strong convergence of the ordinary connection first
differences, and the trigonometric reconstructions `𝓘_h` of the records (with the chart hypothesis on `𝓘_h e_h`).  Then
along one extraction: the all-sector limit with the cutoff banks, the reconstructed curvature
identification, **the complete consistency error of the finite action at the cutoff banks
relative to the continuum first variation at the limit bank evaluated at the reconstructed
fields** tends to zero uniformly on every `C²` ball, and so do the sectorwise differences between
the limit-field and the reconstructed-field continuum covectors (gravity, Yang–Mills, Higgs,
Dirac–Yukawa). -/
theorem native_reconstructed_closure_trig_bank (D₀ : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (Tj : Fin J → 𝔄 →L[ℝ] E) {θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢}
    {θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢} (hθ : BankConv θs θ) (hκ : θ.κ ≠ 0)
    (hwθ : ∀ j, 0 ≤ θ.w j)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    {y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢} (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (hUH : ∀ k x μ (v : EuclideanSpace ℝ (Fin rH)),
      ‖exp ((n k : ℝ)⁻¹ • D₀.ρHL (gauge (y k) μ x)) v‖ = ‖v‖)
    {BH : ℝ} (hHb : ∀ k, gridNorm (higgs (y k)) ≤ BH)
    {K₀ : Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH)}
    (hK : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => higgsLink D₀ (n k : ℝ)⁻¹ (y k) x μ))
      (K₀ μ))
    (hU : ∀ k x μ (v : 𝓢), ‖D₀.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖)
    {B : ℝ} (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B)
    (hKs : ∀ k μ, gridNorm (fun x => spinGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hKb : ∀ k μ, gridNorm (fun x => dualGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    {Pc : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hPc : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y k) ν))) (Pc μ ν))
    (hfK : ∀ k z, recon (coframeM (y k)) z ∈ H.Ke) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
      ∃ P : HiggsHyp (bankData D₀ Tj θ) (fun k => y (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeAllSector.contAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (coHypSubseq H hφ) F P S u₀ τ| ≤ ε) ∧
      -- the reconstructed curvature identification
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] recCurv H.A₀ Pc μ ν) ∧
      -- `K = D_A H`
      P.K₀ = K₀ ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y (φ k)))))
        (fun z => K₀ μ z - D₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      -- `u₀ = (∂Ψ, ∂Ψ̄)`: the spinors converge weakly in `H¹`
      (∀ j, ∃ f : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      (∀ j, ∃ f : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ' (S.χ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ' ((u₀ z).2 μ) j : ℝ) : ℂ)) ∧
      -- the complete error relative to the reconstructed fields, cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          recAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w) (recon (coframeM (y (φ k)))) (fun lam => drecon lam (coframeM (y (φ k)))) (fun μ => recon (gauge (y (φ k)) μ))
            (fun μ ν => drecon μ (gauge (y (φ k)) ν)) (recon (higgs (y (φ k)))) (fun μ => drecon μ (higgs (y (φ k)))) (recon (psi (y (φ k)))) (recon (psiBar (y (φ k)))) (recJets (y (φ k))) τ| ≤ ε) ∧
      -- sectorwise: limit-field versus reconstructed-field covectors at the limit bank
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τk : TorusC2Tests.C2Test M4,
        |NativeGravityFirstJet.contGravVariation θ.κ θ.Λ H.e₀ H.p τk -
          NativeGravityFirstJet.contGravVariation θ.κ θ.Λ (recon (coframeM (y (φ k)))) (fun lam => drecon lam (coframeM (y (φ k)))) τk| ≤
            ε * τk.norm) ∧
      (∀ M : NNReal, ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ k,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeYMMetric.firstVarCont (bankT Tj θ.w) H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a) -
          NativeYMMetric.firstVarCont (bankT Tj θ.w) (recon (coframeM (y (φ k)))) (fun μ => recon (gauge (y (φ k)) μ))
            (recCurv (fun μ => recon (gauge (y (φ k)) μ)) (fun μ ν => drecon μ (gauge (y (φ k)) ν))) τ.k.f (NativeYMBridge.toC1 τ.a)| ≤ β k) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        |contHiggsVar (bankData D₀ Tj θ) (coHypSubseq H hφ) P τ -
          higgsRecVar (bankData D₀ Tj θ) (recon (coframeM (y (φ k)))) (fun μ => recon (gauge (y (φ k)) μ)) (recon (higgs (y (φ k)))) (fun μ => drecon μ (higgs (y (φ k)))) τ| ≤
            ε * τ.norm) ∧
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        |NativeSpinorVariation.contDiracVar (bankData D₀ Tj θ) (κid 𝓢) (coHypSubseq H hφ) S u₀ τ -
          diracRecVar (bankData D₀ Tj θ) (κid 𝓢) (recon (coframeM (y (φ k)))) (fun lam => drecon lam (coframeM (y (φ k)))) (fun μ => recon (gauge (y (φ k)) μ)) (recon (higgs (y (φ k))))
            (recon (psi (y (φ k)))) (recon (psiBar (y (φ k)))) (recJets (y (φ k))) τ| ≤ ε * τ.norm) := by
  set D := bankData D₀ Tj θ with hD
  obtain ⟨φ₁, hφ₁, P₁, hP₁, hDH⟩ := NativeHiggsVar.exists_higgsHyp D H.hn H.hA hUH hHb hK
  have hn₁ : Tendsto (fun k => n (φ₁ k)) atTop atTop := H.hn.comp hφ₁.tendsto_atTop
  obtain ⟨φ₂, hφ₂, S, u₀, hSH, hu₀, ⟨C, hub⟩, hw, hid1, hid2⟩ :=
    NativeSpinorGraph.native_spinor_extraction D Θ Θ' hn₁
      (fun μ => (H.hA μ).comp_strictMono hφ₁) (P₁.hH.mono (by norm_num) (by norm_num))
      (fun k => hU (φ₁ k)) (fun k => hΨ (φ₁ k)) (fun k => hKs (φ₁ k)) (fun k => hΨb (φ₁ k))
      (fun k => hKb (φ₁ k))
  have hφ : StrictMono (fun k => φ₁ (φ₂ k)) := hφ₁.comp hφ₂
  set φ : ℕ → ℕ := fun k => φ₁ (φ₂ k) with hφdef
  set P := NativeAllSectorGraph.higgsHypSubseq P₁ hφ₂ with hPdef
  set H' := coHypSubseq H hφ with hH'
  have hF' : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (gauge (y (φ k))) x μ ν)) (F μ ν) :=
    fun μ ν => (hF μ ν).comp_strictMono hφ
  have hPc' : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (NativeHiggs.DpV μ (gauge (y (φ k)) ν))) (Pc μ ν) :=
    fun μ ν => (hPc μ ν).comp_strictMono hφ
  have hθ' : BankConv (fun k => θs (φ k)) θ :=
    ⟨hθ.κ.comp hφ.tendsto_atTop, hθ.Λ.comp hφ.tendsto_atTop, hθ.lamH.comp hφ.tendsto_atTop,
      hθ.vH.comp hφ.tendsto_atTop, fun j => (hθ.w j).comp hφ.tendsto_atTop,
      hθ.Y.comp hφ.tendsto_atTop⟩
  have hlim := native_all_sector_limit_bank D₀ Tj (κid 𝓢) hθ' hκ hwθ H' hpos hc hF' P S hu₀ hub hw
  have hDH' : ∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y (φ k)))))
      (fun z => P.K₀ μ z - D.ρHL (H'.A₀ μ z) (P.H₀ z)) := by
    intro μ
    have hK₀ : P.K₀ = K₀ := hP₁
    rw [hK₀]
    exact (hDH μ).comp_strictMono hφ₂
  have hcf := recon_tendsto H'.hn (u := fun k => coframeM (y (φ k))) H'.he
    (fun lam => (H'.hp lam).congr (fun k => Eventually.of_forall fun z => rfl)
      (Eventually.of_forall fun z => rfl))
  have hga : ∀ μ, LpTendsto volume 2 (fun k => recon (gauge (y (φ k)) μ)) (H.A₀ μ) ∧
      LpTendsto volume 4 (fun k => recon (gauge (y (φ k)) μ)) (H.A₀ μ) ∧
      ∀ ν, LpTendsto volume 2 (fun k => drecon ν (gauge (y (φ k)) μ)) (Pc ν μ) := fun μ =>
    recon_tendsto H'.hn ((H'.hA μ).mono two_ne_zero (by norm_num)) fun ν =>
      (hPc' ν μ).congr (fun k => Eventually.of_forall fun z => by
        simp only [pc, fwdDiff_eq_DpV]) (Eventually.of_forall fun z => rfl)
  have hhi := recon_tendsto H'.hn (u := fun k => higgs (y (φ k)))
    (P.hH.mono two_ne_zero (by norm_num)) fun μ =>
      (hDH' μ).congr (fun k => Eventually.of_forall fun z => by
        simp only [pc, fwdDiff_eq_DpV]) (Eventually.of_forall fun z => rfl)
  obtain ⟨hΨr, hχr, ⟨B4, hB4, hΨ4, hχ4⟩, ⟨Cr, hurb⟩, hurw⟩ :=
    spinor_rec_data H'.hn S (fun k => hΨ (φ k)) (fun k => hΨb (φ k)) hub hw
  let R : RecDirac (W' := CoSpinor 𝓢) H'.Ke H'.e₀ H'.p H'.A₀ S.H₀ S.Ψ₀ S.χ₀ :=
    { hKe := H.hKe
      hKdet := H.hKdet
      f := fun k => recon (coframeM (y (φ k)))
      hfK := fun k => hfK (φ k)
      hf := hcf.1
      g := fun k lam => drecon lam (coframeM (y (φ k)))
      hg := hcf.2.2
      A := fun k μ => recon (gauge (y (φ k)) μ)
      hA := fun μ => (hga μ).2.1
      Hr := fun k => recon (higgs (y (φ k)))
      hH := by rw [hSH]; exact hhi.1
      Ψ := fun k => recon (psi (y (φ k)))
      hΨ := hΨr
      χ := fun k => recon (psiBar (y (φ k)))
      hχ := hχr
      B4 := B4
      hB4 := hB4
      hΨ4 := hΨ4
      hχ4 := hχ4 }
  have hHr4 := hhi.2.1
  have hdAr' : ∀ μ ν, LpTendsto volume 2 (fun k => drecon μ (gauge (y (φ k)) ν)) (Pc μ ν) :=
    fun μ ν => (hga ν).2.2 μ
  have hdH' := hhi.2.2
  refine ⟨φ, hφ, P, S, u₀, hlim, curvature_identification H hF hPc, hP₁,
    fun μ => (hDH μ).comp_strictMono hφ₂, hid1, hid2, ?_, ?_, ?_, ?_, ?_⟩
  · intro M ε hε
    have h1 := hlim M (ε / 2) (by positivity)
    have h2 := all_rec_close D (κid 𝓢) (bankT Tj θ.w) H' hpos hF' hPc' P S hu₀ R hHr4 hdAr' hdH'
      (fun k => memLp_recJets _) hurb hurw M (ε / 2) (by positivity)
    filter_upwards [h1, h2] with k hk1 hk2 τ hτ
    have := abs_sub_le (NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
      (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ))
      (NativeAllSector.contAllVar D (κid 𝓢) (bankT Tj θ.w) H' F P S u₀ τ)
      (recAllVar D (κid 𝓢) (bankT Tj θ.w) (R.f k) (R.g k) (R.A k)
        (fun μ ν => drecon μ (gauge (y (φ k)) ν)) (R.Hr k) (fun μ => drecon μ (higgs (y (φ k))))
        (R.Ψ k) (R.χ k) (recJets (y (φ k))) τ)
    linarith [hk1 τ hτ, hk2 τ hτ]
  · exact grav_rec_close θ.κ θ.Λ (Ke := (H.Ke : Set Mat)) H.hKe hpos R.hfK R.hf R.hg
  · exact fun M => ym_rec_close (bankT Tj θ.w) H' hF' hPc' R.hfK R.hf R.hA hdAr' M
  · exact higgs_rec_close D H' P R.hfK R.hf R.hA hHr4 hdH'
  · exact dirac_rec_close D (κid 𝓢) H' S hu₀ R (fun k => memLp_recJets _) hurb hurw

end ClosureTrigBank

/-! ### Constants -/

section Constants

open TorusTrigReconstruction LatticeTorusPlancherel TorusCellEmbedding

theorem dft_const {d N : ℕ} [NeZero N] (a : ℂ) (k : Grid d N) :
    dft (fun _ : Grid d N => a) k = if k = 0 then a else 0 := by
  have hs : ∑ x : Grid d N, (starRingEnd ℂ) (latticeChar k x) = if k = 0 then ((N : ℂ) ^ d) else 0 := by
    rw [← map_sum]
    simp_rw [latticeChar_comm k]
    rw [sum_latticeChar]
    split_ifs <;> simp
  simp only [dft, smul_eq_mul]
  rw [← Finset.sum_mul, hs]
  split_ifs
  · have : ((N : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne N))
    field_simp
  · simp

theorem trigInterp_const {d N : ℕ} [NeZero N] (a : ℂ) (z : UnitAddTorus (Fin d)) :
    trigInterp (fun _ : Grid d N => a) z = a := by
  rw [trigInterp_apply]
  simp_rw [dft_const]
  rw [Finset.sum_eq_single (0 : Grid d N) (fun b _ hb => by simp [hb]) (by simp)]
  have : signedRep (0 : Grid d N) = 0 := by funext i; simp [signedRep]
  simp [this, UnitAddTorus.mFourier_zero]

theorem recon_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {N : ℕ} [NeZero N] (v : V) (z : UnitAddTorus (Fin 4)) :
    recon (fun _ : Grid 4 N => v) z = v := by
  have h : ∀ i, comp i (fun _ : Grid 4 N => v) = fun _ => (((Module.finBasis ℝ V).coord i v : ℝ) : ℂ) :=
    fun i => rfl
  simp only [recon, h, trigInterp_const, Complex.ofReal_re, Module.Basis.coord_apply]
  exact (Module.finBasis ℝ V).sum_repr v

end Constants

section NonVacuity

open NativeDensity NativeDiracLimit NativeHiggsVar NativeDiracConvergence
open NativeAllSectorGraph (exData2 exData2_hip exCoHyp2 exCoHyp2_pos flat2 frameC frameCo
  gauge_flat2)
open NativeGravityFirstJet (flatRecord coframeM)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)
open NativeScaling (Mat)
open NativeReconstructed (lpTendsto_zero_of_eq recAllVar)

local instance : Nontrivial (CoSpinor ℂ) :=
  ⟨⟨0, ContinuousLinearMap.id ℝ ℂ, fun h => by
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) h
    simp at this⟩⟩

local instance : NeZero (Module.finrank ℝ (CoSpinor ℂ)) := ⟨Module.finrank_pos.ne'⟩

/-- **Non-vacuity of `native_reconstructed_closure_trig`**: the flat records of the abelian
Einstein–Higgs–Dirac packet satisfy `(N1)–(N4)` and the two hypotheses of the final paragraph
(the trigonometric reconstruction of the constant coframe is the constant coframe, so it stays in
the chart `{1}`); the theorem yields the complete error relative to the trigonometric
reconstructions. -/
example : ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
    ∃ P : NativeHiggsVar.HiggsHyp exData2 (fun k => flat2 (φ k + 1)),
    ∃ S : NativeDiracConvergence.SpinHyp (κid ℂ) (fun k => flat2 (φ k + 1)),
    ∃ u₀ : 𝕋 → Dif ℂ (CoSpinor ℂ),
      ∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest ℂ (EuclideanSpace ℝ (Fin 2)) ℂ (CoSpinor ℂ), τ.norm ≤ M →
        |NativeAllSector.nativeVar exData2 (φ k + 1) (flat2 (φ k + 1))
            (testRec (κid ℂ) (φ k + 1) (flat2 (φ k + 1)) τ) -
          recAllVar exData2 (κid ℂ) (ContinuousLinearMap.id ℝ ℂ)
            (recon (coframeM (flat2 (φ k + 1))))
            (fun lam => drecon lam (coframeM (flat2 (φ k + 1))))
            (fun μ => recon (gauge (flat2 (φ k + 1)) μ))
            (fun μ ν => drecon μ (gauge (flat2 (φ k + 1)) ν)) (recon (higgs (flat2 (φ k + 1))))
            (fun μ => drecon μ (higgs (flat2 (φ k + 1)))) (recon (psi (flat2 (φ k + 1))))
            (recon (psiBar (flat2 (φ k + 1)))) (recJets (flat2 (φ k + 1))) τ| ≤ ε := by
  have hgz : ∀ k μ, gauge (flat2 (k + 1)) μ = fun _ => (0 : ℂ) := fun k μ => rfl
  obtain ⟨φ, hφ, P, S, u₀, -, -, -, -, -, -, htot⟩ := native_reconstructed_closure_trig exData2
    (ContinuousLinearMap.id ℝ ℂ) exData2_hip frameC frameCo exCoHyp2 exCoHyp2_pos
    (by norm_num [exCoHyp2]) (F := fun _ _ _ => 0)
    (fun μ ν => (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
      (fun k => Eventually.of_forall fun z => by
        rw [gauge_flat2]
        simp [pc, NativeScaling.fieldStrength, NativeScaling.gaugePlaquette,
          ShiftedPlaquette.logOneAdd])
      (Eventually.of_forall fun _ => rfl))
    (fun k x μ v => by rw [gauge_flat2]; simp)
    (BH := 0) (fun k => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, higgs, flat2, flatRecord])
    (K₀ := fun _ _ => 0)
    (fun μ => (LpTendsto.const (u := fun _ : 𝕋 => (0 : EuclideanSpace ℝ (Fin 2)))
      (memLp_const _)).congr (fun k => Eventually.of_forall fun z => by
        simp [pc, higgsLink, NativeScaling.higgsLink, higgs, flat2, flatRecord])
      (Eventually.of_forall fun _ => rfl))
    (fun k x μ v => by rw [gauge_flat2]; simp)
    (B := 0) (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psi, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, spinGraph, psi, flat2, flatRecord])
    (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psiBar, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, dualGraph, psiBar, flat2, flatRecord])
    (fun k z => by
      change recon (fun _ => NativeGravityFirstJet.asM4 (1 : Mat)) z ∈ ({NativeGravityFirstJet.asM4 1} : Set _)
      rw [recon_const]; rfl)
    (Pc := fun _ _ _ => 0)
    (fun μ ν => (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
      (fun k => Eventually.of_forall fun z => by
        simp [pc, NativeHiggs.DpV, hgz]) (Eventually.of_forall fun _ => rfl))
  exact ⟨φ, hφ, P, S, u₀, htot⟩

end NonVacuity

end



end RenewalGeometry.NativeTrigRec
