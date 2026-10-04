/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeYangMillsVariation
import RenewalGeometry.Continuum.NativeHiggsCompactness
import RenewalGeometry.DiscreteAnalysis.PeriodicForwardDifferenceHodgeIdentityExact

/-!
# The Lipschitz plaquette envelope and the discrete Coulomb absorption inequality

Deterministic (fixed-grid) part of `thm:native-discrete-Coulomb` of the Einstein–SM
action-closure manuscript, in the unit-torus rendering of `Continuum/TorusTrigReconstruction.lean`
(grid `(ℤ/N)⁴`, mesh `h = 1/N`; the paper's box of side `2π` is its dilation).  This file is the
**convention bridge** between the general-mesh Hodge/Sobolev files
(`DiscreteAnalysis/PeriodicForwardDifferenceHodgeIdentityExact.lean`,
`DiscreteAnalysis/GridSobolevInequality.lean`, side `L = n h`, fields with values in a real inner
product space) and the unit-torus reconstruction files (`curvLog`, `linCurl`, `slots` of
`Continuum/NativeYangMillsIdentification.lean`): at `h = 1/N` the side is `L = 1`, the nodal norm
`periodicHodgeNormSq` is `gridNorm²`, `gridFwd (1/N)` is the forward difference `DpV`, and the
Lie-algebra values `A_μ(x) ∈ 𝔸` are read in the inner product space `E` through a bounded linear
`T : 𝔸 → E` with `‖X‖ ≤ c ‖T X‖` (for `𝔲(N) ⊂ M_N(ℂ)`: the Frobenius identification).

* `norm_nonlin_sub_le` (**`eq:native-YM-envelope`, Lipschitz half, pointwise**): on the chart
  `h |W| ≤ 1/32`, `‖𝒩_h(A) - 𝒩_h(B)‖ ≤ 5 (|W(A)| + |W(B)|) |W(A - B)|` (commutator polarisation and
  the Cauchy-estimate Lipschitz bound `PlaquetteLogDerivative.norm_bchRem_sub_le` for the cubic BCH
  remainder);
* `gridNorm_nonlin_sub_le` (**its `L²_h` form**):
  `‖𝒩_h(A) - 𝒩_h(B)‖_{2,h} ≤ 5 ‖|W(A)| + |W(B)|‖_{4,h} ‖|W(A-B)|‖_{4,h}`, and `g4_slotFn_le`:
  `‖|W(A)|‖_{4,h} ≤ 2(‖A_μ‖_{4,h} + ‖A_ν‖_{4,h})`;
* `hodge_bound`: the exact Hodge identity `lem:native-discrete-Hodge` in the form
  `Σ_{μ,ν} ‖D⁺_μ T w_ν‖_{2,h} ≤ 4 (Σ_{μ<ν} ‖T(d⁺w)_{μν}‖_{2,h} + ‖δ_h T w‖_{2,h})`;
* `g4_le_sobolev`: the uniform grid Sobolev inequality `‖u‖_{4,h} ≤ 3 Σ_μ ‖D⁺_μ u‖_{2,h} + 4 ‖u‖_{2,h}`;
* `coulomb_absorption` (**`eq:native-Coulomb-explicit-absorption`**): if `δ_h T A = 0`, both
  `A`, `B` lie in the chart and `‖A_μ‖_{4,h}, ‖B_μ‖_{4,h} ≤ a` with `23040 ‖T‖ c a ≤ 1`, then
  `Σ_{μ,ν} ‖D⁺_μ T(A - B)_ν‖_{2,h} ≤
     8 (‖T‖ Σ_{μ<ν} ‖F_h(A)_{μν} - F_h(B)_{μν}‖_{2,h} + ‖δ_h T B‖_{2,h}) + 3 Σ_ν ‖T(A - B)_ν‖_{2,h}`.
  With `B = 0` this is the a priori estimate of the theorem.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.NativeCoulomb

open TorusTrigReconstruction NativeCriticalGrid TorusPiecewiseConstantTranslation LogBCH
  NativeYMIdentification PlaquetteLogDerivative NativeYMVariation NativeGridLp NativeHiggs

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fact_one_le_four_c : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two_c : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder442_c : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two

/-! ### Nodal `L⁴` norms at mesh `1/N` -/

section Norms

variable {N : ℕ} [NeZero N]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The nodal `L⁴` norm `‖u‖_{4,h}` at mesh `h = 1/N`. -/
def g4 (u : LatticeTorusPlancherel.Grid 4 N → F) : ℝ := GridSobolev.gridL4Norm ((N : ℝ)⁻¹) u

theorem g4_nonneg (u : LatticeTorusPlancherel.Grid 4 N → F) : 0 ≤ g4 u :=
  GridSobolev.gridL4Norm_nonneg (by positivity) u

theorem eLpNorm_pc_four_g4 (u : LatticeTorusPlancherel.Grid 4 N → F) :
    eLpNorm (pc u) 4 (volume : Measure (UnitAddTorus (Fin 4))) = ENNReal.ofReal (g4 u) :=
  eLpNorm_pc_four_eq u

theorem g4_eq_toReal (u : LatticeTorusPlancherel.Grid 4 N → F) :
    g4 u = (eLpNorm (pc u) 4 (volume : Measure (UnitAddTorus (Fin 4)))).toReal := by
  rw [eLpNorm_pc_four_g4, ENNReal.toReal_ofReal (g4_nonneg u)]

theorem gridNorm_eq_toReal (u : LatticeTorusPlancherel.Grid 4 N → F) :
    gridNorm u = (eLpNorm (pc u) 2 (volume : Measure (UnitAddTorus (Fin 4)))).toReal := by
  rw [eLpNorm_pc_two_eq, ENNReal.toReal_ofReal (gridNorm_nonneg u)]

theorem gridNorm_le_g4 (u : LatticeTorusPlancherel.Grid 4 N → F) : gridNorm u ≤ g4 u := by
  have h := eLpNorm_le_eLpNorm_of_exponent_le (μ := (volume : Measure (UnitAddTorus (Fin 4))))
    (p := 2) (q := 4) (by norm_num) (stronglyMeasurable_pc u).aestronglyMeasurable
  rw [eLpNorm_pc_two_eq, eLpNorm_pc_four_g4] at h
  exact (ENNReal.ofReal_le_ofReal_iff (g4_nonneg u)).1 h

theorem g4_add_le (u v : LatticeTorusPlancherel.Grid 4 N → F) : g4 (u + v) ≤ g4 u + g4 v := by
  have h := eLpNorm_add_le (μ := (volume : Measure (UnitAddTorus (Fin 4))))
    (stronglyMeasurable_pc u).aestronglyMeasurable (stronglyMeasurable_pc v).aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  rw [show pc u + pc v = pc (u + v) from rfl, eLpNorm_pc_four_g4, eLpNorm_pc_four_g4,
    eLpNorm_pc_four_g4, ← ENNReal.ofReal_add (g4_nonneg u) (g4_nonneg v)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (g4_nonneg u) (g4_nonneg v))).1 h

theorem g4_le_mul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {a : ℝ} (ha : 0 ≤ a)
    {u : LatticeTorusPlancherel.Grid 4 N → F} {v : LatticeTorusPlancherel.Grid 4 N → G}
    (h : ∀ x, ‖u x‖ ≤ a * ‖v x‖) : g4 u ≤ a * g4 v :=
  gridL4Norm_le_mul (by positivity) ha h

theorem g4_comp_add (u : LatticeTorusPlancherel.Grid 4 N → F) (c : LatticeTorusPlancherel.Grid 4 N) :
    g4 (fun x => u (x + c)) = g4 u := by
  unfold g4 GridSobolev.gridL4Norm
  congr 2
  exact Equiv.sum_comp (Equiv.addRight c) (fun x => ‖u x‖ ^ 4)

theorem g4_norm (u : LatticeTorusPlancherel.Grid 4 N → F) : g4 (fun x => ‖u x‖) = g4 u := by
  unfold g4 GridSobolev.gridL4Norm
  simp only [norm_norm]

theorem le_g4 (u : LatticeTorusPlancherel.Grid 4 N → F) (x : LatticeTorusPlancherel.Grid 4 N) :
    (N : ℝ)⁻¹ * ‖u x‖ ≤ g4 u := by
  have hN : (0 : ℝ) < (N : ℝ)⁻¹ := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have h4 : g4 u ^ 4 = (N : ℝ)⁻¹ ^ 4 * ∑ y, ‖u y‖ ^ 4 := by
    unfold g4 GridSobolev.gridL4Norm
    rw [Fintype.card_fin, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hs : (N : ℝ)⁻¹ ^ 4 * ‖u x‖ ^ 4 ≤ (N : ℝ)⁻¹ ^ 4 * ∑ y, ‖u y‖ ^ 4 :=
    mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun y => ‖u y‖ ^ 4)
      (fun _ _ => by positivity) (Finset.mem_univ x)) (by positivity)
  rw [← h4, ← mul_pow] at hs
  exact (pow_le_pow_iff_left₀ (by positivity) (g4_nonneg u) (by norm_num)).1 hs

/-- **Uniform grid Sobolev** at mesh `1/N` (side `1`): `‖u‖_{4,h} ≤ 3 Σ_μ ‖D⁺_μ u‖_{2,h} + 4 ‖u‖_{2,h}`. -/
theorem g4_le_sobolev (u : LatticeTorusPlancherel.Grid 4 N → F) :
    g4 u ≤ 3 * ∑ μ, gridNorm (DpV μ u) + 4 * gridNorm u := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h := GridSobolev.grid_sobolev_L4 (inv_pos.2 hN) (Fintype.card_fin 4) u
  rw [mul_inv_cancel₀ hN.ne', div_one] at h
  have hf : ∀ i, GridSobolev.gridFwd ((N : ℝ)⁻¹) i u = DpV i u := by
    intro i; funext x; simp [GridSobolev.gridFwd, DpV, GridSobolev.gridStep]
  simp only [hf, gridL2Norm_inv_eq_gridNorm] at h
  exact h

/-- Hölder `L⁴ × L⁴ → L²` on the grid (through the raw reconstruction). -/
theorem gridNorm_mul_le (a b : LatticeTorusPlancherel.Grid 4 N → ℝ) :
    gridNorm (fun x => a x * b x) ≤ g4 a * g4 b := by
  have h := eLpNorm_bilin_le' (p := 4) (q := 4) (r := 2) (ν := (volume : Measure (UnitAddTorus (Fin 4))))
    (ContinuousLinearMap.mul ℝ ℝ) (stronglyMeasurable_pc a).aestronglyMeasurable
    (stronglyMeasurable_pc b).aestronglyMeasurable
  have hM : (‖ContinuousLinearMap.mul ℝ ℝ‖₊ : ℝ≥0∞) ≤ 1 := by
    rw [ENNReal.coe_le_one_iff, ← NNReal.coe_le_coe]
    exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have e : (fun y => ContinuousLinearMap.mul ℝ ℝ (pc a y) (pc b y)) = pc (fun x => a x * b x) := by
    funext y; rfl
  rw [e, eLpNorm_pc_two_eq, eLpNorm_pc_four_g4, eLpNorm_pc_four_g4] at h
  have h' : ENNReal.ofReal (gridNorm fun x => a x * b x) ≤ ENNReal.ofReal (g4 a * g4 b) := by
    rw [ENNReal.ofReal_mul (g4_nonneg a)]
    calc ENNReal.ofReal (gridNorm fun x => a x * b x) ≤
          ↑‖ContinuousLinearMap.mul ℝ ℝ‖₊ * ENNReal.ofReal (g4 a) * ENNReal.ofReal (g4 b) := h
      _ ≤ 1 * ENNReal.ofReal (g4 a) * ENNReal.ofReal (g4 b) := by gcongr
      _ = _ := by rw [one_mul]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (g4_nonneg a) (g4_nonneg b))).1 h'

theorem gridNorm_neg (u : LatticeTorusPlancherel.Grid 4 N → F) : gridNorm (-u) = gridNorm u := by
  unfold gridNorm; simp [norm_neg]

theorem gridNorm_sub_le (u v : LatticeTorusPlancherel.Grid 4 N → F) :
    gridNorm (u - v) ≤ gridNorm u + gridNorm v := by
  have := gridNorm_add_le u (-v)
  rwa [← sub_eq_add_neg, gridNorm_neg] at this

theorem gridNorm_map_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G)
    (u : LatticeTorusPlancherel.Grid 4 N → F) :
    gridNorm (fun x => L (u x)) ≤ ‖L‖ * gridNorm u := by
  have : gridNorm (fun x => L (u x)) ≤ gridNorm (fun x => ‖L‖ * ‖u x‖) :=
    gridNorm_mono fun x => by
      rw [Real.norm_of_nonneg (by positivity)]; exact L.le_opNorm _
  refine this.trans (le_of_eq ?_)
  have := gridNorm_const_mul (d := Fin 4) (N := N) (fun x => ‖u x‖) (norm_nonneg L)
  rw [this]
  congr 1
  unfold gridNorm; simp only [norm_norm]

end Norms

/-! ### The Lipschitz plaquette envelope -/

section Envelope

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {N : ℕ} [NeZero N]

/-- The nonlinear part `𝒩_h(A) = F^h(A) - (D⁺_μ A_ν - D⁺_ν A_μ)` of the literal curvature. -/
def nonlin (N : ℕ) (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) : 𝔸 :=
  curvLog N A x μ ν - linCurl A x μ ν

/-- The slot size `|W_{μν}(A)(x)|`. -/
def slotFn (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (μ ν : Fin 4) :
    LatticeTorusPlancherel.Grid 4 N → ℝ :=
  fun x => normSum (slots A x μ ν)

theorem nonlin_eq (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    nonlin N A x μ ν = commTerm (slots A x μ ν) +
      ((N : ℝ) ^ 2) • bchRem ((slots A x μ ν).map fun v => (N : ℝ)⁻¹ • v) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [nonlin, curvLog, logOnePlus_expProd_eq, ← slots_sum, sum_map_smul', commTerm_map_smul]
  simp only [smul_add, smul_smul]
  rw [show (N : ℝ) ^ 2 * (N : ℝ)⁻¹ = N by field_simp,
    show (N : ℝ) ^ 2 * (N : ℝ)⁻¹ ^ 2 = 1 by field_simp, one_smul]
  abel

theorem subList_slots (A B : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    subList (slots A x μ ν) (slots B x μ ν) = slots (A - B) x μ ν := by
  simp only [subList, slots, List.zipWith_cons_cons, List.zipWith_nil_right, Pi.sub_apply,
    neg_sub_neg]
  congr 2 <;> abel

theorem subList_map_smul (c : ℝ) (L L' : List 𝔸) :
    subList (L.map fun v => c • v) (L'.map fun v => c • v) = (subList L L').map fun v => c • v := by
  induction L generalizing L' with
  | nil => simp [subList]
  | cons a L ih => cases L' with
    | nil => simp [subList]
    | cons b L' =>
        have := ih L'
        simp only [subList] at this ⊢
        simp only [List.map_cons, List.zipWith_cons_cons, this, smul_sub]

theorem length_slots (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) : (slots A x μ ν).length = 4 := rfl

/-- **`eq:native-YM-envelope`, Lipschitz half (pointwise)**: on the chart `h |W| ≤ 1/32`,
`‖𝒩_h(A) - 𝒩_h(B)‖ ≤ 5 (|W(A)| + |W(B)|) |W(A - B)|`. -/
theorem norm_nonlin_sub_le (A B : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4)
    (hA : (N : ℝ)⁻¹ * slotFn A μ ν x ≤ 1 / 32) (hB : (N : ℝ)⁻¹ * slotFn B μ ν x ≤ 1 / 32) :
    ‖nonlin N A x μ ν - nonlin N B x μ ν‖ ≤
      5 * (slotFn A μ ν x + slotFn B μ ν x) * slotFn (A - B) μ ν x := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set sA := slotFn A μ ν x
  set sB := slotFn B μ ν x
  set sD := slotFn (A - B) μ ν x
  have hsA : 0 ≤ sA := normSum_nonneg _
  have hsB : 0 ≤ sB := normSum_nonneg _
  have hsD : 0 ≤ sD := normSum_nonneg _
  rw [nonlin_eq, nonlin_eq]
  have e : commTerm (slots A x μ ν) + ((N : ℝ) ^ 2) • bchRem ((slots A x μ ν).map
      fun v => (N : ℝ)⁻¹ • v) - (commTerm (slots B x μ ν) + ((N : ℝ) ^ 2) •
      bchRem ((slots B x μ ν).map fun v => (N : ℝ)⁻¹ • v)) =
      (commTerm (slots A x μ ν) - commTerm (slots B x μ ν)) + ((N : ℝ) ^ 2) •
        (bchRem ((slots A x μ ν).map fun v => (N : ℝ)⁻¹ • v) -
          bchRem ((slots B x μ ν).map fun v => (N : ℝ)⁻¹ • v)) := by
    rw [smul_sub]; abel
  rw [e]
  have h1 := norm_commTerm_sub_le (L := slots A x μ ν) (L' := slots B x μ ν) rfl
  rw [subList_slots] at h1
  set m := (N : ℝ)⁻¹ * (sA + sB)
  have hmA : normSum ((slots A x μ ν).map fun v => (N : ℝ)⁻¹ • v) ≤ max ((N : ℝ)⁻¹ * sA)
      ((N : ℝ)⁻¹ * sB) := by
    rw [normSum_map_smul, abs_of_pos (inv_pos.2 hN)]; exact le_max_left _ _
  have hmB : normSum ((slots B x μ ν).map fun v => (N : ℝ)⁻¹ • v) ≤ max ((N : ℝ)⁻¹ * sA)
      ((N : ℝ)⁻¹ * sB) := by
    rw [normSum_map_smul, abs_of_pos (inv_pos.2 hN)]; exact le_max_right _ _
  have h2 := norm_bchRem_sub_le (L := (slots A x μ ν).map fun v => (N : ℝ)⁻¹ • v)
    (L' := (slots B x μ ν).map fun v => (N : ℝ)⁻¹ • v) (by simp [slots])
    (max_le hA hB) hmA hmB
  rw [subList_map_smul, subList_slots, normSum_map_smul, abs_of_pos (inv_pos.2 hN)] at h2
  have hmax : max ((N : ℝ)⁻¹ * sA) ((N : ℝ)⁻¹ * sB) ≤ (N : ℝ)⁻¹ * (sA + sB) := by
    refine max_le ?_ ?_ <;> nlinarith [inv_pos.2 hN]
  have hmax0 : 0 ≤ max ((N : ℝ)⁻¹ * sA) ((N : ℝ)⁻¹ * sB) :=
    le_max_of_le_left (by positivity)
  have hmax1 : max ((N : ℝ)⁻¹ * sA) ((N : ℝ)⁻¹ * sB) ≤ 1 / 32 := max_le hA hB
  calc ‖(commTerm (slots A x μ ν) - commTerm (slots B x μ ν)) + ((N : ℝ) ^ 2) •
        (bchRem ((slots A x μ ν).map fun v => (N : ℝ)⁻¹ • v) -
          bchRem ((slots B x μ ν).map fun v => (N : ℝ)⁻¹ • v))‖
      ≤ (sA + 2 * sB) * sD + (N : ℝ) ^ 2 * (48 * max ((N : ℝ)⁻¹ * sA) ((N : ℝ)⁻¹ * sB) ^ 2 *
          ((N : ℝ)⁻¹ * sD)) := by
        refine (norm_add_le _ _).trans (add_le_add h1 ?_)
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 5 * (sA + sB) * sD := by
        set M := max ((N : ℝ)⁻¹ * sA) ((N : ℝ)⁻¹ * sB)
        have hNM : (N : ℝ) ^ 2 * (48 * M ^ 2 * ((N : ℝ)⁻¹ * sD)) = 48 * M * (N * M) * sD := by
          field_simp
        have hNM2 : (N : ℝ) * M ≤ sA + sB := by
          calc (N : ℝ) * M ≤ N * ((N : ℝ)⁻¹ * (sA + sB)) := mul_le_mul_of_nonneg_left hmax hN.le
            _ = sA + sB := by field_simp
        rw [hNM]
        have : 48 * M * (N * M) * sD ≤ 48 * (1 / 32) * (sA + sB) * sD := by
          have := mul_le_mul hmax1 hNM2 (by positivity) (by norm_num)
          nlinarith
        nlinarith

theorem slotFn_nonneg (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (μ ν : Fin 4)
    (x : LatticeTorusPlancherel.Grid 4 N) : 0 ≤ slotFn A μ ν x := normSum_nonneg _

/-- `‖|W_{μν}(A)|‖_{4,h} ≤ 2 (‖A_μ‖_{4,h} + ‖A_ν‖_{4,h})`. -/
theorem g4_slotFn_le (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (μ ν : Fin 4) :
    g4 (slotFn A μ ν) ≤ 2 * (g4 (fun x => A x μ) + g4 (fun x => A x ν)) := by
  set f1 : LatticeTorusPlancherel.Grid 4 N → ℝ := fun x => ‖A x μ‖
  set f2 : LatticeTorusPlancherel.Grid 4 N → ℝ := fun x => ‖A (x + Pi.single μ 1) ν‖
  set f3 : LatticeTorusPlancherel.Grid 4 N → ℝ := fun x => ‖A (x + Pi.single ν 1) μ‖
  set f4 : LatticeTorusPlancherel.Grid 4 N → ℝ := fun x => ‖A x ν‖
  have e : slotFn A μ ν = f1 + f2 + f3 + f4 := by
    funext x; simp only [slotFn, normSum_slots, Pi.add_apply, f1, f2, f3, f4]
  have e1 : g4 f1 = g4 (fun x => A x μ) := g4_norm (fun x => A x μ)
  have e4 : g4 f4 = g4 (fun x => A x ν) := g4_norm (fun x => A x ν)
  have e2 : g4 f2 = g4 (fun x => A x ν) :=
    (g4_norm (fun x => A (x + Pi.single μ 1) ν)).trans (g4_comp_add (fun y => A y ν) _)
  have e3 : g4 f3 = g4 (fun x => A x μ) :=
    (g4_norm (fun x => A (x + Pi.single ν 1) μ)).trans (g4_comp_add (fun y => A y μ) _)
  have h12 := g4_add_le f1 f2
  have h123 := g4_add_le (f1 + f2) f3
  have h1234 := g4_add_le (f1 + f2 + f3) f4
  rw [e]
  linarith

/-- **`eq:native-YM-envelope`, Lipschitz half (`L²_h` form)**. -/
theorem gridNorm_nonlin_sub_le (A B : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) (μ ν : Fin 4)
    (hA : ∀ x, (N : ℝ)⁻¹ * slotFn A μ ν x ≤ 1 / 32)
    (hB : ∀ x, (N : ℝ)⁻¹ * slotFn B μ ν x ≤ 1 / 32) :
    gridNorm (fun x => nonlin N A x μ ν - nonlin N B x μ ν) ≤
      5 * (g4 (slotFn A μ ν) + g4 (slotFn B μ ν)) * g4 (slotFn (A - B) μ ν) := by
  have h1 : gridNorm (fun x => nonlin N A x μ ν - nonlin N B x μ ν) ≤
      gridNorm (fun x => (5 * (slotFn A μ ν x + slotFn B μ ν x)) * slotFn (A - B) μ ν x) :=
    gridNorm_mono fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (add_nonneg (slotFn_nonneg A μ ν x) (slotFn_nonneg B μ ν x))) (slotFn_nonneg _ μ ν x))]
      exact norm_nonlin_sub_le A B x μ ν (hA x) (hB x)
  refine h1.trans ((gridNorm_mul_le _ _).trans ?_)
  gcongr
  · exact g4_nonneg _
  · calc g4 (fun x => 5 * (slotFn A μ ν x + slotFn B μ ν x))
        ≤ 5 * g4 (fun x => slotFn A μ ν x + slotFn B μ ν x) :=
          g4_le_mul (by norm_num) fun x => by
            rw [Real.norm_of_nonneg (mul_nonneg (by norm_num)
              (add_nonneg (slotFn_nonneg A μ ν x) (slotFn_nonneg B μ ν x))),
              Real.norm_of_nonneg (add_nonneg (slotFn_nonneg A μ ν x) (slotFn_nonneg B μ ν x))]
      _ ≤ 5 * (g4 (slotFn A μ ν) + g4 (slotFn B μ ν)) := by
          gcongr; exact g4_add_le (slotFn A μ ν) (slotFn B μ ν)

end Envelope

/-! ### The Hodge identity in unit-torus notation -/

section Hodge

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : ℕ} [NeZero N]

/-- The ordered pairs `μ < ν`. -/
def pairs4 : Finset (Fin 4 × Fin 4) := (univ : Finset (Fin 4 × Fin 4)).filter fun p => p.1 < p.2

theorem card_pairs4 : pairs4.card = 6 := by decide

/-- The discrete codifferential `δ_h(T w) = -Σ_μ D⁻_μ (T w_μ)` at mesh `1/N`. -/
def codiffT (T : 𝔸 →L[ℝ] E) (w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) :
    LatticeTorusPlancherel.Grid 4 N → E :=
  periodicHodgeCodiff ((N : ℝ)⁻¹) GridSobolev.gridStep (fun μ x => T (w x μ))

theorem codiffT_sub (T : 𝔸 →L[ℝ] E) (w w' : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) :
    codiffT T (w - w') = codiffT T w - codiffT T w' := by
  funext x
  simp only [codiffT, periodicHodgeCodiff, periodicHodgeBwd, Pi.sub_apply, map_sub, smul_sub,
    Finset.sum_sub_distrib, neg_sub_neg]
  abel

theorem codiffT_zero (T : 𝔸 →L[ℝ] E) : codiffT T (0 : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) = 0 := by
  funext x; simp [codiffT, periodicHodgeCodiff, periodicHodgeBwd]

theorem normSq_eq_gridNorm_sq (u : LatticeTorusPlancherel.Grid 4 N → E) :
    periodicHodgeNormSq (Fin 4) ((N : ℝ)⁻¹) u = gridNorm u ^ 2 := by
  rw [gridNorm, Real.sq_sqrt (by positivity), periodicHodgeNormSq, one_div]

theorem fwd_eq_DpV (μ : Fin 4) (u : LatticeTorusPlancherel.Grid 4 N → E) :
    periodicHodgeFwd ((N : ℝ)⁻¹) GridSobolev.gridStep μ u = DpV μ u := by
  funext x; simp [periodicHodgeFwd, DpV, GridSobolev.gridStep]

theorem T_linCurl (T : 𝔸 →L[ℝ] E) (w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (μ ν : Fin 4) (x : LatticeTorusPlancherel.Grid 4 N) :
    T (linCurl w x μ ν) = periodicHodgeExtD ((N : ℝ)⁻¹) GridSobolev.gridStep
      (fun μ x => T (w x μ)) μ ν x := by
  simp [linCurl, DpA, periodicHodgeExtD, periodicHodgeFwd, GridSobolev.gridStep, map_sub, map_smul]

theorem sum_le_four_sqrt (a : Fin 4 → Fin 4 → ℝ) :
    ∑ μ, ∑ ν, a μ ν ≤ 4 * √(∑ μ, ∑ ν, a μ ν ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin 4 × Fin 4)) (fun _ => (1 : ℝ))
    (fun p => a p.1 p.2)
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  rw [show √((4 * 4 : ℕ) : ℝ) = 4 by
    rw [show ((4 * 4 : ℕ) : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  rw [← Finset.sum_product' (f := fun μ ν => a μ ν), ← Finset.sum_product' (f := fun μ ν => a μ ν ^ 2)]
  exact h

theorem sqrt_sum_sq_add_sq_le (s : Finset (Fin 4 × Fin 4)) (b : Fin 4 × Fin 4 → ℝ)
    (hb : ∀ p, 0 ≤ b p) {c : ℝ} (hc : 0 ≤ c) :
    √(∑ p ∈ s, b p ^ 2 + c ^ 2) ≤ ∑ p ∈ s, b p + c := by
  rw [Real.sqrt_le_left (add_nonneg (Finset.sum_nonneg fun p _ => hb p) hc)]
  have h1 : ∑ p ∈ s, b p ^ 2 ≤ (∑ p ∈ s, b p) ^ 2 := by
    rw [sq (∑ p ∈ s, b p), Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [sq]
    exact Finset.single_le_sum (f := fun j => b i * b j) (fun j _ => mul_nonneg (hb i) (hb j)) hi
  have h0 : 0 ≤ ∑ p ∈ s, b p := Finset.sum_nonneg fun p _ => hb p
  nlinarith

/-- **The exact Hodge identity** (`lem:native-discrete-Hodge`) in the form
`Σ_{μ,ν} ‖D⁺_μ T w_ν‖_{2,h} ≤ 4 (Σ_{μ<ν} ‖T(d⁺w)_{μν}‖_{2,h} + ‖δ_h T w‖_{2,h})`. -/
theorem hodge_bound (T : 𝔸 →L[ℝ] E) (w : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸) :
    ∑ μ, ∑ ν, gridNorm (DpV μ (fun x => T (w x ν))) ≤
      4 * (∑ p ∈ pairs4, gridNorm (fun x => T (linCurl w x p.1 p.2)) +
        gridNorm (codiffT T w)) := by
  have hH := periodicHodge_identity ((N : ℝ)⁻¹) GridSobolev.gridStep (fun μ x => T (w x μ))
  simp only [fwd_eq_DpV, normSq_eq_gridNorm_sq, periodicHodgeExtDNormSq] at hH
  have hE : ∀ p : Fin 4 × Fin 4, periodicHodgeExtD ((N : ℝ)⁻¹) GridSobolev.gridStep
      (fun μ x => T (w x μ)) p.1 p.2 = fun x => T (linCurl w x p.1 p.2) := by
    intro p; funext x; rw [T_linCurl]
  simp only [hE] at hH
  refine (sum_le_four_sqrt _).trans ?_
  rw [hH]
  gcongr
  exact sqrt_sum_sq_add_sq_le pairs4 (fun p => gridNorm (fun x => T (linCurl w x p.1 p.2)))
    (fun p => gridNorm_nonneg _) (gridNorm_nonneg _)

theorem linCurl_sub (A B : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (x : LatticeTorusPlancherel.Grid 4 N) (μ ν : Fin 4) :
    linCurl (A - B) x μ ν = (curvLog N A x μ ν - curvLog N B x μ ν) -
      (nonlin N A x μ ν - nonlin N B x μ ν) := by
  simp only [nonlin, linCurl, DpA, Pi.sub_apply, smul_sub]
  abel

/-- **The discrete Coulomb absorption inequality** (`eq:native-Coulomb-explicit-absorption`, unit
torus, explicit constants).  Let `δ_h T A = 0`, let `A` and `B` lie in the scaled chart
`h |W_{μν}| ≤ 1/32`, and let `‖A_μ‖_{4,h}, ‖B_μ‖_{4,h} ≤ a` with `23040 ‖T‖ c a ≤ 1`.  Then, with
`w = A - B`,
`Σ_{μ,ν} ‖D⁺_μ T w_ν‖_{2,h} ≤ 8 (‖T‖ Σ_{μ<ν} ‖F_h(A)_{μν} - F_h(B)_{μν}‖_{2,h} + ‖δ_h T B‖_{2,h})
  + 3 Σ_ν ‖T w_ν‖_{2,h}`. -/
theorem coulomb_absorption (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖)
    (A B : LatticeTorusPlancherel.Grid 4 N → Fin 4 → 𝔸)
    (hAch : ∀ x μ ν, (N : ℝ)⁻¹ * slotFn A μ ν x ≤ 1 / 32)
    (hBch : ∀ x μ ν, (N : ℝ)⁻¹ * slotFn B μ ν x ≤ 1 / 32)
    (hδ : codiffT T A = 0) {a : ℝ} (hA4 : ∀ μ, g4 (fun x => A x μ) ≤ a)
    (hB4 : ∀ μ, g4 (fun x => B x μ) ≤ a) (ha : 23040 * ‖T‖ * c * a ≤ 1) :
    ∑ μ, ∑ ν, gridNorm (DpV μ (fun x => T ((A - B) x ν))) ≤
      8 * (‖T‖ * ∑ p ∈ pairs4, gridNorm (fun x => curvLog N A x p.1 p.2 - curvLog N B x p.1 p.2) +
        gridNorm (codiffT T B)) + 3 * ∑ ν, gridNorm (fun x => T ((A - B) x ν)) := by
  set w := A - B
  set G := ∑ μ, ∑ ν, gridNorm (DpV μ (fun x => T (w x ν)))
  set Z := ∑ ν, gridNorm (fun x => T (w x ν))
  set S4 := ∑ κ, g4 (fun x => T (w x κ))
  set ΔF := ∑ p ∈ pairs4, gridNorm (fun x => curvLog N A x p.1 p.2 - curvLog N B x p.1 p.2)
  have ha0 : 0 ≤ a := (g4_nonneg _).trans (hA4 0)
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => gridNorm_nonneg _
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => gridNorm_nonneg _
  have hΔF0 : 0 ≤ ΔF := Finset.sum_nonneg fun _ _ => gridNorm_nonneg _
  have hδB0 : 0 ≤ gridNorm (codiffT T B) := gridNorm_nonneg _
  -- Hodge
  have hH := hodge_bound T w
  have hcod : gridNorm (codiffT T w) = gridNorm (codiffT T B) := by
    rw [codiffT_sub, hδ, zero_sub, gridNorm_neg]
  rw [hcod] at hH
  -- Sobolev
  have hS4 : S4 ≤ 3 * G + 4 * Z := by
    have : ∀ κ, g4 (fun x => T (w x κ)) ≤ 3 * ∑ μ, gridNorm (DpV μ (fun x => T (w x κ))) +
        4 * gridNorm (fun x => T (w x κ)) := fun κ => g4_le_sobolev _
    calc S4 ≤ ∑ κ, (3 * ∑ μ, gridNorm (DpV μ (fun x => T (w x κ))) +
          4 * gridNorm (fun x => T (w x κ))) := Finset.sum_le_sum fun κ _ => this κ
      _ = 3 * G + 4 * Z := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  -- the nonlinear packet
  have hw4 : ∀ μ, g4 (fun x => w x μ) ≤ c * S4 := by
    intro μ
    refine (g4_le_mul hc0 fun x => hc (w x μ)).trans ?_
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun κ => g4 (fun x => T (w x κ)))
      (fun _ _ => g4_nonneg _) (Finset.mem_univ μ)) hc0
  have hN : ∀ p ∈ pairs4, gridNorm (fun x => nonlin N A x p.1 p.2 - nonlin N B x p.1 p.2) ≤
      160 * a * c * S4 := by
    intro p _
    refine (gridNorm_nonlin_sub_le A B p.1 p.2 (fun x => hAch x _ _) (fun x => hBch x _ _)).trans ?_
    have hsA := g4_slotFn_le A p.1 p.2
    have hsB := g4_slotFn_le B p.1 p.2
    have hsw := g4_slotFn_le w p.1 p.2
    have h1 : g4 (slotFn A p.1 p.2) + g4 (slotFn B p.1 p.2) ≤ 8 * a := by
      linarith [hA4 p.1, hA4 p.2, hB4 p.1, hB4 p.2]
    have h2 : g4 (slotFn w p.1 p.2) ≤ 4 * (c * S4) := by linarith [hw4 p.1, hw4 p.2]
    calc 5 * (g4 (slotFn A p.1 p.2) + g4 (slotFn B p.1 p.2)) * g4 (slotFn w p.1 p.2)
        ≤ 5 * (8 * a) * (4 * (c * S4)) := by
          have h10 : 0 ≤ g4 (slotFn A p.1 p.2) + g4 (slotFn B p.1 p.2) :=
            add_nonneg (g4_nonneg _) (g4_nonneg _)
          have h20 : 0 ≤ g4 (slotFn w p.1 p.2) := g4_nonneg _
          have := mul_le_mul h1 h2 h20 (by linarith)
          nlinarith
      _ = 160 * a * c * S4 := by ring
  have hS40 : 0 ≤ S4 := Finset.sum_nonneg fun _ _ => g4_nonneg _
  have hlin : ∀ p ∈ pairs4, gridNorm (fun x => T (linCurl w x p.1 p.2)) ≤
      ‖T‖ * (gridNorm (fun x => curvLog N A x p.1 p.2 - curvLog N B x p.1 p.2) +
        160 * a * c * S4) := by
    intro p hp
    refine (gridNorm_map_le T _).trans (mul_le_mul_of_nonneg_left ?_ hT0)
    have e : (fun x => linCurl w x p.1 p.2) = (fun x => curvLog N A x p.1 p.2 - curvLog N B x p.1 p.2) -
        fun x => nonlin N A x p.1 p.2 - nonlin N B x p.1 p.2 := by
      funext x; rw [Pi.sub_apply, linCurl_sub]
    rw [e]
    exact (gridNorm_sub_le _ _).trans (add_le_add le_rfl (hN p hp))
  have hsum : ∑ p ∈ pairs4, gridNorm (fun x => T (linCurl w x p.1 p.2)) ≤
      ‖T‖ * ΔF + ‖T‖ * (960 * a * c * S4) := by
    refine (Finset.sum_le_sum hlin).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, card_pairs4, nsmul_eq_mul]
    ring
  -- absorption
  set K := ‖T‖ * a * c
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hT0 ha0) hc0
  have hK : 23040 * K ≤ 1 := by simpa [K, mul_comm, mul_left_comm, mul_assoc] using ha
  have hG1 : G ≤ 4 * (‖T‖ * ΔF + gridNorm (codiffT T B)) + 3840 * K * (3 * G + 4 * Z) := by
    have h3 : ‖T‖ * (960 * a * c * S4) ≤ 960 * K * (3 * G + 4 * Z) := by
      have : ‖T‖ * (960 * a * c * S4) = 960 * K * S4 := by simp only [K]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hS4 (by positivity)
    calc G ≤ 4 * (∑ p ∈ pairs4, gridNorm (fun x => T (linCurl w x p.1 p.2)) +
          gridNorm (codiffT T B)) := hH
      _ ≤ 4 * (‖T‖ * ΔF + ‖T‖ * (960 * a * c * S4) + gridNorm (codiffT T B)) := by
          gcongr
      _ ≤ 4 * (‖T‖ * ΔF + 960 * K * (3 * G + 4 * Z) + gridNorm (codiffT T B)) := by
          gcongr
      _ = 4 * (‖T‖ * ΔF + gridNorm (codiffT T B)) + 3840 * K * (3 * G + 4 * Z) := by ring
  have hKG : 11520 * K * G ≤ G / 2 := by nlinarith
  have hKZ : 30720 * K * Z ≤ 3 * Z := by nlinarith
  nlinarith

end Hodge

end

end RenewalGeometry.NativeCoulomb
