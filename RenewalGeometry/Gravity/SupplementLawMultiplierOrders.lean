/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SupplementLawMultiplierExact

/-!
# Uniform fourth-order multiplier bounds in physical space
  (`lem:supp-law-multiplier`, `eq:supp-law-domination`, `eq:supp-law-orders`,
  `eq:supp-open-norms`; emergent-spacetime manuscript)

`Gravity/SupplementLawMultiplierExact.lean` proves the domination
`h² ‖Λ_h w‖_h² ≤ 12 ∑_i ‖D_i^+ w‖_h²` (`eq:supp-law-domination`) in physical
space and the four order bounds `eq:supp-law-orders` on the Fourier side.
This file proves the four order bounds **directly in physical space**, for the
paper's own forward-difference Sobolev norms `eq:supp-open-norms`
`‖u‖_{r,h}² = ∑_{|α| ≤ r} ‖D^α u‖_h²`, `D^α = ∏_i (D_i^+)^{α_i}`
(`multiDiff`, `diffSobolevNorm`), with explicit constants `C_s` depending on
`s` only (no Fourier transform, no norm equivalence needed).

The tools are:
* all forward and backward differences commute, and `Λ_h` commutes with every
  `D_i^+` (`forwardDiff_comm`, `forwardDiff_gridLaplacian`,
  `gridLaplacian_multiDiff`), so `D^α Λ_h² q = Λ_h² D^α q`;
* `D_i^- v` is a translate of `D_i^+ v`, so
  `‖Λ_h w‖_h² ≤ 3 ∑_i ‖D_i^+ D_i^+ w‖_h²` (`gridNormSq_gridLaplacian_le`);
* the domination `eq:supp-law-domination` for the `h`-losing steps.

Per array `w` this gives (`biharmonic_bound_one/two/three`)
`h⁴ ‖Λ_h² w‖² ≤ 144 ∑_{i,j} ‖D_j D_i w‖²`,
`h⁴ ‖Λ_h² w‖² ≤ 36 h² ∑_{i,j} ‖D_j D_j D_i w‖²`,
`h⁴ ‖Λ_h² w‖² ≤ 9 h⁴ ∑_{i,j} ‖D_j D_j D_i D_i w‖²`,
and applying them to `w = D^α q` with `|α| ≤ s-1, s-2, s-3` yields
**`eq:supp-law-orders`** (`fourth_order_bounds_physical`, and
`law_multiplier_bounds` on the periodic grid together with the domination):

`h² ‖Λ_h² q‖_{s-1,h} ≤ C_s ‖q‖_{s+1,h}`, `h² ‖Λ_h² q‖_{s-2,h} ≤ C_s h ‖q‖_{s+1,h}`,
`h² ‖Λ_h² q‖_{s-3,h} ≤ C_s h² ‖q‖_{s+1,h}`, `h² ‖Λ_h² v‖_{s-3,h} ≤ C_s h ‖v‖_{s,h}`,

with `C_s = 36 √N_{s-1}`, `18 √N_{s-2}`, `9 √N_{s-3}`, `18 √N_{s-3}` where
`N_r = #{α : |α| ≤ r}`; `s ≥ 3` so that the three lower indices are genuine
(the paper uses `s ≥ 11`).  `exists_uniform_order_constants` records the
`h`-independence of the constants in existential form.
-/

namespace RenewalGeometry
namespace LawMultiplier

open Finset

noncomputable section

section Orders

variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Commutation of the difference operators -/

omit [Fintype G] in
/-- Forward differences commute. -/
theorem forwardDiff_comm (h : ℝ) (e e' : G) (w : G → F) :
    forwardDiff h e (forwardDiff h e' w) = forwardDiff h e' (forwardDiff h e w) := by
  funext x
  simp only [forwardDiff]
  rw [add_right_comm x e' e]
  simp only [smul_sub]
  abel

omit [Fintype G] in
theorem forwardDiff_commute (h : ℝ) (e e' : G) :
    Function.Commute (forwardDiff (F := F) h e) (forwardDiff h e') :=
  fun w => forwardDiff_comm h e e' w

omit [Fintype G] in
/-- The backward difference is a translate of the forward difference. -/
theorem backwardDiff_eq (h : ℝ) (e : G) (v : G → F) :
    backwardDiff h e v = fun x => forwardDiff h e v (x - e) := by
  funext x
  simp only [forwardDiff, backwardDiff, sub_add_cancel]

omit [Fintype G] in
theorem forwardDiff_shift (h : ℝ) (e e' : G) (v : G → F) :
    forwardDiff h e' (fun x => v (x - e)) = fun x => forwardDiff h e' v (x - e) := by
  funext x
  simp only [forwardDiff, sub_add_eq_add_sub]

omit [Fintype G] in
theorem forwardDiff_neg_sum (h : ℝ) (e' : G) (f : Fin 3 → G → F) :
    forwardDiff h e' (fun x => -∑ i, f i x) = fun x => -∑ i, forwardDiff h e' (f i) x := by
  funext x
  simp only [forwardDiff]
  rw [neg_sub_neg, ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_sub, smul_sub, neg_sub]

omit [Fintype G] in
/-- `D_i^+` commutes with `Λ_h`. -/
theorem forwardDiff_gridLaplacian (h : ℝ) (e : Fin 3 → G) (e' : G) (w : G → F) :
    forwardDiff h e' (gridLaplacian h e w) = gridLaplacian h e (forwardDiff h e' w) := by
  unfold gridLaplacian
  rw [forwardDiff_neg_sum]
  funext x
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : forwardDiff h e' (backwardDiff h (e i) (forwardDiff h (e i) w))
      = backwardDiff h (e i) (forwardDiff h (e i) (forwardDiff h e' w)) := by
    rw [backwardDiff_eq, backwardDiff_eq, forwardDiff_shift,
      forwardDiff_comm h e' (e i) (forwardDiff h (e i) w), forwardDiff_comm h e' (e i) w]
  rw [this]

omit [Fintype G] in
theorem gridLaplacian_commute (h : ℝ) (e : Fin 3 → G) (e' : G) :
    Function.Commute (gridLaplacian (F := F) h e) (forwardDiff h e') :=
  fun w => (forwardDiff_gridLaplacian h e e' w).symm

/-! ### Multi-index differences and the forward-difference Sobolev norms -/

/-- `D^α = (D_0^+)^{α_0} (D_1^+)^{α_1} (D_2^+)^{α_2}`. -/
def multiDiff (h : ℝ) (e : Fin 3 → G) (α : Fin 3 → ℕ) (w : G → F) : G → F :=
  (forwardDiff h (e 0))^[α 0] ((forwardDiff h (e 1))^[α 1] ((forwardDiff h (e 2))^[α 2] w))

omit [Fintype G] in
/-- `Λ_h D^α = D^α Λ_h`. -/
theorem gridLaplacian_multiDiff (h : ℝ) (e : Fin 3 → G) (α : Fin 3 → ℕ) (w : G → F) :
    gridLaplacian h e (multiDiff h e α w) = multiDiff h e α (gridLaplacian h e w) := by
  unfold multiDiff
  rw [(gridLaplacian_commute h e (e 0)).iterate_right (α 0),
    (gridLaplacian_commute h e (e 1)).iterate_right (α 1),
    (gridLaplacian_commute h e (e 2)).iterate_right (α 2)]

omit [Fintype G] in
/-- `D_i^+ D^α = D^{α + e_i}`. -/
theorem forwardDiff_multiDiff (h : ℝ) (e : Fin 3 → G) (α : Fin 3 → ℕ) (w : G → F) (i : Fin 3) :
    forwardDiff h (e i) (multiDiff h e α w) = multiDiff h e (Function.update α i (α i + 1)) w := by
  unfold multiDiff
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Function.update_self,
      Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
      Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
    rw [← Function.iterate_succ_apply' (forwardDiff h (e 0))]
  · simp only [Fin.mk_one, Fin.isValue, Function.update_self,
      Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
      Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
    rw [(forwardDiff_commute h (e 1) (e 0)).iterate_right (α 0),
      ← Function.iterate_succ_apply' (forwardDiff h (e 1))]
  · simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self,
      Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
      Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
    rw [(forwardDiff_commute h (e 2) (e 0)).iterate_right (α 0),
      (forwardDiff_commute h (e 2) (e 1)).iterate_right (α 1),
      ← Function.iterate_succ_apply' (forwardDiff h (e 2))]

theorem sum_update_succ (α : Fin 3 → ℕ) (i : Fin 3) :
    ∑ j, Function.update α i (α i + 1) j = ∑ j, α j + 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase Finset.univ α (Finset.mem_univ i)]
  ring

/-- The multi-indices `α ∈ ℕ³` with `|α| ≤ r`. -/
def multiIndices (r : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 3 => Finset.range (r + 1)).filter fun α => ∑ i, α i ≤ r

theorem mem_multiIndices {r : ℕ} {α : Fin 3 → ℕ} : α ∈ multiIndices r ↔ ∑ i, α i ≤ r := by
  simp only [multiIndices, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => Nat.lt_succ_of_le (le_trans ?_ h), h⟩
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)

/-- The forward-difference Sobolev norm squared `‖u‖_{r,h}² = ∑_{|α| ≤ r} ‖D^α u‖_h²`
(`eq:supp-open-norms`). -/
def diffSobolevNormSq (h : ℝ) (e : Fin 3 → G) (r : ℕ) (u : G → F) : ℝ :=
  ∑ α ∈ multiIndices r, gridNormSq h (multiDiff h e α u)

/-- The forward-difference Sobolev norm `‖u‖_{r,h}` (`eq:supp-open-norms`). -/
def diffSobolevNorm (h : ℝ) (e : Fin 3 → G) (r : ℕ) (u : G → F) : ℝ :=
  Real.sqrt (diffSobolevNormSq h e r u)

/-- `Λ_h²`. -/
def biharmonic (h : ℝ) (e : Fin 3 → G) (w : G → F) : G → F :=
  gridLaplacian h e (gridLaplacian h e w)

theorem diffSobolevNormSq_nonneg (h : ℝ) (hh : 0 ≤ h) (e : Fin 3 → G) (r : ℕ) (u : G → F) :
    0 ≤ diffSobolevNormSq h e r u :=
  Finset.sum_nonneg fun _ _ => gridNormSq_nonneg h hh _

/-- A single term `‖D^α u‖_h²`, `|α| ≤ r`, is bounded by `‖u‖_{r,h}²`. -/
theorem gridNormSq_multiDiff_le (h : ℝ) (hh : 0 ≤ h) (e : Fin 3 → G) {r : ℕ} {α : Fin 3 → ℕ}
    (hα : ∑ i, α i ≤ r) (u : G → F) :
    gridNormSq h (multiDiff h e α u) ≤ diffSobolevNormSq h e r u :=
  Finset.single_le_sum (f := fun β => gridNormSq h (multiDiff h e β u))
    (fun _ _ => gridNormSq_nonneg h hh _) (mem_multiIndices.mpr hα)

/-- `‖D_j D_i D^α u‖_h² ≤ ‖u‖_{r,h}²` when `|α| + 2 ≤ r`. -/
theorem gridNormSq_two_step_le (h : ℝ) (hh : 0 ≤ h) (e : Fin 3 → G) {r : ℕ} {α : Fin 3 → ℕ}
    (hα : ∑ i, α i + 2 ≤ r) (u : G → F) (i j : Fin 3) :
    gridNormSq h (forwardDiff h (e j) (forwardDiff h (e i) (multiDiff h e α u)))
      ≤ diffSobolevNormSq h e r u := by
  rw [forwardDiff_multiDiff, forwardDiff_multiDiff]
  refine gridNormSq_multiDiff_le h hh e ?_ u
  rw [sum_update_succ, sum_update_succ]
  omega

/-- `‖D_j D_j D_i D^α u‖_h² ≤ ‖u‖_{r,h}²` when `|α| + 3 ≤ r`. -/
theorem gridNormSq_three_step_le (h : ℝ) (hh : 0 ≤ h) (e : Fin 3 → G) {r : ℕ} {α : Fin 3 → ℕ}
    (hα : ∑ i, α i + 3 ≤ r) (u : G → F) (i j : Fin 3) :
    gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
      (forwardDiff h (e i) (multiDiff h e α u)))) ≤ diffSobolevNormSq h e r u := by
  rw [forwardDiff_multiDiff, forwardDiff_multiDiff, forwardDiff_multiDiff]
  refine gridNormSq_multiDiff_le h hh e ?_ u
  rw [sum_update_succ, sum_update_succ, sum_update_succ]
  omega

/-- `‖D_j D_j D_i D_i D^α u‖_h² ≤ ‖u‖_{r,h}²` when `|α| + 4 ≤ r`. -/
theorem gridNormSq_four_step_le (h : ℝ) (hh : 0 ≤ h) (e : Fin 3 → G) {r : ℕ} {α : Fin 3 → ℕ}
    (hα : ∑ i, α i + 4 ≤ r) (u : G → F) (i j : Fin 3) :
    gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j) (forwardDiff h (e i)
      (forwardDiff h (e i) (multiDiff h e α u))))) ≤ diffSobolevNormSq h e r u := by
  rw [forwardDiff_multiDiff, forwardDiff_multiDiff, forwardDiff_multiDiff, forwardDiff_multiDiff]
  refine gridNormSq_multiDiff_le h hh e ?_ u
  rw [sum_update_succ, sum_update_succ, sum_update_succ, sum_update_succ]
  omega

/-! ### Per-array bounds for `Λ_h²` -/

/-- `‖Λ_h w‖_h² ≤ 3 ∑_i ‖D_i^+ D_i^+ w‖_h²` (no `h` lost: `D_i^-` is a translate of `D_i^+`). -/
theorem gridNormSq_gridLaplacian_le (h : ℝ) (hh : 0 ≤ h) (e : Fin 3 → G) (w : G → F) :
    gridNormSq h (gridLaplacian h e w)
      ≤ 3 * ∑ i, gridNormSq h (forwardDiff h (e i) (forwardDiff h (e i) w)) := by
  unfold gridNormSq
  have hpt : ∀ x, ‖gridLaplacian h e w x‖ ^ 2
      ≤ 3 * ∑ i, ‖backwardDiff h (e i) (forwardDiff h (e i) w) x‖ ^ 2 := by
    intro x
    unfold gridLaplacian
    rw [norm_neg]
    exact norm_sum_three_sq_le fun i => backwardDiff h (e i) (forwardDiff h (e i) w) x
  have hsum : ∑ x, ‖gridLaplacian h e w x‖ ^ 2
      ≤ 3 * ∑ i, ∑ x, ‖forwardDiff h (e i) (forwardDiff h (e i) w) x‖ ^ 2 := by
    refine (Finset.sum_le_sum fun x _ => hpt x).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
    rw [backwardDiff_eq]
    exact (sum_norm_sq_sub (e i) _).le
  calc h ^ 3 * ∑ x, ‖gridLaplacian h e w x‖ ^ 2
      ≤ h ^ 3 * (3 * ∑ i, ∑ x, ‖forwardDiff h (e i) (forwardDiff h (e i) w) x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 3 * ∑ i, h ^ 3 * ∑ x, ‖forwardDiff h (e i) (forwardDiff h (e i) w) x‖ ^ 2 := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

/-- `h⁴ ‖Λ_h² w‖_h² ≤ 144 ∑_{i,j} ‖D_j^+ D_i^+ w‖_h²`. -/
theorem biharmonic_bound_one (h : ℝ) (hh : 0 < h) (e : Fin 3 → G) (w : G → F) :
    h ^ 4 * gridNormSq h (biharmonic h e w)
      ≤ 144 * ∑ i, ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e i) w)) := by
  have h1 := grid_laplacian_domination h hh e (gridLaplacian h e w)
  have h2 : ∀ i, h ^ 2 * gridNormSq h (forwardDiff h (e i) (gridLaplacian h e w))
      ≤ 12 * ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e i) w)) := by
    intro i
    rw [forwardDiff_gridLaplacian]
    exact grid_laplacian_domination h hh e _
  calc h ^ 4 * gridNormSq h (biharmonic h e w)
      = h ^ 2 * (h ^ 2 * gridNormSq h (gridLaplacian h e (gridLaplacian h e w))) := by
        unfold biharmonic; ring
    _ ≤ h ^ 2 * (12 * ∑ i, gridNormSq h (forwardDiff h (e i) (gridLaplacian h e w))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 12 * ∑ i, h ^ 2 * gridNormSq h (forwardDiff h (e i) (gridLaplacian h e w)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 12 * ∑ i, 12 * ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e i) w)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h2 i) (by norm_num)
    _ = 144 * ∑ i, ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e i) w)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `h⁴ ‖Λ_h² w‖_h² ≤ 36 h² ∑_{i,j} ‖D_j^+ D_j^+ D_i^+ w‖_h²`. -/
theorem biharmonic_bound_two (h : ℝ) (hh : 0 < h) (e : Fin 3 → G) (w : G → F) :
    h ^ 4 * gridNormSq h (biharmonic h e w)
      ≤ 36 * h ^ 2 * ∑ i, ∑ j,
          gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j) (forwardDiff h (e i) w))) := by
  have h1 := grid_laplacian_domination h hh e (gridLaplacian h e w)
  have h2 : ∀ i, gridNormSq h (forwardDiff h (e i) (gridLaplacian h e w))
      ≤ 3 * ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
          (forwardDiff h (e i) w))) := by
    intro i
    rw [forwardDiff_gridLaplacian]
    exact gridNormSq_gridLaplacian_le h hh.le e _
  calc h ^ 4 * gridNormSq h (biharmonic h e w)
      = h ^ 2 * (h ^ 2 * gridNormSq h (gridLaplacian h e (gridLaplacian h e w))) := by
        unfold biharmonic; ring
    _ ≤ h ^ 2 * (12 * ∑ i, gridNormSq h (forwardDiff h (e i) (gridLaplacian h e w))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ h ^ 2 * (12 * ∑ i, 3 * ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
          (forwardDiff h (e i) w)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => h2 i) (by norm_num)) (by positivity)
    _ = 36 * h ^ 2 * ∑ i, ∑ j,
          gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j) (forwardDiff h (e i) w))) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `h⁴ ‖Λ_h² w‖_h² ≤ 9 h⁴ ∑_{i,j} ‖D_j^+ D_j^+ D_i^+ D_i^+ w‖_h²`. -/
theorem biharmonic_bound_three (h : ℝ) (hh : 0 < h) (e : Fin 3 → G) (w : G → F) :
    h ^ 4 * gridNormSq h (biharmonic h e w)
      ≤ 9 * h ^ 4 * ∑ i, ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
          (forwardDiff h (e i) (forwardDiff h (e i) w)))) := by
  have h1 := gridNormSq_gridLaplacian_le h hh.le e (gridLaplacian h e w)
  have h2 : ∀ i, gridNormSq h (forwardDiff h (e i) (forwardDiff h (e i) (gridLaplacian h e w)))
      ≤ 3 * ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
          (forwardDiff h (e i) (forwardDiff h (e i) w)))) := by
    intro i
    rw [forwardDiff_gridLaplacian, forwardDiff_gridLaplacian]
    exact gridNormSq_gridLaplacian_le h hh.le e _
  calc h ^ 4 * gridNormSq h (biharmonic h e w)
      ≤ h ^ 4 * (3 * ∑ i, gridNormSq h (forwardDiff h (e i) (forwardDiff h (e i)
          (gridLaplacian h e w)))) := by
        unfold biharmonic
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ h ^ 4 * (3 * ∑ i, 3 * ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
          (forwardDiff h (e i) (forwardDiff h (e i) w))))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => h2 i) (by norm_num)) (by positivity)
    _ = 9 * h ^ 4 * ∑ i, ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
          (forwardDiff h (e i) (forwardDiff h (e i) w)))) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `∑_{i,j} a_{ij} ≤ 9 M` when every `a_{ij} ≤ M`. -/
theorem sum_sum_le_nine (a : Fin 3 → Fin 3 → ℝ) (M : ℝ) (ha : ∀ i j, a i j ≤ M) :
    ∑ i, ∑ j, a i j ≤ 9 * M := by
  calc ∑ i, ∑ j, a i j ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, M :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ha i j
    _ = 9 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-! ### Assembly -/

/-- Generic reduction: termwise bounds `h⁴ ‖D^α u‖² ≤ c² ‖q‖²_{r'}` for `|α| ≤ r` give
`h² ‖u‖_{r,h} ≤ c √N_r ‖q‖_{r',h}` with `N_r = #multiIndices r`. -/
theorem sobolev_reduction (h : ℝ) (hh : 0 < h) (e : Fin 3 → G) (r r' : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (u q : G → F)
    (hterm : ∀ α ∈ multiIndices r,
      h ^ 4 * gridNormSq h (multiDiff h e α u) ≤ c ^ 2 * diffSobolevNormSq h e r' q) :
    h ^ 2 * diffSobolevNorm h e r u
      ≤ c * Real.sqrt ((multiIndices r).card : ℝ) * diffSobolevNorm h e r' q := by
  have hN : (0 : ℝ) ≤ ((multiIndices r).card : ℝ) := Nat.cast_nonneg _
  have hS' := diffSobolevNormSq_nonneg h hh.le e r' q
  have hsum : (h ^ 2) ^ 2 * diffSobolevNormSq h e r u
      ≤ (c * Real.sqrt ((multiIndices r).card : ℝ)) ^ 2 * diffSobolevNormSq h e r' q := by
    unfold diffSobolevNormSq
    rw [Finset.mul_sum]
    calc ∑ α ∈ multiIndices r, (h ^ 2) ^ 2 * gridNormSq h (multiDiff h e α u)
        ≤ ∑ _α ∈ multiIndices r, c ^ 2 * ∑ β ∈ multiIndices r', gridNormSq h (multiDiff h e β q) :=
          Finset.sum_le_sum fun α hα => by
            have := hterm α hα
            unfold diffSobolevNormSq at this
            calc (h ^ 2) ^ 2 * gridNormSq h (multiDiff h e α u)
                = h ^ 4 * gridNormSq h (multiDiff h e α u) := by ring
              _ ≤ _ := this
      _ = ((multiIndices r).card : ℝ) * (c ^ 2 * ∑ β ∈ multiIndices r',
            gridNormSq h (multiDiff h e β q)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (c * Real.sqrt ((multiIndices r).card : ℝ)) ^ 2 * ∑ β ∈ multiIndices r',
            gridNormSq h (multiDiff h e β q) := by
          rw [mul_pow, Real.sq_sqrt hN]; ring
  unfold diffSobolevNorm
  have hh2 : h ^ 2 = Real.sqrt ((h ^ 2) ^ 2) := (Real.sqrt_sq (sq_nonneg h)).symm
  have hcN : 0 ≤ c * Real.sqrt ((multiIndices r).card : ℝ) := mul_nonneg hc (Real.sqrt_nonneg _)
  calc h ^ 2 * Real.sqrt (diffSobolevNormSq h e r u)
      = Real.sqrt ((h ^ 2) ^ 2 * diffSobolevNormSq h e r u) := by
        rw [Real.sqrt_mul (sq_nonneg _), ← hh2]
    _ ≤ Real.sqrt ((c * Real.sqrt ((multiIndices r).card : ℝ)) ^ 2 * diffSobolevNormSq h e r' q) :=
        Real.sqrt_le_sqrt hsum
    _ = c * Real.sqrt ((multiIndices r).card : ℝ) * Real.sqrt (diffSobolevNormSq h e r' q) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hcN]

/-- **`eq:supp-law-orders` in physical space**, for the forward-difference Sobolev norms
`eq:supp-open-norms` on any finite abelian grid with steps `e`, `s ≥ 3`:
`h² ‖Λ_h² q‖_{s-1,h} ≤ 36 √N_{s-1} ‖q‖_{s+1,h}`,
`h² ‖Λ_h² q‖_{s-2,h} ≤ 18 √N_{s-2} h ‖q‖_{s+1,h}`,
`h² ‖Λ_h² q‖_{s-3,h} ≤ 9 √N_{s-3} h² ‖q‖_{s+1,h}`,
`h² ‖Λ_h² v‖_{s-3,h} ≤ 18 √N_{s-3} h ‖v‖_{s,h}`, with `N_r = #{α : |α| ≤ r}`. -/
theorem fourth_order_bounds_physical (h : ℝ) (hh : 0 < h) (e : Fin 3 → G) (s : ℕ) (hs : 3 ≤ s)
    (q v : G → F) :
    h ^ 2 * diffSobolevNorm h e (s - 1) (biharmonic h e q)
        ≤ 36 * Real.sqrt ((multiIndices (s - 1)).card : ℝ) * diffSobolevNorm h e (s + 1) q ∧
    h ^ 2 * diffSobolevNorm h e (s - 2) (biharmonic h e q)
        ≤ 18 * Real.sqrt ((multiIndices (s - 2)).card : ℝ) * h * diffSobolevNorm h e (s + 1) q ∧
    h ^ 2 * diffSobolevNorm h e (s - 3) (biharmonic h e q)
        ≤ 9 * Real.sqrt ((multiIndices (s - 3)).card : ℝ) * h ^ 2
            * diffSobolevNorm h e (s + 1) q ∧
    h ^ 2 * diffSobolevNorm h e (s - 3) (biharmonic h e v)
        ≤ 18 * Real.sqrt ((multiIndices (s - 3)).card : ℝ) * h * diffSobolevNorm h e s v := by
  have hcomm : ∀ (α : Fin 3 → ℕ) (u : G → F),
      multiDiff h e α (biharmonic h e u) = biharmonic h e (multiDiff h e α u) := by
    intro α u
    unfold biharmonic
    rw [gridLaplacian_multiDiff, gridLaplacian_multiDiff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine sobolev_reduction h hh e (s - 1) (s + 1) 36 (by norm_num) _ q fun α hα => ?_
    rw [mem_multiIndices] at hα
    rw [hcomm]
    refine (biharmonic_bound_one h hh e _).trans ?_
    have := sum_sum_le_nine
      (fun i j => gridNormSq h (forwardDiff h (e j) (forwardDiff h (e i) (multiDiff h e α q))))
      (diffSobolevNormSq h e (s + 1) q)
      (fun i j => gridNormSq_two_step_le h hh.le e (by omega) q i j)
    linarith
  · refine le_of_le_of_eq (sobolev_reduction h hh e (s - 2) (s + 1) (18 * h) (by positivity) _ q
      fun α hα => ?_) (by rw [mul_right_comm 18 h])
    rw [mem_multiIndices] at hα
    rw [hcomm]
    refine (biharmonic_bound_two h hh e _).trans ?_
    have := sum_sum_le_nine
      (fun i j => gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
        (forwardDiff h (e i) (multiDiff h e α q)))))
      (diffSobolevNormSq h e (s + 1) q)
      (fun i j => gridNormSq_three_step_le h hh.le e (by omega) q i j)
    have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
    calc 36 * h ^ 2 * ∑ i, ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
          (forwardDiff h (e i) (multiDiff h e α q))))
        ≤ 36 * h ^ 2 * (9 * diffSobolevNormSq h e (s + 1) q) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (18 * h) ^ 2 * diffSobolevNormSq h e (s + 1) q := by ring
  · refine le_of_le_of_eq (sobolev_reduction h hh e (s - 3) (s + 1) (9 * h ^ 2) (by positivity)
      _ q fun α hα => ?_) (by rw [mul_right_comm 9 (h ^ 2)])
    rw [mem_multiIndices] at hα
    rw [hcomm]
    refine (biharmonic_bound_three h hh e _).trans ?_
    have := sum_sum_le_nine
      (fun i j => gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
        (forwardDiff h (e i) (forwardDiff h (e i) (multiDiff h e α q))))))
      (diffSobolevNormSq h e (s + 1) q)
      (fun i j => gridNormSq_four_step_le h hh.le e (by omega) q i j)
    calc 9 * h ^ 4 * ∑ i, ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
          (forwardDiff h (e i) (forwardDiff h (e i) (multiDiff h e α q)))))
        ≤ 9 * h ^ 4 * (9 * diffSobolevNormSq h e (s + 1) q) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (9 * h ^ 2) ^ 2 * diffSobolevNormSq h e (s + 1) q := by ring
  · refine le_of_le_of_eq (sobolev_reduction h hh e (s - 3) s (18 * h) (by positivity) _ v
      fun α hα => ?_) (by rw [mul_right_comm 18 h])
    rw [mem_multiIndices] at hα
    rw [hcomm]
    refine (biharmonic_bound_two h hh e _).trans ?_
    have := sum_sum_le_nine
      (fun i j => gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
        (forwardDiff h (e i) (multiDiff h e α v)))))
      (diffSobolevNormSq h e s v)
      (fun i j => gridNormSq_three_step_le h hh.le e (by omega) v i j)
    calc 36 * h ^ 2 * ∑ i, ∑ j, gridNormSq h (forwardDiff h (e j) (forwardDiff h (e j)
          (forwardDiff h (e i) (multiDiff h e α v))))
        ≤ 36 * h ^ 2 * (9 * diffSobolevNormSq h e s v) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (18 * h) ^ 2 * diffSobolevNormSq h e s v := by ring

end Orders

/-! ### The lemma on the periodic grid -/

section Periodic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`lem:supp-law-multiplier`** on the periodic grid `(hℤ/ℤ)³` (`Fin 3 → ZMod N`), for
arrays with values in any normed space, `s ≥ 3`:
`eq:supp-law-domination` `h² ‖Λ_h w‖_h² ≤ 12 ∑_i ‖D_i^+ w‖_h²` for every array `w`, and the
four order bounds `eq:supp-law-orders` for the forward-difference Sobolev norms
`eq:supp-open-norms`, with the explicit `h`-independent constants
`C_s = 36 √N_{s-1}, 18 √N_{s-2}, 9 √N_{s-3}, 18 √N_{s-3}` (`N_r = #{α ∈ ℕ³ : |α| ≤ r}`). -/
theorem law_multiplier_bounds (N : ℕ) [NeZero N] (h : ℝ) (hh : 0 < h) (s : ℕ) (hs : 3 ≤ s)
    (q v : PeriodicGrid N → F) :
    (∀ w : PeriodicGrid N → F, h ^ 2 * gridNormSq h (gridLaplacian h (unitStep N) w)
        ≤ 12 * ∑ i, gridNormSq h (forwardDiff h (unitStep N i) w)) ∧
    h ^ 2 * diffSobolevNorm h (unitStep N) (s - 1) (biharmonic h (unitStep N) q)
        ≤ 36 * Real.sqrt ((multiIndices (s - 1)).card : ℝ)
            * diffSobolevNorm h (unitStep N) (s + 1) q ∧
    h ^ 2 * diffSobolevNorm h (unitStep N) (s - 2) (biharmonic h (unitStep N) q)
        ≤ 18 * Real.sqrt ((multiIndices (s - 2)).card : ℝ) * h
            * diffSobolevNorm h (unitStep N) (s + 1) q ∧
    h ^ 2 * diffSobolevNorm h (unitStep N) (s - 3) (biharmonic h (unitStep N) q)
        ≤ 9 * Real.sqrt ((multiIndices (s - 3)).card : ℝ) * h ^ 2
            * diffSobolevNorm h (unitStep N) (s + 1) q ∧
    h ^ 2 * diffSobolevNorm h (unitStep N) (s - 3) (biharmonic h (unitStep N) v)
        ≤ 18 * Real.sqrt ((multiIndices (s - 3)).card : ℝ) * h
            * diffSobolevNorm h (unitStep N) s v :=
  ⟨fun w => periodic_laplacian_domination N h hh w,
    fourth_order_bounds_physical h hh (unitStep N) s hs q v⟩

/-- The constants of `eq:supp-law-orders` are independent of the cutoff `h` (and of `N`):
existential form. -/
theorem exists_uniform_order_constants (s : ℕ) (hs : 3 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (h : ℝ), 0 < h → ∀ q v : PeriodicGrid N → F,
      h ^ 2 * diffSobolevNorm h (unitStep N) (s - 1) (biharmonic h (unitStep N) q)
          ≤ C * diffSobolevNorm h (unitStep N) (s + 1) q ∧
      h ^ 2 * diffSobolevNorm h (unitStep N) (s - 2) (biharmonic h (unitStep N) q)
          ≤ C * h * diffSobolevNorm h (unitStep N) (s + 1) q ∧
      h ^ 2 * diffSobolevNorm h (unitStep N) (s - 3) (biharmonic h (unitStep N) q)
          ≤ C * h ^ 2 * diffSobolevNorm h (unitStep N) (s + 1) q ∧
      h ^ 2 * diffSobolevNorm h (unitStep N) (s - 3) (biharmonic h (unitStep N) v)
          ≤ C * h * diffSobolevNorm h (unitStep N) s v := by
  refine ⟨36 * Real.sqrt ((multiIndices (s - 1)).card : ℝ)
    + 18 * Real.sqrt ((multiIndices (s - 2)).card : ℝ)
    + 9 * Real.sqrt ((multiIndices (s - 3)).card : ℝ)
    + 18 * Real.sqrt ((multiIndices (s - 3)).card : ℝ), by positivity, ?_⟩
  intro N _ h hh q v
  obtain ⟨-, h1, h2, h3, h4⟩ := law_multiplier_bounds N h hh s hs q v
  have n1 := Real.sqrt_nonneg ((multiIndices (s - 1)).card : ℝ)
  have n2 := Real.sqrt_nonneg ((multiIndices (s - 2)).card : ℝ)
  have n3 := Real.sqrt_nonneg ((multiIndices (s - 3)).card : ℝ)
  have hq := Real.sqrt_nonneg (diffSobolevNormSq h (unitStep N) (s + 1) q)
  have hv := Real.sqrt_nonneg (diffSobolevNormSq h (unitStep N) s v)
  unfold diffSobolevNorm at h1 h2 h3 h4 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith [mul_nonneg hh.le hq]
  · nlinarith [mul_nonneg (sq_nonneg h) hq]
  · nlinarith [mul_nonneg hh.le hv]

end Periodic

end

end LawMultiplier
end RenewalGeometry
