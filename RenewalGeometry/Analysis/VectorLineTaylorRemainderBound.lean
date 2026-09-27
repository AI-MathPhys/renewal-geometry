/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Vector-valued Taylor remainder bounds along lines

The normed-space-valued counterpart of `Analysis/LineTaylorRemainderBound.lean`: global Taylor
bounds at `0` for `φ : ℝ → F` (both directions, by reflection), the centered-difference and
second-difference estimates

* `norm_centered_difference_sub_deriv_le`:
  `‖(2h)⁻¹ (φ(h) - φ(-h)) - φ'(0)‖ ≤ M₃ h² / 2` for `‖φ⁽³⁾‖ ≤ M₃`;
* `norm_second_difference_le`:
  `‖2 φ(0) - φ(h) - φ(-h)‖ ≤ 2 M₂ h²` for `‖φ''‖ ≤ M₂`;

and their transport to restrictions `t ↦ f (x + t • r)` of `C^n` maps `f : E → F`
(`iteratedDeriv_lineMap`, `norm_iteratedDeriv_lineMap_le_of_bound`).  These are the Taylor
ingredients of the lattice consistency estimate `lem:supp-general-core` of the paper
`predictive_spectral_geometry`.
-/

open Set Finset

namespace RenewalGeometry.VectorLineTaylor

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Global Taylor bounds at the origin -/

/-- The Taylor polynomial of `φ` at `0` of degree `n`, with global iterated derivatives. -/
noncomputable def taylorSum (φ : ℝ → F) (n : ℕ) (x : ℝ) : F :=
  ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * x ^ k) • iteratedDeriv k φ 0

theorem taylorSum_zero (φ : ℝ → F) (n : ℕ) : taylorSum φ n 0 = φ 0 := by
  unfold taylorSum
  rw [Finset.sum_range_succ']
  simp

/-- **Global Taylor bound at `0`, forward direction.** -/
theorem norm_sub_taylorSum_le (φ : ℝ → F) (n : ℕ) (M : ℝ) (hφ : ContDiff ℝ (n + 1) φ)
    (hM : ∀ t, ‖iteratedDeriv (n + 1) φ t‖ ≤ M) {h : ℝ} (hh : 0 ≤ h) :
    ‖φ h - taylorSum φ n h‖ ≤ M * h ^ (n + 1) / n.factorial := by
  rcases eq_or_lt_of_le hh with rfl | hpos
  · rw [taylorSum_zero, sub_self, norm_zero]
    simp
  · have hunique : UniqueDiffOn ℝ (Icc 0 h) := uniqueDiffOn_Icc hpos
    have heq : taylorSum φ n h = taylorWithinEval φ n (Icc 0 h) 0 h := by
      rw [taylor_within_apply, taylorSum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [sub_zero, iteratedDerivWithin_eq_iteratedDeriv hunique _ (left_mem_Icc.2 hh)]
      apply ContDiff.contDiffAt
      apply hφ.of_le
      have := Finset.mem_range.mp hk
      exact_mod_cast this.le
    rw [heq]
    have := taylor_mean_remainder_bound (f := φ) (n := n) (C := M) hh hφ.contDiffOn
      (right_mem_Icc.2 hh) (fun y hy => by
        rw [iteratedDerivWithin_eq_iteratedDeriv hunique hφ.contDiffAt hy]
        exact hM y)
    simpa using this

/-- **Global Taylor bound at `0`, backward direction**, obtained by reflection. -/
theorem norm_sub_taylorSum_neg_le (φ : ℝ → F) (n : ℕ) (M : ℝ) (hφ : ContDiff ℝ (n + 1) φ)
    (hM : ∀ t, ‖iteratedDeriv (n + 1) φ t‖ ≤ M) {h : ℝ} (hh : 0 ≤ h) :
    ‖φ (-h) - taylorSum φ n (-h)‖ ≤ M * h ^ (n + 1) / n.factorial := by
  set ψ : ℝ → F := fun t => φ (-t)
  have hψ : ContDiff ℝ (n + 1) ψ := hφ.comp contDiff_neg
  have hMψ : ∀ t, ‖iteratedDeriv (n + 1) ψ t‖ ≤ M := by
    intro t
    rw [show ψ = fun t => φ (-t) from rfl, iteratedDeriv_comp_neg, norm_smul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul]
    exact hM _
  have hsum : taylorSum ψ n h = taylorSum φ n (-h) := by
    unfold taylorSum
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ψ = fun t => φ (-t) from rfl, iteratedDeriv_comp_neg, neg_zero, smul_smul]
    congr 1
    rw [neg_pow]
    ring
  have := norm_sub_taylorSum_le ψ n M hψ hMψ hh
  rwa [hsum] at this

/-! ### Centered and second differences -/

theorem taylorSum_one (φ : ℝ → F) (x : ℝ) :
    taylorSum φ 1 x = φ 0 + x • iteratedDeriv 1 φ 0 := by
  simp [taylorSum, Finset.sum_range_succ, Nat.factorial]

theorem taylorSum_two (φ : ℝ → F) (x : ℝ) :
    taylorSum φ 2 x =
      φ 0 + x • iteratedDeriv 1 φ 0 + ((2 : ℝ)⁻¹ * x ^ 2) • iteratedDeriv 2 φ 0 := by
  simp [taylorSum, Finset.sum_range_succ, Nat.factorial]

/-- **Centered-difference estimate.** For `φ ∈ C³` with `‖φ⁽³⁾‖ ≤ M`,
`‖φ(h) - φ(-h) - 2h φ'(0)‖ ≤ M h³`. -/
theorem norm_centered_difference_sub_le (φ : ℝ → F) (M : ℝ) (hφ : ContDiff ℝ 3 φ)
    (hM : ∀ t, ‖iteratedDeriv 3 φ t‖ ≤ M) {h : ℝ} (hh : 0 ≤ h) :
    ‖φ h - φ (-h) - (2 * h) • iteratedDeriv 1 φ 0‖ ≤ M * h ^ 3 := by
  have h1 := norm_sub_taylorSum_le φ 2 M hφ hM hh
  have h2 := norm_sub_taylorSum_neg_le φ 2 M hφ hM hh
  have hdiff : φ h - φ (-h) - (2 * h) • iteratedDeriv 1 φ 0 =
      (φ h - taylorSum φ 2 h) - (φ (-h) - taylorSum φ 2 (-h)) := by
    rw [taylorSum_two, taylorSum_two]
    module
  rw [hdiff]
  calc ‖(φ h - taylorSum φ 2 h) - (φ (-h) - taylorSum φ 2 (-h))‖
      ≤ ‖φ h - taylorSum φ 2 h‖ + ‖φ (-h) - taylorSum φ 2 (-h)‖ := norm_sub_le _ _
    _ ≤ M * h ^ 3 / 2 + M * h ^ 3 / 2 := by
        gcongr
        · simpa [Nat.factorial] using h1
        · simpa [Nat.factorial] using h2
    _ = M * h ^ 3 := by ring

/-- **`(2h)⁻¹ (φ(h) - φ(-h)) - φ'(0)` is `O(h²)`.** -/
theorem norm_centered_difference_sub_deriv_le (φ : ℝ → F) (M : ℝ) (hφ : ContDiff ℝ 3 φ)
    (hM : ∀ t, ‖iteratedDeriv 3 φ t‖ ≤ M) {h : ℝ} (hh : 0 < h) :
    ‖(2 * h)⁻¹ • (φ h - φ (-h)) - iteratedDeriv 1 φ 0‖ ≤ M * h ^ 2 / 2 := by
  have h2h : (2 * h) ≠ 0 := by positivity
  have heq : (2 * h)⁻¹ • (φ h - φ (-h) - (2 * h) • iteratedDeriv 1 φ 0) =
      (2 * h)⁻¹ • (φ h - φ (-h)) - iteratedDeriv 1 φ 0 := by
    rw [smul_sub ((2 * h)⁻¹) (φ h - φ (-h)) ((2 * h) • iteratedDeriv 1 φ 0), smul_smul,
      inv_mul_cancel₀ h2h, one_smul]
  rw [← heq, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hconst : (2 * h)⁻¹ * (M * h ^ 3) = M * h ^ 2 / 2 := by
    rw [inv_mul_eq_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  calc (2 * h)⁻¹ * ‖φ h - φ (-h) - (2 * h) • iteratedDeriv 1 φ 0‖
      ≤ (2 * h)⁻¹ * (M * h ^ 3) := by
        gcongr
        exact norm_centered_difference_sub_le φ M hφ hM hh.le
    _ = M * h ^ 2 / 2 := hconst

/-- **Second-difference estimate.** For `φ ∈ C²` with `‖φ''‖ ≤ M`,
`‖2 φ(0) - φ(h) - φ(-h)‖ ≤ 2 M h²`. -/
theorem norm_second_difference_le (φ : ℝ → F) (M : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hM : ∀ t, ‖iteratedDeriv 2 φ t‖ ≤ M) {h : ℝ} (hh : 0 ≤ h) :
    ‖(2 : ℝ) • φ 0 - φ h - φ (-h)‖ ≤ 2 * M * h ^ 2 := by
  have h1 := norm_sub_taylorSum_le φ 1 M hφ hM hh
  have h2 := norm_sub_taylorSum_neg_le φ 1 M hφ hM hh
  have hdiff : (2 : ℝ) • φ 0 - φ h - φ (-h) =
      -((φ h - taylorSum φ 1 h) + (φ (-h) - taylorSum φ 1 (-h))) := by
    rw [taylorSum_one, taylorSum_one]
    module
  rw [hdiff, norm_neg]
  calc ‖(φ h - taylorSum φ 1 h) + (φ (-h) - taylorSum φ 1 (-h))‖
      ≤ ‖φ h - taylorSum φ 1 h‖ + ‖φ (-h) - taylorSum φ 1 (-h)‖ := norm_add_le _ _
    _ ≤ M * h ^ 2 + M * h ^ 2 := by
        gcongr
        · simpa [Nat.factorial] using h1
        · simpa [Nat.factorial] using h2
    _ = 2 * M * h ^ 2 := by ring

/-! ### Restrictions to lines -/

section lines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The restriction of `f` to the line `t ↦ x + t • r`. -/
def lineMap (f : E → F) (x r : E) : ℝ → F := fun t => f (x + t • r)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem lineMap_apply (f : E → F) (x r : E) (t : ℝ) : lineMap f x r t = f (x + t • r) := rfl

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem lineMap_zero (f : E → F) (x r : E) : lineMap f x r 0 = f x := by
  simp [lineMap]

/-- The continuous linear map `t ↦ t • r`. -/
noncomputable def smulLine (r : E) : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight r

theorem smulLine_apply (r : E) (t : ℝ) : smulLine r t = t • r := rfl

theorem contDiff_lineMap {n : WithTop ℕ∞} {f : E → F} (hf : ContDiff ℝ n f) (x r : E) :
    ContDiff ℝ n (lineMap f x r) :=
  hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- The `k`-th derivative of the line restriction is the `k`-th differential
applied to `(r, …, r)`. -/
theorem iteratedDeriv_lineMap {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f) (x r : E)
    {k : ℕ} (hk : k ≤ n) (t : ℝ) :
    iteratedDeriv k (lineMap f x r) t = iteratedFDeriv ℝ k f (x + t • r) (fun _ => r) := by
  have hcomp : lineMap f x r = (fun y => f (y + x)) ∘ smulLine r := by
    funext t
    simp [lineMap, smulLine_apply, add_comm]
  have hf' : ContDiff ℝ n (fun y => f (y + x)) := hf.comp (contDiff_id.add contDiff_const)
  rw [iteratedDeriv_eq_iteratedFDeriv, hcomp,
    ContinuousLinearMap.iteratedFDeriv_comp_right (smulLine r) hf' t (by exact_mod_cast hk),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right']
  simp [smulLine_apply, add_comm]

theorem norm_iteratedDeriv_lineMap_le {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f) (x r : E)
    {k : ℕ} (hk : k ≤ n) (t : ℝ) :
    ‖iteratedDeriv k (lineMap f x r) t‖ ≤ ‖iteratedFDeriv ℝ k f (x + t • r)‖ * ‖r‖ ^ k := by
  rw [iteratedDeriv_lineMap hf x r hk t]
  have := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ k f (x + t • r)) (fun _ => r)
  simpa using this

/-- Uniform derivative bound along every line from a global differential bound. -/
theorem norm_iteratedDeriv_lineMap_le_of_bound {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f)
    {k : ℕ} (hk : k ≤ n) {M : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M) (x r : E) (t : ℝ) :
    ‖iteratedDeriv k (lineMap f x r) t‖ ≤ M * ‖r‖ ^ k :=
  (norm_iteratedDeriv_lineMap_le hf x r hk t).trans
    (mul_le_mul_of_nonneg_right (hM _) (pow_nonneg (norm_nonneg _) _))

theorem iteratedDeriv_one_lineMap_zero {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f) (hn : 1 ≤ n)
    (x r : E) : iteratedDeriv 1 (lineMap f x r) 0 = fderiv ℝ f x r := by
  rw [iteratedDeriv_lineMap hf x r hn 0]
  simp [iteratedFDeriv_one_apply]

/-- The first derivative of the line restriction at `0` is the directional derivative
`lineDeriv ℝ f x r`. -/
theorem iteratedDeriv_one_lineMap_zero_eq_lineDeriv (f : E → F) (x r : E) :
    iteratedDeriv 1 (lineMap f x r) 0 = lineDeriv ℝ f x r := by
  rw [iteratedDeriv_one]
  rfl

end lines

end RenewalGeometry.VectorLineTaylor
