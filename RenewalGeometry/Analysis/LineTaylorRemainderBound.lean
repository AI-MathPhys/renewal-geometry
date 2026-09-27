/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Taylor remainder bounds along lines

Reusable one-dimensional Taylor estimates with global iterated-derivative
bounds, and their transport to restrictions of `C^n` maps on a normed space to
affine lines `t ↦ x + t • r`.

* `abs_sub_taylorSum_le`: for `φ : ℝ → ℝ` of class `C^{n+1}` with
  `|φ^{(n+1)}| ≤ M`, `|φ x - Σ_{k ≤ n} φ^{(k)}(x₀) (x - x₀)^k / k!| ≤ M |x - x₀|^{n+1} / (n+1)!`.
* `iteratedDeriv_lineMap`, `abs_iteratedDeriv_lineMap_le`: the `k`-th derivative of
  `t ↦ f (x + t • r)` is `D^k f (x + t r)[r, …, r]`, bounded by `‖D^k f‖ ‖r‖^k`.
* `symmetric_product_expansion_bound`: the fourth-order estimate
  `(α(0)+α(h))(φ(h)-φ(0)) + (α(-h)+α(0))(φ(-h)-φ(0)) = 2h²(α φ'' + α' φ')(0) + O(h⁴)`
  used for variable-coefficient second-difference operators
  (paper `predictive_spectral_geometry`, `thm:supp-general-renewal-process`).
-/

open Set Finset

namespace RenewalGeometry.LineTaylorRemainderBound

/-! ### Global Taylor bound in one variable -/

/-- The Taylor polynomial of `φ` at `x₀` of degree `n`, with global iterated derivatives. -/
noncomputable def taylorSum (φ : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * (x - x₀) ^ k) * iteratedDeriv k φ x₀

theorem taylorSum_eq_taylorWithinEval (φ : ℝ → ℝ) (n : ℕ) {x₀ x : ℝ} (hx : x₀ ≠ x)
    (hφ : ContDiff ℝ (n + 1) φ) :
    taylorSum φ n x₀ x = taylorWithinEval φ n (uIcc x₀ x) x₀ x := by
  rw [taylor_within_apply, taylorSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [smul_eq_mul, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx) _ left_mem_uIcc]
  apply ContDiff.contDiffAt
  apply hφ.of_le
  have := Finset.mem_range.mp hk
  exact_mod_cast this.le

/-- **Global Taylor bound.** -/
theorem abs_sub_taylorSum_le (φ : ℝ → ℝ) (n : ℕ) (M : ℝ) (hφ : ContDiff ℝ (n + 1) φ)
    (hM : ∀ t, |iteratedDeriv (n + 1) φ t| ≤ M) (x₀ x : ℝ) :
    |φ x - taylorSum φ n x₀ x| ≤ M * |x - x₀| ^ (n + 1) / (n + 1).factorial := by
  rcases eq_or_ne x₀ x with rfl | hx
  · have : taylorSum φ n x₀ x₀ = φ x₀ := by
      unfold taylorSum
      rw [Finset.sum_range_succ']
      simp
    rw [this, sub_self, abs_zero, sub_self, abs_zero, zero_pow (Nat.succ_ne_zero n), mul_zero,
      zero_div]
  · obtain ⟨x', -, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx hφ.contDiffOn
    rw [taylorSum_eq_taylorWithinEval φ n hx hφ, heq, abs_div, abs_mul, abs_pow,
      Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (hM x') (pow_nonneg (abs_nonneg _) _)

/-- First-order form: `|φ x - φ x₀| ≤ M |x - x₀|` for `|φ'| ≤ M`. -/
theorem abs_sub_le_of_deriv_bound (φ : ℝ → ℝ) (M : ℝ) (hφ : ContDiff ℝ 1 φ)
    (hM : ∀ t, |iteratedDeriv 1 φ t| ≤ M) (x₀ x : ℝ) :
    |φ x - φ x₀| ≤ M * |x - x₀| := by
  have := abs_sub_taylorSum_le φ 0 M hφ hM x₀ x
  simpa [taylorSum] using this

/-- Second-order form. -/
theorem abs_sub_taylor_one_le (φ : ℝ → ℝ) (M : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hM : ∀ t, |iteratedDeriv 2 φ t| ≤ M) (x₀ x : ℝ) :
    |φ x - (φ x₀ + (x - x₀) * iteratedDeriv 1 φ x₀)| ≤ M * |x - x₀| ^ 2 / 2 := by
  have := abs_sub_taylorSum_le φ 1 M hφ hM x₀ x
  simpa [taylorSum, Finset.sum_range_succ, Nat.factorial] using this

/-- Third-order form. -/
theorem abs_sub_taylor_two_le (φ : ℝ → ℝ) (M : ℝ) (hφ : ContDiff ℝ 3 φ)
    (hM : ∀ t, |iteratedDeriv 3 φ t| ≤ M) (x₀ x : ℝ) :
    |φ x - (φ x₀ + (x - x₀) * iteratedDeriv 1 φ x₀ +
      (x - x₀) ^ 2 / 2 * iteratedDeriv 2 φ x₀)| ≤ M * |x - x₀| ^ 3 / 6 := by
  have := abs_sub_taylorSum_le φ 2 M hφ hM x₀ x
  have h6 : ((2 + 1).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  have hsum : taylorSum φ 2 x₀ x = φ x₀ + (x - x₀) * iteratedDeriv 1 φ x₀ +
      (x - x₀) ^ 2 / 2 * iteratedDeriv 2 φ x₀ := by
    have h0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
    have h1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
    have h2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    simp only [taylorSum, Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero,
      h0, h1, h2]
    ring
  rw [hsum, h6] at this
  simpa using this

/-- Fourth-order form. -/
theorem abs_sub_taylor_three_le (φ : ℝ → ℝ) (M : ℝ) (hφ : ContDiff ℝ 4 φ)
    (hM : ∀ t, |iteratedDeriv 4 φ t| ≤ M) (x₀ x : ℝ) :
    |φ x - (φ x₀ + (x - x₀) * iteratedDeriv 1 φ x₀ +
      (x - x₀) ^ 2 / 2 * iteratedDeriv 2 φ x₀ + (x - x₀) ^ 3 / 6 * iteratedDeriv 3 φ x₀)| ≤
      M * |x - x₀| ^ 4 / 24 := by
  have := abs_sub_taylorSum_le φ 3 M hφ hM x₀ x
  have h24 : ((3 + 1).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  have hsum : taylorSum φ 3 x₀ x = φ x₀ + (x - x₀) * iteratedDeriv 1 φ x₀ +
      (x - x₀) ^ 2 / 2 * iteratedDeriv 2 φ x₀ + (x - x₀) ^ 3 / 6 * iteratedDeriv 3 φ x₀ := by
    have h0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
    have h1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
    have h2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    simp only [taylorSum, Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero,
      h0, h1, h2, h3]
    ring
  rw [hsum, h24] at this
  simpa using this

/-! ### Restrictions to lines -/

section lines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The restriction of `f` to the line `t ↦ x + t • r`. -/
def lineMap (f : E → ℝ) (x r : E) : ℝ → ℝ := fun t => f (x + t • r)

theorem lineMap_apply (f : E → ℝ) (x r : E) (t : ℝ) : lineMap f x r t = f (x + t • r) := rfl

theorem lineMap_zero (f : E → ℝ) (x r : E) : lineMap f x r 0 = f x := by
  simp [lineMap]

/-- The continuous linear map `t ↦ t • r`. -/
noncomputable def smulLine (r : E) : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight r

theorem smulLine_apply (r : E) (t : ℝ) : smulLine r t = t • r := rfl

theorem contDiff_lineMap {n : WithTop ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) (x r : E) :
    ContDiff ℝ n (lineMap f x r) :=
  hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- The `k`-th derivative of the line restriction is the `k`-th differential
applied to `(r, …, r)`. -/
theorem iteratedDeriv_lineMap {n : ℕ} {f : E → ℝ} (hf : ContDiff ℝ n f) (x r : E)
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

theorem abs_iteratedDeriv_lineMap_le {n : ℕ} {f : E → ℝ} (hf : ContDiff ℝ n f) (x r : E)
    {k : ℕ} (hk : k ≤ n) (t : ℝ) :
    |iteratedDeriv k (lineMap f x r) t| ≤ ‖iteratedFDeriv ℝ k f (x + t • r)‖ * ‖r‖ ^ k := by
  rw [iteratedDeriv_lineMap hf x r hk t, ← Real.norm_eq_abs]
  have := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ k f (x + t • r)) (fun _ => r)
  simpa using this

/-- Uniform derivative bound along every line from a global differential bound. -/
theorem abs_iteratedDeriv_lineMap_le_of_bound {n : ℕ} {f : E → ℝ} (hf : ContDiff ℝ n f)
    {k : ℕ} (hk : k ≤ n) {M : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M) (x r : E) (t : ℝ) :
    |iteratedDeriv k (lineMap f x r) t| ≤ M * ‖r‖ ^ k :=
  (abs_iteratedDeriv_lineMap_le hf x r hk t).trans
    (mul_le_mul_of_nonneg_right (hM _) (pow_nonneg (norm_nonneg _) _))

theorem iteratedDeriv_one_lineMap_zero {n : ℕ} {f : E → ℝ} (hf : ContDiff ℝ n f) (hn : 1 ≤ n)
    (x r : E) : iteratedDeriv 1 (lineMap f x r) 0 = fderiv ℝ f x r := by
  rw [iteratedDeriv_lineMap hf x r hn 0]
  simp [iteratedFDeriv_one_apply]

theorem iteratedDeriv_two_lineMap_zero {n : ℕ} {f : E → ℝ} (hf : ContDiff ℝ n f) (hn : 2 ≤ n)
    (x r : E) : iteratedDeriv 2 (lineMap f x r) 0 = fderiv ℝ (fderiv ℝ f) x r r := by
  rw [iteratedDeriv_lineMap hf x r hn 0]
  simp [iteratedFDeriv_two_apply]

end lines

/-! ### The symmetric product expansion -/

theorem abs_mul_le_of_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- The constant in `symmetric_product_expansion_bound`. -/
noncomputable def productExpansionConstant (F1 F2 F3 F4 A0 A1 A2 A3 : ℝ) : ℝ :=
  A2 * F2 / 2 + A1 * F3 / 3 + (2 * A0 + A3 / 6) * F4 / 12 + A3 * F1 / 3

/-- **Symmetric product expansion.** For `φ ∈ C⁴`, `α ∈ C³` with global derivative
bounds and `0 < h ≤ 1`,
`(α(0)+α(h))(φ(h)-φ(0)) + (α(-h)+α(0))(φ(-h)-φ(0)) - 2h²(α(0)φ''(0) + α'(0)φ'(0))`
is bounded by `productExpansionConstant * h⁴`. -/
theorem symmetric_product_expansion_bound (φ α : ℝ → ℝ) (hφ : ContDiff ℝ 4 φ)
    (hα : ContDiff ℝ 3 α) (F1 F2 F3 F4 A0 A1 A2 A3 : ℝ)
    (hF1 : ∀ t, |iteratedDeriv 1 φ t| ≤ F1) (hF2 : ∀ t, |iteratedDeriv 2 φ t| ≤ F2)
    (hF3 : ∀ t, |iteratedDeriv 3 φ t| ≤ F3) (hF4 : ∀ t, |iteratedDeriv 4 φ t| ≤ F4)
    (hA0 : ∀ t, |α t| ≤ A0) (hA1 : ∀ t, |iteratedDeriv 1 α t| ≤ A1)
    (hA2 : ∀ t, |iteratedDeriv 2 α t| ≤ A2) (hA3 : ∀ t, |iteratedDeriv 3 α t| ≤ A3)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    |(α 0 + α h) * (φ h - φ 0) + (α (-h) + α 0) * (φ (-h) - φ 0) -
        2 * h ^ 2 * (α 0 * iteratedDeriv 2 φ 0 + iteratedDeriv 1 α 0 * iteratedDeriv 1 φ 0)| ≤
      productExpansionConstant F1 F2 F3 F4 A0 A1 A2 A3 * h ^ 4 := by
  -- nonnegativity of the bounds
  have hF1n : 0 ≤ F1 := (abs_nonneg _).trans (hF1 0)
  have hF4n : 0 ≤ F4 := (abs_nonneg _).trans (hF4 0)
  have hA0n : 0 ≤ A0 := (abs_nonneg _).trans (hA0 0)
  have hA3n : 0 ≤ A3 := (abs_nonneg _).trans (hA3 0)
  -- Taylor remainders
  set φ1 := iteratedDeriv 1 φ 0
  set φ2 := iteratedDeriv 2 φ 0
  set φ3 := iteratedDeriv 3 φ 0
  set α1 := iteratedDeriv 1 α 0
  set α2 := iteratedDeriv 2 α 0
  have hRp := abs_sub_taylor_three_le φ F4 hφ hF4 0 h
  have hRm := abs_sub_taylor_three_le φ F4 hφ hF4 0 (-h)
  have hSp := abs_sub_taylor_two_le α A3 hα hA3 0 h
  have hSm := abs_sub_taylor_two_le α A3 hα hA3 0 (-h)
  have hDp := abs_sub_le_of_deriv_bound φ F1 (hφ.of_le (by norm_num)) hF1 0 h
  have hDm := abs_sub_le_of_deriv_bound φ F1 (hφ.of_le (by norm_num)) hF1 0 (-h)
  simp only [sub_zero, abs_of_pos hh, abs_neg] at hRp hRm hSp hSm hDp hDm
  set Rp := φ h - (φ 0 + h * φ1 + h ^ 2 / 2 * φ2 + h ^ 3 / 6 * φ3) with hRp_def
  set Rm := φ (-h) - (φ 0 + -h * φ1 + (-h) ^ 2 / 2 * φ2 + (-h) ^ 3 / 6 * φ3) with hRm_def
  set Sp := α h - (α 0 + h * α1 + h ^ 2 / 2 * α2) with hSp_def
  set Sm := α (-h) - (α 0 + -h * α1 + (-h) ^ 2 / 2 * α2) with hSm_def
  have hkey : (α 0 + α h) * (φ h - φ 0) + (α (-h) + α 0) * (φ (-h) - φ 0) -
      2 * h ^ 2 * (α 0 * φ2 + α1 * φ1) =
      h ^ 4 * (α2 * φ2 / 2 + α1 * φ3 / 3) + (α 0 + α h - Sp) * Rp + (α 0 + α (-h) - Sm) * Rm +
        Sp * (φ h - φ 0) + Sm * (φ (-h) - φ 0) := by
    simp only [hRp_def, hRm_def, hSp_def, hSm_def]
    ring
  rw [hkey]
  -- bounds on the pieces
  have hh4 : 0 < h ^ 4 := by positivity
  have hh3 : h ^ 3 ≤ 1 := pow_le_one₀ hh.le hh1
  have hSp' : |Sp| ≤ A3 / 6 := by
    calc |Sp| ≤ A3 * h ^ 3 / 6 := hSp
      _ ≤ A3 / 6 := by
        rw [div_le_div_iff_of_pos_right (by norm_num)]
        exact mul_le_of_le_one_right hA3n hh3
  have hSm' : |Sm| ≤ A3 / 6 := by
    calc |Sm| ≤ A3 * h ^ 3 / 6 := hSm
      _ ≤ A3 / 6 := by
        rw [div_le_div_iff_of_pos_right (by norm_num)]
        exact mul_le_of_le_one_right hA3n hh3
  have hcp : |α 0 + α h - Sp| ≤ 2 * A0 + A3 / 6 := by
    calc |α 0 + α h - Sp| ≤ |α 0 + α h| + |Sp| := abs_sub _ _
      _ ≤ (|α 0| + |α h|) + |Sp| := by gcongr; exact abs_add_le _ _
      _ ≤ (A0 + A0) + A3 / 6 := add_le_add (add_le_add (hA0 _) (hA0 _)) hSp'
      _ = 2 * A0 + A3 / 6 := by ring
  have hcm : |α 0 + α (-h) - Sm| ≤ 2 * A0 + A3 / 6 := by
    calc |α 0 + α (-h) - Sm| ≤ |α 0 + α (-h)| + |Sm| := abs_sub _ _
      _ ≤ (|α 0| + |α (-h)|) + |Sm| := by gcongr; exact abs_add_le _ _
      _ ≤ (A0 + A0) + A3 / 6 := add_le_add (add_le_add (hA0 _) (hA0 _)) hSm'
      _ = 2 * A0 + A3 / 6 := by ring
  have h1 : |h ^ 4 * (α2 * φ2 / 2 + α1 * φ3 / 3)| ≤ h ^ 4 * (A2 * F2 / 2 + A1 * F3 / 3) := by
    refine abs_mul_le_of_le (by rw [abs_of_pos hh4]) ?_
    calc |α2 * φ2 / 2 + α1 * φ3 / 3| ≤ |α2 * φ2 / 2| + |α1 * φ3 / 3| := abs_add_le _ _
      _ ≤ A2 * F2 / 2 + A1 * F3 / 3 := by
        rw [abs_div, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2),
          abs_of_pos (by norm_num : (0:ℝ) < 3)]
        gcongr
        · exact abs_mul_le_of_le (hA2 0) (hF2 0)
        · exact abs_mul_le_of_le (hA1 0) (hF3 0)
  have h2 : |(α 0 + α h - Sp) * Rp| ≤ (2 * A0 + A3 / 6) * (F4 * h ^ 4 / 24) :=
    abs_mul_le_of_le hcp hRp
  have h3 : |(α 0 + α (-h) - Sm) * Rm| ≤ (2 * A0 + A3 / 6) * (F4 * h ^ 4 / 24) :=
    abs_mul_le_of_le hcm hRm
  have h4 : |Sp * (φ h - φ 0)| ≤ (A3 * h ^ 3 / 6) * (F1 * h) := abs_mul_le_of_le hSp hDp
  have h5 : |Sm * (φ (-h) - φ 0)| ≤ (A3 * h ^ 3 / 6) * (F1 * h) := abs_mul_le_of_le hSm hDm
  calc |h ^ 4 * (α2 * φ2 / 2 + α1 * φ3 / 3) + (α 0 + α h - Sp) * Rp + (α 0 + α (-h) - Sm) * Rm +
        Sp * (φ h - φ 0) + Sm * (φ (-h) - φ 0)|
      ≤ |h ^ 4 * (α2 * φ2 / 2 + α1 * φ3 / 3)| + |(α 0 + α h - Sp) * Rp| +
          |(α 0 + α (-h) - Sm) * Rm| + |Sp * (φ h - φ 0)| + |Sm * (φ (-h) - φ 0)| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ h ^ 4 * (A2 * F2 / 2 + A1 * F3 / 3) + (2 * A0 + A3 / 6) * (F4 * h ^ 4 / 24) +
          (2 * A0 + A3 / 6) * (F4 * h ^ 4 / 24) + (A3 * h ^ 3 / 6) * (F1 * h) +
          (A3 * h ^ 3 / 6) * (F1 * h) := by gcongr
    _ = productExpansionConstant F1 F2 F3 F4 A0 A1 A2 A3 * h ^ 4 := by
        unfold productExpansionConstant
        ring

end RenewalGeometry.LineTaylorRemainderBound
