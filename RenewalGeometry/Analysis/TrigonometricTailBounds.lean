/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TorusSobolevDerivatives
import RenewalGeometry.Analysis.TorusSobolevL4

/-!
# Derivative bounds for trigonometric tails (`lem:native-tail-transfer`, first display)

Generic infrastructure (no renewal notions) for the measured-leakage step of the
Einstein–Standard-Model action-closure manuscript (Appendix `app:native-tails`).

A trigonometric polynomial on `𝕋^d` with finite mode set `S ⊂ ℤ^d` (the manuscript's
`Λ_h = {|ℓ_μ| ≤ (n-1)/2}`) and coefficients `c` is `z = Σ_{n ∈ S} c(n) e_n` (`trigPoly S c`).
For a cut-off `K > 0` it splits as `z = z^lo + (z - z^lo)` with the low part on `|n|_∞ ≤ K` and the
measured tail on `|n|_∞ > K` (`lowPart`, `tailPart`; no coefficient is deleted).  The measured tails
of `eq:native-tail` are
`τ_j(K) = Σ_{n ∈ S, |n|_∞ > K} (1 + |n|₁/K)^j |c(n)|` (`tau`).

* `isLineDeriv_trigPoly`, `isLineDeriv_trigPoly_derivCoeff`: the classical partial derivatives of a
  trigonometric polynomial are the trigonometric polynomials with coefficients `(2πi n)^α c(n)`
  (`D α = trigPoly S (derivCoeff α c)`, `D 0 = z`, `D (α + eᵢ) = ∂ᵢ D α`).
* `norm_symbol_le_tailWeight`: the multiplier bound `|(2πn)^α| ≤ (2πK)^{|α|} (1 + |n|₁/K)^j` for
  `|α| ≤ j` (the manuscript's `|ℓ^α| ≤ K^{|α|}(1 + |ℓ|₁/K)^j`, period-`1` normalisation).
* **`norm_deriv_tail_le`** (`eq:native-tail-derivatives`):
  `K^{-|α|} ‖∂^α (z - z^lo)‖_∞ ≤ (2π)^{|α|} τ_j(K)` for every `|α| ≤ j`.
* `tau_mono`, `norm_tail_le_tau`: `τ_j ≤ τ_m` for `j ≤ m` and `‖z - z^lo‖_∞ ≤ τ_0 ≤ τ_m` (the
  chart statement: full and low fields differ uniformly by at most `τ_m`).
* `norm_deriv_low_le` (Bernstein) and **`growing_derivatives_of_tail`**: the complete
  (unfiltered) field satisfies the growing derivative reserve `eq:growing-derivatives`,
  `‖∂^α z‖_∞ ≤ C_q K^{|α|}` for `|α| ≤ q`, with `C_q = (2πd)^q (Σ_S |c| + τ_q(K))`.

Normalisation: unit torus (period `1`, characters `e^{2πi n·x}`); on the manuscript's box of
period `2π` the factor `(2π)^{|α|}` disappears.  Vector-valued records are treated componentwise
(each component a complex trigonometric polynomial).  `trigPoly` is the existing
`TorusSobolev.trigPoly` of `Analysis/TorusSobolevL4.lean`.
-/

open MeasureTheory Filter Topology Set UnitAddTorus Finset
open scoped Real BigOperators

namespace RenewalGeometry.TrigTail

set_option linter.unusedSectionVars false

noncomputable section

open TorusSobolev

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Lattice norms, tails and tail sums -/

/-- `|n|₁ = Σᵢ |nᵢ|`. -/
def l1Norm (n : d → ℤ) : ℝ := ∑ i, |((n i : ℤ) : ℝ)|

/-- `|n|_∞ = maxᵢ |nᵢ|`. -/
def supAbs (n : d → ℤ) : ℕ := Finset.univ.sup fun i => (n i).natAbs

theorem l1Norm_nonneg (n : d → ℤ) : 0 ≤ l1Norm n := sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_l1Norm (n : d → ℤ) (i : d) : |((n i : ℤ) : ℝ)| ≤ l1Norm n :=
  single_le_sum (f := fun i => |((n i : ℤ) : ℝ)|) (fun _ _ => abs_nonneg _) (mem_univ i)

theorem l1Norm_le_card_mul_supAbs (n : d → ℤ) :
    l1Norm n ≤ Fintype.card d * (supAbs n : ℝ) := by
  have h : ∀ i, |((n i : ℤ) : ℝ)| ≤ supAbs n := by
    intro i
    have h1 : (n i).natAbs ≤ supAbs n :=
      Finset.le_sup (f := fun i => (n i).natAbs) (mem_univ i)
    rw [← Int.cast_abs, ← Nat.cast_natAbs]; exact_mod_cast h1
  calc l1Norm n ≤ ∑ _i : d, (supAbs n : ℝ) := sum_le_sum fun i _ => h i
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- The low-frequency coefficients `c · 1_{|n|_∞ ≤ K}`. -/
def lowPart (K : ℝ) (c : (d → ℤ) → ℂ) : (d → ℤ) → ℂ :=
  fun n => if (supAbs n : ℝ) ≤ K then c n else 0

/-- The measured tail coefficients `c · 1_{|n|_∞ > K}`. -/
def tailPart (K : ℝ) (c : (d → ℤ) → ℂ) : (d → ℤ) → ℂ :=
  fun n => if (supAbs n : ℝ) ≤ K then 0 else c n

theorem lowPart_add_tailPart (K : ℝ) (c : (d → ℤ) → ℂ) (n : d → ℤ) :
    lowPart K c n + tailPart K c n = c n := by
  unfold lowPart tailPart; split_ifs <;> simp

/-- The measured tail `τ_j(K) = Σ_{n ∈ S, |n|_∞ > K} (1 + |n|₁/K)^j |c(n)|` (`eq:native-tail`). -/
def tau (S : Finset (d → ℤ)) (K : ℝ) (j : ℕ) (c : (d → ℤ) → ℂ) : ℝ :=
  ∑ n ∈ S.filter (fun n => K < (supAbs n : ℝ)), (1 + l1Norm n / K) ^ j * ‖c n‖

theorem one_le_tailWeight {K : ℝ} (hK : 0 < K) (n : d → ℤ) : 1 ≤ 1 + l1Norm n / K := by
  have := div_nonneg (l1Norm_nonneg n) hK.le; linarith

theorem tau_nonneg (S : Finset (d → ℤ)) {K : ℝ} (hK : 0 < K) (j : ℕ) (c : (d → ℤ) → ℂ) :
    0 ≤ tau S K j c :=
  sum_nonneg fun n _ => mul_nonneg (pow_nonneg (by linarith [one_le_tailWeight hK n]) _)
    (norm_nonneg _)

/-- `τ_j ≤ τ_m` for `j ≤ m`. -/
theorem tau_mono (S : Finset (d → ℤ)) {K : ℝ} (hK : 0 < K) {j m : ℕ} (hjm : j ≤ m)
    (c : (d → ℤ) → ℂ) : tau S K j c ≤ tau S K m c :=
  sum_le_sum fun n _ => mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (one_le_tailWeight hK n) hjm) (norm_nonneg _)

/-! ### Trigonometric polynomials and their classical derivatives -/

-- `trigPoly S c = Σ_{n ∈ S} c(n) e_n` is `TorusSobolev.trigPoly` (`Analysis/TorusSobolevL4.lean`).

theorem trigPoly_apply (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (x : UnitAddTorus d) :
    trigPoly S c x = ∑ n ∈ S, c n * mFourier n x := by
  simp [trigPoly, ContinuousMap.coe_sum, smul_eq_mul]

theorem trigPoly_add (S : Finset (d → ℤ)) (c c' : (d → ℤ) → ℂ) :
    trigPoly S (fun n => c n + c' n) = trigPoly S c + trigPoly S c' := by
  simp only [trigPoly]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ext x; simp [add_mul]

/-- `z = z^lo + (z - z^lo)`: the complete record splits exactly into the low part and the
measured tail. -/
theorem trigPoly_eq_low_add_tail (S : Finset (d → ℤ)) (K : ℝ) (c : (d → ℤ) → ℂ) :
    trigPoly S c = trigPoly S (lowPart K c) + trigPoly S (tailPart K c) := by
  rw [← trigPoly_add]; congr 1; funext n; rw [lowPart_add_tailPart]

theorem sub_low_eq_tail (S : Finset (d → ℤ)) (K : ℝ) (c : (d → ℤ) → ℂ) :
    trigPoly S c - trigPoly S (lowPart K c) = trigPoly S (tailPart K c) := by
  rw [trigPoly_eq_low_add_tail S K c]; abel

/-- `‖Σ_{n∈S} c(n) e_n‖_∞ ≤ Σ_{n∈S} |c(n)|`. -/
theorem norm_trigPoly_le (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    ‖trigPoly S c‖ ≤ ∑ n ∈ S, ‖c n‖ := by
  unfold trigPoly
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [norm_smul, mFourier_norm, mul_one]

/-- **Classical partial derivative of a trigonometric polynomial**: `∂ᵢ Σ c(n) e_n =
Σ (2πi nᵢ) c(n) e_n`. -/
theorem isLineDeriv_trigPoly (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (i : d) :
    IsLineDeriv i (trigPoly S c) (trigPoly S (dCoeff i c)) := by
  intro x
  have hterm : ∀ n ∈ S, HasDerivAt (fun t : ℝ => c n * mFourier n (x + lineShift i t))
      (dCoeff i c n * mFourier n x) 0 := by
    intro n _
    have h1 : HasDerivAt (fun t : ℝ => (2 * π * Complex.I * n i) * (t : ℂ))
        (2 * π * Complex.I * n i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * π * Complex.I * n i)
    have h2 := (h1.cexp).const_mul (c n * mFourier n x)
    have e : (fun t : ℝ => c n * mFourier n (x + lineShift i t)) =
        fun t : ℝ => c n * mFourier n x * Complex.exp (2 * π * Complex.I * n i * t) := by
      funext t; rw [mFourier_add_apply, mFourier_lineShift]; ring
    rw [e]
    refine h2.congr_deriv ?_
    simp [dCoeff]; ring
  have hsum := HasDerivAt.fun_sum hterm
  have e1 : (fun t : ℝ => trigPoly S c (x + lineShift i t)) =
      fun t => ∑ n ∈ S, c n * mFourier n (x + lineShift i t) := by
    funext t; rw [trigPoly_apply]
  rw [e1, trigPoly_apply]
  exact hsum

/-- The iterated classical derivatives: `D α = trigPoly S (derivCoeff α c)` satisfies
`D (α + eᵢ) = ∂ᵢ D α`, and `D 0 = trigPoly S c`. -/
theorem isLineDeriv_trigPoly_derivCoeff (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (α : d → ℕ)
    (i : d) :
    IsLineDeriv i (trigPoly S (derivCoeff α c)) (trigPoly S (derivCoeff (α + Pi.single i 1) c)) := by
  have := isLineDeriv_trigPoly S (derivCoeff α c) i
  rwa [dCoeff_derivCoeff] at this

theorem trigPoly_derivCoeff_zero (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    trigPoly S (derivCoeff 0 c) = trigPoly S c := by rw [derivCoeff_zero]

/-! ### The multiplier bound and the tail-derivative estimate -/

/-- `|(2πi n)^α| ≤ (2π|n|₁)^{|α|}`. -/
theorem norm_symbol_le_l1 (α : d → ℕ) (n : d → ℤ) :
    ‖symbol α n‖ ≤ (2 * π * l1Norm n) ^ mOrder α := by
  unfold symbol mOrder
  rw [norm_prod, ← prod_pow_eq_pow_sum]
  refine prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
  rw [norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
  have : ‖(2 * π * Complex.I * n j : ℂ)‖ = 2 * π * |((n j : ℤ) : ℝ)| := by
    have e : (2 * π * Complex.I * n j : ℂ) = ((2 * π * n j : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  rw [this]
  exact mul_le_mul_of_nonneg_left (abs_le_l1Norm n j) (by positivity)

/-- **Multiplier bound** (`|ℓ^α| ≤ K^{|α|}(1 + |ℓ|₁/K)^j`): for `K > 0` and `|α| ≤ j`,
`|(2πi n)^α| ≤ (2πK)^{|α|} (1 + |n|₁/K)^j`. -/
theorem norm_symbol_le_tailWeight {K : ℝ} (hK : 0 < K) {α : d → ℕ} {j : ℕ} (hα : mOrder α ≤ j)
    (n : d → ℤ) : ‖symbol α n‖ ≤ (2 * π * K) ^ mOrder α * (1 + l1Norm n / K) ^ j := by
  refine (norm_symbol_le_l1 α n).trans ?_
  have h1 : 2 * π * l1Norm n ≤ 2 * π * K * (1 + l1Norm n / K) := by
    have : K * (1 + l1Norm n / K) = K + l1Norm n := by field_simp
    have hl := l1Norm_nonneg n
    nlinarith [Real.pi_pos]
  calc (2 * π * l1Norm n) ^ mOrder α ≤ (2 * π * K * (1 + l1Norm n / K)) ^ mOrder α :=
        pow_le_pow_left₀ (by have := l1Norm_nonneg n; positivity) h1 _
    _ = (2 * π * K) ^ mOrder α * (1 + l1Norm n / K) ^ mOrder α := mul_pow _ _ _
    _ ≤ (2 * π * K) ^ mOrder α * (1 + l1Norm n / K) ^ j := by
        gcongr
        exact one_le_tailWeight hK n

/-- **`eq:native-tail-derivatives`**: for `K > 0` and every multi-index `|α| ≤ j`,
`‖∂^α (z - z^lo)‖_∞ ≤ (2πK)^{|α|} τ_j(K)`, i.e. `K^{-|α|} ‖∂^α(z - z^lo)‖_∞ ≤ (2π)^{|α|} τ_j(K)`. -/
theorem norm_deriv_tail_le (S : Finset (d → ℤ)) {K : ℝ} (hK : 0 < K) (c : (d → ℤ) → ℂ)
    {α : d → ℕ} {j : ℕ} (hα : mOrder α ≤ j) :
    ‖trigPoly S (derivCoeff α (tailPart K c))‖ ≤ (2 * π * K) ^ mOrder α * tau S K j c := by
  refine (norm_trigPoly_le S _).trans ?_
  unfold tau
  rw [mul_sum, sum_filter]
  refine sum_le_sum fun n _ => ?_
  simp only [derivCoeff, tailPart, norm_mul]
  by_cases h : (supAbs n : ℝ) ≤ K
  · have h' : ¬ K < (supAbs n : ℝ) := not_lt.mpr h
    rw [if_pos h, if_neg h', norm_zero, mul_zero]
  · have h' : K < (supAbs n : ℝ) := not_le.mp h
    rw [if_neg h, if_pos h', ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_symbol_le_tailWeight hK hα n) (norm_nonneg _)

/-- The normalised form `K^{-|α|} ‖∂^α (z - z^lo)‖_∞ ≤ (2π)^j τ_j(K)` uniformly in `|α| ≤ j`
(`C_j = (2π)^j`), for `K ≥ 1`. -/
theorem normalized_deriv_tail_le (S : Finset (d → ℤ)) {K : ℝ} (hK : 1 ≤ K) (c : (d → ℤ) → ℂ)
    {α : d → ℕ} {j : ℕ} (hα : mOrder α ≤ j) :
    (K ^ mOrder α)⁻¹ * ‖trigPoly S (derivCoeff α (tailPart K c))‖ ≤ (2 * π) ^ j * tau S K j c := by
  have hK0 : 0 < K := by linarith
  have h := norm_deriv_tail_le S hK0 c hα
  have hpow : 0 < K ^ mOrder α := pow_pos hK0 _
  rw [inv_mul_le_iff₀ hpow]
  have h2 : (2 * π) ^ mOrder α ≤ (2 * π) ^ j :=
    pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) hα
  have ht := tau_nonneg S hK0 j c
  calc ‖trigPoly S (derivCoeff α (tailPart K c))‖ ≤ (2 * π * K) ^ mOrder α * tau S K j c := h
    _ = K ^ mOrder α * ((2 * π) ^ mOrder α * tau S K j c) := by rw [mul_pow]; ring
    _ ≤ K ^ mOrder α * ((2 * π) ^ j * tau S K j c) := by gcongr

/-- The chart statement: `‖z - z^lo‖_∞ ≤ τ_0(K) ≤ τ_m(K)`. -/
theorem norm_tail_le_tau (S : Finset (d → ℤ)) {K : ℝ} (hK : 0 < K) (c : (d → ℤ) → ℂ) (m : ℕ) :
    ‖trigPoly S c - trigPoly S (lowPart K c)‖ ≤ tau S K m c := by
  rw [sub_low_eq_tail]
  have h := norm_deriv_tail_le S hK c (α := 0) (j := 0) (by simp [mOrder])
  rw [derivCoeff_zero] at h
  simp only [mOrder, Pi.zero_apply, sum_const_zero, pow_zero, one_mul] at h
  exact h.trans (tau_mono S hK (Nat.zero_le m) c)

/-! ### Bernstein bound and the growing derivative reserve of the complete field -/

/-- **Bernstein**: `‖∂^α z^lo‖_∞ ≤ (2π d K)^{|α|} Σ_S |c|` for the low part `|n|_∞ ≤ K`. -/
theorem norm_deriv_low_le (S : Finset (d → ℤ)) {K : ℝ} (hK : 0 ≤ K) (c : (d → ℤ) → ℂ)
    (α : d → ℕ) :
    ‖trigPoly S (derivCoeff α (lowPart K c))‖ ≤
      (2 * π * Fintype.card d * K) ^ mOrder α * ∑ n ∈ S, ‖c n‖ := by
  refine (norm_trigPoly_le S _).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun n _ => ?_
  simp only [derivCoeff, lowPart, norm_mul]
  split_ifs with h
  · refine mul_le_mul_of_nonneg_right ((norm_symbol_le_l1 α n).trans ?_) (norm_nonneg _)
    refine pow_le_pow_left₀ (by have := l1Norm_nonneg n; positivity) ?_ _
    have h1 := l1Norm_le_card_mul_supAbs n
    have h2 : (Fintype.card d : ℝ) * (supAbs n : ℝ) ≤ Fintype.card d * K :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    nlinarith [Real.pi_pos]
  · simp only [norm_zero, mul_zero]
    positivity

/-- **The complete field satisfies the growing derivative reserve** `eq:growing-derivatives`
(used in `thm:native-source`, "the full field satisfies the growing `C^5` reserve by the tail
bounds"): for `K ≥ 1`, `d ≥ 1` and every `|α| ≤ q`,
`‖∂^α z‖_∞ ≤ C_q K^{|α|}` with `C_q = (2πd)^q (Σ_S |c| + τ_q(K))`, where
`∂^α z = trigPoly S (derivCoeff α c)` is the classical derivative. -/
theorem growing_derivatives_of_tail [Nonempty d] (S : Finset (d → ℤ)) {K : ℝ} (hK : 1 ≤ K)
    (c : (d → ℤ) → ℂ) {α : d → ℕ} {q : ℕ} (hα : mOrder α ≤ q) :
    ‖trigPoly S (derivCoeff α c)‖ ≤
      (2 * π * Fintype.card d) ^ q * (∑ n ∈ S, ‖c n‖ + tau S K q c) * K ^ mOrder α := by
  have hK0 : 0 < K := by linarith
  have hD : (1 : ℝ) ≤ Fintype.card d := by exact_mod_cast Fintype.card_pos
  have hsplit : trigPoly S (derivCoeff α c) =
      trigPoly S (derivCoeff α (lowPart K c)) + trigPoly S (derivCoeff α (tailPart K c)) := by
    rw [← trigPoly_add]; congr 1; funext n
    simp only [derivCoeff]; rw [← mul_add, lowPart_add_tailPart]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_deriv_low_le S hK0.le c α
  have h2 := norm_deriv_tail_le S hK0 c hα
  have hpi : 1 ≤ 2 * π * (Fintype.card d : ℝ) := by nlinarith [Real.pi_gt_three]
  have hA : (2 * π * Fintype.card d * K) ^ mOrder α ≤ (2 * π * Fintype.card d) ^ q * K ^ mOrder α := by
    rw [mul_pow]; gcongr
  have hB : (2 * π * K) ^ mOrder α ≤ (2 * π * Fintype.card d) ^ q * K ^ mOrder α := by
    rw [mul_pow]
    gcongr
    calc (2 * π) ^ mOrder α ≤ (2 * π * Fintype.card d) ^ mOrder α :=
          pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos, hD]) _
      _ ≤ (2 * π * Fintype.card d) ^ q := pow_le_pow_right₀ hpi hα
  have hs : 0 ≤ ∑ n ∈ S, ‖c n‖ := sum_nonneg fun _ _ => norm_nonneg _
  have ht := tau_nonneg S hK0 q c
  calc ‖trigPoly S (derivCoeff α (lowPart K c))‖ + ‖trigPoly S (derivCoeff α (tailPart K c))‖
      ≤ (2 * π * Fintype.card d * K) ^ mOrder α * ∑ n ∈ S, ‖c n‖ +
          (2 * π * K) ^ mOrder α * tau S K q c := add_le_add h1 h2
    _ ≤ (2 * π * Fintype.card d) ^ q * K ^ mOrder α * ∑ n ∈ S, ‖c n‖ +
          (2 * π * Fintype.card d) ^ q * K ^ mOrder α * tau S K q c := by gcongr
    _ = _ := by ring

/-! ### Non-vacuity -/

/-- A two-mode example on `𝕋¹`: with `S = {0, 3}`, `c = 1` and `K = 1`, the tail is the single
mode `3`, `τ_j(1) = 4^j`, and the bound reads `‖∂^α(z - z^lo)‖ ≤ (2π)^{|α|} 4^j`. -/
example : tau ({0, fun _ => 3} : Finset (Fin 1 → ℤ)) 1 2 (fun _ => 1) = 16 := by
  have hne : (0 : Fin 1 → ℤ) ≠ fun _ => 3 := by
    intro h; have := congrFun h 0; simp at this
  unfold tau
  rw [Finset.filter_insert, if_neg (by simp [supAbs]), Finset.filter_singleton,
    if_pos (by simp [supAbs]), Finset.sum_singleton]
  simp [l1Norm]
  norm_num

end

end RenewalGeometry.TrigTail
