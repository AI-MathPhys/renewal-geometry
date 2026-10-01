/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.PathOrderedExponential

/-!
# Logarithm near the identity and second-order BCH for products of exponentials
(infrastructure for `thm:supp-finite-defects`, `eq:supp-curvature-defect`; emergent-spacetime
manuscript)

Let `𝔸` be a complete normed `ℝ`-algebra with `‖1‖ = 1` (e.g. real matrices with an operator
norm).

* `logOnePlus Y = ∑_{n ≥ 0} (−1)ⁿ Yⁿ⁺¹/(n+1)` is the Mercator series, i.e. the principal
  logarithm `log (1 + Y)` on the ball `‖Y‖ < 1` (the "principal chart" of the paper).
  `summable_logTerm`, `norm_logOnePlus_sub_partial_le`: the tail after `N` terms is bounded by
  `‖Y‖^{N+1}/(1 − ‖Y‖)`; in particular `‖log(1+Y) − Y‖ ≤ ‖Y‖²/(1−‖Y‖)` and
  `‖log(1+Y) − Y + Y²/2‖ ≤ ‖Y‖³/(1−‖Y‖)`.
* `norm_expProd_sub_le`: for a finite list `x₁,…,x_m`, with `s = ∑ ‖xᵢ‖`,
  `‖e^{x₁} ⋯ e^{x_m} − (1 + ∑ xᵢ + ∑ xᵢ²/2 + ∑_{i<j} xᵢ xⱼ)‖ ≤ s³ eˢ`.
* `secondOrder_eq`: `∑ xᵢ²/2 + ∑_{i<j} xᵢxⱼ = ½ ∑_{i<j} [xᵢ, xⱼ] + ½ (∑ xᵢ)²`.
* `norm_log_expProd_sub_bch_le` (**second-order BCH**): for `s ≤ 1/4`,
  `‖log(e^{x₁} ⋯ e^{x_m}) − (∑ xᵢ + ½ ∑_{i<j} [xᵢ, xⱼ])‖ ≤ 6 s³`;
  `norm_log_expProd_sub_comm_le`: for a closed loop (`∑ xᵢ = 0`) the logarithm of the holonomy
  is `½ ∑_{i<j}[xᵢ,xⱼ] + O(s³)`.

* `commTerm_reverse`: reversing the factors negates the commutator term (holonomies compose
  links in reverse boundary order).
* `norm_exp_sub_linear_le`, `norm_integral_exp_smul_sub_le`, `norm_exp_mul_integral_exp_sub_le`:
  first-order bounds for `exp` and for the developed-edge average `∫₀¹ exp(rY) dr = 1 + Y/2 + O(‖Y‖²)`,
  and `‖exp X · ∫₀¹ exp(rY) dr − (1 + X + Y/2)‖ ≤ 20 ρ²` for `‖X‖, ‖Y‖ ≤ ρ ≤ 1`.

These are the algebraic inputs of the nonabelian Stokes expansion
`log U_{∂p} = −|p| Ω(x_p) + O(h³)` of a face holonomy.
-/

namespace RenewalGeometry.LogBCH

open NormedSpace Set
open scoped Interval

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ### Exponential bounds -/

/-- `‖exp X‖ ≤ e^{‖X‖}` in a complete normed algebra with `‖1‖ = 1`. -/
theorem norm_exp_le_real_exp (X : 𝔸) : ‖exp X‖ ≤ Real.exp ‖X‖ := by
  have hT := PathOrderedExp.isTransport_const_exp (-X) 0 1
  have := PathOrderedExp.norm_transport_le (ω := fun _ => -X) (K := ‖-X‖) (fun _ _ => le_rfl)
    hT 1 ⟨zero_le_one, le_rfl⟩
  simpa [norm_neg] using this

/-- Second-order Taylor bound `‖exp X − (1 + X + X²/2)‖ ≤ ‖X‖³ e^{‖X‖}`. -/
theorem norm_exp_sub_quadratic_le (X : 𝔸) :
    ‖exp X - (1 + X + (1 / 2 : ℝ) • (X * X))‖ ≤ ‖X‖ ^ 3 * Real.exp ‖X‖ := by
  have := PathOrderedExp.norm_exp_neg_smul_sub_quadratic_le (-X) (h := 1) zero_le_one
  simp only [one_smul, neg_neg, norm_neg, one_pow, mul_one, neg_mul_neg] at this
  convert this using 2
  norm_num [sub_neg_eq_add]

/-! ### The Mercator series -/

/-- The `n`-th term `(−1)ⁿ Yⁿ⁺¹/(n+1)` of the Mercator series for `log (1 + Y)`. -/
noncomputable def logTerm (Y : 𝔸) (n : ℕ) : 𝔸 := ((-1 : ℝ) ^ n / ((n : ℝ) + 1)) • Y ^ (n + 1)

/-- The principal logarithm `log (1 + Y)`, defined by the Mercator series (convergent for
`‖Y‖ < 1`). -/
noncomputable def logOnePlus (Y : 𝔸) : 𝔸 := ∑' n, logTerm Y n

theorem norm_logTerm_le (Y : 𝔸) (n : ℕ) : ‖logTerm Y n‖ ≤ ‖Y‖ ^ (n + 1) := by
  unfold logTerm
  rw [norm_smul]
  have h1 : ‖((-1 : ℝ) ^ n / ((n : ℝ) + 1))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc ‖((-1 : ℝ) ^ n / ((n : ℝ) + 1))‖ * ‖Y ^ (n + 1)‖ ≤ 1 * ‖Y‖ ^ (n + 1) :=
        mul_le_mul h1 (norm_pow_le _ _) (norm_nonneg _) zero_le_one
    _ = ‖Y‖ ^ (n + 1) := one_mul _

theorem summable_logTerm {Y : 𝔸} (hY : ‖Y‖ < 1) : Summable (logTerm Y) := by
  refine Summable.of_norm_bounded (g := fun n => ‖Y‖ * ‖Y‖ ^ n) ?_ ?_
  · exact (summable_geometric_of_lt_one (norm_nonneg _) hY).mul_left _
  · intro n; rw [← pow_succ']; exact norm_logTerm_le Y n

/-- **Tail bound of the Mercator series**: `‖log(1+Y) − ∑_{n<N} (−1)ⁿYⁿ⁺¹/(n+1)‖ ≤
‖Y‖^{N+1}/(1 − ‖Y‖)` for `‖Y‖ < 1`. -/
theorem norm_logOnePlus_sub_partial_le {Y : 𝔸} (hY : ‖Y‖ < 1) (N : ℕ) :
    ‖logOnePlus Y - ∑ n ∈ Finset.range N, logTerm Y n‖ ≤ ‖Y‖ ^ (N + 1) / (1 - ‖Y‖) := by
  have hs := summable_logTerm hY
  have h := hs.sum_add_tsum_nat_add N
  have heq : logOnePlus Y - ∑ n ∈ Finset.range N, logTerm Y n = ∑' i, logTerm Y (i + N) := by
    unfold logOnePlus; rw [← h]; abel
  rw [heq]
  have hg : HasSum (fun i : ℕ => ‖Y‖ ^ (N + 1) * ‖Y‖ ^ i) (‖Y‖ ^ (N + 1) * (1 - ‖Y‖)⁻¹) :=
    (hasSum_geometric_of_lt_one (norm_nonneg _) hY).mul_left _
  refine (tsum_of_norm_bounded hg fun i => ?_).trans (le_of_eq (by rw [div_eq_mul_inv]))
  refine (norm_logTerm_le Y (i + N)).trans (le_of_eq ?_)
  rw [← pow_add]; congr 1; ring

theorem norm_logOnePlus_le {Y : 𝔸} (hY : ‖Y‖ < 1) :
    ‖logOnePlus Y‖ ≤ ‖Y‖ / (1 - ‖Y‖) := by
  simpa using norm_logOnePlus_sub_partial_le hY 0

/-- `‖log(1+Y) − Y‖ ≤ ‖Y‖²/(1 − ‖Y‖)`. -/
theorem norm_logOnePlus_sub_le {Y : 𝔸} (hY : ‖Y‖ < 1) :
    ‖logOnePlus Y - Y‖ ≤ ‖Y‖ ^ 2 / (1 - ‖Y‖) := by
  have := norm_logOnePlus_sub_partial_le hY 1
  simpa [logTerm] using this

/-- `‖log(1+Y) − (Y − Y²/2)‖ ≤ ‖Y‖³/(1 − ‖Y‖)`. -/
theorem norm_logOnePlus_sub_quadratic_le {Y : 𝔸} (hY : ‖Y‖ < 1) :
    ‖logOnePlus Y - (Y - (1 / 2 : ℝ) • (Y * Y))‖ ≤ ‖Y‖ ^ 3 / (1 - ‖Y‖) := by
  have := norm_logOnePlus_sub_partial_le hY 2
  have e : ∑ n ∈ Finset.range 2, logTerm Y n = Y - (1 / 2 : ℝ) • (Y * Y) := by
    simp [Finset.sum_range_succ, logTerm, pow_two, sub_eq_add_neg, neg_div]
    norm_num
  rwa [e] at this

/-- The logarithm vanishes at the identity. -/
@[simp] theorem logOnePlus_zero : logOnePlus (0 : 𝔸) = 0 := by
  simp [logOnePlus, logTerm]

/-! ### Ordered products of exponentials -/

/-- Ordered product `e^{x₁} e^{x₂} ⋯ e^{x_m}` of the list `[x₁, …, x_m]`. -/
noncomputable def expProd (L : List 𝔸) : 𝔸 := (L.map exp).prod

/-- Second-order term `∑ xᵢ²/2 + ∑_{i<j} xᵢ xⱼ` of the ordered product. -/
noncomputable def secondOrder : List 𝔸 → 𝔸
  | [] => 0
  | x :: L => (1 / 2 : ℝ) • (x * x) + x * L.sum + secondOrder L

/-- Commutator term `½ ∑_{i<j} [xᵢ, xⱼ]` (list order). -/
noncomputable def commTerm : List 𝔸 → 𝔸
  | [] => 0
  | x :: L => (1 / 2 : ℝ) • (x * L.sum - L.sum * x) + commTerm L

/-- `s = ∑ ‖xᵢ‖`. -/
def normSum (L : List 𝔸) : ℝ := (L.map norm).sum

@[simp] theorem expProd_nil : expProd ([] : List 𝔸) = 1 := rfl
@[simp] theorem expProd_cons (x : 𝔸) (L : List 𝔸) : expProd (x :: L) = exp x * expProd L := by
  simp [expProd]
@[simp] theorem normSum_nil : normSum ([] : List 𝔸) = 0 := rfl
@[simp] theorem normSum_cons (x : 𝔸) (L : List 𝔸) : normSum (x :: L) = ‖x‖ + normSum L := by
  simp [normSum]

theorem normSum_nonneg (L : List 𝔸) : 0 ≤ normSum L := by
  induction L with
  | nil => simp
  | cons x L ih => rw [normSum_cons]; exact add_nonneg (norm_nonneg _) ih

theorem norm_sum_le_normSum (L : List 𝔸) : ‖L.sum‖ ≤ normSum L := by
  induction L with
  | nil => simp
  | cons x L ih => rw [List.sum_cons, normSum_cons]; exact (norm_add_le _ _).trans (by linarith)

/-- `secondOrder = commTerm + ½ (∑ xᵢ)²`. -/
theorem secondOrder_eq (L : List 𝔸) :
    secondOrder L = commTerm L + (1 / 2 : ℝ) • (L.sum * L.sum) := by
  induction L with
  | nil => simp [secondOrder, commTerm]
  | cons x L ih =>
    simp only [secondOrder, commTerm, List.sum_cons, ih, add_mul, mul_add]
    module

theorem norm_secondOrder_le (L : List 𝔸) : ‖secondOrder L‖ ≤ normSum L ^ 2 / 2 := by
  induction L with
  | nil => simp [secondOrder]
  | cons x L ih =>
    simp only [secondOrder, normSum_cons]
    have h1 : ‖(1 / 2 : ℝ) • (x * x)‖ ≤ ‖x‖ ^ 2 / 2 := by
      rw [norm_smul]
      have := norm_mul_le x x
      norm_num; nlinarith
    have h2 : ‖x * L.sum‖ ≤ ‖x‖ * normSum L :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_sum_le_normSum L) (norm_nonneg _))
    calc ‖(1 / 2 : ℝ) • (x * x) + x * L.sum + secondOrder L‖
        ≤ ‖(1 / 2 : ℝ) • (x * x)‖ + ‖x * L.sum‖ + ‖secondOrder L‖ := norm_add₃_le
      _ ≤ ‖x‖ ^ 2 / 2 + ‖x‖ * normSum L + normSum L ^ 2 / 2 := by gcongr
      _ = (‖x‖ + normSum L) ^ 2 / 2 := by ring

theorem norm_commTerm_le (L : List 𝔸) : ‖commTerm L‖ ≤ normSum L ^ 2 / 2 := by
  induction L with
  | nil => simp [commTerm]
  | cons x L ih =>
    simp only [commTerm, normSum_cons]
    have hS := norm_sum_le_normSum L
    have h1 : ‖(1 / 2 : ℝ) • (x * L.sum - L.sum * x)‖ ≤ ‖x‖ * normSum L := by
      rw [norm_smul]
      have := norm_sub_le (x * L.sum) (L.sum * x)
      have a1 := norm_mul_le x L.sum
      have a2 := norm_mul_le L.sum x
      have hx := norm_nonneg x
      norm_num
      nlinarith [mul_le_mul_of_nonneg_left hS hx]
    calc ‖(1 / 2 : ℝ) • (x * L.sum - L.sum * x) + commTerm L‖
        ≤ ‖x‖ * normSum L + normSum L ^ 2 / 2 := (norm_add_le _ _).trans (by gcongr)
      _ ≤ (‖x‖ + normSum L) ^ 2 / 2 := by nlinarith [norm_nonneg x]

/-- **Second-order expansion of an ordered product of exponentials**:
`‖e^{x₁} ⋯ e^{x_m} − (1 + ∑ xᵢ + ∑ xᵢ²/2 + ∑_{i<j} xᵢxⱼ)‖ ≤ s³ eˢ`, `s = ∑ ‖xᵢ‖`. -/
theorem norm_expProd_sub_le (L : List 𝔸) :
    ‖expProd L - (1 + L.sum + secondOrder L)‖ ≤ normSum L ^ 3 * Real.exp (normSum L) := by
  induction L with
  | nil => simp [secondOrder]
  | cons x L ih =>
    set P := expProd L
    set S := L.sum
    set s2 := secondOrder L
    set σ := normSum L
    set a := ‖x‖
    have hσ : 0 ≤ σ := normSum_nonneg L
    have ha : 0 ≤ a := norm_nonneg x
    have hS : ‖S‖ ≤ σ := norm_sum_le_normSum L
    have hs2 : ‖s2‖ ≤ σ ^ 2 / 2 := norm_secondOrder_le L
    set r := exp x - (1 + x + (1 / 2 : ℝ) • (x * x))
    have hr : ‖r‖ ≤ a ^ 3 * Real.exp a := norm_exp_sub_quadratic_le x
    set Q := 1 + S + s2
    have hQ : ‖Q‖ ≤ 1 + σ + σ ^ 2 / 2 := by
      calc ‖Q‖ ≤ ‖(1 : 𝔸)‖ + ‖S‖ + ‖s2‖ := norm_add₃_le
        _ ≤ 1 + σ + σ ^ 2 / 2 := by rw [norm_one]; gcongr
    have hQe : 1 + σ + σ ^ 2 / 2 ≤ Real.exp σ := by
      have := Real.quadratic_le_exp_of_nonneg hσ; linarith
    have hexp : ‖exp x‖ ≤ Real.exp a := norm_exp_le_real_exp x
    have key : expProd (x :: L) - (1 + (x :: L).sum + secondOrder (x :: L))
        = exp x * (P - Q) + r * Q
          + (x * s2 + (1 / 2 : ℝ) • (x * x) * S + (1 / 2 : ℝ) • (x * x) * s2) := by
      simp only [expProd_cons, List.sum_cons, secondOrder, r, Q, P, S, s2]
      simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, smul_mul_assoc, mul_assoc]
      abel
    rw [key, normSum_cons]
    have t1 : ‖exp x * (P - Q)‖ ≤ Real.exp a * (σ ^ 3 * Real.exp σ) :=
      (norm_mul_le _ _).trans (mul_le_mul hexp ih (norm_nonneg _) (Real.exp_pos _).le)
    have t2 : ‖r * Q‖ ≤ a ^ 3 * Real.exp a * Real.exp σ :=
      (norm_mul_le _ _).trans (mul_le_mul hr (hQ.trans hQe) (norm_nonneg _) (by positivity))
    have hxx : ‖(1 / 2 : ℝ) • (x * x)‖ ≤ a ^ 2 / 2 := by
      rw [norm_smul]; have := norm_mul_le x x; norm_num; nlinarith
    have t3 : ‖x * s2 + (1 / 2 : ℝ) • (x * x) * S + (1 / 2 : ℝ) • (x * x) * s2‖
        ≤ a * (σ ^ 2 / 2) + a ^ 2 / 2 * σ + a ^ 2 / 2 * (σ ^ 2 / 2) := by
      refine norm_add₃_le.trans ?_
      gcongr
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hs2 ha)
      · exact (norm_mul_le _ _).trans (mul_le_mul hxx hS (norm_nonneg _) (by positivity))
      · exact (norm_mul_le _ _).trans (mul_le_mul hxx hs2 (norm_nonneg _) (by positivity))
    have hE : 1 + σ ≤ Real.exp (a + σ) := by
      have := Real.add_one_le_exp (a + σ); linarith
    have hEab : Real.exp a * Real.exp σ = Real.exp (a + σ) := (Real.exp_add a σ).symm
    have hE0 : 0 < Real.exp (a + σ) := Real.exp_pos _
    calc ‖exp x * (P - Q) + r * Q
          + (x * s2 + (1 / 2 : ℝ) • (x * x) * S + (1 / 2 : ℝ) • (x * x) * s2)‖
        ≤ Real.exp a * (σ ^ 3 * Real.exp σ) + a ^ 3 * Real.exp a * Real.exp σ
          + (a * (σ ^ 2 / 2) + a ^ 2 / 2 * σ + a ^ 2 / 2 * (σ ^ 2 / 2)) :=
          norm_add₃_le.trans (by gcongr)
      _ = (σ ^ 3 + a ^ 3) * Real.exp (a + σ)
          + (a * (σ ^ 2 / 2) + a ^ 2 / 2 * σ + a ^ 2 / 2 * (σ ^ 2 / 2)) := by
          rw [← hEab]; ring
      _ ≤ (a + σ) ^ 3 * Real.exp (a + σ) := by
          have h3 : a * (σ ^ 2 / 2) + a ^ 2 / 2 * σ + a ^ 2 / 2 * (σ ^ 2 / 2)
              ≤ (3 * a ^ 2 * σ + 3 * a * σ ^ 2) * Real.exp (a + σ) := by
            have hm : 0 ≤ 3 * a ^ 2 * σ + 3 * a * σ ^ 2 := by positivity
            have := mul_le_mul_of_nonneg_left hE hm
            nlinarith [mul_nonneg (mul_nonneg ha ha) (mul_nonneg hσ hσ),
              mul_nonneg ha (mul_nonneg hσ hσ), mul_nonneg (mul_nonneg ha ha) hσ]
          nlinarith

/-- **Second-order BCH for a finite product of exponentials**: if `s = ∑ ‖xᵢ‖ ≤ 1/4` then
`‖log(e^{x₁} ⋯ e^{x_m}) − (∑ xᵢ + ½ ∑_{i<j}[xᵢ,xⱼ])‖ ≤ 6 s³`, with `log = logOnePlus (· − 1)` the
principal logarithm. -/
theorem norm_log_expProd_sub_bch_le (L : List 𝔸) (hs : normSum L ≤ 1 / 4) :
    ‖logOnePlus (expProd L - 1) - (L.sum + commTerm L)‖ ≤ 6 * normSum L ^ 3 := by
  set s := normSum L
  have hs0 : 0 ≤ s := normSum_nonneg L
  set S := L.sum
  have hS : ‖S‖ ≤ s := norm_sum_le_normSum L
  set E := expProd L - (1 + S + secondOrder L)
  have hes : Real.exp s ≤ 4 / 3 := by
    rcases hs0.lt_or_eq with h | h
    · have := Real.exp_bound_div_one_sub_of_interval' h (by linarith)
      have h1 : 1 / (1 - s) ≤ 4 / 3 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    · rw [← h, Real.exp_zero]; norm_num
  have hE : ‖E‖ ≤ 4 / 3 * s ^ 3 :=
    (norm_expProd_sub_le L).trans (by nlinarith [pow_nonneg hs0 3])
  have hs2 : ‖secondOrder L‖ ≤ s ^ 2 / 2 := norm_secondOrder_le L
  set Y := expProd L - 1
  have hYS : Y - S = secondOrder L + E := by simp only [Y, E]; abel
  have hYSn : ‖Y - S‖ ≤ 5 / 6 * s ^ 2 := by
    rw [hYS]
    calc ‖secondOrder L + E‖ ≤ s ^ 2 / 2 + 4 / 3 * s ^ 3 := (norm_add_le _ _).trans (by gcongr)
      _ ≤ 5 / 6 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hY : ‖Y‖ ≤ 29 / 24 * s := by
    have : Y = S + (Y - S) := by abel
    rw [this]
    calc ‖S + (Y - S)‖ ≤ s + 5 / 6 * s ^ 2 := (norm_add_le _ _).trans (by gcongr)
      _ ≤ 29 / 24 * s := by nlinarith
  have hY1 : ‖Y‖ < 1 := by linarith
  have hlog := norm_logOnePlus_sub_quadratic_le hY1
  have hlog' : ‖logOnePlus Y - (Y - (1 / 2 : ℝ) • (Y * Y))‖ ≤ 3 * s ^ 3 := by
    refine hlog.trans ?_
    have h1 : 1 / 2 ≤ 1 - ‖Y‖ := by linarith
    rw [div_le_iff₀ (by linarith)]
    have hY3 : ‖Y‖ ^ 3 ≤ (29 / 24 * s) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hY 3
    nlinarith [pow_nonneg hs0 3]
  have hdecomp : logOnePlus Y - (S + commTerm L)
      = (logOnePlus Y - (Y - (1 / 2 : ℝ) • (Y * Y))) + E
        - (1 / 2 : ℝ) • (Y * (Y - S) + (Y - S) * S) := by
    have h2 := secondOrder_eq L
    have hE' : E = Y - S - secondOrder L := by simp only [Y, E]; abel
    rw [hE', h2]
    simp only [mul_sub, sub_mul, smul_sub, smul_add]
    abel
  rw [hdecomp]
  have hq : ‖(1 / 2 : ℝ) • (Y * (Y - S) + (Y - S) * S)‖ ≤ 1 / 2 * ((29 / 24 * s + s) *
      (5 / 6 * s ^ 2)) := by
    rw [norm_smul]
    have : ‖Y * (Y - S) + (Y - S) * S‖ ≤ (29 / 24 * s + s) * (5 / 6 * s ^ 2) := by
      calc ‖Y * (Y - S) + (Y - S) * S‖ ≤ ‖Y‖ * ‖Y - S‖ + ‖Y - S‖ * ‖S‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ 29 / 24 * s * (5 / 6 * s ^ 2) + 5 / 6 * s ^ 2 * s := by
            gcongr
        _ = (29 / 24 * s + s) * (5 / 6 * s ^ 2) := by ring
    norm_num
    linarith
  calc ‖(logOnePlus Y - (Y - (1 / 2 : ℝ) • (Y * Y))) + E
        - (1 / 2 : ℝ) • (Y * (Y - S) + (Y - S) * S)‖
      ≤ 3 * s ^ 3 + 4 / 3 * s ^ 3 + 1 / 2 * ((29 / 24 * s + s) * (5 / 6 * s ^ 2)) :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hlog' hE)) hq)
    _ ≤ 6 * s ^ 3 := by nlinarith [pow_nonneg hs0 3]

/-- **Logarithm of a closed-loop holonomy**: if `∑ xᵢ = 0` and `s = ∑ ‖xᵢ‖ ≤ 1/4`, then
`‖log(e^{x₁} ⋯ e^{x_m}) − ½ ∑_{i<j}[xᵢ,xⱼ]‖ ≤ 6 s³`. -/
theorem norm_log_expProd_sub_comm_le (L : List 𝔸) (hs : normSum L ≤ 1 / 4)
    (h0 : L.sum = 0) :
    ‖logOnePlus (expProd L - 1) - commTerm L‖ ≤ 6 * normSum L ^ 3 := by
  simpa [h0] using norm_log_expProd_sub_bch_le L hs


/-! ### Reversal of the order of the factors -/

theorem expProd_append (L₁ L₂ : List 𝔸) : expProd (L₁ ++ L₂) = expProd L₁ * expProd L₂ := by
  simp [expProd, List.map_append, List.prod_append]

theorem expProd_singleton (x : 𝔸) : expProd [x] = exp x := by simp [expProd]

theorem normSum_reverse (L : List 𝔸) : normSum L.reverse = normSum L := by
  simp [normSum, List.map_reverse, List.sum_reverse]

theorem commTerm_append_singleton (L : List 𝔸) (y : 𝔸) :
    commTerm (L ++ [y]) = commTerm L + (1 / 2 : ℝ) • (L.sum * y - y * L.sum) := by
  induction L with
  | nil => simp [commTerm]
  | cons x L ih =>
    simp only [List.cons_append, commTerm, ih, List.sum_append, List.sum_cons, List.sum_nil,
      add_zero, mul_add, add_mul]
    module

/-- Reversing the order of the factors negates the commutator term. -/
theorem commTerm_reverse (L : List 𝔸) : commTerm L.reverse = -commTerm L := by
  induction L with
  | nil => simp [commTerm]
  | cons x L ih =>
    rw [List.reverse_cons, commTerm_append_singleton, ih, List.sum_reverse]
    simp only [commTerm]
    module

/-! ### First-order bounds and developed (averaged) exponentials -/

/-- First-order Taylor bound `‖exp X − 1 − X‖ ≤ ‖X‖² e^{‖X‖}`. -/
theorem norm_exp_sub_linear_le (X : 𝔸) :
    ‖exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  have hT := PathOrderedExp.isTransport_const_exp (-X) 0 1
  have := PathOrderedExp.norm_transport_sub_dyson_one_le (ω := fun _ => -X) (K := ‖-X‖)
    continuousOn_const (fun _ _ => le_rfl) hT (by simp) ⟨zero_le_one, le_rfl⟩
  simp only [sub_zero, one_smul, neg_neg, norm_neg, one_pow, mul_one,
    intervalIntegral.integral_const, smul_neg] at this
  convert this using 2
  abel

theorem continuous_exp_smul (Y : 𝔸) : Continuous fun r : ℝ => exp (r • Y) :=
  continuous_iff_continuousAt.2 fun r =>
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y r).continuousAt

/-- `‖∫₀¹ exp(rY) dr‖ ≤ e^{‖Y‖}`. -/
theorem norm_integral_exp_smul_le (Y : 𝔸) :
    ‖∫ r in (0 : ℝ)..1, exp (r • Y)‖ ≤ Real.exp ‖Y‖ := by
  have h : ∀ r ∈ Ι (0 : ℝ) 1, ‖exp (r • Y)‖ ≤ Real.exp ‖Y‖ := by
    intro r hr
    rw [uIoc_of_le zero_le_one] at hr
    refine (norm_exp_le_real_exp _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hr.2
  have := intervalIntegral.norm_integral_le_of_norm_le_const h
  simpa using this

/-- **Developed-edge average**: `‖∫₀¹ exp(rY) dr − 1 − Y/2‖ ≤ ‖Y‖² e^{‖Y‖}`. -/
theorem norm_integral_exp_smul_sub_le (Y : 𝔸) :
    ‖(∫ r in (0 : ℝ)..1, exp (r • Y)) - 1 - (1 / 2 : ℝ) • Y‖ ≤ ‖Y‖ ^ 2 * Real.exp ‖Y‖ := by
  have hi1 : IntervalIntegrable (fun r : ℝ => exp (r • Y)) MeasureTheory.volume 0 1 :=
    (continuous_exp_smul Y).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun _ : ℝ => (1 : 𝔸)) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hi3 : IntervalIntegrable (fun r : ℝ => r • Y) MeasureTheory.volume 0 1 :=
    (continuous_id.smul continuous_const).intervalIntegrable 0 1
  have e : (∫ r in (0 : ℝ)..1, exp (r • Y)) - 1 - (1 / 2 : ℝ) • Y
      = ∫ r in (0 : ℝ)..1, (exp (r • Y) - 1 - r • Y) := by
    rw [intervalIntegral.integral_sub (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_smul_const, integral_id]
    simp
  rw [e]
  have h : ∀ r ∈ Ι (0 : ℝ) 1, ‖exp (r • Y) - 1 - r • Y‖ ≤ ‖Y‖ ^ 2 * Real.exp ‖Y‖ := by
    intro r hr
    rw [uIoc_of_le zero_le_one] at hr
    have hrY : ‖r • Y‖ ≤ ‖Y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hr.2
    refine (norm_exp_sub_linear_le _).trans ?_
    gcongr
  have := intervalIntegral.norm_integral_le_of_norm_le_const h
  simpa using this

/-- **One developed edge transported to the face midpoint**: for `‖X‖, ‖Y‖ ≤ ρ ≤ 1`,
`‖exp X · ∫₀¹ exp(rY) dr − (1 + X + Y/2)‖ ≤ 20 ρ²`. -/
theorem norm_exp_mul_integral_exp_sub_le {X Y : 𝔸} {ρ : ℝ} (hX : ‖X‖ ≤ ρ) (hY : ‖Y‖ ≤ ρ)
    (hρ : ρ ≤ 1) :
    ‖exp X * (∫ r in (0 : ℝ)..1, exp (r • Y)) - (1 + X + (1 / 2 : ℝ) • Y)‖ ≤ 20 * ρ ^ 2 := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hX
  have he : Real.exp ρ ≤ 3 := by
    have := Real.exp_one_lt_d9
    have h1 : Real.exp ρ ≤ Real.exp 1 := Real.exp_le_exp.2 hρ
    linarith
  set B := ∫ r in (0 : ℝ)..1, exp (r • Y)
  set α := exp X - 1 - X
  set β := B - 1 - (1 / 2 : ℝ) • Y
  have hα : ‖α‖ ≤ 3 * ρ ^ 2 := by
    refine (norm_exp_sub_linear_le X).trans ?_
    have h1 : ‖X‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hX 2
    have h2 : Real.exp ‖X‖ ≤ 3 := (Real.exp_le_exp.2 hX).trans he
    nlinarith [sq_nonneg ‖X‖, Real.exp_pos ‖X‖]
  have hβ : ‖β‖ ≤ 3 * ρ ^ 2 := by
    refine (norm_integral_exp_smul_sub_le Y).trans ?_
    have h1 : ‖Y‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hY 2
    have h2 : Real.exp ‖Y‖ ≤ 3 := (Real.exp_le_exp.2 hY).trans he
    nlinarith [sq_nonneg ‖Y‖, Real.exp_pos ‖Y‖]
  have hB : ‖B‖ ≤ 3 := (norm_integral_exp_smul_le Y).trans ((Real.exp_le_exp.2 hY).trans he)
  have key : exp X * B - (1 + X + (1 / 2 : ℝ) • Y)
      = X * ((1 / 2 : ℝ) • Y) + (1 + X) * β + α * B := by
    simp only [α, β]
    simp only [mul_sub, sub_mul, add_mul, one_mul, mul_one]
    abel
  rw [key]
  have t1 : ‖X * ((1 / 2 : ℝ) • Y)‖ ≤ ρ * (ρ / 2) := by
    refine (norm_mul_le _ _).trans (mul_le_mul hX ?_ (norm_nonneg _) hρ0)
    rw [norm_smul]; norm_num; linarith
  have t2 : ‖(1 + X) * β‖ ≤ (1 + ρ) * (3 * ρ ^ 2) := by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ hβ (norm_nonneg _) (by linarith))
    exact (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have t3 : ‖α * B‖ ≤ 3 * ρ ^ 2 * 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hα hB (norm_nonneg _) (by positivity))
  calc ‖X * ((1 / 2 : ℝ) • Y) + (1 + X) * β + α * B‖
      ≤ ρ * (ρ / 2) + (1 + ρ) * (3 * ρ ^ 2) + 3 * ρ ^ 2 * 3 :=
        norm_add₃_le.trans (add_le_add (add_le_add t1 t2) t3)
    _ ≤ 20 * ρ ^ 2 := by nlinarith

end RenewalGeometry.LogBCH
