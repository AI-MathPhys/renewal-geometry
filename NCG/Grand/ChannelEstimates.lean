/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Channel-compiler estimate library

The quantitative core shared by the SMST noisy-channel
compiler records (`thm:SMST-noisy-Klein-refocusing`,
`thm:SMST-channel-direct-bracket`,
`thm:SMST-quadratic-channel-remainder`, ...): telescoping over
bounded factors, conjugation Lipschitz bounds, and Trotter
product formulas with explicit constants, all in a general
Banach algebra so that both matrix carriers and superoperator
algebras instantiate them.

Everything here is derived — no estimate is hypothesized:

* `prod_le_pow` / `prod_sub_prod_bound`: **bounded-factor
  telescoping** — ordered products of `ρ`-bounded factors
  satisfy `‖∏a - ∏b‖ ≤ ρ^{n-1}·∑‖aᵢ-bᵢ‖`;
* `conj_sub_conj_bound`: the **conjugation Lipschitz bound**
  `‖UXU* - VXV*‖ ≤ 2‖U-V‖‖X‖` for norm-one `U, V`;
* `norm_exp_le` / `exp_sub_one_bound` /
  `exp_sub_linear_bound`: exponential series tail estimates;
* `exp_mul_exp_sub_exp_add_bound`: the **one-step product
  defect** `‖e^a e^b - e^{a+b}‖ ≤ 2(‖a‖+‖b‖)²e^{‖a‖+‖b‖}`;
* `trotter_bound`: the **Trotter product bound**
  `‖(e^{A/n}e^{B/n})^n - e^{A+B}‖ ≤ 2(‖A‖+‖B‖)²e^{2(‖A‖+‖B‖)}/n`.
-/

open NormedSpace Filter

namespace NCG
namespace ChannelEstimates

variable {A : Type} [NormedRing A]

/-! ### Bounded-factor telescoping -/

theorem prod_le_pow [NormOneClass A] (f : ℕ → A) (ρ : ℝ)
    (hρ : 1 ≤ ρ) (n : ℕ) (hf : ∀ i < n, ‖f i‖ ≤ ρ) :
    ‖((List.range n).map f).prod‖ ≤ ρ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    calc ‖((List.range n).map f).prod * f n‖
        ≤ ‖((List.range n).map f).prod‖ * ‖f n‖ :=
          norm_mul_le _ _
      _ ≤ ρ ^ n * ρ := by
          refine mul_le_mul (ih ?_) (hf n (by omega))
            (norm_nonneg _) (by positivity)
          intro i hi
          exact hf i (by omega)
      _ = ρ ^ (n + 1) := by ring

/-- **Bounded-factor telescoping**: ordered products of
`ρ`-bounded factors differ by at most `ρ^{n-1}` times the sum
of the factor differences. -/
theorem prod_sub_prod_bound [NormOneClass A] (f g : ℕ → A)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (n : ℕ)
    (hf : ∀ i < n, ‖f i‖ ≤ ρ) (hg : ∀ i < n, ‖g i‖ ≤ ρ) :
    ‖((List.range n).map f).prod
      - ((List.range n).map g).prod‖
    ≤ ρ ^ (n - 1) * ∑ i ∈ Finset.range n, ‖f i - g i‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append,
      List.prod_append, List.prod_append]
    simp only [List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    have hid : ((List.range n).map f).prod * f n
        - ((List.range n).map g).prod * g n
        = (((List.range n).map f).prod
            - ((List.range n).map g).prod) * f n
          + ((List.range n).map g).prod * (f n - g n) := by
      noncomm_ring
    rw [hid]
    have h1 : ‖(((List.range n).map f).prod
        - ((List.range n).map g).prod) * f n‖
        ≤ (ρ ^ (n - 1)
            * ∑ i ∈ Finset.range n, ‖f i - g i‖) * ρ := by
      calc ‖(((List.range n).map f).prod
          - ((List.range n).map g).prod) * f n‖
          ≤ ‖((List.range n).map f).prod
              - ((List.range n).map g).prod‖ * ‖f n‖ :=
            norm_mul_le _ _
        _ ≤ (ρ ^ (n - 1)
              * ∑ i ∈ Finset.range n, ‖f i - g i‖) * ρ := by
            refine mul_le_mul (ih ?_ ?_) (hf n (by omega))
              (norm_nonneg _) ?_
            · intro i hi
              exact hf i (by omega)
            · intro i hi
              exact hg i (by omega)
            · positivity
    have h2 : ‖((List.range n).map g).prod * (f n - g n)‖
        ≤ ρ ^ n * ‖f n - g n‖ := by
      calc ‖((List.range n).map g).prod * (f n - g n)‖
          ≤ ‖((List.range n).map g).prod‖
            * ‖f n - g n‖ := norm_mul_le _ _
        _ ≤ ρ ^ n * ‖f n - g n‖ := by
            refine mul_le_mul_of_nonneg_right
              (prod_le_pow g ρ hρ n ?_) (norm_nonneg _)
            intro i hi
            exact hg i (by omega)
    have h5 : (ρ ^ (n - 1)
        * ∑ i ∈ Finset.range n, ‖f i - g i‖) * ρ
        ≤ ρ ^ n * ∑ i ∈ Finset.range n, ‖f i - g i‖ := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        simp
      · have h6 : ρ ^ (n - 1) * ρ = ρ ^ n := by
          rw [← pow_succ, show n - 1 + 1 = n from by omega]
        refine le_of_eq ?_
        rw [← h6]
        ring
    calc ‖(((List.range n).map f).prod
        - ((List.range n).map g).prod) * f n
        + ((List.range n).map g).prod * (f n - g n)‖
        ≤ ‖(((List.range n).map f).prod
            - ((List.range n).map g).prod) * f n‖
          + ‖((List.range n).map g).prod
              * (f n - g n)‖ := norm_add_le _ _
      _ ≤ (ρ ^ (n - 1)
            * ∑ i ∈ Finset.range n, ‖f i - g i‖) * ρ
          + ρ ^ n * ‖f n - g n‖ := add_le_add h1 h2
      _ ≤ ρ ^ n * ∑ i ∈ Finset.range n, ‖f i - g i‖
          + ρ ^ n * ‖f n - g n‖ :=
          add_le_add h5 (le_refl _)
      _ = ρ ^ n * ∑ i ∈ Finset.range (n + 1),
            ‖f i - g i‖ := by
          rw [Finset.sum_range_succ, mul_add]
      _ = ρ ^ (n + 1 - 1) * ∑ i ∈ Finset.range (n + 1),
            ‖f i - g i‖ := by
          rw [show n + 1 - 1 = n from rfl]

/-! ### Conjugation Lipschitz bound -/

/-- **Conjugation Lipschitz bound**: for norm-one `U, V` in a
normed star ring, `‖UXU* - VXV*‖ ≤ 2‖U-V‖‖X‖`. -/
theorem conj_sub_conj_bound [StarRing A] [NormedStarGroup A]
    (U V X : A) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖U * X * star U - V * X * star V‖
      ≤ 2 * ‖U - V‖ * ‖X‖ := by
  have hid : U * X * star U - V * X * star V
      = (U - V) * X * star U
        + V * X * (star U - star V) := by
    noncomm_ring
  rw [hid]
  have h1 : ‖(U - V) * X * star U‖ ≤ ‖U - V‖ * ‖X‖ := by
    calc ‖(U - V) * X * star U‖
        ≤ ‖(U - V) * X‖ * ‖star U‖ := norm_mul_le _ _
      _ ≤ ‖U - V‖ * ‖X‖ * ‖star U‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ ‖U - V‖ * ‖X‖ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_
            (by positivity)
          rw [norm_star]
          exact hU
      _ = ‖U - V‖ * ‖X‖ := mul_one _
  have h2 : ‖V * X * (star U - star V)‖
      ≤ ‖U - V‖ * ‖X‖ := by
    calc ‖V * X * (star U - star V)‖
        ≤ ‖V * X‖ * ‖star U - star V‖ := norm_mul_le _ _
      _ ≤ ‖V‖ * ‖X‖ * ‖star U - star V‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ = ‖V‖ * ‖X‖ * ‖U - V‖ := by
          rw [← star_sub, norm_star]
      _ ≤ 1 * ‖X‖ * ‖U - V‖ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hV
              (norm_nonneg _)) (norm_nonneg _)
      _ = ‖U - V‖ * ‖X‖ := by ring
  calc ‖(U - V) * X * star U
      + V * X * (star U - star V)‖
      ≤ ‖(U - V) * X * star U‖
        + ‖V * X * (star U - star V)‖ := norm_add_le _ _
    _ ≤ ‖U - V‖ * ‖X‖ + ‖U - V‖ * ‖X‖ := add_le_add h1 h2
    _ = 2 * ‖U - V‖ * ‖X‖ := by ring

/-! ### Exponential remainders -/

section Exponential

variable [NormOneClass A] [NormedAlgebra ℝ A]
  [NormedAlgebra ℚ A] [CompleteSpace A]

omit [NormedAlgebra ℚ A] [CompleteSpace A] in
theorem norm_exp_le (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [exp_eq_tsum (𝕂 := ℝ)]
  have hbound : ∀ n : ℕ,
      ‖(n.factorial : ℝ)⁻¹ • x ^ n‖
      ≤ ‖x‖ ^ n / n.factorial := by
    intro n
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x n)
      (by positivity)
  have hnsum : Summable (fun n : ℕ =>
      ‖(n.factorial : ℝ)⁻¹ • x ^ n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      hbound (Real.summable_pow_div_factorial ‖x‖)
  calc ‖∑' n : ℕ, (n.factorial : ℝ)⁻¹ • x ^ n‖
      ≤ ∑' n : ℕ, ‖(n.factorial : ℝ)⁻¹ • x ^ n‖ :=
        norm_tsum_le_tsum_norm hnsum
    _ ≤ ∑' n : ℕ, ‖x‖ ^ n / n.factorial :=
        Summable.tsum_le_tsum hbound hnsum
          (Real.summable_pow_div_factorial ‖x‖)
    _ = Real.exp ‖x‖ := by
        rw [Real.exp_eq_exp_ℝ, exp_eq_tsum_div]

omit [NormedAlgebra ℚ A] in
/-- The quadratic exponential tail. -/
theorem exp_sub_linear_bound (x : A) :
    ‖NormedSpace.exp x - 1 - x‖
      ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have hfull : HasSum
      (fun n : ℕ => (n.factorial : ℝ)⁻¹ • x ^ n)
      (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have htail : HasSum
      (fun m : ℕ => (((m + 2).factorial : ℝ))⁻¹ • x ^ (m + 2))
      (NormedSpace.exp x - 1 - x) := by
    refine (hasSum_nat_add_iff
      (f := fun n => ((n.factorial : ℝ))⁻¹ • x ^ n)
      2).mpr ?_
    have hsum01 : ∑ i ∈ Finset.range 2,
        ((i.factorial : ℝ))⁻¹ • x ^ i = 1 + x := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    rw [hsum01, show NormedSpace.exp x - 1 - x + (1 + x)
      = NormedSpace.exp x from by abel]
    exact hfull
  have hbound : ∀ m : ℕ,
      ‖(((m + 2).factorial : ℝ))⁻¹ • x ^ (m + 2)‖
      ≤ ‖x‖ ^ 2 * (‖x‖ ^ m / m.factorial) := by
    intro m
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have h1 : ‖x ^ (m + 2)‖ ≤ ‖x‖ ^ (m + 2) :=
      norm_pow_le x (m + 2)
    have h2 : ((m.factorial : ℝ)) ≤ (m + 2).factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h3 : (0:ℝ) < m.factorial := by positivity
    have h4 : (((m + 2).factorial : ℝ))⁻¹
        ≤ (m.factorial : ℝ)⁻¹ := by
      exact (inv_le_inv₀ (by positivity) h3).mpr h2
    calc (((m + 2).factorial : ℝ))⁻¹ * ‖x ^ (m + 2)‖
        ≤ (m.factorial : ℝ)⁻¹ * ‖x‖ ^ (m + 2) := by
          refine mul_le_mul h4 h1 (norm_nonneg _)
            (by positivity)
      _ = ‖x‖ ^ 2 * (‖x‖ ^ m / m.factorial) := by
          rw [pow_add]
          ring
  have hgsum : Summable (fun m : ℕ =>
      ‖x‖ ^ 2 * (‖x‖ ^ m / m.factorial)) :=
    (Real.summable_pow_div_factorial ‖x‖).mul_left _
  calc ‖NormedSpace.exp x - 1 - x‖
      ≤ ∑' m : ℕ,
          ‖(((m + 2).factorial : ℝ))⁻¹ • x ^ (m + 2)‖ := by
        rw [← htail.tsum_eq]
        exact norm_tsum_le_tsum_norm
          (Summable.of_nonneg_of_le
            (fun m => norm_nonneg _) hbound hgsum)
    _ ≤ ∑' m : ℕ, ‖x‖ ^ 2 * (‖x‖ ^ m / m.factorial) :=
        Summable.tsum_le_tsum hbound
          (Summable.of_nonneg_of_le
            (fun m => norm_nonneg _) hbound hgsum) hgsum
    _ = ‖x‖ ^ 2 * Real.exp ‖x‖ := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ,
          exp_eq_tsum_div]

omit [NormedAlgebra ℚ A] in
/-- The linear exponential tail. -/
theorem exp_sub_one_bound (x : A) :
    ‖NormedSpace.exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have hfull : HasSum
      (fun n : ℕ => (n.factorial : ℝ)⁻¹ • x ^ n)
      (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have htail : HasSum
      (fun m : ℕ => (((m + 1).factorial : ℝ))⁻¹ • x ^ (m + 1))
      (NormedSpace.exp x - 1) := by
    refine (hasSum_nat_add_iff
      (f := fun n => ((n.factorial : ℝ))⁻¹ • x ^ n)
      1).mpr ?_
    have hsum0 : ∑ i ∈ Finset.range 1,
        ((i.factorial : ℝ))⁻¹ • x ^ i = 1 := by
      rw [Finset.sum_range_one]
      norm_num
    rw [hsum0, show NormedSpace.exp x - 1 + 1
      = NormedSpace.exp x from by abel]
    exact hfull
  have hbound : ∀ m : ℕ,
      ‖(((m + 1).factorial : ℝ))⁻¹ • x ^ (m + 1)‖
      ≤ ‖x‖ * (‖x‖ ^ m / m.factorial) := by
    intro m
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have h1 : ‖x ^ (m + 1)‖ ≤ ‖x‖ ^ (m + 1) :=
      norm_pow_le x (m + 1)
    have h2 : ((m.factorial : ℝ)) ≤ (m + 1).factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h4 : (((m + 1).factorial : ℝ))⁻¹
        ≤ (m.factorial : ℝ)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr h2
    calc (((m + 1).factorial : ℝ))⁻¹ * ‖x ^ (m + 1)‖
        ≤ (m.factorial : ℝ)⁻¹ * ‖x‖ ^ (m + 1) := by
          refine mul_le_mul h4 h1 (norm_nonneg _)
            (by positivity)
      _ = ‖x‖ * (‖x‖ ^ m / m.factorial) := by
          rw [pow_succ]
          ring
  have hgsum : Summable (fun m : ℕ =>
      ‖x‖ * (‖x‖ ^ m / m.factorial)) :=
    (Real.summable_pow_div_factorial ‖x‖).mul_left _
  calc ‖NormedSpace.exp x - 1‖
      ≤ ∑' m : ℕ,
          ‖(((m + 1).factorial : ℝ))⁻¹ • x ^ (m + 1)‖ := by
        rw [← htail.tsum_eq]
        exact norm_tsum_le_tsum_norm
          (Summable.of_nonneg_of_le
            (fun m => norm_nonneg _) hbound hgsum)
    _ ≤ ∑' m : ℕ, ‖x‖ * (‖x‖ ^ m / m.factorial) :=
        Summable.tsum_le_tsum hbound
          (Summable.of_nonneg_of_le
            (fun m => norm_nonneg _) hbound hgsum) hgsum
    _ = ‖x‖ * Real.exp ‖x‖ := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ,
          exp_eq_tsum_div]

omit [NormedAlgebra ℚ A] in
/-- **The one-step product defect**:
`‖e^a e^b - e^{a+b}‖ ≤ 2(‖a‖+‖b‖)²·e^{‖a‖+‖b‖}`. -/
theorem exp_mul_exp_sub_exp_add_bound (a b : A) :
    ‖NormedSpace.exp a * NormedSpace.exp b
      - NormedSpace.exp (a + b)‖
    ≤ 2 * (‖a‖ + ‖b‖) ^ 2
      * Real.exp (‖a‖ + ‖b‖) := by
  have hid : NormedSpace.exp a * NormedSpace.exp b
      - NormedSpace.exp (a + b)
      = ((NormedSpace.exp b - 1 - b)
        + a * (NormedSpace.exp b - 1)
        + (NormedSpace.exp a - 1 - a) * NormedSpace.exp b)
        - (NormedSpace.exp (a + b) - 1 - (a + b)) := by
    noncomm_ring
  rw [hid]
  have h1 := exp_sub_linear_bound b
  have h2 : ‖a * (NormedSpace.exp b - 1)‖
      ≤ ‖a‖ * (‖b‖ * Real.exp ‖b‖) :=
    le_trans (norm_mul_le _ _)
      (mul_le_mul_of_nonneg_left (exp_sub_one_bound b)
        (norm_nonneg a))
  have h3 : ‖(NormedSpace.exp a - 1 - a)
      * NormedSpace.exp b‖
      ≤ ‖a‖ ^ 2 * Real.exp ‖a‖ * Real.exp ‖b‖ :=
    le_trans (norm_mul_le _ _)
      (mul_le_mul (exp_sub_linear_bound a) (norm_exp_le b)
        (norm_nonneg _) (by positivity))
  have h4 : ‖NormedSpace.exp (a + b) - 1 - (a + b)‖
      ≤ (‖a‖ + ‖b‖) ^ 2 * Real.exp (‖a‖ + ‖b‖) := by
    refine le_trans (exp_sub_linear_bound (a + b)) ?_
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_add_le a b) 2
    · exact Real.exp_le_exp.mpr (norm_add_le a b)
  have hea : Real.exp ‖a‖ ≤ Real.exp (‖a‖ + ‖b‖) :=
    Real.exp_le_exp.mpr (by linarith [norm_nonneg b])
  have heb : Real.exp ‖b‖ ≤ Real.exp (‖a‖ + ‖b‖) :=
    Real.exp_le_exp.mpr (by linarith [norm_nonneg a])
  have heab : Real.exp ‖a‖ * Real.exp ‖b‖
      = Real.exp (‖a‖ + ‖b‖) := (Real.exp_add _ _).symm
  have hnn_a := norm_nonneg a
  have hnn_b := norm_nonneg b
  have hexp_pos := Real.exp_pos (‖a‖ + ‖b‖)
  calc ‖(NormedSpace.exp b - 1 - b)
      + a * (NormedSpace.exp b - 1)
      + (NormedSpace.exp a - 1 - a) * NormedSpace.exp b
      - (NormedSpace.exp (a + b) - 1 - (a + b))‖
      ≤ ‖(NormedSpace.exp b - 1 - b)
          + a * (NormedSpace.exp b - 1)
          + (NormedSpace.exp a - 1 - a)
            * NormedSpace.exp b‖
        + ‖NormedSpace.exp (a + b) - 1 - (a + b)‖ :=
        norm_sub_le _ _
    _ ≤ (‖NormedSpace.exp b - 1 - b‖
          + ‖a * (NormedSpace.exp b - 1)‖
          + ‖(NormedSpace.exp a - 1 - a)
              * NormedSpace.exp b‖)
        + ‖NormedSpace.exp (a + b) - 1 - (a + b)‖ := by
        gcongr
        exact norm_add₃_le
    _ ≤ 2 * (‖a‖ + ‖b‖) ^ 2
        * Real.exp (‖a‖ + ‖b‖) := by
        rw [← heab] at h4 ⊢
        nlinarith [h1, h2, h3, h4,
          Real.exp_pos ‖a‖, Real.exp_pos ‖b‖,
          Real.one_le_exp hnn_a, Real.one_le_exp hnn_b,
          mul_nonneg hnn_a hnn_b]

/-- **The Trotter product bound** with explicit constant:
`‖(e^{X/n}e^{Y/n})^n - e^{X+Y}‖
  ≤ 2(‖X‖+‖Y‖)²·e^{2(‖X‖+‖Y‖)}/n`. -/
theorem trotter_bound (X Y : A) (n : ℕ) (hn : 0 < n) :
    ‖(NormedSpace.exp ((n : ℝ)⁻¹ • X)
        * NormedSpace.exp ((n : ℝ)⁻¹ • Y)) ^ n
      - NormedSpace.exp (X + Y)‖
    ≤ 2 * (‖X‖ + ‖Y‖) ^ 2
      * Real.exp (2 * (‖X‖ + ‖Y‖)) / n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hnne : ((n : ℝ)) ≠ 0 := ne_of_gt hnR
  set s : ℝ := ‖X‖ + ‖Y‖ with hs
  have hs0 : 0 ≤ s := by
    have := norm_nonneg X
    have := norm_nonneg Y
    linarith
  set u : A := NormedSpace.exp ((n : ℝ)⁻¹ • X)
    * NormedSpace.exp ((n : ℝ)⁻¹ • Y) with hu
  set v : A := NormedSpace.exp ((n : ℝ)⁻¹ • (X + Y))
    with hv
  have hvpow : v ^ n = NormedSpace.exp (X + Y) := by
    rw [hv, ← exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ hnne, one_smul]
  have hXn : ‖(n : ℝ)⁻¹ • X‖ = ‖X‖ / n := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  have hYn : ‖(n : ℝ)⁻¹ • Y‖ = ‖Y‖ / n := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  have hXYn : ‖(n : ℝ)⁻¹ • (X + Y)‖ ≤ s / n := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    have := norm_add_le X Y
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (by linarith)
      (by positivity)
  have hubound : ‖u‖ ≤ Real.exp (s / n) := by
    calc ‖u‖ ≤ ‖NormedSpace.exp ((n : ℝ)⁻¹ • X)‖
        * ‖NormedSpace.exp ((n : ℝ)⁻¹ • Y)‖ :=
        norm_mul_le _ _
      _ ≤ Real.exp (‖X‖ / n) * Real.exp (‖Y‖ / n) := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _)
            (by positivity)
          · rw [← hXn]
            exact norm_exp_le _
          · rw [← hYn]
            exact norm_exp_le _
      _ = Real.exp (s / n) := by
          rw [← Real.exp_add]
          congr 1
          rw [hs]
          ring
  have hvbound : ‖v‖ ≤ Real.exp (s / n) := by
    refine le_trans (norm_exp_le _) ?_
    exact Real.exp_le_exp.mpr hXYn
  have hstep : ‖u - v‖
      ≤ 2 * (s / n) ^ 2 * Real.exp (s / n) := by
    have h := exp_mul_exp_sub_exp_add_bound
      ((n : ℝ)⁻¹ • X) ((n : ℝ)⁻¹ • Y)
    rw [hXn, hYn, ← smul_add] at h
    have heq : ‖X‖ / n + ‖Y‖ / n = s / n := by
      rw [hs]
      ring
    rw [heq] at h
    exact h
  -- telescoping over the constant products
  have hulist : ((List.range n).map (fun _ => u)).prod
      = u ^ n := by
    rw [List.map_const', List.length_range,
      List.prod_replicate]
  have hvlist : ((List.range n).map (fun _ => v)).prod
      = v ^ n := by
    rw [List.map_const', List.length_range,
      List.prod_replicate]
  have hρ : (1:ℝ) ≤ Real.exp (s / n) :=
    Real.one_le_exp (by positivity)
  have htel := prod_sub_prod_bound (fun _ => u)
    (fun _ => v) (Real.exp (s / n)) hρ n
    (fun i _ => hubound) (fun i _ => hvbound)
  rw [hulist, hvlist] at htel
  have hsum : ∑ _i ∈ Finset.range n, ‖u - v‖
      = n * ‖u - v‖ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum] at htel
  have hval : Real.exp (s / n) ^ (n - 1)
      * (n * (2 * (s / n) ^ 2 * Real.exp (s / n)))
      ≤ 2 * s ^ 2 * Real.exp (2 * s) / n := by
    have h1 : Real.exp (s / n) ^ (n - 1)
        = Real.exp ((n - 1 : ℕ) * (s / n)) := by
      rw [← Real.exp_nat_mul]
    have h2 : ((n - 1 : ℕ) : ℝ) * (s / n) ≤ s := by
      have h3 : ((n - 1 : ℕ) : ℝ) ≤ n := by
        exact_mod_cast Nat.sub_le n 1
      rw [div_eq_inv_mul, ← mul_assoc]
      calc ((n - 1 : ℕ) : ℝ) * (n : ℝ)⁻¹ * s
          ≤ (n : ℝ) * (n : ℝ)⁻¹ * s := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h3
                (by positivity)) hs0
        _ = s := by
            rw [mul_inv_cancel₀ hnne, one_mul]
    have h4 : s / n ≤ s := by
      rw [div_le_iff₀ hnR]
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      nlinarith
    have h5 : Real.exp (s / n) ^ (n - 1)
        * Real.exp (s / n) ≤ Real.exp (2 * s) := by
      rw [h1, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [h2, h4]
    calc Real.exp (s / n) ^ (n - 1)
        * (n * (2 * (s / n) ^ 2 * Real.exp (s / n)))
        = (Real.exp (s / n) ^ (n - 1)
            * Real.exp (s / n)) * (2 * s ^ 2 / n) := by
          field_simp
      _ ≤ Real.exp (2 * s) * (2 * s ^ 2 / n) := by
          refine mul_le_mul_of_nonneg_right h5
            (by positivity)
      _ = 2 * s ^ 2 * Real.exp (2 * s) / n := by
          ring
  have hstepn : Real.exp (s / n) ^ (n - 1)
      * (n * ‖u - v‖)
      ≤ Real.exp (s / n) ^ (n - 1)
        * (n * (2 * (s / n) ^ 2 * Real.exp (s / n))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  calc ‖u ^ n - NormedSpace.exp (X + Y)‖
      = ‖u ^ n - v ^ n‖ := by rw [hvpow]
    _ ≤ Real.exp (s / n) ^ (n - 1) * (n * ‖u - v‖) :=
        htel
    _ ≤ Real.exp (s / n) ^ (n - 1)
        * (n * (2 * (s / n) ^ 2
            * Real.exp (s / n))) := hstepn
    _ ≤ 2 * s ^ 2 * Real.exp (2 * s) / n := hval

end Exponential

end ChannelEstimates
end NCG
