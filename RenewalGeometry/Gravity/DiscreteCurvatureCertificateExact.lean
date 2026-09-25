/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Fully discrete initial-energy curvature certificate
  (`thm:main-discrete-curvature`, `eq:main-discrete-curvature-update`,
  `eq:main-discrete-curvature-budgets`, `eq:main-discrete-curvature-bound`;
  emergent-spacetime manuscript)

On a finite-dimensional real inner-product space `V` (the normalized curvature
record space `Y_j = M_j^{1/2} y_j`), the recorded midpoint step
`eq:main-discrete-curvature-update`
`Y_{j+1} - T_j Y_j = s_j (K_j + L_j) (Y_{j+1} + T_j Y_j)/2 + ε_j`
with `K_j` skew, `(L_j + L_jᵀ)/2 ≼ a_j I` (encoded as `⟪x, L_j x⟫ ≤ a_j ‖x‖²`),
`‖T_j‖_op ≤ e^{d_j}`, `a_j, d_j ≥ 0`, `s_j > 0` and `s_j a_j / 2 ≤ b < 1`
satisfies:

* unique solvability of each recorded linear step
  (`implicit_step_bijective`, `discrete_curvature_certificate`, first clause);
* the energy step `(1 - s a/2) ‖Y_{j+1}‖ ≤ (1 + s a/2) ‖T Y_j‖ + ‖ε_j‖`
  obtained by pairing the update with the midpoint, so that the skew part
  cancels before any norm is taken (`discrete_energy_step`; no restriction on
  `s_j ‖K_j‖_op` enters);
* the boxed bound `eq:main-discrete-curvature-bound`
  `max_j ‖Y_j‖ ≤ e^{D + A/(1-b)} (‖Y_0‖ + √(T 𝒟)/(1-b))` with
  `D = Σ d_j`, `A = Σ s_j a_j`, `𝒟 = Σ ‖ε_j‖²/s_j`, `T = Σ s_j`
  (`discrete_curvature_certificate`, second clause, stated for every
  `j ≤ M`), via `(1+x)/(1-x) ≤ e^{2x/(1-b)}` (`one_add_div_one_sub_le_exp`)
  and the weighted Cauchy–Schwarz inequality `Σ ‖ε_j‖ ≤ √(T 𝒟)`
  (`sum_norm_le_sqrt_weighted`).

Scoped out (disclosed): the final sentence of the theorem (uniform
`L²(K)` curvature bound from a stable interval interpolation, a lapse bound
and a bounded reconstruction error) is the same analytic interpolation
abstraction as in `thm:main-curvature-propagation` and is not formalised here.
-/

open scoped BigOperators InnerProductSpace
open Finset

namespace RenewalGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Coercivity of the implicit midpoint operator `I - (s/2)(K + L)`:
`⟪x, (I - (s/2)(K+L)) x⟫ ≥ (1 - s a/2) ‖x‖²` when `K` is skew and
`⟪x, L x⟫ ≤ a ‖x‖²`. -/
theorem inner_implicit_step_ge {K L : V →L[ℝ] V} {s a : ℝ}
    (hK : ∀ x, ⟪x, K x⟫_ℝ = 0) (hL : ∀ x, ⟪x, L x⟫_ℝ ≤ a * ‖x‖ ^ 2) (hs : 0 ≤ s)
    (x : V) :
    (1 - s * a / 2) * ‖x‖ ^ 2 ≤ ⟪x, x - (s / 2) • (K + L) x⟫_ℝ := by
  rw [inner_sub_right, real_inner_smul_right, ContinuousLinearMap.add_apply, inner_add_right,
    hK, real_inner_self_eq_norm_sq]
  have := mul_le_mul_of_nonneg_left (hL x) (div_nonneg hs zero_le_two)
  linarith

/-- Each recorded linear step is uniquely solvable: `x ↦ x - (s/2)(K+L)x` is a
bijection of the finite-dimensional record space when `s a / 2 < 1`. -/
theorem implicit_step_bijective [FiniteDimensional ℝ V] {K L : V →L[ℝ] V} {s a : ℝ}
    (hK : ∀ x, ⟪x, K x⟫_ℝ = 0) (hL : ∀ x, ⟪x, L x⟫_ℝ ≤ a * ‖x‖ ^ 2) (hs : 0 ≤ s)
    (hsa : s * a / 2 < 1) :
    Function.Bijective (fun x : V => x - (s / 2) • (K + L) x) := by
  let B : V →ₗ[ℝ] V := LinearMap.id - (s / 2) • (K + L : V →L[ℝ] V).toLinearMap
  have hB : (fun x : V => x - (s / 2) • (K + L) x) = B := by
    funext x
    simp [B]
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : B x = x - (s / 2) • (K + L) x := by simp [B]
    have h1 := inner_implicit_step_ge hK hL hs x
    rw [← h0, hx, inner_zero_right] at h1
    have h2 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
    have h3 : 0 < 1 - s * a / 2 := by linarith
    have h4 : ‖x‖ ^ 2 = 0 := by nlinarith
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4)
  rw [hB]
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Energy step obtained by pairing the midpoint update
`w - v = s (K + L) (w + v)/2 + ε` with the midpoint: the skew part cancels
exactly and `(1 - s a/2) ‖w‖ ≤ (1 + s a/2) ‖v‖ + ‖ε‖`. -/
theorem discrete_energy_step {K L : V →L[ℝ] V} {s a : ℝ}
    (hK : ∀ x, ⟪x, K x⟫_ℝ = 0) (hL : ∀ x, ⟪x, L x⟫_ℝ ≤ a * ‖x‖ ^ 2) (hs : 0 ≤ s)
    (ha : 0 ≤ a) {v w ε : V}
    (hupd : w - v = s • (K + L) ((1 / 2 : ℝ) • (w + v)) + ε) :
    (1 - s * a / 2) * ‖w‖ ≤ (1 + s * a / 2) * ‖v‖ + ‖ε‖ := by
  set m : V := (1 / 2 : ℝ) • (w + v) with hm
  have h1 : ⟪w - v, m⟫_ℝ = (‖w‖ ^ 2 - ‖v‖ ^ 2) / 2 := by
    rw [hm, real_inner_smul_right, inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm v w]
    ring
  have h2 : ⟪w - v, m⟫_ℝ ≤ s * a * ‖m‖ ^ 2 + ‖ε‖ * ‖m‖ := by
    rw [hupd, inner_add_left, real_inner_smul_left, ContinuousLinearMap.add_apply,
      inner_add_left]
    have hKm : ⟪K m, m⟫_ℝ = 0 := by rw [real_inner_comm]; exact hK m
    have hLm : ⟪L m, m⟫_ℝ ≤ a * ‖m‖ ^ 2 := by rw [real_inner_comm]; exact hL m
    have hε : ⟪ε, m⟫_ℝ ≤ ‖ε‖ * ‖m‖ := real_inner_le_norm ε m
    have := mul_le_mul_of_nonneg_left hLm hs
    rw [hKm]
    nlinarith
  have hm_norm : ‖m‖ ≤ (‖w‖ + ‖v‖) / 2 := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := norm_add_le w v
    linarith
  have hm0 : 0 ≤ ‖m‖ := norm_nonneg _
  have h3 : ‖w‖ ^ 2 - ‖v‖ ^ 2 ≤ s * a / 2 * (‖w‖ + ‖v‖) ^ 2 + ‖ε‖ * (‖w‖ + ‖v‖) := by
    have hsa : 0 ≤ s * a := mul_nonneg hs ha
    have hm2 : ‖m‖ ^ 2 ≤ ((‖w‖ + ‖v‖) / 2) ^ 2 := pow_le_pow_left₀ hm0 hm_norm 2
    have hε0 : 0 ≤ ‖ε‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hm2 hsa, mul_le_mul_of_nonneg_left hm_norm hε0]
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  rcases (add_nonneg hw0 hv0).lt_or_eq with hS | hS
  · have h4 : (1 - s * a / 2) * ‖w‖ * (‖w‖ + ‖v‖) ≤
        ((1 + s * a / 2) * ‖v‖ + ‖ε‖) * (‖w‖ + ‖v‖) := by nlinarith [h3]
    exact le_of_mul_le_mul_right h4 hS
  · have hw : ‖w‖ = 0 := by linarith
    have hv : ‖v‖ = 0 := by linarith
    rw [hw, hv]
    have := norm_nonneg ε
    linarith

/-- `(1 + x)/(1 - x) ≤ exp (2x/(1-b))` for `0 ≤ x ≤ b < 1`. -/
theorem one_add_div_one_sub_le_exp {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) (hb : b < 1) :
    (1 + x) / (1 - x) ≤ Real.exp (2 * x / (1 - b)) := by
  have hx1 : 0 < 1 - x := by linarith
  have hb1 : 0 < 1 - b := by linarith
  have h1 : (1 + x) / (1 - x) = 1 + 2 * x / (1 - x) := by
    field_simp
    ring
  have h2 : 2 * x / (1 - x) ≤ 2 * x / (1 - b) :=
    div_le_div_of_nonneg_left (by linarith) hb1 (by linarith)
  have h3 := Real.add_one_le_exp (2 * x / (1 - b))
  rw [h1]
  linarith

/-- One recorded step: `‖Y_{j+1}‖ ≤ e^{d + s a/(1-b)} ‖Y_j‖ + ‖ε‖/(1-b)`. -/
theorem discrete_step_bound {K L T : V →L[ℝ] V} {s a d b : ℝ}
    (hK : ∀ x, ⟪x, K x⟫_ℝ = 0) (hL : ∀ x, ⟪x, L x⟫_ℝ ≤ a * ‖x‖ ^ 2) (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hT : ‖T‖ ≤ Real.exp d) (hb : s * a / 2 ≤ b) (hb1 : b < 1)
    {Y Y' ε : V}
    (hupd : Y' - T Y = s • (K + L) ((1 / 2 : ℝ) • (Y' + T Y)) + ε) :
    ‖Y'‖ ≤ Real.exp (d + s * a / (1 - b)) * ‖Y‖ + ‖ε‖ / (1 - b) := by
  set x : ℝ := s * a / 2 with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : 0 < 1 - x := by linarith
  have hb0 : 0 < 1 - b := by linarith
  have h := discrete_energy_step hK hL hs ha hupd
  rw [← hx] at h
  have hTY : ‖T Y‖ ≤ Real.exp d * ‖Y‖ :=
    (T.le_opNorm Y).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have h' : (1 - x) * ‖Y'‖ ≤ (1 + x) * (Real.exp d * ‖Y‖) + ‖ε‖ := by
    have := mul_le_mul_of_nonneg_left hTY (by linarith : (0 : ℝ) ≤ 1 + x)
    linarith
  have hdiv : ‖Y'‖ ≤ ((1 + x) * (Real.exp d * ‖Y‖) + ‖ε‖) / (1 - x) := by
    rw [le_div_iff₀ hx1]
    linarith
  have hratio : (1 + x) / (1 - x) ≤ Real.exp (2 * x / (1 - b)) :=
    one_add_div_one_sub_le_exp hx0 hb hb1
  have hε : ‖ε‖ / (1 - x) ≤ ‖ε‖ / (1 - b) :=
    div_le_div_of_nonneg_left (norm_nonneg _) hb0 (by linarith)
  have hsplit : ((1 + x) * (Real.exp d * ‖Y‖) + ‖ε‖) / (1 - x) =
      (1 + x) / (1 - x) * (Real.exp d * ‖Y‖) + ‖ε‖ / (1 - x) := by
    field_simp
  have hexp : Real.exp (d + s * a / (1 - b)) = Real.exp (2 * x / (1 - b)) * Real.exp d := by
    rw [← Real.exp_add, hx]
    congr 1
    ring
  have hY0 : 0 ≤ Real.exp d * ‖Y‖ := by positivity
  calc ‖Y'‖ ≤ ((1 + x) * (Real.exp d * ‖Y‖) + ‖ε‖) / (1 - x) := hdiv
    _ = (1 + x) / (1 - x) * (Real.exp d * ‖Y‖) + ‖ε‖ / (1 - x) := hsplit
    _ ≤ Real.exp (2 * x / (1 - b)) * (Real.exp d * ‖Y‖) + ‖ε‖ / (1 - b) := by
        gcongr
    _ = Real.exp (d + s * a / (1 - b)) * ‖Y‖ + ‖ε‖ / (1 - b) := by
        rw [hexp]; ring

/-- Weighted Cauchy–Schwarz: `Σ ‖ε_j‖ ≤ √((Σ s_j) (Σ ‖ε_j‖²/s_j))` for
positive weights `s_j`. -/
theorem sum_norm_le_sqrt_weighted (M : ℕ) (s : ℕ → ℝ) (ε : ℕ → V)
    (hs : ∀ j < M, 0 < s j) :
    ∑ j ∈ range M, ‖ε j‖ ≤
      Real.sqrt ((∑ j ∈ range M, s j) * ∑ j ∈ range M, ‖ε j‖ ^ 2 / s j) := by
  have hsq : (∑ j ∈ range M, ‖ε j‖) ^ 2 ≤
      (∑ j ∈ range M, s j) * ∑ j ∈ range M, ‖ε j‖ ^ 2 / s j := by
    have h := sum_mul_sq_le_sq_mul_sq (range M) (fun j => Real.sqrt (s j))
      (fun j => ‖ε j‖ / Real.sqrt (s j))
    have e1 : ∀ j ∈ range M, Real.sqrt (s j) * (‖ε j‖ / Real.sqrt (s j)) = ‖ε j‖ := by
      intro j hj
      have := Real.sqrt_pos.mpr (hs j (mem_range.mp hj))
      field_simp
    have e2 : ∀ j ∈ range M, Real.sqrt (s j) ^ 2 = s j := fun j hj =>
      Real.sq_sqrt (hs j (mem_range.mp hj)).le
    have e3 : ∀ j ∈ range M, (‖ε j‖ / Real.sqrt (s j)) ^ 2 = ‖ε j‖ ^ 2 / s j := by
      intro j hj
      rw [div_pow, Real.sq_sqrt (hs j (mem_range.mp hj)).le]
    rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at h
    exact h
  have h0 : 0 ≤ ∑ j ∈ range M, ‖ε j‖ := sum_nonneg fun j _ => norm_nonneg _
  calc ∑ j ∈ range M, ‖ε j‖ = Real.sqrt ((∑ j ∈ range M, ‖ε j‖) ^ 2) :=
        (Real.sqrt_sq h0).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq

/-- `thm:main-discrete-curvature`: for the recorded midpoint propagation
`eq:main-discrete-curvature-update` with `K_j` skew, `(L_j+L_jᵀ)/2 ≼ a_j I`,
`‖T_j‖_op ≤ e^{d_j}`, `a_j, d_j ≥ 0`, `s_j > 0` and `s_j a_j/2 ≤ b < 1`,
each recorded linear step is uniquely solvable and the boxed bound
`eq:main-discrete-curvature-bound`
`max_j ‖Y_j‖ ≤ e^{D + A/(1-b)} (‖Y_0‖ + √(T 𝒟)/(1-b))` holds with the budgets
`eq:main-discrete-curvature-budgets`.  No restriction on `s_j ‖K_j‖_op` is
used. -/
theorem discrete_curvature_certificate [FiniteDimensional ℝ V] (M : ℕ) (s a d : ℕ → ℝ)
    (K L T : ℕ → V →L[ℝ] V) (Y ε : ℕ → V) (b : ℝ) (hb1 : b < 1)
    (hs : ∀ j < M, 0 < s j) (ha : ∀ j < M, 0 ≤ a j) (hd : ∀ j < M, 0 ≤ d j)
    (hK : ∀ j < M, ∀ x y, ⟪K j x, y⟫_ℝ = -⟪x, K j y⟫_ℝ)
    (hL : ∀ j < M, ∀ x, ⟪x, L j x⟫_ℝ ≤ a j * ‖x‖ ^ 2)
    (hT : ∀ j < M, ‖T j‖ ≤ Real.exp (d j))
    (hb : ∀ j < M, s j * a j / 2 ≤ b)
    (hupd : ∀ j < M, Y (j + 1) - T j (Y j) =
      s j • (K j + L j) ((1 / 2 : ℝ) • (Y (j + 1) + T j (Y j))) + ε j) :
    (∀ j < M, ∀ r : V, ∃! w : V, w - (s j / 2) • (K j + L j) w = r) ∧
    ∀ j ≤ M, ‖Y j‖ ≤
      Real.exp (∑ i ∈ range M, d i + (∑ i ∈ range M, s i * a i) / (1 - b)) *
        (‖Y 0‖ + Real.sqrt ((∑ i ∈ range M, s i) * ∑ i ∈ range M, ‖ε i‖ ^ 2 / s i) /
          (1 - b)) := by
  have hb0 : 0 < 1 - b := by linarith
  -- skew symmetry gives `⟪x, K x⟫ = 0`
  have hK0 : ∀ j < M, ∀ x, ⟪x, K j x⟫_ℝ = 0 := by
    intro j hj x
    have h := hK j hj x x
    rw [real_inner_comm] at h
    linarith
  refine ⟨?_, ?_⟩
  · intro j hj r
    exact (implicit_step_bijective (hK0 j hj) (hL j hj) (hs j hj).le
      (lt_of_le_of_lt (hb j hj) hb1)).existsUnique r
  -- growth exponents and forcing terms
  set e : ℕ → ℝ := fun i => d i + s i * a i / (1 - b) with he
  set β : ℕ → ℝ := fun k => ‖ε k‖ / (1 - b) with hβ
  have he0 : ∀ i < M, 0 ≤ e i := by
    intro i hi
    simp only [he]
    have := hd i hi
    have := mul_nonneg (hs i hi).le (ha i hi)
    positivity
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by simp only [hβ]; positivity
  -- the inductive bound with the running exponent
  have hind : ∀ n, n ≤ M →
      ‖Y n‖ ≤ Real.exp (∑ i ∈ range n, e i) * (‖Y 0‖ + ∑ k ∈ range n, β k) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hnM : n < M := hn
      have ih' := ih hnM.le
      have hstep := discrete_step_bound (hK0 n hnM) (hL n hnM) (hs n hnM).le (ha n hnM)
        (hT n hnM) (hb n hnM) hb1 (hupd n hnM)
      have hE : Real.exp (∑ i ∈ range (n + 1), e i) =
          Real.exp (∑ i ∈ range n, e i) * Real.exp (e n) := by
        rw [sum_range_succ, Real.exp_add]
      have hE1 : 1 ≤ Real.exp (∑ i ∈ range (n + 1), e i) := by
        rw [Real.one_le_exp_iff]
        exact sum_nonneg fun i hi => he0 i (lt_of_lt_of_le (mem_range.mp hi) hn)
      have hEn : 0 < Real.exp (e n) := Real.exp_pos _
      have hYs : 0 ≤ ‖Y 0‖ + ∑ k ∈ range n, β k :=
        add_nonneg (norm_nonneg _) (sum_nonneg fun k _ => hβ0 k)
      rw [hE, sum_range_succ]
      calc ‖Y (n + 1)‖ ≤ Real.exp (e n) * ‖Y n‖ + β n := hstep
        _ ≤ Real.exp (e n) * (Real.exp (∑ i ∈ range n, e i) * (‖Y 0‖ + ∑ k ∈ range n, β k))
            + Real.exp (∑ i ∈ range n, e i) * Real.exp (e n) * β n := by
            gcongr
            rw [← hE]
            exact le_mul_of_one_le_left (hβ0 n) hE1
        _ = Real.exp (∑ i ∈ range n, e i) * Real.exp (e n) *
              (‖Y 0‖ + (∑ k ∈ range n, β k + β n)) := by ring
  intro j hj
  have h1 := hind j hj
  -- monotonicity of the running exponent and of the forcing sum
  have hsub : range j ⊆ range M := range_subset_range.mpr hj
  have hE_le : Real.exp (∑ i ∈ range j, e i) ≤ Real.exp (∑ i ∈ range M, e i) := by
    apply Real.exp_le_exp.mpr
    exact sum_le_sum_of_subset_of_nonneg hsub fun i hi _ => he0 i (mem_range.mp hi)
  have hβ_le : ∑ k ∈ range j, β k ≤ ∑ k ∈ range M, β k :=
    sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hβ0 k
  have hβsum : ∑ k ∈ range M, β k ≤
      Real.sqrt ((∑ i ∈ range M, s i) * ∑ i ∈ range M, ‖ε i‖ ^ 2 / s i) / (1 - b) := by
    simp only [hβ]
    rw [← sum_div]
    exact div_le_div_of_nonneg_right (sum_norm_le_sqrt_weighted M s ε hs) hb0.le
  have hEeq : Real.exp (∑ i ∈ range M, e i) =
      Real.exp (∑ i ∈ range M, d i + (∑ i ∈ range M, s i * a i) / (1 - b)) := by
    congr 1
    simp only [he]
    rw [sum_add_distrib, sum_div]
  have hYs : 0 ≤ ‖Y 0‖ + ∑ k ∈ range j, β k :=
    add_nonneg (norm_nonneg _) (sum_nonneg fun k _ => hβ0 k)
  calc ‖Y j‖ ≤ Real.exp (∑ i ∈ range j, e i) * (‖Y 0‖ + ∑ k ∈ range j, β k) := h1
    _ ≤ Real.exp (∑ i ∈ range M, e i) * (‖Y 0‖ + ∑ k ∈ range M, β k) := by
        gcongr
    _ ≤ Real.exp (∑ i ∈ range M, e i) *
        (‖Y 0‖ + Real.sqrt ((∑ i ∈ range M, s i) * ∑ i ∈ range M, ‖ε i‖ ^ 2 / s i) /
          (1 - b)) := by
        gcongr
    _ = _ := by rw [hEeq]

end RenewalGeometry
