/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Markov screen area law
  (`prop:screen-area`, arithmetic manuscript)

For a stationary finite-state screen chain with stationary law `π`
and transition matrix `P`:

* the joint Shannon entropy of the chain with `N` transitions
  satisfies the boxed chain rule
  `H(X₁,…,X_{N+1}) = H(π) + N·h(P)` with entropy rate
  `h(P) = -Σ_{ij} π_i P_{ij} log P_{ij}` (`screen_chain_rule`;
  the manuscript's `N` cells carry `N-1` transitions — indexing
  disclosed);
* the boxed area law: with one cell per area `a₀` and
  `|N·a₀ - Area| ≤ a₀`, the entropy deviates from
  `(h(P)/a₀)·Area` by at most `|H(π)| + |h(P)|` — the `O(1)`
  constant in explicit form (`screen_area_law`).

The joint law is the explicit product `π(x₀)·Π P(x_k, x_{k+1})`
(the Markov property is its definition here, disclosed); zero
probabilities are handled by the `log 0 = 0` convention, under
which the chain rule is exact.
-/

open Finset

namespace NCG

variable {s : Type*} [Fintype s]

/-- Shannon entropy of a finite law. -/
noncomputable def entropyOf {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    ℝ :=
  -∑ i, p i * Real.log (p i)

/-- Entropy rate of a stationary chain. -/
noncomputable def entropyRate (π : s → ℝ) (P : s → s → ℝ) : ℝ :=
  -∑ i, ∑ j, π i * P i j * Real.log (P i j)

/-- Joint law of the screen chain with `N` transitions. -/
noncomputable def chainLaw (π : s → ℝ) (P : s → s → ℝ) :
    (N : ℕ) → (Fin (N + 1) → s) → ℝ
  | 0, x => π (x 0)
  | N + 1, x =>
      chainLaw π P N (fun k => x k.castSucc)
        * P (x (Fin.castSucc (Fin.last N))) (x (Fin.last (N + 1)))

omit [Fintype s] in
/-- Appending one cell multiplies by one transition weight. -/
lemma chainLaw_snoc (π : s → ℝ) (P : s → s → ℝ) (N : ℕ)
    (x : Fin (N + 1) → s) (y : s) :
    chainLaw π P (N + 1) (Fin.snoc x y)
      = chainLaw π P N x * P (x (Fin.last N)) y := by
  simp only [chainLaw, Fin.snoc_castSucc, Fin.snoc_last]

/-- Splitting a chain sum at the final cell. -/
lemma sum_snoc_split (N : ℕ) (F : (Fin (N + 2) → s) → ℝ) :
    ∑ x : Fin (N + 2) → s, F x
      = ∑ y : s, ∑ x : Fin (N + 1) → s, F (Fin.snoc x y) := by
  rw [← (Fin.snocEquiv (fun _ => s)).sum_comp F,
    Fintype.sum_prod_type]
  rfl

omit [Fintype s] in
/-- The chain law is nonnegative. -/
lemma chainLaw_nonneg (π : s → ℝ) (P : s → s → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hP0 : ∀ i j, 0 ≤ P i j) :
    ∀ (N : ℕ) (x : Fin (N + 1) → s), 0 ≤ chainLaw π P N x := by
  intro N
  induction N with
  | zero => intro x; exact hπ0 _
  | succ N ih => intro x; exact mul_nonneg (ih _) (hP0 _ _)

/-- The final-cell marginal of the stationary chain is `π`. -/
lemma chainLaw_last_marginal (π : s → ℝ) (P : s → s → ℝ)
    (hstat : ∀ j, ∑ i, π i * P i j = π j) (N : ℕ) (f : s → ℝ) :
    ∑ x : Fin (N + 1) → s,
        chainLaw π P N x * f (x (Fin.last N))
      = ∑ i, π i * f i := by
  induction N generalizing f with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) s).symm.sum_comp
      (fun x : Fin 1 → s =>
        chainLaw π P 0 x * f (x (Fin.last 0)))]
    rfl
  | succ N ih =>
    rw [sum_snoc_split N (fun x =>
      chainLaw π P (N + 1) x * f (x (Fin.last (N + 1))))]
    calc ∑ y : s, ∑ x : Fin (N + 1) → s,
          chainLaw π P (N + 1) (Fin.snoc x y)
            * f ((Fin.snoc x y : Fin (N + 2) → s)
                (Fin.last (N + 1)))
        = ∑ y : s, ∑ x : Fin (N + 1) → s,
            chainLaw π P N x
              * (P (x (Fin.last N)) y * f y) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [chainLaw_snoc, Fin.snoc_last]
          ring
      _ = ∑ x : Fin (N + 1) → s, chainLaw π P N x
            * (∑ y, P (x (Fin.last N)) y * f y) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, π i * (∑ y, P i y * f y) :=
          ih (fun i => ∑ y, P i y * f y)
      _ = ∑ y, ∑ i, π i * P i y * f y := by
          rw [← Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = ∑ i, π i * f i := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_mul, hstat y]

/-- The `log 0 = 0` convention makes the product log split
exact. -/
lemma mul_log_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b * Real.log (a * b)
      = a * b * Real.log a + a * b * Real.log b := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]
    simp
  rcases eq_or_lt_of_le hb with h2 | h2
  · rw [← h2]
    simp
  rw [Real.log_mul h.ne' h2.ne']
  ring

/-- One-step entropy recursion. -/
lemma entropy_chain_step (π : s → ℝ) (P : s → s → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hP0 : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j) (N : ℕ) :
    entropyOf (chainLaw π P (N + 1))
      = entropyOf (chainLaw π P N) + entropyRate π P := by
  rw [entropyOf, sum_snoc_split N (fun x =>
    chainLaw π P (N + 1) x * Real.log (chainLaw π P (N + 1) x))]
  have hsplit : ∑ y : s, ∑ x : Fin (N + 1) → s,
      chainLaw π P (N + 1) (Fin.snoc x y)
        * Real.log (chainLaw π P (N + 1) (Fin.snoc x y))
      = (∑ y : s, ∑ x : Fin (N + 1) → s,
          chainLaw π P N x * P (x (Fin.last N)) y
            * Real.log (chainLaw π P N x))
        + ∑ y : s, ∑ x : Fin (N + 1) → s,
            chainLaw π P N x * P (x (Fin.last N)) y
              * Real.log (P (x (Fin.last N)) y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [chainLaw_snoc]
    exact mul_log_mul _ _ (chainLaw_nonneg π P hπ0 hP0 N x)
      (hP0 _ _)
  rw [hsplit]
  have h1 : ∑ y : s, ∑ x : Fin (N + 1) → s,
      chainLaw π P N x * P (x (Fin.last N)) y
        * Real.log (chainLaw π P N x)
      = ∑ x : Fin (N + 1) → s,
          chainLaw π P N x * Real.log (chainLaw π P N x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    calc ∑ y, chainLaw π P N x * P (x (Fin.last N)) y
          * Real.log (chainLaw π P N x)
        = (chainLaw π P N x * Real.log (chainLaw π P N x))
            * ∑ y, P (x (Fin.last N)) y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = chainLaw π P N x * Real.log (chainLaw π P N x) := by
          rw [hrow, mul_one]
  have h2 : ∑ y : s, ∑ x : Fin (N + 1) → s,
      chainLaw π P N x * P (x (Fin.last N)) y
        * Real.log (P (x (Fin.last N)) y)
      = ∑ i, ∑ j, π i * P i j * Real.log (P i j) := by
    rw [Finset.sum_comm]
    calc ∑ x : Fin (N + 1) → s, ∑ y : s,
          chainLaw π P N x * P (x (Fin.last N)) y
            * Real.log (P (x (Fin.last N)) y)
        = ∑ x : Fin (N + 1) → s, chainLaw π P N x
            * (∑ y, P (x (Fin.last N)) y
                * Real.log (P (x (Fin.last N)) y)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = ∑ i, π i * (∑ y, P i y * Real.log (P i y)) :=
          chainLaw_last_marginal π P hstat N
            (fun i => ∑ y, P i y * Real.log (P i y))
      _ = ∑ i, ∑ j, π i * P i j * Real.log (P i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [h1, h2, entropyOf, entropyRate]
  ring

/-- `prop:screen-area`, boxed chain rule:
`H(X₁,…,X_{N+1}) = H(π) + N·h(P)`. -/
theorem screen_chain_rule (π : s → ℝ) (P : s → s → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hP0 : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j) (N : ℕ) :
    entropyOf (chainLaw π P N)
      = entropyOf π + N * entropyRate π P := by
  induction N with
  | zero =>
    rw [Nat.cast_zero, zero_mul, add_zero, entropyOf, entropyOf,
      ← (Equiv.funUnique (Fin 1) s).symm.sum_comp
        (fun x : Fin 1 → s =>
          chainLaw π P 0 x * Real.log (chainLaw π P 0 x))]
    rfl
  | succ N ih =>
    rw [entropy_chain_step π P hπ0 hP0 hrow hstat N, ih,
      Nat.cast_succ]
    ring

/-- `prop:screen-area`, boxed area law: with one cell per area
`a₀`, the screen entropy is `(h(P)/a₀)·Area + O(1)` with the
explicit constant `|H(π)| + |h(P)|`. -/
theorem screen_area_law (π : s → ℝ) (P : s → s → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hP0 : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (a0 Area : ℝ) (ha0 : 0 < a0) (N : ℕ)
    (hN : |N * a0 - Area| ≤ a0) :
    |entropyOf (chainLaw π P N)
        - entropyRate π P / a0 * Area|
      ≤ |entropyOf π| + |entropyRate π P| := by
  rw [screen_chain_rule π P hπ0 hP0 hrow hstat N]
  have h1 : entropyOf π + N * entropyRate π P
      - entropyRate π P / a0 * Area
      = entropyOf π
        + entropyRate π P / a0 * (N * a0 - Area) := by
    field_simp
    ring
  rw [h1]
  refine le_trans (abs_add_le _ _) ?_
  have h2 : |entropyRate π P / a0 * (N * a0 - Area)|
      ≤ |entropyRate π P| := by
    rw [abs_mul, abs_div, abs_of_pos ha0]
    calc |entropyRate π P| / a0 * |N * a0 - Area|
        ≤ |entropyRate π P| / a0 * a0 := by
          exact mul_le_mul_of_nonneg_left hN (by positivity)
      _ = |entropyRate π P| := by
          field_simp
  linarith

end NCG
