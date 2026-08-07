/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform KMS birth–death tail bound
  (`thm:YM-birth-death-tail-master`, flagship manuscript)

* `schur_test`: the weighted Schur test — for a symmetric
  entrywise-nonnegative kernel `K` with positive weights `w` and
  weighted row sums `Σ_j K_ij w_j ≤ c·w_i`, the quadratic form
  satisfies `x·Kx ≤ c‖x‖²` — the Collatz–Wielandt upper bound
  used with the birth–death weight `w_j = (p/q)^{j/2}`;
* `birth_death_row_identity`: the interior-row computation — for
  `p, q > 0` the tridiagonal row quotient is exactly
  `r + √(pq)(√(p/q) + √(q/p)) = r + p + q = 1 - κ`;
* `birth_death_margin`: the second boxed estimate —
  `r + 2√(pq) = 1 - κ - (√q - √p)²`, so the return-biased row-sum
  bound improves the gap by the bias margin `(√q - √p)²`.

Rendering disclosed: the reduction `‖D_N‖ ≤ ‖K_N‖` (positivity
of the operator tail and the block bounds
`‖Π_iD_NΠ_j‖ ≤ (K_N)_{ij}` turning the operator quadratic form
into the scalar kernel form) and the boundary-row inequalities of
the finite cutoff are the manuscript's remaining bookkeeping on
top of the Schur test and row identities proved here; both
estimates are independent of the cutoff `N` and all shell
multiplicities because the weight and row identities are.
-/

open Finset

namespace NCG

/-- Weighted Schur test: symmetric nonnegative kernel, positive
weights, weighted row sums `≤ c·w` ⇒ quadratic form `≤ c‖x‖²`. -/
theorem schur_test {n : Type*} [Fintype n]
    (K : Matrix n n ℝ) (w : n → ℝ) (c : ℝ)
    (hsym : ∀ i j, K i j = K j i) (hnn : ∀ i j, 0 ≤ K i j)
    (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, K i j * w j ≤ c * w i) (x : n → ℝ) :
    x ⬝ᵥ K.mulVec x ≤ c * (x ⬝ᵥ x) := by
  have hterm : ∀ i j, x i * (K i j * x j)
      ≤ K i j * (w j / w i * x i ^ 2
        + w i / w j * x j ^ 2) / 2 := by
    intro i j
    have hwi := hw i
    have hwj := hw j
    have hK := hnn i j
    have hkey : 2 * (w i * w j) * (x i * x j)
        ≤ w j ^ 2 * x i ^ 2 + w i ^ 2 * x j ^ 2 := by
      nlinarith [sq_nonneg (w j * x i - w i * x j)]
    have hgoal : 2 * (x i * x j)
        ≤ w j / w i * x i ^ 2 + w i / w j * x j ^ 2 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
        div_add_div _ _ hwi.ne' hwj.ne',
        le_div_iff₀ (by positivity)]
      nlinarith [hkey]
    calc x i * (K i j * x j) = K i j * (x i * x j) := by ring
      _ ≤ K i j * ((w j / w i * x i ^ 2
          + w i / w j * x j ^ 2) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          linarith
      _ = K i j * (w j / w i * x i ^ 2
          + w i / w j * x j ^ 2) / 2 := by ring
  have hexpand : x ⬝ᵥ K.mulVec x
      = ∑ i, ∑ j, x i * (K i j * x j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hexpand]
  have hsum1 : ∑ i, ∑ j, x i * (K i j * x j)
      ≤ ∑ i, ∑ j, K i j * (w j / w i * x i ^ 2
        + w i / w j * x j ^ 2) / 2 :=
    Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hterm i j
  refine le_trans hsum1 ?_
  have hsplit : ∑ i, ∑ j, K i j * (w j / w i * x i ^ 2
        + w i / w j * x j ^ 2) / 2
      = ∑ i, x i ^ 2 / w i * ∑ j, K i j * w j := by
    have hdecomp : ∑ i, ∑ j, K i j * (w j / w i * x i ^ 2
          + w i / w j * x j ^ 2) / 2
        = (∑ i, ∑ j, K i j * (w j / w i * x i ^ 2)) / 2
          + (∑ i, ∑ j, K i j * (w i / w j * x j ^ 2)) / 2 := by
      calc ∑ i, ∑ j, K i j * (w j / w i * x i ^ 2
            + w i / w j * x j ^ 2) / 2
          = ∑ i, ∑ j, (K i j * (w j / w i * x i ^ 2) / 2
            + K i j * (w i / w j * x j ^ 2) / 2) := by
            refine Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => by ring
        _ = (∑ i, ∑ j, K i j * (w j / w i * x i ^ 2)) / 2
            + (∑ i, ∑ j, K i j * (w i / w j * x j ^ 2)) / 2 := by
            simp only [Finset.sum_div,
              ← Finset.sum_add_distrib]
    have hswap : ∑ i, ∑ j, K i j * (w i / w j * x j ^ 2)
        = ∑ i, ∑ j, K i j * (w j / w i * x i ^ 2) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => by rw [hsym]
    rw [hdecomp, hswap]
    have hhalf : ∀ X : ℝ, X / 2 + X / 2 = X := fun X => by
      ring
    rw [hhalf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [hsplit]
  have hfinal : ∑ i, x i ^ 2 / w i * ∑ j, K i j * w j
      ≤ ∑ i, x i ^ 2 / w i * (c * w i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_left (hrow i)
      (div_nonneg (sq_nonneg _) (hw i).le)
  refine le_trans hfinal (le_of_eq ?_)
  calc ∑ i, x i ^ 2 / w i * (c * w i)
      = ∑ i, c * (x i * x i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hwi := (hw i).ne'
        field_simp
    _ = c * (x ⬝ᵥ x) := by
        rw [dotProduct, Finset.mul_sum]

/-- Interior-row identity: for `p, q > 0`,
`√(pq)(√(p/q) + √(q/p)) = p + q`, so the weighted row quotient is
`r + p + q = 1 - κ`. -/
theorem birth_death_row_identity (p q r κ : ℝ) (hp : 0 < p)
    (hq : 0 < q) (hsum : p + q + r + κ = 1) :
    Real.sqrt (p * q) * (Real.sqrt (p / q) + Real.sqrt (q / p))
      = p + q
    ∧ r + (p + q) = 1 - κ := by
  constructor
  · have h1 : Real.sqrt (p * q) * Real.sqrt (p / q) = p := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show p * q * (p / q) = p ^ 2 by field_simp]
      exact Real.sqrt_sq hp.le
    have h2 : Real.sqrt (p * q) * Real.sqrt (q / p) = q := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show p * q * (q / p) = q ^ 2 by field_simp]
      exact Real.sqrt_sq hq.le
    rw [mul_add, h1, h2]
  · linarith

/-- Second boxed estimate: the return-biased margin —
`r + 2√(pq) = 1 - κ - (√q - √p)²`. -/
theorem birth_death_margin (p q r κ : ℝ) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hsum : p + q + r + κ = 1) :
    r + 2 * Real.sqrt (p * q)
      = 1 - κ - (Real.sqrt q - Real.sqrt p) ^ 2 := by
  have hpq : Real.sqrt (p * q)
      = Real.sqrt p * Real.sqrt q := Real.sqrt_mul hp q
  have hsp : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  rw [hpq]
  nlinarith [hsp, hsq]

end NCG
