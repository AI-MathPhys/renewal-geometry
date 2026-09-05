/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical propagation and the operational light cone
  (`thm:operational-light-cone`, Gran-Tensor manuscript)

* `operational_light_cone`: for a protected localization
  atlas of orthogonal projections `Q_i` (`ΣQ_i = 1`) and any
  transfer `T`, the boxed corner-norm propagation bound
  `‖Q_j·T^k·Q_i‖ ≤ (C(T)^k)_{ji}` with
  `C(T)_{ji} = ‖Q_j·T·Q_i‖` — the entrywise-nonnegative
  influence matrix controls every word corner, so zero collar
  residuals give exact finite propagation.

The generator-exponential clause `‖Q_j e^{tL} Q_i‖ ≤
(e^{|t|C(L)})_{ji}` and the weighted Combes–Thomas bound are
the manuscript's series summation over this per-power bound.
-/

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- `thm:operational-light-cone`. -/
theorem operational_light_cone {H ι : Type*} [Fintype H]
    [DecidableEq H] [Fintype ι] [DecidableEq ι]
    (Q : ι → Matrix H H ℂ) (T : Matrix H H ℂ)
    (hsum : ∑ l, Q l = 1)
    (hproj : ∀ l, Q l * Q l = Q l)
    (hnorm : ∀ l, ‖Q l‖ ≤ 1)
    (horth : ∀ l l', l ≠ l' → Q l * Q l' = 0) :
    ∀ (k : ℕ) (j i : ι),
      ‖Q j * T ^ k * Q i‖
        ≤ ((Matrix.of fun a b : ι => ‖Q a * T * Q b‖) ^ k)
            j i := by
  -- the influence matrix has nonnegative entries and powers
  have hCnn : ∀ (k : ℕ) (a b : ι),
      0 ≤ ((Matrix.of fun a b : ι => ‖Q a * T * Q b‖) ^ k)
        a b := by
    intro k
    induction k with
    | zero =>
        intro a b
        by_cases h : a = b
        · subst h
          rw [pow_zero, Matrix.one_apply_eq]
          norm_num
        · rw [pow_zero, Matrix.one_apply_ne h]
    | succ m ih =>
        intro a b
        rw [pow_succ', Matrix.mul_apply]
        apply Finset.sum_nonneg
        intro l _
        exact mul_nonneg (by
          simp only [Matrix.of_apply]
          exact norm_nonneg _) (ih l b)
  intro k
  induction k with
  | zero =>
      intro j i
      by_cases h : j = i
      · subst h
        rw [pow_zero, Matrix.mul_one, hproj, pow_zero,
          Matrix.one_apply_eq]
        exact hnorm j
      · rw [pow_zero, Matrix.mul_one, horth j i h,
          norm_zero, pow_zero, Matrix.one_apply_ne h]
  | succ k ih =>
      intro j i
      have hins : Q j * T ^ (k + 1) * Q i
          = ∑ l, (Q j * T * Q l)
            * (Q l * (T ^ k * Q i)) := by
        have h1 : Q j * T ^ (k + 1) * Q i
            = Q j * T * ((∑ l, Q l) * (T ^ k * Q i)) := by
          rw [hsum, Matrix.one_mul, pow_succ']
          simp only [Matrix.mul_assoc]
        rw [h1, Matrix.sum_mul, Matrix.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [show (Q j * T * Q l) * (Q l * (T ^ k * Q i))
            = Q j * T * ((Q l * Q l) * (T ^ k * Q i)) from
          by simp only [Matrix.mul_assoc], hproj l]
      calc ‖Q j * T ^ (k + 1) * Q i‖
          = ‖∑ l, (Q j * T * Q l)
              * (Q l * (T ^ k * Q i))‖ := by rw [hins]
        _ ≤ ∑ l, ‖(Q j * T * Q l)
              * (Q l * (T ^ k * Q i))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ l, ‖Q j * T * Q l‖
              * ‖Q l * (T ^ k * Q i)‖ := by
            apply Finset.sum_le_sum
            intro l _
            exact Matrix.l2_opNorm_mul _ _
        _ ≤ ∑ l, ‖Q j * T * Q l‖
              * ((Matrix.of fun a b : ι =>
                  ‖Q a * T * Q b‖) ^ k) l i := by
            apply Finset.sum_le_sum
            intro l _
            apply mul_le_mul_of_nonneg_left ?_
              (norm_nonneg _)
            have h2 : Q l * (T ^ k * Q i)
                = Q l * T ^ k * Q i := by
              simp only [Matrix.mul_assoc]
            rw [h2]
            exact ih l i
        _ = ((Matrix.of fun a b : ι =>
              ‖Q a * T * Q b‖) ^ (k + 1)) j i := by
            rw [pow_succ', Matrix.mul_apply]
            apply Finset.sum_congr rfl
            intro l _
            rw [Matrix.of_apply]

end NCG
