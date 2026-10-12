/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exponential of an idempotent-split element

Split out of `MathPhys.MarkovChains.DiscreteClock`:

* `exp_one_sub_idem`: for an idempotent `P` in a real Banach algebra,
  `exp(c(1-P)) = 1 + (e^c - 1)(1-P)`.
-/

open Matrix NormedSpace

namespace MathPhys

/-- Exponential of an idempotent-split generator. -/
theorem exp_one_sub_idem {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (P : A) (hP : P * P = P) (c : ℝ) :
    exp (c • ((1 : A) - P))
      = 1 + (Real.exp c - 1) • ((1 : A) - P) := by
  have hQ2 : ((1 : A) - P) * ((1 : A) - P) = 1 - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
    abel
  have hQ : ∀ n : ℕ, 1 ≤ n →
      ((1 : A) - P) ^ n = 1 - P := by
    intro n hn
    induction n with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp
      · rw [pow_succ, ih hk, hQ2]
  have hs : Summable fun n : ℕ =>
      ((n.factorial : ℝ))⁻¹ • (c • ((1 : A) - P)) ^ n :=
    expSeries_summable' (𝕂 := ℝ) _
  rw [exp_eq_tsum (𝕂 := ℝ)]
  beta_reduce
  rw [hs.tsum_eq_zero_add]
  have htail : ∀ n : ℕ,
      (((n + 1).factorial : ℝ))⁻¹
        • (c • ((1 : A) - P)) ^ (n + 1)
      = (c ^ (n + 1) / ((n + 1).factorial : ℝ))
        • ((1 : A) - P) := by
    intro n
    rw [smul_pow, hQ (n + 1) (by omega), smul_smul]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have hexpc : Real.exp c
      = ∑' n : ℕ, c ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, exp_eq_tsum (𝕂 := ℝ)]
    exact tsum_congr fun n => by
      rw [smul_eq_mul, div_eq_mul_inv]
      ring
  have htailval : ∑' n : ℕ,
      c ^ (n + 1) / (((n + 1).factorial : ℝ))
      = Real.exp c - 1 := by
    have h :=
      (Real.summable_pow_div_factorial c).tsum_eq_zero_add
    rw [← hexpc] at h
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one]
      at h
    have h1 : (1 : ℝ) / 1 = 1 := by norm_num
    rw [h1] at h
    linarith
  have hshift : Summable fun n : ℕ =>
      c ^ (n + 1) / (((n + 1).factorial : ℝ)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_pow_div_factorial c)
    simpa using h
  rw [tsum_congr htail, hshift.tsum_smul_const, htailval]
  simp

end MathPhys
