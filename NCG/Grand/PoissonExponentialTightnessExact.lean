/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteMetzlerUniformizationExact

/-!
# Poisson exponential moments and exponential tightness

This file proves the scalar Poisson estimate used after finite-state
uniformization.  It is deliberately stated directly in terms of the Poisson
factorial series, so it can be applied both to an actual Poisson law and to
the uniformized semigroup expansion.
-/

open scoped BigOperators

noncomputable section

namespace NCG.PoissonExponentialTightness

/-- The upper tail of the Poisson factorial series. -/
def poissonUpperTail (r : ℝ) (N : ℕ) : ℝ :=
  ∑' n : ℕ, if N ≤ n then
    Real.exp (-r) * r ^ n / n.factorial else 0

/-- Exact exponential moment of the Poisson factorial series. -/
theorem poisson_exponential_moment (r theta : ℝ) :
    (∑' n : ℕ, Real.exp (-r) * r ^ n / n.factorial *
      Real.exp (theta * n)) =
      Real.exp (r * (Real.exp theta - 1)) := by
  calc
    (∑' n : ℕ, Real.exp (-r) * r ^ n / n.factorial *
        Real.exp (theta * n)) =
      Real.exp (-r) *
        (∑' n : ℕ, (r * Real.exp theta) ^ n / n.factorial) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          rw [mul_pow, ← Real.exp_nat_mul]
          ring
    _ = Real.exp (-r) * Real.exp (r * Real.exp theta) := by
          congr 1
          rw [Real.exp_eq_exp_ℝ]
          calc
            (∑' n : ℕ, (r * NormedSpace.exp theta) ^ n /
                n.factorial) =
              ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) *
                (r * NormedSpace.exp theta) ^ n := by
                  apply tsum_congr
                  intro n
                  ring
            _ = NormedSpace.exp (r * NormedSpace.exp theta) :=
              (congrFun (NormedSpace.exp_eq_tsum ℝ)
                (r * NormedSpace.exp theta)).symm
    _ = Real.exp (r * (Real.exp theta - 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring

theorem summable_poisson_upperTail_terms (r : ℝ) (N : ℕ) :
    Summable (fun n : ℕ => if N ≤ n then
      Real.exp (-r) * r ^ n / n.factorial else 0) := by
  have hbase : Summable (fun n : ℕ =>
      Real.exp (-r) * (r ^ n / n.factorial)) :=
    (Real.summable_pow_div_factorial r).mul_left _
  let s : Set ℕ := {n | N ≤ n}
  have hindicator :
      (fun n : ℕ => if N ≤ n then
        Real.exp (-r) * r ^ n / n.factorial else 0) =
      s.indicator (fun n : ℕ =>
        Real.exp (-r) * (r ^ n / n.factorial)) := by
    funext n
    by_cases hn : N ≤ n
    · simp only [s, Set.indicator, Set.mem_setOf_eq, hn, ↓reduceIte]
      ring
    · simp [s, Set.indicator, hn]
  rw [hindicator]
  exact hbase.indicator s

/-- Chernoff bound for the Poisson upper tail. -/
theorem poissonUpperTail_le_chernoff
    (r theta : ℝ) (N : ℕ) (hr : 0 ≤ r) (htheta : 0 ≤ theta) :
    poissonUpperTail r N ≤
      Real.exp (-(theta * N) + r * (Real.exp theta - 1)) := by
  let lhs : ℕ → ℝ := fun n => if N ≤ n then
    Real.exp (-r) * r ^ n / n.factorial else 0
  let rhs : ℕ → ℝ := fun n =>
    Real.exp (-(theta * N)) *
      (Real.exp (-r) * r ^ n / n.factorial * Real.exp (theta * n))
  have hlhs : Summable lhs := by
    simpa [lhs] using summable_poisson_upperTail_terms r N
  have hmoment : Summable (fun n : ℕ =>
      Real.exp (-r) * r ^ n / n.factorial * Real.exp (theta * n)) := by
    have hbase := Real.summable_pow_div_factorial (r * Real.exp theta)
    have heq : (fun n : ℕ =>
        Real.exp (-r) * r ^ n / n.factorial * Real.exp (theta * n)) =
      (fun n : ℕ => Real.exp (-r) *
        ((r * Real.exp theta) ^ n / n.factorial)) := by
      funext n
      rw [mul_pow, ← Real.exp_nat_mul]
      ring
    rw [heq]
    exact hbase.mul_left _
  have hrhs : Summable rhs := by
    dsimp only [rhs]
    exact hmoment.mul_left _
  have hpoint : ∀ n, lhs n ≤ rhs n := by
    intro n
    dsimp only [lhs, rhs]
    by_cases hn : N ≤ n
    · rw [if_pos hn]
      have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnon : 0 ≤ theta * ((n : ℝ) - (N : ℝ)) :=
        mul_nonneg htheta (sub_nonneg.mpr hcast)
      have hexp : 1 ≤ Real.exp (theta * ((n : ℝ) - (N : ℝ))) :=
        Real.one_le_exp hnon
      have hcoeff : 0 ≤ Real.exp (-r) * r ^ n / n.factorial := by
        positivity
      have hfactor :
          Real.exp (-(theta * (N : ℝ))) * Real.exp (theta * (n : ℝ)) =
            Real.exp (theta * ((n : ℝ) - (N : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        Real.exp (-r) * r ^ n / n.factorial =
            (Real.exp (-r) * r ^ n / n.factorial) * 1 := by ring
        _ ≤ (Real.exp (-r) * r ^ n / n.factorial) *
            Real.exp (theta * ((n : ℝ) - (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp hcoeff
        _ = Real.exp (-(theta * N)) *
            (Real.exp (-r) * r ^ n / n.factorial *
              Real.exp (theta * n)) := by
          rw [← hfactor]
          ring
    · rw [if_neg hn]
      positivity
  have hsum := hlhs.tsum_le_tsum hpoint hrhs
  unfold poissonUpperTail
  change (∑' n, lhs n) ≤ _
  calc
    (∑' n, lhs n) ≤ ∑' n, rhs n := hsum
    _ = Real.exp (-(theta * N)) *
        (∑' n : ℕ, Real.exp (-r) * r ^ n / n.factorial *
          Real.exp (theta * n)) := tsum_mul_left
    _ = Real.exp (-(theta * N)) *
        Real.exp (r * (Real.exp theta - 1)) := by
          rw [poisson_exponential_moment]
    _ = Real.exp (-(theta * N) + r * (Real.exp theta - 1)) := by
          rw [Real.exp_add]

/-- Linear thresholds have exponentially small Poisson tails. -/
theorem poissonUpperTail_linear_exponential
    (lambda a theta : ℝ) (n : ℕ)
    (hlambda : 0 ≤ lambda) (ha : 0 ≤ a) (htheta : 0 ≤ theta) :
    poissonUpperTail (lambda * n) (Nat.ceil (a * n)) ≤
      Real.exp (-(theta * Nat.ceil (a * n)) +
        lambda * n * (Real.exp theta - 1)) := by
  exact poissonUpperTail_le_chernoff (lambda * n) theta
    (Nat.ceil (a * n)) (mul_nonneg hlambda (Nat.cast_nonneg n)) htheta

/-- Explicit exponential tightness at integer time horizons. For every target
decay rate `A`, the linear threshold shown below makes the Poisson upper tail
at most `exp (-A*n)` for every `n`. -/
theorem poissonUpperTail_exponentially_tight
    (lambda A : ℝ) (n : ℕ) (hlambda : 0 ≤ lambda) (hA : 0 ≤ A) :
    poissonUpperTail (lambda * n)
        (Nat.ceil ((A + lambda * (Real.exp 1 - 1) + 1) * n)) ≤
      Real.exp (-(A * n)) := by
  let M : ℝ := A + lambda * (Real.exp 1 - 1) + 1
  have hexp1 : 0 ≤ Real.exp 1 - 1 := by
    linarith [Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)]
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hbound := poissonUpperTail_linear_exponential
    lambda M 1 n hlambda hM (by norm_num : (0 : ℝ) ≤ 1)
  have hceil : M * (n : ℝ) ≤
      (Nat.ceil (M * (n : ℝ)) : ℝ) := Nat.le_ceil _
  have hexponent :
      -((Nat.ceil (M * (n : ℝ)) : ℝ)) +
          lambda * (n : ℝ) * (Real.exp 1 - 1) ≤
        -(A * (n : ℝ)) := by
    dsimp only [M] at hceil ⊢
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  exact hbound.trans ((Real.exp_le_exp).2 (by
    simpa only [one_mul] using hexponent))

end NCG.PoissonExponentialTightness
