/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact difference and sum selectors
  (`thm:marginals`, `cor:twin-gold-port`, arithmetic monograph)

For finite windowed Dirichlet/port polynomials
`F(θ) = Σ_{m<X} a(m) e^{2πimθ}`:

* `selector_integral` — the phase integral
  `∫₀¹ e^{2πikθ} dθ = δ_{k,0}` for `k : ℤ`;
* `difference_selector` — the normal (difference) marginal:
  `∫₀¹ F_a(θ) conj(F_b(θ)) e^{-2πihθ} dθ
     = Σ_{m-n=h} a(m) conj(b(n))`;
* `sum_selector` — the anomalous (sum) marginal:
  `∫₀¹ F_a(θ) F_b(θ) e^{-2πiNθ} dθ = Σ_{m+n=N} a(m) b(n)`;
* `twin_port` / `goldbach_port` — the von Mangoldt specialization
  (`cor:twin-gold-port`): the twin-prime correlation
  `Σ_{n≤X-2} Λ(n+2)Λ(n)` and the Goldbach sum
  `Σ_{m+n=N} Λ(m)Λ(n)` are the `h = 2` difference and `N` sum
  projections of the same windowed tensor.

The weights `w_X(m) m^{-σ}` of the manuscript display are absorbed
into the coefficient sequences, which are arbitrary here.
-/

namespace NCG.AffineSelectors

open Complex Finset intervalIntegral

open scoped Real ArithmeticFunction

noncomputable section

/-- The windowed port polynomial `Σ_{m<X} a(m) e^{2πimθ}`. -/
def dirPoly (a : ℕ → ℂ) (X : ℕ) (θ : ℝ) : ℂ :=
  ∑ m ∈ Finset.range X, a m * Complex.exp (2 * π * Complex.I * m * θ)

/-- The exact phase selector: `∫₀¹ e^{2πikθ} dθ = δ_{k,0}`. -/
theorem selector_integral (k : ℤ) :
    (∫ θ in (0 : ℝ)..1, Complex.exp (2 * π * Complex.I * k * θ))
      = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    have hc : (2 * (π : ℂ) * Complex.I * k) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_)
        Complex.I_ne_zero) ?_
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hk
    rw [integral_exp_mul_complex hc]
    push_cast
    have h1 : (2 * (π : ℂ) * Complex.I * k * 1) = (k : ℂ) * (2 * π * Complex.I) := by
      ring
    have h0 : (2 * (π : ℂ) * Complex.I * k * 0) = 0 := by ring
    rw [h1, h0, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_zero,
      sub_self, zero_div]

private lemma exp_term_continuous (c : ℂ) :
    Continuous fun θ : ℝ => Complex.exp (c * θ) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- `thm:marginals` (normal block): the difference selector
`D_{ab}(h) = Σ_{m-n=h} a(m) conj(b(n))`. -/
theorem difference_selector (a b : ℕ → ℂ) (X : ℕ) (h : ℤ) :
    (∫ θ in (0 : ℝ)..1,
        dirPoly a X θ * (starRingEnd ℂ) (dirPoly b X θ)
          * Complex.exp (2 * π * Complex.I * (-h) * θ))
      = ∑ m ∈ Finset.range X, ∑ n ∈ Finset.range X,
          if (m : ℤ) - n = h then a m * (starRingEnd ℂ) (b n) else 0 := by
  have hpt : ∀ θ : ℝ,
      dirPoly a X θ * (starRingEnd ℂ) (dirPoly b X θ)
          * Complex.exp (2 * π * Complex.I * (-h) * θ)
        = ∑ m ∈ Finset.range X, ∑ n ∈ Finset.range X,
            (a m * (starRingEnd ℂ) (b n))
              * Complex.exp (2 * π * Complex.I * ((m : ℂ) - n - h) * θ) := by
    intro θ
    rw [dirPoly, dirPoly, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      Complex.conj_natCast]
    calc _ = a m * (starRingEnd ℂ) (b n)
        * (Complex.exp (2 * π * Complex.I * m * θ)
          * Complex.exp (2 * π * -Complex.I * n * θ)
          * Complex.exp (2 * π * Complex.I * -(h : ℂ) * θ)) := by ring
    _ = a m * (starRingEnd ℂ) (b n)
        * Complex.exp (2 * π * Complex.I * ((m : ℂ) - n - h) * θ) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring_nf
  rw [intervalIntegral.integral_congr fun θ _ => hpt θ]
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_finsetSum fun n _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have hcast : ((m : ℂ) - n - h) = (((m : ℤ) - n - h : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hcast, selector_integral ((m : ℤ) - n - h)]
  by_cases hmn : (m : ℤ) - n = h
  · rw [if_pos (by omega), if_pos hmn, mul_one]
  · rw [if_neg (by omega), if_neg hmn, mul_zero]

/-- `thm:marginals` (anomalous block): the sum selector
`H_{ab}(N) = Σ_{m+n=N} a(m) b(n)`. -/
theorem sum_selector (a b : ℕ → ℂ) (X : ℕ) (N : ℤ) :
    (∫ θ in (0 : ℝ)..1,
        dirPoly a X θ * dirPoly b X θ
          * Complex.exp (2 * π * Complex.I * (-N) * θ))
      = ∑ m ∈ Finset.range X, ∑ n ∈ Finset.range X,
          if (m : ℤ) + n = N then a m * b n else 0 := by
  have hpt : ∀ θ : ℝ,
      dirPoly a X θ * dirPoly b X θ
          * Complex.exp (2 * π * Complex.I * (-N) * θ)
        = ∑ m ∈ Finset.range X, ∑ n ∈ Finset.range X,
            (a m * b n)
              * Complex.exp (2 * π * Complex.I * ((m : ℂ) + n - N) * θ) := by
    intro θ
    rw [dirPoly, dirPoly, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    calc _ = a m * b n
        * (Complex.exp (2 * π * Complex.I * m * θ)
          * Complex.exp (2 * π * Complex.I * n * θ)
          * Complex.exp (2 * π * Complex.I * -(N : ℂ) * θ)) := by ring
    _ = a m * b n
        * Complex.exp (2 * π * Complex.I * ((m : ℂ) + n - N) * θ) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring_nf
  rw [intervalIntegral.integral_congr fun θ _ => hpt θ]
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_finsetSum fun n _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have hcast : ((m : ℂ) + n - N) = (((m : ℤ) + n - N : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hcast, selector_integral ((m : ℤ) + n - N)]
  by_cases hmn : (m : ℤ) + n = N
  · rw [if_pos (by omega), if_pos hmn, mul_one]
  · rw [if_neg (by omega), if_neg hmn, mul_zero]

/-! ## The von Mangoldt twin and Goldbach ports -/

/-- The twin collapse: the `h`-difference double sum over the window
collapses to the single shifted correlation sum. -/
theorem twin_collapse (X : ℕ) :
    (∑ m ∈ Finset.range X, ∑ n ∈ Finset.range X,
        if (m : ℤ) - n = 2 then ((Λ m : ℂ)) * (starRingEnd ℂ) ((Λ n : ℂ))
          else 0)
      = ∑ n ∈ Finset.range (X - 2), (Λ (n + 2) : ℂ) * (Λ n : ℂ) := by
  rw [Finset.sum_comm]
  have hcol : ∀ n ∈ Finset.range X,
      (∑ m ∈ Finset.range X,
        if (m : ℤ) - n = 2 then ((Λ m : ℂ)) * (starRingEnd ℂ) ((Λ n : ℂ))
          else 0)
      = if n + 2 < X then (Λ (n + 2) : ℂ) * (Λ n : ℂ) else 0 := by
    intro n _
    have hite : ∀ m ∈ Finset.range X,
        (if (m : ℤ) - n = 2 then ((Λ m : ℂ)) * (starRingEnd ℂ) ((Λ n : ℂ))
          else 0)
        = if m = n + 2 then ((Λ m : ℂ)) * (starRingEnd ℂ) ((Λ n : ℂ))
          else 0 := by
      intro m _
      congr 1
      simp only [eq_iff_iff]
      omega
    rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq' (Finset.range X)]
    simp only [Finset.mem_range, Complex.conj_ofReal]
  rw [Finset.sum_congr rfl hcol, ← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- `cor:twin-gold-port` (Goldbach port): for `N < X` the anomalous
`N`-sum double sum is the full Goldbach correlation
`Σ_{m+n=N} Λ(m)Λ(n)`. -/
theorem goldbach_collapse (X N : ℕ) (hNX : N < X) :
    (∑ m ∈ Finset.range X, ∑ n ∈ Finset.range X,
        if (m : ℤ) + n = N then (Λ m : ℂ) * (Λ n : ℂ) else 0)
      = ∑ m ∈ Finset.range (N + 1), (Λ m : ℂ) * (Λ (N - m) : ℂ) := by
  have hcol : ∀ m ∈ Finset.range X,
      (∑ n ∈ Finset.range X,
        if (m : ℤ) + n = N then (Λ m : ℂ) * (Λ n : ℂ) else 0)
      = if m < N + 1 then (Λ m : ℂ) * (Λ (N - m) : ℂ) else 0 := by
    intro m _
    have hite : ∀ n ∈ Finset.range X,
        (if (m : ℤ) + n = N then (Λ m : ℂ) * (Λ n : ℂ) else 0)
        = if m ≤ N ∧ n = N - m then (Λ m : ℂ) * (Λ n : ℂ) else 0 := by
      intro n _
      congr 1
      simp only [eq_iff_iff]
      omega
    rw [Finset.sum_congr rfl hite]
    by_cases hm : m ≤ N
    · simp only [hm, true_and]
      rw [Finset.sum_ite_eq' (Finset.range X)]
      simp only [Finset.mem_range]
      rw [if_pos (by omega), if_pos (by omega)]
    · rw [if_neg (by omega)]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [if_neg (by tauto)]
  rw [Finset.sum_congr rfl hcol, ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

end

end NCG.AffineSelectors
