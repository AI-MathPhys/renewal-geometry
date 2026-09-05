/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Cramér–Chernoff upper bound
  (missing large-deviations machinery; `thm:deficiency-rate-function`,
   GR_emergence)

Mathlib has no large-deviations theory.  This file proves the upper
half of the Cramér/Gärtner–Ellis principle for finite-alphabet
i.i.d. records — the exponential decay of upper tails at the
Legendre rate:

* `iid_mgf_factorization` — the product formula
  `Σ_ω Π_k F(ω_k) = (Σ_a F(a))ⁿ` on path space;
* `chernoff_bound` — the exponential Markov bound
  `P(S_n ≥ na) ≤ e^{-χna}·M(χ)ⁿ` for every tilt `χ ≥ 0`;
* `cramer_upper_bound` — the Legendre form
  `P(S_n ≥ na) ≤ exp(-n·(χa - Λ(χ)))`, `Λ = log M`, whose optimal
  `χ` is the rate function `I(a) = sup_χ (χa - Λ(χ))` of
  `NCG.rateFunction`.

Together with the convex layer in `NCG/Gravity/RateFunction.lean`
this proves the upper-bound half of `thm:deficiency-rate-function`'s
large-deviation principle for i.i.d. finite records; the matching
lower bound (tilted change of measure) and the Markov-renewal
extension remain the declared layer.
-/

namespace NCG

/-- Path-space factorization: sums of products over i.i.d. steps
factor through the single-step sum. -/
theorem iid_mgf_factorization {A : Type*} [Fintype A]
    (F : A → ℝ) (n : ℕ) :
    (∑ ω : Fin n → A, ∏ k, F (ω k)) = (∑ a, F a) ^ n := by
  classical
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : (∑ ω : Fin (m + 1) → A, ∏ k, F (ω k))
        = ∑ p : A × (Fin m → A), F p.1 * ∏ k, F (p.2 k) := by
      apply Fintype.sum_equiv (Fin.consEquiv fun _ => A).symm
      intro ω
      rw [Fin.prod_univ_succ]
      rfl
    rw [hsplit, Fintype.sum_prod_type]
    rw [show (∑ a : A, ∑ ω : Fin m → A, F a * ∏ k, F (ω k))
      = (∑ a : A, F a * ∑ ω : Fin m → A, ∏ k, F (ω k)) from by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]]
    rw [← Finset.sum_mul, ih, pow_succ]
    ring

/-- The Chernoff bound: for every nonnegative tilt `χ`, the upper
tail of the additive record is bounded by
`e^{-χna}·M(χ)ⁿ`, `M(χ) = Σ_b q_b e^{χf(b)}`. -/
theorem chernoff_bound {A : Type*} [Fintype A]
    (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (f : A → ℝ) (n : ℕ)
    (a chi : ℝ) (hchi : 0 ≤ chi) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin n → A => (n : ℝ) * a ≤ ∑ k, f (ω k)),
      ∏ k, q (ω k))
      ≤ Real.exp (-(chi * ((n : ℝ) * a)))
          * (∑ b, q b * Real.exp (chi * f b)) ^ n := by
  classical
  rw [← iid_mgf_factorization (fun b => q b * Real.exp (chi * f b)) n]
  rw [Finset.mul_sum]
  have hterm : ∀ ω : Fin n → A,
      Real.exp (-(chi * ((n : ℝ) * a)))
        * ∏ k, (q (ω k) * Real.exp (chi * f (ω k)))
      = (∏ k, q (ω k))
          * Real.exp (chi * ((∑ k, f (ω k)) - (n : ℝ) * a)) := by
    intro ω
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    rw [show (∑ k, chi * f (ω k)) = chi * ∑ k, f (ω k) from by
      rw [Finset.mul_sum]]
    rw [show Real.exp (-(chi * ((n : ℝ) * a)))
          * ((∏ k, q (ω k)) * Real.exp (chi * ∑ k, f (ω k)))
        = (∏ k, q (ω k))
          * (Real.exp (chi * ∑ k, f (ω k))
              * Real.exp (-(chi * ((n : ℝ) * a)))) from by ring]
    rw [← Real.exp_add]
    congr 2
    ring
  rw [show (∑ ω : Fin n → A, Real.exp (-(chi * ((n : ℝ) * a)))
        * ∏ k, (q (ω k) * Real.exp (chi * f (ω k))))
      = ∑ ω : Fin n → A, (∏ k, q (ω k))
          * Real.exp (chi * ((∑ k, f (ω k)) - (n : ℝ) * a)) from
    Finset.sum_congr rfl fun ω _ => hterm ω]
  calc (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin n → A => (n : ℝ) * a ≤ ∑ k, f (ω k)),
      ∏ k, q (ω k))
      ≤ ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin n → A => (n : ℝ) * a ≤ ∑ k, f (ω k)),
        (∏ k, q (ω k))
          * Real.exp (chi * ((∑ k, f (ω k)) - (n : ℝ) * a)) := by
        apply Finset.sum_le_sum
        intro ω hω
        rw [Finset.mem_filter] at hω
        have hexp : (1 : ℝ)
            ≤ Real.exp (chi * ((∑ k, f (ω k)) - (n : ℝ) * a)) := by
          rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
          apply Real.exp_le_exp.mpr
          have : (0 : ℝ) ≤ (∑ k, f (ω k)) - (n : ℝ) * a := by
            linarith [hω.2]
          positivity
        calc (∏ k, q (ω k))
            = (∏ k, q (ω k)) * 1 := (mul_one _).symm
        _ ≤ (∏ k, q (ω k))
              * Real.exp (chi * ((∑ k, f (ω k)) - (n : ℝ) * a)) := by
            apply mul_le_mul_of_nonneg_left hexp
            exact Finset.prod_nonneg fun k _ => hq (ω k)
  _ ≤ ∑ ω : Fin n → A, (∏ k, q (ω k))
        * Real.exp (chi * ((∑ k, f (ω k)) - (n : ℝ) * a)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro ω _ _
        apply mul_nonneg (Finset.prod_nonneg fun k _ => hq (ω k))
        exact (Real.exp_pos _).le

/-- `thm:deficiency-rate-function` (Cramér upper bound): the upper
tail decays at the Legendre rate — for every `χ ≥ 0`,
`P(S_n ≥ na) ≤ exp(-n·(χa - Λ(χ)))` with `Λ = log M`; optimizing
over `χ` gives the rate function `I(a)`. -/
theorem cramer_upper_bound {A : Type*} [Fintype A]
    (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (f : A → ℝ) (n : ℕ)
    (a chi : ℝ) (hchi : 0 ≤ chi)
    (hM : 0 < ∑ b, q b * Real.exp (chi * f b)) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin n → A => (n : ℝ) * a ≤ ∑ k, f (ω k)),
      ∏ k, q (ω k))
      ≤ Real.exp (-((n : ℝ) * (chi * a
          - Real.log (∑ b, q b * Real.exp (chi * f b))))) := by
  have h := chernoff_bound q hq f n a chi hchi
  calc (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin n → A => (n : ℝ) * a ≤ ∑ k, f (ω k)),
      ∏ k, q (ω k))
      ≤ Real.exp (-(chi * ((n : ℝ) * a)))
          * (∑ b, q b * Real.exp (chi * f b)) ^ n := h
  _ = Real.exp (-((n : ℝ) * (chi * a
        - Real.log (∑ b, q b * Real.exp (chi * f b))))) := by
        rw [show (∑ b, q b * Real.exp (chi * f b)) ^ n
          = Real.exp ((n : ℝ)
              * Real.log (∑ b, q b * Real.exp (chi * f b))) from by
            rw [Real.exp_nat_mul, Real.exp_log hM]]
        rw [← Real.exp_add]
        congr 1
        ring

end NCG
