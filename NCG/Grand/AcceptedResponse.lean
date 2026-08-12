/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact accepted-response renewal and source-native coarse gap
  (`thm:accepted-response-renewal`, Gran-Tensor manuscript)

* `accepted_response_renewal`: the boxed geometric-thinning
  transform `F_T = θF_W/(1-(1-θ)F_W) = 8θz²/(15-8z+(8θ-7)z²)`,
  the survivor transform `(1-F_T)/(1-z) = (15+7z)/(…)`, its
  value `11/(4θ)` at `z = 1` (the tail-sum mean `𝔼T`), and the
  exact response rate `p_resp = (4/11)θ = 52441/104485552128`.
* `accepted_channel_power`: the boxed idempotent channel decay
  `(R + c(I-R))ᴺ = R + cᴺ(I-R)`, giving both boxed channel
  formulas at `c = 1-θ` and `c = Pr(T>n)`.

The actual iid geometric-random-sum PMF, its first moment, strict-tail
generating series, positive exponential moment, and the explicit
regulator-uniform assumptions are proved in
`NCG.Renewal.AcceptedResponseLaw`.  This module retains the reusable closed-form
algebra and idempotent-channel identity.
-/

open Matrix

namespace NCG

/-- Idempotent channel mixtures decay geometrically. -/
theorem accepted_channel_power {n : Type*} [Fintype n]
    [DecidableEq n] (R : Matrix n n ℝ) (hR : R * R = R)
    (c : ℝ) :
    ∀ N : ℕ, 1 ≤ N →
      (R + c • ((1 : Matrix n n ℝ) - R)) ^ N
        = R + c ^ N • ((1 : Matrix n n ℝ) - R) := by
  have hR1 : R * ((1 : Matrix n n ℝ) - R) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hR, sub_self]
  have h1R : ((1 : Matrix n n ℝ) - R) * R = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hR, sub_self]
  have h1R1 : ((1 : Matrix n n ℝ) - R) * (1 - R) = 1 - R := by
    rw [Matrix.sub_mul, Matrix.one_mul, hR1, sub_zero]
  intro N hN
  induction N with
  | zero => omega
  | succ k ih =>
      by_cases hk : 1 ≤ k
      · rw [pow_succ, ih hk]
        rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
          hR, Matrix.mul_smul, hR1, smul_zero, add_zero,
          Matrix.smul_mul, h1R, smul_zero, zero_add,
          Matrix.smul_mul, Matrix.mul_smul, h1R1, smul_smul,
          ← pow_succ]
      · have hk0 : k = 0 := by omega
        subst hk0
        rw [pow_one, pow_one]

/-- `thm:accepted-response-renewal`: the boxed rational
identities and the exact response rate. -/
theorem accepted_response_renewal :
    (∀ θ z : ℝ, (5 - z) * (3 - z) ≠ 0 →
      15 - 8 * z + (8 * θ - 7) * z ^ 2 ≠ 0 →
      θ * (8 * z ^ 2 / ((5 - z) * (3 - z)))
        / (1 - (1 - θ) * (8 * z ^ 2 / ((5 - z) * (3 - z))))
      = 8 * θ * z ^ 2 / (15 - 8 * z + (8 * θ - 7) * z ^ 2))
    ∧ (∀ θ z : ℝ, 15 - 8 * z + (8 * θ - 7) * z ^ 2 ≠ 0 →
        z ≠ 1 →
        (1 - 8 * θ * z ^ 2
            / (15 - 8 * z + (8 * θ - 7) * z ^ 2)) / (1 - z)
        = (15 + 7 * z)
            / (15 - 8 * z + (8 * θ - 7) * z ^ 2))
    ∧ (∀ θ : ℝ, θ ≠ 0 →
        (15 + 7 * (1 : ℝ))
            / (15 - 8 * 1 + (8 * θ - 7) * 1 ^ 2)
          = 11 / (4 * θ))
    ∧ ((4 / 11 : ℚ) * (576851 / 417942208512)
        = 52441 / 104485552128) := by
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · intro θ z hD hE
    have hden : 1 - (1 - θ) * (8 * z ^ 2 / ((5 - z) * (3 - z)))
        = (15 - 8 * z + (8 * θ - 7) * z ^ 2)
          / ((5 - z) * (3 - z)) := by
      rw [eq_div_iff hD, sub_mul, one_mul, mul_assoc,
        div_mul_cancel₀ _ hD]
      ring
    rw [hden, div_div_eq_mul_div, mul_assoc,
      div_mul_cancel₀ _ hD]
    ring
  · intro θ z hE hz
    have hz' : (1 : ℝ) - z ≠ 0 := sub_ne_zero.mpr
      (fun h => hz h.symm)
    rw [div_eq_div_iff hz' hE, sub_mul, one_mul,
      div_mul_cancel₀ _ hE]
    ring
  · intro θ hθ
    have h4θ : (4 : ℝ) * θ ≠ 0 := by
      exact mul_ne_zero (by norm_num) hθ
    rw [show (15 : ℝ) - 8 * 1 + (8 * θ - 7) * 1 ^ 2
        = 8 * θ from by ring]
    rw [div_eq_div_iff (by
      intro h
      exact hθ (by linarith)) h4θ]
    ring

end NCG
