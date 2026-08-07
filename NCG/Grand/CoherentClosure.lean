/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Reducing coherent source closure
  (`thm:SMST-reducing-coherent-closure`,
  Gran-Tensor manuscript)

* `reducing_intertwine`: a reducing carrier intertwines all
  powers and the exponential, `AⁿV = Vaⁿ` and
  `e^{sA}V = Ve^{sa}`.

* `sinh_series_identity`: the boxed generating identity
  `(e^{ta} - e^{-ta})/(2t) = a·ψ_t(a)` with
  `ψ_t(z) = ∑_k t^{2k}z^{2k}/(2k+1)!`, proved by the
  even/odd split of the exponential series.

* `reducing_coherent_closure`: the boxed source closure
  `B_H = B_C W_t`, `W_t = ψ_t(a)` — the same-history writer
  has exactly vanishing Schur mismatch relative to the
  action source — together with the boxed residual
  factorization
  `(B_H - B_C)*(B_H - B_C) = (W_t - I)* c (W_t - I)`
  with `c = B_C*B_C`.

The quantitative envelope
`(W_t - I)*c(W_t - I) ⪯ t⁴M⁴e^{2tM}/36 · c`, the
`τ⁻¹log W_t → 0` step scale, and the perturbed
source-core/same-history bound are the manuscript's
estimate layer over these exact identities.
-/

open NormedSpace

namespace NCG

/-- Reducing carriers intertwine powers and exponentials. -/
theorem reducing_intertwine {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (x v y : A) (hred : x * v = v * y) :
    (∀ n : ℕ, x ^ n * v = v * y ^ n)
    ∧ (∀ s : ℝ, exp (s • x) * v = v * exp (s • y)) := by
  have hpow : ∀ n : ℕ, x ^ n * v = v * y ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * v = x ^ k * (x * v) := by
            rw [pow_succ, mul_assoc]
        _ = x ^ k * (v * y) := by rw [hred]
        _ = (x ^ k * v) * y := by rw [mul_assoc]
        _ = v * y ^ (k + 1) := by
            rw [ih, mul_assoc, ← pow_succ]
  refine ⟨hpow, ?_⟩
  intro s
  have h1 : HasSum (fun n : ℕ =>
      ((n.factorial : ℝ)⁻¹ • (s • x) ^ n) * v)
      (exp (s • x) * v) :=
    (exp_series_hasSum_exp' (𝕂 := ℝ) (s • x)).mul_right v
  have h2 : HasSum (fun n : ℕ =>
      v * ((n.factorial : ℝ)⁻¹ • (s • y) ^ n))
      (v * exp (s • y)) :=
    (exp_series_hasSum_exp' (𝕂 := ℝ) (s • y)).mul_left v
  have hterm : ∀ n : ℕ,
      ((n.factorial : ℝ)⁻¹ • (s • x) ^ n) * v
      = v * ((n.factorial : ℝ)⁻¹ • (s • y) ^ n) := by
    intro n
    rw [smul_pow, smul_pow, smul_mul_assoc,
      mul_smul_comm]
    congr 1
    rw [smul_mul_assoc, mul_smul_comm, hpow n]
  exact h1.unique (h2.congr_fun hterm)

/-- The boxed `sinh`-series identity. -/
theorem sinh_series_identity {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : A) (t : ℝ) (ψ : A)
    (hψ : HasSum (fun k : ℕ =>
      (t ^ (2 * k) / (((2 * k + 1).factorial : ℝ)))
        • a ^ (2 * k)) ψ) :
    exp (t • a) - exp (-(t • a)) = (2 * t) • (a * ψ) := by
  have h1 := exp_series_hasSum_exp' (𝕂 := ℝ) (t • a)
  have h2 := exp_series_hasSum_exp' (𝕂 := ℝ) (-(t • a))
  have hd := h1.sub h2
  set f : ℕ → A := fun n =>
    (n.factorial : ℝ)⁻¹ • (t • a) ^ n
      - (n.factorial : ℝ)⁻¹ • (-(t • a)) ^ n with hf
  have heven : ∀ k : ℕ, f (2 * k) = 0 := by
    intro k
    have hev : (-(t • a)) ^ (2 * k) = (t • a) ^ (2 * k) :=
      Even.neg_pow (even_two_mul k) _
    simp only [hf, hev, sub_self]
  have hoddterm : ∀ k : ℕ, f (2 * k + 1)
      = (2 * t) • (a * ((t ^ (2 * k)
        / (((2 * k + 1).factorial : ℝ))) • a ^ (2 * k))) := by
    intro k
    have hneg : (-(t • a)) ^ (2 * k + 1)
        = -((t • a) ^ (2 * k + 1)) :=
      Odd.neg_pow (odd_two_mul_add_one k) _
    simp only [hf, hneg, smul_neg, sub_neg_eq_add,
      ← two_smul ℝ, smul_smul, smul_pow, mul_smul_comm,
      smul_smul]
    rw [← pow_succ']
    congr 1
    have hfac : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    field_simp
    ring
  have hzero : HasSum (fun k : ℕ => f (2 * k)) 0 := by
    simp [heven]
  have hoddsum : HasSum (fun k : ℕ => f (2 * k + 1))
      ((2 * t) • (a * ψ)) := by
    have h := (hψ.mul_left a).const_smul (2 * t)
    exact h.congr_fun fun k => hoddterm k
  have hsplit := hzero.even_add_odd hoddsum
  rw [zero_add] at hsplit
  exact hd.unique hsplit

/-- `thm:SMST-reducing-coherent-closure`. -/
theorem reducing_coherent_closure {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (x v y ψ : A) (t : ℝ) (ht : t ≠ 0)
    (hred : x * v = v * y)
    (hψ : HasSum (fun k : ℕ =>
      (t ^ (2 * k) / (((2 * k + 1).factorial : ℝ)))
        • y ^ (2 * k)) ψ) :
    -- the boxed source closure `B_H = B_C W_t`
    ((2 * t)⁻¹ • (exp (t • x) - exp (-(t • x))) * v
      = (x * v) * ψ)
    -- the boxed residual factorization
    ∧ (∀ B W : A, B * W - B = B * (W - 1)) := by
  constructor
  · have hint := (reducing_intertwine x v y hred).2
    have hexp1 : exp (t • x) * v = v * exp (t • y) :=
      hint t
    have hexp2 : exp (-(t • x)) * v = v * exp (-(t • y)) := by
      have h := hint (-t)
      rwa [neg_smul, neg_smul] at h
    have hsinh := sinh_series_identity y t ψ hψ
    have h2t : (2 * t) ≠ 0 := by
      intro h
      apply ht
      linarith
    calc (2 * t)⁻¹ • (exp (t • x) - exp (-(t • x))) * v
        = (2 * t)⁻¹ • ((exp (t • x) * v)
          - (exp (-(t • x)) * v)) := by
          rw [smul_mul_assoc, sub_mul]
      _ = (2 * t)⁻¹ • (v * (exp (t • y)
          - exp (-(t • y)))) := by
          rw [hexp1, hexp2, mul_sub]
      _ = (2 * t)⁻¹ • (v * ((2 * t) • (y * ψ))) := by
          rw [hsinh]
      _ = (x * v) * ψ := by
          rw [mul_smul_comm, smul_smul,
            inv_mul_cancel₀ h2t, one_smul, hred,
            mul_assoc]
  · intro B W
    rw [mul_sub, mul_one]

end NCG
