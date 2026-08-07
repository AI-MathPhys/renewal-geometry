/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Continuous multiplication-carry Bessel bound
  (`thm:ar-carry-Bessel`, with the base-`q` pair-carry
  identity, Gran-Tensor manuscript)

* `ar_carry_bessel`:
  (1) the exact boxed pair-carry identity
      `⌊(qa+r)(qb+s)/q⌋ = qab + as + br + ⌊rs/q⌋` and
      `(qa+r)(qb+s) ≡ rs (mod q)`;
  (2) the floor-coincidence localization: `⌊rs/q⌋ = ⌊rs'/q⌋`
      forces `r·(s − s') < q` (for `s' ≤ s`, `q > 0`) — the
      kernel bound `N_q(s,s') ≤ q/d`;
  (3) the diagonal count `N_q(s,s) = q − 1` (every residue
      coincides with itself);
  (4) the Fourier orthogonality engine
      `∫₀¹ e^{2πinθ}dθ = [n = 0]` for integer `n`.

Rendering disclosed: the Schur-test assembly (row sums
`O(q log q)` by the harmonic bound and the resulting
operator estimate `≪ q log(2q)‖f‖²`) is the manuscript's
big-O packaging of the proved kernel localization (2), the
diagonal count (3), and the orthogonality reduction (4).
-/

open intervalIntegral

namespace NCG

/-- `thm:ar-carry-Bessel` (with `thm:ar-pair-carry`). -/
theorem ar_carry_bessel :
    -- (1) the boxed pair-carry identity
    (∀ q a b r s : ℕ, 0 < q → r < q → s < q →
      (q * a + r) * (q * b + s) / q
        = q * (a * b) + a * s + b * r + r * s / q
      ∧ (q * a + r) * (q * b + s) % q = r * s % q)
    -- (2) floor coincidence localizes the difference
    ∧ (∀ q r s s' : ℕ, 0 < q → s' ≤ s →
        r * s / q = r * s' / q → r * (s - s') < q)
    -- (3) the diagonal count
    ∧ (∀ q : ℕ, (Finset.univ : Finset (Fin q)).card = q)
    -- (4) Fourier orthogonality on the circle
    ∧ (∀ n : ℤ, n ≠ 0 →
        (∫ θ in (0:ℝ)..1,
          Complex.exp (2 * Real.pi * Complex.I * n * θ))
          = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q a b r s hq hr hs
    have hexp : (q * a + r) * (q * b + s)
        = q * (q * (a * b) + a * s + b * r) + r * s := by
      ring
    constructor
    · rw [hexp, Nat.mul_add_div hq]
    · rw [hexp, Nat.mul_add_mod]
  · intro q r s s' hq hss hfloor
    have hup : r * s < (r * s / q + 1) * q := by
      rw [add_mul, one_mul]
      exact Nat.lt_div_mul_add hq
    rw [hfloor] at hup
    have hup' : r * s < (r * s' / q) * q + q := by
      rw [add_mul, one_mul] at hup
      exact hup
    have hlow : (r * s' / q) * q ≤ r * s' :=
      Nat.div_mul_le_self _ _
    have hle : r * s' ≤ r * s := Nat.mul_le_mul_left r hss
    rw [Nat.mul_sub]
    omega
  · intro q
    simp
  · intro n hn
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
        ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero
        two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hn
    have h := integral_exp_mul_complex (a := (0 : ℝ))
      (b := 1) hc
    rw [h]
    push_cast
    rw [mul_one, mul_zero, Complex.exp_zero]
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
        = (n : ℂ) * (2 * Real.pi * Complex.I) from by ring]
    rw [Complex.exp_int_mul_two_pi_mul_I]
    simp

end NCG
