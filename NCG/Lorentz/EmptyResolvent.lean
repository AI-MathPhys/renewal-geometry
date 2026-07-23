/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Empty resolvent of the covariant Lorentzian Dirac symbol

**Proposition `prop:empty-resolvent`**: the covariant Dirac operator
has empty resolvent set.  The algebraic mechanism proved here: since
the symbol squares to the scalar quadratic form, `σ² = Q·1`, the
resolvent factorises as
`(σ − z)(σ + z) = (Q − z²)·1` (`NCG.symbol_resolvent_factorisation`);
whenever the hyperbolic form attains `Q = z²` — which happens for
every `z` along the null-cone tubes — the factor `σ − z` is a zero
divisor and cannot be invertible (`NCG.not_isUnit_of_symbol_null`).
The `L²` essential-boundedness packaging of the Fourier multiplier is
the noted analytic step.
-/

namespace NCG

/-- **Proposition `prop:empty-resolvent` (factorisation)**: a symbol
squaring to the scalar `q` factorises the resolvent:
`(σ − z·1)(σ + z·1) = (q − z²)·1`. -/
theorem symbol_resolvent_factorisation {A : Type*} [Ring A]
    [Algebra ℂ A] (σ : A) (q z : ℂ) (hσ : σ ^ 2 = q • 1) :
    (σ - z • 1) * (σ + z • 1) = (q - z ^ 2) • (1 : A) := by
  have hc : (z • (1:A)) * σ = σ * (z • 1) := by
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have h2 : (z • (1:A)) * (z • 1) = (z ^ 2) • 1 := by
    rw [smul_mul_assoc, one_mul, smul_smul, pow_two]
  calc (σ - z • 1) * (σ + z • 1)
      = σ * σ + σ * (z • 1) - ((z • 1) * σ + (z • 1) * (z • 1)) := by
        rw [sub_mul, mul_add, mul_add]
    _ = q • 1 - (z ^ 2) • 1 := by
        rw [← pow_two, hσ, hc, h2]
        abel
    _ = (q - z ^ 2) • 1 := by rw [sub_smul]

/-- **Proposition `prop:empty-resolvent` (obstruction)**: when the
quadratic form attains `q = z²` on a covector, the symbol difference
`σ − z·1` is a zero divisor, hence not invertible — the candidate
resolvent point `z` is in the spectrum. -/
theorem not_isUnit_of_symbol_null {A : Type*} [Ring A] [Algebra ℂ A]
    (σ : A) (q z : ℂ) (hσ : σ ^ 2 = q • 1) (hz : q = z ^ 2)
    (hnz : σ + z • 1 ≠ 0) : ¬IsUnit (σ - z • 1) := by
  intro hu
  apply hnz
  have h0 : (σ - z • 1) * (σ + z • 1) = 0 := by
    rw [symbol_resolvent_factorisation σ q z hσ, hz]
    simp
  obtain ⟨u, hu'⟩ := hu
  calc σ + z • 1 = (↑u⁻¹ * ↑u) * (σ + z • 1) := by
        rw [Units.inv_mul, one_mul]
    _ = ↑u⁻¹ * ((σ - z • 1) * (σ + z • 1)) := by
        rw [hu', mul_assoc]
    _ = 0 := by rw [h0, mul_zero]

end NCG
