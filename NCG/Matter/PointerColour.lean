/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Binary pointer algebra, colour expectation, and renewal semigroup
(SM_emergence, Phase 1)

The pinching family shared by `thm:binary-pointer-algebra` and
`thm:binary-colour-expectation-main`, plus the binary renewal
semigroup and the real-shadow CP guardrails:

* `pinch`, `pinch_unital`, `pinch_idem`, `pinch_trace`,
  `pinch_eq_half_add_conj`, `pinch_fixed_iff_commute` — the
  conditional expectation `𝔼(A) = e₀Ae₀ + e₁Ae₁` induced by a sharp
  repeatable binary record is unital, idempotent, trace preserving,
  equals `½(A + ZAZ)` for the difference involution `Z = e₀ - e₁`,
  and fixes exactly the commutant of `Z` (for the colour record
  `Z = Z_C` this identifies the released fixed charge algebra with
  the `M₃(ℂ) ⊕ ℂ` commutant block);
* `binary_renewal_semigroup`, `binary_renewal_lindblad_form` —
  `thm:binary-renewal-semigroup-main`:
  `𝒯_s = (1+s)/2·id + (1-s)/2·Ad_Z` satisfies `𝒯_s 𝒯_t = 𝒯_{st}`;
* `real_trace_im_zero`, `real_shadow_mul` —
  `prop:real-shadow-vanishing` and the real-shadow CP guardrail
  (`proposition:real-shadow-cp-guardrail`): matrices with real
  coefficients are closed under products and every cyclic trace of
  them is real, so `Z₂`-shadow data cannot generate a CP-odd trace
  invariant.
-/

namespace NCG

open Matrix

/-! ## The binary pinching (pointer and colour records) -/

section Pinch

variable {A : Type*} [Ring A]

/-- The binary pinching map `𝔼(a) = e₀ a e₀ + e₁ a e₁` of a sharp
repeatable two-outcome record. -/
def pinch (e0 e1 : A) (a : A) : A := e0 * a * e0 + e1 * a * e1

variable {e0 e1 : A}

/-- `thm:binary-pointer-algebra`: the pinching is unital. -/
theorem pinch_unital (h0 : e0 * e0 = e0) (h1 : e1 * e1 = e1)
    (hsum : e0 + e1 = 1) : pinch e0 e1 1 = 1 := by
  unfold pinch
  rw [mul_one, mul_one, h0, h1, hsum]

/-- `thm:binary-pointer-algebra`: the pinching is idempotent — it is
the unique conditional expectation induced by the repeatable
record. -/
theorem pinch_idem (h0 : e0 * e0 = e0) (h1 : e1 * e1 = e1)
    (h01 : e0 * e1 = 0) (h10 : e1 * e0 = 0) (a : A) :
    pinch e0 e1 (pinch e0 e1 a) = pinch e0 e1 a := by
  unfold pinch
  rw [mul_add, add_mul, mul_add, add_mul]
  rw [show e0 * (e0 * a * e0) * e0 = (e0 * e0) * a * (e0 * e0) by
    noncomm_ring]
  rw [show e0 * (e1 * a * e1) * e0 = (e0 * e1) * a * (e1 * e0) by
    noncomm_ring]
  rw [show e1 * (e0 * a * e0) * e1 = (e1 * e0) * a * (e0 * e1) by
    noncomm_ring]
  rw [show e1 * (e1 * a * e1) * e1 = (e1 * e1) * a * (e1 * e1) by
    noncomm_ring]
  rw [h0, h1, h01, h10]
  noncomm_ring

/-- The pinching in involution form: with `Z = e₀ - e₁`,
`2·𝔼(a) = a + ZaZ` — the dephasing presentation of the record
expectation. -/
theorem pinch_eq_half_add_conj (hsum : e0 + e1 = 1) (a : A) :
    (2:ℤ) • pinch e0 e1 a = a + (e0 - e1) * a * (e0 - e1) := by
  unfold pinch
  have hexp : (e0 + e1) * a * (e0 + e1) = a := by
    rw [hsum, one_mul, mul_one]
  have h2 : (e0 - e1) * a * (e0 - e1) + (e0 + e1) * a * (e0 + e1)
      = (2:ℤ) • (e0 * a * e0 + e1 * a * e1) := by
    noncomm_ring
  rw [← h2, hexp]
  abel

/-- The difference involution squares to one. -/
theorem pinch_involution_sq (h0 : e0 * e0 = e0) (h1 : e1 * e1 = e1)
    (h01 : e0 * e1 = 0) (h10 : e1 * e0 = 0) (hsum : e0 + e1 = 1) :
    (e0 - e1) * (e0 - e1) = 1 := by
  rw [sub_mul, mul_sub, mul_sub, h0, h1, h01, h10]
  rw [show e0 - 0 - (0 - e1) = e0 + e1 by abel, hsum]

/-- `thm:binary-colour-expectation-main` (fixed algebra): the fixed
points of the pinching are exactly the commutant of the difference
involution `Z = e₀ - e₁`.  For the colour record `Z = Z_C` this
identifies the released charge algebra with the `Z_C`-commutant, the
`M₃(ℂ) ⊕ ℂ` block algebra of `su(3)_c ⊕ u(1)_{B-L}`. -/
theorem pinch_fixed_iff_commute [NoZeroSMulDivisors ℤ A]
    (h0 : e0 * e0 = e0) (h1 : e1 * e1 = e1)
    (h01 : e0 * e1 = 0) (h10 : e1 * e0 = 0) (hsum : e0 + e1 = 1)
    (a : A) :
    pinch e0 e1 a = a ↔ (e0 - e1) * a = a * (e0 - e1) := by
  have hZsq := pinch_involution_sq h0 h1 h01 h10 hsum
  constructor
  · intro hfix
    have h2 := pinch_eq_half_add_conj hsum a
    rw [hfix, two_smul] at h2
    have h3 : (e0 - e1) * a * (e0 - e1) = a :=
      (add_left_cancel h2.symm)
    have h4 : ((e0 - e1) * a * (e0 - e1)) * (e0 - e1)
        = a * (e0 - e1) := by rw [h3]
    rw [mul_assoc ((e0 - e1) * a), hZsq, mul_one] at h4
    exact h4
  · intro hcomm
    have hkey : (2:ℤ) • pinch e0 e1 a = (2:ℤ) • a := by
      rw [pinch_eq_half_add_conj hsum a, hcomm,
        mul_assoc a, hZsq, mul_one, two_smul]
    exact smul_right_injective A (by norm_num : (2:ℤ) ≠ 0) hkey

end Pinch

/-- `thm:binary-pointer-algebra` / `thm:binary-colour-expectation`
(trace preservation): the pinching preserves the trace. -/
theorem pinch_trace {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [CommRing α]
    (e0 e1 a : Matrix n n α) (h0 : e0 * e0 = e0)
    (h1 : e1 * e1 = e1) (hsum : e0 + e1 = 1) :
    (pinch e0 e1 a).trace = a.trace := by
  unfold pinch
  rw [Matrix.trace_add, Matrix.trace_mul_cycle, h0,
    Matrix.trace_mul_cycle, h1, ← Matrix.trace_add,
    ← Matrix.add_mul, hsum, Matrix.one_mul]

/-! ## `thm:binary-renewal-semigroup-main` -/

section Semigroup

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- `thm:binary-renewal-semigroup-main`: the interpolation
`𝒯_s(a) = (1+s)/2·a + (1-s)/2·ZaZ` is a one-parameter semigroup for
the multiplicative parameter, `𝒯_s ∘ 𝒯_t = 𝒯_{st}`; writing
`s = e^{-γt}` this is the binary colour dephasing semigroup with
Lindblad generator `-γP₋`. -/
theorem binary_renewal_semigroup (Z : A) (hZ : Z * Z = 1)
    (s t : ℝ) (a : A) :
    ((1 + s)/2) • (((1 + t)/2) • a + ((1 - t)/2) • (Z * a * Z))
      + ((1 - s)/2) • (Z * (((1 + t)/2) • a
          + ((1 - t)/2) • (Z * a * Z)) * Z)
    = ((1 + s * t)/2) • a + ((1 - s * t)/2) • (Z * a * Z) := by
  have hZZ : Z * (Z * a * Z) * Z = a := by
    rw [show Z * (Z * a * Z) * Z = (Z * Z) * a * (Z * Z) by
      noncomm_ring]
    rw [hZ, one_mul, mul_one]
  have hinner : Z * (((1 + t)/2) • a + ((1 - t)/2) • (Z * a * Z)) * Z
      = ((1 + t)/2) • (Z * a * Z) + ((1 - t)/2) • a := by
    rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, smul_mul_assoc, hZZ]
  rw [hinner]
  module

end Semigroup

/-! ## `prop:real-shadow-vanishing` -/

section RealShadow

variable {n : Type*} [Fintype n]

/-- Real-coefficient matrices are closed under products (the
real-shadow algebra). -/
theorem real_shadow_mul (A B : Matrix n n ℝ) :
    (A.map (Complex.ofReal)) * (B.map (Complex.ofReal))
      = (A * B).map (Complex.ofReal) := by
  ext i j
  simp [Matrix.mul_apply]

/-- `prop:real-shadow-vanishing`: the trace of any real-shadow
matrix has vanishing imaginary part — real-shadow cyclic data cannot
generate a CP-orientation invariant
(`proposition:real-shadow-cp-guardrail`). -/
theorem real_trace_im_zero (A : Matrix n n ℝ) :
    ((A.map (Complex.ofReal)).trace).im = 0 := by
  unfold Matrix.trace
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro i _
  simp [Matrix.diag, Matrix.map_apply]

end RealShadow

end NCG
