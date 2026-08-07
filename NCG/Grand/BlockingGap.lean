/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Blocking does not create a gap
  (`cth:blocking-does-not-create-gap`, Gran-Tensor manuscript)

* `blocking_reduction`: for an idempotent `E` reducing `T`
  (`TE = ET = E`), the blocked compression obeys the exact
  algebraic identity `(1-E)Tᵐ(1-E) = ((1-E)T(1-E))ᵐ` in any
  ring.
* `selfAdjoint_norm_pow`: in a `C*`-algebra,
  `‖aᵐ‖ = ‖a‖ᵐ` for self-adjoint `a`.
* `blocking_does_not_create_gap`: hence the boxed norm identity
  `‖(1-E)Tᵐ(1-E)‖ = ‖(1-E)T(1-E)‖ᵐ` — rewriting a regulator as
  a thicker block proves no gap.

Rendering disclosed: `0 ⪯ T ⪯ I` with `E` the fixed-space
projection is rendered by its consequences used in the proof
(`T` self-adjoint, `E` a self-adjoint idempotent with `TE = E`);
the spectral-theorem step is the `C*`-norm power identity.
-/

namespace NCG

/-- The blocked compression identity in any ring. -/
theorem blocking_reduction {A : Type*} [Ring A] (T E : A)
    (hE : E * E = E) (hTE : T * E = E) (hET : E * T = E) :
    ∀ m : ℕ, 1 ≤ m →
      (1 - E) * T ^ m * (1 - E) = ((1 - E) * T * (1 - E)) ^ m := by
  have hTmE : ∀ m : ℕ, T ^ m * E = E := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mul]
    | succ k ih => rw [pow_succ, mul_assoc, hTE, ih]
  have hETm : ∀ m : ℕ, E * T ^ m = E := by
    intro m
    induction m with
    | zero => rw [pow_zero, mul_one]
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hET]
  have hQTQ : ∀ m : ℕ, (1 - E) * T ^ m * (1 - E) = T ^ m - E := by
    intro m
    rw [sub_mul, one_mul, hETm, mul_sub, mul_one, sub_mul,
      hTmE, hE, sub_self, sub_zero]
  have hpow : ∀ m : ℕ, 1 ≤ m → (T - E) ^ m = T ^ m - E := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih =>
        by_cases hk : 1 ≤ k
        · rw [pow_succ, ih hk, sub_mul, mul_sub, mul_sub,
            hTmE, hET, hE, sub_self, sub_zero, ← pow_succ]
        · have hk0 : k = 0 := by omega
          subst hk0
          rw [pow_one, pow_one]
  intro m hm
  rw [hQTQ m]
  have h1 : (1 - E) * T * (1 - E) = T - E := by
    have := hQTQ 1
    rwa [pow_one] at this
  rw [h1, hpow m hm]

/-- `‖aᵐ‖ = ‖a‖ᵐ` for self-adjoint elements of a `C*`-algebra
(via dyadic interpolation from the `2^k` power identity). -/
theorem selfAdjoint_norm_pow {A : Type*} [NormedRing A]
    [StarRing A] [CStarRing A] (a : A) (ha : IsSelfAdjoint a)
    (m : ℕ) (hm : 1 ≤ m) : ‖a ^ m‖ = ‖a‖ ^ m := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_pow (by omega : m ≠ 0), norm_zero,
      zero_pow (by omega : m ≠ 0)]
  · refine le_antisymm (norm_pow_le' a (by omega)) ?_
    have hk : m < 2 ^ m := Nat.lt_two_pow_self
    have hnorm0 : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha0
    have hsplit : a ^ (2 ^ m) = a ^ m * a ^ (2 ^ m - m) := by
      rw [← pow_add]
      congr 1
      omega
    have h1 : ‖a‖ ^ (2 ^ m) ≤ ‖a ^ m‖ * ‖a‖ ^ (2 ^ m - m) := by
      calc ‖a‖ ^ (2 ^ m) = ‖a ^ (2 ^ m)‖ :=
            (ha.norm_pow_two_pow m).symm
        _ = ‖a ^ m * a ^ (2 ^ m - m)‖ := by rw [hsplit]
        _ ≤ ‖a ^ m‖ * ‖a ^ (2 ^ m - m)‖ := norm_mul_le _ _
        _ ≤ ‖a ^ m‖ * ‖a‖ ^ (2 ^ m - m) :=
            mul_le_mul_of_nonneg_left
              (norm_pow_le' a (by omega)) (norm_nonneg _)
    have h2 : ‖a‖ ^ m * ‖a‖ ^ (2 ^ m - m)
        ≤ ‖a ^ m‖ * ‖a‖ ^ (2 ^ m - m) := by
      rw [← pow_add, show m + (2 ^ m - m) = 2 ^ m from by omega]
      exact h1
    exact le_of_mul_le_mul_right h2 (pow_pos hnorm0 _)

/-- `cth:blocking-does-not-create-gap`: the boxed norm
identity. -/
theorem blocking_does_not_create_gap {A : Type*} [NormedRing A]
    [StarRing A] [CStarRing A] (T E : A)
    (hT : IsSelfAdjoint T) (hEsa : IsSelfAdjoint E)
    (hE : E * E = E) (hTE : T * E = E) :
    ∀ m : ℕ, 1 ≤ m →
      ‖(1 - E) * T ^ m * (1 - E)‖
        = ‖(1 - E) * T * (1 - E)‖ ^ m := by
  have hET : E * T = E := by
    have h := congrArg star hTE
    rwa [star_mul, hEsa.star_eq, hT.star_eq] at h
  intro m hm
  rw [blocking_reduction T E hE hTE hET m hm]
  have hQTQeq : (1 - E) * T * (1 - E) = T - E := by
    rw [sub_mul, one_mul, hET, mul_sub, mul_one, sub_mul,
      hTE, hE, sub_self, sub_zero]
  have hsa : IsSelfAdjoint ((1 - E) * T * (1 - E)) := by
    rw [hQTQeq]
    exact hT.sub hEsa
  exact selfAdjoint_norm_pow _ hsa m hm

end NCG
