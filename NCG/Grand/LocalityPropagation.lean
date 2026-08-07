/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite propagation from source-locality residuals
  (`thm:source-locality-propagation`, Gran-Tensor manuscript)

* `source_locality_propagation`: for a contraction `T` and a
  family of contractive idempotent source projections `P n`,
  the boxed propagation bound
  `‖(1-P_{n+k})·Tᵏ·P_n‖ ≤ Σ_{j<k} ℓ_{n+j}(T)` holds, where
  `ℓ_m(T) = ‖(1-P_{m+1})·T·P_m‖` is the one-step locality
  residual. Exact one-step locality therefore gives exact
  finite propagation.

Rendering disclosed: stated in an arbitrary normed ring
(instantiating to bounded operators on the source Hilbert
space); the projections enter through the norm bounds
`‖P‖ ≤ 1`, `‖1-P‖ ≤ 1` and idempotence, which orthogonal
projections satisfy.
-/

namespace NCG

/-- `thm:source-locality-propagation`: the telescoping
propagation bound. -/
theorem source_locality_propagation {A : Type*} [NormedRing A]
    (T : A) (P : ℕ → A) (hT : ‖T‖ ≤ 1)
    (hP : ∀ n, ‖P n‖ ≤ 1) (hQ : ∀ n, ‖1 - P n‖ ≤ 1)
    (hidem : ∀ n, P n * P n = P n) (n : ℕ) :
    ∀ k : ℕ,
      ‖(1 - P (n + k)) * T ^ k * P n‖
        ≤ ∑ j ∈ Finset.range k,
            ‖(1 - P (n + j + 1)) * T * P (n + j)‖ := by
  intro k
  induction k with
  | zero =>
      rw [pow_zero, mul_one, Nat.add_zero, sub_mul, one_mul,
        hidem, sub_self, norm_zero, Finset.range_zero,
        Finset.sum_empty]
  | succ k ih =>
      have hsplit : (1 - P (n + (k + 1))) * T ^ (k + 1) * P n
          = ((1 - P (n + k + 1)) * T * P (n + k))
              * (T ^ k * P n)
            + ((1 - P (n + k + 1)) * T)
              * ((1 - P (n + k)) * T ^ k * P n) := by
        have hexp : n + (k + 1) = n + k + 1 := by omega
        rw [hexp, pow_succ']
        noncomm_ring
      rw [hsplit]
      have hTkP : ‖T ^ k * P n‖ ≤ 1 := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [pow_zero, one_mul]
          exact hP n
        · calc ‖T ^ k * P n‖
              ≤ ‖T ^ k‖ * ‖P n‖ := norm_mul_le _ _
            _ ≤ 1 * 1 :=
                mul_le_mul
                  (le_trans (norm_pow_le' T hk)
                    (pow_le_one₀ (norm_nonneg T) hT))
                  (hP n) (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      have hQT : ‖(1 - P (n + k + 1)) * T‖ ≤ 1 := by
        calc ‖(1 - P (n + k + 1)) * T‖
            ≤ ‖1 - P (n + k + 1)‖ * ‖T‖ := norm_mul_le _ _
          _ ≤ 1 * 1 :=
              mul_le_mul (hQ (n + k + 1)) hT (norm_nonneg _)
                zero_le_one
          _ = 1 := one_mul 1
      calc ‖((1 - P (n + k + 1)) * T * P (n + k))
              * (T ^ k * P n)
            + ((1 - P (n + k + 1)) * T)
              * ((1 - P (n + k)) * T ^ k * P n)‖
          ≤ ‖((1 - P (n + k + 1)) * T * P (n + k))
                * (T ^ k * P n)‖
            + ‖((1 - P (n + k + 1)) * T)
                * ((1 - P (n + k)) * T ^ k * P n)‖ :=
            norm_add_le _ _
        _ ≤ ‖(1 - P (n + k + 1)) * T * P (n + k)‖ * 1
            + 1 * ‖(1 - P (n + k)) * T ^ k * P n‖ := by
            refine add_le_add ?_ ?_
            · exact le_trans (norm_mul_le _ _)
                (mul_le_mul_of_nonneg_left hTkP
                  (norm_nonneg _))
            · exact le_trans (norm_mul_le _ _)
                (mul_le_mul_of_nonneg_right hQT
                  (norm_nonneg _))
        _ = ‖(1 - P (n + k + 1)) * T * P (n + k)‖
            + ‖(1 - P (n + k)) * T ^ k * P n‖ := by ring
        _ ≤ ‖(1 - P (n + k + 1)) * T * P (n + k)‖
            + ∑ j ∈ Finset.range k,
                ‖(1 - P (n + j + 1)) * T * P (n + j)‖ := by
            exact add_le_add le_rfl ih
        _ = ∑ j ∈ Finset.range (k + 1),
              ‖(1 - P (n + j + 1)) * T * P (n + j)‖ := by
            rw [Finset.sum_range_succ]
            ring

end NCG
