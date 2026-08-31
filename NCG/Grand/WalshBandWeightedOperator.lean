/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Weighted norm bounds for tridiagonal Walsh-degree operators

This module supplies the operator-norm step in
`thm:renewal-chaos-localization`.  If an insertion splits into diagonal,
degree-raising, and degree-lowering blocks, conjugation by the exponential
degree weight multiplies the latter two blocks by `exp α` and `exp (-α)`.
Re-expanding about the unweighted insertion gives the sharp manuscript
constant `1 + 2 sinh α` using only the three natural block bounds.
-/

namespace NCG
namespace WalshBandWeightedOperator

variable {A : Type*} [SeminormedAddCommGroup A] [NormedSpace ℝ A]

/-- Algebraic re-expansion of a weighted tridiagonal-degree operator about
the original unweighted operator. -/
theorem weighted_band_identity (D R L : A) (α : ℝ) :
    D + Real.exp α • R + Real.exp (-α) • L =
      (D + R + L) + (Real.exp α - 1) • R -
        (1 - Real.exp (-α)) • L := by
  module

/-- The sharp weighted band bound.  Here `D + R + L` is the original
insertion, while `R` and `L` are its raising and lowering blocks. -/
theorem norm_weighted_band_le (D R L : A) (q α : ℝ)
    (hα : 0 ≤ α)
    (hT : ‖D + R + L‖ ≤ q) (hR : ‖R‖ ≤ q) (hL : ‖L‖ ≤ q) :
    ‖D + Real.exp α • R + Real.exp (-α) • L‖ ≤
      q * (1 + 2 * Real.sinh α) := by
  have he : 1 ≤ Real.exp α := by
    simpa using Real.exp_le_exp.mpr hα
  have hen : Real.exp (-α) ≤ 1 := by
    have : -α ≤ 0 := neg_nonpos.mpr hα
    simpa using Real.exp_le_exp.mpr this
  have hca : 0 ≤ Real.exp α - 1 := sub_nonneg.mpr he
  have hcn : 0 ≤ 1 - Real.exp (-α) := sub_nonneg.mpr hen
  rw [weighted_band_identity]
  calc
    ‖(D + R + L) + (Real.exp α - 1) • R -
        (1 - Real.exp (-α)) • L‖
        ≤ ‖D + R + L‖ + ‖(Real.exp α - 1) • R‖ +
            ‖(1 - Real.exp (-α)) • L‖ := by
          calc
            ‖(D + R + L) + (Real.exp α - 1) • R -
                (1 - Real.exp (-α)) • L‖
                ≤ ‖(D + R + L) + (Real.exp α - 1) • R‖ +
                    ‖(1 - Real.exp (-α)) • L‖ := norm_sub_le _ _
            _ ≤ (‖D + R + L‖ + ‖(Real.exp α - 1) • R‖) +
                    ‖(1 - Real.exp (-α)) • L‖ :=
                  add_le_add (norm_add_le _ _) le_rfl
    _ = ‖D + R + L‖ + (Real.exp α - 1) * ‖R‖ +
          (1 - Real.exp (-α)) * ‖L‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hca, abs_of_nonneg hcn]
    _ ≤ q + (Real.exp α - 1) * q +
          (1 - Real.exp (-α)) * q := by
          gcongr
    _ = q * (1 + 2 * Real.sinh α) := by
          rw [Real.sinh_eq]
          ring

end WalshBandWeightedOperator
end NCG
