/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Divisor-safe positivity order

An explicit rank-one divisor model separates the vanishing partition from its first saturated
zero-mode coefficient.  The latter is the physical kernel/cokernel pairing and its sign is tested
directly; dividing it by the zero partition cannot satisfy the defining reconstruction equation.
-/

open Matrix

namespace NCG.SMQGDivisorSafePositivityOrder

/-- A two-dimensional precision with one hard mode and one source-saturated zero mode. -/
def saturatedDivisorMatrix (t q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, t * q]

/-- The determinant polynomial is exactly the first-degree zero-mode pairing. -/
theorem saturatedDivisorMatrix_det (t q : ℝ) :
    (saturatedDivisorMatrix t q).det = t * q := by
  simp [saturatedDivisorMatrix, Matrix.det_fin_two]

/-- At the divisor the partition vanishes, while a complete kernel/cokernel pairing gives a
nonzero first saturated coefficient. -/
theorem zero_mode_saturation_first_nonzero {q : ℝ} (hq : q ≠ 0) :
    (saturatedDivisorMatrix 0 q).det = 0 ∧
      (saturatedDivisorMatrix 1 q).det = q ∧
      (saturatedDivisorMatrix 1 q).det ≠ 0 := by
  refine ⟨by simp [saturatedDivisorMatrix_det], by simp [saturatedDivisorMatrix_det], ?_⟩
  simpa [saturatedDivisorMatrix_det] using hq

/-- Normalizing the nonzero saturated coefficient by the vanishing partition is algebraically
invalid: there is no quotient which reconstructs it by multiplication with that partition. -/
theorem no_normalized_covariance_at_divisor {q : ℝ} (hq : q ≠ 0) :
    ¬∃ normalized : ℝ,
      (saturatedDivisorMatrix 0 q).det * normalized =
        (saturatedDivisorMatrix 1 q).det := by
  rintro ⟨normalized, hnormalized⟩
  simp only [saturatedDivisorMatrix_det, zero_mul, one_mul] at hnormalized
  exact hq hnormalized.symm

/-- After saturation, positivity is exactly the direct sign of the physical zero-mode pairing. -/
theorem direct_crossing_sign_after_saturation {t q : ℝ} (ht : 0 < t) :
    0 < (saturatedDivisorMatrix t q).det ↔ 0 < q := by
  rw [saturatedDivisorMatrix_det]
  exact (mul_pos_iff_of_pos_left ht)

/-- Exact finite content of `cor:SMQG-zero-positivity-order`: the zero mode must first be saturated,
the resulting kernel/cokernel coefficient is nonzero and carries its direct crossing sign, and it
cannot be normalized by the vanishing partition. -/
theorem divisor_safe_positivity_order {q : ℝ} (hq : q ≠ 0) :
    (saturatedDivisorMatrix 0 q).det = 0 ∧
    (saturatedDivisorMatrix 1 q).det = q ∧
    (saturatedDivisorMatrix 1 q).det ≠ 0 ∧
    (∀ t, 0 < t →
      (0 < (saturatedDivisorMatrix t q).det ↔ 0 < q)) ∧
    ¬∃ normalized : ℝ,
      (saturatedDivisorMatrix 0 q).det * normalized =
        (saturatedDivisorMatrix 1 q).det := by
  exact ⟨(zero_mode_saturation_first_nonzero hq).1,
    (zero_mode_saturation_first_nonzero hq).2.1,
    (zero_mode_saturation_first_nonzero hq).2.2,
    fun _ ht => direct_crossing_sign_after_saturation ht,
    no_normalized_covariance_at_divisor hq⟩

end NCG.SMQGDivisorSafePositivityOrder
