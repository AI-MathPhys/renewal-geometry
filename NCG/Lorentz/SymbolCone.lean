/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Frozen-symbol and cone convergence (Lipschitz core)

**Proposition `prop:joint-symbol-cone`**: as the second-moment fields
converge, the frozen symbols and their null cones converge.  The core
proved here: the quadratic form of a matrix depends Lipschitz-ly on
the coefficients — an entrywise `K`-perturbation moves the form on a
bounded set by at most `d²·K·M²` (`NCG.quadratic_form_lipschitz`).
With the proved scalar symbol square, the characteristic variety is
the zero set of this quadratic form, so cone convergence follows from
coefficient convergence; the locally uniform packaging is the noted
step.
-/

namespace NCG

/-- **Proposition `prop:joint-symbol-cone` (Lipschitz core)**: the
quadratic form depends Lipschitz-continuously on the coefficient
matrix: an entrywise `K`-perturbation moves `ξᵀMξ` on the box
`|ξᵢ| ≤ M₀` by at most `d²·K·M₀²`. -/
theorem quadratic_form_lipschitz {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (K M₀ : ℝ) (hK0 : 0 ≤ K) (hM0 : 0 ≤ M₀)
    (hK : ∀ i j, |A i j - B i j| ≤ K) (hx : ∀ i, |x i| ≤ M₀) :
    |x ⬝ᵥ A.mulVec x - x ⬝ᵥ B.mulVec x| ≤ (d^2 : ℕ) * K * M₀^2 := by
  have hdiff : x ⬝ᵥ A.mulVec x - x ⬝ᵥ B.mulVec x
      = ∑ i, ∑ j, x i * ((A i j - B i j) * x j) := by
    rw [dotProduct, dotProduct, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
      ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hdiff]
  calc |∑ i, ∑ j, x i * ((A i j - B i j) * x j)|
      ≤ ∑ i, |∑ j, x i * ((A i j - B i j) * x j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * ((A i j - B i j) * x j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, M₀ * (K * M₀) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hx i)
          (mul_le_mul (hK i j) (hx j) (abs_nonneg _) hK0)
          (by positivity) hM0
    _ = (d^2 : ℕ) * K * M₀^2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

end NCG
