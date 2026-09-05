/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Integrated-box router and zero-mode reduction
  (`thm:GRH-integrated-zero-mode`,
  Gran-Tensor manuscript)

* `grh_integrated_zero_mode_dispersion`: the boxed router
  dispersion — for positive weights `aⱼ` and phase sources
  `bⱼ` in a real inner-product space (covering the complex
  scalar case as `ℝ²`),
  `∑ⱼ ‖bⱼ‖²/aⱼ - ‖∑b‖²/∑a = ∑ⱼ aⱼ‖bⱼ/aⱼ - K‖² ≥ 0` with
  the pooled router `K = (∑a)⁻¹∑b`: the short of the
  assembled complete Gram is not the sum of the pointwise
  shorts (the scalar law of total variance / router
  dispersion for the accepted energy partition).

The operator clause — the predictable mixed energy bound
`D_X^pred ≤ ‖Z*P₀Z‖` through the zero-mode projection of
the accepted contraction, and the arithmetic loading
identifying `B_X` with the completed Euler endpoint at
scale `A_X = X^{1+o(1)}` — is the manuscript's
representation layer; its zero-mode mechanism (a co-fixed
source reads only `P₀`) is proved as
`NCG.gt_fixed_coboundary` (iv).
-/

open scoped InnerProductSpace
open Finset

namespace NCG

/-- `thm:GRH-integrated-zero-mode` (the boxed router
dispersion). -/
theorem grh_integrated_zero_mode_dispersion {ι : Type}
    [Fintype ι] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    (a : ι → ℝ) (b : ι → V) (ha : ∀ j, 0 < a j)
    (hne : Nonempty ι) :
    ∑ j, ‖b j‖ ^ 2 / a j
        - ‖∑ j, b j‖ ^ 2 / (∑ j, a j)
      = ∑ j, a j * ‖(a j)⁻¹ • b j
          - (∑ i, a i)⁻¹ • ∑ i, b i‖ ^ 2 := by
  have hA : 0 < ∑ j, a j :=
    Finset.sum_pos (fun j _ => ha j) univ_nonempty
  set K := (∑ i, a i)⁻¹ • ∑ i, b i with hK
  have hterm : ∀ j, a j * ‖(a j)⁻¹ • b j - K‖ ^ 2
      = ‖b j‖ ^ 2 / a j - 2 * ⟪b j, K⟫_ℝ
        + a j * ‖K‖ ^ 2 := by
    intro j
    have hj := ha j
    have hexp := norm_sub_sq_real ((a j)⁻¹ • b j) K
    have h1 : ‖(a j)⁻¹ • b j‖ ^ 2
        = ‖b j‖ ^ 2 / (a j) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hj), mul_pow]
      rw [inv_pow]
      field_simp
    have h2 : ⟪(a j)⁻¹ • b j, K⟫_ℝ
        = (a j)⁻¹ * ⟪b j, K⟫_ℝ :=
      real_inner_smul_left _ _ _
    rw [hexp, h1, h2]
    field_simp
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← sum_inner]
  have hIK : ⟪∑ i, b i, K⟫_ℝ
      = ‖∑ i, b i‖ ^ 2 / (∑ i, a i) := by
    rw [hK, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
  have hK2 : ‖K‖ ^ 2
      = ‖∑ i, b i‖ ^ 2 / (∑ i, a i) ^ 2 := by
    rw [hK, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hA), mul_pow, inv_pow]
    field_simp
  rw [hIK, hK2]
  field_simp
  ring

end NCG
