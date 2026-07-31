/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The exterior-power three-scale criterion
  (`thm:exterior-power-hierarchy-main`,
   `cor:nested-half-order-rank-filtration`, SM_emergence)

For ordered singular values, `‖Y‖ = s₁`, `‖Λ²Y‖ = s₁s₂`, and
`|det Y| = s₁s₂s₃` (the declared multilinear-algebra inputs).
Given the three two-sided scales

`‖Y‖ ≍ δ^{1/2}`, `‖Λ²Y‖ ≍ δ^{3/2}`, `|det Y| ≍ δ³`,

successive division yields the three-scale hierarchy:

* `sandwich_ratio` — the generic two-sided division step:
  `c·P ≤ x ≤ C·P` and `c'·Q ≤ xy ≤ C'·Q` give
  `(c'/C)(Q/P) ≤ y ≤ (C'/c)(Q/P)`;
* `exterior_power_three_scale` — hence `s₂ ≍ δ` and
  `s₃ ≍ δ^{3/2}`, so both consecutive ratios are `≍ δ^{1/2}` — the
  nested half-order rank filtration.
-/

namespace NCG

/-- Two-sided division step: if `x ≍ P` and `xy ≍ Q` with explicit
constants, then `y ≍ Q/P` with the divided constants. -/
theorem sandwich_ratio {x y P Q cx Cx cq Cq : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hP : 0 < P)
    (hcx : 0 < cx)
    (hxl : cx * P ≤ x) (hxu : x ≤ Cx * P)
    (hql : cq * Q ≤ x * y) (hqu : x * y ≤ Cq * Q) :
    (cq / Cx) * (Q / P) ≤ y ∧ y ≤ (Cq / cx) * (Q / P) := by
  have hCx : 0 < Cx := by nlinarith
  constructor
  · rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hxu hy.le]
  · rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hxl hy.le]

/-- `thm:exterior-power-hierarchy-main`: if `s₁ ≍ δ^{1/2}`,
`s₁s₂ ≍ δ^{3/2}` and `s₁s₂s₃ ≍ δ³` (the norm, exterior-square norm
and determinant scales), then `s₂ ≍ δ` and `s₃ ≍ δ^{3/2}`: both
consecutive ratios are `≍ δ^{1/2}`. -/
theorem exterior_power_three_scale
    {s1 s2 s3 delta c1 C1 c2 C2 c3 C3 : ℝ}
    (hd : 0 < delta)
    (h1 : 0 < s1) (h2 : 0 < s2) (h3 : 0 < s3)
    (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hb1l : c1 * delta ^ ((1 : ℝ) / 2) ≤ s1)
    (hb1u : s1 ≤ C1 * delta ^ ((1 : ℝ) / 2))
    (hb2l : c2 * delta ^ ((3 : ℝ) / 2) ≤ s1 * s2)
    (hb2u : s1 * s2 ≤ C2 * delta ^ ((3 : ℝ) / 2))
    (hb3l : c3 * delta ^ (3 : ℝ) ≤ s1 * s2 * s3)
    (hb3u : s1 * s2 * s3 ≤ C3 * delta ^ (3 : ℝ)) :
    ((c2 / C1) * delta ≤ s2 ∧ s2 ≤ (C2 / c1) * delta)
      ∧ ((c3 / C2) * delta ^ ((3 : ℝ) / 2) ≤ s3
        ∧ s3 ≤ (C3 / c2) * delta ^ ((3 : ℝ) / 2)) := by
  have hP1 : (0 : ℝ) < delta ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hd _
  have hP2 : (0 : ℝ) < delta ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hd _
  have hP3 : (0 : ℝ) < delta ^ (3 : ℝ) :=
    Real.rpow_pos_of_pos hd _
  have hr1 : delta ^ ((3 : ℝ) / 2) / delta ^ ((1 : ℝ) / 2)
      = delta := by
    rw [← Real.rpow_sub hd]
    norm_num
  have hr2 : delta ^ (3 : ℝ) / delta ^ ((3 : ℝ) / 2)
      = delta ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_sub hd]
    norm_num
  have hs2 := sandwich_ratio h1 h2 hP1 hc1 hb1l hb1u hb2l hb2u
  have hs3 := sandwich_ratio (by positivity : (0 : ℝ) < s1 * s2) h3
    hP2 hc2 hb2l hb2u hb3l hb3u
  rw [hr1] at hs2
  rw [hr2] at hs3
  exact ⟨hs2, hs3⟩

end NCG
