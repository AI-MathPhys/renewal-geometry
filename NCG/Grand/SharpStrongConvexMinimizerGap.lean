/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RestrictedResolventObjectiveStrongConvexity

/-!
# Sharp gap above a strongly convex minimizer

The midpoint estimate loses a factor two.  Letting an arbitrary convex weight tend to one
recovers the sharp `m / 2` quadratic gap, without differentiability assumptions.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A minimizer of an `m`-strongly convex function has the sharp quadratic objective gap
`m / 2 * ‖x - y‖²`. -/
theorem sharp_objective_gap_on_of_strongConvexOn
    {s : Set E} (F : E → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hstrong : StrongConvexOn s m F)
    (x y : E) (hx : x ∈ s) (hy : y ∈ s)
    (hmin : ∀ z ∈ s, F x ≤ F z) :
    m / 2 * ‖x - y‖ ^ 2 ≤ F y - F x := by
  have hgapNonneg : 0 ≤ F y - F x := sub_nonneg.mpr (hmin y hy)
  have hX : 0 ≤ m / 2 * ‖x - y‖ ^ 2 :=
    mul_nonneg (div_nonneg hm (by norm_num)) (sq_nonneg ‖x - y‖)
  have hweighted : ∀ a : ℝ, a < 1 →
      a * (m / 2 * ‖x - y‖ ^ 2) ≤ F y - F x := by
    intro a ha
    by_cases ha0 : 0 ≤ a
    · have hba : 0 < 1 - a := sub_pos.mpr ha
      have hconv := hstrong.2 hx hy ha0 hba.le (by ring)
      have hmidMem : a • x + (1 - a) • y ∈ s :=
        hstrong.1 hx hy ha0 hba.le (by ring)
      have hxmin : F x ≤ F (a • x + (1 - a) • y) :=
        hmin _ hmidMem
      simp only [smul_eq_mul] at hconv
      nlinarith [mul_pos hba (show 0 < 1 - a from hba)]
    · have haNonpos : a ≤ 0 := le_of_not_ge ha0
      simpa [mul_comm] using (mul_nonpos_of_nonneg_of_nonpos hX haNonpos).trans hgapNonneg
  by_contra hsharp
  have hlt : F y - F x < m / 2 * ‖x - y‖ ^ 2 := lt_of_not_ge hsharp
  have hXpos : 0 < m / 2 * ‖x - y‖ ^ 2 := lt_of_le_of_lt hgapNonneg hlt
  let a := ((F y - F x) + m / 2 * ‖x - y‖ ^ 2) /
    (2 * (m / 2 * ‖x - y‖ ^ 2))
  have hdenPos : 0 < 2 * (m / 2 * ‖x - y‖ ^ 2) := mul_pos (by norm_num) hXpos
  have ha : a < 1 := by
    dsimp [a]
    rw [div_lt_one hdenPos]
    nlinarith
  have haX : F y - F x < a * (m / 2 * ‖x - y‖ ^ 2) := by
    have hcancel :
        (((F y - F x) + m / 2 * ‖x - y‖ ^ 2) /
            (2 * (m / 2 * ‖x - y‖ ^ 2))) * (m / 2 * ‖x - y‖ ^ 2) =
          ((F y - F x) + m / 2 * ‖x - y‖ ^ 2) / 2 := by
      rw [div_mul_eq_mul_div]
      exact mul_div_mul_right _ _ (ne_of_gt hXpos)
    dsimp [a]
    rw [hcancel]
    nlinarith
  exact (not_lt_of_ge (hweighted a ha)) haX

end NCG.VaryingHilbert
