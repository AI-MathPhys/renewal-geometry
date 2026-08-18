/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventObjectiveStrongConvexity

/-!
# Strong convexity of resolvent objectives on effective domains

Extended-valued forms are real-valued only on their effective domains.  These lemmas keep all
convexity, gap, and uniqueness arguments on an arbitrary convex subset rather than extending a
`toReal` surrogate to the whole ambient space.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ K H]

/-- A convex form on a convex subset gives a strongly convex resolvent objective on that same
subset. -/
theorem resolventObjective_strongConvexOn_subset
    (s : Set H) (q : H → ℝ) (hq : ConvexOn ℝ s q)
    (lam : ℝ) (f : H) :
    StrongConvexOn s (2 * lam) (resolventObjective (K := K) q lam f) := by
  rw [strongConvexOn_iff_convex]
  constructor
  · exact hq.1
  intro x hx y hy a b ha hb hab
  have hqxy := hq.2 hx hy ha hb hab
  rw [← algebraMap_smul K a x, ← algebraMap_smul K b y]
  simp only [resolventObjective, inner_add_left, inner_smul_real_left,
    smul_eq_mul]
  simp only [smul_eq_mul] at hqxy
  rw [map_add, RCLike.smul_re, RCLike.smul_re]
  norm_num
  nlinarith

/-- Strong convexity on a domain supplies a quantitative gap above a domain minimizer. -/
theorem coercive_objective_gap_on_of_strongConvexOn
    {s : Set H} (F : H → ℝ) (m : ℝ)
    (hstrong : StrongConvexOn s m F)
    (x y : H) (hx : x ∈ s) (hy : y ∈ s)
    (hmin : ∀ z ∈ s, F x ≤ F z) :
    m / 4 * ‖x - y‖ ^ 2 ≤ F y - F x := by
  have hmid := hstrong.2 hx hy
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hmidMem : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ s :=
    hstrong.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have hxmin : F x ≤ F ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) :=
    hmin _ hmidMem
  simp only [smul_eq_mul] at hmid
  nlinarith [sq_nonneg ‖x - y‖]

/-- A positive strongly convex functional has at most one minimizer inside its domain. -/
theorem eq_minimizer_on_of_strongConvexOn
    {s : Set H} (F : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hstrong : StrongConvexOn s m F)
    (x : H) (hx : x ∈ s) (hmin : ∀ z ∈ s, F x ≤ F z)
    (y : H) (hy : y ∈ s) (hyx : F y ≤ F x) :
    y = x := by
  have hgap := coercive_objective_gap_on_of_strongConvexOn
    F m hstrong x y hx hy hmin
  have hsquare : ‖x - y‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖x - y‖]
  have hnorm : ‖x - y‖ = 0 := (sq_eq_zero_iff).mp hsquare
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

/-- A positive-shift resolvent objective has a unique minimizer on any convex effective domain. -/
theorem resolventObjective_unique_minimizerOn
    (s : Set H) (q : H → ℝ) (hq : ConvexOn ℝ s q)
    (lam : ℝ) (hlam : 0 < lam) (f x : H)
    (hx : x ∈ s)
    (hmin : ∀ z ∈ s, resolventObjective (K := K) q lam f x ≤
      resolventObjective (K := K) q lam f z)
    (y : H) (hy : y ∈ s)
    (hyx : resolventObjective (K := K) q lam f y ≤
      resolventObjective (K := K) q lam f x) :
    y = x := by
  apply eq_minimizer_on_of_strongConvexOn
    (resolventObjective (K := K) q lam f) (2 * lam)
    (mul_pos (by norm_num) hlam)
    (resolventObjective_strongConvexOn_subset s q hq lam f)
    x hx hmin y hy hyx

end NCG.VaryingHilbert
