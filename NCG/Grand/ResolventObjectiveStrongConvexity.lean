/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertResolventObjective
import NCG.Grand.CoerciveObjectiveStrongConvergence
import Mathlib.Analysis.Convex.Strong

/-!
# Strong convexity of resolvent objectives

Adding a positive squared-norm penalty to a convex quadratic form makes the full resolvent
objective strongly convex.  The moving source term is real-linear and therefore does not alter
the convexity modulus.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ K H]

/-- A convex form gives a `2 * lam`-strongly convex resolvent objective. -/
theorem resolventObjective_strongConvexOn
    (q : H → ℝ) (hq : ConvexOn ℝ univ q) (lam : ℝ) (f : H) :
    StrongConvexOn univ (2 * lam) (resolventObjective (K := K) q lam f) := by
  rw [strongConvexOn_iff_convex]
  constructor
  · exact convex_univ
  intro x _hx y _hy a b ha hb hab
  have hqxy := hq.2 (mem_univ x) (mem_univ y) ha hb hab
  rw [← algebraMap_smul K a x, ← algebraMap_smul K b y]
  simp only [resolventObjective, inner_add_left, inner_smul_real_left,
    smul_eq_mul]
  simp only [smul_eq_mul] at hqxy
  rw [map_add, RCLike.smul_re, RCLike.smul_re]
  norm_num
  nlinarith

/-- A convex form and positive resolvent shift make every global minimizer unique. -/
theorem resolventObjective_unique_minimizer
    (q : H → ℝ) (hq : ConvexOn ℝ univ q)
    (lam : ℝ) (hlam : 0 < lam) (f x : H)
    (hmin : ∀ z, resolventObjective (K := K) q lam f x ≤
      resolventObjective (K := K) q lam f z)
    (y : H) (hy : resolventObjective (K := K) q lam f y ≤
      resolventObjective (K := K) q lam f x) :
    y = x := by
  apply System.eq_minimizer_of_strongConvexOn
    (resolventObjective (K := K) q lam f) (2 * lam)
    (mul_pos (by norm_num) hlam)
    (resolventObjective_strongConvexOn q hq lam f)
    x hmin y hy

end NCG.VaryingHilbert
