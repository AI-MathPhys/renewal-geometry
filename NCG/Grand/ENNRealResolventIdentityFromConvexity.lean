/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SharpStrongConvexMinimizerGap

/-!
# Resolvent identities from convex minimizers

For a convex extended form, the minimizing property at every positive shift already forces the
second resolvent identity.  Thus the identity need not be supplied as separate model data.
-/

open scoped ENNReal

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ K E]

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ K E] in
/-- Changing the positive quadratic coefficient and shifting the source changes an objective gap
by exactly the corresponding multiple of the squared distance. -/
theorem resolventObjective_sourceShift_sub
    (q : E → ℝ) (a b : ℝ) (f y z : E) :
    resolventObjective (K := K) q a
          (f + (((a - b : ℝ) : K)) • y) z -
        resolventObjective (K := K) q a
          (f + (((a - b : ℝ) : K)) • y) y =
      (resolventObjective (K := K) q b f z -
        resolventObjective (K := K) q b f y) +
        (a - b) * ‖z - y‖ ^ 2 := by
  simp only [resolventObjective, inner_add_right, inner_smul_real_right]
  simp only [map_add, RCLike.smul_re]
  rw [← norm_sq_eq_re_inner (𝕜 := K) y]
  rw [norm_sub_sq (𝕜 := K)]
  ring

/-- Convexity and positive-shift minimizing properties imply the source-transform form of the
resolvent identity. -/
theorem realResolvent_sourceTransform_of_convexMinimizers
    (q : E → ℝ≥0∞) (T : ℝ → E →L[K] E)
    (hconvex : ConvexOn ℝ {z : E | q z ≠ ∞} (fun z ↦ (q z).toReal))
    (hfinite : ∀ lam, 0 < lam → ∀ f : E, q (T lam f) ≠ ∞)
    (hmin : ∀ lam, 0 < lam → ∀ (f z : E), q z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f (T lam f) ≤
        resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f z)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : E) :
    T a (f + (((a - b : ℝ) : K)) • T b f) = T b f := by
  let s : Set E := {z : E | q z ≠ ∞}
  let qreal : E → ℝ := fun z ↦ (q z).toReal
  let y : E := T b f
  let g : E := f + (((a - b : ℝ) : K)) • y
  have hy : y ∈ s := hfinite b hb f
  have hyMin : ∀ z ∈ s,
      resolventObjective (K := K) qreal b f y ≤
        resolventObjective (K := K) qreal b f z := by
    intro z hz
    exact hmin b hb f z hz
  have hyShiftMin : ∀ z ∈ s,
      resolventObjective (K := K) qreal a g y ≤
        resolventObjective (K := K) qreal a g z := by
    intro z hz
    have hgap := sharp_objective_gap_on_of_strongConvexOn
      (resolventObjective (K := K) qreal b f) (2 * b)
      (mul_nonneg (by norm_num) hb.le)
      (resolventObjective_strongConvexOn_subset s qreal hconvex b f)
      y z hy hz hyMin
    have htransport := resolventObjective_sourceShift_sub
      (K := K) qreal a b f y z
    dsimp [g] at htransport ⊢
    have hnorm : ‖y - z‖ ^ 2 = ‖z - y‖ ^ 2 := by
      rw [norm_sub_rev]
    nlinarith [mul_nonneg ha.le (sq_nonneg ‖z - y‖)]
  have hTaFinite : T a g ∈ s := hfinite a ha g
  have hTaMin : ∀ z ∈ s,
      resolventObjective (K := K) qreal a g (T a g) ≤
        resolventObjective (K := K) qreal a g z := by
    intro z hz
    exact hmin a ha g z hz
  have heq : y = T a g := resolventObjective_unique_minimizerOn
    s qreal hconvex a ha g (T a g) hTaFinite hTaMin y hy (hyShiftMin _ hTaFinite)
  exact heq.symm

/-- The second resolvent identity is automatic for the positive-shift minimizers of a convex
extended form. -/
theorem realSecondResolventIdentity_of_convexMinimizers
    (q : E → ℝ≥0∞) (T : ℝ → E →L[K] E)
    (hconvex : ConvexOn ℝ {z : E | q z ≠ ∞} (fun z ↦ (q z).toReal))
    (hfinite : ∀ lam, 0 < lam → ∀ f : E, q (T lam f) ≠ ∞)
    (hmin : ∀ lam, 0 < lam → ∀ (f z : E), q z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f (T lam f) ≤
        resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f z)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    T a - T b = (((b - a : ℝ) : K)) • ((T a).comp (T b)) := by
  apply ContinuousLinearMap.ext
  intro f
  have hsource := realResolvent_sourceTransform_of_convexMinimizers
    q T hconvex hfinite hmin a b ha hb f
  simp only [map_add, map_smul] at hsource
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply]
  have hdiff :
      T a f - T b f = -((((a - b : ℝ) : K)) • T a (T b f)) := by
    calc
      T a f - T b f = T a f -
          (T a f + (((a - b : ℝ) : K)) • T a (T b f)) :=
        congrArg (fun w ↦ T a f - w) hsource.symm
      _ = -((((a - b : ℝ) : K)) • T a (T b f)) := by abel
  calc
    T a f - T b f = -((((a - b : ℝ) : K)) • T a (T b f)) := hdiff
    _ = (((b - a : ℝ) : K)) • T a (T b f) := by
      rw [← neg_smul]
      congr 1
      push_cast
      ring

end NCG.VaryingHilbert
