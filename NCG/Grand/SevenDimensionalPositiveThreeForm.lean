/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HigherDimensionalCrossProductBoundary
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Seven-dimensional cross products and positive three-forms

This module makes the `G₂` stabilizer clause of the higher-dimensional
boundary theorem exact.  A positive three-form is carried together with the
metric cross product that induces it.  Its stabilizer among orientation-free
linear isometries is proved to be exactly the cross-product stabilizer.
-/

namespace NCG.SevenDimensionalCrossProduct

/-- The Euclidean seven-dimensional carrier. -/
abbrev W7 := EuclideanSpace ℝ (Fin 7)

/-- A metric vector cross product on the seven-dimensional carrier. -/
structure MetricCrossProduct where
  cross : W7 →ₗ[ℝ] W7 →ₗ[ℝ] W7
  alternating : ∀ x, cross x x = 0
  orthogonal_left : ∀ x y, inner ℝ (cross x y) x = 0
  orthogonal_right : ∀ x y, inner ℝ (cross x y) y = 0
  norm_sq : ∀ x y,
    ‖cross x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2

/-- The three-form induced by a metric cross product. -/
noncomputable def inducedThreeForm (X : MetricCrossProduct) (x y z : W7) : ℝ :=
  inner ℝ (X.cross x y) z

/-- A protected positive stable three-form, represented by the metric cross
product that induces it.  This is the standard positive-orbit description
used for `G₂` structures. -/
structure PositiveStableThreeForm where
  form : W7 → W7 → W7 → ℝ
  crossProduct : MetricCrossProduct
  form_eq : ∀ x y z, form x y z = inducedThreeForm crossProduct x y z

/-- Every seven-dimensional metric cross product canonically supplies its
protected positive three-form. -/
noncomputable def MetricCrossProduct.positiveStableThreeForm (X : MetricCrossProduct) :
    PositiveStableThreeForm where
  form := inducedThreeForm X
  crossProduct := X
  form_eq := by intros; rfl

/-- Isometric symmetries preserving a metric cross product.  This is the
compact `G₂` stabilizer in its seven-dimensional representation. -/
def PreservesCrossProduct (X : MetricCrossProduct)
    (A : W7 ≃ₗᵢ[ℝ] W7) : Prop :=
  ∀ x y, A (X.cross x y) = X.cross (A x) (A y)

/-- Isometric symmetries preserving the induced positive three-form. -/
def PreservesThreeForm (φ : W7 → W7 → W7 → ℝ)
    (A : W7 ≃ₗᵢ[ℝ] W7) : Prop :=
  ∀ x y z, φ (A x) (A y) (A z) = φ x y z

/-- The isometric stabilizer of the induced positive three-form is exactly
the cross-product stabilizer (`G₂`). -/
theorem preserves_inducedThreeForm_iff_preservesCrossProduct
    (X : MetricCrossProduct) (A : W7 ≃ₗᵢ[ℝ] W7) :
    PreservesThreeForm (inducedThreeForm X) A ↔
      PreservesCrossProduct X A := by
  constructor
  · intro hφ x y
    apply ext_inner_right ℝ
    intro w
    obtain ⟨z, rfl⟩ := A.surjective w
    calc
      inner ℝ (A (X.cross x y)) (A z) = inner ℝ (X.cross x y) z := by
        exact A.inner_map_map (X.cross x y) z
      _ = inner ℝ (X.cross (A x) (A y)) (A z) := by
        exact (hφ x y z).symm
  · intro hX x y z
    simp only [inducedThreeForm]
    rw [← hX x y]
    exact A.inner_map_map (X.cross x y) z

/-- Stabilizer equality for a protected positive stable three-form. -/
theorem positiveStableThreeForm_stabilizer_iff_G2
    (Φ : PositiveStableThreeForm) (A : W7 ≃ₗᵢ[ℝ] W7) :
    PreservesThreeForm Φ.form A ↔
      PreservesCrossProduct Φ.crossProduct A := by
  rw [show Φ.form = inducedThreeForm Φ.crossProduct by
    funext x y z
    exact Φ.form_eq x y z]
  exact preserves_inducedThreeForm_iff_preservesCrossProduct Φ.crossProduct A

end NCG.SevenDimensionalCrossProduct
