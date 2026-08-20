/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventDenseRange
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positivity of weak graph resolvents

At a nonnegative shift, the weak graph-resolvent equation identifies the resolvent quadratic form
with the sum of the graph energy and the shifted ambient norm.  It is therefore nonnegative.
Together with the symmetry recovered from imaginary test vectors, this proves positivity of the
bounded resolvent operator.
-/

noncomputable section

namespace NCG.VaryingHilbert

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The weak graph equation at the resolvent vector gives a nonnegative resolvent quadratic form
at every nonnegative shift. -/
theorem operatorGraphResolvent_re_inner_nonneg
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 ≤ lam) (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f))
    (f : E) :
    0 ≤ RCLike.re (inner ℂ (R f) f) := by
  let xD : D := ⟨R f, (hequation f).mem⟩
  have h := (hequation f).weakEuler xD
  change RCLike.re (inner ℂ (A xD) (A xD)) +
      lam * RCLike.re (inner ℂ (xD : E) (xD : E)) =
    RCLike.re (inner ℂ (xD : E) f) at h
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ) (A xD),
    ← norm_sq_eq_re_inner (𝕜 := ℂ) (xD : E)] at h
  rw [← h]
  exact add_nonneg (sq_nonneg _) (mul_nonneg hlam (sq_nonneg _))

/-- Every weak graph resolvent at a nonnegative shift is a positive bounded operator. -/
theorem operatorGraphResolvent_isPositive
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 ≤ lam) (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    R.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro f
  have hsymm : (R : E →ₗ[ℂ] E).IsSymmetric :=
    operatorGraphResolvent_isSymmetric D A lam R hequation
  constructor
  · exact hsymm.coe_reApplyInnerSelf_apply f
  · exact operatorGraphResolvent_re_inner_nonneg D A lam hlam R hequation f

end NCG.VaryingHilbert
