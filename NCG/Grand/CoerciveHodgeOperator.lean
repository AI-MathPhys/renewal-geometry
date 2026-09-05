/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Coercive covariant Hodge operators

For a bounded covariant derivative `D` and a coercive fibre metric `G`, this
module identifies the kernel of `D† G D` exactly with the parallel kernel of
`D`, and transports a Poincaré floor through the metric coercivity constant.
-/

noncomputable section

namespace NCG

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]
  [CompleteSpace F]

/-- The metric-weighted Hodge quadratic form associated with `D` and `G`.
The inner-product orientation matches the adjoint identity directly. -/
def coerciveHodgeForm (D : E →L[K] F) (G : F →L[K] F) (v : E) : ℝ :=
  RCLike.re (inner K (G (D v)) (D v))

/-- The bounded Hodge operator `D† G D`. -/
def coerciveHodgeOperator (D : E →L[K] F) (G : F →L[K] F) :
    E →L[K] E :=
  D.adjoint.comp (G.comp D)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Coercivity makes the weighted quadratic form vanish exactly on the
covariantly parallel vectors. -/
theorem coerciveHodgeForm_eq_zero_iff
    (D : E →L[K] F) (G : F →L[K] F) (gmin : ℝ) (hgmin : 0 < gmin)
    (hG : ∀ y : F, gmin * ‖y‖ ^ 2 ≤ RCLike.re (inner K (G y) y))
    (v : E) :
    coerciveHodgeForm D G v = 0 ↔ D v = 0 := by
  constructor
  · intro hq
    have hle := hG (D v)
    rw [← coerciveHodgeForm, hq] at hle
    have hnorm : ‖D v‖ = 0 := by
      by_contra hne
      have hn : 0 < ‖D v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have hp : 0 < gmin * ‖D v‖ ^ 2 := mul_pos hgmin (sq_pos_of_pos hn)
      exact (not_lt_of_ge hle) hp
    exact norm_eq_zero.mp hnorm
  · intro hDv
    simp [coerciveHodgeForm, hDv]

/-- Pointwise kernel identification for the Hodge operator. -/
theorem coerciveHodgeOperator_apply_eq_zero_iff
    (D : E →L[K] F) (G : F →L[K] F) (gmin : ℝ) (hgmin : 0 < gmin)
    (hG : ∀ y : F, gmin * ‖y‖ ^ 2 ≤ RCLike.re (inner K (G y) y))
    (v : E) :
    coerciveHodgeOperator D G v = 0 ↔ D v = 0 := by
  constructor
  · intro hLv
    apply (coerciveHodgeForm_eq_zero_iff D G gmin hgmin hG v).mp
    have hinner : inner K (coerciveHodgeOperator D G v) v =
        inner K (G (D v)) (D v) := by
      simp only [coerciveHodgeOperator, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_left]
    rw [hLv, inner_zero_left] at hinner
    simpa [coerciveHodgeForm] using congrArg RCLike.re hinner.symm
  · intro hDv
    simp [coerciveHodgeOperator, hDv]

/-- Submodule form of the exact kernel identification. -/
theorem coerciveHodgeOperator_ker_eq
    (D : E →L[K] F) (G : F →L[K] F) (gmin : ℝ) (hgmin : 0 < gmin)
    (hG : ∀ y : F, gmin * ‖y‖ ^ 2 ≤ RCLike.re (inner K (G y) y)) :
    LinearMap.ker (coerciveHodgeOperator D G : E →ₗ[K] E) =
      LinearMap.ker (D : E →ₗ[K] F) := by
  ext v
  simp only [LinearMap.mem_ker]
  exact coerciveHodgeOperator_apply_eq_zero_iff D G gmin hgmin hG v

omit [CompleteSpace E] [CompleteSpace F] in
/-- A covariant Poincaré floor transports through any nonnegative fibre
metric coercivity constant. -/
theorem coerciveHodgeForm_gap
    (D : E →L[K] F) (G : F →L[K] F)
    (gmin lambda : ℝ) (hgmin : 0 ≤ gmin)
    (hG : ∀ y : F, gmin * ‖y‖ ^ 2 ≤ RCLike.re (inner K (G y) y))
    (v : E) (hgap : lambda * ‖v‖ ^ 2 ≤ ‖D v‖ ^ 2) :
    gmin * lambda * ‖v‖ ^ 2 ≤ coerciveHodgeForm D G v := by
  calc
    gmin * lambda * ‖v‖ ^ 2 = gmin * (lambda * ‖v‖ ^ 2) := by ring
    _ ≤ gmin * ‖D v‖ ^ 2 := mul_le_mul_of_nonneg_left hgap hgmin
    _ ≤ coerciveHodgeForm D G v := hG (D v)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Exact manuscript constant on the protected-parallel complement. -/
theorem coerciveHodgeForm_gap_176_div_225
    (D : E →L[K] F) (G : F →L[K] F) (lambda : ℝ)
    (hG : ∀ y : F, (176 / 225 : ℝ) * ‖y‖ ^ 2 ≤
      RCLike.re (inner K (G y) y))
    (v : E) (hgap : lambda * ‖v‖ ^ 2 ≤ ‖D v‖ ^ 2) :
    (176 / 225 : ℝ) * lambda * ‖v‖ ^ 2 ≤
      coerciveHodgeForm D G v := by
  apply coerciveHodgeForm_gap D G (176 / 225) lambda (by norm_num) hG v hgap

end NCG
