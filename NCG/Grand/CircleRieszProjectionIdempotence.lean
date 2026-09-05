/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CircleRieszProjectionEigenvector
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Circle Riesz projection idempotence

The exact inside/outside residue formulas make a circle Riesz operator idempotent whenever the
eigenspaces of the underlying operator have dense algebraic sum.  The compact self-adjoint
spectral theorem supplies precisely that density, so compact self-adjoint Riesz operators are
idempotent without an additional functional-calculus hypothesis.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Dense spanning by eigenspaces and contour separation imply idempotence of the circle Riesz
operator. -/
theorem circleRieszProjection_isIdempotentElem_of_dense_eigenspaces
    (T : E →L[ℂ] E)
    (hdense : Dense
      (((⨆ μ, Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ E) : Set E))
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsIdempotentElem (circleRieszProjection T center radius).toLinearMap := by
  let P : E →L[ℂ] E := circleRieszProjection T center radius
  let S : Submodule ℂ E := ⨆ μ, Module.End.eigenspace T.toLinearMap μ
  have hEqOn : Set.EqOn (fun x ↦ P (P x)) P (S : Set E) := by
    intro x hx
    change x ∈ ⨆ μ, Module.End.eigenspace T.toLinearMap μ at hx
    refine Submodule.iSup_induction
      (motive := fun x ↦ P (P x) = P x)
      (fun μ ↦ Module.End.eigenspace T.toLinearMap μ) hx ?_ ?_ ?_
    · intro μ x hx
      by_cases hxzero : x = 0
      · simp [hxzero]
      have heigen : T x = μ • x := Module.End.mem_eigenspace_iff.mp hx
      have hnotSphere : μ ∉ Metric.sphere center radius := by
        intro hμsphere
        have hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) μ - T) :=
          hcontour μ hμsphere
        have hkill : (algebraMap ℂ (E →L[ℂ] E) μ - T) x = 0 := by
          simp [heigen]
        have hunitkill : (↑hu.unit : E →L[ℂ] E) x = 0 := by
          simpa using hkill
        apply hxzero
        calc
          x = ((↑hu.unit⁻¹ : E →L[ℂ] E) * (↑hu.unit : E →L[ℂ] E)) x := by
            rw [hu.unit.inv_mul]
            rfl
          _ = (↑hu.unit⁻¹ : E →L[ℂ] E) ((↑hu.unit : E →L[ℂ] E) x) := rfl
          _ = 0 := by rw [hunitkill]; simp
      by_cases hμball : μ ∈ Metric.ball center radius
      · have hfix : P x = x :=
          circleRieszProjection_apply_eigenvector_of_mem_ball
            T center μ radius x hμball hcontour heigen
        rw [hfix, hfix]
      · have hμoutside : μ ∉ Metric.closedBall center radius := by
          intro hμclosed
          have hle : dist μ center ≤ radius := Metric.mem_closedBall.mp hμclosed
          have hge : radius ≤ dist μ center :=
            le_of_not_gt (fun hlt ↦ hμball (Metric.mem_ball.mpr hlt))
          exact hnotSphere (Metric.mem_sphere.mpr (hle.antisymm hge))
        have hzero : P x = 0 :=
          circleRieszProjection_apply_eigenvector_of_not_mem_closedBall
            T center μ radius x hR hμoutside hcontour heigen
        rw [hzero, map_zero]
    · simp
    · intro x y hx hy
      simp only [map_add, hx, hy]
  have hdenseS : Dense (S : Set E) := by
    simpa [S] using hdense
  have hfun : (fun x ↦ P (P x)) = P :=
    Continuous.ext_on hdenseS (P.continuous.comp P.continuous) P.continuous hEqOn
  change P.toLinearMap * P.toLinearMap = P.toLinearMap
  ext x
  exact congrFun hfun x

/-- The circle Riesz operator of a compact self-adjoint operator is idempotent. -/
theorem circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator T)
    (hT : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsIdempotentElem (circleRieszProjection T center radius).toLinearMap := by
  let S : Submodule ℂ E := ⨆ μ, Module.End.eigenspace T.toLinearMap μ
  have horth : Sᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hT
  have hclosure : S.topologicalClosure = ⊤ := by
    rw [← S.orthogonal_orthogonal_eq_closure, horth]
    exact Submodule.bot_orthogonal_eq_top
  have hdense : Dense (S : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosure
  exact circleRieszProjection_isIdempotentElem_of_dense_eigenspaces
    T hdense center radius hR hcontour

end NCG.ResolventStability
