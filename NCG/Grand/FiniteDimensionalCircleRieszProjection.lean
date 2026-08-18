/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CircleRieszProjectionEigenvector
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Finite-dimensional circle Riesz projections

For a symmetric operator in finite dimension, the eigenspaces span the whole Hilbert space.
The exact inside/outside residue formulas therefore imply directly that the circle Riesz
operator is idempotent whenever its contour avoids the spectrum.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The circle Riesz operator of a finite-dimensional symmetric operator is idempotent. -/
theorem circleRieszProjection_isIdempotentElem_of_isSymmetric
    (T : E →L[ℂ] E) (hT : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsIdempotentElem (circleRieszProjection T center radius).toLinearMap := by
  let P : E →L[ℂ] E := circleRieszProjection T center radius
  have hspan :
      (⨆ μ, Module.End.eigenspace T.toLinearMap μ) = (⊤ : Submodule ℂ E) :=
    Submodule.orthogonal_eq_bot_iff.mp
      hT.orthogonalComplement_iSup_eigenspaces_eq_bot
  change P.toLinearMap * P.toLinearMap = P.toLinearMap
  ext x
  change P (P x) = P x
  have hxspan : x ∈ ⨆ μ, Module.End.eigenspace T.toLinearMap μ := by
    rw [hspan]
    exact Submodule.mem_top
  refine Submodule.iSup_induction
    (motive := fun x ↦ P (P x) = P x)
    (fun μ ↦ Module.End.eigenspace T.toLinearMap μ) hxspan ?_ ?_ ?_
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
          T center μ radius x hμball hcontour
            heigen
      rw [hfix, hfix]
    · have hμoutside : μ ∉ Metric.closedBall center radius := by
        intro hμclosed
        have hle : dist μ center ≤ radius := Metric.mem_closedBall.mp hμclosed
        have hge : radius ≤ dist μ center :=
          le_of_not_gt (fun hlt ↦ hμball (Metric.mem_ball.mpr hlt))
        exact hnotSphere (Metric.mem_sphere.mpr (hle.antisymm hge))
      have hzero : P x = 0 :=
        circleRieszProjection_apply_eigenvector_of_not_mem_closedBall
          T center μ radius x hR hμoutside hcontour
              heigen
      rw [hzero, map_zero]
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]

end NCG.ResolventStability
