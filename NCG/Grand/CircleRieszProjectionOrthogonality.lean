/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CircleRieszProjectionIdempotence

/-!
# Orthogonality of circle Riesz projections

For a symmetric operator, a circle Riesz operator acts by either zero or the
identity on every eigenspace.  Mutual orthogonality of distinct eigenspaces
therefore makes it symmetric on their algebraic span.  If that span is dense,
continuity upgrades the Riesz idempotent to an orthogonal projection.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Dense spanning by eigenspaces makes a real spectral-cut circle Riesz
operator symmetric. -/
theorem circleRieszProjection_isSymmetric_of_dense_eigenspaces
    (T : E →L[ℂ] E) (hT : LinearMap.IsSymmetric T.toLinearMap)
    (hdense : Dense
      (((⨆ μ, Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ E) : Set E))
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    LinearMap.IsSymmetric
      (circleRieszProjection T center radius).toLinearMap := by
  classical
  let P : E →L[ℂ] E := circleRieszProjection T center radius
  let S : Submodule ℂ E := ⨆ μ, Module.End.eigenspace T.toLinearMap μ
  have hP_eigen : ∀ μ x, x ∈ Module.End.eigenspace T.toLinearMap μ →
      P x = if μ ∈ Metric.ball center radius then x else 0 := by
    intro μ x hx
    by_cases hμball : μ ∈ Metric.ball center radius
    · rw [if_pos hμball]
      exact circleRieszProjection_apply_eigenvector_of_mem_ball
        T center μ radius x hμball hcontour
          (Module.End.mem_eigenspace_iff.mp hx)
    · rw [if_neg hμball]
      by_cases hxzero : x = 0
      · simp [hxzero]
      have hnotSphere : μ ∉ Metric.sphere center radius := by
        intro hμsphere
        have hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) μ - T) :=
          hcontour μ hμsphere
        have heigen : T x = μ • x := Module.End.mem_eigenspace_iff.mp hx
        have hkill : (algebraMap ℂ (E →L[ℂ] E) μ - T) x = 0 := by
          change μ • x - T x = 0
          rw [heigen, sub_self]
        have hunitkill : (↑hu.unit : E →L[ℂ] E) x = 0 := by
          simpa using hkill
        apply hxzero
        calc
          x = ((↑hu.unit⁻¹ : E →L[ℂ] E) * (↑hu.unit : E →L[ℂ] E)) x := by
            rw [hu.unit.inv_mul]
            rfl
          _ = (↑hu.unit⁻¹ : E →L[ℂ] E) ((↑hu.unit : E →L[ℂ] E) x) := rfl
          _ = 0 := by rw [hunitkill]; simp
      have houtside : μ ∉ Metric.closedBall center radius := by
        intro hclosed
        have hle : dist μ center ≤ radius := Metric.mem_closedBall.mp hclosed
        have hge : radius ≤ dist μ center :=
          le_of_not_gt (fun hlt ↦ hμball (Metric.mem_ball.mpr hlt))
        exact hnotSphere (Metric.mem_sphere.mpr (hle.antisymm hge))
      exact circleRieszProjection_apply_eigenvector_of_not_mem_closedBall
        T center μ radius x hR houtside hcontour
          (Module.End.mem_eigenspace_iff.mp hx)
  have hsymmS : ∀ x ∈ S, ∀ y ∈ S,
      inner ℂ (P x) y = inner ℂ x (P y) := by
    intro x hx
    change x ∈ ⨆ μ, Module.End.eigenspace T.toLinearMap μ at hx
    refine Submodule.iSup_induction
      (motive := fun x ↦ ∀ y ∈ S, inner ℂ (P x) y = inner ℂ x (P y))
      (fun μ ↦ Module.End.eigenspace T.toLinearMap μ) hx ?_ ?_ ?_
    · intro μ x hx y hy
      change y ∈ ⨆ ν, Module.End.eigenspace T.toLinearMap ν at hy
      refine Submodule.iSup_induction
        (motive := fun y ↦ inner ℂ (P x) y = inner ℂ x (P y))
        (fun ν ↦ Module.End.eigenspace T.toLinearMap ν) hy ?_ ?_ ?_
      · intro ν y hy
        rw [hP_eigen μ x hx, hP_eigen ν y hy]
        by_cases hμball : μ ∈ Metric.ball center radius
        · rw [if_pos hμball]
          by_cases hνball : ν ∈ Metric.ball center radius
          · rw [if_pos hνball]
          · rw [if_neg hνball, inner_zero_right]
            have hμν : μ ≠ ν := fun h ↦ hνball (h ▸ hμball)
            exact hT.orthogonalFamily_eigenspaces hμν ⟨x, hx⟩ ⟨y, hy⟩
        · rw [if_neg hμball, inner_zero_left]
          by_cases hνball : ν ∈ Metric.ball center radius
          · rw [if_pos hνball]
            have hμν : μ ≠ ν := fun h ↦ hμball (h.symm ▸ hνball)
            exact
              (hT.orthogonalFamily_eigenspaces hμν ⟨x, hx⟩ ⟨y, hy⟩).symm
          · rw [if_neg hνball, inner_zero_right]
      · simp
      · intro y z hy hz
        simp only [map_add, inner_add_right, hy, hz]
    · simp
    · intro x y hx hy z hz
      simp only [map_add, inner_add_left, hx z hz, hy z hz]
  have hsymmLeft : ∀ x ∈ S, ∀ y,
      inner ℂ (P x) y = inner ℂ x (P y) := by
    intro x hx
    have heq : (fun y ↦ inner ℂ (P x) y) = fun y ↦ inner ℂ x (P y) :=
      Continuous.ext_on hdense
        (continuous_const.inner continuous_id)
        (continuous_const.inner P.continuous) (hsymmS x hx)
    exact fun y ↦ congrFun heq y
  intro x y
  have heq : (fun x ↦ inner ℂ (P x) y) = fun x ↦ inner ℂ x (P y) :=
    Continuous.ext_on hdense
      (P.continuous.inner continuous_const)
      (continuous_id.inner continuous_const)
      (fun x hx ↦ hsymmLeft x hx y)
  exact congrFun heq x

/-- With dense eigenspaces, a symmetric circle Riesz operator is an orthogonal
projection. -/
theorem circleRieszProjection_isStarProjection_of_dense_eigenspaces
    (T : E →L[ℂ] E) (hT : LinearMap.IsSymmetric T.toLinearMap)
    (hdense : Dense
      (((⨆ μ, Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ E) : Set E))
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsStarProjection (circleRieszProjection T center radius) := by
  apply ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection.mpr
  exact ⟨circleRieszProjection_isIdempotentElem_of_dense_eigenspaces
      T hdense center radius hR hcontour,
    circleRieszProjection_isSymmetric_of_dense_eigenspaces
      T hT hdense center radius hR hcontour⟩

/-- Every circle Riesz operator of a compact symmetric operator is an
orthogonal projection. -/
theorem circleRieszProjection_isStarProjection_of_compact_of_isSymmetric
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator T)
    (hT : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsStarProjection (circleRieszProjection T center radius) := by
  let S : Submodule ℂ E := ⨆ μ, Module.End.eigenspace T.toLinearMap μ
  have horth : Sᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hT
  have hclosure : S.topologicalClosure = ⊤ := by
    rw [← S.orthogonal_orthogonal_eq_closure, horth]
    exact Submodule.bot_orthogonal_eq_top
  have hdense : Dense (S : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosure
  exact circleRieszProjection_isStarProjection_of_dense_eigenspaces
    T hT (by simpa [S] using hdense) center radius hR hcontour

end NCG.ResolventStability

