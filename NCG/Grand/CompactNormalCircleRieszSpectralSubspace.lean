/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CircleRieszProjectionCommutation
import NCG.Grand.CompactNormalCircleRieszProjectionOrthogonality

/-!
# Spectral subspaces of compact normal circle Riesz projections

For a compact normal operator, every zero-avoiding circle Riesz projection is the orthogonal
projection onto the algebraic sum of precisely the eigenspaces enclosed by the circle. This gives
an exact, coordinate-free description of the finite-dimensional spectral subspace at every stage.
-/

open Complex Set Module End

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A compact normal operator commutes with each of its circle Riesz projections. -/
theorem circleRieszProjection_commute_of_compact_of_isStarNormal
    (T : H →L[ℂ] H) (hcompact : IsCompactOperator (T : H → H))
    (hnormal : IsStarNormal T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    Commute T (circleRieszProjection T center radius) := by
  exact circleRieszProjection_commute_of_dense_eigenspaces T
    (NCG.NormalSpectrum.dense_iSup_eigenspaces_of_compact_of_isStarNormal
      T hcompact hnormal)
    center radius hR hcontour

set_option maxHeartbeats 800000 in
-- Two nested eigenspace sums and the finite-dimensional orthogonal projection are elaboration
-- intensive, but this proof is the reusable exact spectral-subspace identification.
/-- A zero-avoiding circle Riesz projection of a compact normal operator has range equal to the
sum of exactly the eigenspaces whose eigenvalues lie in the open disc. -/
theorem range_circleRieszProjection_eq_iSup_eigenspaces_mem_ball_of_compact_of_isStarNormal
    (T : H →L[ℂ] H) (hcompact : IsCompactOperator (T : H → H))
    (hnormal : IsStarNormal T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    LinearMap.range (circleRieszProjection T center radius).toLinearMap =
      ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
        eigenspace T.toLinearMap μ := by
  let P : H →L[ℂ] H := circleRieszProjection T center radius
  let S : Submodule ℂ H :=
    ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
      eigenspace T.toLinearMap μ
  letI : FiniteDimensional ℂ (LinearMap.range P.toLinearMap) := by
    dsimp [P]
    exact finiteDimensional_range_circleRieszProjection_of_compact_of_isStarNormal
      T hcompact hnormal center radius hR hzero hcontour
  have hSle : S ≤ LinearMap.range P.toLinearMap := by
    dsimp [S]
    apply iSup_le
    intro μ
    apply iSup_le
    intro hμ x hx
    have hPx : P x = x := by
      dsimp [P]
      exact circleRieszProjection_apply_eigenvector_of_mem_ball
        T center μ radius x hμ hcontour (mem_eigenspace_iff.mp hx)
    exact ⟨x, hPx⟩
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.of_injective (Submodule.inclusion hSle)
      (fun x y hxy ↦ Subtype.ext
        (congrArg
          (fun z : LinearMap.range P.toLinearMap ↦ (z : H)) hxy))
  let Q : H →L[ℂ] H := S.starProjection
  have hEqEigen : ∀ μ : ℂ, ∀ x ∈ eigenspace T.toLinearMap μ, P x = Q x := by
    intro μ x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hnotSphere : μ ∉ Metric.sphere center radius := by
      intro hμsphere
      have hu : IsUnit (algebraMap ℂ (H →L[ℂ] H) μ - T) :=
        hcontour μ hμsphere
      have heigen : T x = μ • x := mem_eigenspace_iff.mp hx
      have hkill : (algebraMap ℂ (H →L[ℂ] H) μ - T) x = 0 := by
        simp [heigen]
      have hunitkill : (↑hu.unit : H →L[ℂ] H) x = 0 := by
        simpa using hkill
      apply hx0
      calc
        x = ((↑hu.unit⁻¹ : H →L[ℂ] H) * (↑hu.unit : H →L[ℂ] H)) x := by
          rw [hu.unit.inv_mul]
          rfl
        _ = (↑hu.unit⁻¹ : H →L[ℂ] H) ((↑hu.unit : H →L[ℂ] H) x) := rfl
        _ = 0 := by rw [hunitkill]; simp
    by_cases hμball : μ ∈ Metric.ball center radius
    · have hPx : P x = x := by
        dsimp [P]
        exact circleRieszProjection_apply_eigenvector_of_mem_ball
          T center μ radius x hμball hcontour (mem_eigenspace_iff.mp hx)
      have hxS : x ∈ S := by
        dsimp [S]
        exact (le_iSup (fun ν : ℂ ↦
          ⨆ (_ : ν ∈ Metric.ball center radius), eigenspace T.toLinearMap ν) μ)
          ((le_iSup (fun _ : μ ∈ Metric.ball center radius ↦
            eigenspace T.toLinearMap μ) hμball) hx)
      have hQx : Q x = x := by
        simpa [Q] using S.starProjection_mem_subspace_eq_self ⟨x, hxS⟩
      rw [hPx, hQx]
    · have hμoutside : μ ∉ Metric.closedBall center radius := by
        intro hμclosed
        have hle : dist μ center ≤ radius := Metric.mem_closedBall.mp hμclosed
        have hge : radius ≤ dist μ center :=
          le_of_not_gt (fun hlt ↦ hμball (Metric.mem_ball.mpr hlt))
        exact hnotSphere (Metric.mem_sphere.mpr (hle.antisymm hge))
      have hPx : P x = 0 := by
        dsimp [P]
        exact circleRieszProjection_apply_eigenvector_of_not_mem_closedBall
          T center μ radius x hR hμoutside hcontour (mem_eigenspace_iff.mp hx)
      have hxOrth : x ∈ Sᗮ := by
        rw [Submodule.mem_orthogonal]
        intro y hy
        change y ∈ ⨆ ν : ℂ, ⨆ (_ : ν ∈ Metric.ball center radius),
          eigenspace T.toLinearMap ν at hy
        refine Submodule.iSup_induction
          (motive := fun y ↦ inner ℂ y x = 0)
          (fun ν : ℂ ↦ ⨆ (_ : ν ∈ Metric.ball center radius),
            eigenspace T.toLinearMap ν) hy ?_ ?_ ?_
        · intro ν y hyν
          refine Submodule.iSup_induction
            (motive := fun y ↦ inner ℂ y x = 0)
            (fun _ : ν ∈ Metric.ball center radius ↦ eigenspace T.toLinearMap ν)
            hyν ?_ ?_ ?_
          · intro hν y hyEig
            have hνμ : ν ≠ μ := by
              intro hEq
              subst ν
              exact hμball hν
            exact NCG.NormalSpectrum.inner_eq_zero_of_isStarNormal_of_eigenvectors
              T hnormal hνμ (mem_eigenspace_iff.mp hyEig)
                (mem_eigenspace_iff.mp hx)
          · simp
          · intro a b ha hb
            rw [inner_add_left, ha, hb, add_zero]
        · simp
        · intro a b ha hb
          rw [inner_add_left, ha, hb, add_zero]
      have hQx : Q x = 0 := by
        change S.starProjection x = 0
        rw [Submodule.starProjection_apply,
          Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hxOrth]
        rfl
      rw [hPx, hQx]
  let K : Submodule ℂ H := ⨆ μ : ℂ, eigenspace T.toLinearMap μ
  let D : H →L[ℂ] H := P - Q
  have hKle : K ≤ LinearMap.ker D.toLinearMap := by
    dsimp [K]
    apply iSup_le
    intro μ x hx
    rw [LinearMap.mem_ker]
    change P x - Q x = 0
    rw [hEqEigen μ x hx, sub_self]
  have hKClosureTop : K.topologicalClosure = (⊤ : Submodule ℂ H) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mp
    simpa [K] using
      NCG.NormalSpectrum.dense_iSup_eigenspaces_of_compact_of_isStarNormal
        T hcompact hnormal
  have hclosureLe : K.topologicalClosure ≤ LinearMap.ker D.toLinearMap :=
    K.topologicalClosure_minimal hKle D.isClosed_ker
  have hDzero : D = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hxKer : x ∈ LinearMap.ker D.toLinearMap := by
      apply hclosureLe
      rw [hKClosureTop]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp hxKer
  have hPQ : P = Q := sub_eq_zero.mp hDzero
  change LinearMap.range P.toLinearMap = S
  rw [hPQ]
  exact S.range_starProjection

end NCG.ResolventStability
