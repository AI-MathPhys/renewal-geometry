/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactSymmetricSpectralIsolation
import NCG.Grand.CircleRieszProjectionEigenvector
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Automatic Riesz-eigenspace identification for compact symmetric operators

Around a nonzero spectral center of a compact symmetric operator, one can choose a circle whose
Riesz projection is exactly the orthogonal projection onto the center eigenspace.  The proof
checks the two projections on every eigenspace and uses totality of compact symmetric
eigenvectors to extend the equality to the whole Hilbert space.
-/

open Complex Set Module End

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

set_option maxHeartbeats 800000 in
-- The total-eigenspace density and orthogonal-projection instances are elaboration intensive.
/-- A nonzero point for a compact symmetric operator has an automatically selected Riesz circle
whose projection range is exactly its eigenspace (possibly the zero eigenspace). -/
theorem exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isSymmetric
    (T : H →L[ℂ] H) (hcompact : IsCompactOperator T)
    (hsymm : LinearMap.IsSymmetric T.toLinearMap)
    (μ : ℂ) (hμ : μ ≠ 0) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall μ radius ∧
      (∀ z ∈ Metric.sphere μ radius, z ∈ resolventSet ℂ T) ∧
      LinearMap.range (circleRieszProjection T μ radius).toLinearMap =
        eigenspace T.toLinearMap μ := by
  obtain ⟨ε, hε, hisolated⟩ :=
    exists_isolatedInBall_of_compact_of_isSymmetric T hcompact hsymm μ hμ
  let radius : ℝ := min (ε / 2) (dist 0 μ / 2)
  have hdistPos : 0 < dist (0 : ℂ) μ := dist_pos.mpr (Ne.symm hμ)
  have hR : 0 < radius := by
    dsimp [radius]
    exact lt_min (by linarith) (by linarith)
  have hRε : radius < ε := by
    have : radius ≤ ε / 2 := by
      dsimp [radius]
      exact min_le_left _ _
    linarith
  have hzero : (0 : ℂ) ∉ Metric.closedBall μ radius := by
    intro hzeroMem
    have hdistLe : dist (0 : ℂ) μ ≤ radius := Metric.mem_closedBall.mp hzeroMem
    have hradiusLe : radius ≤ dist (0 : ℂ) μ / 2 := by
      dsimp [radius]
      exact min_le_right _ _
    linarith
  have hcontour : ∀ z ∈ Metric.sphere μ radius, z ∈ resolventSet ℂ T := by
    intro z hzSphere
    by_contra hzResolvent
    have hzSpectrum : z ∈ spectrum ℂ T := by
      change z ∈ (resolventSet ℂ T)ᶜ
      exact hzResolvent
    have hzNear : dist z μ < ε := by
      rw [Metric.mem_sphere.mp hzSphere]
      exact hRε
    have hzμ := hisolated z hzSpectrum hzNear
    subst z
    have : (0 : ℝ) = radius := by
      simpa using Metric.mem_sphere.mp hzSphere
    exact hR.ne' this.symm
  let Eμ : Submodule ℂ H := eigenspace T.toLinearMap μ
  letI : FiniteDimensional ℂ Eμ := by
    dsimp [Eμ]
    exact T.finite_dimensional_eigenspace hcompact μ hμ
  let P : H →L[ℂ] H := circleRieszProjection T μ radius
  let Q : H →L[ℂ] H := Eμ.starProjection
  have hμBall : μ ∈ Metric.ball μ radius := by
    simpa [Metric.mem_ball] using hR
  have hEqEigen : ∀ ν : ℂ, ∀ x ∈ eigenspace T.toLinearMap ν, P x = Q x := by
    intro ν x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hνμ : ν = μ
    · subst ν
      have hPx : P x = x := by
        exact circleRieszProjection_apply_eigenvector_of_mem_ball
          T μ μ radius x hμBall hcontour (mem_eigenspace_iff.mp hx)
      have hxEμ : x ∈ Eμ := by simpa [Eμ] using hx
      have hQx : Q x = x := by
        simpa [Q] using Eμ.starProjection_mem_subspace_eq_self ⟨x, hxEμ⟩
      rw [hPx, hQx]
    · have hνEigen : HasEigenvalue T.toLinearMap ν :=
        hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩
      have hνSpectrum : ν ∈ spectrum ℂ T := by
        rw [ContinuousLinearMap.spectrum_eq]
        exact hνEigen.mem_spectrum
      have hνOutside : ν ∉ Metric.closedBall μ radius := by
        intro hνClosed
        have hνLe : dist ν μ ≤ radius := Metric.mem_closedBall.mp hνClosed
        by_cases hνLt : dist ν μ < radius
        · exact hνμ (hisolated ν hνSpectrum (hνLt.trans hRε))
        · have hνEq : dist ν μ = radius := le_antisymm hνLe (le_of_not_gt hνLt)
          have hνSphere : ν ∈ Metric.sphere μ radius := Metric.mem_sphere.mpr hνEq
          exact hνSpectrum (hcontour ν hνSphere)
      have hPx : P x = 0 := by
        exact circleRieszProjection_apply_eigenvector_of_not_mem_closedBall
          T μ ν radius x hR hνOutside hcontour (mem_eigenspace_iff.mp hx)
      have hxOrth : x ∈ Eμᗮ := by
        intro y hy
        exact hsymm.orthogonalFamily_eigenspaces (Ne.symm hνμ)
          ⟨y, by simpa [Eμ] using hy⟩ ⟨x, hx⟩
      have hQx : Q x = 0 := by
        change Eμ.starProjection x = 0
        rw [Submodule.starProjection_apply,
          Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hxOrth]
        rfl
      rw [hPx, hQx]
  let K : Submodule ℂ H := ⨆ ν : ℂ, eigenspace T.toLinearMap ν
  let D : H →L[ℂ] H := P - Q
  have hKle : K ≤ LinearMap.ker D.toLinearMap := by
    dsimp [K]
    apply iSup_le
    intro ν x hx
    rw [LinearMap.mem_ker]
    change P x - Q x = 0
    rw [hEqEigen ν x hx, sub_self]
  have hKOrth : Kᗮ = (⊥ : Submodule ℂ H) := by
    simpa [K] using T.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hsymm
  have hKClosureOrth : K.topologicalClosureᗮ = (⊥ : Submodule ℂ H) := by
    rw [Submodule.orthogonal_closure, hKOrth]
  have hKClosureTop : K.topologicalClosure = (⊤ : Submodule ℂ H) :=
    Submodule.orthogonal_eq_bot_iff.mp hKClosureOrth
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
  refine ⟨radius, hR, hzero, hcontour, ?_⟩
  rw [show circleRieszProjection T μ radius = P from rfl, hPQ]
  exact Eμ.range_starProjection

end NCG.ResolventStability
