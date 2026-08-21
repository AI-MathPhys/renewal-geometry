/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalCircleRieszSpectralSubspace
import NCG.Grand.CompactNormalSpectralIsolation

/-!
# Arbitrarily small Riesz circles for compact normal eigenspaces

Every nonzero point of a compact normal operator admits an isolating Riesz circle below any
prescribed positive radius. Its range is exactly the center eigenspace, including when that
eigenspace is zero.
-/

open Complex Set Module End

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A compact normal operator admits an exact eigenspace Riesz circle around any nonzero center
whose radius is smaller than any prescribed positive bound. -/
theorem exists_small_circleRieszProjection_range_eq_eigenspace_of_compact_of_isStarNormal
    (T : H →L[ℂ] H) (hcompact : IsCompactOperator (T : H → H))
    (hnormal : IsStarNormal T)
    (μ : ℂ) (hμ : μ ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ radius : ℝ, 0 < radius ∧ radius < δ ∧
      (0 : ℂ) ∉ Metric.closedBall μ radius ∧
      (∀ z ∈ Metric.sphere μ radius, z ∈ resolventSet ℂ T) ∧
      LinearMap.range (circleRieszProjection T μ radius).toLinearMap =
        eigenspace T.toLinearMap μ := by
  obtain ⟨ε, hε, hisolated⟩ :=
    exists_isolatedInBall_of_compact_of_isStarNormal T hcompact hnormal μ hμ
  let radius : ℝ := min (ε / 2) (min (dist 0 μ / 2) (δ / 2))
  have hdistPos : 0 < dist (0 : ℂ) μ := dist_pos.mpr (Ne.symm hμ)
  have hR : 0 < radius := by
    dsimp [radius]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hRε : radius < ε := by
    have : radius ≤ ε / 2 := by
      dsimp [radius]
      exact min_le_left _ _
    linarith
  have hRδ : radius < δ := by
    have : radius ≤ δ / 2 := by
      dsimp [radius]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hzero : (0 : ℂ) ∉ Metric.closedBall μ radius := by
    intro hzeroMem
    have hdistLe : dist (0 : ℂ) μ ≤ radius := Metric.mem_closedBall.mp hzeroMem
    have hradiusLe : radius ≤ dist (0 : ℂ) μ / 2 := by
      dsimp [radius]
      exact (min_le_right _ _).trans (min_le_left _ _)
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
  have hrange :=
    range_circleRieszProjection_eq_iSup_eigenspaces_mem_ball_of_compact_of_isStarNormal
      T hcompact hnormal μ radius hR hzero hcontour
  have hsum :
      ((⨆ ν : ℂ, ⨆ (_ : ν ∈ Metric.ball μ radius),
        eigenspace T.toLinearMap ν) : Submodule ℂ H) =
        eigenspace T.toLinearMap μ := by
    apply le_antisymm
    · apply iSup_le
      intro ν
      apply iSup_le
      intro hν x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      have hνSpectrum : ν ∈ spectrum ℂ T := by
        rw [ContinuousLinearMap.spectrum_eq]
        exact (hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩).mem_spectrum
      have hνNear : dist ν μ < ε :=
        (Metric.mem_ball.mp hν).trans hRε
      have hνμ : ν = μ := hisolated ν hνSpectrum hνNear
      subst ν
      exact hx
    · exact le_iSup_of_le μ
        (le_iSup_of_le (show μ ∈ Metric.ball μ radius by
          simpa [Metric.mem_ball] using hR) le_rfl)
  refine ⟨radius, hR, hRδ, hzero, hcontour, ?_⟩
  exact hrange.trans hsum

end NCG.ResolventStability
