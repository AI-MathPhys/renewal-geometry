/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Automatic circle selection from a spectral gap

A quantified isolation gap around a nonzero spectral value contains exactly the information
needed by the Riesz-projection machinery.  This file chooses a radius smaller than both half
the spectral gap and half the distance to zero.  The resulting closed disc avoids zero and its
boundary lies in the resolvent set.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A positive spectral gap around a nonzero point automatically supplies a positive
zero-avoiding circle contained in the resolvent set.  No self-adjointness is needed: the
quantified gap is precisely the contour-separation input used by this construction. -/
theorem exists_zeroAvoiding_resolvent_circle_of_spectral_gap
    (T : H →L[ℂ] H) (center : ℂ) (gap : ℝ)
    (hgapPos : 0 < gap) (hcenter : center ≠ 0)
    (hgap : ∀ z ∈ spectrum ℂ T, z ≠ center → gap ≤ dist z center) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T := by
  let radius : ℝ := min (gap / 2) (dist 0 center / 2)
  have hdistPos : 0 < dist (0 : ℂ) center := dist_pos.mpr (Ne.symm hcenter)
  have hradiusPos : 0 < radius := by
    dsimp [radius]
    exact lt_min (by linarith) (by linarith)
  refine ⟨radius, hradiusPos, ?_, ?_⟩
  · intro hzero
    have hdistLe : dist (0 : ℂ) center ≤ radius := Metric.mem_closedBall.mp hzero
    have hradiusLe : radius ≤ dist (0 : ℂ) center / 2 := by
      dsimp [radius]
      exact min_le_right _ _
    linarith
  · intro z hz
    by_contra hres
    have hzspec : z ∈ spectrum ℂ T := by
      change z ∈ (resolventSet ℂ T)ᶜ
      exact hres
    have hdist : dist z center = radius := Metric.mem_sphere.mp hz
    have hzcenter : z ≠ center := by
      intro hzc
      subst z
      have : (0 : ℝ) = radius := by simpa using hdist
      exact hradiusPos.ne' this.symm
    have hgapLe : gap ≤ radius := by simpa [hdist] using hgap z hzspec hzcenter
    have hradiusLe : radius ≤ gap / 2 := by
      dsimp [radius]
      exact min_le_left _ _
    linarith

/-- Open-ball isolation is a convenient topological form of the spectral-gap certificate.
If an open ball contains no spectral point other than its center, a smaller zero-avoiding
resolvent circle is selected automatically. -/
theorem exists_zeroAvoiding_resolvent_circle_of_isolatedInBall
    (T : H →L[ℂ] H) (center : ℂ) (ε : ℝ)
    (hε : 0 < ε) (hcenter : center ≠ 0)
    (hisolated : ∀ z ∈ spectrum ℂ T, dist z center < ε → z = center) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T := by
  apply exists_zeroAvoiding_resolvent_circle_of_spectral_gap
    T center ε hε hcenter
  intro z hz hzcenter
  by_contra hnot
  have hlt : dist z center < ε := lt_of_not_ge hnot
  exact hzcenter (hisolated z hz hlt)


end NCG.ResolventStability
