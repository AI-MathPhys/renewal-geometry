/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ContourResolventBounds
import NCG.Grand.RieszProjectionStability
import NCG.Grand.SelfAdjointContourSeparation

/-!
# Automatic stability of circle Riesz projections

Norm convergence and separation of the limiting contour already force all sufficiently late
operators to have uniformly bounded resolvents on that contour.  Consequently no separate
cutoff resolvent-set or uniform-bound hypotheses are needed for convergence of circle Riesz
projections.  For symmetric operators on a real-centered circle, the limiting contour condition
itself reduces to the two real endpoints.
-/

open Complex Filter Set Topology

noncomputable section

namespace NCG.ResolventStability

universe u v

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Circle Riesz projections vary continuously under norm convergence as soon as the limiting
circle is contained in the resolvent set.  All cutoff contour and bound data are automatic. -/
theorem circleRieszProjection_tendsto_of_tendsto_of_circle_subset_resolventSet
    {J : Type v} {l : Filter J} [l.IsCountablyGenerated]
    (aSeq : J → A) (a : A) (ha : Tendsto aSeq l (𝓝 a))
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius)
    (hunit : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ a) :
    Tendsto (fun j ↦ circleRieszProjection (aSeq j) center radius) l
      (𝓝 (circleRieszProjection a center radius)) := by
  obtain ⟨M, hM, hlimitBound⟩ :=
    exists_circle_resolvent_norm_bound a center radius hunit
  obtain ⟨N, hN, hstage⟩ :=
    eventually_circle_resolvent_bound_of_tendsto
      aSeq a ha center radius M hM hunit hlimitBound
  exact circleRieszProjection_tendsto ha center radius hradius M N hM hunit hlimitBound
    (hstage.mono fun j hj z hz ↦ (hj z hz).1)
    (hstage.mono fun j hj z hz ↦ (hj z hz).2)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a norm-convergent family of bounded operators with symmetric limit, two real endpoint
checks imply convergence of the Riesz projections on the corresponding real-centered circle. -/
theorem circleRieszProjection_tendsto_of_tendsto_of_isSymmetric_of_endpoints
    {J : Type v} {l : Filter J} [l.IsCountablyGenerated]
    (T : J → H →L[ℂ] H) (Tlim : H →L[ℂ] H) (hT : Tendsto T l (𝓝 Tlim))
    (hlimSymmetric : LinearMap.IsSymmetric Tlim.toLinearMap)
    (center radius : ℝ) (hradius : 0 ≤ radius)
    (hleft : ((center - radius : ℝ) : ℂ) ∈ resolventSet ℂ Tlim)
    (hright : ((center + radius : ℝ) : ℂ) ∈ resolventSet ℂ Tlim) :
    Tendsto (fun j ↦ circleRieszProjection (T j) (center : ℂ) radius) l
      (𝓝 (circleRieszProjection Tlim (center : ℂ) radius)) := by
  apply circleRieszProjection_tendsto_of_tendsto_of_circle_subset_resolventSet
    T Tlim hT (center : ℂ) radius hradius
  exact circle_subset_resolventSet_of_isSymmetric_of_endpoints
    Tlim hlimSymmetric center radius hleft hright

end NCG.ResolventStability
