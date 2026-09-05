/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Contour separation for self-adjoint operators

The spectrum of a self-adjoint bounded operator is real.  Consequently, to verify that a
complex contour lies in its resolvent set, it suffices to check the real points of the contour.
This removes all non-real contour points from concrete spectral-separation obligations.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {A : Type u} [CStarAlgebra A]

set_option maxHeartbeats 400000 in
-- The generic C-star real-spectrum theorem requires extra elaboration heartbeats here.
/-- Every non-real complex number belongs to the resolvent set of a symmetric bounded operator. -/
theorem mem_resolventSet_of_isSelfAdjoint_of_im_ne_zero
    (a : A) (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ resolventSet ℂ a := by
  by_contra hres
  have hzspec : z ∈ spectrum ℂ a := by
    change z ∈ (resolventSet ℂ a)ᶜ
    exact hres
  exact hz (ha.im_eq_zero_of_mem_spectrum hzspec)

/-- For a symmetric operator, checking the real points of a set is enough to prove that the
whole set is contained in the resolvent set. -/
theorem subset_resolventSet_of_isSelfAdjoint_of_real_points
    (a : A) (ha : IsSelfAdjoint a)
    (s : Set ℂ)
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ s → (x : ℂ) ∈ resolventSet ℂ a) :
    s ⊆ resolventSet ℂ a := by
  intro z hz
  by_cases him : z.im = 0
  · have hzeq : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hzeq]
    exact hreal z.re (hzeq ▸ hz)
  · exact mem_resolventSet_of_isSelfAdjoint_of_im_ne_zero a ha him

/-- Circle-contour specialization of
`subset_resolventSet_of_isSelfAdjoint_of_real_points`. -/
theorem circle_subset_resolventSet_of_isSelfAdjoint_of_real_points
    (a : A) (ha : IsSelfAdjoint a)
    (center : ℂ) (radius : ℝ)
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ Metric.sphere center radius →
      (x : ℂ) ∈ resolventSet ℂ a) :
    ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ a := by
  exact subset_resolventSet_of_isSelfAdjoint_of_real_points
    a ha (Metric.sphere center radius) hreal

/-- For a circle centered on the real axis, self-adjoint contour separation reduces to checking
the two real endpoints. Every other point of the circle is automatically resolvent. -/
theorem circle_subset_resolventSet_of_isSelfAdjoint_of_endpoints
    (a : A) (ha : IsSelfAdjoint a)
    (center radius : ℝ)
    (hleft : ((center - radius : ℝ) : ℂ) ∈ resolventSet ℂ a)
    (hright : ((center + radius : ℝ) : ℂ) ∈ resolventSet ℂ a) :
    ∀ z ∈ Metric.sphere (center : ℂ) radius, z ∈ resolventSet ℂ a := by
  apply circle_subset_resolventSet_of_isSelfAdjoint_of_real_points
    a ha (center : ℂ) radius
  intro x hx
  have hdist := Metric.mem_sphere.mp hx
  rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq] at hdist
  change |x - center| = radius at hdist
  by_cases hnonneg : 0 ≤ x - center
  · have hxeq : x = center + radius := by
      rw [abs_of_nonneg hnonneg] at hdist
      linarith
    simpa [hxeq] using hright
  · have hxeq : x = center - radius := by
      rw [abs_of_nonpos (le_of_not_ge hnonneg)] at hdist
      linarith
    simpa [hxeq] using hleft
set_option maxHeartbeats 400000 in
-- Synthesizing the bounded-operator C-star instance and real-spectrum wrapper is expensive.
/-- Hilbert-space specialization stated with the symmetric linear-map hypothesis used by
the graph-resolvent machinery. -/
theorem circle_subset_resolventSet_of_isSymmetric_of_endpoints
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : LinearMap.IsSymmetric T.toLinearMap)
    (center radius : ℝ)
    (hleft : ((center - radius : ℝ) : ℂ) ∈ resolventSet ℂ T)
    (hright : ((center + radius : ℝ) : ℂ) ∈ resolventSet ℂ T) :
    ∀ z ∈ Metric.sphere (center : ℂ) radius, z ∈ resolventSet ℂ T :=
  circle_subset_resolventSet_of_isSelfAdjoint_of_endpoints
    T hT.isSelfAdjoint center radius hleft hright
end NCG.ResolventStability
