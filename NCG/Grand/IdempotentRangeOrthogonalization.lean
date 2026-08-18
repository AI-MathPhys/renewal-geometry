/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProtectedSpectralProjectionRigidity

/-!
# Orthogonalizing convergent idempotent ranges

An orthogonal projection onto the range of an idempotent is controlled by the idempotent when
the limiting idempotent is already orthogonal.  Consequently norm convergence of arbitrary
idempotents, together with equality of cutoff ranges, implies norm convergence of the associated
orthogonal projections.  This avoids requiring every cutoff contour projection to be proved
self-adjoint separately.
-/

open Filter Topology

noncomputable section

namespace NCG.ProjectionStability

universe u v

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]

/-- Equal-range idempotents absorb one another under composition. -/
theorem mul_eq_right_of_idempotent_of_range_eq
    (P Q : H →L[K] H) (hP : IsIdempotentElem P)
    (hrange : LinearMap.range P.toLinearMap = LinearMap.range Q.toLinearMap) :
    P * Q = Q := by
  apply ContinuousLinearMap.ext
  intro x
  have hx : Q x ∈ LinearMap.range P.toLinearMap := by
    rw [hrange]
    exact LinearMap.mem_range_self Q.toLinearMap x
  exact (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr hP).mem_range_iff.mp hx

/-- If both equal-range operators are idempotent, composition in the other order absorbs the
first operator as well. -/
theorem mul_eq_left_of_idempotent_of_range_eq
    (P Q : H →L[K] H) (hQ : IsIdempotentElem Q)
    (hrange : LinearMap.range P.toLinearMap = LinearMap.range Q.toLinearMap) :
    Q * P = P := by
  exact mul_eq_right_of_idempotent_of_range_eq Q P hQ hrange.symm

/-- The orthogonal projection onto an idempotent range is within three times the distance from
that idempotent to an orthogonal limiting projection. -/
theorem norm_starProjection_sub_le_three_mul_norm_idempotent_sub
    (P Q Qlim : H →L[K] H)
    (hP : IsStarProjection P) (hQ : IsIdempotentElem Q)
    (hQlim : IsStarProjection Qlim)
    (hrange : LinearMap.range P.toLinearMap = LinearMap.range Q.toLinearMap) :
    ‖P - Qlim‖ ≤ 3 * ‖Q - Qlim‖ := by
  have hPQ : P * Q = Q :=
    mul_eq_right_of_idempotent_of_range_eq P Q hP.isIdempotentElem hrange
  have hQP : Q * P = P :=
    mul_eq_left_of_idempotent_of_range_eq P Q hQ hrange
  have hleft : (1 - Qlim) * P = (Q - Qlim) * P := by
    rw [sub_mul, one_mul, sub_mul, hQP]
  have hright : P * (1 - Qlim) = star ((1 - Qlim) * P) := by
    rw [star_mul, star_sub, star_one, hP.isSelfAdjoint.star_eq,
      hQlim.isSelfAdjoint.star_eq]
  have hP_sub_Q : P - Q = P * (1 - Q) := by
    rw [mul_sub, mul_one, hPQ]
  calc
    ‖P - Qlim‖ ≤ ‖P - Q‖ + ‖Q - Qlim‖ := by
      simpa [sub_add_sub_cancel] using norm_add_le (P - Q) (Q - Qlim)
    _ = ‖P * (1 - Q)‖ + ‖Q - Qlim‖ := by rw [hP_sub_Q]
    _ ≤ (‖P * (1 - Qlim)‖ + ‖P * (Qlim - Q)‖) + ‖Q - Qlim‖ := by
      gcongr
      rw [show (1 - Q) = (1 - Qlim) + (Qlim - Q) by abel]
      exact norm_add_le _ _
    _ ≤ (‖Q - Qlim‖ + ‖Q - Qlim‖) + ‖Q - Qlim‖ := by
      gcongr
      · rw [hright, norm_star, hleft]
        exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
          hP.norm_le)
      · rw [norm_sub_rev Qlim Q]
        exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _)
          hP.norm_le)
    _ = 3 * ‖Q - Qlim‖ := by ring

/-- Norm-convergent idempotents transfer convergence to orthogonal projections with the same
eventual ranges, provided the limiting idempotent is orthogonal. -/
theorem starProjection_tendsto_of_idempotent_range_eq
    {I : Type*} {l : Filter I}
    (P Q : I → H →L[K] H) (Qlim : H →L[K] H)
    (hstarP : ∀ᶠ i in l, IsStarProjection (P i))
    (hidempotentQ : ∀ᶠ i in l, IsIdempotentElem (Q i))
    (hstarQlim : IsStarProjection Qlim)
    (hrange : ∀ᶠ i in l,
      LinearMap.range (P i).toLinearMap = LinearMap.range (Q i).toLinearMap)
    (hQlim : Tendsto Q l (nhds Qlim)) :
    Tendsto P l (nhds Qlim) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound : ∀ᶠ i in l, ‖P i - Qlim‖ ≤ 3 * ‖Q i - Qlim‖ := by
    filter_upwards [hstarP, hidempotentQ, hrange] with i hPi hQi hi
    exact norm_starProjection_sub_le_three_mul_norm_idempotent_sub
      (P i) (Q i) Qlim hPi hQi hstarQlim hi
  have hright : Tendsto (fun i ↦ 3 * ‖Q i - Qlim‖) l (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hQlim)
  exact squeeze_zero' (Filter.Eventually.of_forall fun i ↦ norm_nonneg _) hbound hright

end NCG.ProjectionStability
