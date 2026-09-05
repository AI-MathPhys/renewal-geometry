/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalEigenspaces
import NCG.Grand.CompactCircleRieszProjection

/-!
# Circle Riesz projections of compact normal operators

The compact-normal eigenspace theorem removes the dense-spectrum premise from circle Riesz
idempotence.  On a zero-avoiding circle, compactness then makes the idempotent Riesz range
finite-dimensional.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The circle Riesz operator of a compact normal operator is idempotent. -/
theorem circleRieszProjection_isIdempotentElem_of_compact_of_isStarNormal
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator (T : E → E))
    (hnormal : IsStarNormal T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsIdempotentElem (circleRieszProjection T center radius).toLinearMap := by
  exact circleRieszProjection_isIdempotentElem_of_dense_eigenspaces
    T (NCG.NormalSpectrum.dense_iSup_eigenspaces_of_compact_of_isStarNormal
      T hcompact hnormal) center radius hR hcontour

/-- A zero-avoiding circle Riesz projection of a compact normal operator has finite-dimensional
range. -/
theorem finiteDimensional_range_circleRieszProjection_of_compact_of_isStarNormal
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator (T : E → E))
    (hnormal : IsStarNormal T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    FiniteDimensional ℂ
      (LinearMap.range
        (circleRieszProjection T center radius : E →L[ℂ] E).toLinearMap) := by
  apply finiteDimensional_range_of_compact_idempotent
  · exact circleRieszProjection_isCompactOperator
      T hcompact center radius hR hzero hcontour
  · exact ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mp
      (circleRieszProjection_isIdempotentElem_of_compact_of_isStarNormal
        T hcompact hnormal center radius hR hcontour)

end NCG.ResolventStability
