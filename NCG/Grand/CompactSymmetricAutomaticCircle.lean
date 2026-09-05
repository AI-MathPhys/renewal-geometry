/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactSymmetricSpectralIsolation
import NCG.Grand.SpectralGapCircleSelection

/-!
# Automatic Riesz circles for compact symmetric operators

Compact symmetric spectral isolation and metric circle selection combine to produce an
admissible zero-avoiding resolvent circle around every nonzero center automatically.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Every nonzero center for a compact symmetric operator admits a positive zero-avoiding circle
whose boundary lies in the resolvent set.  When the center is spectral, this is its isolating
Riesz circle; when it is resolvent, the selected disc contains no spectrum. -/
theorem exists_zeroAvoiding_resolvent_circle_of_compact_of_isSymmetric
    (T : H →L[ℂ] H) (hcompact : IsCompactOperator T)
    (hsymm : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (hcenter : center ≠ 0) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T := by
  obtain ⟨ε, hε, hisolated⟩ :=
    exists_isolatedInBall_of_compact_of_isSymmetric
      T hcompact hsymm center hcenter
  exact exists_zeroAvoiding_resolvent_circle_of_isolatedInBall
    T center ε hε hcenter hisolated

end NCG.ResolventStability
