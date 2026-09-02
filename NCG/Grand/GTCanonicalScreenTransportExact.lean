/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GappedCanonicalScreenTransport
import NCG.Grand.SelfAdjointWeylGap
import NCG.Grand.NearbyProjectionRankStability

/-!
# Exact SC.3 canonical-screen transport

This is the manuscript-facing perturbation theorem.  A single protected gap
for the old self-adjoint operator and an operator-norm perturbation smaller
than half that gap imply both equality of threshold-screen ranks and the
displayed Davis--Kahan norm bound.
-/

noncomputable section

namespace NCG.CanonicalScreen

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- `thm:GT-canonical-screen`, SC.3: exact finite-dimensional rank and norm
transport of the strict sub-threshold spectral screen. -/
theorem gt_canonical_screen_transport_exact
    (A B : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (beta gap epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsHalf : epsilon < gap / 2)
    (hAB : ‖A - B‖ ≤ epsilon)
    (hspecA : ∀ x ∈ spectrum ℝ A,
      x ≤ beta - gap ∨ beta + gap ≤ x) :
    let P := gappedCanonicalScreen A beta gap
    let Q := gappedCanonicalScreen B beta (gap - epsilon)
    Module.finrank ℂ (LinearMap.range P.toLinearMap) =
        Module.finrank ℂ (LinearMap.range Q.toLinearMap) ∧
      ‖P - Q‖ ≤ 2 * epsilon / (gap - epsilon) := by
  dsimp only
  have hepsGap : epsilon < gap := by linarith
  have hgap : 0 < gap := by linarith
  have hgapB : 0 < gap - epsilon := sub_pos.mpr hepsGap
  have hspecB : ∀ x ∈ spectrum ℝ B,
      x ≤ beta - (gap - epsilon) ∨
        beta + (gap - epsilon) ≤ x :=
    NCG.ResolventStability.selfAdjoint_spectrum_separated_of_norm_sub_le
      A B hA hB beta gap epsilon hepsilon hepsGap hAB hspecA
  let P := gappedCanonicalScreen A beta gap
  let Q := gappedCanonicalScreen B beta (gap - epsilon)
  have hPstar : IsStarProjection P :=
    gappedCanonicalScreen_isStarProjection A hA beta gap hgap hspecA
  have hQstar : IsStarProjection Q :=
    gappedCanonicalScreen_isStarProjection
      B hB beta (gap - epsilon) hgapB hspecB
  have hstrong : ‖P - Q‖ ≤ 2 * epsilon / (2 * gap - epsilon) :=
    norm_gappedCanonicalScreen_sub_le_strong
      A B hA hB beta gap epsilon hepsilon hepsGap hAB hspecA hspecB
  have hstrongLt : 2 * epsilon / (2 * gap - epsilon) < 1 := by
    have hden : 0 < 2 * gap - epsilon := by linarith
    rw [div_lt_one hden]
    linarith
  have hnormLt : ‖P - Q‖ < 1 := hstrong.trans_lt hstrongLt
  have hPidem : IsIdempotentElem P.toLinearMap := by
    show P.toLinearMap * P.toLinearMap = P.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap hPstar.isIdempotentElem.eq
  have hQidem : IsIdempotentElem Q.toLinearMap := by
    show Q.toLinearMap * Q.toLinearMap = Q.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap hQstar.isIdempotentElem.eq
  constructor
  · exact NCG.ProjectionStability.finrank_range_eq_of_norm_sub_lt_one
      P Q hPidem hQidem hnormLt
  · exact norm_gappedCanonicalScreen_sub_le
      A B hA hB beta gap epsilon hepsilon hepsGap hAB hspecA hspecB

end NCG.CanonicalScreen
