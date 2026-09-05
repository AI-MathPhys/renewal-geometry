/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RieszProjectionStability
import NCG.Grand.NearbyProjectionRankStability

/-!
# Quantitative stability of circle Riesz projections

The qualitative Riesz-continuity API is strengthened here by the explicit
resolvent-identity estimate needed for transported finite spectral screens.
-/

open Complex

noncomputable section

namespace NCG.ResolventStability

universe u

variable {A : Type u}
variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- If both resolvents are bounded on one circle, their Riesz projections
differ by at most radius times M times N times the perturbation norm. -/
theorem norm_circleRieszProjection_sub_le
    (a b : A) (center : ℂ) (radius M N : ℝ)
    (hradius : 0 ≤ radius) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (ha_unit : ∀ z ∈ Metric.sphere center radius,
      z ∈ resolventSet ℂ a)
    (hb_unit : ∀ z ∈ Metric.sphere center radius,
      z ∈ resolventSet ℂ b)
    (ha_bound : ∀ z ∈ Metric.sphere center radius,
      ‖resolvent a z‖ ≤ M)
    (hb_bound : ∀ z ∈ Metric.sphere center radius,
      ‖resolvent b z‖ ≤ N) :
    ‖circleRieszProjection a center radius -
        circleRieszProjection b center radius‖
      ≤ radius * (M * N * ‖a - b‖) := by
  have hca : ContinuousOn (resolvent a) (Metric.sphere center radius) := by
    intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left
      (ha_unit z hz)).continuousAt.continuousWithinAt
  have hcb : ContinuousOn (resolvent b) (Metric.sphere center radius) := by
    intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left
      (hb_unit z hz)).continuousAt.continuousWithinAt
  have hia : CircleIntegrable (resolvent a) center radius :=
    hca.circleIntegrable hradius
  have hib : CircleIntegrable (resolvent b) center radius :=
    hcb.circleIntegrable hradius
  rw [circleRieszProjection, circleRieszProjection, ← smul_sub,
    ← circleIntegral.integral_sub hia hib]
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    hradius
  intro z hz
  have hid :
      resolvent a z - resolvent b z =
        resolvent a z *
          ((algebraMap ℂ A z - b) - (algebraMap ℂ A z - a)) *
            resolvent b z := by
    simpa [resolvent] using
      (Ring.inverse_sub_inverse
        (iff_of_true (ha_unit z hz) (hb_unit z hz)))
  rw [hid]
  calc
    ‖resolvent a z *
          ((algebraMap ℂ A z - b) - (algebraMap ℂ A z - a)) *
            resolvent b z‖
        ≤ (‖resolvent a z‖ *
            ‖(algebraMap ℂ A z - b) - (algebraMap ℂ A z - a)‖) *
              ‖resolvent b z‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (M * ‖(algebraMap ℂ A z - b) -
          (algebraMap ℂ A z - a)‖) * N := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (ha_bound z hz) (norm_nonneg _)
          · exact hb_bound z hz
          · exact norm_nonneg _
          · exact mul_nonneg hM (norm_nonneg _)
    _ = M * N * ‖a - b‖ := by
          rw [show (algebraMap ℂ A z - b) - (algebraMap ℂ A z - a) =
            a - b by abel]
          ring

/-- Quantitative contour control below one implies equality of the finite
Riesz-screen multiplicities. -/
theorem finrank_circleRieszProjection_eq_of_quantitative_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P Q : H →L[ℂ] H)
    (hP : IsIdempotentElem P.toLinearMap)
    (hQ : IsIdempotentElem Q.toLinearMap)
    (bound : ℝ) (hbound : ‖P - Q‖ ≤ bound) (hlt : bound < 1)
    [Module.Finite ℂ (LinearMap.range P.toLinearMap)]
    [Module.Finite ℂ (LinearMap.range Q.toLinearMap)] :
    Module.finrank ℂ (LinearMap.range P.toLinearMap) =
      Module.finrank ℂ (LinearMap.range Q.toLinearMap) :=
  NCG.ProjectionStability.finrank_range_eq_of_norm_sub_lt_one
    P Q hP hQ (hbound.trans_lt hlt)

/-- The difference of two projections is the sum of its two cross-leakage
corners.  Equal cross bounds therefore give the factor-two Davis--Kahan
estimate used in SC.3. -/
theorem norm_projection_sub_le_two_mul_of_cross_bounds
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P Q : H →L[ℂ] H) (delta : ℝ)
    (hPQ : ‖P * (1 - Q)‖ ≤ delta)
    (hQP : ‖(1 - P) * Q‖ ≤ delta) :
    ‖P - Q‖ ≤ 2 * delta := by
  have hsplit : P - Q = P * (1 - Q) - (1 - P) * Q := by
    noncomm_ring
  rw [hsplit]
  calc
    ‖P * (1 - Q) - (1 - P) * Q‖
        ≤ ‖P * (1 - Q)‖ + ‖(1 - P) * Q‖ := norm_sub_le _ _
    _ ≤ delta + delta := add_le_add hPQ hQP
    _ = 2 * delta := by ring

/-- Exact rational form of the SC.3 projection estimate once the two standard
spectral cross-leakage estimates have been established. -/
theorem norm_projection_sub_le_davisKahan
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P Q : H →L[ℂ] H) (epsilon gap : ℝ)
    (hleft : ‖P * (1 - Q)‖ ≤ epsilon / (gap - epsilon))
    (hright : ‖(1 - P) * Q‖ ≤ epsilon / (gap - epsilon)) :
    ‖P - Q‖ ≤ 2 * epsilon / (gap - epsilon) := by
  have h := norm_projection_sub_le_two_mul_of_cross_bounds
    P Q (epsilon / (gap - epsilon)) hleft hright
  convert h using 1 <;> ring

end NCG.ResolventStability
