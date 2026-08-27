/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HypocoerciveScreensExact

/-!
# Exact sampled hypocoercive rate

Attainment of the least sampled-loss Rayleigh value upgrades the previously
proved contraction inequality to the exact operator-norm identity in FC.11.
-/

open scoped RealInnerProductSpace
open NormedSpace

namespace NCG
namespace ExactSampledHypocoerciveRate

open HypocoerciveScreens

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- If `ω` is the attained least Rayleigh value of the sampled loss, the
sampled contraction bound is sharp in operator norm. -/
theorem sampled_opNorm_sq_eq
    (K A S : E →L[ℝ] E) (hKAS : K = A - S)
    (hA : ∀ u, ⟪A u, u⟫ = 0) (T ω : ℝ)
    (hωlower : ∀ x, ω * ‖x‖ ^ 2 ≤ sampledLoss K S T x)
    (hattain : ∃ x : E, ‖x‖ = 1 ∧ sampledLoss K S T x = ω) :
    ‖exp (T • K)‖ ^ 2 = 1 - 2 * ω := by
  obtain ⟨x, hx, hxloss⟩ := hattain
  have hpoint := normSq_flow_eq K A S hKAS hA x T
  rw [hx, hxloss, one_pow] at hpoint
  have hlower : ‖flow K T x‖ ≤ ‖exp (T • K)‖ := by
    have h := (exp (T • K)).le_opNorm x
    simpa [flow, hx] using h
  have hupper := (sampled_contraction K A S hKAS hA T ω hωlower).2
  have hq : 0 ≤ 1 - 2 * ω := by
    rw [← hpoint]
    positivity
  have hsqrt : Real.sqrt (1 - 2 * ω) ^ 2 = 1 - 2 * ω :=
    Real.sq_sqrt hq
  have hflow0 : 0 ≤ ‖flow K T x‖ := norm_nonneg _
  have hop0 : 0 ≤ ‖exp (T • K)‖ := norm_nonneg _
  have hsqrt0 : 0 ≤ Real.sqrt (1 - 2 * ω) := Real.sqrt_nonneg _
  nlinarith

/-- The complete exact sampled-rate and Lyapunov-decay corollary. -/
theorem exact_sampled_rate_and_lyapunov_decay
    (K A S P : E →L[ℝ] E) (hKAS : K = A - S)
    (hA : ∀ u, ⟪A u, u⟫ = 0) (T ω pminus pplus : ℝ)
    (hT : 0 < T) (hω : 0 < ω)
    (hωlower : ∀ x, ω * ‖x‖ ^ 2 ≤ sampledLoss K S T x)
    (hattain : ∃ x : E, ‖x‖ = 1 ∧ sampledLoss K S T x = ω)
    (hpminus : 0 < pminus) (hpplus : 0 < pplus)
    (hlyap : ContinuousLinearMap.adjoint K * P + P * K = -1)
    (hPlow : ∀ u, pminus * ‖u‖ ^ 2 ≤ ⟪u, P u⟫)
    (hPhigh : ∀ u, ⟪u, P u⟫ ≤ pplus * ‖u‖ ^ 2) :
    ‖exp (T • K)‖ ^ 2 = 1 - 2 * ω ∧
      0 < -Real.log (1 - 2 * ω) / (2 * T) ∧
      ∀ t : ℝ, 0 ≤ t →
        ‖exp (t • K)‖ ≤
          Real.sqrt (pplus / pminus) * Real.exp (-t / (2 * pplus)) := by
  have htwo : 2 * ω < 1 :=
    two_omega_lt_one K A S hKAS hA T ω hωlower
  refine ⟨sampled_opNorm_sq_eq K A S hKAS hA T ω hωlower hattain,
    hypocoercive_rate_pos T ω hT hω htwo, ?_⟩
  intro t ht
  exact hypocoercive_decay_opNorm K P pminus pplus hpminus hpplus
    hlyap hPlow hPhigh ht

end ExactSampledHypocoerciveRate
end NCG
