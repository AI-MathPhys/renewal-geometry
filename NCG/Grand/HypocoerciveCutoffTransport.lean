/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AcceptedArithmeticAndAffineConsequences
import NCG.Grand.LyapunovObservabilityExact
import NCG.Flagship.AnalyticPolar

/-!
# Cutoff transport of the hypocoercive packet

This file completes `thm:GT-hypocoercive-transport`.  Unitary conjugation of
the generator and symmetric loss transports the exponential flow, the sampled
loss Gram `W_K(T)`, and every solution of the Lyapunov equation.  Uniqueness of
the Lyapunov solution therefore transports the canonical metric itself.
-/

open ContinuousLinearMap MeasureTheory

namespace NCG
namespace HypocoerciveCutoffTransport

open HypocoerciveMemory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Exponential flow is functorial under a unitary conjugation. -/
theorem flow_unitaryConjugation (U K : E →L[ℂ] E)
    (hUleft : star U * U = 1) (hUright : U * star U = 1) (t : ℝ) :
    flow (U * K * star U) t = U * flow K t * star U := by
  unfold flow
  have harg : (t : ℂ) • (U * K * star U) =
      U * ((t : ℂ) • K) * star U := by
    simp only [smul_mul_assoc, mul_smul_comm]
  rw [harg, ← exp_conj_pair U (star U) ((t : ℂ) • K) hUright hUleft]

/-- The sampled loss Gram is transported by the same packet unitary. -/
theorem sampledGram_unitaryConjugation (U K S : E →L[ℂ] E)
    (hUleft : star U * U = 1) (hUright : U * star U = 1) (T : ℝ) :
    sampledGram (U * K * star U) (U * S * star U) T =
      U * sampledGram K S T * star U := by
  let L : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) U (star U)
  have hint : IntervalIntegrable
      (fun t : ℝ => star (flow K t) * S * flow K t)
      volume 0 T :=
    (HypocoerciveMemory.continuous_integrand K S).intervalIntegrable 0 T
  unfold sampledGram
  change (∫ t : ℝ in (0 : ℝ)..T,
      star (flow (U * K * star U) t) * (U * S * star U) *
        flow (U * K * star U) t) =
    L (∫ t : ℝ in (0 : ℝ)..T, star (flow K t) * S * flow K t)
  rw [← L.intervalIntegral_comp_comm hint]
  apply intervalIntegral.integral_congr
  intro t _
  change star (flow (U * K * star U) t) * (U * S * star U) *
      flow (U * K * star U) t =
    L (star (flow K t) * S * flow K t)
  rw [flow_unitaryConjugation U K hUleft hUright]
  change star (U * flow K t * star U) * (U * S * star U) *
      (U * flow K t * star U) =
    U * (star (flow K t) * S * flow K t) * star U
  rw [show star (U * flow K t * star U) =
      U * star (flow K t) * star U by
    simp only [star_mul, star_star]
    noncomm_ring]
  calc
    _ = U * star (flow K t) * (star U * U) * S *
        (star U * U) * flow K t * star U := by noncomm_ring
    _ = _ := by rw [hUleft]; simp; noncomm_ring

/-- Unitary conjugation carries a Lyapunov solution to a Lyapunov solution. -/
theorem lyapunovEquation_unitaryConjugation (U K P : E →L[ℂ] E)
    (hUleft : star U * U = 1) (hUright : U * star U = 1)
    (hP : star K * P + P * K = -1) :
    star (U * K * star U) * (U * P * star U)
        + (U * P * star U) * (U * K * star U) = -1 := by
  rw [show star (U * K * star U) = U * star K * star U by
    simp only [star_mul, star_star]
    noncomm_ring]
  have hterm1 :
      (U * star K * star U) * (U * P * star U) =
        U * (star K * P) * star U := by
    calc
      _ = U * star K * (star U * U) * P * star U := by noncomm_ring
      _ = _ := by rw [hUleft]; noncomm_ring
  have hterm2 :
      (U * P * star U) * (U * K * star U) =
        U * (P * K) * star U := by
    calc
      _ = U * P * (star U * U) * K * star U := by noncomm_ring
      _ = _ := by rw [hUleft]; noncomm_ring
  calc
    (U * star K * star U) * (U * P * star U)
          + (U * P * star U) * (U * K * star U) =
        U * (star K * P + P * K) * star U := by
          rw [hterm1, hterm2]
          noncomm_ring
    _ = -1 := by rw [hP]; simp [hUright]

/-- If the target Lyapunov equation has a unique solution, it is exactly the
unitary transport of the source solution. -/
theorem uniqueLyapunovSolution_unitaryConjugation
    (U K P P' : E →L[ℂ] E)
    (hUleft : star U * U = 1) (hUright : U * star U = 1)
    (hP : star K * P + P * K = -1)
    (hunique : ∀ Q : E →L[ℂ] E,
      star (U * K * star U) * Q + Q * (U * K * star U) = -1 → Q = P') :
    P' = U * P * star U := by
  symm
  exact hunique _
    (lyapunovEquation_unitaryConjugation U K P hUleft hUright hP)

/-- The full missing FC.17 transport layer: sampled Gram and canonical
Lyapunov metric are carried by the same unitary.  Together with
`hypocoercive_transport_words_and_grams`, this transports the whole finite
observability/Krylov packet. -/
theorem hypocoercive_cutoff_transport_exact
    (U K S P P' : E →L[ℂ] E)
    (hUleft : star U * U = 1) (hUright : U * star U = 1)
    (hP : star K * P + P * K = -1)
    (hunique : ∀ Q : E →L[ℂ] E,
      star (U * K * star U) * Q + Q * (U * K * star U) = -1 → Q = P')
    (T : ℝ) :
    sampledGram (U * K * star U) (U * S * star U) T =
        U * sampledGram K S T * star U ∧
      P' = U * P * star U :=
  ⟨sampledGram_unitaryConjugation U K S hUleft hUright T,
    uniqueLyapunovSolution_unitaryConjugation U K P P'
      hUleft hUright hP hunique⟩

end HypocoerciveCutoffTransport
end NCG
