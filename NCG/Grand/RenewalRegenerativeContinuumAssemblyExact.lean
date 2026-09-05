/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GlobalCylinderDescentCStarCompletionExact
import NCG.Grand.StateTransport
import NCG.Grand.FluctuationObservability
import NCG.Grand.PhysicalRate
import NCG.Grand.MeanNoiseShort
import NCG.Grand.RenewalShortedHodgeAndCompactScreen

/-!
# Regenerative continuum assembly

This file supplies the packet-level theorem missing from the earlier slices of
`thm:renewal-regenerative-continuum`.  The packet contains the primitive
finite-regulator margins.  Its conclusion retains the exact quantitative
outputs, while the compatible finite states are descended to the unique state
on the completed inductive-limit C-star algebra.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.RenewalRegenerativeContinuum

universe u v

variable {V n i Hn eS eF Hp Ep : Type*}
variable [NormedAddCommGroup V]
variable [Fintype n] [DecidableEq n]
variable [Fintype i]
variable [Fintype Hn] [Fintype eS]
variable [Fintype Hp] [Fintype Ep] [DecidableEq Hp] [DecidableEq Ep]

/-- Exact conclusion of the renewal state-transport estimate. -/
def StateTransportConclusion (T : V → V) (q δ : ℝ) (e : V) : Prop :=
  ‖e‖ ≤ δ / (1 - q) ∧
    (δ = 0 → e = 0) ∧
    (T e = e → 0 ≤ ‖e‖ → ‖e‖ = 0)

/-- Exact finite covariance/Lyapunov output used by the regenerative packet. -/
def FluctuationDissipationConclusion
    (H K Q : Matrix n n ℂ) (dp : ℝ) : Prop :=
  (∀ A B : Matrix n n ℂ, (B - A).PosSemidef →
      (Kᴴ * B * K - Kᴴ * A * K).PosSemidef) ∧
  (∀ N : ℕ,
      (∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k)
          - Kᴴ * (∑ k ∈ Finset.range N,
              Kᴴ ^ k * Q * K ^ k) * K
        = Q - Kᴴ ^ N * Q * K ^ N) ∧
  (∀ k : ℕ,
      (((dp : ℂ) • (Kᴴ ^ k * H * K ^ k
          - Kᴴ ^ (k + 1) * H * K ^ (k + 1)))
        - Kᴴ ^ k * Q * K ^ k).PosSemidef) ∧
  (∀ C : Matrix n n ℂ, Hᴴ = H → ∀ _ : Invertible H,
      H - (H⁻¹ * C)ᴴ * H * (H⁻¹ * C)
        = H - Cᴴ * H⁻¹ * C)

/-- Exact compact Lyapunov/tightness output. -/
def LyapunovTightnessConclusion (κ b τ τmax x : ℝ) : Prop :=
  x ≤ b * τ / (1 - Real.exp (-(κ * τ))) ∧
  b * τ / (1 - Real.exp (-(κ * τ)))
      ≤ b * Real.exp (κ * τmax) / κ ∧
  (∀ z ψ : ℝ, 0 < ψ → ψ * z ≤ x → z ≤ x / ψ)

/-- Exact predictable-mean/noise-short conclusion. -/
def NoiseShortConclusion
    (S : Matrix Hn eS ℂ) (M N : Matrix Hn eF ℂ)
    (W : Matrix eS eF ℂ) (τ : ℝ)
    (Gn E : Matrix eF eF ℂ) : Prop :=
  ((M + N) - S * W)ᴴ * ((M + N) - S * W)
      = (M - S * W)ᴴ * (M - S * W) + Nᴴ * N ∧
  ((M + N) - S * W)ᴴ * ((M + N) - S * W)
      = (τ : ℂ) • Gn + ((M - S * W)ᴴ * (M - S * W) + E)

/-- Exact physical-time comparison and noncollapsing-rate output. -/
def PhysicalRateConclusion
    (T : Matrix Hp Hp ℂ) (V : Matrix Hp Ep ℂ)
    (W : Matrix Ep Ep ℂ) : Prop :=
  ‖T * V‖ ≤ ‖V * W‖ + ‖T * V - V * W‖ ∧
  ∀ m : ℕ, ‖T ^ m * V - V * W ^ m‖ ≤
    m * ‖T * V - V * W‖

/-- The finite complete-observability--Lyapunov packet.  Its fields are the
primitive margins appearing in the component theorems, not their conclusions. -/
structure FinitePacket where
  stateT : V → V
  stateQ : ℝ
  stateDefect : ℝ
  stateError : V
  stateQ_lt_one : stateQ < 1
  state_contracts : ‖stateT stateError‖ ≤ stateQ * ‖stateError‖
  state_defect_bound : ‖stateError - stateT stateError‖ ≤ stateDefect
  covarianceH : Matrix n n ℂ
  covarianceK : Matrix n n ℂ
  covarianceQ : Matrix n n ℂ
  covarianceScale : ℝ
  covariance_domination :
    (((covarianceScale : ℂ) •
      (covarianceH - covarianceKᴴ * covarianceH * covarianceK))
      - covarianceQ).PosSemidef
  lyapunovKappa : ℝ
  lyapunovB : ℝ
  physicalStep : ℝ
  maximalStep : ℝ
  stationaryEnergy : ℝ
  lyapunovKappa_pos : 0 < lyapunovKappa
  physicalStep_pos : 0 < physicalStep
  physicalStep_le : physicalStep ≤ maximalStep
  lyapunovB_nonneg : 0 ≤ lyapunovB
  stationary_drift : stationaryEnergy ≤
    Real.exp (-(lyapunovKappa * physicalStep)) * stationaryEnergy +
      lyapunovB * physicalStep
  screenEigenvalue : i → ℝ
  screenField : i → ℂ
  screenRadius : ℝ
  screenOrder : ℝ
  screenFloor : ℝ
  screenOffset : ℝ
  screenBudget : ℝ
  screenAction : ℝ
  screenEigenvalue_nonneg : ∀ j, 0 ≤ screenEigenvalue j
  screenRadius_nonneg : 0 ≤ screenRadius
  screenOrder_pos : 0 < screenOrder
  screenFloor_pos : 0 < screenFloor
  screenAction_le : screenAction ≤ screenBudget
  screen_coercive :
    screenFloor * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
        screenEigenvalue screenOrder screenField
      - screenOffset * (∑ j, Complex.normSq (screenField j)) ≤ screenAction
  source : Matrix Hn eS ℂ
  predictable : Matrix Hn eF ℂ
  noise : Matrix Hn eF ℂ
  sourceCoefficient : Matrix eS eF ℂ
  noiseScale : ℝ
  noiseGram : Matrix eF eF ℂ
  noiseRemainder : Matrix eF eF ℂ
  source_noise_orthogonal : sourceᴴ * noise = 0
  predictable_noise_orthogonal : predictableᴴ * noise = 0
  noise_scaling : noiseᴴ * noise =
    (noiseScale : ℂ) • noiseGram + noiseRemainder
  cycle : Matrix Hp Hp ℂ
  embedding : Matrix Hp Ep ℂ
  model : Matrix Ep Ep ℂ
  cycle_contraction : ‖cycle‖ ≤ 1
  model_contraction : ‖model‖ ≤ 1

/-- Packet-level analytic conclusions, with no semantic observable-limit claim
folded into the result. -/
structure AnalyticConclusions (P : FinitePacket
    (V := V) (n := n) (i := i) (Hn := Hn) (eS := eS) (eF := eF)
    (Hp := Hp) (Ep := Ep)) where
  stateTransport : StateTransportConclusion P.stateT P.stateQ
    P.stateDefect P.stateError
  fluctuationDissipation : FluctuationDissipationConclusion
    P.covarianceH P.covarianceK P.covarianceQ P.covarianceScale
  lyapunovTightness : LyapunovTightnessConclusion P.lyapunovKappa
    P.lyapunovB P.physicalStep P.maximalStep P.stationaryEnergy
  compactScreen :
    NCG.RenewalShortedHodgeAndCompactScreen.spectralTailNormSq
        P.screenEigenvalue P.screenRadius P.screenField ≤
      (P.screenBudget + P.screenOffset *
        (∑ j, Complex.normSq (P.screenField j))) /
      (P.screenFloor * (1 + P.screenRadius) ^ P.screenOrder)
  noiseShort : NoiseShortConclusion P.source P.predictable P.noise
    P.sourceCoefficient P.noiseScale P.noiseGram P.noiseRemainder
  physicalRate : PhysicalRateConclusion P.cycle P.embedding P.model

/-- The regenerative finite packet discharges all of its quantitative entrance
coordinates simultaneously. -/
theorem finitePacket_analytic_conclusions
    (P : FinitePacket
      (V := V) (n := n) (i := i) (Hn := Hn) (eS := eS) (eF := eF)
      (Hp := Hp) (Ep := Ep)) :
    AnalyticConclusions P := by
  refine {
    stateTransport := ?_
    fluctuationDissipation := ?_
    lyapunovTightness := ?_
    compactScreen := ?_
    noiseShort := ?_
    physicalRate := ?_ }
  · exact NCG.renewal_state_transport P.stateT P.stateQ P.stateDefect
      P.stateQ_lt_one P.stateError P.state_contracts P.state_defect_bound
  · exact NCG.renewal_fluctuation_dissipation P.covarianceH P.covarianceK
      P.covarianceQ P.covarianceScale P.covariance_domination
  · exact NCG.renewal_lyapunov_tightness P.lyapunovKappa P.lyapunovB
      P.physicalStep P.maximalStep P.stationaryEnergy P.lyapunovKappa_pos
      P.physicalStep_pos P.physicalStep_le P.lyapunovB_nonneg
      P.stationary_drift
  · exact NCG.RenewalShortedHodgeAndCompactScreen.common_compact_screen_bound
      P.screenEigenvalue P.screenField P.screenRadius P.screenOrder
      P.screenFloor P.screenOffset P.screenBudget P.screenAction
      P.screenEigenvalue_nonneg P.screenRadius_nonneg P.screenOrder_pos
      P.screenFloor_pos P.screenAction_le P.screen_coercive
  · exact NCG.renewal_noise_shorted_ward P.source P.predictable P.noise
      P.source_noise_orthogonal P.predictable_noise_orthogonal
      P.sourceCoefficient P.noiseScale P.noiseGram P.noiseRemainder
      P.noise_scaling
  · exact NCG.renewal_physical_rate P.cycle P.embedding P.model
      P.cycle_contraction P.model_contraction

section CompletedState

variable {ι₀ : Type u} [Preorder ι₀] [IsDirectedOrder ι₀] [Nonempty ι₀]
variable {A : ι₀ → Type v}
variable [∀ j, NormedRing (A j)] [∀ j, StarRing (A j)]
variable [∀ j, CStarRing (A j)] [∀ j, NormedAlgebra ℂ (A j)]
variable [∀ j, StarModule ℂ (A j)]
variable {f : ∀ j k, j ≤ k → A j →⋆ₐ[ℂ] A k}
variable [DirectedSystem A (fun j k hjk => f j k hjk)]
variable [NCG.PreCStarDirectLimit.IsometricSystem f]

/-- **Renewal-native reduction of the physical-continuum entrance.**  A
compatible (including summably corrected) regenerative state descends to one
and only one completed C-star state, while the same packet supplies all finite
quantitative entrance coordinates. -/
theorem renewal_regenerative_continuum
    (omega : NCG.PreCStarDirectLimit.CompatibleState f)
    (P : FinitePacket
      (V := V) (n := n) (i := i) (Hn := Hn) (eS := eS) (eF := eF)
      (Hp := Hp) (Ep := Ep)) :
    (∃! Omega : NCG.PreCStarDirectLimit.Completion f →ₚ[ℂ] ℂ,
      ∀ j (a : A j),
        Omega (NCG.PreCStarDirectLimit.completionOf f j a) =
          omega.state j a) ∧
    AnalyticConclusions P := by
  exact ⟨NCG.GlobalCylinderDescent.completedCylinderState_existsUnique omega,
    finitePacket_analytic_conclusions P⟩

end CompletedState

end NCG.RenewalRegenerativeContinuum
