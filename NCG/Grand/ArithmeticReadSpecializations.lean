/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TargetSandwichSharpExact
import NCG.Grand.TargetUnisolventCalibration
import NCG.Grand.CalibrationTransportAndPressureGauge
import NCG.Grand.TargetNativeCalibration
import NCG.Grand.FiniteCalibrationAndDynamicalCounterexamples
import NCG.Grand.TargetNativeReadLayerExact
import NCG.Grand.TrineTransportExtras

/-!
# Arithmetic Read specializations

The arithmetic records `thm:arithmetic-order-interval`,
`thm:arithmetic-calibration-compiler` and `thm:arithmetic-complex-quotient`
are, by their manuscript proofs, the general Gran-Tensor read-layer theorems
"applied to the finite arithmetic writer system".  The arithmetic loading
(chronology orientation, Peano relations) fixes *which* finite writer system,
reference law, or multiplier rows are used; it does not change the
statements.  This file records each arithmetic record as the corresponding
general theorem instantiated at an arbitrary finite writer system / finite
quotient / multiplier bank, so that the arithmetic record is formally the
specialization of the proved general record.

* `arithmetic_order_interval` — `thm:GT-target-sandwich` (sharp interval,
  attained endpoints, identification criterion);
* `arithmetic_calibration_residual`, `arithmetic_comparator_not_pairwise`,
  `arithmetic_calibration_cutoff_transport`,
  `arithmetic_calibrated_scalar_cofinal` — the four cited components of
  `thm:arithmetic-calibration-compiler`;
* `arithmetic_amplitude_representation`, `arithmetic_boundary_weight_tower`,
  `arithmetic_lebesgue_decomposition`, `arithmetic_global_phase_iff`,
  `arithmetic_trine_floor`, `arithmetic_common_gain`,
  `arithmetic_payoff_transport`, `arithmetic_trine_cofinal`,
  `arithmetic_normalized_amplitude` — the cited components of
  `thm:arithmetic-complex-quotient`.
-/

open Finset Filter Topology Matrix

namespace NCG
namespace ArithmeticReadSpecializations

/-! ### `thm:arithmetic-order-interval` -/

section OrderInterval

open BoundedWriterComparison

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

set_option linter.unusedFintypeInType false in
/-- **Arithmetic order interval**: for a finite unital arithmetic writer
system `S` with order-positive value functional `Φ` and a target writer `w`,
every compatible positive extension lies in the minorant–majorant interval,
both endpoints are attained, and the target is identified iff the interval
collapses. -/
theorem arithmetic_order_interval (S : Submodule ℝ (Ω → ℝ)) (Φ : S →ₗ[ℝ] ℝ)
    (hunit : constWriter (1 : ℝ) ∈ S) (hΦ : OrderPositive S Φ) (w : Ω → ℝ) :
    (∀ g : (Ω → ℝ) →ₗ[ℝ] ℝ, IsPositiveExtension S Φ g →
        lowEnd S Φ w ≤ g w ∧ g w ≤ highEnd S Φ w) ∧
      (∃ g : (Ω → ℝ) →ₗ[ℝ] ℝ, IsPositiveExtension S Φ g ∧ g w = lowEnd S Φ w) ∧
      (∃ g : (Ω → ℝ) →ₗ[ℝ] ℝ, IsPositiveExtension S Φ g ∧ g w = highEnd S Φ w) ∧
      ((∀ g₁ g₂ : (Ω → ℝ) →ₗ[ℝ] ℝ, IsPositiveExtension S Φ g₁ →
          IsPositiveExtension S Φ g₂ → g₁ w = g₂ w) ↔ lowEnd S Φ w = highEnd S Φ w) :=
  ⟨fun g hg => extension_value_mem_interval S Φ hunit w g hg,
    exists_extension_attaining_low S Φ hunit hΦ w,
    exists_extension_attaining_high S Φ hunit hΦ w,
    identified_iff_interval_collapses S Φ hunit hΦ w⟩

end OrderInterval

/-! ### `thm:arithmetic-calibration-compiler` -/

section Calibration

open TargetUnisolventCalibration in
/-- **Arithmetic calibration residual**: for acquired multiplier rows `C` and
intended target rows `T`, the residual vanishes iff the acquired rows
determine the target bank (kernel inclusion / `TargetRowsDetermined`), and its
rank is the rank of `T` on `Ker C`. -/
theorem arithmetic_calibration_residual {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ) :
    (targetCalibrationResidual C T = 0 ↔
      ∀ x : Fin d → ℂ, C *ᵥ x = 0 → T *ᵥ x = 0)
    ∧ (targetCalibrationResidual C T = 0 ↔ TargetRowsDetermined C T)
    ∧ (targetCalibrationResidual C T).rank =
      ((1 - sourceRangeProjection Cᴴ) * Tᴴ).rank :=
  target_unisolvent_calibration C T

open FiniteCalibrationAndDynamicalCounterexamples in
/-- **Comparator occurrence is not pairwise-determined**: the even and odd
parity laws share all one- and two-record marginals and differ. -/
theorem arithmetic_comparator_not_pairwise :
    (∀ w u, ∑ b, evenParityLaw w u b = ∑ b, oddParityLaw w u b)
    ∧ (∀ w b, ∑ u, evenParityLaw w u b = ∑ u, oddParityLaw w u b)
    ∧ (∀ u b, ∑ w, evenParityLaw w u b = ∑ w, oddParityLaw w u b)
    ∧ evenParityLaw 0 0 0 = 1 / 4
    ∧ oddParityLaw 0 0 0 = 0 :=
  pairwise_panels_do_not_determine_comparator

open CalibrationTransportAndPressureGauge in
/-- **Adjacent-cutoff transport of the selected calibration bias**
(CAL.7–CAL.8). -/
theorem arithmetic_calibration_cutoff_transport {ΩY ΩX : Type*}
    [Fintype ΩY] [Fintype ΩX]
    (π : ΩY → ΩX) (μY : ΩY → ℝ) (μX : ΩX → ℝ)
    (dY : ΩY → ℝ) (dX : ΩX → ℝ) (fine old tv : ℝ)
    (hfine : supBound (fun y => dY y - dX (π y)) fine)
    (hold : supBound dX old) (hfine0 : 0 ≤ fine) (hold0 : 0 ≤ old)
    (htv0 : 0 ≤ tv)
    (hpush :
      |expectation μY (fun y => dX (π y)) - expectation μX dX| ≤ old * tv)
    (hμY : ∀ y, 0 ≤ μY y) (hμYsum : ∑ y, μY y = 1) :
    (expectation μY dY - expectation μX dX =
      expectation μY (fun y => dY y - dX (π y))
        + (expectation μY (fun y => dX (π y)) - expectation μX dX))
    ∧ |expectation μY dY - expectation μX dX| ≤ fine + old * tv :=
  ⟨selected_bias_transport_identity π μY μX dY dX,
    selected_bias_transport_bound π μY μX dY dX fine old tv hfine hold hfine0 hold0 htv0
      hpush hμY hμYsum⟩

open TargetNativeCalibration in
/-- **Calibrated scalar cofinality**: a selected arithmetic scalar converges
along a cofinal family once the Read converges and the calibration error
vanishes. -/
theorem arithmetic_calibrated_scalar_cofinal {EY Ew ε : ℕ → ℝ} {L : ℝ}
    (hread : Tendsto EY atTop (𝓝 L))
    (herr : ∀ n, |EY n - Ew n| ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto Ew atTop (𝓝 L) :=
  calibrated_scalar_tendsto hread herr hε

end Calibration

/-! ### `thm:arithmetic-complex-quotient` -/

section ComplexQuotient

open FiniteTargetProjectionAndQuotients AcceptedActionInformationPythagoras
  TrineComplexAcquisitionAndTransport

/-- **Arithmetic amplitude representation**: `J(a) = ∫ a dζ_T = E_ν[w_T a]`
under domination on the quotient. -/
theorem arithmetic_amplitude_representation
    {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    (T : Ω → X) (ζ : Ω → ℂ) (ν : Ω → ℝ)
    (f : X → ℂ) (hT : Function.Surjective T)
    (hν : ∀ ω, 0 < ν ω) :
    complexIntegral ζ (fun ω => f (T ω)) =
      complexIntegral (fun x => (pushforwardRow T ν x : ℂ))
        (fun x => projectedComplexWeight T ζ ν x * f x) :=
  projected_complex_representation T ζ ν f hT hν

set_option linter.unusedFintypeInType false in
/-- **Boundary weight tower**: the coarser boundary weight is the conditional
expectation of the quotient weight. -/
theorem arithmetic_boundary_weight_tower
    {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (T : Ω → X) (s : X → Y) (ζ : Ω → ℂ)
    (ν : Ω → ℝ) (hT : Function.Surjective T)
    (hν : ∀ ω, 0 < ν ω) (y : Y) :
    projectedComplexWeight (fun ω => s (T ω)) ζ ν y =
      (Finset.univ.filter (fun x => s x = y)).sum (fun x =>
        (pushforwardRow T ν x : ℂ) * projectedComplexWeight T ζ ν x) /
        (pushforwardRow s (pushforwardRow T ν) y : ℂ) :=
  projected_complex_tower T s ζ ν hT hν y

/-- **Lebesgue decomposition on the quotient**: a singular component invisible
after projection is separated from the dominated part. -/
theorem arithmetic_lebesgue_decomposition {X : Type*}
    (ζT : X → ℂ) (νT : X → ℝ) (x : X) :
    ζT x = complexRegularDensity ζT νT x * (νT x : ℂ)
      + complexSingularPart ζT νT x :=
  complex_lebesgue_decomposition ζT νT x

/-- **Global phase criterion**: a normalized positive target law reproducing
every amplitude exists iff the quotient weight has one global phase. -/
theorem arithmetic_global_phase_iff {X : Type*} [Fintype X]
    (ζT : X → ℂ) (hZ : (∑ x, ζT x) ≠ 0) :
    (∃ μ : X → ℝ, (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x) = 1 ∧
        ∀ f : X → ℂ, (∑ x, ζT x * f x)
          = (∑ x, ζT x) * ∑ x, (μ x : ℂ) * f x)
      ↔ ∀ x, ∃ r : ℝ, 0 ≤ r ∧ ζT x = (∑ x, ζT x) * r :=
  positive_shadow_iff ζT hZ

/-- **Trine floor** `2|ζ| ≤ τ`: the complex amplitude of a trine packet is
dominated by half the carrier mass. -/
theorem arithmetic_trine_floor
    {p q x y : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdet : x ^ 2 + y ^ 2 ≤ p * q) :
    2 * Real.sqrt (x ^ 2 + y ^ 2) ≤ p + q :=
  trace_minimal_positive_lift hp hq hdet

/-- **Common gain cancels** from normalized visibility. -/
theorem arithmetic_common_gain {g t x y : ℝ} (hg : g ≠ 0) (ht : t ≠ 0) :
    (g * x) / (g * t) = x / t ∧ (g * y) / (g * t) = y / t :=
  common_gain_visibility hg ht

/-- **Payoff transport** across an adjacent cutoff map with trine defect `ε`. -/
theorem arithmetic_payoff_transport {ΩY X : Type*} [Fintype ΩY] [Fintype X]
    [DecidableEq X] (π : ΩY → X) (ζX : X → ℂ) (ζY : ΩY → ℂ)
    (A : X → ℂ) (M ε : ℝ) (hA : ∀ x, ‖A x‖ ≤ M)
    (hε : complexVariation (fun x => ζX x - complexPushforward π ζY x) ≤ ε)
    (hM : 0 ≤ M) :
    ‖complexIntegral ζX A - complexIntegral ζY (fun ω => A (π ω))‖ ≤ M * ε :=
  trine_payoff_transport π ζX ζY A M ε hA hε hM

/-- **Cofinal convergence** of the positive outcome measures under summable
defects, and of their linear (carrier/complex) outputs. -/
theorem arithmetic_trine_cofinal {X : Type*} [Fintype X]
    (ρ : Fin 3 → ℕ → (X → ℝ)) (ε : ℕ → ℝ)
    (hstep : ∀ k n, dist (ρ k n) (ρ k (n + 1)) ≤ ε n)
    (hsum : Summable ε) :
    ∀ k, ∃ limit : X → ℝ, Tendsto (ρ k) atTop (𝓝 limit) :=
  trine_positive_outcome_cofinal ρ ε hstep hsum

/-- **Normalized amplitudes** converge under a nonvanishing partition floor. -/
theorem arithmetic_normalized_amplitude {X : Type*}
    (τ : ℕ → X → ℝ) (ζ : ℕ → X → ℂ) (τlim : X → ℝ) (ζlim : X → ℂ)
    (hτ : ∀ x, Tendsto (fun n => τ n x) atTop (𝓝 (τlim x)))
    (hζ : ∀ x, Tendsto (fun n => ζ n x) atTop (𝓝 (ζlim x)))
    (x : X) (hfloor : τlim x ≠ 0) :
    Tendsto (fun n => ζ n x / (τ n x : ℂ)) atTop (𝓝 (ζlim x / (τlim x : ℂ))) :=
  normalized_amplitude_tendsto τ ζ τlim ζlim hτ hζ x hfloor

end ComplexQuotient

end ArithmeticReadSpecializations
end NCG
