/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ArithmeticReadSpecializations
import NCG.Grand.ExactSourceSchurResidual

/-!
# Exact finite arithmetic calibration compiler

This bundles the finite calibration residual, comparator counterexample,
adjacent-cutoff transport, hidden calibration birth, and scalar cofinality
into the single packet asserted by `thm:arithmetic-calibration-compiler`.
-/

open Matrix Finset Filter Topology
open scoped ComplexOrder

namespace NCG
namespace ArithmeticCalibrationCompiler

open TargetUnisolventCalibration
open ArithmeticReadSpecializations
open CalibrationTransportAndPressureGauge
open FiniteCalibrationAndDynamicalCounterexamples

/-- `thm:arithmetic-calibration-compiler`, exact assembled finite packet. -/
theorem arithmetic_calibration_compiler_exact
    {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ)
    {OmegaY OmegaX Omega : Type*}
    [Fintype OmegaY] [Fintype OmegaX] [Fintype Omega]
    (pi : OmegaY → OmegaX) (muY : OmegaY → ℝ) (muX : OmegaX → ℝ)
    (dY : OmegaY → ℝ) (dX : OmegaX → ℝ)
    (fine old tv : ℝ)
    (hfine : supBound (fun y => dY y - dX (pi y)) fine)
    (hold : supBound dX old) (hfine0 : 0 ≤ fine) (hold0 : 0 ≤ old)
    (htv0 : 0 ≤ tv)
    (hpush :
      |expectation muY (fun y => dX (pi y)) - expectation muX dX|
        ≤ old * tv)
    (hmuY : ∀ y, 0 ≤ muY y) (hmuYsum : ∑ y, muY y = 1)
    (mu delta down : Omega → ℝ)
    (horth : expectation mu (fun w => down w * (delta w - down w)) = 0)
    {EY Ew eps : ℕ → ℝ} {L : ℝ}
    (hread : Tendsto EY atTop (𝓝 L))
    (herr : ∀ n, |EY n - Ew n| ≤ eps n)
    (heps : Tendsto eps atTop (𝓝 0)) :
    (targetCalibrationResidual C T).PosSemidef
      ∧ ((targetCalibrationResidual C T = 0) ↔
        ∀ x : Fin d → ℂ, C *ᵥ x = 0 → T *ᵥ x = 0)
      ∧ ((targetCalibrationResidual C T = 0) ↔
        TargetRowsDetermined C T)
      ∧ (targetCalibrationResidual C T).rank =
        ((1 - sourceRangeProjection Cᴴ) * Tᴴ).rank
      ∧ ((∀ w u, ∑ b, evenParityLaw w u b = ∑ b, oddParityLaw w u b)
        ∧ (∀ w b, ∑ u, evenParityLaw w u b = ∑ u, oddParityLaw w u b)
        ∧ (∀ u b, ∑ w, evenParityLaw w u b = ∑ w, oddParityLaw w u b)
        ∧ evenParityLaw 0 0 0 = 1 / 4
        ∧ oddParityLaw 0 0 0 = 0)
      ∧ (expectation muY dY - expectation muX dX =
          expectation muY (fun y => dY y - dX (pi y)) +
            (expectation muY (fun y => dX (pi y)) - expectation muX dX)
        ∧ |expectation muY dY - expectation muX dX| ≤ fine + old * tv)
      ∧ expectation mu (fun w => delta w ^ 2) =
          expectation mu (fun w => down w ^ 2) +
            expectation mu (fun w => (delta w - down w) ^ 2)
      ∧ Tendsto Ew atTop (𝓝 L) := by
  have hcal := arithmetic_calibration_residual C T
  refine ⟨?_, hcal.1, hcal.2.1, hcal.2.2, ?_, ?_, ?_, ?_⟩
  · exact sourceSchurResidual_posSemidef Cᴴ Tᴴ
  · exact arithmetic_comparator_not_pairwise
  · exact arithmetic_calibration_cutoff_transport pi muY muX dY dX
      fine old tv hfine hold hfine0 hold0 htv0 hpush hmuY hmuYsum
  · exact hidden_calibration_birth_pythagoras mu delta down horth
  · exact arithmetic_calibrated_scalar_cofinal hread herr heps

end ArithmeticCalibrationCompiler
end NCG
