/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Calibration transport and the normalized-pressure gauge

Finite exact forms of the selected-bias transport identity, its total-variation
bound and conditional Pythagoras, together with the scalar gauge obstruction to
recovering an absolute pressure Hessian from normalized laws.
-/

open Finset Filter Topology

namespace NCG
namespace CalibrationTransportAndPressureGauge

def expectation {Ω : Type*} [Fintype Ω] (μ f : Ω → ℝ) : ℝ :=
  ∑ ω, μ ω * f ω

def totalVariation {Ω : Type*} [Fintype Ω] (σ : Ω → ℝ) : ℝ :=
  ∑ ω, |σ ω|

def supBound {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) : Prop :=
  ∀ ω, |f ω| ≤ c

/-- `thm:GT-calibration-cutoff-transport`, equation (CAL.7). -/
theorem selected_bias_transport_identity {ΩY ΩX : Type*}
    [Fintype ΩY] [Fintype ΩX]
    (π : ΩY → ΩX) (μY : ΩY → ℝ) (μX : ΩX → ℝ)
    (dY : ΩY → ℝ) (dX : ΩX → ℝ) :
    expectation μY dY - expectation μX dX =
      expectation μY (fun y => dY y - dX (π y))
        + (expectation μY (fun y => dX (π y)) - expectation μX dX) := by
  simp only [expectation, mul_sub, sum_sub_distrib]
  ring

/-- Finite total-variation duality in the normalization used in (CAL.8). -/
theorem expectation_abs_le_totalVariation {Ω : Type*} [Fintype Ω]
    (σ f : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : supBound f c) :
    |expectation σ f| ≤ c * totalVariation σ := by
  calc
    |expectation σ f| ≤ ∑ ω, |σ ω * f ω| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, c * |σ ω| := by
      apply sum_le_sum
      intro ω _
      rw [abs_mul, mul_comm c]
      exact mul_le_mul_of_nonneg_left (hf ω) (abs_nonneg _)
    _ = c * totalVariation σ := by
      simp [totalVariation, Finset.mul_sum]

/-- `thm:GT-calibration-cutoff-transport`, equation (CAL.8), with the
pushforward discrepancy supplied as the signed old-record law. -/
theorem selected_bias_transport_bound {ΩY ΩX : Type*}
    [Fintype ΩY] [Fintype ΩX]
    (π : ΩY → ΩX) (μY : ΩY → ℝ) (μX : ΩX → ℝ)
    (dY : ΩY → ℝ) (dX : ΩX → ℝ) (fine old tv : ℝ)
    (hfine : supBound (fun y => dY y - dX (π y)) fine)
    (hold : supBound dX old) (hfine0 : 0 ≤ fine) (hold0 : 0 ≤ old)
    (htv0 : 0 ≤ tv)
    (hpush :
      |expectation μY (fun y => dX (π y)) - expectation μX dX| ≤ old * tv)
    (hμY : ∀ y, 0 ≤ μY y) (hμYsum : ∑ y, μY y = 1) :
    |expectation μY dY - expectation μX dX| ≤ fine + old * tv := by
  rw [selected_bias_transport_identity]
  refine (abs_add_le _ _).trans ?_
  gcongr
  · calc
      |expectation μY (fun y => dY y - dX (π y))|
          ≤ expectation μY (fun y => |dY y - dX (π y)|) := by
            rw [expectation]
            calc
              |∑ y, μY y * (dY y - dX (π y))|
                  ≤ ∑ y, |μY y * (dY y - dX (π y))| :=
                    abs_sum_le_sum_abs _ _
              _ = ∑ y, μY y * |dY y - dX (π y)| := by
                    apply sum_congr rfl
                    intro y _
                    rw [abs_mul, abs_of_nonneg (hμY y)]
      _ ≤ expectation μY (fun _ => fine) := by
            apply sum_le_sum
            intro y _
            exact mul_le_mul_of_nonneg_left (hfine y) (hμY y)
      _ = fine := by simp [expectation, ← Finset.sum_mul, hμYsum]

/-- `thm:GT-calibration-cutoff-transport`, equation (CAL.9).  The hypothesis
is precisely the defining orthogonality of conditional expectation. -/
theorem hidden_calibration_birth_pythagoras {Ω : Type*} [Fintype Ω]
    (μ d down : Ω → ℝ)
    (horth : expectation μ (fun ω => down ω * (d ω - down ω)) = 0) :
    expectation μ (fun ω => d ω ^ 2) =
      expectation μ (fun ω => down ω ^ 2) +
        expectation μ (fun ω => (d ω - down ω) ^ 2) := by
  simp only [expectation] at horth ⊢
  calc
    ∑ ω, μ ω * d ω ^ 2 =
        ∑ ω, (μ ω * down ω ^ 2
          + 2 * (μ ω * (down ω * (d ω - down ω)))
          + μ ω * (d ω - down ω) ^ 2) := by
            apply sum_congr rfl
            intro ω _
            ring
    _ = (∑ ω, μ ω * down ω ^ 2)
        + ∑ ω, μ ω * (d ω - down ω) ^ 2 := by
          simp only [sum_add_distrib]
          rw [show (∑ ω, 2 * (μ ω * (down ω * (d ω - down ω))))
              = 2 * ∑ ω, μ ω * (down ω * (d ω - down ω)) by
                rw [Finset.mul_sum]]
          rw [horth]
          ring

/-- Multiplying every unnormalized weight by the same nonzero scalar does not
change its normalized law. -/
theorem normalized_weight_scalar_gauge {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (a : ℝ) (ha : a ≠ 0) (hZ : ∑ ω, w ω ≠ 0) :
    (fun ω => (a * w ω) / ∑ z, a * w z) =
      fun ω => w ω / ∑ z, w z := by
  funext ω
  rw [← Finset.mul_sum]
  field_simp

/-- The logarithmic partition changes by the scalar gauge on its positive
branch. -/
theorem log_partition_scalar_gauge (c Z : ℝ) (hZ : 0 < Z) :
    Real.log (Real.exp c * Z) = c + Real.log Z := by
  rw [Real.log_mul (Real.exp_ne_zero c) (ne_of_gt hZ), Real.log_exp]

/-- `cth:GT-normalized-no-pressure`, equation (NL.10): once the logarithmic
partition is shifted by `c`, its second derivative is shifted by `c''`. -/
theorem pressure_hessian_scalar_gauge
    (logZ c dlogZ dc : ℝ → ℝ) (θ hZ hc hZ2 hc2 : ℝ)
    (hZ' : HasDerivAt logZ (dlogZ θ) θ)
    (hc' : HasDerivAt c (dc θ) θ)
    (hZ'' : HasDerivAt dlogZ hZ2 θ)
    (hc'' : HasDerivAt dc hc2 θ) :
    HasDerivAt (fun x => logZ x + c x) (dlogZ θ + dc θ) θ
      ∧ HasDerivAt (fun x => dlogZ x + dc x) (hZ2 + hc2) θ := by
  exact ⟨hZ'.add hc', hZ''.add hc''⟩

end CalibrationTransportAndPressureGauge
end NCG
