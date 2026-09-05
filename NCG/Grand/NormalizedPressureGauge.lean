/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CalibrationTransportAndPressureGauge
import NCG.Grand.ScorePressureExact

/-!
# Normalized pressure gauge

This file completes `cth:GT-normalized-no-pressure`.  Adding a scalar function
of the parameter to every log-weight leaves the normalized law, its centred
score, and hence the score localizer unchanged.  The same gauge adds that
scalar to the log-partition function.  A quadratic gauge supplies arbitrary
second-order pressure curvature while preserving the base partition value.
-/

open Finset

namespace NCG
namespace NormalizedPressureGauge

open ScorePressure

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Add a state-independent scalar gauge to a family of log-weights. -/
def scalarGauge (φ : ℝ → Ω → ℝ) (c : ℝ → ℝ) : ℝ → Ω → ℝ :=
  fun θ ω => c θ + φ θ ω

/-- The scalar gauge factors out of the partition function. -/
theorem partition_scalarGauge (φ : ℝ → Ω → ℝ) (c : ℝ → ℝ) (θ : ℝ) :
    partition (scalarGauge φ c) θ = Real.exp (c θ) * partition φ θ := by
  simp only [partition, scalarGauge, Real.exp_add, Finset.mul_sum]

/-- The scalar factor cancels exactly in the normalized law. -/
theorem law_scalarGauge (φ : ℝ → Ω → ℝ) (c : ℝ → ℝ) (θ : ℝ) :
    law (scalarGauge φ c) θ = law φ θ := by
  funext ω
  rw [law, law, partition_scalarGauge]
  simp only [scalarGauge, Real.exp_add]
  field_simp [Real.exp_ne_zero (c θ)]

/-- Expectations of state observables are gauge invariant. -/
theorem expect_scalarGauge (φ : ℝ → Ω → ℝ) (c : ℝ → ℝ)
    (θ : ℝ) (f : Ω → ℝ) :
    ScorePressure.expect (scalarGauge φ c) θ f =
      ScorePressure.expect φ θ f := by
  simp only [ScorePressure.expect, law_scalarGauge]

/-- Adding a constant to the score does not change its centred representative. -/
theorem centeredScore_scalarGauge (φ : ℝ → Ω → ℝ) (c : ℝ → ℝ)
    (φ' : ℝ → Ω → ℝ) (c' : ℝ → ℝ) (θ : ℝ) (ω : Ω) :
    (φ' θ ω + c' θ) -
        ScorePressure.expect (scalarGauge φ c) θ (fun x => φ' θ x + c' θ) =
      φ' θ ω - ScorePressure.expect φ θ (φ' θ) := by
  rw [expect_scalarGauge]
  have hsum := law_sum φ θ
  unfold ScorePressure.expect
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show (∑ x, law φ θ x * c' θ) = c' θ by
    rw [← Finset.sum_mul, hsum, one_mul]]
  ring

/-- The score localizer (the variance of the logarithmic score) is exactly
invariant under a state-independent scalar gauge. -/
theorem variance_scalarGauge (φ : ℝ → Ω → ℝ) (c : ℝ → ℝ)
    (φ' : ℝ → Ω → ℝ) (c' : ℝ → ℝ) (θ : ℝ) :
    variance (scalarGauge φ c) θ (fun ω => φ' θ ω + c' θ) =
      variance φ θ (φ' θ) := by
  unfold variance
  rw [expect_scalarGauge]
  apply Finset.sum_congr rfl
  intro ω _
  change law φ θ ω *
      ((φ' θ ω + c' θ) -
        ScorePressure.expect (scalarGauge φ c) θ (fun x => φ' θ x + c' θ)) ^ 2 =
    law φ θ ω *
      (φ' θ ω - ScorePressure.expect φ θ (φ' θ)) ^ 2
  rw [centeredScore_scalarGauge]

/-- The Hellinger coordinates of the normalized family are gauge invariant. -/
theorem hellinger_scalarGauge (φ : ℝ → Ω → ℝ) (c : ℝ → ℝ) (θ : ℝ) :
    hellinger (scalarGauge φ c) θ = hellinger φ θ := by
  funext ω
  simp only [hellinger, law_scalarGauge]

/-- The log-partition changes by precisely the scalar gauge. -/
theorem log_partition_scalarGauge (φ : ℝ → Ω → ℝ) (c : ℝ → ℝ) (θ : ℝ) :
    Real.log (partition (scalarGauge φ c) θ) =
      c θ + Real.log (partition φ θ) := by
  rw [partition_scalarGauge,
    CalibrationTransportAndPressureGauge.log_partition_scalar_gauge]
  exact partition_pos φ θ

/-- A gauge with `c(0)=0` preserves the base partition value. -/
theorem base_partition_scalarGauge (φ : ℝ → Ω → ℝ) (c : ℝ → ℝ)
    (hc0 : c 0 = 0) :
    partition (scalarGauge φ c) 0 = partition φ 0 := by
  rw [partition_scalarGauge, hc0, Real.exp_zero, one_mul]

/-- Quadratic scalar gauges preserve the base value and contribute an arbitrary
second derivative `2a` to the absolute log-pressure. -/
theorem quadraticGauge_pressureCurvature
    (logZ dlogZ : ℝ → ℝ) (a θ z1 z2 : ℝ)
    (hZ' : HasDerivAt logZ (dlogZ θ) θ)
    (hZ'' : HasDerivAt dlogZ z2 θ) :
    HasDerivAt (fun x => logZ x + a * x ^ 2)
        (dlogZ θ + 2 * a * θ) θ ∧
      HasDerivAt (fun x => dlogZ x + 2 * a * x)
        (z2 + 2 * a) θ := by
  have hc' : HasDerivAt (fun x : ℝ => a * x ^ 2) (2 * a * θ) θ := by
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      ((hasDerivAt_id θ).pow 2).const_mul a
  have hc'' : HasDerivAt (fun x : ℝ => 2 * a * x) (2 * a) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 * a)
  exact CalibrationTransportAndPressureGauge.pressure_hessian_scalar_gauge
    logZ (fun x => a * x ^ 2) dlogZ (fun x => 2 * a * x)
    θ z1 0 z2 (2 * a) hZ' hc' hZ'' hc''

/-- Exact assembly of `cth:GT-normalized-no-pressure` (NL.10): the normalized
family and score localizer are unchanged, the base partition is unchanged, but
the absolute pressure curvature receives the freely chosen increment `2a`. -/
theorem normalized_no_pressure_exact
    (φ φ' : ℝ → Ω → ℝ) (a : ℝ) :
    law (scalarGauge φ (fun θ => a * θ ^ 2)) 0 = law φ 0 ∧
      variance (scalarGauge φ (fun θ => a * θ ^ 2)) 0
          (fun ω => φ' 0 ω + 0) = variance φ 0 (φ' 0) ∧
      partition (scalarGauge φ (fun θ => a * θ ^ 2)) 0 = partition φ 0 ∧
      (∀ θ, Real.log (partition (scalarGauge φ (fun x => a * x ^ 2)) θ) =
        a * θ ^ 2 + Real.log (partition φ θ)) := by
  refine ⟨law_scalarGauge φ _ 0, ?_, ?_, fun θ => log_partition_scalarGauge φ _ θ⟩
  · simpa using variance_scalarGauge φ (fun θ => a * θ ^ 2) φ' (fun _ => 0) 0
  · exact base_partition_scalarGauge φ _ (by simp)

end NormalizedPressureGauge
end NCG
