/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Target-native calibration and scalar transport

Finite exact cores for the V047 target-native calibration statements.
-/

open Finset Filter Topology

namespace NCG
namespace TargetNativeCalibration

/-- Expectation of a real writer against a finite (not necessarily normalized)
weight. -/
def expectation {Ω : Type*} [Fintype Ω] (μ f : Ω → ℝ) : ℝ :=
  ∑ ω, μ ω * f ω

/-- Calibration against a declared multiplier bank. -/
def Calibrated {Ω H : Type*} [Fintype Ω]
    (μ Y w : Ω → ℝ) (h : H → Ω → ℝ) : Prop :=
  ∀ a, expectation μ (fun ω => h a ω * Y ω)
    = expectation μ (fun ω => h a ω * w ω)

/-- `thm:GT-multiplier-calibration`: zero multiplier residual is literally
equality of all multiplier-weighted expectations. -/
theorem multiplier_calibration_iff {Ω H : Type*} [Fintype Ω]
    (μ Y w : Ω → ℝ) (h : H → Ω → ℝ) :
    Calibrated μ Y w h ↔ ∀ a,
      expectation μ (fun ω => h a ω * Y ω)
        = expectation μ (fun ω => h a ω * w ω) := by
  rfl

/-- The selected-mean information split in
`thm:GT-multiplier-calibration`. -/
theorem mean_bias_identity {Ω : Type*} [Fintype Ω]
    (μ Y w : Ω → ℝ) :
    expectation μ Y - expectation μ w
      = expectation μ (fun ω => Y ω - w ω) := by
  simp only [expectation, mul_sub, sum_sub_distrib]

/-- Orthogonal visible/hidden calibration errors obey exact Pythagoras. -/
theorem calibration_information_split {Ω : Type*} [Fintype Ω]
    (μ d visible : Ω → ℝ)
    (horth : expectation μ (fun ω =>
      visible ω * (d ω - visible ω)) = 0) :
    expectation μ (fun ω => d ω ^ 2)
      = expectation μ (fun ω => visible ω ^ 2)
        + expectation μ (fun ω => (d ω - visible ω) ^ 2) := by
  simp only [expectation] at horth ⊢
  calc
    ∑ ω, μ ω * d ω ^ 2 =
        ∑ ω, (μ ω * visible ω ^ 2
          + 2 * (μ ω * (visible ω * (d ω - visible ω)))
          + μ ω * (d ω - visible ω) ^ 2) := by
            apply sum_congr rfl
            intro ω _
            ring
    _ = (∑ ω, μ ω * visible ω ^ 2)
        + ∑ ω, μ ω * (d ω - visible ω) ^ 2 := by
          simp only [sum_add_distrib]
          rw [show (∑ ω, 2 * (μ ω * (visible ω * (d ω - visible ω))))
              = 2 * ∑ ω, μ ω * (visible ω * (d ω - visible ω)) by
                rw [Finset.mul_sum]]
          rw [horth]
          ring

/-- `cor:GT-affine-two-anchor-calibration`: the calibrated affine response
recovers the writer mean. -/
theorem affine_response_mean (EY α β : ℝ) (hβ : β ≠ 0) :
    (EY - α) / β * β + α = EY := by
  rw [div_mul_cancel₀ _ hβ]
  ring

/-- Two distinct anchors uniquely determine an affine response. -/
theorem affine_two_anchors_unique (x₀ x₁ y₀ y₁ α β α' β' : ℝ)
    (hx : x₀ ≠ x₁)
    (h₀ : α + β * x₀ = y₀) (h₁ : α + β * x₁ = y₁)
    (h₀' : α' + β' * x₀ = y₀) (h₁' : α' + β' * x₁ = y₁) :
    α = α' ∧ β = β' := by
  have hprod : (β - β') * (x₁ - x₀) = 0 := by
    calc
      (β - β') * (x₁ - x₀) =
          (α + β * x₁ - (α' + β' * x₁))
            - (α + β * x₀ - (α' + β' * x₀)) := by ring
      _ = 0 := by rw [h₁, h₁', h₀, h₀']; ring
  have hxsub : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx.symm
  have hβeq : β = β' := by
    rcases mul_eq_zero.mp hprod with hβzero | hxzero
    · exact sub_eq_zero.mp hβzero
    · exact (hxsub hxzero).elim
  constructor
  · rw [hβeq] at h₀
    linarith
  · exact hβeq

/-- `thm:GT-target-interval-transport`: sharp adjacent-cutoff interval. -/
theorem target_interval_transport {LX JX UX LY JY UY : ℝ}
    (hLX : LX ≤ JX) (hXU : JX ≤ UX)
    (hLY : LY ≤ JY) (hYU : JY ≤ UY) :
    LY - UX ≤ JY - JX ∧ JY - JX ≤ UY - LX := by
  constructor <;> linarith

/-- Absolute form of the target interval transport bound. -/
theorem target_interval_transport_abs {LX JX UX LY JY UY : ℝ}
    (hLX : LX ≤ JX) (hXU : JX ≤ UX)
    (hLY : LY ≤ JY) (hYU : JY ≤ UY) :
    |JY - JX| ≤ max (UY - LX) (UX - LY) := by
  rw [abs_le]
  constructor
  · have hlower := (target_interval_transport hLX hXU hLY hYU).1
    have hmax := le_max_right (UY - LX) (UX - LY)
    linarith
  · exact (target_interval_transport hLX hXU hLY hYU).2.trans
      (le_max_left _ _)

/-- `thm:arithmetic-scalar-cutoff` is the same target-native interval law. -/
theorem arithmetic_scalar_cutoff {LX JX UX LY JY UY : ℝ}
    (hLX : LX ≤ JX) (hXU : JX ≤ UX)
    (hLY : LY ≤ JY) (hYU : JY ≤ UY) :
    LY - UX ≤ JY - JX ∧ JY - JX ≤ UY - LX :=
  target_interval_transport hLX hXU hLY hYU

/-- The calibration information against the constant subspace for one
selected scalar expectation.  This is the one-dimensional Gram residual
appearing in `cor:accepted-target-native-scalar`. -/
def scalarCalibrationDefect (EY Ew : ℝ) : ℝ := (EY - Ew) ^ 2

/-- Vanishing scalar calibration information is exactly equality of the
physical Read and writer expectations. -/
theorem scalarCalibrationDefect_eq_zero_iff (EY Ew : ℝ) :
    scalarCalibrationDefect EY Ew = 0 ↔ EY = Ew := by
  rw [scalarCalibrationDefect, sq_eq_zero_iff, sub_eq_zero]

/-- `cor:accepted-target-native-scalar`: calibration against constants closes
the selected scalar. -/
theorem accepted_target_native_scalar (EY Ew : ℝ)
    (h : scalarCalibrationDefect EY Ew = 0) : EY = Ew :=
  (scalarCalibrationDefect_eq_zero_iff EY Ew).mp h

/-- `cor:GT-calibrated-scalar-cofinal`: a vanishing calibration error transfers
a Cauchy Read limit to the selected writer means. -/
theorem calibrated_scalar_tendsto {EY Ew ε : ℕ → ℝ} {L : ℝ}
    (hread : Tendsto EY atTop (nhds L))
    (herr : ∀ n, |EY n - Ew n| ≤ ε n)
    (hε : Tendsto ε atTop (nhds 0)) :
    Tendsto Ew atTop (nhds L) := by
  have hdiff : Tendsto (fun n => EY n - Ew n) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using hε.neg) hε ?_ ?_
    · intro n
      exact neg_le_of_abs_le (herr n)
    · intro n
      exact le_of_abs_le (herr n)
  have := hread.sub hdiff
  simpa using this

end TargetNativeCalibration
end NCG
