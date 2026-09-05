/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ChannelEstimates

/-!
# Exponential difference quotients in Banach algebras

The fixed-Fourier-mode symbol of a covariant forward difference is a
difference of two exponentials divided by the mesh.  This file gives its
first-order limit with a quantitative error bound valid in an arbitrary real
Banach algebra.
-/

open Filter NormedSpace Set Topology

namespace NCG

variable {A : Type} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Quantitative first-order estimate for the difference of two exponential
curves. -/
theorem norm_exponentialDifferenceQuotient_sub_le
    (X Y : A) (h : ℝ) (hh : 0 < h) :
    ‖h⁻¹ • (exp (h • X) - exp (h • Y)) - (X - Y)‖ ≤
      h * (‖X‖ ^ 2 * Real.exp (h * ‖X‖) +
        ‖Y‖ ^ 2 * Real.exp (h * ‖Y‖)) := by
  have hne : h ≠ 0 := ne_of_gt hh
  let RX : A := exp (h • X) - 1 - h • X
  let RY : A := exp (h • Y) - 1 - h • Y
  have hscaleX : h⁻¹ • (h • X) = X := by
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hscaleY : h⁻¹ • (h • Y) = Y := by
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hid :
      h⁻¹ • (exp (h • X) - exp (h • Y)) - (X - Y) =
        h⁻¹ • (RX - RY) := by
    calc
      h⁻¹ • (exp (h • X) - exp (h • Y)) - (X - Y) =
          h⁻¹ • ((exp (h • X) - h • X) -
            (exp (h • Y) - h • Y)) := by
        simp only [smul_sub]
        rw [hscaleX, hscaleY]
        abel
      _ = h⁻¹ • (RX - RY) := by
        congr 1
        dsimp [RX, RY]
        abel
  have hRX := ChannelEstimates.exp_sub_linear_bound (h • X)
  have hRY := ChannelEstimates.exp_sub_linear_bound (h • Y)
  have hnormX : ‖h • X‖ = h * ‖X‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  have hnormY : ‖h • Y‖ = h * ‖Y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  rw [hnormX] at hRX
  rw [hnormY] at hRY
  have hRX' : ‖RX‖ ≤ (h * ‖X‖) ^ 2 * Real.exp (h * ‖X‖) := by
    simpa only [RX] using hRX
  have hRY' : ‖RY‖ ≤ (h * ‖Y‖) ^ 2 * Real.exp (h * ‖Y‖) := by
    simpa only [RY] using hRY
  rw [hid, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hh]
  calc
    h⁻¹ * ‖RX - RY‖ ≤ h⁻¹ * (‖RX‖ + ‖RY‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hh.le)
    _ ≤ h⁻¹ *
        ((h * ‖X‖) ^ 2 * Real.exp (h * ‖X‖) +
          (h * ‖Y‖) ^ 2 * Real.exp (h * ‖Y‖)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hRX' hRY')
        (inv_nonneg.mpr hh.le)
    _ = h * (‖X‖ ^ 2 * Real.exp (h * ‖X‖) +
        ‖Y‖ ^ 2 * Real.exp (h * ‖Y‖)) := by
      field_simp

/-- The two-exponential quotient converges to the difference of its
generators from the positive-mesh side. -/
theorem exponentialDifferenceQuotient_tendsto_right
    (X Y : A) :
    Tendsto
      (fun h : ℝ =>
        ‖h⁻¹ • (exp (h • X) - exp (h • Y)) - (X - Y)‖)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  let bound : ℝ → ℝ := fun h =>
    h * (‖X‖ ^ 2 * Real.exp (h * ‖X‖) +
      ‖Y‖ ^ 2 * Real.exp (h * ‖Y‖))
  have hbound : Tendsto bound (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have hc : Continuous bound := by
      exact continuous_id.mul
        ((continuous_const.mul
          (Real.continuous_exp.comp (continuous_id.mul continuous_const))).add
        (continuous_const.mul
          (Real.continuous_exp.comp (continuous_id.mul continuous_const))))
    have h0 := hc.tendsto 0
    simp only [bound, zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact norm_exponentialDifferenceQuotient_sub_le X Y h hh

end NCG
