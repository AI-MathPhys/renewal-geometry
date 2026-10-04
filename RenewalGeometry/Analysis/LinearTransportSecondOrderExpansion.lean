/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Second-order expansion of linear transport

Let `A` be a normed `ℝ`-algebra and `U : ℝ → A` a solution of the linear transport equation
`U' = U Ω(t)`, `U(0) = 1`, with a coefficient that is bounded and Lipschitz at `0` on `[0, h]`:
`‖Ω(t)‖ ≤ B`, `‖Ω(t) - Ω(0)‖ ≤ L t`.  Then

`‖U(h) - 1 - h Ω(0)‖ ≤ (B² ‖1‖ e^{Bh} + L) h²` (`norm_transport_sub_le`).

This is the expansion `U_j = I + h Ω_j + O(h²)` of exact (inverse) spin parallel transport along a
lattice edge used in `lem:supp-general-core` of the paper `predictive_spectral_geometry`.  The
proof is Grönwall's inequality (`‖U(t)‖ ≤ ‖1‖ e^{Bt}`) followed by two applications of the
mean-value inequality.
-/

open Set Real

namespace RenewalGeometry.LinearTransport

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- **Grönwall bound for linear transport**: `‖U(t)‖ ≤ ‖1‖ e^{Bt}` on `[0, h]`. -/
theorem norm_transport_le {Ω U : ℝ → A} {h B : ℝ}
    (hΩB : ∀ t ∈ Icc 0 h, ‖Ω t‖ ≤ B) (hU0 : U 0 = 1)
    (hU : ∀ t, HasDerivAt U (U t * Ω t) t) :
    ∀ t ∈ Icc 0 h, ‖U t‖ ≤ ‖(1 : A)‖ * exp (B * t) := by
  intro t ht
  have hcont : ContinuousOn U (Icc 0 h) := fun s _ => (hU s).continuousAt.continuousWithinAt
  have h1 := norm_le_gronwallBound_of_norm_deriv_right_le (f := U) (f' := fun s => U s * Ω s)
    (δ := ‖(1 : A)‖) (K := B) (ε := 0) hcont (fun s _ => (hU s).hasDerivWithinAt)
    (by rw [hU0]) (fun s hs => by
      rw [add_zero]
      refine (norm_mul_le _ _).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hΩB s (Ico_subset_Icc_self hs)) (norm_nonneg _)) t ht
  rwa [gronwallBound_ε0, sub_zero] at h1

/-- **First-order bound**: `‖U(t) - 1‖ ≤ B ‖1‖ e^{Bh} t` on `[0, h]`. -/
theorem norm_transport_sub_one_le {Ω U : ℝ → A} {h B : ℝ} (hB : 0 ≤ B)
    (hΩB : ∀ t ∈ Icc 0 h, ‖Ω t‖ ≤ B) (hU0 : U 0 = 1)
    (hU : ∀ t, HasDerivAt U (U t * Ω t) t) :
    ∀ t ∈ Icc 0 h, ‖U t - 1‖ ≤ B * ‖(1 : A)‖ * exp (B * h) * t := by
  intro t ht
  have hbound : ∀ s ∈ Ico 0 h, ‖U s * Ω s‖ ≤ B * ‖(1 : A)‖ * exp (B * h) := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    refine (norm_mul_le _ _).trans ?_
    have h1 := norm_transport_le hΩB hU0 hU s hs'
    have h2 : exp (B * s) ≤ exp (B * h) := exp_le_exp.2 (mul_le_mul_of_nonneg_left hs'.2 hB)
    calc ‖U s‖ * ‖Ω s‖ ≤ (‖(1 : A)‖ * exp (B * h)) * B := by
          refine mul_le_mul (h1.trans ?_) (hΩB s hs') (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = B * ‖(1 : A)‖ * exp (B * h) := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := U) (f' := fun s => U s * Ω s)
    (fun s _ => (hU s).hasDerivWithinAt) hbound t ht
  rwa [hU0, sub_zero] at this

/-- **Second-order expansion of linear transport**:
`‖U(h) - 1 - h Ω(0)‖ ≤ (B² ‖1‖ e^{Bh} + L) h²`. -/
theorem norm_transport_sub_le {Ω U : ℝ → A} {h B L : ℝ} (hh : 0 ≤ h) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hΩB : ∀ t ∈ Icc 0 h, ‖Ω t‖ ≤ B) (hΩL : ∀ t ∈ Icc 0 h, ‖Ω t - Ω 0‖ ≤ L * t)
    (hU0 : U 0 = 1) (hU : ∀ t, HasDerivAt U (U t * Ω t) t) :
    ‖U h - 1 - h • Ω 0‖ ≤ (B ^ 2 * ‖(1 : A)‖ * exp (B * h) + L) * h ^ 2 := by
  set g : ℝ → A := fun t => U t - 1 - t • Ω 0
  have hg : ∀ t, HasDerivAt g (U t * Ω t - Ω 0) t := by
    intro t
    have h1 := ((hU t).sub_const 1).sub ((hasDerivAt_id t).smul_const (Ω 0))
    rw [one_smul] at h1
    exact h1
  have hbound : ∀ s ∈ Ico 0 h, ‖U s * Ω s - Ω 0‖ ≤ (B ^ 2 * ‖(1 : A)‖ * exp (B * h) + L) * h := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have e : U s * Ω s - Ω 0 = (U s - 1) * Ω s + (Ω s - Ω 0) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_transport_sub_one_le hB hΩB hU0 hU s hs'
    have h2 := hΩL s hs'
    have hsh : s ≤ h := hs'.2
    have hs0 : 0 ≤ s := hs'.1
    have h3 : ‖(U s - 1) * Ω s‖ ≤ B * ‖(1 : A)‖ * exp (B * h) * s * B :=
      (norm_mul_le _ _).trans (mul_le_mul h1 (hΩB s hs') (norm_nonneg _) (by positivity))
    have hE : 0 ≤ B ^ 2 * ‖(1 : A)‖ * exp (B * h) := by positivity
    calc ‖(U s - 1) * Ω s‖ + ‖Ω s - Ω 0‖
        ≤ B * ‖(1 : A)‖ * exp (B * h) * s * B + L * s := add_le_add h3 h2
      _ = (B ^ 2 * ‖(1 : A)‖ * exp (B * h) + L) * s := by ring
      _ ≤ (B ^ 2 * ‖(1 : A)‖ * exp (B * h) + L) * h :=
          mul_le_mul_of_nonneg_left hsh (by positivity)
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := fun s => U s * Ω s - Ω 0)
    (fun s _ => (hg s).hasDerivWithinAt) hbound h ⟨hh, le_rfl⟩
  have hg0 : g 0 = 0 := by simp [g, hU0]
  rw [hg0, sub_zero, sub_zero] at this
  calc ‖g h‖ ≤ (B ^ 2 * ‖(1 : A)‖ * exp (B * h) + L) * h * h := this
    _ = (B ^ 2 * ‖(1 : A)‖ * exp (B * h) + L) * h ^ 2 := by ring

end RenewalGeometry.LinearTransport
