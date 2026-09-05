/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Predictable-mean/martingale-noise Pythagoras and the
  noise-shorted Ward identity
  (`thm:renewal-mean-noise-short` and
  `thm:renewal-noise-shorted-Ward`, Gran-Tensor manuscript)

* `renewal_mean_noise_short`: with a current source `S`, a
  predictable mean `M`, and a fresh noise source `N`
  satisfying `SᴴN = 0`, `MᴴN = 0`, and `Y = M + N`:
  (i) the boxed router Pythagoras
      `(Y-SW)ᴴ(Y-SW) = (M-SW)ᴴ(M-SW) + Q`, `Q = NᴴN`;
  (ii) the complete `(S,Y,N)` Gram entries
      (`SᴴY = SᴴM`, `YᴴY = MᴴM + Q`, `NᴴY = Q`);
  (iii) the Anderson–Trapp short away from the noise source
      is exactly the current/mean Gram:
      `YᴴY - (NᴴY)ᴴ(NᴴN)⁻¹(NᴴY) = MᴴM` and
      `SᴴY - (NᴴS)ᴴ(NᴴN)⁻¹(NᴴY) = SᴴM`.

* `renewal_noise_shorted_ward`: the raw Ward form splits as
  `𝔚ʳᵃʷ(W) = 𝔚ᵐᵉᵃⁿ(W) + NᴴN`, and on the dense scaling
  `NᴴN = τ·G_noise + E` the raw form is exactly
  `τ·G_noise + (𝔚ᵐᵉᵃⁿ(W) + E)` — the Brownian order-`τ`
  covariance and the deterministic mean residual are distinct
  positive coordinates.
-/

open Matrix

namespace NCG

/-- `thm:renewal-mean-noise-short`. -/
theorem renewal_mean_noise_short {H eS eF : Type*}
    [Fintype H] [Fintype eS] [Fintype eF] [DecidableEq eF]
    (S : Matrix H eS ℂ) (M N : Matrix H eF ℂ)
    (hSN : Sᴴ * N = 0) (hMN : Mᴴ * N = 0)
    (W : Matrix eS eF ℂ) [Invertible (Nᴴ * N)] :
    -- (i) the router Pythagoras
    ((M + N) - S * W)ᴴ * ((M + N) - S * W)
      = (M - S * W)ᴴ * (M - S * W) + Nᴴ * N
    -- (ii) the complete Gram entries
    ∧ Sᴴ * (M + N) = Sᴴ * M
    ∧ (M + N)ᴴ * (M + N) = Mᴴ * M + Nᴴ * N
    ∧ Nᴴ * (M + N) = Nᴴ * N
    -- (iii) the Anderson–Trapp short away from the noise
    ∧ (M + N)ᴴ * (M + N)
        - (Nᴴ * (M + N))ᴴ * (Nᴴ * N)⁻¹ * (Nᴴ * (M + N))
      = Mᴴ * M
    ∧ Sᴴ * (M + N)
        - (Nᴴ * S)ᴴ * (Nᴴ * N)⁻¹ * (Nᴴ * (M + N))
      = Sᴴ * M := by
  have hNS : Nᴴ * S = 0 := by
    have h := congrArg conjTranspose hSN
    rwa [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h
  have hNM : Nᴴ * M = 0 := by
    have h := congrArg conjTranspose hMN
    rwa [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h
  have hSY : Sᴴ * (M + N) = Sᴴ * M := by
    rw [Matrix.mul_add, hSN, add_zero]
  have hYY : (M + N)ᴴ * (M + N) = Mᴴ * M + Nᴴ * N := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_add, hMN, hNM,
      add_zero, zero_add]
  have hNY : Nᴴ * (M + N) = Nᴴ * N := by
    rw [Matrix.mul_add, hNM, zero_add]
  refine ⟨?_, hSY, hYY, hNY, ?_, ?_⟩
  · -- expand both sides and cancel the cross terms
    have hNSW : Nᴴ * (S * W) = 0 := by
      rw [← Matrix.mul_assoc, hNS, Matrix.zero_mul]
    have hSNW : (S * W)ᴴ * N = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hSN,
        Matrix.mul_zero]
    simp only [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_add, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      hMN, hNM, hNSW, hSNW, add_zero, zero_add,
      sub_zero]
    abel
  · rw [hYY, hNY]
    have h : (Nᴴ * N)ᴴ * (Nᴴ * N)⁻¹ * (Nᴴ * N)
        = Nᴴ * N := by
      rw [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
        Matrix.mul_one]
    rw [h]
    abel
  · rw [hSY, hNS, hNY]
    rw [Matrix.conjTranspose_zero, Matrix.zero_mul,
      Matrix.zero_mul, sub_zero]

/-- `thm:renewal-noise-shorted-Ward`. -/
theorem renewal_noise_shorted_ward {H eS eF : Type*}
    [Fintype H] [Fintype eS]
    (S : Matrix H eS ℂ) (M N : Matrix H eF ℂ)
    (hSN : Sᴴ * N = 0) (hMN : Mᴴ * N = 0)
    (W : Matrix eS eF ℂ) (τ : ℝ)
    (Gn E : Matrix eF eF ℂ)
    (hτ : Nᴴ * N = (τ : ℂ) • Gn + E) :
    -- the raw Ward form splits mean + noise
    ((M + N) - S * W)ᴴ * ((M + N) - S * W)
      = (M - S * W)ᴴ * (M - S * W) + Nᴴ * N
    -- dense scaling: raw = τ·G_noise + (mean + residual)
    ∧ ((M + N) - S * W)ᴴ * ((M + N) - S * W)
      = (τ : ℂ) • Gn
        + ((M - S * W)ᴴ * (M - S * W) + E) := by
  have hNS : Nᴴ * S = 0 := by
    have h := congrArg conjTranspose hSN
    rwa [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h
  have hNM : Nᴴ * M = 0 := by
    have h := congrArg conjTranspose hMN
    rwa [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h
  have hmain : ((M + N) - S * W)ᴴ * ((M + N) - S * W)
      = (M - S * W)ᴴ * (M - S * W) + Nᴴ * N := by
    have hNSW : Nᴴ * (S * W) = 0 := by
      rw [← Matrix.mul_assoc, hNS, Matrix.zero_mul]
    have hSNW : (S * W)ᴴ * N = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hSN,
        Matrix.mul_zero]
    simp only [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_add, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      hMN, hNM, hNSW, hSNW, add_zero, zero_add,
      sub_zero]
    abel
  refine ⟨hmain, ?_⟩
  rw [hmain, hτ]
  abel

end NCG
