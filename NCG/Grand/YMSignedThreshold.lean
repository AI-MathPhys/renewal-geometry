/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Common-time signed compression and Stieltjes return
  packet (`thm:YM-signed-threshold-packet`,
  Gran-Tensor manuscript)

* `ym_signed_threshold_packet`: for a source-range
  isometry `J` (`J*J = 1`, `P = JJ*`) and self-adjoint
  transfers `T_X, T_Y` with compressed moments
  `M₁ = J*T_YJ`, `M₂ = J*T_Y²J`, `C = M₁ - T_X`,
  `L = (1-P)T_YJ`:
  (i) the boxed YM.1 variance identification
      `𝕍 = L*L = M₂ - M₁²`;
  (ii) the boxed YM.2 exact split
      `T_YJ - JT_X = L + JC` with the boxed Pythagoras
      `(T_YJ - JT_X)*(T_YJ - JT_X) = 𝕍 + C²`
      (the leakage `L` and the compression mismatch `JC`
      are exactly orthogonal, `J*L = 0`).

The boxed YM.3 threshold transfer
(`qI - M₁ - 𝕍/(q-d) ⪰ 0 ⟹ T_Y ⪯ qI`), the YM.4–YM.5
third-moment Stieltjes sandwich for the return
self-energy, and the boxed YM.6 Haynsworth inertia count
(`In(qI-T_Y) = In(qI-D) + In(qI-M₁-B(qI-D)⁻¹B*)`) are the
manuscript's block-spectral layer on top of these exact
identities (cf. `thm:GT-signed-Haynsworth`); the signedness
warning for `C` is its reading of the Pythagoras.
-/

open Matrix

set_option linter.unusedSimpArgs false

namespace NCG

/-- `thm:YM-signed-threshold-packet` (the exact YM.1–YM.2
identities). -/
theorem ym_signed_threshold_packet {H K : Type}
    [Fintype H] [Fintype K] [DecidableEq H]
    [DecidableEq K]
    (J : Matrix H K ℂ) (TX : Matrix K K ℂ)
    (TY : Matrix H H ℂ)
    (hJ : Jᴴ * J = 1) (hTX : TXᴴ = TX)
    (hTY : TYᴴ = TY) :
    -- (i) the boxed YM.1: 𝕍 = L*L = M₂ - M₁²
    ((((1 - J * Jᴴ) * (TY * J))ᴴ
        * ((1 - J * Jᴴ) * (TY * J)))
      = Jᴴ * (TY * TY * J)
        - (Jᴴ * (TY * J)) * (Jᴴ * (TY * J)))
    -- (ii) the boxed YM.2 split and Pythagoras
    ∧ (TY * J - J * TX
        = (1 - J * Jᴴ) * (TY * J)
          + J * (Jᴴ * (TY * J) - TX))
    ∧ ((TY * J - J * TX)ᴴ * (TY * J - J * TX)
        = (((1 - J * Jᴴ) * (TY * J))ᴴ
            * ((1 - J * Jᴴ) * (TY * J)))
          + (Jᴴ * (TY * J) - TX)
            * (Jᴴ * (TY * J) - TX)) := by
  set P := J * Jᴴ with hP
  set L := (1 - P) * (TY * J) with hL
  set C := Jᴴ * (TY * J) - TX with hC
  have hPP : P * P = P := by
    rw [hP]
    calc J * Jᴴ * (J * Jᴴ)
        = J * ((Jᴴ * J) * Jᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = J * Jᴴ := by rw [hJ, Matrix.one_mul]
  have hPH : Pᴴ = P := by
    rw [hP, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hJL : Jᴴ * L = 0 := by
    rw [hL, hP]
    calc Jᴴ * ((1 - J * Jᴴ) * (TY * J))
        = (Jᴴ - (Jᴴ * J) * Jᴴ) * (TY * J) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_one, Matrix.one_mul,
            Matrix.mul_assoc]
      _ = 0 := by
          rw [hJ, Matrix.one_mul, sub_self,
            Matrix.zero_mul]
  have h1P : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  have h1PH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPH]
  -- YM.1
  have hVar : Lᴴ * L
      = Jᴴ * (TY * TY * J)
        - (Jᴴ * (TY * J)) * (Jᴴ * (TY * J)) := by
    rw [hL, Matrix.conjTranspose_mul, h1PH]
    have h1 : (TY * J)ᴴ * ((1 - P)
        * ((1 - P) * (TY * J)))
        = (TY * J)ᴴ * ((1 - P) * (TY * J)) := by
      rw [← Matrix.mul_assoc (1 - P) (1 - P), h1P]
    rw [Matrix.mul_assoc, h1]
    rw [Matrix.conjTranspose_mul, hTY]
    rw [hP]
    simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  refine ⟨hVar, ?_, ?_⟩
  · rw [hL, hC, hP]
    simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  · have hsplit : TY * J - J * TX = L + J * C := by
      rw [hL, hC, hP]
      simp only [Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_assoc]
      abel
    rw [hsplit]
    have hCH : Cᴴ = C := by
      rw [hC, Matrix.conjTranspose_sub, hTX,
        Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul, hTY,
        Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    have hLJ : Lᴴ * (J * C) = 0 := by
      have h := congrArg conjTranspose hJL
      rw [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_zero] at h
      calc Lᴴ * (J * C) = (Lᴴ * J) * C := by
            rw [Matrix.mul_assoc]
        _ = 0 := by rw [h, Matrix.zero_mul]
    have hJLC : (J * C)ᴴ * L = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
        hJL, Matrix.mul_zero]
    rw [Matrix.conjTranspose_add, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_add, hLJ, hJLC]
    have hJC : (J * C)ᴴ * (J * C) = C * C := by
      calc (J * C)ᴴ * (J * C)
          = Cᴴ * ((Jᴴ * J) * C) := by
            rw [Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = C * C := by
            rw [hJ, Matrix.one_mul, hCH]
    rw [hJC]
    abel

end NCG
