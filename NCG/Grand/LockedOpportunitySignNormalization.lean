/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LockedSignReversal
import NCG.Grand.LockedOpportunityNaimarkFrame

/-!
# Exact physical and environment sign normalization

This module completes `thm:SMST-exact-locked-sign`.  It proves the literal
two-sided inverse-square-root normalization on the physical space, the
twenty-four-dimensional whitened-environment calculation, and the sharp
likelihood-metric spectral window.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- Two-sided normalization of the scalar physical likelihood metric removes
the acceptance coefficient exactly. -/
theorem physicalSign_inverseSqrt_normalization {n : Type*} [Fintype n]
    [DecidableEq n] (θ : ℝ) (hθ : 0 < θ) (Z : Matrix n n ℂ) :
    (((Real.sqrt θ : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))
        * ((θ : ℂ) • Z)
        * (((Real.sqrt θ : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ)) = Z := by
  have hs : Real.sqrt θ ≠ 0 := Real.sqrt_ne_zero'.mpr hθ
  have hsC : (((Real.sqrt θ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hs
  have hs2 : (((Real.sqrt θ : ℝ) : ℂ)) ^ 2 = (θ : ℂ) := by
    exact_mod_cast Real.sq_sqrt hθ.le
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_smul]
  rw [← hs2]
  field_simp [hsC]
  exact one_smul ℂ Z

/-- Summing the two coordinate-sign effects gives the accepted environment
metric, while taking their difference gives the whitened sign observable. -/
theorem environmentSign_effect_sum_difference {e : Type*} [Fintype e]
    [DecidableEq e] (θ : ℂ) (R Pp Pm : Matrix e e ℂ)
    (hsum : Pp + Pm = 1) :
    (θ • (R * Pp * R) + θ • (R * Pm * R) = θ • (R * R))
      ∧ (θ • (R * Pp * R) - θ • (R * Pm * R)
        = θ • (R * (Pp - Pm) * R)) := by
  constructor
  · rw [← smul_add]
    congr 1
    rw [← Matrix.add_mul, ← Matrix.mul_add, hsum, Matrix.mul_one]
  · rw [← smul_sub]
    congr 1
    rw [Matrix.mul_sub, Matrix.sub_mul]

/-- The nonorthogonal minimal-environment frame changes the accepted metric
but not the normalized sign: inverse whitening cancels on both sides. -/
theorem environmentSign_inverseSqrt_normalization {e : Type*} [Fintype e]
    [DecidableEq e] (θ : ℝ) (hθ : 0 < θ)
    (R T Pp Pm : Matrix e e ℂ) (hTR : T * R = 1) (hRT : R * T = 1) :
    let Fp := (θ : ℂ) • (R * Pp * R)
    let Fm := (θ : ℂ) • (R * Pm * R)
    let hInvSqrt := (((Real.sqrt θ : ℝ) : ℂ)⁻¹) • T
    hInvSqrt * (Fp - Fm) * hInvSqrt = Pp - Pm := by
  dsimp
  have hs : Real.sqrt θ ≠ 0 := Real.sqrt_ne_zero'.mpr hθ
  have hsC : (((Real.sqrt θ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hs
  have hs2 : (((Real.sqrt θ : ℝ) : ℂ)) ^ 2 = (θ : ℂ) := by
    exact_mod_cast Real.sq_sqrt hθ.le
  rw [← smul_sub]
  have hdiff : R * Pp * R - R * Pm * R = R * (Pp - Pm) * R := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hdiff]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_assoc]
  rw [hRT, Matrix.mul_one, ← Matrix.mul_assoc, hTR, Matrix.one_mul]
  have hreal : ∀ X : Matrix e e ℂ, θ • X = (θ : ℂ) • X := by
    intro X
    ext i j
    simp [Matrix.smul_apply]
  rw [hreal]
  simp only [smul_smul]
  have hc : ((((Real.sqrt θ : ℝ) : ℂ)⁻¹) * (θ : ℂ)
      * (((Real.sqrt θ : ℝ) : ℂ)⁻¹)) = 1 := by
    rw [← hs2]
    field_simp [hsC]
  rw [← mul_assoc, hc, one_smul]

/-- Spectral two-sided bound for the environment likelihood metric.  Written
as positive-semidefinite differences, this is exactly
`α I ≼ h_env ≼ I`, with `α = θ/(12-11θ)`. -/
theorem environmentLikelihood_spectralWindow {e : Type*} [Fintype e]
    [DecidableEq e] (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (P : Matrix e e ℂ) (hP : P.PosSemidef)
    (hPc : ((1 : Matrix e e ℂ) - P).PosSemidef) :
    let α : ℝ := θ / (12 - 11 * θ)
    let hEnv : Matrix e e ℂ := (1 - P) + (α : ℂ) • P
    (hEnv - (α : ℂ) • 1).PosSemidef
      ∧ ((1 : Matrix e e ℂ) - hEnv).PosSemidef := by
  dsimp
  have hden : 0 < 12 - 11 * θ := by linarith
  have hα0 : 0 ≤ θ / (12 - 11 * θ) := (div_pos hθ0 hden).le
  have hα1 : θ / (12 - 11 * θ) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  constructor
  · have hs : (0 : ℂ) ≤ ((1 - θ / (12 - 11 * θ) : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr (by linarith)
    have h := hPc.smul hs
    convert h using 1 <;> module
  · have hs : (0 : ℂ) ≤ ((1 - θ / (12 - 11 * θ) : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr (by linarith)
    have h := hP.smul hs
    convert h using 1 <;> module

end NCG
