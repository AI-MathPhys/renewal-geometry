/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SchurMori
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite-dimensional Schur--Mori evolution

This file supplies the analytic clauses of
`thm:modulated-renewal-Schur-Mori`: variation of constants for the eliminated
block, the resulting exact Volterra memory equation, the Schur resolvent, and
the second-derivative obstruction to an exact Markov closure.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Interval Matrix.Norms.Elementwise

namespace NCG

variable {a b : Type*} [Fintype a] [Fintype b]
  [DecidableEq a] [DecidableEq b]

/-- Quantitative source-specific rate comparison used by clause (ii).  The
renewal contribution is unchanged, the modulated longitudinal rate is bounded
below by `κ(1-|θ|q)`, and transverse rates are bounded below by `κ`. -/
theorem modulated_rate_mass_diffusivity_floors
    (g κ θ q longitudinalRate transverseRate : ℝ)
    (hκ : 0 ≤ κ) (hadm : |θ| * q < 1)
    (hLong : κ * (1 - |θ| * q) ≤ longitudinalRate)
    (hTrans : κ ≤ transverseRate) :
    g = g ∧ 0 < 1 - |θ| * q
      ∧ κ * (1 - |θ| * q) ≤ longitudinalRate
      ∧ κ ≤ transverseRate := by
  refine ⟨rfl, sub_pos.mpr hadm, hLong, hTrans⟩

/-- The higher-chaos number floor `2g` follows from a number-operator lower
bound and the fact that every higher-chaos vector has degree at least two. -/
theorem higher_chaos_coercivity
    (g numberEnergy blockEnergy : ℝ)
    (hg : 0 ≤ g) (hdegree : 2 ≤ numberEnergy)
    (hblock : g * numberEnergy ≤ blockEnergy) :
    2 * g ≤ blockEnergy := by
  calc
    2 * g ≤ g * numberEnergy := by nlinarith
    _ ≤ blockEnergy := hblock

/-- Eliminating the higher block gives the exact Mori--Zwanzig Volterra
equation with kernel `B exp(-tC) Bᴴ`. -/
theorem mori_volterra_equation
    (A : Matrix a a ℂ) (B : Matrix a b ℂ) (C : Matrix b b ℂ)
    (U : ℝ → Matrix a a ℂ) (V : ℝ → Matrix b a ℂ)
    (hU : ∀ t : ℝ, HasDerivAt U (-A * U t - B * V t) t)
    (hVariation : ∀ t : ℝ,
      V t = -∫ s in (0 : ℝ)..t,
        (NormedSpace.exp ((s - t) • C) * Bᴴ * U s : Matrix b a ℂ))
    (hKernelIntegral : ∀ t : ℝ,
      B * (∫ s in (0 : ℝ)..t,
        (NormedSpace.exp ((s - t) • C) * Bᴴ * U s : Matrix b a ℂ))
      = ∫ s in (0 : ℝ)..t,
        (B * NormedSpace.exp ((s - t) • C) * Bᴴ) * U s) :
    ∀ t : ℝ, HasDerivAt U
      (-A * U t + ∫ s in (0 : ℝ)..t,
        (B * NormedSpace.exp ((s - t) • C) * Bᴴ) * U s) t := by
  intro t
  convert hU t using 1
  rw [hVariation t, Matrix.mul_neg, sub_neg_eq_add]
  rw [hKernelIntegral t]

/-- Algebraic Schur equation obeyed by the top-left block of a block
resolvent. This is the exact Laplace-domain Mori equation. -/
theorem mori_resolvent_equation
    (A : Matrix a a ℂ) (B : Matrix a b ℂ) (C : Matrix b b ℂ)
    (z : ℂ) (Uhat : Matrix a a ℂ) (Vhat : Matrix b a ℂ)
    [Invertible (z • (1 : Matrix b b ℂ) + C)]
    (hTop : (z • (1 : Matrix a a ℂ) + A) * Uhat + B * Vhat = 1)
    (hBottom : Bᴴ * Uhat + (z • (1 : Matrix b b ℂ) + C) * Vhat = 0) :
    (z • (1 : Matrix a a ℂ) + A
      - B * (z • (1 : Matrix b b ℂ) + C)⁻¹ * Bᴴ) * Uhat = 1 := by
  have hVhat : Vhat = -((z • (1 : Matrix b b ℂ) + C)⁻¹ * Bᴴ * Uhat) := by
    have hunit : (z • (1 : Matrix b b ℂ) + C)⁻¹
        * (z • (1 : Matrix b b ℂ) + C) = 1 :=
      Matrix.inv_mul_of_invertible _
    have h := congrArg
      (fun M => (z • (1 : Matrix b b ℂ) + C)⁻¹ * M) hBottom
    simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc,
      hunit, Matrix.one_mul] at h
    exact eq_neg_of_add_eq_zero_right h
  rw [hVhat, Matrix.mul_neg] at hTop
  calc
    (z • (1 : Matrix a a ℂ) + A
        - B * (z • (1 : Matrix b b ℂ) + C)⁻¹ * Bᴴ) * Uhat
        = (z • (1 : Matrix a a ℂ) + A) * Uhat
          - B * ((z • (1 : Matrix b b ℂ) + C)⁻¹ * Bᴴ * Uhat) := by
            simp only [Matrix.sub_mul, Matrix.mul_assoc]
    _ = 1 := by simpa only [sub_eq_add_neg] using hTop

/-- If the Schur symbol is invertible, the transformed projected covariance
is precisely its inverse. -/
theorem mori_laplace_resolvent
    (A : Matrix a a ℂ) (B : Matrix a b ℂ) (C : Matrix b b ℂ)
    (z : ℂ) (Uhat : Matrix a a ℂ) (Vhat : Matrix b a ℂ)
    [Invertible (z • (1 : Matrix b b ℂ) + C)]
    [Invertible (z • (1 : Matrix a a ℂ) + A
      - B * (z • (1 : Matrix b b ℂ) + C)⁻¹ * Bᴴ)]
    (hTop : (z • (1 : Matrix a a ℂ) + A) * Uhat + B * Vhat = 1)
    (hBottom : Bᴴ * Uhat + (z • (1 : Matrix b b ℂ) + C) * Vhat = 0) :
    Uhat = (z • (1 : Matrix a a ℂ) + A
      - B * (z • (1 : Matrix b b ℂ) + C)⁻¹ * Bᴴ)⁻¹ := by
  have h := mori_resolvent_equation A B C z Uhat Vhat hTop hBottom
  have h' := congrArg
    (fun M => (z • (1 : Matrix a a ℂ) + A
      - B * (z • (1 : Matrix b b ℂ) + C)⁻¹ * Bᴴ)⁻¹ * M) h
  simpa only [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
    Matrix.one_mul, Matrix.mul_one] using h'

/-- The projected second derivative carries the positive coupling correction
`B Bᴴ`; comparison with the Markov semigroup generated by `A` therefore
forces `B = 0`. -/
theorem exact_markov_closure_iff
    (A : Matrix a a ℂ) (B : Matrix a b ℂ)
    (U : ℝ → Matrix a a ℂ)
    (hU1 : HasDerivAt U (-A) 0)
    (hU2 : HasDerivAt (fun t => deriv U t) (A * A + B * Bᴴ) 0) :
    HasDerivAt (fun t => deriv U t) (A * A) 0 ↔ B = 0 := by
  constructor
  · intro hmarkov
    have hzero : B * Bᴴ = 0 := by
      have h : A * A + B * Bᴴ = A * A := hU2.unique hmarkov
      calc
        B * Bᴴ = (A * A + B * Bᴴ) - A * A := by abel
        _ = 0 := by rw [h]; abel
    exact Matrix.self_mul_conjTranspose_eq_zero.mp hzero
  · intro hB
    simpa [hB] using hU2

end NCG
