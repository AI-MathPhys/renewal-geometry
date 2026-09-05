/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SingularPolarData
import NCG.Grand.SquarePartialIsometryUnitaryExtension
import NCG.Grand.PositiveSquareContraction
import NCG.Grand.NaimarkPhaseSharpness

/-!
# Frobenius approximation by a unitary polar factor

A square contraction with defect `I - AAᴴ` admits a unitary polar factor
whose squared Hilbert--Schmidt distance is at most the trace of that defect.
The proof treats singular matrices by extending the polar partial isometry to
a unitary on the whole square space.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace NCG
namespace SquarePolarUnitaryApproximation

variable {d : ℕ}

/-- A square matrix with `AAᴴ ≤ I` is within squared Frobenius distance
`Tr(I-AAᴴ)` of a unitary matrix. -/
theorem exists_unitary_frobenius_close
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hcontract : (1 - A * Aᴴ).PosSemidef) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      hsFrobSq (A - U) ≤ (1 - A * Aᴴ).trace.re := by
  rcases exists_singular_polar_data Aᴴ with
    ⟨V, P, Pd, hP, hAP, hP2, hVp, hPPd, hPdP, _hsupp⟩
  let p : Matrix (Fin d) (Fin d) ℂ := Vᴴ * V
  have hpH : pᴴ = p := by
    simp only [p, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hp2 : p * p = p := by
    calc
      p * p = Vᴴ * (V * p) := by simp only [p, Matrix.mul_assoc]
      _ = Vᴴ * V := by rw [hVp]
      _ = p := rfl
  have hP2' : P * P = A * Aᴴ := by
    simpa using hP2
  have hPpP : P * p * P = P * P := by
    calc
      P * p * P = (V * P)ᴴ * (V * P) := by
        rw [Matrix.conjTranspose_mul, hP.1.eq]
        simp only [p, Matrix.mul_assoc]
      _ = (Aᴴ)ᴴ * Aᴴ := by rw [← hAP]
      _ = P * P := by simpa using hP2'.symm
  let Y : Matrix (Fin d) (Fin d) ℂ := (1 - p) * P
  have hcomp : (1 - p) * (1 - p) = 1 - p := by
    noncomm_ring [hp2]
  have hY2 : Yᴴ * Y = 0 := by
    calc
      Yᴴ * Y = P * (1 - p) * (1 - p) * P := by
        simp only [Y, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
          hP.1.eq, hpH, Matrix.mul_assoc]
      _ = P * ((1 - p) * (1 - p)) * P := by
        simp only [Matrix.mul_assoc]
      _ = P * (1 - p) * P := by rw [hcomp]
      _ = P * P - P * p * P := by noncomm_ring
      _ = 0 := by rw [hPpP, sub_self]
  have hY : Y = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hY2
  have hpP : p * P = P := by
    dsimp only [Y] at hY
    rw [Matrix.sub_mul, Matrix.one_mul] at hY
    exact (sub_eq_zero.mp hY).symm
  rcases SquarePartialIsometryUnitaryExtension.exists_unitary_extension
      V p hp2 rfl hVp with ⟨W, hWtW, hWWt, hWp⟩
  have hAWP : Aᴴ = W * P := by
    calc
      Aᴴ = V * P := hAP
      _ = (W * p) * P := by rw [hWp]
      _ = W * P := by rw [Matrix.mul_assoc, hpP]
  let U : Matrix (Fin d) (Fin d) ℂ := Wᴴ
  have hUtU : Uᴴ * U = 1 := by simpa [U] using hWWt
  have hUUt : U * Uᴴ = 1 := by simpa [U] using hWtW
  have hA : A = P * U := by
    have ht := congrArg Matrix.conjTranspose hAWP
    simpa [U, hP.1.eq] using ht
  have hIP2 : (1 - P * P).PosSemidef := by
    rw [hP2']
    exact hcontract
  have hdefP : (P - P * P).PosSemidef :=
    (PositiveSquareContraction.positive_and_defect P hP hIP2).2
  have hdefTrace : 0 ≤ (P - P * P).trace.re :=
    (Complex.nonneg_iff.mp hdefP.trace_nonneg).1
  have htraceBound :
      ((P - 1) * (P - 1)).trace.re ≤ (1 - P * P).trace.re := by
    have hmat : 1 - P * P =
        (P - 1) * (P - 1) + (P - P * P) + (P - P * P) := by
      noncomm_ring
    rw [hmat, Matrix.trace_add, Matrix.trace_add]
    simp only [Complex.add_re]
    linarith
  have hdiff : A - U = (P - 1) * U := by
    rw [hA]
    noncomm_ring
  refine ⟨U, hUtU, hUUt, ?_⟩
  rw [hdiff]
  calc
    hsFrobSq ((P - 1) * U) ≤ hsFrobSq (P - 1) :=
      hsFrobSq_mul_isometry_le (P - 1) U hUtU
    _ = ((P - 1) * (P - 1)).trace.re := by
      rw [hsFrobSq_eq_re_trace]
      congr 2
      rw [Matrix.conjTranspose_sub, hP.1.eq,
        Matrix.conjTranspose_one]
    _ ≤ (1 - P * P).trace.re := htraceBound
    _ = (1 - A * Aᴴ).trace.re := by rw [hP2']

end SquarePolarUnitaryApproximation
end NCG
