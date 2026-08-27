/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CriticalLineReflection

/-!
# Critical-line/circle duality for a unitarily diagonalized normal matrix

This transports the diagonal spectral-determinant theorem through the unitary
diagonalization supplied by finite-dimensional normality.
-/

open Matrix

namespace NCG
namespace NormalCriticalLineCircleExact

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unitary conjugation transports both the spectral determinant and the
scalar Gram condition. -/
theorem unitary_diagonal_transport
    (A U : Matrix n n ℂ) (lam : n → ℂ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1)
    (hA : A = U * Matrix.diagonal lam * Uᴴ) :
    (∀ z : ℂ,
      Matrix.det (1 - z • A) =
        Matrix.det (1 - z • Matrix.diagonal lam)) ∧
    (∀ c : ℝ, Aᴴ * A = (c : ℂ) • 1 ↔
      (Matrix.diagonal lam)ᴴ * Matrix.diagonal lam = (c : ℂ) • 1) := by
  have hdetU : Matrix.det U * Matrix.det Uᴴ = 1 := by
    rw [← Matrix.det_mul, hU₂, Matrix.det_one]
  constructor
  · intro z
    have hconj : 1 - z • A = U * (1 - z • Matrix.diagonal lam) * Uᴴ := by
      rw [hA]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
        hU₂]
    rw [hconj, Matrix.det_mul, Matrix.det_mul]
    calc
      Matrix.det U * Matrix.det (1 - z • Matrix.diagonal lam) * Matrix.det Uᴴ =
          Matrix.det (1 - z • Matrix.diagonal lam) *
            (Matrix.det U * Matrix.det Uᴴ) := by ring
      _ = _ := by rw [hdetU, mul_one]
  · intro c
    have hgram : Aᴴ * A =
        U * ((Matrix.diagonal lam)ᴴ * Matrix.diagonal lam) * Uᴴ := by
      rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU₁, Matrix.one_mul]
    let Dg := (Matrix.diagonal lam)ᴴ * Matrix.diagonal lam
    have hleft : Uᴴ * (U * Dg * Uᴴ) * U = Dg := by
      calc
        Uᴴ * (U * Dg * Uᴴ) * U = (Uᴴ * U) * Dg * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
        _ = Dg := by rw [hU₁]; simp
    have hright : Uᴴ * ((c : ℂ) • (1 : Matrix n n ℂ)) * U =
        (c : ℂ) • 1 := by
      calc
        Uᴴ * ((c : ℂ) • (1 : Matrix n n ℂ)) * U =
            (c : ℂ) • (Uᴴ * U) := by simp [Matrix.mul_assoc]
        _ = (c : ℂ) • 1 := by rw [hU₁]
    constructor
    · intro hscalar
      have h := congrArg (fun X : Matrix n n ℂ => Uᴴ * X * U) hscalar
      rw [hgram] at h
      change Uᴴ * (U * Dg * Uᴴ) * U = Uᴴ * ((c : ℂ) • 1) * U at h
      rw [hleft, hright] at h
      exact h
    · intro hscalar
      rw [hgram, hscalar]
      simp [Matrix.mul_assoc, hU₂]
/-- The full manuscript packet for an invertible normal matrix, presented by
its unitary eigenbasis: reflected zeros preserve multiplicity, and the
critical-line, spectral-circle, and scalar-Gram conditions are equivalent. -/
theorem critical_line_circle_for_normal_matrix
    (A U : Matrix n n ℂ) (lam : n → ℂ) (σ : n ≃ n)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1)
    (hA : A = U * Matrix.diagonal lam * Uᴴ)
    (hlam : ∀ j, lam j ≠ 0)
    (l : ℝ) (hl : 0 < l) (c : ℝ) (hc : 0 < c)
    (hσ : ∀ j, lam (σ j) = (c : ℂ) / star (lam j)) :
    (∀ s : ℂ,
      Matrix.det (1 - Complex.exp (-(l : ℂ) * s) • A) = 0 ↔
      Matrix.det (1 - Complex.exp
        (-(l : ℂ) * criticalReflection l c s) • A) = 0) ∧
    (((∀ s : ℂ, Matrix.det (1 - Complex.exp (-(l : ℂ) * s) • A) = 0 →
        l * s.re = Real.log (Real.sqrt c)) ↔
      ∀ j, ‖lam j‖ = Real.sqrt c) ∧
      ((∀ j, ‖lam j‖ = Real.sqrt c) ↔ Aᴴ * A = (c : ℂ) • 1)) := by
  obtain ⟨hdet, hgram⟩ := unitary_diagonal_transport A U lam hU₁ hU₂ hA
  have hdiag := critical_line_circle lam hlam l hl c hc
  constructor
  · intro s
    rw [hdet, hdet]
    exact criticalLineZeroReflection lam σ l c hl.ne' hc hσ s
  · constructor
    · constructor
      · intro hline
        exact hdiag.1.mp (fun s hs => hline s ((hdet _).symm ▸ hs))
      · intro hcircle s hs
        exact hdiag.1.mpr hcircle s ((hdet _) ▸ hs)
    · exact hdiag.2.trans (hgram c).symm

end NormalCriticalLineCircleExact
end NCG
