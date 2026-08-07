/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Marked bi-Hankel reconstruction of the finite Dirac operator
  (`thm:SM-marked-Dirac`, Gran-Tensor manuscript)

* `sm_marked_dirac`: for a full-row-rank Gram factor `R`
  (rendered as `Invertible (RRᴴ)`) with explicit pseudo-inverse
  `R† = Rᴴ(RRᴴ)⁻¹`, the boxed reconstruction
  `D_R = (R†)ᴴ 𝕹 R†` is the unique packet operator with
  `𝕹 = Rᴴ D_R R` whenever `𝕹` factors through the packet at
  all; and different Gram factors `R' = UR` (packet unitary
  `U`) conjugate the reconstruction: `D_{UR} = U D_R Uᴴ`.

Rendering disclosed: the flatness of the ordinary Hankel Gram
and the vanishing null test `Δ_null^D = 0` are the manuscript's
hypotheses ensuring `𝕹` factors through the packet — they enter
here as the factorization hypothesis `𝕹 = RᴴDR`; the
self-adjointness/grading/reality/…​ tests and the physical
export `Y_u, …, M_R` are the manuscript's bookkeeping over the
one reconstructed operator.
-/

open Matrix

namespace NCG

/-- `thm:SM-marked-Dirac`: the boxed pseudo-inverse
reconstruction is exact, unique, and Gram-factor covariant. -/
theorem sm_marked_dirac {r w : Type*} [Fintype r] [Fintype w]
    [DecidableEq r]
    (R : Matrix r w ℂ) [Invertible (R * Rᴴ)]
    (N : Matrix w w ℂ) :
    (∀ D : Matrix r r ℂ, N = Rᴴ * D * R →
      D = (Rᴴ * (R * Rᴴ)⁻¹)ᴴ * N * (Rᴴ * (R * Rᴴ)⁻¹))
    ∧ (∀ D : Matrix r r ℂ, N = Rᴴ * D * R →
        N = Rᴴ * ((Rᴴ * (R * Rᴴ)⁻¹)ᴴ * N
          * (Rᴴ * (R * Rᴴ)⁻¹)) * R)
    ∧ (∀ U : Matrix r r ℂ, Uᴴ * U = 1 → U * Uᴴ = 1 →
        ((U * R)ᴴ * ((U * R) * (U * R)ᴴ)⁻¹)ᴴ * N
            * ((U * R)ᴴ * ((U * R) * (U * R)ᴴ)⁻¹)
          = U * ((Rᴴ * (R * Rᴴ)⁻¹)ᴴ * N
              * (Rᴴ * (R * Rᴴ)⁻¹)) * Uᴴ) := by
  have hLh : (R * Rᴴ)ᴴ = R * Rᴴ := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hinvh : ((R * Rᴴ)⁻¹)ᴴ = (R * Rᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hLh]
  have hdagh : (Rᴴ * (R * Rᴴ)⁻¹)ᴴ = (R * Rᴴ)⁻¹ * R := by
    rw [Matrix.conjTranspose_mul, hinvh,
      Matrix.conjTranspose_conjTranspose]
  have hrec : ∀ D : Matrix r r ℂ,
      (Rᴴ * (R * Rᴴ)⁻¹)ᴴ * (Rᴴ * D * R)
          * (Rᴴ * (R * Rᴴ)⁻¹) = D := by
    intro D
    rw [hdagh]
    calc (R * Rᴴ)⁻¹ * R * (Rᴴ * D * R) * (Rᴴ * (R * Rᴴ)⁻¹)
        = ((R * Rᴴ)⁻¹ * (R * Rᴴ)) * D
          * ((R * Rᴴ) * (R * Rᴴ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = D := by
          rw [Matrix.inv_mul_of_invertible,
            Matrix.mul_inv_of_invertible, Matrix.one_mul,
            Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · intro D hD
    rw [hD, hrec]
  · intro D hD
    rw [hD, hrec, ← hD, hD]
  · intro U hUl hUr
    have hconj : (U * R) * (U * R)ᴴ = U * (R * Rᴴ) * Uᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hconjinv : ((U * R) * (U * R)ᴴ)⁻¹
        = U * (R * Rᴴ)⁻¹ * Uᴴ := by
      rw [hconj]
      apply Matrix.inv_eq_right_inv
      calc U * (R * Rᴴ) * Uᴴ * (U * (R * Rᴴ)⁻¹ * Uᴴ)
          = U * (R * Rᴴ) * (Uᴴ * U) * (R * Rᴴ)⁻¹ * Uᴴ := by
            simp only [Matrix.mul_assoc]
        _ = U * ((R * Rᴴ) * (R * Rᴴ)⁻¹) * Uᴴ := by
            rw [hUl]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = 1 := by
            rw [Matrix.mul_inv_of_invertible, Matrix.mul_one,
              hUr]
    have hdag' : (U * R)ᴴ * ((U * R) * (U * R)ᴴ)⁻¹
        = Rᴴ * (R * Rᴴ)⁻¹ * Uᴴ := by
      rw [hconjinv, Matrix.conjTranspose_mul]
      calc Rᴴ * Uᴴ * (U * (R * Rᴴ)⁻¹ * Uᴴ)
          = Rᴴ * (Uᴴ * U) * (R * Rᴴ)⁻¹ * Uᴴ := by
            simp only [Matrix.mul_assoc]
        _ = Rᴴ * (R * Rᴴ)⁻¹ * Uᴴ := by
            rw [hUl]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [hdag']
    rw [Matrix.conjTranspose_mul, hdagh,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]

end NCG
