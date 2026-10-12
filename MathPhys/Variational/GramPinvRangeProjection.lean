/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib
/-!
# The Moore--Penrose range projector of a Gram matrix

For a complex matrix `B` and a Hermitian `J` satisfying the Penrose identities for the Gram
matrix `Bᴴ B`, the matrix `P = B J Bᴴ` is an orthogonal projector (`Pᴴ = P`, `P² = P`) fixing
`B` (`P B = B`) (`gram_pinv_range_projection`).

Split out of `SameHistoryProvenancePythagoras` (declaration name unchanged).
-/

open Matrix
open scoped ComplexOrder

namespace MathPhys

set_option maxHeartbeats 800000

/-- The Moore--Penrose range formula is an orthogonal projector and fixes the
joint synthesis.  Here `J` is the dagger of the Gram, represented by its
Hermiticity, Penrose identities, and the equivalent synthesis-range identity. -/
theorem gram_pinv_range_projection
    {Y K : Type*} [Fintype Y] [Fintype K]
    [DecidableEq Y] [DecidableEq K]
    (B : Matrix Y K ℂ) (J : Matrix K K ℂ)
    (hJH : Jᴴ = J)
    (_hGJG : (Bᴴ * B) * J * (Bᴴ * B) = Bᴴ * B)
    (hJGJ : J * (Bᴴ * B) * J = J)
    (hBJG : B * J * (Bᴴ * B) = B) :
    let P := B * J * Bᴴ
    Pᴴ = P ∧ P * P = P ∧ P * B = B := by
  dsimp only
  have hPH : (B * J * Bᴴ)ᴴ = B * J * Bᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJH]
    simp only [Matrix.mul_assoc]
  have hP2 : (B * J * Bᴴ) * (B * J * Bᴴ) = B * J * Bᴴ := by
    calc
      (B * J * Bᴴ) * (B * J * Bᴴ)
          = B * (J * (Bᴴ * B) * J) * Bᴴ := by
              simp only [Matrix.mul_assoc]
      _ = B * J * Bᴴ := by rw [hJGJ]
  refine ⟨hPH, hP2, ?_⟩
  simpa only [Matrix.mul_assoc] using hBJG

end MathPhys
