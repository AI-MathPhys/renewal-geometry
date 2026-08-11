/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The three-generation Jarlskog commutator identity

Exact finite-dimensional algebra for the boxed CP invariant in
`thm:SM-mixing-invariants`.  The first identity below performs the complete
three-cycle expansion of the cube of a commutator with a diagonal Hermitian
matrix.  It is stated in coordinates that parameterize every Hermitian
three-by-three matrix.
-/

open Matrix

namespace NCG
namespace JarlskogCommutatorIdentity

/-- A diagonal three-generation Hermitian matrix with eigenvalues `a₀,a₁,a₂`. -/
def eigenvalueDiagonal (a₀ a₁ a₂ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(a₀ : ℂ), 0, 0;
     0, (a₁ : ℂ), 0;
     0, 0, (a₂ : ℂ)]

/-- Hermitian coordinates with oriented off-diagonal entries
`B₀₁=z₀₁`, `B₁₂=z₁₂`, and `B₂₀=z₂₀`.

The diagonal coordinates are allowed to be arbitrary because they cancel from
the commutator; taking them real gives every Hermitian matrix. -/
def hermitianOffDiagonalCoordinates
    (b₀ b₁ b₂ z₀₁ z₁₂ z₂₀ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![b₀, z₀₁, star z₂₀;
     star z₀₁, b₁, z₁₂;
     z₂₀, star z₁₂, b₂]

/-- The cyclic Vandermonde convention used in the manuscript. -/
def cyclicVandermonde (a₀ a₁ a₂ : ℝ) : ℝ :=
  (a₀ - a₁) * (a₁ - a₂) * (a₂ - a₀)

/-- Only the two oriented three-cycles contribute to `Tr([A,B]³)`.
The result is the exact complex identity before taking imaginary parts. -/
theorem diagonal_commutator_cube_trace
    (a₀ a₁ a₂ : ℝ) (b₀ b₁ b₂ z₀₁ z₁₂ z₂₀ : ℂ) :
    let A := eigenvalueDiagonal a₀ a₁ a₂
    let B := hermitianOffDiagonalCoordinates b₀ b₁ b₂ z₀₁ z₁₂ z₂₀
    ((A * B - B * A) ^ 3).trace =
      3 * (cyclicVandermonde a₀ a₁ a₂ : ℂ) *
        (z₀₁ * z₁₂ * z₂₀ - star (z₀₁ * z₁₂ * z₂₀)) := by
  dsimp
  simp [eigenvalueDiagonal, hermitianOffDiagonalCoordinates,
    cyclicVandermonde, pow_succ, Matrix.trace, Fin.sum_univ_three]
  ring

/-- Imaginary-part form of the commutator identity:
`Im Tr([A,B]³) = 6 Δ↻(A) Im(B₀₁B₁₂B₂₀)`. -/
theorem diagonal_commutator_cube_imaginary_trace
    (a₀ a₁ a₂ : ℝ) (b₀ b₁ b₂ z₀₁ z₁₂ z₂₀ : ℂ) :
    let A := eigenvalueDiagonal a₀ a₁ a₂
    let B := hermitianOffDiagonalCoordinates b₀ b₁ b₂ z₀₁ z₁₂ z₂₀
    Complex.im (((A * B - B * A) ^ 3).trace) =
      6 * cyclicVandermonde a₀ a₁ a₂ *
        Complex.im (z₀₁ * z₁₂ * z₂₀) := by
  dsimp
  rw [diagonal_commutator_cube_trace]
  simp [Complex.mul_im, Complex.sub_im, cyclicVandermonde]
  ring

/-- Coordinate-free Hermitian version of the three-cycle computation. -/
theorem hermitian_diagonal_commutator_cube_imaginary_trace
    (a₀ a₁ a₂ : ℝ) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hB : Bᴴ = B) :
    Complex.im
        (((eigenvalueDiagonal a₀ a₁ a₂ * B -
            B * eigenvalueDiagonal a₀ a₁ a₂) ^ 3).trace) =
      6 * cyclicVandermonde a₀ a₁ a₂ *
        Complex.im (B 0 1 * B 1 2 * B 2 0) := by
  have h10 := congrFun (congrFun hB 1) 0
  have h02 := congrFun (congrFun hB 0) 2
  have h21 := congrFun (congrFun hB 2) 1
  simp only [Matrix.conjTranspose_apply] at h10 h02 h21
  have hcoord : B = hermitianOffDiagonalCoordinates
      (B 0 0) (B 1 1) (B 2 2) (B 0 1) (B 1 2) (B 2 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianOffDiagonalCoordinates, h10, h02, h21]
  rw [hcoord]
  exact diagonal_commutator_cube_imaginary_trace
    a₀ a₁ a₂ (B 0 0) (B 1 1) (B 2 2) (B 0 1) (B 1 2) (B 2 0)

end JarlskogCommutatorIdentity
end NCG
