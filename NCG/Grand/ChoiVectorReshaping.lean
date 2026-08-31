/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct
import NCG.Grand.HermitianRankOneTraceNorm
import NCG.Grand.NaimarkPhaseSharpness

/-!
# Choi vector reshaping and marginal identities

This file fixes the row-major equivalence
`Fin d × Fin d ≃ Fin (d*d)` and proves the elementary identities connecting
Euclidean Choi vectors, square matrices, and the traced Choi marginal.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace ChoiVectorReshaping

variable {d : ℕ}

/-- Row-major flattening of a square matrix as a Euclidean Choi vector. -/
def matrixVector (A : Matrix (Fin d) (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin (d * d)) :=
  WithLp.toLp 2 (fun q =>
    A (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)

/-- Reshape a flattened Euclidean Choi vector as a square matrix. -/
def vectorMatrix (x : EuclideanSpace ℂ (Fin (d * d))) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => x (finProdFinEquiv (i, j))

/-- Trace the second Choi leg in flattened coordinates. -/
def choiMarginal (J : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ∑ k, J (finProdFinEquiv (i, k))
    (finProdFinEquiv (j, k))

@[simp] theorem vectorMatrix_matrixVector
    (A : Matrix (Fin d) (Fin d) ℂ) :
    vectorMatrix (matrixVector A) = A := by
  ext i j
  change A (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = A i j
  rw [Equiv.symm_apply_apply]

@[simp] theorem matrixVector_vectorMatrix
    (x : EuclideanSpace ℂ (Fin (d * d))) :
    matrixVector (vectorMatrix x) = x := by
  apply WithLp.ofLp_injective
  funext q
  change x (finProdFinEquiv (finProdFinEquiv.symm q)) = x q
  rw [Equiv.apply_symm_apply]

/-- Euclidean vector norm squared is the matrix Frobenius square. -/
theorem norm_sq_matrixVector (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖matrixVector A‖ ^ 2 = hsFrobSq A := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [matrixVector, WithLp.ofLp_toLp, hsFrobSq]
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, Complex.normSq_eq_norm_sq]

/-- The flattened-vector distance is the Frobenius distance. -/
theorem norm_sub_matrixVector_sq
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    ‖matrixVector A - matrixVector B‖ ^ 2 = hsFrobSq (A - B) := by
  have hsub : matrixVector A - matrixVector B = matrixVector (A - B) := by
    apply WithLp.ofLp_injective
    funext q
    simp [matrixVector, Matrix.sub_apply]
  rw [hsub, norm_sq_matrixVector]

/-- The Choi marginal is additive. -/
theorem choiMarginal_add
    (J K : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) :
    choiMarginal (J + K) = choiMarginal J + choiMarginal K := by
  ext i j
  simp [choiMarginal, Matrix.add_apply, Finset.sum_add_distrib]

/-- The Choi marginal of a rank-one vector is its matrix row Gram `AAᴴ`. -/
theorem choiMarginal_pureOuter
    (x : EuclideanSpace ℂ (Fin (d * d))) :
    choiMarginal (HermitianRankOneTraceNorm.pureOuter x) =
      vectorMatrix x * (vectorMatrix x)ᴴ := by
  ext i j
  change (∑ k, x (finProdFinEquiv (i, k)) *
      star (x (finProdFinEquiv (j, k)))) =
    ∑ k, x (finProdFinEquiv (i, k)) *
      star (x (finProdFinEquiv (j, k)))
  rfl

/-- Partial trace preserves positivity. -/
theorem choiMarginal_posSemidef
    {J : Matrix (Fin (d * d)) (Fin (d * d)) ℂ}
    (hJ : J.PosSemidef) : (choiMarginal J).PosSemidef := by
  have hsum : choiMarginal J = ∑ k : Fin d,
      J.submatrix (fun i => finProdFinEquiv (i, k))
        (fun i => finProdFinEquiv (i, k)) := by
    ext i j
    simp [choiMarginal, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  simpa using Matrix.posSemidef_sum (R := ℂ) Finset.univ
    (fun k _ => hJ.submatrix (fun i => finProdFinEquiv (i, k)))

/-- Partial trace preserves the total trace. -/
theorem trace_choiMarginal
    (J : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) :
    (choiMarginal J).trace = J.trace := by
  simp only [choiMarginal, Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]

end ChoiVectorReshaping
end NCG
