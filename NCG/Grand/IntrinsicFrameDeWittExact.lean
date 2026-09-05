/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.IntrinsicFrameVolumeDeWitt

/-!
# Exact intrinsic frame-volume and DeWitt certificate

This module bundles the exact clauses of `thm:DeWitt`.  The analytic
determinant Hessian, exterior-volume identity, and inverse trace map are
provided by the flagship modules.  Here we add an explicit global coordinate
chart for real symmetric `3 × 3` matrices.  In these coordinates the DeWitt
form is diagonal with five positive coefficients and one negative coefficient,
which records the full `(5, 1)` signature rather than only exhibiting positive
and negative test directions.
-/

open Matrix

namespace NCG
namespace IntrinsicFrameDeWitt

/-- A six-coordinate chart on real symmetric `3 × 3` matrices.  Coordinates
`0` through `4` are traceless; coordinate `5` is the scalar direction. -/
def sym3Chart (x : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x 0 + x 1 + x 5, x 2, x 3;
     x 2, -x 0 + x 1 + x 5, x 4;
     x 3, x 4, -2 * x 1 + x 5]

theorem sym3Chart_symmetric (x : Fin 6 → ℝ) :
    (sym3Chart x)ᵀ = sym3Chart x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sym3Chart_injective : Function.Injective sym3Chart := by
  intro x y hxy
  have h00 := congrArg (fun A => A (0 : Fin 3) (0 : Fin 3)) hxy
  have h11 := congrArg (fun A => A (1 : Fin 3) (1 : Fin 3)) hxy
  have h22 := congrArg (fun A => A (2 : Fin 3) (2 : Fin 3)) hxy
  have h01 := congrArg (fun A => A (0 : Fin 3) (1 : Fin 3)) hxy
  have h02 := congrArg (fun A => A (0 : Fin 3) (2 : Fin 3)) hxy
  have h12 := congrArg (fun A => A (1 : Fin 3) (2 : Fin 3)) hxy
  simp [sym3Chart] at h00 h11 h22 h01 h02 h12
  have h0 : x 0 = y 0 := by linarith
  have h1 : x 1 = y 1 := by linarith
  have h5 : x 5 = y 5 := by linarith
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h01
  · exact h02
  · exact h12
  · exact h5

/-- Every real symmetric `3 × 3` matrix has coordinates in `sym3Chart`. -/
theorem sym3Chart_surjective_on_symmetric
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ = A) :
    ∃ x : Fin 6 → ℝ, sym3Chart x = A := by
  let x : Fin 6 → ℝ := ![
    (A 0 0 - A 1 1) / 2,
    (A 0 0 + A 1 1 - 2 * A 2 2) / 6,
    A 0 1,
    A 0 2,
    A 1 2,
    (A 0 0 + A 1 1 + A 2 2) / 3]
  refine ⟨x, ?_⟩
  have hs (i j : Fin 3) : A j i = A i j := by
    have := congrArg (fun M => M i j) hA
    simpa using this
  have h10 : A 0 1 = A 1 0 := hs 1 0
  have h20 : A 0 2 = A 2 0 := hs 2 0
  have h21 : A 1 2 = A 2 1 := hs 2 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sym3Chart, x, h10, h20, h21] <;> ring

/-- The DeWitt form diagonalizes in `sym3Chart` with five positive axes and
one negative axis.  Together with injectivity and surjectivity on symmetric
matrices, this is an exact `(5,1)` signature certificate. -/
theorem sym3Chart_deWitt_diagonal (x y : Fin 6 → ℝ) :
    Matrix.trace (sym3Chart x * sym3Chart y) -
        Matrix.trace (sym3Chart x) * Matrix.trace (sym3Chart y) =
      2 * x 0 * y 0 + 6 * x 1 * y 1 +
      2 * x 2 * y 2 + 2 * x 3 * y 3 + 2 * x 4 * y 4 -
      6 * x 5 * y 5 := by
  simp [sym3Chart, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- The cotangent inverse pairing is exactly
`Tr(PQ) - 1/2 Tr(P) Tr(Q)`. -/
theorem cotangentInverse_pairing
    (P Q : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (dewittInv 3 P * Q) =
      Matrix.trace (P * Q) - 1 / 2 * Matrix.trace P * Matrix.trace Q := by
  rw [dewittInv, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  norm_num

/-- Exact clause bundle for the manuscript theorem `thm:DeWitt`. -/
theorem intrinsic_frame_volume_deWitt_exact :
    Function.Injective sym3Chart ∧
    (∀ A : Matrix (Fin 3) (Fin 3) ℝ, Aᵀ = A →
      ∃ x : Fin 6 → ℝ, sym3Chart x = A) ∧
    (∀ x y : Fin 6 → ℝ,
      Matrix.trace (sym3Chart x * sym3Chart y) -
          Matrix.trace (sym3Chart x) * Matrix.trace (sym3Chart y) =
        2 * x 0 * y 0 + 6 * x 1 * y 1 +
        2 * x 2 * y 2 + 2 * x 3 * y 3 + 2 * x 4 * y 4 -
        6 * x 5 * y 5) ∧
    (∀ P Q : Matrix (Fin 3) (Fin 3) ℝ,
      Matrix.trace (dewittInv 3 P * Q) =
        Matrix.trace (P * Q) - 1 / 2 * Matrix.trace P * Matrix.trace Q) := by
  exact ⟨sym3Chart_injective, sym3Chart_surjective_on_symmetric,
    sym3Chart_deWitt_diagonal, cotangentInverse_pairing⟩

end IntrinsicFrameDeWitt
end NCG
