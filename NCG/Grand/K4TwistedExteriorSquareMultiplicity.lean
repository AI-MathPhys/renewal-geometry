/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.K4CutCycleIsotypicSchur

/-!
# Multiplicity one for the twisted exterior square of the `S₄` standard module

This file supplies the finite Schur calculation missing from the `N = 4`
part of `thm:dimension-K4-selector`.  In the wedge basis
`e₀ ∧ e₁, e₀ ∧ e₂, e₁ ∧ e₂`, the matrices below are the second compound
matrices of the standard transposition and four-cycle.  The explicit Hodge
matrix identifies this exterior-square action with the sign twist of the
standard triplet.  Solving the two generator equations then proves that every
such intertwiner is a unique scalar multiple of that Hodge matrix.
-/

namespace NCG

/-- The action of the standard transposition on `Λ² ℂ³` in the ordered wedge
basis `(01, 02, 12)`. -/
def k4ExteriorSquareTransposition : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1, 0, 0; 0, 0, 1; 0, 1, 0]

/-- The action of the standard four-cycle on `Λ² ℂ³` in the ordered wedge
basis `(01, 02, 12)`. -/
def k4ExteriorSquareFourCycle : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, 0; -1, 0, 1; 1, 0, 0]

/-- An integral Hodge identification `Λ²W₄ ≃ W₄ ⊗ sgn` in the chosen
non-orthonormal standard basis.  Its determinant is `-16`. -/
def k4TwistedHodgeMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, -1, -3; 1, 3, 1; -3, -1, 1]

/-- The inverse of the integral Hodge identification. -/
noncomputable def k4TwistedHodgeInverse : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(1 / 4), -(1 / 4), -(1 / 2);
      1 / 4, 1 / 2, 1 / 4;
      -(1 / 2), -(1 / 4), -(1 / 4)]

/-- The explicit Hodge matrix intertwines the two generator actions. -/
theorem k4TwistedHodgeMatrix_intertwines :
    k4TwistedHodgeMatrix * k4ExteriorSquareTransposition =
        (-k4StandardTransposition) * k4TwistedHodgeMatrix
    ∧ k4TwistedHodgeMatrix * k4ExteriorSquareFourCycle =
        (-k4StandardFourCycle) * k4TwistedHodgeMatrix := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [k4TwistedHodgeMatrix, k4ExteriorSquareTransposition,
      k4ExteriorSquareFourCycle, k4StandardTransposition,
      k4StandardFourCycle, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

/-- The Hodge identification is nonsingular. -/
theorem k4TwistedHodgeMatrix_det : k4TwistedHodgeMatrix.det = -16 := by
  rw [Matrix.det_fin_three]
  norm_num [k4TwistedHodgeMatrix, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]

/-- The displayed rational matrix is a two-sided inverse. -/
theorem k4TwistedHodgeInverse_twoSided :
    k4TwistedHodgeInverse * k4TwistedHodgeMatrix = 1 ∧
      k4TwistedHodgeMatrix * k4TwistedHodgeInverse = 1 := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [k4TwistedHodgeMatrix, k4TwistedHodgeInverse,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val]

/-- Moving a standard generator through the inverse Hodge map produces the
negative exterior-square generator. -/
theorem k4TwistedHodgeInverse_generator_relations :
    k4TwistedHodgeInverse * k4StandardTransposition =
        -(k4ExteriorSquareTransposition * k4TwistedHodgeInverse)
    ∧ k4TwistedHodgeInverse * k4StandardFourCycle =
        -(k4ExteriorSquareFourCycle * k4TwistedHodgeInverse) := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [k4TwistedHodgeInverse, k4ExteriorSquareTransposition,
      k4ExteriorSquareFourCycle, k4StandardTransposition,
      k4StandardFourCycle, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

/-- **Multiplicity one at `N = 4`.**  An intertwiner from the exterior square
of the standard triplet to its sign twist is a scalar multiple of the explicit
Hodge identification.  Because the Hodge matrix is nonzero, the scalar is
unique; hence this Hom space is exactly one-dimensional. -/
theorem k4TwistedExteriorSquare_intertwiner_unique
    (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hs : B * k4ExteriorSquareTransposition =
      (-k4StandardTransposition) * B)
    (ht : B * k4ExteriorSquareFourCycle =
      (-k4StandardFourCycle) * B) :
    ∃! α : ℂ, B = α • k4TwistedHodgeMatrix := by
  let C := B * k4TwistedHodgeInverse
  have hCs : C * k4StandardTransposition =
      k4StandardTransposition * C := by
    rw [show C = B * k4TwistedHodgeInverse from rfl, Matrix.mul_assoc,
      k4TwistedHodgeInverse_generator_relations.1, Matrix.mul_neg,
      ← Matrix.mul_assoc, hs]
    simp [Matrix.mul_assoc]
  have hCt : C * k4StandardFourCycle =
      k4StandardFourCycle * C := by
    rw [show C = B * k4TwistedHodgeInverse from rfl, Matrix.mul_assoc,
      k4TwistedHodgeInverse_generator_relations.2, Matrix.mul_neg,
      ← Matrix.mul_assoc, ht]
    simp [Matrix.mul_assoc]
  obtain ⟨α, hC⟩ := k4StandardTriplet_jointCommutant_scalar C hCs hCt
  have hB : B = α • k4TwistedHodgeMatrix := by
    calc
      B = B * 1 := (Matrix.mul_one B).symm
      _ = B * (k4TwistedHodgeInverse * k4TwistedHodgeMatrix) := by
        rw [k4TwistedHodgeInverse_twoSided.1]
      _ = C * k4TwistedHodgeMatrix := by rw [Matrix.mul_assoc]
      _ = (α • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *
          k4TwistedHodgeMatrix := by rw [hC]
      _ = α • k4TwistedHodgeMatrix := by simp
  refine ⟨α, hB, ?_⟩
  intro β hβ
  have hentryα := congrArg (fun M => M 2 2) hB
  have hentryβ := congrArg (fun M => M 2 2) hβ
  simpa [k4TwistedHodgeMatrix, Matrix.of_apply, Matrix.cons_val] using
    hentryβ.symm.trans hentryα

end NCG
