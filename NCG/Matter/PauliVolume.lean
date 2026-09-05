/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.GradingAmbiguity

/-!
# Pauli-volume theorem (`cor:v5-pauli-volume`, SM manuscript)

For Pauli directions `Δ_j = x_j·σ`, the cyclic Nambu bracket
`s₃(X,Y,Z) = X[Y,Z] + Y[Z,X] + Z[X,Y]` evaluates to
`6i·det[x₁ x₂ x₃]·I₂`: the primitive source is a genuine oriented
three-dimensional noncommutative volume.  (The concluding sentence
— one nonzero commutator is insufficient, linearly dependent
directions are load bearing — is interpretive prose about the
determinant's vanishing on dependent triples.)
-/

open Matrix Complex

namespace NCG

/-- The cyclic Nambu bracket `s₃(X,Y,Z) = X[Y,Z] + Y[Z,X] + Z[X,Y]`. -/
def nambuS3 (X Y Z : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  X * (Y * Z - Z * Y) + Y * (Z * X - X * Z) + Z * (X * Y - Y * X)

/-- `cor:v5-pauli-volume`: for Pauli directions,
`s₃(x·σ, y·σ, z·σ) = 6i·det[x y z]·I₂`. -/
theorem pauli_volume (x y z : Fin 3 → ℝ) :
    nambuS3 (pauliVec x) (pauliVec y) (pauliVec z)
      = (6 * Complex.I
          * ((Matrix.of ![![x 0, y 0, z 0], ![x 1, y 1, z 1],
              ![x 2, y 2, z 2]]).det : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.det_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [nambuS3, pauliVec]
      ring

end NCG
