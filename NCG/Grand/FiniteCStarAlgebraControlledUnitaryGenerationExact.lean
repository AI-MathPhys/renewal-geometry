/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite controlled-unitary generation of finite C-star algebras

Every element of a unital C-star algebra is a linear combination of four
unitaries.  Applying that theorem to a finite vector-space basis produces one
finite, target-specific bank of controlled unitary operations which spans the
entire represented coefficient algebra.
-/

namespace NCG.FiniteCStarAlgebraControlledUnitaryGenerationExact

noncomputable section

open Submodule

universe u

variable (A : Type u) [CStarAlgebra A] [FiniteDimensional ℂ A]

/-- A finite basis index paired with the four unitary summands. -/
abbrev ControlIndex := Module.Basis.ofVectorSpaceIndex ℂ A × Fin 4

private noncomputable def basisFourUnitaryData
    (i : Module.Basis.ofVectorSpaceIndex ℂ A) :=
  CStarAlgebra.exists_sum_four_unitary
    ((Module.Basis.ofVectorSpace ℂ A) i)

/-- The finite controlled-unitary bank attached to a vector-space basis. -/
noncomputable def controlledUnitary (q : ControlIndex A) : unitary A :=
  (basisFourUnitaryData A q.1).choose q.2

/-- Coefficients expressing each basis vector in its four unitary controls. -/
noncomputable def controlledCoefficient (q : ControlIndex A) : ℂ :=
  (basisFourUnitaryData A q.1).choose_spec.choose q.2

theorem basis_eq_sum_controlledUnitary
    (i : Module.Basis.ofVectorSpaceIndex ℂ A) :
    (Module.Basis.ofVectorSpace ℂ A) i =
      ∑ j : Fin 4,
        controlledCoefficient A (i, j) •
          (controlledUnitary A (i, j) : A) := by
  exact (basisFourUnitaryData A i).choose_spec.choose_spec.1

/-- The chosen bank is finite and its underlying unitary operations span the
whole finite C-star algebra. -/
theorem finite_controlled_unitaries_span :
    span ℂ (Set.range fun q : ControlIndex A =>
      (controlledUnitary A q : A)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  let b := Module.Basis.ofVectorSpace ℂ A
  rw [← b.sum_repr x]
  apply sum_mem
  intro i hi
  apply smul_mem
  rw [basis_eq_sum_controlledUnitary A i]
  apply sum_mem
  intro j hj
  apply smul_mem
  exact subset_span ⟨(i, j), rfl⟩

/-- Existential form: a genuinely finite index type and a unitary family span
the target algebra. -/
theorem exists_finite_controlled_unitary_spanning_family :
    ∃ (ι : Type u) (_ : Fintype ι) (u : ι → unitary A),
      span ℂ (Set.range fun i => (u i : A)) = ⊤ := by
  exact ⟨ControlIndex A, inferInstance, controlledUnitary A,
    finite_controlled_unitaries_span A⟩

end

end NCG.FiniteCStarAlgebraControlledUnitaryGenerationExact
