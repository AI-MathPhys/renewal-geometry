/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.NCG.OperatorAlgebras.HilbertSchmidtSlices

/-!
# The slice map as a linear map in the functional

Split out of `MathPhys.Commutant.IntrinsicCoefficientQuiver`: `sliceLinearMap T` is
`φ ↦ (φ ⊗ id)(T)`, linear in the functional `φ ∈ B(V_a, V_b)^*`.
-/

open Matrix
open scoped Kronecker

namespace MathPhys

section SliceLinear

open SMSTQuiverCommutantAssembly

variable {Va Vb Na Nb : Type*} [Fintype Va] [Fintype Vb] [DecidableEq Va] [DecidableEq Vb]

/-- The slice map `φ ↦ (φ ⊗ id)(T)`, linear in the functional `φ ∈ B(V_a, V_b)^*`. -/
def sliceLinearMap (T : Matrix (Vb × Nb) (Va × Na) ℂ) :
    (Matrix Vb Va ℂ →ₗ[ℂ] ℂ) →ₗ[ℂ] Matrix Nb Na ℂ where
  toFun φ := functionalSlice φ T
  map_add' φ ψ := by
    funext n m
    rfl
  map_smul' a φ := by
    funext n m
    rfl

omit [Fintype Va] [Fintype Vb] [DecidableEq Va] [DecidableEq Vb] in
theorem sliceLinearMap_apply (T : Matrix (Vb × Nb) (Va × Na) ℂ) (φ : Matrix Vb Va ℂ →ₗ[ℂ] ℂ) :
    sliceLinearMap T φ = functionalSlice φ T :=
  rfl

end SliceLinear

end MathPhys
