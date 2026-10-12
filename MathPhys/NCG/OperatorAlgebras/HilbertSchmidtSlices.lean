/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Hilbert–Schmidt slices of block matrices

Split out of `MathPhys.Commutant.MultiplicityQuiverArrows`: for a block
`T : V_a ⊗ N_a → V_b ⊗ N_b`, `functionalSlice φ T = (φ ⊗ id)(T)` is the slice along a linear
functional `φ ∈ B(V_a, V_b)^*`, and `blockSlice T vb va` is its value on the matrix-entry
functionals (the `(vb, va)` coefficient block).  Every functional slice is a linear
combination of the entry slices (`functionalSlice_eq_sum`).
-/

open Matrix

namespace MathPhys
namespace SMSTQuiverCommutantAssembly

section Slices

variable {Va Vb Na Nb : Type*} [Fintype Va] [Fintype Vb] [DecidableEq Va] [DecidableEq Vb]

/-- `(φ ⊗ id)(T)`: the slice of a block `T : V_a ⊗ N_a → V_b ⊗ N_b` along a
linear functional `φ ∈ B(V_a, V_b)^*`. -/
def functionalSlice (φ : Matrix Vb Va ℂ →ₗ[ℂ] ℂ)
    (T : Matrix (Vb × Nb) (Va × Na) ℂ) : Matrix Nb Na ℂ :=
  fun n m => φ (fun vb va => T (vb, n) (va, m))

/-- The Hilbert--Schmidt basis slice `(E_{vb,va}^* ⊗ id)(T)`, i.e. the
`(vb, va)` coefficient block of `T`. -/
def blockSlice (T : Matrix (Vb × Nb) (Va × Na) ℂ) (vb : Vb) (va : Va) :
    Matrix Nb Na ℂ :=
  fun n m => T (vb, n) (va, m)

omit [Fintype Va] [Fintype Vb] [DecidableEq Va] [DecidableEq Vb] in
/-- The entry slice is the functional slice along the entry functional. -/
theorem blockSlice_eq_functionalSlice (T : Matrix (Vb × Nb) (Va × Na) ℂ)
    (vb : Vb) (va : Va) :
    blockSlice T vb va = functionalSlice (Matrix.entryLinearMap ℂ ℂ vb va) T := by
  funext n m
  rfl

/-- Every functional slice is a linear combination of the entry slices. -/
theorem functionalSlice_eq_sum (φ : Matrix Vb Va ℂ →ₗ[ℂ] ℂ)
    (T : Matrix (Vb × Nb) (Va × Na) ℂ) :
    functionalSlice φ T =
      ∑ vb : Vb, ∑ va : Va, φ (Matrix.single vb va 1) • blockSlice T vb va := by
  funext n m
  simp only [functionalSlice, Matrix.sum_apply, Matrix.smul_apply, blockSlice,
    smul_eq_mul]
  conv_lhs =>
    rw [Matrix.matrix_eq_sum_single (fun vb va => T (vb, n) (va, m))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun vb _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun va _ => ?_
  have : Matrix.single vb va (T (vb, n) (va, m)) =
      T (vb, n) (va, m) • Matrix.single vb va (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

end Slices

end SMSTQuiverCommutantAssembly
end MathPhys
