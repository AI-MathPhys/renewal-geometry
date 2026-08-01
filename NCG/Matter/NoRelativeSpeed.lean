/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# No sectorwise speed after common-origin descent
  (`cor:no-relative-speed`, SM manuscript)

If the finite fermion coordinate maps `C₊`, `C₋` are unitary
identifications of the reduced source and one-form modules, then
`B_F = C₋ ∂_F C₊*` has the same Gram operator as `∂_F` (transported
by `C₊`), and orthogonal representation projections preserve their
sectorwise Hilbert–Schmidt norms.  Relative source–residue speed
factors are therefore equal to one for the actual reduced operator
(interpretive prose about these identities).
-/

open Matrix

namespace NCG

/-- `cor:no-relative-speed`: under unitary coordinate maps, the
descended operator has the transported Gram, and sectorwise
Hilbert–Schmidt norms are preserved. -/
theorem no_relative_speed {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (Cm : Matrix m m ℂ) (Cp : Matrix n n ℂ) (dF : Matrix m n ℂ)
    (hCm : Cmᴴ * Cm = 1) (hCp' : Cpᴴ * Cp = 1) :
    ((Cm * dF * Cpᴴ)ᴴ * (Cm * dF * Cpᴴ)
      = Cp * (dFᴴ * dF) * Cpᴴ) ∧
    ∀ P : Matrix n n ℂ,
      Matrix.trace (((Cm * dF * Cpᴴ) * (Cp * P * Cpᴴ))ᴴ
        * ((Cm * dF * Cpᴴ) * (Cp * P * Cpᴴ)))
      = Matrix.trace ((dF * P)ᴴ * (dF * P)) := by
  have hGram : (Cm * dF * Cpᴴ)ᴴ * (Cm * dF * Cpᴴ)
      = Cp * (dFᴴ * dF) * Cpᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Cmᴴ Cm, hCm, Matrix.one_mul]
  refine ⟨hGram, fun P => ?_⟩
  have hB : (Cm * dF * Cpᴴ) * (Cp * P * Cpᴴ)
      = Cm * (dF * P) * Cpᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Cpᴴ Cp, hCp', Matrix.one_mul]
  rw [hB, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Cmᴴ Cm, hCm, Matrix.one_mul,
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [hCp', Matrix.mul_one]

end NCG
