/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib

/-!
# Centered commutant normal component

The Haar conditional expectation onto a finite kinematic commutant is
trace-preserving and has its range in that commutant.  This file proves the
last algebraic step of `thm:SMST-generator-projections`: after subtracting the
scalar trace component, its output vanishes whenever the commutant is scalar.
-/

open Matrix

namespace NCG

/-- The canonical centered normal candidate associated with a
trace-preserving commutant expectation. -/
noncomputable def centeredCommutantNormal
    {n : Type*} [Fintype n] [DecidableEq n]
    (expectedEven : Matrix n n ℂ) (evenGenerator : Matrix n n ℂ) :
    Matrix n n ℂ :=
  expectedEven -
    (Matrix.trace evenGenerator / (Fintype.card n : ℂ)) • 1

/-- In a scalar commutant, every trace-preserving commutant expectation is
the scalar trace expectation.  Hence its centered normal candidate is zero. -/
theorem scalarCommutant_centeredExpectation_zero
    {n a : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (kinematic : a → Matrix n n ℂ)
    (evenGenerator expectedEven : Matrix n n ℂ)
    (hrange : ∀ i, expectedEven * kinematic i =
      kinematic i * expectedEven)
    (hscalarCommutant : ∀ Z : Matrix n n ℂ,
      (∀ i, Z * kinematic i = kinematic i * Z) →
        ∃ c : ℂ, Z = c • 1)
    (htrace : Matrix.trace expectedEven = Matrix.trace evenGenerator) :
    centeredCommutantNormal expectedEven evenGenerator = 0 := by
  obtain ⟨c, hc⟩ := hscalarCommutant expectedEven hrange
  have htraceScalar := htrace
  rw [hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at htraceScalar
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcoefficient :
      c = Matrix.trace evenGenerator / (Fintype.card n : ℂ) :=
    (eq_div_iff hcard).2 htraceScalar
  unfold centeredCommutantNormal
  rw [hc, hcoefficient, sub_self]

end NCG
