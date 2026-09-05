/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical process-history representation
  (`thm:process-representation`, Gran-Tensor manuscript)

* `process_representation`: the free path algebra modulo the
  kernel of its response representation is canonically the
  generated finite-dimensional algebra (first isomorphism
  theorem via the kernel congruence), and the construction is
  independent of the physical frame: conjugating the
  representation by any invertible frame leaves the kernel
  unchanged.

Rendering disclosed: the `*`-structure and the
support-minimality clause are the manuscript's citation of
`thm:canonical-comb-dilation` (hard tier); the failure of
independence for arbitrary unreduced positive factorizations is
`cth:nonminimal-factorization` (proved,
`NCG.nonminimal_factorization`).
-/

open Matrix

namespace NCG

/-- `thm:process-representation`. -/
theorem process_representation {A : Type*} [Ring A]
    {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : A →+* Matrix n n ℂ) :
    -- (1) first isomorphism: the path algebra modulo the
    --     kernel congruence is the generated algebra
    Nonempty ((RingCon.ker ρ).Quotient ≃+* ρ.rangeS)
    -- (2) frame independence: conjugation by an invertible
    --     frame preserves the kernel
    ∧ (∀ (U : Matrix n n ℂ), IsUnit U →
        ∀ a : A, U * ρ a * U⁻¹ = 0 ↔ ρ a = 0) := by
  constructor
  · exact ⟨RingCon.quotientKerEquivRangeS ρ⟩
  · intro U hU a
    constructor
    · intro h
      have h1 := congrArg (fun M => U⁻¹ * M * U) h
      simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
      letI := hU.invertible
      calc ρ a = (U⁻¹ * U) * ρ a * (U⁻¹ * U) := by
            rw [Matrix.inv_mul_of_invertible, Matrix.one_mul,
              Matrix.mul_one]
        _ = U⁻¹ * (U * ρ a * U⁻¹) * U := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
    · intro h
      rw [h, Matrix.mul_zero, Matrix.zero_mul]

end NCG
