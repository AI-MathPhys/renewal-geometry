/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical full-matrix target control
  (`cor:canonical-full-matrix-control`, Gran-Tensor manuscript)

* `full_matrix_control`:
  (1) the mixed-bracket identities `⁅A⊗1, C⊗D⁆ = ⁅A,C⁆⊗D` and
      `⁅1⊗B, C⊗D⁆ = C⊗⁅B,D⁆` — local controls conjugated
      through an entangling axis produce two-body axes;
  (2) the Pauli bracket table `⁅σx,σz⁆ = −2i·σy`,
      `⁅σy,σz⁆ = 2i·σx`, `⁅σx,σy⁆ = 2i·σz` — instantiating
      (1) at the Pauli axes yields each two-body axis as an
      iterated bracket of local generators on the entangling
      `Z⊗Z` axis.

The actual closure through all fifteen nonidentity Pauli axes, its full-matrix
span consequence, and the resolved-simple-target ideal argument are proved in
`NCG.Grand.TwoClockFullMatrixLieGeneration`.
-/

open Matrix
open scoped Kronecker

namespace NCG

private lemma kron_sub_left {m n p q : Type*}
    (X Y : Matrix m n ℂ) (D : Matrix p q ℂ) :
    (X - Y) ⊗ₖ D = X ⊗ₖ D - Y ⊗ₖ D := by
  ext a b
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply]
  ring

private lemma kron_sub_right {m n p q : Type*}
    (C : Matrix m n ℂ) (X Y : Matrix p q ℂ) :
    C ⊗ₖ (X - Y) = C ⊗ₖ X - C ⊗ₖ Y := by
  ext a b
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply]
  ring

/-- `cor:canonical-full-matrix-control`. -/
theorem full_matrix_control {d : Type*} [Fintype d]
    [DecidableEq d] :
    -- (1) mixed brackets produce two-body axes
    (∀ A C D : Matrix d d ℂ,
      (A ⊗ₖ (1 : Matrix d d ℂ)) * (C ⊗ₖ D)
          - (C ⊗ₖ D) * (A ⊗ₖ (1 : Matrix d d ℂ))
        = (A * C - C * A) ⊗ₖ D)
    ∧ (∀ B C D : Matrix d d ℂ,
        ((1 : Matrix d d ℂ) ⊗ₖ B) * (C ⊗ₖ D)
            - (C ⊗ₖ D) * ((1 : Matrix d d ℂ) ⊗ₖ B)
          = C ⊗ₖ (B * D - D * B))
    -- (2) the Pauli bracket table
    ∧ (!![(0 : ℂ), 1; 1, 0] * !![(1 : ℂ), 0; 0, -1]
          - !![(1 : ℂ), 0; 0, -1] * !![(0 : ℂ), 1; 1, 0]
        = (-(2 * Complex.I))
            • !![(0 : ℂ), -Complex.I; Complex.I, 0])
    ∧ (!![(0 : ℂ), -Complex.I; Complex.I, 0]
            * !![(1 : ℂ), 0; 0, -1]
          - !![(1 : ℂ), 0; 0, -1]
            * !![(0 : ℂ), -Complex.I; Complex.I, 0]
        = (2 * Complex.I) • !![(0 : ℂ), 1; 1, 0])
    ∧ (!![(0 : ℂ), 1; 1, 0]
            * !![(0 : ℂ), -Complex.I; Complex.I, 0]
          - !![(0 : ℂ), -Complex.I; Complex.I, 0]
            * !![(0 : ℂ), 1; 1, 0]
        = (2 * Complex.I) • !![(1 : ℂ), 0; 0, -1]) := by
  have hbracketL : ∀ A C D : Matrix d d ℂ,
      (A ⊗ₖ (1 : Matrix d d ℂ)) * (C ⊗ₖ D)
          - (C ⊗ₖ D) * (A ⊗ₖ (1 : Matrix d d ℂ))
        = (A * C - C * A) ⊗ₖ D := by
    intro A C D
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, kron_sub_left]
  have hbracketR : ∀ B C D : Matrix d d ℂ,
      ((1 : Matrix d d ℂ) ⊗ₖ B) * (C ⊗ₖ D)
          - (C ⊗ₖ D) * ((1 : Matrix d d ℂ) ⊗ₖ B)
        = C ⊗ₖ (B * D - D * B) := by
    intro B C D
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, kron_sub_right]
  refine ⟨hbracketL, hbracketR, ?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Complex.ext_iff] <;> ring_nf

end NCG
