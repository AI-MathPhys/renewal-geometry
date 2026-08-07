/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Minimal CP-capable residue rank
  (`prop:SM-residue-minimum`, Gran-Tensor manuscript)

* `residue_minimum`: a positive rank-one additive residue
  cannot generate a nonzero Dirac triangle phase — for
  `R = vv*` the triangle product is
  `R₁₂R₂₃R₃₁ = |v₁v₂v₃|² ∈ ℝ≥0`; while the explicit rank-two
  residue `R = vv* + ww*` with `v = (1,1,1)`, `w = (1,i,0)` is
  positive semidefinite, has two independent directions, and
  carries the nonzero CP triangle `R₁₂R₂₃R₃₁ = 1 - i`.  Rank
  one may produce mixing but not Dirac CP; rank two is the
  minimum capable of a nonzero CP phase.

Rendering disclosed: `rank R = 2` is rendered by the linear
independence of the two generating directions of the displayed
additive residue.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Rank-one operators `vv*` are positive semidefinite. -/
lemma vecMulVec_psd {n : Type*} [Fintype n]
    (u : n → ℂ) : (Matrix.vecMulVec u (star u)).PosSemidef := by
  have hA : Matrix.vecMulVec u (star u)
      = (Matrix.of fun (_ : Unit) (j : n) => star u j)ᴴ
        * (Matrix.of fun (_ : Unit) (j : n) => star u j) := by
    ext i j
    rw [Matrix.mul_apply]
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
      mul_comm]
  rw [hA]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `prop:SM-residue-minimum`: rank one cannot generate a Dirac
CP triangle; the explicit rank-two residue can. -/
theorem residue_minimum :
    (∀ v : Fin 3 → ℂ,
      Matrix.vecMulVec v (star v) 0 1
        * Matrix.vecMulVec v (star v) 1 2
        * Matrix.vecMulVec v (star v) 2 0
      = ((Complex.normSq (v 0) * Complex.normSq (v 1)
          * Complex.normSq (v 2) : ℝ) : ℂ))
    ∧ (Matrix.vecMulVec (![1, 1, 1] : Fin 3 → ℂ)
          (star (![1, 1, 1] : Fin 3 → ℂ))
        + Matrix.vecMulVec (![1, Complex.I, 0] : Fin 3 → ℂ)
            (star (![1, Complex.I, 0] : Fin 3 → ℂ))).PosSemidef
    ∧ (∀ c d : ℂ,
        c • (![1, 1, 1] : Fin 3 → ℂ)
          + d • (![1, Complex.I, 0] : Fin 3 → ℂ) = 0
        → c = 0 ∧ d = 0)
    ∧ (Matrix.vecMulVec (![1, 1, 1] : Fin 3 → ℂ)
          (star (![1, 1, 1] : Fin 3 → ℂ))
        + Matrix.vecMulVec (![1, Complex.I, 0] : Fin 3 → ℂ)
            (star (![1, Complex.I, 0] : Fin 3 → ℂ))) 0 1
      * (Matrix.vecMulVec (![1, 1, 1] : Fin 3 → ℂ)
          (star (![1, 1, 1] : Fin 3 → ℂ))
        + Matrix.vecMulVec (![1, Complex.I, 0] : Fin 3 → ℂ)
            (star (![1, Complex.I, 0] : Fin 3 → ℂ))) 1 2
      * (Matrix.vecMulVec (![1, 1, 1] : Fin 3 → ℂ)
          (star (![1, 1, 1] : Fin 3 → ℂ))
        + Matrix.vecMulVec (![1, Complex.I, 0] : Fin 3 → ℂ)
            (star (![1, Complex.I, 0] : Fin 3 → ℂ))) 2 0
      = 1 - Complex.I := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    simp only [Matrix.vecMulVec_apply, Pi.star_apply,
      Complex.star_def]
    rw [Complex.ofReal_mul, Complex.ofReal_mul,
      ← Complex.mul_conj, ← Complex.mul_conj,
      ← Complex.mul_conj]
    ring
  · exact (vecMulVec_psd _).add (vecMulVec_psd _)
  · intro c d h
    have h2 : c = 0 := by
      have h' := congrFun h 2
      simpa using h'
    refine ⟨h2, ?_⟩
    have h1 : c + d * Complex.I = 0 := by
      have h' := congrFun h 1
      simpa using h'
    rw [h2, zero_add] at h1
    rcases mul_eq_zero.mp h1 with hd | hI
    · exact hd
    · exact absurd hI Complex.I_ne_zero
  · rw [show (Matrix.vecMulVec (![1, 1, 1] : Fin 3 → ℂ)
          (star (![1, 1, 1] : Fin 3 → ℂ))
        + Matrix.vecMulVec (![1, Complex.I, 0] : Fin 3 → ℂ)
            (star (![1, Complex.I, 0] : Fin 3 → ℂ))) 0 1
        = 1 - Complex.I from by
      rw [Matrix.add_apply, Matrix.vecMulVec_apply,
        Matrix.vecMulVec_apply]
      simp [Pi.star_apply, Complex.star_def, Complex.conj_I]
      try ring]
    rw [show (Matrix.vecMulVec (![1, 1, 1] : Fin 3 → ℂ)
          (star (![1, 1, 1] : Fin 3 → ℂ))
        + Matrix.vecMulVec (![1, Complex.I, 0] : Fin 3 → ℂ)
            (star (![1, Complex.I, 0] : Fin 3 → ℂ))) 1 2
        = 1 from by
      rw [Matrix.add_apply, Matrix.vecMulVec_apply,
        Matrix.vecMulVec_apply]
      simp [Pi.star_apply, Complex.star_def, Complex.conj_I]]
    rw [show (Matrix.vecMulVec (![1, 1, 1] : Fin 3 → ℂ)
          (star (![1, 1, 1] : Fin 3 → ℂ))
        + Matrix.vecMulVec (![1, Complex.I, 0] : Fin 3 → ℂ)
            (star (![1, Complex.I, 0] : Fin 3 → ℂ))) 2 0
        = 1 from by
      rw [Matrix.add_apply, Matrix.vecMulVec_apply,
        Matrix.vecMulVec_apply]
      simp [Pi.star_apply, Complex.star_def, Complex.conj_I]]
    ring

end NCG
