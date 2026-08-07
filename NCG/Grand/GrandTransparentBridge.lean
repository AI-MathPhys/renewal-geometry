/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The universal grading bridge is transparent
  (`cor:SM-K4-transparent`, Gran-Tensor manuscript)

* `k4_transparent`: tensoring a flavour source with an
  isometric grading bridge (`B*B = 1`) leaves every normalized
  Krylov moment unchanged —
  `(S⊗B)*(T⊗1)^k(S⊗B) = (S*T^kS) ⊗ 1` — so all moment-derived
  data (saturation ranks, transfer-intertwining residuals, and
  the source-whitened `K₄` cycle–flavour comparison) coincide
  with the unbridged ones tensored by the identity: the bridge
  can neither prove three generations nor repair a failed
  cycle–flavour comparison.

Rendering disclosed: the Gram case is `k = 0`; the rank and
comparison invariance are read off the displayed moment
identity blockwise.
-/

open Matrix Kronecker

namespace NCG

/-- `cor:SM-K4-transparent`: bridged Krylov moments factor
through the unbridged ones. -/
theorem k4_transparent {n p g g' : Type*} [Fintype n]
    [Fintype g] [DecidableEq n]
    [DecidableEq g] [DecidableEq g']
    (T : Matrix n n ℂ) (S : Matrix n p ℂ)
    (B : Matrix g g' ℂ) (hB : Bᴴ * B = 1) (k : ℕ) :
    (S ⊗ₖ B)ᴴ * ((T ⊗ₖ (1 : Matrix g g ℂ)) ^ k) * (S ⊗ₖ B)
      = (Sᴴ * T ^ k * S) ⊗ₖ (1 : Matrix g' g' ℂ) := by
  have hpow : (T ⊗ₖ (1 : Matrix g g ℂ)) ^ k
      = (T ^ k) ⊗ₖ (1 : Matrix g g ℂ) := by
    induction k with
    | zero =>
      rw [pow_zero, pow_zero, Matrix.one_kronecker_one]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul]
  rw [hpow, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    ← Matrix.mul_kronecker_mul, hB]

end NCG
