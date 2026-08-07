/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical controlled-history compiler
  (`thm:canonical-history-compiler`, Gran-Tensor manuscript)

* `path_projection_idempotent`: the path projection
  `p₁ = ½(1 - Z)` of a sign observable `Z² = 1` is idempotent —
  the control register carries a genuine two-valued path label;
* `controlled_lift_unitary`: every reversible primitive unitary
  has an exact one-sided controlled lift — the block lift
  `diag(1, U)` is unitary whenever `U` is;
* `controlled_letters_multiply`: controlled reversible letters
  multiply to controlled words —
  `Λ(U)·Λ(V) = Λ(UV)` for `Λ(U) = P ⊗ U + (1-P) ⊗ 1` with any
  idempotent control `P`;
* `controlled_word_power`: iterated letters compile to the
  controlled word `Λ(U)ᵏ = Λ(Uᵏ)`.

Rendering disclosed: the joint-Lie-algebra generation statement
(`iZ_ε ⊗ 𝔰𝔲(d)` and `ip₁^ε ⊗ 𝔰𝔲(d)` inside the generated
algebra) and the derived CP completion of a finite irreversible
alphabet are the manuscript's Lie-theoretic layer; the exact
controlled-lift algebra proved here is the compiler's
multiplication table.
-/

open Matrix Kronecker

namespace NCG

variable {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

/-- The path projection `p₁ = ½(1 - Z)` of a sign observable is
idempotent. -/
theorem path_projection_idempotent (Z : Matrix n n ℂ)
    (hZ : Z * Z = 1) :
    ((2 : ℂ)⁻¹ • (1 - Z)) * ((2 : ℂ)⁻¹ • (1 - Z))
      = (2 : ℂ)⁻¹ • (1 - Z) := by
  have hsq : (1 - Z) * (1 - Z) = (2 : ℂ) • (1 - Z) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hZ, two_smul]
    abel
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq,
    smul_smul]
  norm_num

/-- One-sided controlled lift: `diag(1, U)` is unitary whenever
`U` is. -/
theorem controlled_lift_unitary (U : Matrix m m ℂ)
    (hU : Uᴴ * U = 1) :
    (Matrix.fromBlocks (1 : Matrix n n ℂ) 0 0 U)ᴴ
      * Matrix.fromBlocks (1 : Matrix n n ℂ) 0 0 U = 1 := by
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hU, ← Matrix.fromBlocks_one]

/-- Controlled reversible letters multiply to controlled words:
`Λ(U)·Λ(V) = Λ(UV)` for `Λ(U) = P ⊗ U + (1-P) ⊗ 1`. -/
theorem controlled_letters_multiply (P : Matrix n n ℂ)
    (hP : P * P = P) (U V : Matrix m m ℂ) :
    (P ⊗ₖ U + (1 - P) ⊗ₖ (1 : Matrix m m ℂ))
        * (P ⊗ₖ V + (1 - P) ⊗ₖ (1 : Matrix m m ℂ))
      = P ⊗ₖ (U * V) + (1 - P) ⊗ₖ (1 : Matrix m m ℂ) := by
  have hPQ : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
  have hQP : (1 - P) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP]
    abel
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hP, hPQ, hQP, hQQ, Matrix.mul_one, Matrix.one_mul]
  simp

/-- Iterated controlled letters compile to the controlled word:
`Λ(U)ᵏ = Λ(Uᵏ)`. -/
theorem controlled_word_power (P : Matrix n n ℂ)
    (hP : P * P = P) (U : Matrix m m ℂ) (k : ℕ) :
    (P ⊗ₖ U + (1 - P) ⊗ₖ (1 : Matrix m m ℂ)) ^ k
      = P ⊗ₖ (U ^ k) + (1 - P) ⊗ₖ (1 : Matrix m m ℂ) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, ← Matrix.add_kronecker,
      add_sub_cancel, Matrix.one_kronecker_one]
  | succ k ih =>
    rw [pow_succ, ih,
      controlled_letters_multiply P hP (U ^ k) U, ← pow_succ]

end NCG
