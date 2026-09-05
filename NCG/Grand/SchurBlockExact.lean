/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Hard-range Schur complement of a block localizer

Machinery for `thm:SM-localizer-jets` (RG.3f).  On the block space `m ⊕ n` with the kernel
projection `P = fromBlocks 1 0 0 0` and hard-range projection `Q = fromBlocks 0 0 0 1`, the
exact localizer induced on the constant kernel of a matrix `L` is
`𝒮(L) = P L P - P L Q [P + Q L Q]⁻¹ Q L P`, where `[P + Q L Q]⁻¹` is the ring inverse of the unit
`P + Q L Q` (it acts as `(Q L Q)⁻¹` on the hard range).  For a block matrix
`L = fromBlocks A B Bᴴ D` with `D ≻ 0` this is `fromBlocks (A - B D⁻¹ Bᴴ) 0 0 0`, the classical
Schur complement placed on the kernel block (`schur_fromBlocks`), and it is positive
semidefinite whenever `L` is (`schur_posSemidef`).
-/

open Matrix

namespace NCG
namespace SchurBlock

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The block matrix space. -/
abbrev M (m n : Type*) := Matrix (m ⊕ n) (m ⊕ n) ℝ

/-- The kernel projection `P = fromBlocks 1 0 0 0`. -/
def P : M m n := fromBlocks 1 0 0 0

/-- The hard-range projection `Q = fromBlocks 0 0 0 1`. -/
def Q : M m n := fromBlocks 0 0 0 1

omit [Fintype m] [Fintype n] in
theorem P_add_Q : (P : M m n) + Q = 1 := by
  rw [P, Q, fromBlocks_add, ← fromBlocks_one]
  simp

omit [DecidableEq n] in
theorem P_mul_P : (P : M m n) * P = P := by simp [P, fromBlocks_multiply]

omit [DecidableEq m] in
theorem Q_mul_Q : (Q : M m n) * Q = Q := by simp [Q, fromBlocks_multiply]

theorem P_mul_Q : (P : M m n) * Q = 0 := by simp [P, Q, fromBlocks_multiply]

theorem Q_mul_P : (Q : M m n) * P = 0 := by simp [P, Q, fromBlocks_multiply]

omit [Fintype m] [Fintype n] [DecidableEq n] in
theorem P_conjTranspose : (P : M m n)ᴴ = P := by simp [P, fromBlocks_transpose]

omit [Fintype m] [Fintype n] [DecidableEq m] in
theorem Q_conjTranspose : (Q : M m n)ᴴ = Q := by simp [Q, fromBlocks_transpose]

/-- The hard-range inverse `[P + Q L Q]⁻¹`. -/
noncomputable def hardInv (L : M m n) : M m n := Ring.inverse (P + Q * L * Q)

/-- (RG.3f) the exact localizer induced on the constant kernel
`𝒮(L) = P L P - P L Q [P + Q L Q]⁻¹ Q L P`. -/
noncomputable def schur (L : M m n) : M m n :=
  P * L * P - P * L * Q * hardInv L * Q * L * P

/-! ### Block identification -/

variable (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)

omit [DecidableEq n] in
theorem P_mul_fromBlocks_mul_P : P * fromBlocks A B C D * P = fromBlocks A 0 0 0 := by
  simp [P, fromBlocks_multiply]

omit [DecidableEq m] in
theorem Q_mul_fromBlocks_mul_Q : Q * fromBlocks A B C D * Q = fromBlocks 0 0 0 D := by
  simp [Q, fromBlocks_multiply]

theorem P_mul_fromBlocks_mul_Q : P * fromBlocks A B C D * Q = fromBlocks 0 B 0 0 := by
  simp [P, Q, fromBlocks_multiply]

theorem Q_mul_fromBlocks_mul_P : Q * fromBlocks A B C D * P = fromBlocks 0 0 C 0 := by
  simp [P, Q, fromBlocks_multiply]

theorem P_add_Q_mul_fromBlocks_mul_Q :
    P + Q * fromBlocks A B C D * Q = fromBlocks 1 0 0 D := by
  rw [Q_mul_fromBlocks_mul_Q, P, fromBlocks_add]
  simp

theorem hardInv_fromBlocks (hD : IsUnit D) :
    hardInv (fromBlocks A B C D) = fromBlocks 1 0 0 D⁻¹ := by
  rw [hardInv, P_add_Q_mul_fromBlocks_mul_Q, ← Matrix.nonsing_inv_eq_ringInverse,
    inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (by simp [hD])]
  simp

/-- The induced localizer of a block matrix is the Schur complement on the kernel block. -/
theorem schur_fromBlocks (hD : IsUnit D) :
    schur (fromBlocks A B C D) = fromBlocks (A - B * D⁻¹ * C) 0 0 0 := by
  rw [schur, hardInv_fromBlocks A B C D hD]
  simp only [P, Q, fromBlocks_multiply]
  rw [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

/-! ### (RG.3f): positivity -/

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- A matrix supported on the kernel block is positive semidefinite iff its block is. -/
theorem posSemidef_fromBlocks_zero [Finite m] [Finite n] {S : Matrix m m ℝ} (hS : S.PosSemidef) :
    (fromBlocks S 0 0 0 : M m n).PosSemidef := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, fromBlocks_conjTranspose, hS.1]
    simp
  · obtain ⟨x₁, x₂, rfl⟩ : ∃ x₁ x₂, x = Sum.elim x₁ x₂ := ⟨_, _, (Sum.elim_comp_inl_inr x).symm⟩
    have hdot : ∀ (u w : m → ℝ) (v z : n → ℝ),
        Sum.elim u v ⬝ᵥ Sum.elim w z = u ⬝ᵥ w + v ⬝ᵥ z := by
      intro u w v z
      simp [dotProduct, Fintype.sum_sum_type]
    rw [fromBlocks_mulVec, star_trivial]
    simp only [zero_mulVec, add_zero, hdot, dotProduct_zero]
    have := hS.dotProduct_mulVec_nonneg x₁
    simpa using this

/-- **(RG.3f)**: for a positive block localizer with positive definite hard block, the induced
kernel localizer is positive semidefinite. -/
theorem schur_posSemidef (hL : (fromBlocks A B Bᴴ D).PosSemidef) (hD : D.PosDef) :
    (schur (fromBlocks A B Bᴴ D)).PosSemidef := by
  haveI : Invertible D := Matrix.invertibleOfIsUnitDet D hD.det_pos.ne'.isUnit
  have hDu : IsUnit D := (isUnit_iff_isUnit_det D).mpr hD.det_pos.ne'.isUnit
  rw [schur_fromBlocks A B Bᴴ D hDu]
  exact posSemidef_fromBlocks_zero ((PosDef.fromBlocks₂₂ A B hD).mp hL)

end SchurBlock
end NCG
