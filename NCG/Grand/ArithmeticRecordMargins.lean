/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RecordChain

/-!
# arithmetic record margins
-/

open Matrix

namespace NCG

/-- Projection onto the first `n` chronological record lines. -/
noncomputable def recPrefix (X n : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < n then 1 else 0

/-- Projection onto one chronological record line. -/
def recPoint {X : ℕ} (i : Fin X) : Matrix (Fin X) (Fin X) ℂ :=
  Matrix.single i i 1

theorem rec_prefix_kills_backflow {X : ℕ} (i : Fin X)
    (hi : (i : ℕ) + 1 < X) :
    recPrefix X ((i : ℕ) + 1) * recS X * recPoint i = 0 := by
  let s : Fin X := ⟨(i : ℕ) + 1, hi⟩
  have hshift : recS X * recPoint i = Matrix.single s i 1 := by
    change recS X * Matrix.single i i 1 = Matrix.single s i 1
    ext a b
    by_cases hb : b = i
    · subst b
      rw [Matrix.mul_single_apply_same]
      by_cases ha : a = s
      · subst a
        simp [recS, recPoint, s]
      · rw [Matrix.single_apply, if_neg]
        · rw [recS, Matrix.of_apply, if_neg (by
            intro hval
            exact ha (Fin.ext hval))]
          simp
        · intro h
          exact ha h.1.symm
    · rw [Matrix.mul_single_apply_of_ne (1 : ℂ) i i a b hb (recS X)]
      rw [Matrix.single_apply, if_neg]
      intro h
      exact hb h.2.symm
  rw [Matrix.mul_assoc, hshift]
  ext a b
  by_cases hb : b = i
  · subst b
    rw [Matrix.mul_single_apply_same]
    rw [recPrefix, Matrix.diagonal_apply]
    by_cases ha : a = s
    · subst a
      simp [s]
    · simp [ha]
  · rw [Matrix.mul_single_apply_of_ne (1 : ℂ) s i a b hb
      (recPrefix X ((i : ℕ) + 1))]
    rfl

theorem rec_terminal_has_zero_future {X : ℕ} (i : Fin X)
    (hi : (i : ℕ) + 1 = X) :
    recS X * recPoint i = 0 := by
  change recS X * Matrix.single i i 1 = 0
  ext a b
  by_cases hb : b = i
  · subst b
    rw [Matrix.mul_single_apply_same]
    rw [recS, Matrix.of_apply, if_neg (by
      intro hval
      exact (Nat.ne_of_lt a.isLt) (hval.trans hi))]
    simp
  · rw [Matrix.mul_single_apply_of_ne (1 : ℂ) i i a b hb (recS X)]
    rfl

/-- The manuscript's Hilbert--Schmidt backflow residual. -/
noncomputable def recBackflow (X : ℕ) : ℝ :=
  ∑ i : Fin X,
    if h : (i : ℕ) + 1 < X then
      (Matrix.trace ((recPrefix X ((i : ℕ) + 1) * recS X * recPoint i)ᴴ
        * (recPrefix X ((i : ℕ) + 1) * recS X * recPoint i))).re
    else (Matrix.trace ((recS X * recPoint i)ᴴ
      * (recS X * recPoint i))).re

theorem rec_backflow_zero (X : ℕ) : recBackflow X = 0 := by
  classical
  rw [recBackflow]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · rw [rec_prefix_kills_backflow i hi]
    simp
  · have hlast : (i : ℕ) + 1 = X := by omega
    rw [rec_terminal_has_zero_future i hlast]
    simp

/-- `thm:ar-record-margins`, with all displayed finite identities:
identity chronology/Read Gram, zero backflow, and identity endpoint
source Gram. -/
theorem arithmetic_record_margins_exact (X : ℕ) (hX : 1 ≤ X) :
    (∀ i j : Fin X,
      star (Pi.single i (1 : ℂ)) ⬝ᵥ
        ((recS X) ^ (j : ℕ) *ᵥ
          Pi.single (⟨0, by omega⟩ : Fin X) 1)
        = if i = j then 1 else 0)
    ∧ recBackflow X = 0
    ∧ (1 : Matrix (Fin X) (Fin X) ℂ)ᴴ * 1 = 1 := by
  refine ⟨record_margins hX, rec_backflow_zero X, ?_⟩
  rw [Matrix.conjTranspose_one, Matrix.one_mul]

end NCG
