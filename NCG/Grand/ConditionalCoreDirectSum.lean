/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConditionalCoreMinimality

/-!
# Direct-sum record-conditioned predictive core

This supplies the finite direct-sum packaging and intervention-moment clauses
of `thm:conditional-core-minimality`.  Protected record sectors are explicit
in the row and column indices, so the assembled gauge cannot mix them.
-/

open Matrix

namespace NCG

/-- Finite record-indexed block diagonal matrix. -/
def recordBlockDiagonal {R a b : Type} [DecidableEq R]
    (A : R → Matrix a b ℂ) : Matrix (R × a) (R × b) ℂ :=
  fun ri sj => if ri.1 = sj.1 then A ri.1 ri.2 sj.2 else 0

theorem recordBlockDiagonal_mul {R a b c : Type}
    [Fintype R] [Fintype b] [DecidableEq R]
    (A : R → Matrix a b ℂ) (B : R → Matrix b c ℂ) :
    recordBlockDiagonal A * recordBlockDiagonal B =
      recordBlockDiagonal (fun r => A r * B r) := by
  classical
  ext ⟨r, i⟩ ⟨s, k⟩
  by_cases hrs : r = s
  · subst s
    simp [recordBlockDiagonal, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [recordBlockDiagonal, Matrix.mul_apply, Fintype.sum_prod_type, hrs]

theorem recordBlockDiagonal_conjTranspose {R a b : Type}
    [DecidableEq R]
    (A : R → Matrix a b ℂ) :
    (recordBlockDiagonal A)ᴴ =
      recordBlockDiagonal (fun r => (A r)ᴴ) := by
  ext ⟨r, i⟩ ⟨s, j⟩
  by_cases hrs : r = s
  · subst s
    simp [recordBlockDiagonal, Matrix.conjTranspose_apply]
  · simp [recordBlockDiagonal, Matrix.conjTranspose_apply, hrs, Ne.symm hrs]

theorem recordBlockDiagonal_pow {R a : Type}
    [Fintype R] [Fintype a] [DecidableEq R] [DecidableEq a]
    (A : R → Matrix a a ℂ) (n : ℕ) :
    recordBlockDiagonal A ^ n =
      recordBlockDiagonal (fun r => A r ^ n) := by
  induction n with
  | zero =>
      ext ⟨r, i⟩ ⟨s, j⟩
      by_cases hrs : r = s
      · subst s
        simp [recordBlockDiagonal, Matrix.one_apply, Prod.ext_iff]
      · simp [recordBlockDiagonal, Matrix.one_apply, Prod.ext_iff, hrs]
  | succ n ih =>
      rw [pow_succ, ih, recordBlockDiagonal_mul]
      apply congrArg recordBlockDiagonal
      funext r
      rw [pow_succ]

/-- The intervention moment table of the explicit record-direct-sum core is
the block diagonal of the sector moment tables.  Cross-record blocks vanish. -/
theorem record_direct_sum_moment {R u p : Type}
    [Fintype R] [Fintype u] [Fintype p]
    [DecidableEq R] [DecidableEq u] [DecidableEq p]
    (G : R → Matrix u u ℂ) (B : R → Matrix u p ℂ) (n : ℕ) :
    (recordBlockDiagonal B)ᴴ *
        (recordBlockDiagonal G) ^ n * recordBlockDiagonal B =
      recordBlockDiagonal (fun r => (B r)ᴴ * G r ^ n * B r) := by
  rw [recordBlockDiagonal_conjTranspose, recordBlockDiagonal_pow,
    recordBlockDiagonal_mul, recordBlockDiagonal_mul]

/-- The exact finite record-conditioned core: all intervention probabilities
(all moments) are preserved, every protected sector has its unique minimal
gauge, and the assembled gauge is block diagonal in the record value. -/
theorem conditional_core_direct_sum_exact {R u p : Type}
    [Fintype R] [Fintype u] [Fintype p]
    [DecidableEq R] [DecidableEq u] [DecidableEq p]
    (G G' : R → Matrix u u ℂ) (B B' : R → Matrix u p ℂ)
    (hG : ∀ r, (G r)ᴴ = G r) (hG' : ∀ r, (G' r)ᴴ = G' r)
    (d : ℕ) (hd : 0 < d)
    (hmin : ∀ r,
      Function.Surjective (krylovMat (G r) (B r) d).mulVec)
    (hmom : ∀ r (n : ℕ), (B r)ᴴ * (G r) ^ n * (B r)
        = (B' r)ᴴ * (G' r) ^ n * (B' r)) :
    (∀ n,
      (recordBlockDiagonal B)ᴴ *
          (recordBlockDiagonal G) ^ n * recordBlockDiagonal B =
        (recordBlockDiagonal B')ᴴ *
          (recordBlockDiagonal G') ^ n * recordBlockDiagonal B')
    ∧ (∃ W : R → Matrix u u ℂ,
        (∀ r, W r * krylovMat (G r) (B r) d =
          krylovMat (G' r) (B' r) d)
        ∧ (∀ W' : R → Matrix u u ℂ,
          (∀ r, W' r * krylovMat (G r) (B r) d =
            krylovMat (G' r) (B' r) d) → W' = W)
        ∧ ∀ r s i j, r ≠ s →
          recordBlockDiagonal W (r, i) (s, j) = 0) := by
  constructor
  · intro n
    rw [record_direct_sum_moment, record_direct_sum_moment]
    apply congrArg recordBlockDiagonal
    funext r
    exact hmom r n
  · have hsector := conditional_core_minimality
      G G' B B' hG hG' d hd hmin hmom
    let W : R → Matrix u u ℂ := fun r => (hsector r).choose
    have hW : ∀ r, W r * krylovMat (G r) (B r) d =
        krylovMat (G' r) (B' r) d := fun r => (hsector r).choose_spec.1
    refine ⟨W, hW, ?_, ?_⟩
    · intro W' hW'
      funext r
      exact (hsector r).choose_spec.2 (W' r) (hW' r)
    · intro r s i j hrs
      simp [recordBlockDiagonal, hrs]

end NCG
