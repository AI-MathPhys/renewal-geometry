/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.OccurrenceMarginals

/-!
# Exact EASY 48: occurrence environment rank

The spectral rank formula is upgraded here to a source-minimal Gram
factorization statement.  For a zero/one occurrence effect, the canonical
environment is the support of the full `1 + 15` diagonal source Gram.  Its
coordinate synthesis realizes the Gram, has exactly the displayed dimension,
and every other finite synthesis has at least that many rows.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {q : Type*} [Fintype q] [DecidableEq q]

/-- Coordinate synthesis indexed by the nonzero support of a diagonal Gram. -/
def diagonalSupportSynthesis (g : q -> Complex) :
    Matrix {i : q // g i ≠ 0} q Complex :=
  fun e j => if e.1 = j then 1 else 0

theorem diagonalSupportSynthesis_gram (g : q -> Complex)
    (hg : ∀ i, g i = 0 ∨ g i = 1) :
    (diagonalSupportSynthesis g)ᴴ * diagonalSupportSynthesis g
      = Matrix.diagonal g := by
  classical
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.conjTranspose_apply, diagonalSupportSynthesis]
  by_cases hij : i = j
  · subst j
    rcases hg i with hi | hi
    · rw [if_pos rfl, hi]
      apply Finset.sum_eq_zero
      intro e _
      by_cases hei : e.1 = i
      · exact False.elim (e.2 (hei.symm ▸ hi))
      · simp [hei]
    · have hne : g i ≠ 0 := by simp [hi]
      rw [if_pos rfl]
      rw [Finset.sum_eq_single (⟨i, hne⟩ : {x : q // g x ≠ 0})]
      · simp [hi]
      · intro e _ he
        have hval : e.1 ≠ i := by
          intro h
          apply he
          exact Subtype.ext h
        simp [hval]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro e _
    by_cases hei : e.1 = i
    · by_cases hej : e.1 = j
      · exact False.elim (hij (hei.symm.trans hej))
      · simp [hei, hij]
    · simp [hei]

/-- The full occurrence weight: one copy of the selected effect and fifteen
copies of its complement. -/
def occurrenceFullWeight {n : Type*} (d : n -> Complex) :
    n ⊕ (Fin 15 × n) -> Complex
  | Sum.inl i => d i
  | Sum.inr ki => 1 - d ki.2

theorem occurrenceFullGram_rank {n : Type*} [Fintype n] [DecidableEq n]
    (d : n -> Complex) :
    (Matrix.diagonal (occurrenceFullWeight d)).rank
      = (Matrix.diagonal d).rank
        + 15 * (Matrix.diagonal fun i => 1 - d i).rank := by
  classical
  rw [Matrix.rank_diagonal, Matrix.rank_diagonal, Matrix.rank_diagonal]
  let eright :
      {x : Fin 15 × n // (1 : Complex) - d x.2 ≠ 0}
        ≃ Fin 15 × {i : n // (1 : Complex) - d i ≠ 0} := {
    toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
    invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  calc
    Fintype.card {x : n ⊕ (Fin 15 × n) // occurrenceFullWeight d x ≠ 0}
        = Fintype.card ({i : n // d i ≠ 0} ⊕
            {x : Fin 15 × n // (1 : Complex) - d x.2 ≠ 0}) := by
              exact Fintype.card_congr
                (Equiv.subtypeSum
                  (p := fun x => occurrenceFullWeight d x ≠ 0))
    _ = Fintype.card {i : n // d i ≠ 0}
          + Fintype.card {x : Fin 15 × n //
              (1 : Complex) - d x.2 ≠ 0} := Fintype.card_sum
    _ = Fintype.card {i : n // d i ≠ 0}
          + Fintype.card (Fin 15 ×
              {i : n // (1 : Complex) - d i ≠ 0}) := by
                rw [Fintype.card_congr eright]
    _ = Fintype.card {i : n // d i ≠ 0}
          + 15 * Fintype.card {i : n //
              (1 : Complex) - d i ≠ 0} := by simp

/-- Exact source-minimality of the occurrence environment.  The existential
synthesis attains the displayed rank, and the universal clause proves that no
finite Gram realization can have a smaller environment carrier. -/
theorem occurrence_environment_rank_source_minimal
    {n : Type*} [Fintype n] [DecidableEq n]
    (d : n -> Complex) (hd : ∀ i, d i = 0 ∨ d i = 1) :
    let g := occurrenceFullWeight d
    ∃ W : Matrix {x : n ⊕ (Fin 15 × n) // g x ≠ 0}
        (n ⊕ (Fin 15 × n)) Complex,
      Wᴴ * W = Matrix.diagonal g
      ∧ Fintype.card {x : n ⊕ (Fin 15 × n) // g x ≠ 0}
        = (Matrix.diagonal d).rank
          + 15 * (Matrix.diagonal fun i => 1 - d i).rank
      ∧ ∀ {e : Type*} [Fintype e]
          (W' : Matrix e (n ⊕ (Fin 15 × n)) Complex),
          W'ᴴ * W' = Matrix.diagonal g ->
          (Matrix.diagonal d).rank
              + 15 * (Matrix.diagonal fun i => 1 - d i).rank
            ≤ Fintype.card e := by
  dsimp only
  let g := occurrenceFullWeight d
  have hg : ∀ x, g x = 0 ∨ g x = 1 := by
    intro x
    cases x with
    | inl i => exact hd i
    | inr ki =>
        rcases hd ki.2 with hi | hi
        · right
          simp [g, occurrenceFullWeight, hi]
        · left
          simp [g, occurrenceFullWeight, hi]
  refine ⟨diagonalSupportSynthesis g,
    diagonalSupportSynthesis_gram g hg, ?_, ?_⟩
  · rw [← Matrix.rank_diagonal]
    exact occurrenceFullGram_rank d
  · intro e _ W' hW'
    calc
      (Matrix.diagonal d).rank
            + 15 * (Matrix.diagonal fun i => 1 - d i).rank
          = (Matrix.diagonal g).rank :=
              (occurrenceFullGram_rank d).symm
      _ = W'.rank := by
            rw [← hW', Matrix.rank_conjTranspose_mul_self]
      _ ≤ Fintype.card e := Matrix.rank_le_card_height W'

end NCG
