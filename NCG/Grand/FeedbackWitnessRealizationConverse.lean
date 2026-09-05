/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TemporalTailRankWitnesses

/-!
# Hankel realization converse for feedback witnesses

The finite Hankel realization theorem identifies an `M`-coordinate recurrent
memory with a uniform rank bound `rank H_n ≤ M`.  This file records the exact
logical converse needed by `thm:feedback-witnesses`: failure of that bound is
witnessed by one finite block with positive singular value number `M + 1`.
-/

open Matrix

namespace NCG

set_option maxHeartbeats 800000

/-- Exact finite-Hankel meaning of representability by at most `M` recurrent
coordinates. -/
def RepresentsFeedbackWithMemoryDimension
    {p q : Type} [Fintype p] [Fintype q]
    (H : ℕ → Matrix p q ℂ) (M : ℕ) : Prop :=
  ∀ n, (H n).rank ≤ M

/-- If no `M`-coordinate memory represents the family, one finite Hankel
block has a positive `(M+1)`st singular value (zero-indexed as `M`). -/
theorem feedback_rank_growth_witness_of_no_memory
    {p q : Type} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (H : ℕ → Matrix p q ℂ) (M : ℕ)
    (hno : ¬ RepresentsFeedbackWithMemoryDimension H M) :
    ∃ n, 0 < (H n).toEuclideanLin.singularValues M := by
  rw [RepresentsFeedbackWithMemoryDimension] at hno
  push Not at hno
  obtain ⟨n, hn⟩ := hno
  refine ⟨n, (matrix_singularValue_pos_iff_rank_gt (p := p) (q := q) (H n) M).2 ?_⟩
  omega

/-- Conversely, a positive singular-value witness excludes every uniform
`M`-coordinate realization of the family. -/
theorem feedback_rank_growth_witness_excludes_memory
    {p q : Type} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (H : ℕ → Matrix p q ℂ) (M n : ℕ)
    (hw : 0 < (H n).toEuclideanLin.singularValues M) :
    ¬ RepresentsFeedbackWithMemoryDimension H M := by
  intro hmem
  have hrank := (matrix_singularValue_pos_iff_rank_gt (p := p) (q := q) (H n) M).1 hw
  exact (Nat.not_lt_of_ge (hmem n)) hrank

/-- Exact iff form of the realization converse. -/
theorem no_feedback_memory_iff_positive_singular_witness
    {p q : Type} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (H : ℕ → Matrix p q ℂ) (M : ℕ) :
    ¬ RepresentsFeedbackWithMemoryDimension H M ↔
      ∃ n, 0 < (H n).toEuclideanLin.singularValues M := by
  constructor
  · exact feedback_rank_growth_witness_of_no_memory H M
  · rintro ⟨n, hn⟩
    exact feedback_rank_growth_witness_excludes_memory H M n hn

end NCG
