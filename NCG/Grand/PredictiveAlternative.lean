/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite/infinite predictive alternative
  (`thm:predictive-alternative`, Gran-Tensor manuscript)

* `predictive_alternative`: every finite submatrix of the word
  table has rank at most the rank of any exhaustive panel
  containing it (so `d_∞ = sup d_n`); bounded nondecreasing
  panel ranks stabilize; and every `d`-dimensional
  reachable/observable factorization bounds every panel rank by
  `d` — so infinite Hankel rank excludes every
  finite-dimensional linear predictor.

Rendering disclosed: the unique global `d`-dimensional
realization on the stabilized branch is
`thm:typed-hankel-realization`/`thm:hankel-minimality` (proved);
the "no finite panel forecloses later innovations" clause is
the manuscript's growing-tensor witness (the growing-ledger
mechanism proved in
`corollary:finite-recurrent-core-versus-growing-ledger`).
-/

open Matrix

namespace NCG

/-- `thm:predictive-alternative`. -/
theorem predictive_alternative :
    -- (1) submatrix ranks are dominated by panel ranks
    (∀ {m n m₀ n₀ : Type} [Fintype n] [Fintype n₀]
      (A : Matrix m n ℝ) (r : m₀ → m) (c : n₀ → n),
      (A.submatrix r c).rank ≤ A.rank)
    -- (2) bounded nondecreasing panel ranks stabilize
    ∧ (∀ (d : ℕ → ℕ) (K : ℕ), Monotone d → (∀ n, d n ≤ K) →
        ∃ N, ∀ n, N ≤ n → d n = d N)
    -- (3) every d-dimensional realization bounds all panel
    --     ranks by d
    ∧ (∀ {m n : Type} [Fintype m] [Fintype n] (dd : ℕ)
        (C : Matrix m (Fin dd) ℝ) (O : Matrix (Fin dd) n ℝ),
        (C * O).rank ≤ dd) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n m₀ n₀ _ _ A r c
    exact Matrix.rank_submatrix_le A r c
  · intro d K hmono hbound
    by_contra h
    push Not at h
    have key : ∀ k, ∃ n, k ≤ d n := by
      intro k
      induction k with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ k ihk =>
          obtain ⟨n, hn⟩ := ihk
          obtain ⟨m, hm, hne⟩ := h n
          have hmn := hmono hm
          exact ⟨m, by omega⟩
    obtain ⟨n, hn⟩ := key (K + 1)
    exact absurd (hbound n) (by omega)
  · intro m n _ _ dd C O
    calc (C * O).rank ≤ C.rank := Matrix.rank_mul_le_left C O
      _ ≤ Fintype.card (Fin dd) := Matrix.rank_le_card_width C
      _ = dd := Fintype.card_fin dd

end NCG
