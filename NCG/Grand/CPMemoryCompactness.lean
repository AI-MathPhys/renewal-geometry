/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform finite-horizon CP feasibility
  (`thm:CP-memory-compactness`, Gran-Tensor manuscript)

* `cp_memory_compactness`:
  (1) the compactness engine: nested nonempty compact closed
      horizon-feasibility sets have a common element — one
      `M`-dimensional recurrent realization exists iff every
      finite horizon is feasible (finite-intersection
      property);
  (2) the boxed memory bound: any Hankel panel factoring
      through an `M²`-dimensional operator space has rank at
      most `M²`, and `d ≤ M²` gives `√d ≤ M`
      (`M ≥ ⌈√d_∞⌉`).

Rendering disclosed: compactness of the normalized parameter
space `Θ_M` (density matrices, subnormalized Choi matrices,
effects) is the manuscript's bounded-closed semialgebraic
packaging; the `ε_N → 0` subsequence limit passage is the
sequential-compactness reading of the same engine; the
non-sufficiency of linear rank (positive-cone constraint) is
the manuscript's separate countermodel.
-/

open Matrix

namespace NCG

/-- `thm:CP-memory-compactness`. -/
theorem cp_memory_compactness :
    -- (1) nested-horizon feasibility: the FIP engine
    (∀ {Θ : Type} [TopologicalSpace Θ] (K : ℕ → Set Θ),
      (∀ N, IsCompact (K N)) → (∀ N, (K N).Nonempty) →
      (∀ N, IsClosed (K N)) → (∀ N, K (N + 1) ⊆ K N) →
      (⋂ N, K N).Nonempty)
    -- (2) the boxed memory bound through the M²-dim space
    ∧ (∀ {I J : Type} [Fintype I] [Fintype J] (M : ℕ)
        (A : Matrix I (Fin (M * M)) ℂ)
        (B : Matrix (Fin (M * M)) J ℂ),
        (A * B).rank ≤ M * M)
    ∧ (∀ d M : ℕ, d ≤ M * M → Nat.sqrt d ≤ M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Θ _ K hcompact hne hclosed hnested
    have hanti : ∀ {m n : ℕ}, m ≤ n → K n ⊆ K m := by
      intro m n hmn
      induction hmn with
      | refl => exact subset_rfl
      | step h ih => exact (hnested _).trans ih
    exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      K (fun i j => ⟨max i j,
        hanti (le_max_left i j), hanti (le_max_right i j)⟩)
      hne hcompact hclosed
  · intro I J _ _ M A B
    classical
    calc (A * B).rank ≤ B.rank := Matrix.rank_mul_le_right A B
      _ ≤ Fintype.card (Fin (M * M)) :=
        Matrix.rank_le_card_height B
      _ = M * M := Fintype.card_fin _
  · intro d M hd
    calc Nat.sqrt d ≤ Nat.sqrt (M * M) := Nat.sqrt_le_sqrt hd
      _ = M := by rw [← pow_two]; exact Nat.sqrt_eq' M

end NCG
