/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PrefixSupportMemory

/-!
# Finite recurrent core versus growing ledger
  (`corollary:finite-recurrent-core-versus-growing-ledger`,
   Gran-Tensor manuscript)

* `finite_core_vs_growing_ledger`: the iid fair-bit process has
  a one-state recurrent core (every fixed-horizon panel has rank
  at most one), yet for every bound `K` there is a horizon `N`
  at which any faithful carrier of the complete protected
  cylinder (any purification of the `N`-output cylinder density)
  needs dimension exceeding `K` — finite recurrent memory must
  not be identified with a finite faithful carrier of the
  complete chronology.

Rendering disclosed: the recurrent-core clause and the
purification bound are the proved clauses of
`cth:prefix-support-memory` instantiated along the growing
horizon.
-/

open Matrix

namespace NCG

/-- `corollary:finite-recurrent-core-versus-growing-ledger`. -/
theorem finite_core_vs_growing_ledger :
    -- one-state recurrent core at every horizon
    (∀ (P F : Type) [Fintype P] [Fintype F]
      (u : P → ℝ) (v : F → ℝ),
      (Matrix.vecMulVec u v).rank ≤ 1)
    -- but the faithful ledger carrier grows without bound
    ∧ (∀ K : ℕ, ∃ N : ℕ, K < 2 ^ N ∧
        (∀ (E : Type) [Fintype E]
          (M : Matrix (Fin (2 ^ N)) E ℂ),
          M * Mᴴ = ((2 : ℂ) ^ N)⁻¹ • 1 →
          K < Fintype.card E)) := by
  constructor
  · intro P F _ _ u v
    exact (prefix_support_memory 0).2.1 P F u v
  · intro K
    refine ⟨K + 1, ?_, ?_⟩
    · calc K < 2 ^ K := Nat.lt_two_pow_self
        _ ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num)
            (by omega)
    · intro E _ M hM
      have h1 : 2 ^ (K + 1) ≤ Fintype.card E :=
        (prefix_support_memory (K + 1)).2.2.2 E M hM
      have h2 : K < 2 ^ (K + 1) := by
        calc K < 2 ^ K := Nat.lt_two_pow_self
          _ ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num)
              (by omega)
      omega

end NCG
