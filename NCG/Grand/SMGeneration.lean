/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Tensor generation of one chiral matter packet
  (`thm:SM-generation`, Gran-Tensor manuscript)

* `sm_generation`: the additive central-charge bookkeeping of
  the tensor-type table (`y(Q⊗H) = y(u)`, `y(Q⊗H*) = y(d)`,
  `y(L⊗H*) = y(e)`), the exterior-square dimension identity
  `dim Λ²ℂ³ = 3` (so `Λ²3̄ ≅ 3` as a dimension count), and the
  full label table at the seed charges `C ↦ -2`, `W ↦ 3`.

Rendering disclosed: the one-dimensionality of each intertwiner
space is Schur's lemma for the concrete `SU(3)×SU(2)`
irreducibles (the manuscript's representation-theoretic step);
the charge equations and dimension counts proved here are the
finite bookkeeping that pins the table.
-/

namespace NCG

/-- `thm:SM-generation`. -/
theorem sm_generation :
    -- seed charges (C, W) = (-2, 3); tensor charges add,
    -- duals negate, exterior squares double
    (∀ yC yW : ℤ, yC = -2 → yW = 3 →
      -- the six labels
      (yC + yW = 1            -- Q = C⊗W
        ∧ -(2 * yC) = 4       -- u = Λ²C*
        ∧ yC = -2             -- d = C
        ∧ -yW = -3            -- L = W*
        ∧ -(2 * yW) = -6      -- e = Λ²W*
        ∧ yW = 3)             -- H = W
      -- the three Yukawa channels balance
      ∧ ((yC + yW) + yW = -(2 * yC)       -- Q⊗H → u
        ∧ (yC + yW) + (-yW) = yC          -- Q⊗H* → d
        ∧ (-yW) + (-yW) = -(2 * yW)))     -- L⊗H* → e
    -- the exterior-square dimension identity Λ²ℂ³ ≅ ℂ³
    ∧ Nat.choose 3 2 = 3
    ∧ Nat.choose 2 2 = 1 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro yC yW hC hW
  subst hC
  subst hW
  norm_num

end NCG
