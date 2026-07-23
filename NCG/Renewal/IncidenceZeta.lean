/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The chain-counting renewal resolvent

**Proposition `prop:incidence-zeta`**: the resolvent `Σ Φᵏ = (1−Φ)⁻¹`
of the Hasse transfer operator counts **saturated chains** and differs
from the ordinary incidence zeta whenever intervals carry several
saturated chains.  The manuscript's witness: in `ℕ²` there are **two**
saturated chains from `(0,0)` to `(1,1)`, while `ζ((0,0),(1,1)) = 1`.

We prove the multiplicity core: the set of Hasse-middle points between
`(0,0)` and `(1,1)` is exactly `{(1,0),(0,1)}` — so the saturated chain
count is `2 ≠ 1` (`NCG.covBy_middle_pair`,
`NCG.incidence_chain_multiplicity`).  (The completed-incidence-algebra
resolvent identity is the standard geometric series and is not
formalised.) -/

namespace NCG

/-- The Hasse middles between `(0,0)` and `(1,1)` in `ℕ²` are exactly
the two lattice neighbours (Proposition `prop:incidence-zeta`). -/
theorem covBy_middle_pair :
    {m : ℕ × ℕ | (0, 0) ⋖ m ∧ m ⋖ (1, 1)}
      = {(1, 0), (0, 1)} := by
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk_covBy_mk_iff,
    Nat.covBy_iff_add_one_eq, Prod.mk.injEq]
  omega

/-- **Proposition `prop:incidence-zeta`, multiplicity core**: the
interval `[(0,0),(1,1)] ⊆ ℕ²` carries exactly two saturated chains, so
the chain-counting resolvent differs from the `{0,1}`-valued incidence
zeta — path counting sees multiplicities that order membership does
not. -/
theorem incidence_chain_multiplicity :
    ({m : ℕ × ℕ | (0, 0) ⋖ m ∧ m ⋖ (1, 1)}).ncard = 2 := by
  rw [covBy_middle_pair]
  rw [Set.ncard_pair (by decide)]

end NCG
