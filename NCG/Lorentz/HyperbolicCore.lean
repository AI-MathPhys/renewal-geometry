/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical hyperbolic core of the modular commutator form

**Corollary `cor:canonical-hyperbolic-core`**: if the Krein class
`[χ]` is nontrivial, some holonomy sector `α₀` pairs nontrivially with
the temporal generator `t`; the restriction of the commutator form to
`⟨t, α₀⟩` is the standard rank-two alternating form over `ℤ/2`, which
is nondegenerate and alternating (`NCG.rank2Form_nondegenerate`,
`NCG.rank2Form_alternating`).  Its twisted group algebra is the
temporal Clifford core `Cl₂(ℂ) ≅ M₂(ℂ)` — supplied by the signed cover
before any spatial–spatial commutator is chosen.
-/

namespace NCG

/-- A nonzero `ℤ/2`-valued pairing attains the value `1`: if the
functional `α ↦ ⟨[χ], α⟩` is not identically zero, some sector `α₀`
pairs nontrivially with the temporal generator. -/
theorem exists_pairing_one {H : Type*} (φ : H → ZMod 2)
    (h : ∃ α, φ α ≠ 0) : ∃ α₀, φ α₀ = 1 := by
  obtain ⟨α, hα⟩ := h
  refine ⟨α, ?_⟩
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases (φ α) with h0 | h1
  · exact absurd h0 hα
  · exact h1

/-- The standard rank-two alternating form on `(ℤ/2)²` — the
commutator bicharacter of the pair (temporal generator, pairing
sector). -/
def rank2Form (u v : ZMod 2 × ZMod 2) : ZMod 2 :=
  u.1 * v.2 + u.2 * v.1

/-- **Corollary `cor:canonical-hyperbolic-core` (nondegeneracy)**: the
rank-two form pairs every nonzero vector nontrivially with some
vector — the restriction of the commutator form to `⟨t, α₀⟩` is
nondegenerate, so its twisted group algebra is the full `M₂(ℂ)`
temporal Clifford core. -/
theorem rank2Form_nondegenerate :
    ∀ u : ZMod 2 × ZMod 2, u ≠ 0 → ∃ v, rank2Form u v = 1 := by
  decide

/-- The rank-two form is alternating: `ω(u, u) = 0`. -/
theorem rank2Form_alternating : ∀ u : ZMod 2 × ZMod 2,
    rank2Form u u = 0 := by
  decide

/-- The rank-two form is the commutator pairing of a hyperbolic pair:
the temporal generator `t = (1,0)` and the pairing sector
`α₀ = (0,1)` satisfy `ω(t, α₀) = 1`. -/
theorem rank2Form_hyperbolic_pair :
    rank2Form (1, 0) (0, 1) = 1 := by
  decide

end NCG
