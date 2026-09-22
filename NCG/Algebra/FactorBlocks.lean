/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Block decomposition counting for the revision algebra

**Theorem `thm:factor-quotients-corrected`** (counting core): the
revision algebra decomposes as `𝒜 ≅ ⊕_{ψ ∈ (rad ω)^} M_{2^m}(ℂ)` with
`2m = dim(H/rad ω)`.  This file certifies the numerical bookkeeping:

* the character group of the radical has exactly `2^{dim rad ω}`
  elements (`NCG.card_radical_characters`) — one block per character,
  matching `Z(𝒜) ≅ ℂ^{2^{dim rad ω}}` of `thm:radical-centre`;
* the dimensions balance: `2^r · (2^m)² = 2^{r+2m} = |H|`
  (`NCG.block_dimension_count`) — the direct sum of `2^r` blocks of
  size `2^m` recovers the full twisted group algebra dimension.

The Wedderburn/structure-theoretic part (each quotient is a matrix
algebra `≅ Cl_{2m}(ℂ)`) rests on the nondegeneracy of the descended form
(`NCG.inducedForm_separating`) and is not formalised. -/

namespace NCG

/-- **Theorem `thm:factor-quotients-corrected`, block count**: the
radical has exactly `2^{dim rad ω}` characters — one factor block per
character of `rad ω`. -/
theorem card_radical_characters (W : Type*) [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Finite (ZMod 2) W] :
    Nat.card (Module.Dual (ZMod 2) W)
      = 2 ^ Module.finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
    Subspace.dual_finrank_eq, Nat.card_eq_fintype_card, ZMod.card]

/-- **Theorem `thm:factor-quotients-corrected`, dimension balance**:
`2^r` blocks of complex dimension `(2^m)²` fill up the twisted group
algebra of dimension `2^{r+2m} = |H|`, `r = dim rad ω`,
`2m = dim(H/rad ω)`. -/
theorem block_dimension_count (r m : ℕ) :
    2 ^ r * (2 ^ m) ^ 2 = 2 ^ (r + 2 * m) := by
  rw [← pow_mul, ← pow_add]
  ring_nf

end NCG
