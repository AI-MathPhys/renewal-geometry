/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# `C*`-quotients cannot merge surviving classical records
  (`cth:record-cstar-merge`, Gran-Tensor manuscript)

* `record_cstar_merge`: if `p, q` are orthogonal idempotents and
  `π` a ring homomorphism with `π(p) = π(q)`, then
  `π(p) = π(q) = 0` — so classical record minimization cannot be
  delegated to a two-sided quotient once nonzero point
  projections have been generated.

Rendering disclosed: the statement is proved for any ring
homomorphism and idempotents (subsuming `*`-homomorphisms of the
finite history `C*`-algebra and its record projections); the
consequence clause about generated writers is the manuscript's
reading of the identity.
-/

namespace NCG

/-- `cth:record-cstar-merge`: a quotient identifying two
orthogonal idempotents kills both. -/
theorem record_cstar_merge {A B : Type*} [Ring A] [Ring B]
    (π : A →+* B) (p q : A)
    (hp : p * p = p) (_hq : q * q = q) (hpq : p * q = 0)
    (heq : π p = π q) :
    π p = 0 ∧ π q = 0 := by
  have h : π p = 0 := by
    calc π p = π (p * p) := by rw [hp]
      _ = π p * π p := by rw [map_mul]
      _ = π p * π q := by rw [heq]
      _ = π (p * q) := by rw [map_mul]
      _ = 0 := by rw [hpq, map_zero]
  exact ⟨h, heq ▸ h⟩

end NCG
