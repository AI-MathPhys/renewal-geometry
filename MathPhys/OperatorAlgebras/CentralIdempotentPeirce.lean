/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Peirce split along a central idempotent

Split out of `MathPhys.Commutant.SourceIdealSplit` (`thm:central-source-decomposition`):
a central idempotent `z` of a ring gives the two-sided ideal `zA`, the decomposition
`a = za + (1-z)a`, and `z` is unique for its ideal (`central_source_decomposition`).
-/

namespace MathPhys

section Peirce

variable {R : Type*} [Ring R]

/-- `thm:central-source-decomposition`: the central idempotent
Peirce split, with uniqueness of the central support. -/
theorem central_source_decomposition (z : R)
    (hz : z * z = z) (hcen : ∀ a, z * a = a * z) :
    (∀ a, a = z * a + (1 - z) * a)
    ∧ (∀ a b, (z * a) * b = z * (a * b)
        ∧ b * (z * a) = z * (b * a))
    ∧ ∀ z' : R, z' * z' = z' → (∀ a, z' * a = a * z') →
        (∀ a, ∃ b, z * a = z' * b)
        → (∀ a, ∃ b, z' * a = z * b) → z = z' := by
  refine ⟨fun a => by noncomm_ring, fun a b => ⟨by noncomm_ring,
    by rw [← mul_assoc, ← hcen b, mul_assoc]⟩, ?_⟩
  intro z' hz' hcen' h1 h2
  obtain ⟨b, hb⟩ := h1 1
  obtain ⟨c, hc⟩ := h2 1
  rw [mul_one] at hb hc
  have h3 : z' * z = z := by
    rw [hb, ← mul_assoc, hz']
  have h4 : z * z' = z' := by
    rw [hc, ← mul_assoc, hz]
  calc z = z' * z := h3.symm
    _ = z * z' := hcen' z
    _ = z' := h4

end Peirce

end MathPhys
