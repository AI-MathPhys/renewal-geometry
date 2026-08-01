/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Unique nonzero tetrahedrally invariant sign class
  (`thm:unique-antibalanced-class`, SM manuscript)

Switching classes of sign structures on `K₄` are encoded by the
parities of the four triangular faces: every edge lies in exactly
two faces, so the parity vector has even Hamming weight, and the
eight even-weight vectors in `𝔽₂⁴` are exactly the eight switching
classes `H¹(K₄;𝔽₂)` (the standard Zaslavsky correspondence used by
the manuscript).  The `S₄` symmetry permutes the four face
coordinates.  In this encoding:

* `antibalanced_card` — there are eight classes;
* `antibalanced_invariant_iff` — the `S₄`-invariant classes are
  exactly `0` and the all-negative class `[c]` (the all-ones parity
  vector);
* `antibalanced_orbit_transitive` — the remaining six classes form
  a single `S₄`-orbit `𝒪₆`;
* `antibalanced_middle_card` — that orbit has six elements.

Together these give the boxed decomposition
`H¹(K₄;𝔽₂) = {0} ⊔ {[c]} ⊔ 𝒪₆` and
`H¹(K₄;𝔽₂)^{S₄} = {0, [c]}`.
-/

namespace NCG

/-- There are eight even-weight parity vectors — the eight
switching classes of `K₄`. -/
theorem antibalanced_card :
    Fintype.card {v : Fin 4 → ZMod 2 // ∑ i, v i = 0} = 8 := by
  decide

/-- The `S₄`-invariant classes are exactly `0` and the all-negative
class `[c]` (all-ones). -/
theorem antibalanced_invariant_iff :
    ∀ v : Fin 4 → ZMod 2, (∑ i, v i = 0) →
      ((∀ g : Equiv.Perm (Fin 4), (fun i => v (g i)) = v)
        ↔ v = (fun _ => 0) ∨ v = (fun _ => 1)) := by
  decide

/-- The six classes other than `0` and `[c]` form a single
`S₄`-orbit. -/
theorem antibalanced_orbit_transitive :
    ∀ v w : Fin 4 → ZMod 2, (∑ i, v i = 0) → (∑ i, w i = 0) →
      v ≠ (fun _ => 0) → v ≠ (fun _ => 1) →
      w ≠ (fun _ => 0) → w ≠ (fun _ => 1) →
      ∃ g : Equiv.Perm (Fin 4), (fun i => v (g i)) = w := by
  decide

/-- The nontrivial non-invariant orbit `𝒪₆` has six elements. -/
theorem antibalanced_middle_card :
    Fintype.card {v : Fin 4 → ZMod 2 //
      (∑ i, v i = 0) ∧ v ≠ (fun _ => 0) ∧ v ≠ (fun _ => 1)} = 6 := by
  decide

end NCG
