/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2
import NCG.Upstream.KalmanRealization

/-!
# Terminating arithmetic–renewal source test
  (`corollary:terminating-arithmetic-renewal-source-test`,
   Gran-Tensor manuscript)

* `terminating_renewal_source_test`: (i) `S₄`-invariance reduces
  a pointed tetrahedral pairing to five Gram parameters (one
  anchor value, one diagonal, one off-diagonal — the content of
  `tetrahedral_gram`), so two pointed tetrahedral families have
  matching Grams exactly when the five parameters agree; and
  (ii) for cyclic (source-minimal) families, equality of the
  finite orbit panels `⟨Tʳξ_a, Tˢξ_b⟩` yields a source-fixing
  transfer intertwiner — the finite Krylov Gram construction of
  `physical_source_uniqueness`.

Rendering disclosed: clause (i) is the five-parameter reduction
of the pointed Gram; the label-fixing isometry it defines on
linear combinations is the manuscript's "defines and makes well
defined" step over these equalities.  Clause (ii) is the cited
Kalman construction with the `S₄` reduction of each inserted
Gram to its orbit entries as bookkeeping.
-/

open Matrix

namespace NCG

/-- `corollary:terminating-arithmetic-renewal-source-test`:
five-parameter tetrahedral Gram reduction plus the terminating
Krylov source test. -/
theorem terminating_renewal_source_test
    {V : Type*} (P : V → V → ℂ) (ξt : V) (ξ : Fin 4 → V)
    (hactP : ∀ g : Equiv.Perm (Fin 4), ∀ i j,
      P (ξ i) (ξ j) = P (ξ (g i)) (ξ (g j)))
    (hactT : ∀ g : Equiv.Perm (Fin 4), ∀ i,
      P ξt (ξ i) = P ξt (ξ (g i))) :
    ((∀ i j, P ξt (ξ i) = P ξt (ξ j))
      ∧ (∀ i j, P (ξ i) (ξ i) = P (ξ j) (ξ j))
      ∧ (∀ i j k l, i ≠ j → k ≠ l →
          P (ξ i) (ξ j) = P (ξ k) (ξ l)))
    ∧ (∀ {u p : Type} [Fintype u] [Fintype p] [DecidableEq u]
        (G G' : Matrix u u ℂ) (B B' : Matrix u p ℂ),
        Gᴴ = G → G'ᴴ = G' →
        ∀ d : ℕ, 0 < d →
        Function.Surjective (krylovMat G B d).mulVec →
        (∀ n : ℕ, Bᴴ * G ^ n * B = B'ᴴ * G' ^ n * B') →
        ∃ W : Matrix u u ℂ, Wᴴ * W = 1 ∧ W * B = B'
          ∧ W * G = G' * W) := by
  refine ⟨tetrahedral_gram P ξt ξ hactP hactT, ?_⟩
  intro u p _ _ _ G G' B B' hG hG' d hd hmin hmom
  exact physical_source_uniqueness G G' B B' hG hG' d hd
    hmin hmom

end NCG
