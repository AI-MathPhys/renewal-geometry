/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Matching-axis half-edges and the vertex no-go
  (`thm:matching-axis-half-edge` and
  `cth:vertex-no-local-edge`, Gran-Tensor manuscript)

* `matching_axis_half_edge`: with the three perfect matchings
  of `K₄` as the fixed-point-free involutions
  `matchPartner`:
  (i) each matching pairs every vertex with a distinct
      partner (`ε(i,m) ∋ i` well defined);
  (ii) the boxed assignment `(i,m) ↦ (i, ε(i,m))` is a
      bijection from `Ω × ℳ` onto the twelve half-edges.

* `vertex_no_local_edge`: there is no `S₄`-equivariant
  deterministic map from opportunity values to edges — a
  card-two subset invariant under the stabilizer swaps of a
  vertex does not exist.
-/

namespace NCG

/-- The three perfect matchings of `K₄` as partner maps. -/
def matchPartner : Fin 3 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

/-- `thm:matching-axis-half-edge`. -/
theorem matching_axis_half_edge :
    -- (i) fixed-point-free involutions
    (∀ (m : Fin 3) (i : Fin 4),
      matchPartner m i ≠ i
      ∧ matchPartner m (matchPartner m i) = i)
    -- (ii) the boxed bijection onto the twelve half-edges
    ∧ Function.Injective
        (fun p : Fin 4 × Fin 3 =>
          (p.1, matchPartner p.2 p.1))
    ∧ Fintype.card (Fin 4 × Fin 3) = 12
    ∧ Fintype.card {p : Fin 4 × Fin 4 // p.1 ≠ p.2} = 12
    ∧ (∀ p : Fin 4 × Fin 4, p.1 ≠ p.2 →
        ∃ q : Fin 4 × Fin 3,
          (q.1, matchPartner q.2 q.1) = p) := by
  refine ⟨by decide, by decide, by decide, by decide,
    by decide⟩

/-- `cth:vertex-no-local-edge`. -/
theorem vertex_no_local_edge :
    ¬ ∃ f : Fin 4 → Finset (Fin 4),
      (∀ i, (f i).card = 2)
      ∧ (∀ (σ : Equiv.Perm (Fin 4)) (i : Fin 4),
          f (σ i) = (f i).image σ) := by
  rintro ⟨f, hcard, hequiv⟩
  have h1 := hequiv (Equiv.swap 1 2) 0
  have h2 := hequiv (Equiv.swap 1 3) 0
  have h3 := hequiv (Equiv.swap 2 3) 0
  rw [show (Equiv.swap (1 : Fin 4) 2) 0 = 0 from by
    decide] at h1
  rw [show (Equiv.swap (1 : Fin 4) 3) 0 = 0 from by
    decide] at h2
  rw [show (Equiv.swap (2 : Fin 4) 3) 0 = 0 from by
    decide] at h3
  have hex : ∃ s : Finset (Fin 4), s.card = 2
      ∧ s = s.image ⇑(Equiv.swap (1 : Fin 4) 2)
      ∧ s = s.image ⇑(Equiv.swap (1 : Fin 4) 3)
      ∧ s = s.image ⇑(Equiv.swap (2 : Fin 4) 3) :=
    ⟨f 0, hcard 0, h1, h2, h3⟩
  exact absurd hex (by decide)

end NCG
