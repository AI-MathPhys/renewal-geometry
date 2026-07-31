/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# `ℤ₄` amplitude-orbit classification on `H¹(K₄; ℤ₄)`
  (`thm:z4-full-orbits`, `thm:z4-residual-orbits`, SM_emergence)

Gauge-fixing the tree `{01,02,03}` identifies `H¹(K₄;ℤ₄) ≅ ℤ₄³`
with holonomy coordinates `(x₁,x₂,x₃)` on the fundamental cycles
through the non-tree edges `12, 13, 23`.  The transpositions act by

`(01) : (x₁,x₂,x₃) ↦ (-x₁, -x₂, x₁-x₂+x₃)`,
`(12) : (x₁,x₂,x₃) ↦ (-x₁, x₃, x₂)`,
`(23) : (x₁,x₂,x₃) ↦ (x₂, x₁, -x₃)`,

and amplitude conjugation by global negation.

* `z4_full_orbit_card_*` / `z4_full_orbits_cover` /
  `z4_full_orbits_disjoint` / `z4_full_orbits_closed` — under
  `S₄ × ℤ₂^conj` the sixty-four classes form exactly eight orbits
  with the stated representatives and sizes
  `1, 12, 6, 24, 6, 12, 2, 1` (kernel-checked enumeration);
* `z4_residual_*` — under the residual
  `S₃ × ℤ₂^conj` (background distinguishing vertex `3`) they split
  into exactly thirteen orbits with the stated sizes;
* `z4_orbit_001_splits` — the full orbit of `(0,0,1)` splits into
  the two residual alignments `(0,0,1)` and `(1,0,0)`.
-/

namespace NCG

/-- Gauge-fixed `H¹(K₄;ℤ₄) ≅ ℤ₄³` holonomy coordinates. -/
abbrev Z4V := ZMod 4 × ZMod 4 × ZMod 4

/-- The transposition `(01)` on holonomy coordinates. -/
def z4ActA (x : Z4V) : Z4V := (-x.1, -x.2.1, x.1 - x.2.1 + x.2.2)

/-- The transposition `(12)` on holonomy coordinates. -/
def z4ActB (x : Z4V) : Z4V := (-x.1, x.2.2, x.2.1)

/-- The transposition `(23)` on holonomy coordinates. -/
def z4ActC (x : Z4V) : Z4V := (x.2.1, x.1, -x.2.2)

/-- Amplitude conjugation `c ↦ -c`. -/
def z4ActN (x : Z4V) : Z4V := (-x.1, -x.2.1, -x.2.2)

/-- One closure step under the full generator set. -/
def z4Step (S : Finset Z4V) : Finset Z4V :=
  S ∪ S.image z4ActA ∪ S.image z4ActB ∪ S.image z4ActC
    ∪ S.image z4ActN

/-- The full `S₄ × ℤ₂^conj` orbit of a class (closure stabilizes
well within eight steps on sixty-four states). -/
def z4OrbitOf (v : Z4V) : Finset Z4V := z4Step^[8] {v}

/-- One closure step under the residual generator set
(`S₃` fixing the background vertex `3`, plus conjugation). -/
def z4ResStep (S : Finset Z4V) : Finset Z4V :=
  S ∪ S.image z4ActA ∪ S.image z4ActB ∪ S.image z4ActN

/-- The residual `S₃ × ℤ₂^conj` orbit of a class. -/
def z4ResOrbitOf (v : Z4V) : Finset Z4V := z4ResStep^[8] {v}

set_option maxRecDepth 40000 in
/-- The eight full orbit sizes: `1, 12, 6, 24, 6, 12, 2, 1`. -/
theorem z4_full_orbit_sizes :
    (z4OrbitOf (0, 0, 0)).card = 1
      ∧ (z4OrbitOf (0, 0, 1)).card = 12
      ∧ (z4OrbitOf (0, 0, 2)).card = 6
      ∧ (z4OrbitOf (0, 1, 2)).card = 24
      ∧ (z4OrbitOf (1, 1, 1)).card = 6
      ∧ (z4OrbitOf (1, 1, 2)).card = 12
      ∧ (z4OrbitOf (1, 3, 1)).card = 2
      ∧ (z4OrbitOf (2, 2, 2)).card = 1 := by
  decide

set_option maxRecDepth 40000 in
/-- The eight full orbits exhaust the sixty-four classes. -/
theorem z4_full_orbits_cover :
    z4OrbitOf (0, 0, 0) ∪ z4OrbitOf (0, 0, 1)
      ∪ z4OrbitOf (0, 0, 2) ∪ z4OrbitOf (0, 1, 2)
      ∪ z4OrbitOf (1, 1, 1) ∪ z4OrbitOf (1, 1, 2)
      ∪ z4OrbitOf (1, 3, 1) ∪ z4OrbitOf (2, 2, 2)
      = Finset.univ := by
  decide

set_option maxRecDepth 40000 in
/-- The eight full orbits are pairwise disjoint. -/
theorem z4_full_orbits_disjoint :
    ([z4OrbitOf (0, 0, 0), z4OrbitOf (0, 0, 1),
      z4OrbitOf (0, 0, 2), z4OrbitOf (0, 1, 2),
      z4OrbitOf (1, 1, 1), z4OrbitOf (1, 1, 2),
      z4OrbitOf (1, 3, 1), z4OrbitOf (2, 2, 2)] :
      List (Finset Z4V)).Pairwise Disjoint := by
  decide

set_option maxRecDepth 40000 in
/-- Each computed full orbit is closed under all generators, hence
is the complete orbit of its representative. -/
theorem z4_full_orbits_closed :
    z4Step (z4OrbitOf (0, 0, 0)) = z4OrbitOf (0, 0, 0)
      ∧ z4Step (z4OrbitOf (0, 0, 1)) = z4OrbitOf (0, 0, 1)
      ∧ z4Step (z4OrbitOf (0, 0, 2)) = z4OrbitOf (0, 0, 2)
      ∧ z4Step (z4OrbitOf (0, 1, 2)) = z4OrbitOf (0, 1, 2)
      ∧ z4Step (z4OrbitOf (1, 1, 1)) = z4OrbitOf (1, 1, 1)
      ∧ z4Step (z4OrbitOf (1, 1, 2)) = z4OrbitOf (1, 1, 2)
      ∧ z4Step (z4OrbitOf (1, 3, 1)) = z4OrbitOf (1, 3, 1)
      ∧ z4Step (z4OrbitOf (2, 2, 2)) = z4OrbitOf (2, 2, 2) := by
  decide

set_option maxRecDepth 40000 in
/-- The thirteen residual orbit sizes:
`1, 6, 3, 6, 6, 12, 6, 6, 2, 3, 6, 6, 1`. -/
theorem z4_residual_orbit_sizes :
    (z4ResOrbitOf (0, 0, 0)).card = 1
      ∧ (z4ResOrbitOf (0, 0, 1)).card = 6
      ∧ (z4ResOrbitOf (0, 0, 2)).card = 3
      ∧ (z4ResOrbitOf (0, 1, 2)).card = 6
      ∧ (z4ResOrbitOf (1, 0, 0)).card = 6
      ∧ (z4ResOrbitOf (1, 0, 1)).card = 12
      ∧ (z4ResOrbitOf (1, 1, 1)).card = 6
      ∧ (z4ResOrbitOf (1, 1, 2)).card = 6
      ∧ (z4ResOrbitOf (1, 3, 1)).card = 2
      ∧ (z4ResOrbitOf (2, 0, 0)).card = 3
      ∧ (z4ResOrbitOf (2, 0, 1)).card = 6
      ∧ (z4ResOrbitOf (2, 1, 1)).card = 6
      ∧ (z4ResOrbitOf (2, 2, 2)).card = 1 := by
  decide

set_option maxRecDepth 40000 in
/-- The thirteen residual orbits exhaust the sixty-four classes. -/
theorem z4_residual_orbits_cover :
    z4ResOrbitOf (0, 0, 0) ∪ z4ResOrbitOf (0, 0, 1)
      ∪ z4ResOrbitOf (0, 0, 2) ∪ z4ResOrbitOf (0, 1, 2)
      ∪ z4ResOrbitOf (1, 0, 0) ∪ z4ResOrbitOf (1, 0, 1)
      ∪ z4ResOrbitOf (1, 1, 1) ∪ z4ResOrbitOf (1, 1, 2)
      ∪ z4ResOrbitOf (1, 3, 1) ∪ z4ResOrbitOf (2, 0, 0)
      ∪ z4ResOrbitOf (2, 0, 1) ∪ z4ResOrbitOf (2, 1, 1)
      ∪ z4ResOrbitOf (2, 2, 2)
      = Finset.univ := by
  decide

set_option maxRecDepth 40000 in
/-- The thirteen residual orbits are pairwise disjoint. -/
theorem z4_residual_orbits_disjoint :
    ([z4ResOrbitOf (0, 0, 0), z4ResOrbitOf (0, 0, 1),
      z4ResOrbitOf (0, 0, 2), z4ResOrbitOf (0, 1, 2),
      z4ResOrbitOf (1, 0, 0), z4ResOrbitOf (1, 0, 1),
      z4ResOrbitOf (1, 1, 1), z4ResOrbitOf (1, 1, 2),
      z4ResOrbitOf (1, 3, 1), z4ResOrbitOf (2, 0, 0),
      z4ResOrbitOf (2, 0, 1), z4ResOrbitOf (2, 1, 1),
      z4ResOrbitOf (2, 2, 2)] :
      List (Finset Z4V)).Pairwise Disjoint := by
  decide

set_option maxRecDepth 40000 in
/-- `thm:z4-residual-orbits` (split): the full orbit of `(0,0,1)`
splits into exactly the two residual alignments represented by
`(0,0,1)` and `(1,0,0)`. -/
theorem z4_orbit_001_splits :
    z4ResOrbitOf (0, 0, 1) ∪ z4ResOrbitOf (1, 0, 0)
        = z4OrbitOf (0, 0, 1)
      ∧ Disjoint (z4ResOrbitOf (0, 0, 1))
          (z4ResOrbitOf (1, 0, 0)) := by
  decide

end NCG
