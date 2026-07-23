/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spatial nondegeneracy and the dimension-selection corollaries

* **Definition `def:spatially-nondegenerate`**: an endpoint is spatially
  nondegenerate when its spatial sector has at least two independent
  directions (`S^{d−1}` supports angular averaging) — the one-axis case
  `d = 1` is excluded, and among odd primitive ranks the first
  nondegenerate one is `d = 3`.

* **Corollary `cor:first-order-symbol-selects-three`**: matching the
  volume-dual degree `d − 2` (Proposition `prop:volume-dual-degree`)
  with the degree-one primitive Dirac symbol forces `d = 3`.

* **Corollary `cor:dimension-final-status`**: within the primitive
  class, `d = 3` is minimal unconditionally among spatially
  nondegenerate odd ranks, and unique under interference closure.

* **Corollary `cor:concordant-native-selection`**: interference closure
  and the real-even division condition (whose Clifford-table content
  `Cl⁰₁ ≅ ℝ`, `Cl⁰₃ ≅ ℍ`, zero divisors for odd `d ≥ 5` enters as the
  hypothesis `d ∈ {1,3}`) are distinct criteria that concordantly select
  `d = 3` among spatially nondegenerate odd ranks. -/

namespace NCG

/-- **Definition `def:spatially-nondegenerate`**: the spatial sector has
at least two independent directions, so `S^{d−1}` carries a nontrivial
angular second-moment problem.  `d = 1` (where `S⁰ = {±1}` has no
angular averaging) is degenerate. -/
def SpatiallyNondegenerate (d : ℕ) : Prop := 2 ≤ d

theorem not_spatiallyNondegenerate_one : ¬SpatiallyNondegenerate 1 := by
  unfold SpatiallyNondegenerate
  omega

theorem spatiallyNondegenerate_three : SpatiallyNondegenerate 3 := by
  unfold SpatiallyNondegenerate
  omega

/-- The first spatially nondegenerate odd (primitive) rank is `3`
(Definition `def:spatially-nondegenerate`). -/
theorem three_le_of_odd_nondegenerate {d : ℕ} (hodd : Odd d)
    (hnd : SpatiallyNondegenerate d) : 3 ≤ d := by
  obtain ⟨k, rfl⟩ := hodd
  unfold SpatiallyNondegenerate at hnd
  omega

/-- **Corollary `cor:first-order-symbol-selects-three`**: if the
volume-dual response (degree `d − 2` by `prop:volume-dual-degree`) is
required to lie in the degree-one primitive Dirac symbol sector, then
`d = 3`. -/
theorem first_order_symbol_selects_three {d : ℕ} (hd : 3 ≤ d)
    (hdeg : d - 2 = 1) : d = 3 := by
  omega

/-- **Corollary `cor:dimension-final-status`**: within the primitive
(odd-rank) class, `d = 3` is the unconditional minimum among spatially
nondegenerate ranks, and it is the unique such rank once the oriented
volume-dual response closes into the elementary (degree-one) revision
sector.  (The regular-crystal chain `q_alg = q_met = rank ω = 4` is
tracked separately.) -/
theorem dimension_final_status {d : ℕ} (hodd : Odd d)
    (hnd : SpatiallyNondegenerate d) :
    3 ≤ d ∧ (d - 2 = 1 → d = 3) := by
  refine ⟨three_le_of_odd_nondegenerate hodd hnd, fun hdeg => ?_⟩
  exact first_order_symbol_selects_three
    (three_le_of_odd_nondegenerate hodd hnd) hdeg

/-- **Theorem `thm:minimal-field`** (minimal-field-content closure): if
the continuum endpoint's one-reset observable sector is exactly the
degree-one coframe/Dirac sector and the (nonzero, by chirality —
`NCG.chirality_of_circulation_ne_zero`) volume-dual response of degree
`d − 2` (Proposition `prop:volume-dual-degree`) is a one-reset
observable, then its degree must be one: `d = 3`. -/
theorem minimal_field_selects_three {d : ℕ} (hd : 3 ≤ d)
    (hdeg : d - 2 = 1) : d = 3 := by
  omega

/-- **Corollary `cor:concordant-native-selection`**: the two native
selection criteria — the real-even division condition (Clifford table:
only `d = 1, 3` give division algebras among odd ranks) and oriented
interference closure (`d − 2 = 1`) — both select exactly `d = 3` among
spatially nondegenerate odd ranks. -/
theorem concordant_native_selection {d : ℕ} (hodd : Odd d)
    (hnd : SpatiallyNondegenerate d) :
    ((d = 1 ∨ d = 3) → d = 3) ∧ (d - 2 = 1 → d = 3) := by
  have h3 := three_le_of_odd_nondegenerate hodd hnd
  exact ⟨fun hdiv => by omega, fun hdeg => by omega⟩

end NCG
