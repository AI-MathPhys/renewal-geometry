/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PeriodicQuotientDistanceExact
import NCG.Grand.A3PeriodicSmoothEnergyExact

/-!
# The genuine flat A3 torus metric

The period subgroup is closed because its root-basis coordinates are integral.
Its quotient is therefore a separated normed additive group. The flat distance
is the canonical quotient metric, equivalently the distance to the period lattice.
-/

open Set

namespace NCG.A3FlatTorusMetric

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy LatticePeriodicDifferentiation

noncomputable section

theorem lattice_eq_integral_coordinates :
    (lattice : Set Space) = ⋂ i : Fin 3, {x | coordinates x i ∈ Set.range (fun z : ℤ => (z : ℝ))} := by
  ext x
  simp only [mem_iInter, mem_setOf_eq, mem_range]
  constructor
  · rintro ⟨z, hz⟩ i
    refine ⟨z i, ?_⟩
    rw [← hz, coordinates_integerCombination]
  · intro hx
    choose z hz using hx
    refine ⟨z, ?_⟩
    apply coordinates.injective
    rw [coordinates_integerCombination]
    funext i
    exact hz i

instance lattice_isClosed : IsClosed (lattice : Set Space) := by
  rw [lattice_eq_integral_coordinates]
  apply isClosed_iInter
  intro i
  exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage
    ((continuous_apply i).comp coordinates.toLinearMap.continuous_of_finiteDimensional)

abbrev Torus := Space ⧸ lattice

def flatDistance (x y : Space) : ℝ := PeriodicQuotientDistance.distance lattice x y

theorem flatDistance_eq_infDist (x y : Space) :
    flatDistance x y = Metric.infDist (x - y) (lattice : Set Space) :=
  PeriodicQuotientDistance.distance_eq_infDist lattice x y

theorem flatDistance_eq_zero_iff (x y : Space) : flatDistance x y = 0 ↔ x - y ∈ lattice :=
  PeriodicQuotientDistance.distance_eq_zero_iff lattice x y

end

end NCG.A3FlatTorusMetric
