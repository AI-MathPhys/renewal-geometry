/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Navier--Stokes cubic-cylinder accounting

This file isolates the exact accounting arguments in NS.12--NS.15.  A packet
controlled by three nonnegative rows must charge one row by a fixed fraction;
absolute continuity of the cubic mass collapses radii carrying a scale-normal
lower bound; and disjoint cylinders obey the claimed square-radius packing
estimate.
-/

open Filter Topology

noncomputable section

namespace NCG.NavierStokesCylinderPacking

/-- If three assembled rows pay a packet of size at least `packetFloor`, then
one row pays at least one third of that floor. -/
theorem one_of_three_rows_pays
    (packetFloor packet inherited assembled cubic : ℝ)
    (hfloor : packetFloor ≤ packet)
    (hledger : packet ≤ inherited + assembled + cubic) :
    packetFloor / 3 ≤ inherited ∨ packetFloor / 3 ≤ assembled ∨
      packetFloor / 3 ≤ cubic := by
  by_contra h
  simp only [not_or, not_le] at h
  linarith

/-- A scale-normal cubic lower bound and vanishing local mass force the
selected cylinder radii to collapse. -/
theorem radii_tendsto_zero_of_cubic_mass
    {ι : Type*} {l : Filter ι}
    (radius localMass : ι → ℝ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hradius : ∀ i, 0 ≤ radius i) (hmass : ∀ i, 0 ≤ localMass i)
    (hlower : ∀ i, epsilon * (radius i) ^ 2 ≤ localMass i)
    (hmassZero : Tendsto localMass l (𝓝 0)) :
    Tendsto radius l (𝓝 0) := by
  have hquotient : Tendsto (fun i ↦ localMass i / epsilon) l (𝓝 0) := by
    convert hmassZero.div_const epsilon using 1 <;> simp [hepsilon.ne']
  have hsqrt : Tendsto (fun i ↦ Real.sqrt (localMass i / epsilon)) l (𝓝 0) := by
    simpa using hquotient.sqrt
  refine squeeze_zero hradius ?_ hsqrt
  intro i
  have hsquare : (radius i) ^ 2 ≤ localMass i / epsilon :=
    (le_div_iff₀ hepsilon).2 (by simpa [mul_comm] using hlower i)
  rw [← Real.sqrt_sq (hradius i)]
  exact Real.sqrt_le_sqrt hsquare

/-- Denominator-free NS.15: summing scale-normal lower bounds over disjoint
cylinders (represented by `hsum`) controls the total squared radius. -/
theorem finite_cylinder_packing
    {ι : Type*} (s : Finset ι) (radius localMass : ι → ℝ)
    (epsilon nu totalMass : ℝ)
    (hlower : ∀ i ∈ s, epsilon * nu ^ 2 * radius i ^ 2 ≤ localMass i)
    (hsum : ∑ i ∈ s, localMass i ≤ totalMass) :
    epsilon * nu ^ 2 * ∑ i ∈ s, radius i ^ 2 ≤ totalMass := by
  calc
    epsilon * nu ^ 2 * ∑ i ∈ s, radius i ^ 2 =
        ∑ i ∈ s, epsilon * nu ^ 2 * radius i ^ 2 := by
      simp [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, localMass i :=
      Finset.sum_le_sum fun i hi ↦ hlower i hi
    _ ≤ totalMass := hsum

/-- The divided form of the finite packing estimate appearing in NS.15. -/
theorem finite_cylinder_packing_divided
    {ι : Type*} (s : Finset ι) (radius localMass : ι → ℝ)
    (epsilon nu totalMass : ℝ) (hepsilon : 0 < epsilon) (hnu : 0 < nu)
    (hlower : ∀ i ∈ s, epsilon * nu ^ 2 * radius i ^ 2 ≤ localMass i)
    (hsum : ∑ i ∈ s, localMass i ≤ totalMass) :
    ∑ i ∈ s, radius i ^ 2 ≤ totalMass / (epsilon * nu ^ 2) := by
  exact (le_div_iff₀ (mul_pos hepsilon (sq_pos_of_pos hnu))).2
    (by simpa [mul_assoc, mul_comm, mul_left_comm] using
      finite_cylinder_packing s radius localMass epsilon nu totalMass hlower hsum)

end NCG.NavierStokesCylinderPacking
