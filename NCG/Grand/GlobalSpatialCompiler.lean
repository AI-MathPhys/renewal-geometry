/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteEndpointCoequalizerCapacityReconstruction
import NCG.Grand.FinitePressureFlowMaxCut
import NCG.Grand.OperationalSobolevWeylExact
import NCG.Grand.OperationalSobolevWeylFiniteGraph

/-!
# Finite global spatial compiler and exact obstruction
  (`thm:global-spatial-compiler`)

This file supplies the assembly missing from the earlier one-directional cut
certificate.  It defines the manuscript's centered dimension-three pressure
demand on a finite weighted endpoint graph and proves:

* exact centering and positive mass on the selected cut;
* the max-flow/min-cut equivalence for that canonical demand;
* an explicit normalized dual potential, obtained from the actual endpoint
  cut indicator, whose variation is one and whose pressure pairing is the
  reciprocal cut ratio;
* finite termination of the endpoint coequalizer ledger.

The positive Sobolev, Poincare, heat-trace, low-energy counting and compact
screen consequences are imported above and are cited together with this
assembly by the manuscript ledger.
-/

open Finset

namespace NCG
namespace GlobalSpatialCompiler

/-- Physical mass of a finite endpoint cut. -/
def cutMass {V : Type*} [Fintype V]
    (mass : V → ℝ) (A : Finset V) : ℝ :=
  ∑ v ∈ A, mass v

/-- Canonical centered pressure demand with prescribed positive cut mass
`scale`.  For the manuscript demand take `scale = cutMass mass A ^ (2/3)`.
-/
noncomputable def pressureDemand {V : Type*} [Fintype V]
    [DecidableEq V] (mass : V → ℝ) (A : Finset V)
    (scale : ℝ) (v : V) : ℝ :=
  if v ∈ A then scale / cutMass mass A * mass v
  else -(scale / cutMass mass Aᶜ) * mass v

theorem pressureDemand_sum_cut {V : Type*} [Fintype V]
    [DecidableEq V] (mass : V → ℝ) (A : Finset V)
    (scale : ℝ) (hA : cutMass mass A ≠ 0) :
    ∑ v ∈ A, pressureDemand mass A scale v = scale := by
  calc
    (∑ v ∈ A, pressureDemand mass A scale v)
        = ∑ v ∈ A, (scale / cutMass mass A) * mass v := by
            apply Finset.sum_congr rfl
            intro v hv
            simp [pressureDemand, hv]
    _ = (scale / cutMass mass A) * (∑ v ∈ A, mass v) := by
          rw [Finset.mul_sum]
    _ = scale := by
          change scale / cutMass mass A * cutMass mass A = scale
          exact div_mul_cancel₀ scale hA

theorem pressureDemand_sum_compl {V : Type*} [Fintype V]
    [DecidableEq V] (mass : V → ℝ) (A : Finset V)
    (scale : ℝ) (hAc : cutMass mass Aᶜ ≠ 0) :
    ∑ v ∈ Aᶜ, pressureDemand mass A scale v = -scale := by
  calc
    (∑ v ∈ Aᶜ, pressureDemand mass A scale v)
        = ∑ v ∈ Aᶜ, -(scale / cutMass mass Aᶜ) * mass v := by
            apply Finset.sum_congr rfl
            intro v hv
            have hvA : v ∉ A := Finset.mem_compl.mp hv
            simp [pressureDemand, hvA]
    _ = -(scale / cutMass mass Aᶜ) * (∑ v ∈ Aᶜ, mass v) := by
          rw [Finset.mul_sum]
    _ = -scale := by
          change -(scale / cutMass mass Aᶜ) * cutMass mass Aᶜ = -scale
          rw [neg_mul, div_mul_cancel₀ scale hAc]

/-- The canonical pressure demand is exactly centered. -/
theorem pressureDemand_centered {V : Type*} [Fintype V]
    [DecidableEq V] (mass : V → ℝ) (A : Finset V)
    (scale : ℝ) (hA : cutMass mass A ≠ 0)
    (hAc : cutMass mass Aᶜ ≠ 0) :
    ∑ v, pressureDemand mass A scale v = 0 := by
  rw [← Finset.sum_add_sum_compl A,
    pressureDemand_sum_cut mass A scale hA,
    pressureDemand_sum_compl mass A scale hAc]
  ring

/-- The endpoint cut indicator pairs with the canonical pressure demand to
give its prescribed positive mass. -/
theorem pressureDemand_pairing_cutIndicator {V : Type*} [Fintype V]
    [DecidableEq V] (mass : V → ℝ) (A : Finset V)
    (scale : ℝ) (hA : cutMass mass A ≠ 0) :
    demandPairing (pressureDemand mass A scale) (cutIndicator A) = scale := by
  unfold demandPairing
  rw [← Finset.sum_add_sum_compl A]
  have hinside :
      (∑ v ∈ A, pressureDemand mass A scale v * cutIndicator A v)
        = scale := by
    calc
      (∑ v ∈ A, pressureDemand mass A scale v * cutIndicator A v)
          = ∑ v ∈ A, pressureDemand mass A scale v := by
              apply Finset.sum_congr rfl
              intro v hv
              simp [cutIndicator, hv]
      _ = scale := pressureDemand_sum_cut mass A scale hA
  have houtside :
      (∑ v ∈ Aᶜ, pressureDemand mass A scale v * cutIndicator A v)
        = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hvA : v ∉ A := Finset.mem_compl.mp hv
    simp [cutIndicator, hvA]
  rw [hinside, houtside, add_zero]

/-- The actual endpoint-record cut gives a canonical normalized dual
potential. -/
noncomputable def normalizedCutPotential {V : Type*} [Fintype V]
    [DecidableEq V] (capacity : V → V → ℝ) (A : Finset V) : V → ℝ :=
  fun v ↦ (finiteCutCapacity capacity A)⁻¹ * cutIndicator A v

theorem normalizedCutPotential_pairing {V : Type*} [Fintype V]
    [DecidableEq V] (mass : V → ℝ) (capacity : V → V → ℝ)
    (A : Finset V) (scale : ℝ) (hA : cutMass mass A ≠ 0) :
    demandPairing (pressureDemand mass A scale)
        (normalizedCutPotential capacity A) =
      scale / finiteCutCapacity capacity A := by
  have hpair := pressureDemand_pairing_cutIndicator mass A scale hA
  calc
    demandPairing (pressureDemand mass A scale)
        (normalizedCutPotential capacity A)
        = (finiteCutCapacity capacity A)⁻¹ *
            demandPairing (pressureDemand mass A scale) (cutIndicator A) := by
              unfold demandPairing normalizedCutPotential
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro v _
              ring
    _ = (finiteCutCapacity capacity A)⁻¹ * scale := by rw [hpair]
    _ = scale / finiteCutCapacity capacity A := by
          rw [div_eq_mul_inv]
          ring

/-- The normalized cut potential has unit undirected weighted variation. -/
theorem normalizedCutPotential_variation {V : Type*} [Fintype V]
    [DecidableEq V] (capacity : V → V → ℝ)
    (hsym : ∀ u v, capacity u v = capacity v u)
    (A : Finset V) (hcap : 0 < finiteCutCapacity capacity A) :
    (1 / 2 : ℝ) *
        (∑ u, ∑ v, capacity u v *
          |normalizedCutPotential capacity A u -
            normalizedCutPotential capacity A v|) = 1 := by
  have hinv : 0 ≤ (finiteCutCapacity capacity A)⁻¹ :=
    inv_nonneg.mpr hcap.le
  have hpoint (u v : V) :
      |normalizedCutPotential capacity A u -
          normalizedCutPotential capacity A v| =
        (finiteCutCapacity capacity A)⁻¹ *
          |cutIndicator A u - cutIndicator A v| := by
    unfold normalizedCutPotential
    rw [← mul_sub, abs_mul, abs_of_nonneg hinv]
  simp_rw [hpoint]
  have hfactor :
      (∑ u, ∑ v, capacity u v *
        ((finiteCutCapacity capacity A)⁻¹ *
          |cutIndicator A u - cutIndicator A v|)) =
        (finiteCutCapacity capacity A)⁻¹ *
          (∑ u, ∑ v, capacity u v *
            |cutIndicator A u - cutIndicator A v|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hvariation := cutIndicator_weightedVariation capacity hsym A
  calc
    (1 / 2 : ℝ) *
        (∑ u, ∑ v, capacity u v *
          ((finiteCutCapacity capacity A)⁻¹ *
            |cutIndicator A u - cutIndicator A v|))
        = (1 / 2 : ℝ) * (finiteCutCapacity capacity A)⁻¹ *
            (∑ u, ∑ v, capacity u v *
              |cutIndicator A u - cutIndicator A v|) := by
                rw [hfactor]
                ring
    _ = (1 / 2 : ℝ) * (finiteCutCapacity capacity A)⁻¹ *
          (2 * finiteCutCapacity capacity A) := by rw [hvariation]
    _ = 1 := by
          field_simp

/-- Clause (G4): every nondegenerate endpoint cut supplies the exact
normalized macroscopic-neck witness. -/
theorem normalized_macroscopic_neck_obstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (capacity : V → V → ℝ)
    (hsym : ∀ u v, capacity u v = capacity v u)
    (A : Finset V) (scale : ℝ) (hscale : 0 ≤ scale)
    (hA : cutMass mass A ≠ 0)
    (hcap : 0 < finiteCutCapacity capacity A) :
    ∃ phi : V → ℝ,
      (1 / 2 : ℝ) *
          (∑ u, ∑ v, capacity u v * |phi u - phi v|) = 1 ∧
      |demandPairing (pressureDemand mass A scale) phi| =
        scale / finiteCutCapacity capacity A := by
  refine ⟨normalizedCutPotential capacity A,
    normalizedCutPotential_variation capacity hsym A hcap, ?_⟩
  rw [normalizedCutPotential_pairing mass capacity A scale hA,
    abs_of_nonneg]
  exact div_nonneg hscale hcap.le

/-- Clause (G2): exact finite pressure flow/cut equivalence for the canonical
centered demand. -/
theorem canonical_pressure_flow_cut_iff
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (mass : V → ℝ) (capacity : V → V → ℝ)
    (hcapacity : ∀ u v, 0 ≤ capacity u v)
    (hsym : ∀ u v, capacity u v = capacity v u)
    (A : Finset V) (scale congestion : ℝ)
    (hA : cutMass mass A ≠ 0) (hAc : cutMass mass Aᶜ ≠ 0)
    (hcongestion : 0 ≤ congestion) :
    (∃ current,
        current ∈ finiteCapacityCurrentSet capacity congestion ∧
        finiteDivergence current = pressureDemand mass A scale) ↔
      ∀ B : Finset V,
        |∑ v ∈ B, pressureDemand mass A scale v| ≤
          congestion * finiteCutCapacity capacity B := by
  exact finite_transshipment_flow_cut_iff capacity hcapacity hsym
    (pressureDemand mass A scale) congestion hcongestion
    (pressureDemand_centered mass A scale hA hAc)

/-- Finite ledger of nontrivial cuts used by the three-dimensional
isoperimetric enumeration. -/
noncomputable def admissibleCuts {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun A =>
    0 < cutMass mass A ∧ cutMass mass A ≤ cutMass mass Finset.univ / 2

/-- The finite list of all admissible cut ratios. -/
noncomputable def finiteCutRatios {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (capacity : V → V → ℝ) : Finset ℝ := by
  classical
  exact (admissibleCuts mass).image fun A =>
    finiteCutCapacity capacity A /
      (cutMass mass A) ^ ((2 : ℝ) / 3)

/-- Clause (G2), finite enumeration form: whenever an admissible cut exists,
the isoperimetric infimum is one of the explicitly enumerated cut ratios and
is attained by an actual endpoint-record cut. -/
theorem finite_cut_ratio_min_attained
    {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (capacity : V → V → ℝ)
    (hne : (finiteCutRatios mass capacity).Nonempty) :
    ∃ A ∈ admissibleCuts mass,
      finiteCutCapacity capacity A /
          (cutMass mass A) ^ ((2 : ℝ) / 3) =
        (finiteCutRatios mass capacity).min' hne := by
  classical
  have hmem := (finiteCutRatios mass capacity).min'_mem hne
  simp only [finiteCutRatios, Finset.mem_image] at hmem
  obtain ⟨A, hA, hratio⟩ := hmem
  exact ⟨A, hA, hratio⟩

/-- Clause (G4), limiting form: a positive cut constant converging to zero
has reciprocal obstruction diverging to infinity. Combined with
`normalized_macroscopic_neck_obstruction`, this is the manuscript's
normalized macroscopic-neck sequence. -/
theorem vanishing_cut_ratio_obstruction
    (isoperimetric : ℕ → ℝ)
    (hvanish : Filter.Tendsto isoperimetric Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0))) :
    Filter.Tendsto (fun n => (isoperimetric n)⁻¹)
      Filter.atTop Filter.atTop := by
  exact hvanish.inv_tendsto_nhdsGT_zero

/-- Clause (G1): the generated endpoint equivalence ledger and its quotient
are finite, so all relation and cut comparisons terminate by enumeration. -/
theorem endpoint_compiler_finite
    {X : Type*} [Fintype X] (matchRel : X → X → Prop) :
    Finite (EndpointRefinementCoequalizer.Coequalizer matchRel) :=
  FiniteEndpointCapacity.endpointCoequalizer_finite matchRel

end GlobalSpatialCompiler
end NCG
