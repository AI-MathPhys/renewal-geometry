/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AtlasIsoperimetry

/-!
# Chart-core aggregation for protected atlas isoperimetry

This file removes the scalar aggregation hypotheses from the atlas branch of
`thm:coordinate-atlas-isoperimetry`.  Chart masses and local/interface cuts
are defined from a genuine finite vertex partition and a common edge set;
their required sum and domination identities then follow automatically.
-/

open Finset

namespace NCG
namespace AtlasChartCoreAggregationExact

variable {V E ι : Type*} [Fintype V] [Fintype E] [Fintype ι]
  [DecidableEq V] [DecidableEq E] [DecidableEq ι]

def chartMass (chart : V → ι) (mass : V → ℝ) (a : ι) : ℝ :=
  ∑ v with chart v = a, mass v

def insideMass (chart : V → ι) (mass : V → ℝ)
    (A : Finset V) (a : ι) : ℝ :=
  ∑ v with chart v = a, if v ∈ A then mass v else 0

def totalMass (mass : V → ℝ) : ℝ := ∑ v, mass v

def selectedMass (mass : V → ℝ) (A : Finset V) : ℝ :=
  ∑ v, if v ∈ A then mass v else 0

def Crosses (A : Finset V) (s t : V) : Prop :=
  (s ∈ A ∧ t ∉ A) ∨ (s ∉ A ∧ t ∈ A)

noncomputable def globalCut (src tgt : E → V) (capacity : E → ℝ)
    (A : Finset V) : ℝ := by
  classical
  exact ∑ e, if Crosses A (src e) (tgt e) then capacity e else 0

noncomputable def localCut (chart : V → ι) (src tgt : E → V)
    (capacity : E → ℝ) (A : Finset V) (a : ι) : ℝ := by
  classical
  exact ∑ e, if chart (src e) = a ∧ chart (tgt e) = a ∧
    Crosses A (src e) (tgt e) then capacity e else 0

noncomputable def interfaceCut (chart : V → ι) (src tgt : E → V)
    (capacity : E → ℝ) (A : Finset V) (a b : ι) : ℝ := by
  classical
  exact ∑ e, if (((chart (src e) = a ∧ chart (tgt e) = b) ∨
      (chart (src e) = b ∧ chart (tgt e) = a)) ∧
      Crosses A (src e) (tgt e)) then capacity e else 0

/-- A genuine chart partition automatically partitions total mass. -/
theorem totalMass_eq_sum_chartMass
    (chart : V → ι) (mass : V → ℝ) :
    totalMass mass = ∑ a, chartMass chart mass a := by
  classical
  exact (Finset.sum_fiberwise Finset.univ chart mass).symm

/-- The selected mass is partitioned by the same chart fibers. -/
theorem selectedMass_eq_sum_insideMass
    (chart : V → ι) (mass : V → ℝ) (A : Finset V) :
    selectedMass mass A = ∑ a, insideMass chart mass A a := by
  classical
  exact (Finset.sum_fiberwise Finset.univ chart
    (fun v => if v ∈ A then mass v else 0)).symm

/-- Internal chart cuts are disjoint subcollections of the global cut. -/
theorem sum_localCut_le_globalCut
    (chart : V → ι) (src tgt : E → V) (capacity : E → ℝ)
    (A : Finset V) (hcap : ∀ e, 0 ≤ capacity e) :
    ∑ a, localCut chart src tgt capacity A a ≤
      globalCut src tgt capacity A := by
  classical
  change (∑ a : ι, ∑ e : E,
      if chart (src e) = a ∧ chart (tgt e) = a ∧
        Crosses A (src e) (tgt e) then capacity e else 0) ≤
    ∑ e : E, if Crosses A (src e) (tgt e) then capacity e else 0
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e _
  by_cases hx : Crosses A (src e) (tgt e)
  · by_cases hc : chart (src e) = chart (tgt e)
    · simp [localCut, hx, hc]
    · have hzero : ∀ a : ι,
          ¬(chart (src e) = a ∧ chart (tgt e) = a) := by
        intro a ha
        exact hc (ha.1.trans ha.2.symm)
      simp [localCut, hx, hzero, hcap]
  · simp [localCut, hx, hcap]

/-- Every chart-interface cut is a subcollection of the global cut. -/
theorem interfaceCut_le_globalCut
    (chart : V → ι) (src tgt : E → V) (capacity : E → ℝ)
    (A : Finset V) (a b : ι) (hcap : ∀ e, 0 ≤ capacity e) :
    interfaceCut chart src tgt capacity A a b ≤
      globalCut src tgt capacity A := by
  classical
  apply Finset.sum_le_sum
  intro e _
  by_cases hx : Crosses A (src e) (tgt e)
  · by_cases hi : (chart (src e) = a ∧ chart (tgt e) = b) ∨
        (chart (src e) = b ∧ chart (tgt e) = a)
    · simp [interfaceCut, globalCut, hx, hi]
    · simp [interfaceCut, globalCut, hx, hi, hcap]
  · simp [interfaceCut, globalCut, hx]

/-- Atlas cut bound with all chart-core aggregation identities derived from
the underlying partition and common edge set. -/
theorem protected_atlas_cut_bound_of_partition
    [Nonempty ι]
    (chart : V → ι) (mass : V → ℝ) (A : Finset V)
    (src tgt : E → V) (capacity : E → ℝ)
    (adj : ι → ι → Prop)
    (I0 Jstar η vstar Vstar : ℝ)
    (hcap : ∀ e, 0 ≤ capacity e)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hv : 0 < vstar) (hV : 0 < Vstar)
    (hI : 0 ≤ I0) (hJ : 0 ≤ Jstar)
    (hchartMass : ∀ a, vstar ≤ chartMass chart mass a)
    (hinside0 : ∀ a, 0 ≤ insideMass chart mass A a)
    (hinside : ∀ a, insideMass chart mass A a ≤ chartMass chart mass a)
    (htotal : totalMass mass ≤ Vstar)
    (hglobalHalf : selectedMass mass A ≤ totalMass mass / 2)
    (hlocal : ∀ a,
      I0 * min (insideMass chart mass A a)
        (chartMass chart mass a - insideMass chart mass A a) ^
          ((2 : ℝ) / 3) ≤ localCut chart src tgt capacity A a)
    (hconn : NerveCutConnected adj)
    (hinterface : ∀ a b, adj a b →
      η * chartMass chart mass a ≤ insideMass chart mass A a →
      insideMass chart mass A b ≤ (1 - η) * chartMass chart mass b →
      Jstar ≤ interfaceCut chart src tgt capacity A a b) :
    min (I0 * (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3))
        (Jstar * (2 / Vstar) ^ ((2 : ℝ) / 3)) *
      selectedMass mass A ^ ((2 : ℝ) / 3) ≤
        globalCut src tgt capacity A := by
  apply protected_atlas_cut_bound
    (chartMass chart mass) (insideMass chart mass A)
    (localCut chart src tgt capacity A)
    (interfaceCut chart src tgt capacity A) adj
    (totalMass mass) (selectedMass mass A)
    (globalCut src tgt capacity A) I0 Jstar η vstar Vstar
    hη hηhalf hv hV hI hJ hchartMass hinside0 hinside
  · exact totalMass_eq_sum_chartMass chart mass
  · exact selectedMass_eq_sum_insideMass chart mass A
  · exact htotal
  · exact hglobalHalf
  · exact hlocal
  · exact sum_localCut_le_globalCut chart src tgt capacity A hcap
  · exact hconn
  · exact hinterface
  · intro a b
    exact interfaceCut_le_globalCut chart src tgt capacity A a b hcap

end AtlasChartCoreAggregationExact
end NCG
