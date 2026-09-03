/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Tight probability laws and convergence-determining marginals

This file supplies the missing abstract Prokhorov upgrade used by the hard
renewal, score-process, and Ornstein--Uhlenbeck limits.  It is deliberately
independent of a particular path-space model.

First, a uniformly tight sequence of probability laws converges once every
cluster point is identified with the same target.  Second, a family of
continuous pushforwards identifies every cluster point if those pushforwards
converge and the family determines probability measures.  The combination is
the standard ``tightness + finite-dimensional distributions'' compiler; the
remaining model-specific obligation is precisely to prove tightness and that
the chosen cylinder maps determine laws on the selected path space.
-/

open Filter Set Topology
open MeasureTheory

namespace NCG
namespace TightMeasureMarginalConvergence

variable {Path : Type*}
variable [MeasurableSpace Path] [TopologicalSpace Path]
variable [T2Space Path] [BorelSpace Path] [HasOuterApproxClosed Path]

/-- Prokhorov compactness plus uniqueness of all cluster points upgrades a
tight sequence of probability measures to weak convergence. -/
theorem tendsto_of_tight_of_unique_clusterPoint
    (law : ℕ → ProbabilityMeasure Path) (limit : ProbabilityMeasure Path)
    (htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure Path) : Measure Path) | ν ∈ Set.range law})
    (hunique : ∀ ν : ProbabilityMeasure Path,
      MapClusterPt ν atTop law → ν = limit) :
    Tendsto law atTop (𝓝 limit) := by
  have hcompact : IsCompact (closure (Set.range law)) :=
    isCompact_closure_of_isTightMeasureSet htight
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
  · exact Eventually.of_forall fun n =>
      subset_closure (Set.mem_range_self n)
  · intro ν _ hν
    exact hunique ν hν

variable {Marginal Index : Type*}
variable [MeasurableSpace Marginal] [TopologicalSpace Marginal]
variable [T2Space Marginal] [BorelSpace Marginal]
variable [HasOuterApproxClosed Marginal]

/-- A convergence-determining family of continuous marginals identifies every
weak cluster point of a sequence whose marginal laws converge. -/
theorem clusterPoint_eq_of_determining_marginals
    (law : ℕ → ProbabilityMeasure Path) (limit ν : ProbabilityMeasure Path)
    (observe : Index → Path → Marginal)
    (hcontinuous : ∀ i, Continuous (observe i))
    (hmarginal : ∀ i,
      Tendsto
        (fun n => (law n).map
          (hcontinuous i).measurable.aemeasurable)
        atTop
        (𝓝 (limit.map (hcontinuous i).measurable.aemeasurable)))
    (hdetermines : ∀ η : ProbabilityMeasure Path,
      (∀ i,
        η.map (hcontinuous i).measurable.aemeasurable =
          limit.map (hcontinuous i).measurable.aemeasurable) →
      η = limit)
    (hν : MapClusterPt ν atTop law) :
    ν = limit := by
  apply hdetermines ν
  intro i
  let push : ProbabilityMeasure Path → ProbabilityMeasure Marginal :=
    fun η => η.map (hcontinuous i).measurable.aemeasurable
  have hpushContinuous : Continuous push :=
    ProbabilityMeasure.continuous_map (hcontinuous i)
  have hcluster : MapClusterPt (push ν) atTop (push ∘ law) :=
    hν.tendsto_comp hpushContinuous.continuousAt
  have hclusterAtLimit :
      ClusterPt (push ν) (𝓝 (push limit)) := by
    exact hcluster.clusterPt.mono (hmarginal i)
  exact eq_of_nhds_neBot hclusterAtLimit.neBot

/-- **Tightness plus determining marginals.**  If the laws are uniformly
tight, every selected continuous marginal converges to the target marginal,
and equality of all selected marginals determines a law, then the full laws
converge weakly to the target. -/
theorem tendsto_of_tight_of_determining_marginals
    (law : ℕ → ProbabilityMeasure Path) (limit : ProbabilityMeasure Path)
    (observe : Index → Path → Marginal)
    (hcontinuous : ∀ i, Continuous (observe i))
    (htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure Path) : Measure Path) | ν ∈ Set.range law})
    (hmarginal : ∀ i,
      Tendsto
        (fun n => (law n).map
          (hcontinuous i).measurable.aemeasurable)
        atTop
        (𝓝 (limit.map (hcontinuous i).measurable.aemeasurable)))
    (hdetermines : ∀ η : ProbabilityMeasure Path,
      (∀ i,
        η.map (hcontinuous i).measurable.aemeasurable =
          limit.map (hcontinuous i).measurable.aemeasurable) →
      η = limit) :
    Tendsto law atTop (𝓝 limit) := by
  apply tendsto_of_tight_of_unique_clusterPoint law limit htight
  intro ν hν
  exact clusterPoint_eq_of_determining_marginals law limit ν observe
    hcontinuous hmarginal hdetermines hν

/-! ## Process laws on a product path space -/

section ProductPath

variable {Time State : Type*}
variable [MeasurableSpace State]

/-- Probability laws on a coordinate process are determined by all of their
finite-coordinate restrictions.  This is the exact cylinder uniqueness step,
proved using Mathlib's projective-limit uniqueness theorem. -/
theorem probabilityMeasure_eq_of_finite_restriction_laws
    (μ ν : ProbabilityMeasure (Time → State))
    (hfinite : ∀ I : Finset Time,
      (μ : Measure (Time → State)).map I.restrict =
        (ν : Measure (Time → State)).map I.restrict) :
    μ = ν := by
  let P : ∀ I : Finset Time, Measure (I → State) :=
    fun I => (μ : Measure (Time → State)).map I.restrict
  have hμ : IsProjectiveLimit (μ : Measure (Time → State)) P := by
    intro I
    rfl
  have hν : IsProjectiveLimit (ν : Measure (Time → State)) P := by
    intro I
    exact (hfinite I).symm
  apply Subtype.ext
  exact hμ.unique hν

variable [TopologicalSpace State] [T2Space State] [BorelSpace State]
variable [HasOuterApproxClosed State]
variable [SecondCountableTopology State]
variable [BorelSpace (Time → State)]
variable [HasOuterApproxClosed (Time → State)]
variable [∀ I : Finset Time, HasOuterApproxClosed (I → State)]

/-- On the product path space, tightness and convergence of every finite
coordinate law imply weak convergence of the full process laws.  In contrast
to an abstract determining-family hypothesis, cylinder determination is
discharged here by `probabilityMeasure_eq_of_finite_restriction_laws`. -/
theorem tendsto_productPath_laws_of_tight_of_finiteDimensional
    (law : ℕ → ProbabilityMeasure (Time → State))
    (limit : ProbabilityMeasure (Time → State))
    (htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure (Time → State)) : Measure (Time → State)) |
        ν ∈ Set.range law})
    (hmarginal : ∀ I : Finset Time,
      let restrictContinuous : Continuous
          (I.restrict : (Time → State) → (I → State)) :=
        by fun_prop
      Tendsto
        (fun n => (law n).map
          restrictContinuous.measurable.aemeasurable)
        atTop
        (𝓝 (limit.map restrictContinuous.measurable.aemeasurable))) :
    Tendsto law atTop (𝓝 limit) := by
  apply tendsto_of_tight_of_unique_clusterPoint law limit htight
  intro ν hν
  apply probabilityMeasure_eq_of_finite_restriction_laws ν limit
  intro I
  let restrictContinuous : Continuous
      (I.restrict : (Time → State) → (I → State)) :=
    by fun_prop
  let push : ProbabilityMeasure (Time → State) →
      ProbabilityMeasure (I → State) :=
    fun η => η.map restrictContinuous.measurable.aemeasurable
  have hpushContinuous : Continuous push :=
    ProbabilityMeasure.continuous_map restrictContinuous
  have hcluster : MapClusterPt (push ν) atTop (push ∘ law) :=
    hν.tendsto_comp hpushContinuous.continuousAt
  have hclusterAtLimit : ClusterPt (push ν) (𝓝 (push limit)) := by
    exact hcluster.clusterPt.mono (hmarginal I)
  have heq : push ν = push limit :=
    eq_of_nhds_neBot hclusterAtLimit.neBot
  simpa [push] using congrArg ProbabilityMeasure.toMeasure heq

end ProductPath

end TightMeasureMarginalConvergence
end NCG
