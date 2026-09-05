/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact

/-!
# Kolmogorov extension for finite-state projective families

Every measurable cylinder in a product of finite discrete spaces is clopen.
Compactness therefore turns countable cylinder covers into finite covers,
which proves sigma-subadditivity of the canonical projective-family content.
Caratheodory extension then produces a genuine process measure with exactly
the prescribed finite-dimensional laws.
-/

open Set Filter Topology
open scoped ENNReal

noncomputable section

namespace NCG.FiniteStateProjectiveLimit

variable {ι : Type*} {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)] [∀ i, DiscreteTopology (X i)]
  [∀ i, CompactSpace (X i)] [∀ i, MeasurableSpace (X i)]

/-- Measurable cylinders over a finite discrete state space are open. -/
theorem isOpen_of_mem_measurableCylinders
    {s : Set (∀ i, X i)}
    (hs : s ∈ MeasureTheory.measurableCylinders X) :
    IsOpen s := by
  obtain ⟨I, t, _ht, rfl⟩ :=
    (MeasureTheory.mem_measurableCylinders _).mp hs
  have hdisc : @DiscreteTopology (∀ i : I, X i) Pi.topologicalSpace :=
    Pi.discreteTopology
  rw [MeasureTheory.cylinder]
  exact (discreteTopology_iff_forall_isOpen.mp hdisc t).preimage (by fun_prop)

/-- Measurable cylinders over a finite discrete state space are closed. -/
theorem isClosed_of_mem_measurableCylinders
    {s : Set (∀ i, X i)}
    (hs : s ∈ MeasureTheory.measurableCylinders X) :
    IsClosed s := by
  obtain ⟨I, t, _ht, rfl⟩ :=
    (MeasureTheory.mem_measurableCylinders _).mp hs
  have hdisc : @DiscreteTopology (∀ i : I, X i) Pi.topologicalSpace :=
    Pi.discreteTopology
  rw [MeasureTheory.cylinder]
  exact (discreteTopology_iff_forall_isClosed.mp hdisc t).preimage (by fun_prop)

/-- The canonical content of a projective family of finite-state laws is
sigma-subadditive. -/
theorem projectiveFamilyContent_isSigmaSubadditive
    (P : ∀ J : Finset ι, MeasureTheory.Measure (∀ j : J, X j))
    (hP : MeasureTheory.IsProjectiveMeasureFamily P) :
    (MeasureTheory.projectiveFamilyContent hP).IsSigmaSubadditive := by
  intro f hf hUnion
  let m := MeasureTheory.projectiveFamilyContent hP
  have hcompact : IsCompact (⋃ n, f n) :=
    (isClosed_of_mem_measurableCylinders hUnion).isCompact
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover f
    (fun n => isOpen_of_mem_measurableCylinders (hf n))
    (by exact Set.Subset.rfl)
  have hfinite : (⋃ n ∈ t, f n) ∈
      MeasureTheory.measurableCylinders X :=
    MeasureTheory.isSetRing_measurableCylinders.biUnion_mem t
      (fun n _ => hf n)
  calc
    m (⋃ n, f n) ≤ m (⋃ n ∈ t, f n) :=
      MeasureTheory.projectiveFamilyContent_mono hP hUnion hfinite ht
    _ ≤ ∑ n ∈ t, m (f n) :=
      MeasureTheory.addContent_biUnion_le
        MeasureTheory.isSetRing_measurableCylinders
        (fun n _ => hf n)
    _ ≤ ∑' n, m (f n) := ENNReal.sum_le_tsum t

/-- The genuine product-space measure extending a projective family of
finite-state finite-dimensional laws. -/
def projectiveLimitMeasure
    (P : ∀ J : Finset ι, MeasureTheory.Measure (∀ j : J, X j))
    (hP : MeasureTheory.IsProjectiveMeasureFamily P) :
    MeasureTheory.Measure (∀ i, X i) :=
  (MeasureTheory.projectiveFamilyContent hP).measure
    MeasureTheory.isSetSemiring_measurableCylinders
    (by
      rw [MeasureTheory.generateFrom_measurableCylinders])
    (projectiveFamilyContent_isSigmaSubadditive P hP)

/-- The constructed measure has exactly the prescribed finite-dimensional
marginals. -/
theorem projectiveLimitMeasure_isProjectiveLimit
    (P : ∀ J : Finset ι, MeasureTheory.Measure (∀ j : J, X j))
    (hP : MeasureTheory.IsProjectiveMeasureFamily P) :
    MeasureTheory.IsProjectiveLimit (projectiveLimitMeasure P hP) P := by
  intro I
  apply MeasureTheory.Measure.ext
  intro s hs
  rw [MeasureTheory.Measure.map_apply (by fun_prop) hs]
  change (projectiveLimitMeasure P hP)
      (MeasureTheory.cylinder I s) = P I s
  unfold projectiveLimitMeasure
  rw [MeasureTheory.AddContent.measure_eq]
  · exact MeasureTheory.projectiveFamilyContent_cylinder hP hs
  · exact MeasureTheory.generateFrom_measurableCylinders.symm
  · exact (MeasureTheory.mem_measurableCylinders _).mpr
      ⟨I, s, hs, rfl⟩

/-- A projective family of probability laws extends to a probability law on
the full coordinate process. -/
theorem exists_probability_projectiveLimit
    (P : ∀ J : Finset ι, MeasureTheory.Measure (∀ j : J, X j))
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    [∀ J, MeasureTheory.IsProbabilityMeasure (P J)] :
    ∃ μ : MeasureTheory.Measure (∀ i, X i),
      MeasureTheory.IsProbabilityMeasure μ ∧
      MeasureTheory.IsProjectiveLimit μ P := by
  let μ := projectiveLimitMeasure P hP
  have hlim : MeasureTheory.IsProjectiveLimit μ P :=
    projectiveLimitMeasure_isProjectiveLimit P hP
  letI : MeasureTheory.IsProbabilityMeasure μ := hlim.isProbabilityMeasure
  exact ⟨μ, inferInstance, hlim⟩

end NCG.FiniteStateProjectiveLimit
