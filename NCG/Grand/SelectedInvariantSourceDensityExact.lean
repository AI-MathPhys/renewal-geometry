/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MeasurableRecordProjectionExact
import NCG.Grand.InvariantVacuumOrthogonalCenteringExact

/-!
# Retained-record selection and centering of invariant source families

The selected sector is defined by two independent requirements: invariance
under the actual measure-preserving transformations, and vanishing outside
the retained measurable event. Its density is derived by applying the actual
indicator projection to the full invariant source family. Centering removes
the selected vacuum line only after record selection.
-/

open MeasureTheory Set

namespace NCG.SelectedInvariantSourceDensity

open MeasurableRecordProjection InvariantVacuumOrthogonalCentering

noncomputable section

variable {X I : Type*} [MeasurableSpace X]
variable (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
variable (act : I → X → X) (hpres : ∀ i, MeasurePreserving (act i) μ μ)

def pullbackOperator (i : I) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (act i) (hpres i)).toContinuousLinearMap

def selectedOperators : Option I → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ
  | none => selection μ S hS
  | some i => pullbackOperator μ act hpres i

def selectedSector : Submodule ℂ (Lp ℂ 2 μ) :=
  fixedSubmodule (selectedOperators μ S hS act hpres)

theorem mem_selectedSector_iff (f : Lp ℂ 2 μ) :
    f ∈ selectedSector μ S hS act hpres ↔
      (∀ i, Lp.compMeasurePreserving (act i) (hpres i) f = f) ∧ select μ S hS f = f := by
  constructor
  · intro h
    exact ⟨fun i => h (some i), h none⟩
  · rintro ⟨hi, hs⟩
    rintro (_ | i)
    · exact hs
    · exact hi i

theorem mem_selectedSector_iff_supported_invariant (f : Lp ℂ 2 μ) :
    f ∈ selectedSector μ S hS act hpres ↔
      (∀ i, Lp.compMeasurePreserving (act i) (hpres i) f = f) ∧
        ∀ᵐ x ∂μ, x ∉ S → f x = 0 := by
  rw [mem_selectedSector_iff, select_eq_self_iff]

theorem isClosed_selectedSector : IsClosed (selectedSector μ S hS act hpres : Set (Lp ℂ 2 μ)) :=
  isClosed_fixedSubmodule _

variable (hinvariant : ∀ i x, act i x ∈ S ↔ x ∈ S)

include hinvariant

theorem select_mem_selectedSector (f : Lp ℂ 2 μ)
    (hf : ∀ i, Lp.compMeasurePreserving (act i) (hpres i) f = f) :
    select μ S hS f ∈ selectedSector μ S hS act hpres := by
  apply (mem_selectedSector_iff μ S hS act hpres _).mpr
  refine ⟨?_, select_idempotent μ S hS f⟩
  intro i
  rw [← select_commutes_pullback μ S hS (act i) (hpres i) (hinvariant i), hf i]

theorem selection_image_fixedSubmodule :
    selection μ S hS '' (fixedSubmodule (pullbackOperator μ act hpres) : Set (Lp ℂ 2 μ)) =
      (selectedSector μ S hS act hpres : Set (Lp ℂ 2 μ)) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact select_mem_selectedSector μ S hS act hpres hinvariant g hg
  · intro hf
    obtain ⟨hi, hs⟩ := (mem_selectedSector_iff μ S hS act hpres f).mp hf
    exact ⟨f, hi, hs⟩

theorem closure_selected_writers_eq_sector
    (writers : Set (Lp ℂ 2 μ))
    (hdense : closure writers = (fixedSubmodule (pullbackOperator μ act hpres) : Set (Lp ℂ 2 μ))) :
    closure (selection μ S hS '' writers) = (selectedSector μ S hS act hpres : Set (Lp ℂ 2 μ)) := by
  have h := closure_image_closure (selection μ S hS).continuous (s := writers)
  rw [hdense, selection_image_fixedSubmodule μ S hS act hpres hinvariant,
    (isClosed_selectedSector μ S hS act hpres).closure_eq] at h
  exact h.symm

/-- Selection precedes centering, so precisely the selected vacuum line is removed. -/
theorem closure_centered_selected_writers_eq_neutral
    (vacuum : Lp ℂ 2 μ)
    (hv : ∀ i, Lp.compMeasurePreserving (act i) (hpres i) vacuum = vacuum)
    (writers : Set (Lp ℂ 2 μ))
    (hdense : closure writers = (fixedSubmodule (pullbackOperator μ act hpres) : Set (Lp ℂ 2 μ))) :
    let selectedVacuum := select μ S hS vacuum
    closure ((Submodule.span ℂ {selectedVacuum})ᗮ.starProjection ''
      (selection μ S hS '' writers)) =
      (selectedSector μ S hS act hpres : Set (Lp ℂ 2 μ)) ∩
        ((Submodule.span ℂ {selectedVacuum})ᗮ : Set (Lp ℂ 2 μ)) := by
  exact closure_centered_eq_inter (selectedSector μ S hS act hpres)
    (isClosed_selectedSector μ S hS act hpres) (select μ S hS vacuum)
    (select_mem_selectedSector μ S hS act hpres hinvariant vacuum hv)
    (selection μ S hS '' writers)
    (closure_selected_writers_eq_sector μ S hS act hpres hinvariant writers hdense)

end

end NCG.SelectedInvariantSourceDensity
