/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Navier--Stokes dissipation-defect measure

On a compact cylinder the absolutely continuous limiting dissipation measure
is finite.  If weak lower semicontinuity places it below the weak-* limit of
the approximating dissipation measures, their ordered measure difference is a
nonnegative Radon-measure candidate and gives the exact NS.20 ledger
decomposition.
-/

open MeasureTheory

noncomputable section

namespace NCG.NavierStokesDissipationDefectMeasure

variable {X : Type*} [MeasurableSpace X]

/-- The positive dissipation defect: total limiting dissipation minus the
absolutely continuous dissipation of the weak limit. -/
def dissipationDefect (totalLimit absolutelyContinuous : Measure X) : Measure X :=
  totalLimit - absolutelyContinuous

/-- Weak lower semicontinuity (`absolutelyContinuous ≤ totalLimit`) gives the
exact measure ledger `totalLimit = absolutelyContinuous + defect`. -/
theorem absolutelyContinuous_add_defect
    (totalLimit absolutelyContinuous : Measure X)
    [IsFiniteMeasure absolutelyContinuous]
    (hlower : absolutelyContinuous ≤ totalLimit) :
    absolutelyContinuous + dissipationDefect totalLimit absolutelyContinuous =
      totalLimit := by
  rw [dissipationDefect, add_comm]
  exact Measure.sub_add_cancel_of_le hlower

/-- The defect is a nonnegative measure by construction. -/
theorem defect_nonnegative
    (totalLimit absolutelyContinuous : Measure X) :
    0 ≤ dissipationDefect totalLimit absolutelyContinuous :=
  Measure.zero_le _

/-- On measurable sets, the defect has the expected scalar difference when
the absolutely continuous component is finite. -/
theorem defect_apply
    (totalLimit absolutelyContinuous : Measure X)
    [IsFiniteMeasure absolutelyContinuous]
    (hlower : absolutelyContinuous ≤ totalLimit)
    {s : Set X} (hs : MeasurableSet s) :
    dissipationDefect totalLimit absolutelyContinuous s =
      totalLimit s - absolutelyContinuous s := by
  exact Measure.sub_apply hs hlower

/-- The defect vanishes exactly when the lower-semicontinuity comparison is
an equality, in the forward direction needed by the no-defect branch. -/
theorem defect_eq_zero_of_eq
    (totalLimit absolutelyContinuous : Measure X)
    (h : totalLimit = absolutelyContinuous) :
    dissipationDefect totalLimit absolutelyContinuous = 0 := by
  rw [dissipationDefect, h]
  exact Measure.sub_self

end NCG.NavierStokesDissipationDefectMeasure
