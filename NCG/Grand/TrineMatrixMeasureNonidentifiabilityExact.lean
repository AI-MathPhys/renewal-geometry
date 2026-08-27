/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCalibrationAndDynamicalCounterexamples
import Mathlib.MeasureTheory.VectorMeasure.Basic

/-!
# Trine matrix-measure nonidentifiability

The pointwise two-by-two witness is promoted here to a genuine matrix-valued vector measure.
On a one-atom probability space, every population parameter in `[0,1]` gives a positive matrix
measure.  All members have the same trace and off-diagonal measures, while evaluation on the atom
recovers the population parameter.  Since the parameter interval is infinite, this closes the
measure-level clause of `cth:GT-trine-no-full-matrix`.
-/

open Matrix MeasureTheory

namespace NCG.TrineMatrixMeasureNonidentifiability

abbrev ArmMatrix := Matrix (Fin 2) (Fin 2) ℝ
abbrev ArmMatrixMeasure := VectorMeasure Unit ArmMatrix

/-- The atomic positive matrix-valued measure with first-arm population `a`. -/
noncomputable def armPopulationMeasure (a : ℝ) : ArmMatrixMeasure :=
  VectorMeasure.dirac ()
    (FiniteCalibrationAndDynamicalCounterexamples.armPopulationMatrix a)

lemma armPopulationMatrix_posSemidef {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (FiniteCalibrationAndDynamicalCounterexamples.armPopulationMatrix a).PosSemidef := by
  rw [show FiniteCalibrationAndDynamicalCounterexamples.armPopulationMatrix a =
      Matrix.diagonal ![a, 1 - a] by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [FiniteCalibrationAndDynamicalCounterexamples.armPopulationMatrix]]
  exact Matrix.PosSemidef.diagonal (by
    intro i
    fin_cases i <;> simp [ha0, sub_nonneg.mpr ha1])

/-- Every measurable value of the atomic matrix measure is positive semidefinite. -/
theorem armPopulationMeasure_posSemidef {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (s : Set Unit) (hs : MeasurableSet s) :
    (armPopulationMeasure a s).PosSemidef := by
  by_cases hmem : () ∈ s
  · simpa [armPopulationMeasure, VectorMeasure.dirac_apply_of_mem hs hmem] using
      armPopulationMatrix_posSemidef ha0 ha1
  · rw [armPopulationMeasure, VectorMeasure.dirac_apply_of_notMem hmem]
    exact Matrix.PosSemidef.zero

/-- Trace and off-diagonal evaluations are independent of the arm population. -/
theorem armPopulationMeasure_same_target {a b : ℝ}
    (s : Set Unit) (hs : MeasurableSet s) :
    Matrix.trace (armPopulationMeasure a s) = Matrix.trace (armPopulationMeasure b s) ∧
      armPopulationMeasure a s 0 1 = armPopulationMeasure b s 0 1 := by
  by_cases hmem : () ∈ s
  · simp [armPopulationMeasure, VectorMeasure.dirac_apply_of_mem hs hmem,
      FiniteCalibrationAndDynamicalCounterexamples.armPopulationMatrix,
      Matrix.trace, Fin.sum_univ_two]
  · simp [armPopulationMeasure, VectorMeasure.dirac_apply_of_notMem hmem]

/-- Evaluation on the atom recovers the first diagonal population, so the family is injective. -/
theorem armPopulationMeasure_injective : Function.Injective armPopulationMeasure := by
  intro a b hab
  have hvalue := congrArg (fun μ : ArmMatrixMeasure => μ Set.univ) hab
  have hentry := congrFun (congrFun hvalue 0) 0
  simpa [armPopulationMeasure,
    FiniteCalibrationAndDynamicalCounterexamples.armPopulationMatrix] using hentry

/-- Exact measure-level form of `cth:GT-trine-no-full-matrix`: on a set of positive base measure
where `g = 0` and hence `4|g|² < 1`, infinitely many distinct positive matrix-valued measures have
the same trace/off-diagonal target and different diagonal populations. -/
theorem infinitely_many_positive_matrix_measures_same_trine_target :
    Set.Infinite (Set.Icc (0 : ℝ) 1) ∧
    Function.Injective
      (fun a : Set.Icc (0 : ℝ) 1 => armPopulationMeasure a.1) ∧
    (∀ a : Set.Icc (0 : ℝ) 1, ∀ s : Set Unit, MeasurableSet s →
      (armPopulationMeasure a.1 s).PosSemidef) ∧
    (∀ a b : Set.Icc (0 : ℝ) 1, ∀ s : Set Unit, MeasurableSet s →
      Matrix.trace (armPopulationMeasure a.1 s) =
          Matrix.trace (armPopulationMeasure b.1 s) ∧
        armPopulationMeasure a.1 s 0 1 = armPopulationMeasure b.1 s 0 1) ∧
    (Measure.dirac () : Measure Unit) Set.univ = 1 ∧
    4 * |(0 : ℝ)| ^ 2 < 1 := by
  refine ⟨Set.Icc_infinite (by norm_num), ?_, ?_, ?_, by simp, by norm_num⟩
  · exact armPopulationMeasure_injective.comp Subtype.val_injective
  · intro a s hs
    exact armPopulationMeasure_posSemidef a.2.1 a.2.2 s hs
  · intro a b s hs
    exact armPopulationMeasure_same_target s hs

end NCG.TrineMatrixMeasureNonidentifiability
