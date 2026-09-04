/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BivectorRotationCommutantExact

/-!
# The actual Lorentz action on the six-dimensional bivector carrier

The action consists of the 2 by 2 minors of a spacetime matrix in the
oriented basis (01,02,03,23,31,12). The audit rotations and rational boost
are verified against the spacetime metric, determinant, and time orientation.
-/

open Matrix
open scoped BigOperators

namespace NCG.LorentzBivectorAction

open BivectorRotationCommutant

noncomputable section

abbrev SpacetimeMatrix := Matrix (Fin 4) (Fin 4) ℝ
abbrev BivectorMatrix := Matrix BivectorIndex BivectorIndex ℝ

def minkowskiMetric : SpacetimeMatrix := Matrix.diagonal ![-1, 1, 1, 1]

def IsProperTimeOrientedLorentz (L : SpacetimeMatrix) : Prop :=
  Lᵀ * minkowskiMetric * L = minkowskiMetric ∧ L.det = 1 ∧ 0 < L 0 0

def framePair (a : BivectorIndex) : Fin 4 × Fin 4 :=
  if a.1 = 0 then (0, ![1, 2, 3] a.2) else (![2, 3, 1] a.2, ![3, 1, 2] a.2)

/-- Exterior-square action, with no inferred or supplied representation matrix. -/
def bivectorAction (L : SpacetimeMatrix) : BivectorMatrix := fun r s =>
  L (framePair r).1 (framePair s).1 * L (framePair r).2 (framePair s).2 -
    L (framePair r).1 (framePair s).2 * L (framePair r).2 (framePair s).1

def cycleRotation : SpacetimeMatrix :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

def halfTurnRotation : SpacetimeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

def rationalBoost : SpacetimeMatrix :=
  !![5 / 4, 3 / 4, 0, 0; 3 / 4, 5 / 4, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem cycleRotation_lorentz : IsProperTimeOrientedLorentz cycleRotation := by
  refine ⟨?_, ?_, by norm_num [cycleRotation]⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cycleRotation, minkowskiMetric, Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [cycleRotation, Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.submatrix,
      Fin.succAbove, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> rfl

theorem halfTurnRotation_lorentz : IsProperTimeOrientedLorentz halfTurnRotation := by
  refine ⟨?_, ?_, by norm_num [halfTurnRotation]⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [halfTurnRotation, minkowskiMetric, Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [halfTurnRotation, Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.submatrix,
      Fin.succAbove, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem rationalBoost_lorentz : IsProperTimeOrientedLorentz rationalBoost := by
  refine ⟨?_, ?_, by norm_num [rationalBoost]⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rationalBoost, minkowskiMetric, Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [rationalBoost, Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.submatrix,
      Fin.succAbove, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three]
    change (25 / 16 : ℝ) + -(3 / 4 * (3 / 4 * 1)) = 1
    norm_num

theorem bivectorAction_cycleRotation :
    bivectorAction cycleRotation = doubledRotation spatialCycle := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [bivectorAction, framePair, cycleRotation, doubledRotation, spatialCycle,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem bivectorAction_halfTurnRotation :
    bivectorAction halfTurnRotation = doubledRotation spatialHalfTurn := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [bivectorAction, framePair, halfTurnRotation, doubledRotation, spatialHalfTurn,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- Lorentzian Hodge star in the oriented electric/magnetic basis. -/
def hodgeStar : BivectorMatrix := scalarBlocks !![0, 1; -1, 0]

theorem hodgeStar_squared : hodgeStar * hodgeStar = -1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [hodgeStar, scalarBlocks, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_two]

end

end NCG.LorentzBivectorAction
