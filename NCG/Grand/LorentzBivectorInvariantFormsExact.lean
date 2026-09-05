/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LorentzBivectorActionExact

/-!
# Natural bivector metric, wedge pairing and Lorentzian Hodge star

The exterior-square multiplication law is proved from the actual minors.
The induced metric and determinant wedge pairing then prove that every
proper Lorentz transformation commutes with Hodge star.
-/

open Matrix
open scoped BigOperators

namespace NCG.LorentzBivectorInvariantForms

open BivectorRotationCommutant LorentzBivectorAction

noncomputable section

def bivectorMetric : BivectorMatrix := scalarBlocks !![-1, 0; 0, 1]
def wedgePairing : BivectorMatrix := scalarBlocks !![0, 1; 1, 0]

theorem bivectorAction_mul (A B : SpacetimeMatrix) :
    bivectorAction (A * B) = bivectorAction A * bivectorAction B := by
  ext r s
  simp [bivectorAction, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_succ, framePair, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem bivectorAction_transpose (A : SpacetimeMatrix) :
    bivectorAction Aᵀ = (bivectorAction A)ᵀ := by
  ext r s
  simp [bivectorAction, Matrix.transpose_apply]
  ring

theorem bivectorAction_minkowskiMetric : bivectorAction minkowskiMetric = bivectorMetric := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [bivectorAction, minkowskiMetric, Matrix.diagonal_apply, bivectorMetric, scalarBlocks, framePair,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem bivectorMetric_squared : bivectorMetric * bivectorMetric = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [bivectorMetric, scalarBlocks, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_two]

theorem metric_mul_wedgePairing : bivectorMetric * wedgePairing = -hodgeStar := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [bivectorMetric, wedgePairing, hodgeStar, scalarBlocks, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_two]

theorem bivectorAction_preserves_metric (L : SpacetimeMatrix)
    (hL : Lᵀ * minkowskiMetric * L = minkowskiMetric) :
    (bivectorAction L)ᵀ * bivectorMetric * bivectorAction L = bivectorMetric := by
  rw [← bivectorAction_minkowskiMetric, ← bivectorAction_transpose,
    ← bivectorAction_mul, ← bivectorAction_mul, hL]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The wedge pairing transforms by the actual spacetime determinant. -/
theorem bivectorAction_wedgePairing (L : SpacetimeMatrix) :
    (bivectorAction L)ᵀ * wedgePairing * bivectorAction L = L.det • wedgePairing := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j
  all_goals norm_num [wedgePairing, scalarBlocks, bivectorAction, framePair,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals try ring
  all_goals simp [Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.submatrix,
    Fin.succAbove, Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.cons_val_three]
  all_goals norm_num
  all_goals ring

/-- Hodge naturality follows from the two actual invariant bilinear forms. -/
theorem hodgeStar_commutes_lorentz (L : SpacetimeMatrix)
    (hL : IsProperTimeOrientedLorentz L) :
    bivectorAction L * hodgeStar = hodgeStar * bivectorAction L := by
  let W := bivectorAction L
  have hQ : Wᵀ * bivectorMetric * W = bivectorMetric :=
    bivectorAction_preserves_metric L hL.1
  have hE : Wᵀ * wedgePairing * W = wedgePairing := by
    have he := bivectorAction_wedgePairing L
    rw [hL.2.1, one_smul] at he
    exact he
  have hleft : (bivectorMetric * Wᵀ * bivectorMetric) * W = 1 := by
    calc
      _ = bivectorMetric * (Wᵀ * bivectorMetric * W) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ, bivectorMetric_squared]
  have hright : W * (bivectorMetric * Wᵀ * bivectorMetric) = 1 :=
    Matrix.mul_eq_one_comm.mp hleft
  have hWQW : W * bivectorMetric * Wᵀ = bivectorMetric := by
    calc
      _ = (W * (bivectorMetric * Wᵀ * bivectorMetric)) * bivectorMetric := by
        simp only [Matrix.mul_assoc, bivectorMetric_squared, Matrix.mul_one]
      _ = bivectorMetric := by rw [hright, Matrix.one_mul]
  have hc : (bivectorMetric * wedgePairing) * W = W * (bivectorMetric * wedgePairing) := by
    calc
      _ = (W * bivectorMetric * Wᵀ) * wedgePairing * W := by rw [hWQW]
      _ = W * bivectorMetric * (Wᵀ * wedgePairing * W) := by simp only [Matrix.mul_assoc]
      _ = W * (bivectorMetric * wedgePairing) := by rw [hE, Matrix.mul_assoc]
  rw [metric_mul_wedgePairing] at hc
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_inj] at hc
  exact hc.symm

end

end NCG.LorentzBivectorInvariantForms
