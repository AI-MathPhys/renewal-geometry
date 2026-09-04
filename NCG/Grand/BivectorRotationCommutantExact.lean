/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The spatial-rotation commutant on electric and magnetic bivectors

Two explicit proper spatial rotations already force every 3 by 3 intertwiner
to be scalar. On the two copies of the vector representation this leaves a
2 by 2 matrix of scalar blocks. No irreducibility or commutant classification
is assumed.
-/

open Matrix
open scoped BigOperators

namespace NCG.BivectorRotationCommutant

noncomputable section

abbrev BivectorIndex := Fin 2 × Fin 3

def spatialCycle : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

def spatialHalfTurn : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, -1, 0; 0, 0, -1]

theorem spatial_commutant_scalar (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hhalf : A * spatialHalfTurn = spatialHalfTurn * A)
    (hcycle : A * spatialCycle = spatialCycle * A) :
    A = A 0 0 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h01 := congrFun (congrFun hhalf 0) 1
  have h02 := congrFun (congrFun hhalf 0) 2
  have h10 := congrFun (congrFun hhalf 1) 0
  have h20 := congrFun (congrFun hhalf 2) 0
  have h12 := congrFun (congrFun hcycle 1) 1
  have h21 := congrFun (congrFun hcycle 0) 1
  have h11 := congrFun (congrFun hcycle 1) 0
  have h22 := congrFun (congrFun hcycle 2) 1
  norm_num [spatialHalfTurn, spatialCycle, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.cons_val_two]
    at h01 h02 h10 h20 h12 h21 h11 h22
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.one_apply] <;> linarith

def block (T : Matrix BivectorIndex BivectorIndex ℝ) (a b : Fin 2) :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j => T (a, i) (b, j)

def doubledRotation (R : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix BivectorIndex BivectorIndex ℝ :=
  fun ai bj => if ai.1 = bj.1 then R ai.2 bj.2 else 0

def scalarBlocks (C : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix BivectorIndex BivectorIndex ℝ :=
  fun ai bj => C ai.1 bj.1 * (if ai.2 = bj.2 then 1 else 0)

theorem block_mul_doubledRotation (T : Matrix BivectorIndex BivectorIndex ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 2) :
    block (T * doubledRotation R) a b = block T a b * R := by
  ext i j
  fin_cases a <;> fin_cases b <;>
    simp [block, doubledRotation, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem block_doubledRotation_mul (T : Matrix BivectorIndex BivectorIndex ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 2) :
    block (doubledRotation R * T) a b = R * block T a b := by
  ext i j
  fin_cases a <;> fin_cases b <;>
    simp [block, doubledRotation, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem rotation_commutant_scalar_blocks (T : Matrix BivectorIndex BivectorIndex ℝ)
    (hhalf : T * doubledRotation spatialHalfTurn = doubledRotation spatialHalfTurn * T)
    (hcycle : T * doubledRotation spatialCycle = doubledRotation spatialCycle * T) :
    T = scalarBlocks (fun a b => T (a, 0) (b, 0)) := by
  have hblock (a b : Fin 2) : block T a b = T (a, 0) (b, 0) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    have h1 := congrArg (fun M => block M a b) hhalf
    have h2 := congrArg (fun M => block M a b) hcycle
    rw [block_mul_doubledRotation, block_doubledRotation_mul] at h1 h2
    exact spatial_commutant_scalar (block T a b) h1 h2
  ext ⟨a, i⟩ ⟨b, j⟩
  have h := congrFun (congrFun (hblock a b) i) j
  simpa only [block, scalarBlocks, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] using h

theorem scalarBlocks_commutes_doubledRotation (C : Matrix (Fin 2) (Fin 2) ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) :
    scalarBlocks C * doubledRotation R = doubledRotation R * scalarBlocks C := by
  ext ⟨a, i⟩ ⟨b, j⟩
  have h1 := congrFun (congrFun (block_mul_doubledRotation (scalarBlocks C) R a b) i) j
  have h2 := congrFun (congrFun (block_doubledRotation_mul (scalarBlocks C) R a b) i) j
  change (scalarBlocks C * doubledRotation R) (a, i) (b, j) = _ at h1
  change (doubledRotation R * scalarBlocks C) (a, i) (b, j) = _ at h2
  rw [h1, h2]
  simp [block, scalarBlocks, Matrix.mul_apply, mul_ite, ite_mul, mul_comm]

end

end NCG.BivectorRotationCommutant
