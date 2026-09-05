/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ADMAudit
import NCG.Flagship.CrossTomography
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.SqrtPolar

/-!
# Normalized clock--geometry source residual

The singular Moore--Penrose projection, positivity, range criterion, and rank
increment are supplied by `exact_source_schur_residual`.  This file adds the
faithful-marginal normal form: the normalized cross Gram is a contraction and
the whitened residual is exactly `I - Cᴴ C`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false

/-- For faithful clock and geometry marginal Grams, whitening identifies the
source Schur residual with the defect of the principal-cosine contraction. -/
theorem clockGeometry_normalizedResidual_eq_contractionDefect
    {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
    [DecidableEq n] [DecidableEq m] [DecidableEq k]
    (Sclk : Matrix n m ℂ) (Sgeo : Matrix n k ℂ)
    (hA : (Sclkᴴ * Sclk).PosDef) (hD : (Sgeoᴴ * Sgeo).PosDef) :
    let A := Sclkᴴ * Sclk
    let B := Sclkᴴ * Sgeo
    let D := Sgeoᴴ * Sgeo
    let G := D - Bᴴ * A⁻¹ * B
    let C := (CFC.sqrt A)⁻¹ * B * (CFC.sqrt D)⁻¹
    ((1 : Matrix k k ℂ) - Cᴴ * C).PosSemidef ∧
      (CFC.sqrt D)⁻¹ * G * (CFC.sqrt D)⁻¹ = 1 - Cᴴ * C := by
  dsimp only
  let A : Matrix m m ℂ := Sclkᴴ * Sclk
  let B : Matrix m k ℂ := Sclkᴴ * Sgeo
  let D : Matrix k k ℂ := Sgeoᴴ * Sgeo
  let G : Matrix k k ℂ := D - Bᴴ * A⁻¹ * B
  let C : Matrix m k ℂ := (CFC.sqrt A)⁻¹ * B * (CFC.sqrt D)⁻¹
  haveI := hA.isUnit.invertible
  haveI := (sqrt_isUnit hA).invertible
  haveI := (sqrt_isUnit hD).invertible
  have hAi : (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ = A⁻¹ :=
    sqrt_inv_mul_sqrt_inv hA
  have hDone : (CFC.sqrt D)⁻¹ * D * (CFC.sqrt D)⁻¹ = 1 := by
    calc
      (CFC.sqrt D)⁻¹ * D * (CFC.sqrt D)⁻¹ =
          (CFC.sqrt D)⁻¹ * (CFC.sqrt D * CFC.sqrt D) *
            (CFC.sqrt D)⁻¹ := congrArg
              (fun X => (CFC.sqrt D)⁻¹ * X * (CFC.sqrt D)⁻¹)
              (sqrt_mul_self_eq D hD.posSemidef).symm
      _ = 1 := by
        simp only [Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
          Matrix.mul_inv_of_invertible, Matrix.one_mul, Matrix.mul_one]
  have hCHC : Cᴴ * C =
      (CFC.sqrt D)⁻¹ * Bᴴ * A⁻¹ * B * (CFC.sqrt D)⁻¹ := by
    dsimp only [C]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      sqrt_inv_isHermitian, sqrt_inv_isHermitian]
    change ((CFC.sqrt D)⁻¹ * (Bᴴ * (CFC.sqrt A)⁻¹)) *
        ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt D)⁻¹) =
      (CFC.sqrt D)⁻¹ * Bᴴ * A⁻¹ * B * (CFC.sqrt D)⁻¹
    calc
      ((CFC.sqrt D)⁻¹ * (Bᴴ * (CFC.sqrt A)⁻¹)) *
          ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt D)⁻¹)
        = (CFC.sqrt D)⁻¹ * Bᴴ *
            ((CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹) * B *
              (CFC.sqrt D)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (CFC.sqrt D)⁻¹ * Bᴴ * A⁻¹ * B *
              (CFC.sqrt D)⁻¹ := by rw [hAi]
  have hidentity : (CFC.sqrt D)⁻¹ * G * (CFC.sqrt D)⁻¹
      = 1 - Cᴴ * C := by
    dsimp only [G]
    rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [hDone, hCHC]
    simp only [Matrix.mul_assoc]
  have hG : G.PosSemidef := by
    have hschur := adm_gram_posSemidef Sclk Sgeo
      ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)
    rw [← adm_gram_identity Sclk Sgeo] at hschur
    exact hschur
  have hcontract := hG.conjTranspose_mul_mul_same (CFC.sqrt D)⁻¹
  rw [sqrt_inv_isHermitian, hidentity] at hcontract
  exact ⟨hcontract, hidentity⟩

end NCG
