/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Exact geometry short of the accepted Store source
  (`thm:SM-active-residual-short`,
  Gran-Tensor manuscript)

* `sm_active_residual_short`: the boxed SM.0e — on an
  arbitrary historical common carrier the shorted internal
  Gram is
  `G_{int|ST} = θI - C_ext*D_ext⁻¹C_ext ⪰ 0`
  (Schur-complement positivity of the assembled block
  Gram), and the boxed SM.0d is historical exactly when
  `C_ext = 0`: `G_{int|ST} = θI ⟺ C_ext = 0` (through the
  positive square root of `D⁻¹`).

The locked-branch isometry SM.0b (`S*S = θI`), the
categorical allocation SM.0c, the statement that the
explicit active spacetime completion routes all additional
geometric directions through the independently adjoined
relational port (making SM.0d exact there), and the
multiplicity-free `S₄ × ⟨ι⟩` decomposition SM.0f (whose
odd standard block is the endpoint quotient of
`thm:dimension-locked-K4-source`) are the manuscript's
construction and census layers.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `thm:SM-active-residual-short` (SM.0d–SM.0e). -/
theorem sm_active_residual_short {k d : Type} [Fintype k]
    [Fintype d] [DecidableEq k] [DecidableEq d]
    (θ : ℝ) (C : Matrix d k ℂ) (D : Matrix d d ℂ)
    (hD : D.PosDef)
    (hG : (fromBlocks ((θ : ℂ) • 1) Cᴴ C D).PosSemidef) :
    -- the boxed SM.0e shorted residual Gram
    (((θ : ℂ) • 1 - Cᴴ * D⁻¹ * C).PosSemidef)
    -- the boxed SM.0d exactness criterion
    ∧ ((θ : ℂ) • 1 - Cᴴ * D⁻¹ * C = (θ : ℂ) • 1
        ↔ C = 0) := by
  haveI : Invertible D := hD.isUnit.invertible
  have hG' : (fromBlocks ((θ : ℂ) • 1) Cᴴ Cᴴᴴ
      D).PosSemidef := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hG
  have hschur : ((θ : ℂ) • 1
      - Cᴴ * D⁻¹ * Cᴴᴴ).PosSemidef :=
    (Matrix.PosDef.fromBlocks₂₂ ((θ : ℂ) • 1) Cᴴ
      hD).mp hG'
  rw [Matrix.conjTranspose_conjTranspose] at hschur
  refine ⟨hschur, ?_⟩
  rw [sub_eq_self]
  constructor
  · intro hzero
    -- factor through the positive square root of D⁻¹
    have hDinv : D⁻¹.PosDef := hD.inv
    have hQ : CFC.sqrt D⁻¹ * CFC.sqrt D⁻¹ = D⁻¹ :=
      sqrt_mul_self_eq D⁻¹ hDinv.posSemidef
    have hQH : (CFC.sqrt D⁻¹)ᴴ = CFC.sqrt D⁻¹ :=
      sqrt_isHermitian D⁻¹
    have hfact : Cᴴ * D⁻¹ * C
        = (CFC.sqrt D⁻¹ * C)ᴴ * (CFC.sqrt D⁻¹ * C) := by
      rw [Matrix.conjTranspose_mul, hQH]
      calc Cᴴ * D⁻¹ * C
          = Cᴴ * (CFC.sqrt D⁻¹
              * (CFC.sqrt D⁻¹ * C)) := by
            rw [← Matrix.mul_assoc (CFC.sqrt D⁻¹), hQ]
            simp only [Matrix.mul_assoc]
        _ = Cᴴ * CFC.sqrt D⁻¹ * (CFC.sqrt D⁻¹ * C) := by
            simp only [Matrix.mul_assoc]
    rw [hfact] at hzero
    have hQC : CFC.sqrt D⁻¹ * C = 0 :=
      Matrix.conjTranspose_mul_self_eq_zero.mp hzero
    have hunit : IsUnit (CFC.sqrt D⁻¹) :=
      sqrt_isUnit hDinv
    haveI := hunit.invertible
    calc C = (CFC.sqrt D⁻¹)⁻¹
        * (CFC.sqrt D⁻¹ * C) :=
          (Matrix.inv_mul_cancel_left_of_invertible
            _ _).symm
      _ = 0 := by rw [hQC, Matrix.mul_zero]
  · rintro rfl
    simp

end NCG
