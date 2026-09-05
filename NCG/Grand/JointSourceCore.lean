/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Mutual range tests and the corrected Douglas factor
  (`thm:joint-source-short`, `thm:corrected-Douglas-factor`,
   Gran-Tensor manuscript)

* `joint_source_short`: the boxed Schur residual identity
  `R_{1|2} = G₁ - C₂₁ᴴG₂⁻¹C₂₁ = S₁ᴴ(I - Π₂)S₁ ⪰ 0` for the
  range projection `Π₂ = S₂G₂⁻¹S₂ᴴ`, with vanishing exactly on
  the range inclusion `(I - Π₂)S₁ = 0`.
* `corrected_douglas_factor`: when the residual vanishes, the
  boxed reduced factor `D = G₂⁻¹C₂₁` satisfies `S₁ = S₂D` and
  the boxed Gram-norm isometry `DᴴG₂D = G₁`.

Rendering disclosed: the Grams are rendered invertible
(faithful sources); the pseudo-inverse general case, the
principal-angle description of the normalized transport, the
Anderson–Trapp short display, and the order-equivalence clause
`S₁S₁* ⪯ S₂S₂* ↔ ∃ contraction factor` are the manuscript's
remaining clauses over these identities; the mirror residual
`R_{2|1}` is the same statement with the families exchanged.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false

/-- `thm:joint-source-short`: the Schur residual is the
projected source Gram, positive, and vanishes exactly on the
range inclusion. -/
theorem joint_source_short {h e1 e2 : Type*} [Fintype h]
    [Fintype e1] [Fintype e2] [DecidableEq h] [DecidableEq e2]
    (S1 : Matrix h e1 ℂ) (S2 : Matrix h e2 ℂ)
    [Invertible (S2ᴴ * S2)] :
    (S1ᴴ * S1 - (S2ᴴ * S1)ᴴ * (S2ᴴ * S2)⁻¹ * (S2ᴴ * S1)
      = S1ᴴ * ((1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ) * S1))
    ∧ (S1ᴴ * S1
        - (S2ᴴ * S1)ᴴ * (S2ᴴ * S2)⁻¹ * (S2ᴴ * S1)).PosSemidef
    ∧ (S1ᴴ * S1 - (S2ᴴ * S1)ᴴ * (S2ᴴ * S2)⁻¹ * (S2ᴴ * S1) = 0
        ↔ (1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ) * S1 = 0) := by
  have hGherm : (S2ᴴ * S2)ᴴ = S2ᴴ * S2 := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hGinvherm : ((S2ᴴ * S2)⁻¹)ᴴ = (S2ᴴ * S2)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGherm]
  have hPherm : (1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ)ᴴ
      = 1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hGinvherm, Matrix.conjTranspose_conjTranspose]
    congr 1
    simp only [Matrix.mul_assoc]
  have hPidem : (1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ)
      * (1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ)
      = 1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ := by
    have hcore : S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ
        * (S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ)
        = S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ := by
      calc S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ
            * (S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ)
          = S2 * ((S2ᴴ * S2)⁻¹ * ((S2ᴴ * S2)
              * ((S2ᴴ * S2)⁻¹ * S2ᴴ))) := by
            simp only [Matrix.mul_assoc]
        _ = S2 * ((S2ᴴ * S2)⁻¹ * S2ᴴ) := by
            rw [show (S2ᴴ * S2) * ((S2ᴴ * S2)⁻¹ * S2ᴴ)
                = ((S2ᴴ * S2) * (S2ᴴ * S2)⁻¹) * S2ᴴ from by
              simp only [Matrix.mul_assoc],
              Matrix.mul_inv_of_invertible, Matrix.one_mul]
        _ = S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ := by
            simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [hcore]
    abel
  have hstep1 : S1ᴴ * S1
      - (S2ᴴ * S1)ᴴ * (S2ᴴ * S2)⁻¹ * (S2ᴴ * S1)
      = S1ᴴ * ((1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ) * S1) := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
    congr 1
    simp only [Matrix.mul_assoc]
  have hkey : S1ᴴ * S1
      - (S2ᴴ * S1)ᴴ * (S2ᴴ * S2)⁻¹ * (S2ᴴ * S1)
      = ((1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ) * S1)ᴴ
        * ((1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ) * S1) := by
    rw [hstep1, Matrix.conjTranspose_mul, hPherm]
    calc S1ᴴ * ((1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ) * S1)
        = S1ᴴ * (((1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ)
            * (1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ)) * S1) := by
          rw [hPidem]
      _ = S1ᴴ * (1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ)
            * ((1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ) * S1) := by
          simp only [Matrix.mul_assoc]
  refine ⟨hstep1, ?_, ?_⟩
  · rw [hkey]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [hkey]
    exact Matrix.conjTranspose_mul_self_eq_zero

/-- `thm:corrected-Douglas-factor`: on vanishing residual, the
reduced factor recovers the synthesis and is a Gram-norm
isometry. -/
theorem corrected_douglas_factor {h e1 e2 : Type*} [Fintype h]
    [Fintype e1] [Fintype e2] [DecidableEq h] [DecidableEq e2]
    (S1 : Matrix h e1 ℂ) (S2 : Matrix h e2 ℂ)
    [Invertible (S2ᴴ * S2)]
    (hres : (1 - S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ) * S1 = 0) :
    S2 * ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1)) = S1
    ∧ ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1))ᴴ * (S2ᴴ * S2)
        * ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1)) = S1ᴴ * S1 := by
  have hGherm : (S2ᴴ * S2)ᴴ = S2ᴴ * S2 := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hGinvherm : ((S2ᴴ * S2)⁻¹)ᴴ = (S2ᴴ * S2)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGherm]
  rw [Matrix.sub_mul, Matrix.one_mul] at hres
  have hPiS1 : S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ * S1 = S1 :=
    (sub_eq_zero.mp hres).symm
  have hA : S2 * ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1)) = S1 := by
    calc S2 * ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1))
        = S2 * (S2ᴴ * S2)⁻¹ * S2ᴴ * S1 := by
          simp only [Matrix.mul_assoc]
      _ = S1 := hPiS1
  refine ⟨hA, ?_⟩
  calc ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1))ᴴ * (S2ᴴ * S2)
      * ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1))
      = (S2ᴴ * S1)ᴴ * (((S2ᴴ * S2)⁻¹)ᴴ * ((S2ᴴ * S2)
          * ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1)))) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = (S2ᴴ * S1)ᴴ * ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1)) := by
        rw [hGinvherm, show (S2ᴴ * S2)
            * ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1))
            = ((S2ᴴ * S2) * (S2ᴴ * S2)⁻¹) * (S2ᴴ * S1) from by
          simp only [Matrix.mul_assoc],
          Matrix.mul_inv_of_invertible, Matrix.one_mul]
    _ = S1ᴴ * (S2 * ((S2ᴴ * S2)⁻¹ * (S2ᴴ * S1))) := by
        rw [Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]
    _ = S1ᴴ * S1 := by rw [hA]

end NCG
