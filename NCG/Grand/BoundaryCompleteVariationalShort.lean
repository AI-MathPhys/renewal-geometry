/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTBoundaryShort
import NCG.Grand.GRHRestoringShortExact
import NCG.Grand.SampledVersusKilledExact

/-!
# Variational assembly of the boundary-complete short

The earlier boundary module proved the normal equation and Woodbury identity.
Here they are assembled with the literal complete block action, its Schur
complement, the two-stage minimizing correction, and the completion-of-square
identity which certifies the infimum in the manuscript definition.
-/

open Matrix
open scoped ComplexOrder
open NCG.SourceCoercivityInfluence NCG.PsdBlockSchur
  NCG.GRHRestoringShort

namespace NCG

section BoundaryComplete

variable {H T b : Type} [Fintype H] [Fintype T] [Fintype b]
  [DecidableEq H] [DecidableEq T] [DecidableEq b]

/-- Interior harmonic corrector `C⁻¹B*`. -/
noncomputable def boundaryInteriorCorrector
    (B : Matrix H T ℂ) (C : Matrix T T ℂ) [Invertible C] : Matrix T H ℂ :=
  C⁻¹ * Bᴴ

/-- Interior Schur complement `S`. -/
noncomputable def boundaryInteriorShort
    (A : Matrix H H ℂ) (B : Matrix H T ℂ) (C : Matrix T T ℂ)
    [Invertible C] : Matrix H H ℂ :=
  A - B * C⁻¹ * Bᴴ

/-- Effective boundary row `E`. -/
noncomputable def boundaryEffectiveRow
    (B : Matrix H T ℂ) (C : Matrix T T ℂ)
    (DH : Matrix b H ℂ) (DT : Matrix b T ℂ)
    [Invertible C] : Matrix b H ℂ :=
  DH - DT * C⁻¹ * Bᴴ

/-- Boundary stiffness `K`. -/
noncomputable def boundaryStiffness
    (C : Matrix T T ℂ) (DT : Matrix b T ℂ)
    [Invertible C] : Matrix b b ℂ :=
  DT * C⁻¹ * DTᴴ

/-- Detail block of the complete action. -/
def boundaryCompleteDetail
    (C : Matrix T T ℂ) (DT : Matrix b T ℂ) : Matrix T T ℂ :=
  C + DTᴴ * DT

/-- Head block of the complete action. -/
def boundaryCompleteHead
    (A : Matrix H H ℂ) (DH : Matrix b H ℂ) : Matrix H H ℂ :=
  A + DHᴴ * DH

/-- Head--detail coupling of the complete action. -/
def boundaryCompleteCoupling
    (B : Matrix H T ℂ) (DH : Matrix b H ℂ)
    (DT : Matrix b T ℂ) : Matrix H T ℂ :=
  B + DHᴴ * DT

/-- Algebraic head short of the literal complete action. -/
noncomputable def boundaryCompleteSchur
    (A : Matrix H H ℂ) (B : Matrix H T ℂ) (C : Matrix T T ℂ)
    (DH : Matrix b H ℂ) (DT : Matrix b T ℂ)
    [Invertible (boundaryCompleteDetail C DT)] : Matrix H H ℂ :=
  boundaryCompleteHead A DH -
    boundaryCompleteCoupling B DH DT *
      (boundaryCompleteDetail C DT)⁻¹ *
        (boundaryCompleteCoupling B DH DT)ᴴ

/-- The two-stage detail correction displayed in BC.5. -/
noncomputable def boundaryCompleteMinimizer
    (B : Matrix H T ℂ) (C : Matrix T T ℂ)
    (DH : Matrix b H ℂ) (DT : Matrix b T ℂ)
    [Invertible C] [Invertible (boundaryCompleteDetail C DT)] :
    Matrix T H ℂ :=
  -(C⁻¹ * Bᴴ) -
    (boundaryCompleteDetail C DT)⁻¹ * DTᴴ *
      boundaryEffectiveRow B C DH DT

set_option maxHeartbeats 800000 in
/-- The Schur complement of the complete block action is exactly the
boundary-complete formula `S + E*(I+K)⁻¹E`. -/
theorem boundaryCompleteSchur_eq_formula
    (A : Matrix H H ℂ) (B : Matrix H T ℂ) (C : Matrix T T ℂ)
    (DH : Matrix b H ℂ) (DT : Matrix b T ℂ)
    (hC : C.PosDef)
    [Invertible C] [Invertible (boundaryCompleteDetail C DT)] :
    boundaryCompleteSchur A B C DH DT =
      boundaryInteriorShort A B C +
        (boundaryEffectiveRow B C DH DT)ᴴ *
          (((1 : Matrix b b ℂ) + boundaryStiffness C DT)⁻¹ *
            boundaryEffectiveRow B C DH DT) := by
  let R : Matrix T H ℂ := C⁻¹ * Bᴴ
  let E : Matrix b H ℂ := boundaryEffectiveRow B C DH DT
  let S : Matrix H H ℂ := boundaryInteriorShort A B C
  let M : Matrix T T ℂ := boundaryCompleteDetail C DT
  let Y : Matrix T T ℂ := M⁻¹
  let W : Matrix b b ℂ := 1 - DT * Y * DTᴴ

  have hCH : Cᴴ = C := hC.isHermitian
  have hXH : (C⁻¹)ᴴ = C⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hCH]
  have hMH : Mᴴ = M := by
    dsimp only [M, boundaryCompleteDetail]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hCH]
  have hYH : Yᴴ = Y := by
    dsimp only [Y, M, boundaryCompleteDetail]
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hCH]
  have hCX : C * C⁻¹ = 1 := Matrix.mul_inv_of_invertible C
  have hXC : C⁻¹ * C = 1 := Matrix.inv_mul_of_invertible C
  have hMY : M * Y = 1 := by
    dsimp only [M, Y]
    exact Matrix.mul_inv_of_invertible (boundaryCompleteDetail C DT)
  have hYM : Y * M = 1 := by
    dsimp only [M, Y]
    exact Matrix.inv_mul_of_invertible (boundaryCompleteDetail C DT)
  have hMY_apply : ∀ {p : Type} [Fintype p] (Z : Matrix T p ℂ),
      M * (Y * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, hMY, Matrix.one_mul]
  have hYM_apply : ∀ {p : Type} [Fintype p] (Z : Matrix T p ℂ),
      Y * (M * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, hYM, Matrix.one_mul]
  have hCR : C * R = Bᴴ := by
    dsimp only [R]
    rw [← Matrix.mul_assoc, hCX, Matrix.one_mul]
  have hRHC : Rᴴ * C = B := by
    have h := congrArg Matrix.conjTranspose hCR
    rw [Matrix.conjTranspose_mul, hCH,
      Matrix.conjTranspose_conjTranspose] at h
    exact h
  have hDH : DH = E + DT * R := by
    dsimp only [E, boundaryEffectiveRow, R]
    simp only [Matrix.mul_assoc]
    abel
  have hGHT : boundaryCompleteCoupling B DH DT = Rᴴ * M + Eᴴ * DT := by
    rw [boundaryCompleteCoupling, hDH, ← hRHC]
    simp only [M, boundaryCompleteDetail]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.mul_assoc]
    abel
  have hS : A = S + B * R := by
    dsimp only [S, boundaryInteriorShort, R]
    simp only [Matrix.mul_assoc]
    abel
  have hGHH : boundaryCompleteHead A DH =
      S + Eᴴ * E + Eᴴ * DT * R + Rᴴ * DTᴴ * E + Rᴴ * M * R := by
    rw [boundaryCompleteHead, hDH, hS, ← hRHC]
    simp only [M, boundaryCompleteDetail]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.mul_assoc]
    abel
  have hGHTH : (boundaryCompleteCoupling B DH DT)ᴴ =
      M * R + DTᴴ * E := by
    have h := congrArg Matrix.conjTranspose hGHT
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hMH] using h
  have hprod : boundaryCompleteCoupling B DH DT * Y *
        (boundaryCompleteCoupling B DH DT)ᴴ =
      Rᴴ * M * R + Rᴴ * DTᴴ * E + Eᴴ * DT * R +
        Eᴴ * DT * Y * DTᴴ * E := by
    nth_rewrite 1 [hGHT]
    rw [hGHTH]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    rw [hMY_apply (M * R), hYM_apply R, hMY_apply (DTᴴ * E)]
    abel
  have hshort : boundaryCompleteSchur A B C DH DT =
      S + Eᴴ * (W * E) := by
    rw [boundaryCompleteSchur]
    change boundaryCompleteHead A DH -
      boundaryCompleteCoupling B DH DT * Y *
        (boundaryCompleteCoupling B DH DT)ᴴ = _
    rw [hGHH, hprod]
    dsimp only [W]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_assoc]
    abel
  have hWright :
      ((1 : Matrix b b ℂ) + DT * C⁻¹ * DTᴴ) *
        ((1 : Matrix b b ℂ) -
          DT * ((C + DTᴴ * DT)⁻¹ * DTᴴ)) = 1 := by
    letI : Invertible (C + DTᴴ * DT) := by
      simpa only [boundaryCompleteDetail] using
        (inferInstance : Invertible (boundaryCompleteDetail C DT))
    exact (gt_boundary_complete_short C DT).2.1
  have hW : W = ((1 : Matrix b b ℂ) + boundaryStiffness C DT)⁻¹ := by
    have hinv : ((1 : Matrix b b ℂ) + boundaryStiffness C DT)⁻¹ = W := by
      apply Matrix.inv_eq_right_inv
      simpa only [W, M, Y, boundaryStiffness, boundaryCompleteDetail,
        Matrix.mul_assoc] using hWright
    exact hinv.symm
  calc
    boundaryCompleteSchur A B C DH DT = S + Eᴴ * (W * E) := hshort
    _ = boundaryInteriorShort A B C +
        (boundaryEffectiveRow B C DH DT)ᴴ *
          (((1 : Matrix b b ℂ) + boundaryStiffness C DT)⁻¹ *
            boundaryEffectiveRow B C DH DT) := by
      rw [hW]

/-- The BC.5 two-stage correction equals the one-step complete-block normal
equation solution and satisfies that equation. -/
theorem boundaryCompleteMinimizer_normalEquation
    (B : Matrix H T ℂ) (C : Matrix T T ℂ)
    (DH : Matrix b H ℂ) (DT : Matrix b T ℂ)
    [Invertible C] [Invertible (boundaryCompleteDetail C DT)] :
    boundaryCompleteMinimizer B C DH DT =
        -((boundaryCompleteDetail C DT)⁻¹ *
          (boundaryCompleteCoupling B DH DT)ᴴ)
    ∧ boundaryCompleteDetail C DT *
        boundaryCompleteMinimizer B C DH DT =
          -(boundaryCompleteCoupling B DH DT)ᴴ := by
  let R : Matrix T H ℂ := C⁻¹ * Bᴴ
  let E : Matrix b H ℂ := boundaryEffectiveRow B C DH DT
  let M : Matrix T T ℂ := boundaryCompleteDetail C DT
  let Y : Matrix T T ℂ := M⁻¹

  have hYM : Y * M = 1 := by
    dsimp only [Y]
    exact Matrix.inv_mul_of_invertible M
  have hMY : M * Y = 1 := by
    dsimp only [Y]
    exact Matrix.mul_inv_of_invertible M
  have hdecomp : (boundaryCompleteCoupling B DH DT)ᴴ =
      M * R + DTᴴ * E := by
    dsimp only [boundaryCompleteCoupling, M, boundaryCompleteDetail, R, E,
      boundaryEffectiveRow]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc C C⁻¹ Bᴴ,
      Matrix.mul_inv_of_invertible, Matrix.one_mul]
    abel_nf
  have hmin : boundaryCompleteMinimizer B C DH DT =
      -(Y * (boundaryCompleteCoupling B DH DT)ᴴ) := by
    change -R - Y * DTᴴ * E =
      -(Y * (boundaryCompleteCoupling B DH DT)ᴴ)
    rw [hdecomp, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y M R, hYM, Matrix.one_mul]
    abel_nf
  constructor
  · simpa only [M, Y, boundaryCompleteDetail] using hmin
  · change M * boundaryCompleteMinimizer B C DH DT = _
    rw [hmin, Matrix.mul_neg, ← Matrix.mul_assoc, hMY,
      Matrix.one_mul]

/-- Literal completion of the complete action around the BC.5 minimizer.  The
second term is a positive detail square, so the displayed correction attains
the variational infimum and its head value is the boxed BC.4 operator. -/
theorem boundaryComplete_variational_completion
    (A : Matrix H H ℂ) (B : Matrix H T ℂ) (C : Matrix T T ℂ)
    (DH : Matrix b H ℂ) (DT : Matrix b T ℂ)
    (hC : C.PosDef)
    [Invertible C] [Invertible (boundaryCompleteDetail C DT)] :
    let Gswap := fromBlocks
      (boundaryCompleteDetail C DT)
      (boundaryCompleteCoupling B DH DT)ᴴ
      (boundaryCompleteCoupling B DH DT)
      (boundaryCompleteHead A DH)
    ∀ (x : H → ℂ) (y : T → ℂ),
      star (Sum.elim y x) ⬝ᵥ (Gswap *ᵥ Sum.elim y x) =
        star (y - boundaryCompleteMinimizer B C DH DT *ᵥ x) ⬝ᵥ
          (boundaryCompleteDetail C DT *ᵥ
            (y - boundaryCompleteMinimizer B C DH DT *ᵥ x))
        + star x ⬝ᵥ
          ((boundaryInteriorShort A B C +
            (boundaryEffectiveRow B C DH DT)ᴴ *
              (((1 : Matrix b b ℂ) + boundaryStiffness C DT)⁻¹ *
                boundaryEffectiveRow B C DH DT)) *ᵥ x) := by
  dsimp only
  intro x y
  let M : Matrix T T ℂ := boundaryCompleteDetail C DT
  let Q : Matrix H T ℂ := boundaryCompleteCoupling B DH DT
  let P : Matrix H H ℂ := boundaryCompleteHead A DH
  have hM : M.PosDef := by
    dsimp only [M, boundaryCompleteDetail]
    exact hC.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self DT)
  have hrange : M * pinv hM.isHermitian * Qᴴ = Qᴴ := by
    rw [self_mul_pinv hM, Matrix.one_mul]
  have hcomp := completion_of_square hM.posSemidef Qᴴ P hrange y x
  rw [Matrix.conjTranspose_conjTranspose] at hcomp
  have hmin := (boundaryCompleteMinimizer_normalEquation B C DH DT).1
  have hshort := boundaryCompleteSchur_eq_formula A B C DH DT hC
  have hpinv : pinv hM.isHermitian = M⁻¹ :=
    (Matrix.inv_eq_left_inv (pinv_mul_self hM)).symm
  rw [hpinv] at hcomp
  change _ =
    star (y - boundaryCompleteMinimizer B C DH DT *ᵥ x) ⬝ᵥ
        (M *ᵥ (y - boundaryCompleteMinimizer B C DH DT *ᵥ x)) + _
  have hcorr : y - boundaryCompleteMinimizer B C DH DT *ᵥ x =
      y + M⁻¹ *ᵥ (Qᴴ *ᵥ x) := by
    rw [hmin, Matrix.neg_mulVec, sub_neg_eq_add]
    change y + (M⁻¹ * Qᴴ) *ᵥ x = y + M⁻¹ *ᵥ (Qᴴ *ᵥ x)
    rw [Matrix.mulVec_mulVec]
  rw [hcorr, ← hshort]
  simpa only [M, Q, P, boundaryCompleteSchur] using hcomp

/-- The complete variational packet: exact operator, exact correction, normal
equation, and attainment-by-positive-square in one theorem. -/
theorem boundary_complete_short_exact_packet
    (A : Matrix H H ℂ) (B : Matrix H T ℂ) (C : Matrix T T ℂ)
    (DH : Matrix b H ℂ) (DT : Matrix b T ℂ)
    (hC : C.PosDef)
    [Invertible C] [Invertible (boundaryCompleteDetail C DT)] :
    boundaryCompleteSchur A B C DH DT =
      boundaryInteriorShort A B C +
        (boundaryEffectiveRow B C DH DT)ᴴ *
          (((1 : Matrix b b ℂ) + boundaryStiffness C DT)⁻¹ *
            boundaryEffectiveRow B C DH DT)
    ∧ boundaryCompleteMinimizer B C DH DT =
        -((boundaryCompleteDetail C DT)⁻¹ *
          (boundaryCompleteCoupling B DH DT)ᴴ)
    ∧ boundaryCompleteDetail C DT *
        boundaryCompleteMinimizer B C DH DT =
          -(boundaryCompleteCoupling B DH DT)ᴴ
    ∧ (let Gswap := fromBlocks
          (boundaryCompleteDetail C DT)
          (boundaryCompleteCoupling B DH DT)ᴴ
          (boundaryCompleteCoupling B DH DT)
          (boundaryCompleteHead A DH)
        ∀ (x : H → ℂ) (y : T → ℂ),
          star (Sum.elim y x) ⬝ᵥ (Gswap *ᵥ Sum.elim y x) =
            star (y - boundaryCompleteMinimizer B C DH DT *ᵥ x) ⬝ᵥ
              (boundaryCompleteDetail C DT *ᵥ
                (y - boundaryCompleteMinimizer B C DH DT *ᵥ x))
            + star x ⬝ᵥ (boundaryCompleteSchur A B C DH DT *ᵥ x)) := by
  refine ⟨boundaryCompleteSchur_eq_formula A B C DH DT hC, ?_⟩
  obtain ⟨hmin, hnormal⟩ := boundaryCompleteMinimizer_normalEquation B C DH DT
  refine ⟨hmin, hnormal, ?_⟩
  have hvar := boundaryComplete_variational_completion A B C DH DT hC
  dsimp only at hvar ⊢
  intro x y
  rw [boundaryCompleteSchur_eq_formula A B C DH DT hC]
  exact hvar x y

end BoundaryComplete

end NCG
