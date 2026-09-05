/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.FiniteChoiRadonNikodym

/-!
# Corrected finite Douglas factor

This removes the invertibility restriction from the earlier source factor.
The canonical factor uses the spectral Moore--Penrose inverse, is unique on
the supported coefficient space, and is an isometry for the source Gram
metrics.  The final theorem is the finite Douglas order/contraction
equivalence.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- Canonical Moore--Penrose reduced source factor. -/
noncomputable def reducedDouglasFactor {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) : Matrix (Fin e₂) (Fin e₁) ℂ :=
  sourceGramPseudoinverse S₂ * (S₂ᴴ * S₁)

/-- Singular exact reduced factor: factorization, Gram isometry, supportedness,
and uniqueness among supported factors. -/
theorem corrected_douglas_factor_exact {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ)
    (hres : sourceSchurResidual S₂ S₁ = 0) :
    let G₂ := S₂ᴴ * S₂
    let J₂ := sourceGramPseudoinverse S₂
    let Q₂ := J₂ * G₂
    let D := reducedDouglasFactor S₁ S₂
    S₂ * D = S₁
    ∧ Dᴴ * G₂ * D = S₁ᴴ * S₁
    ∧ Q₂ * D = D
    ∧ ∀ T : Matrix (Fin e₂) (Fin e₁) ℂ,
        S₂ * T = S₁ → Q₂ * T = T → T = D := by
  dsimp only
  let G₂ : Matrix (Fin e₂) (Fin e₂) ℂ := S₂ᴴ * S₂
  let J₂ : Matrix (Fin e₂) (Fin e₂) ℂ := sourceGramPseudoinverse S₂
  let Q₂ : Matrix (Fin e₂) (Fin e₂) ℂ := J₂ * G₂
  let D : Matrix (Fin e₂) (Fin e₁) ℂ := reducedDouglasFactor S₁ S₂
  obtain ⟨T, hT⟩ :=
    (sourceSchurResidual_eq_zero_iff_rangeIncluded S₂ S₁).mp hres
  have hS₂Q : S₂ * Q₂ = S₂ := by
    exact (sourceCoefficientSupport_properties S₂).2.2
  have hfactor : S₂ * D = S₁ := by
    calc
      S₂ * D = (S₂ * Q₂) * T := by
        dsimp [D, reducedDouglasFactor, Q₂, G₂, J₂]
        rw [hT]
        simp only [Matrix.mul_assoc]
      _ = S₂ * T := by rw [hS₂Q]
      _ = S₁ := hT.symm
  obtain ⟨-, -, hJGJ, -⟩ := sourceGramPseudoinverse_projection S₂
  have hsupported : Q₂ * D = D := by
    calc
      Q₂ * D =
          (J₂ * G₂ * J₂) * (S₂ᴴ * S₁) := by
        dsimp [Q₂, D, reducedDouglasFactor, G₂, J₂]
        simp only [Matrix.mul_assoc]
      _ = J₂ * (S₂ᴴ * S₁) := by rw [hJGJ]
      _ = D := rfl
  refine ⟨hfactor, ?_, hsupported, ?_⟩
  · calc
      Dᴴ * G₂ * D = (S₂ * D)ᴴ * (S₂ * D) := by
        rw [Matrix.conjTranspose_mul]
        simp only [G₂, Matrix.mul_assoc]
      _ = S₁ᴴ * S₁ := by rw [hfactor]
  · intro U hU hsuppU
    calc
      U = Q₂ * U := hsuppU.symm
      _ = J₂ * (S₂ᴴ * (S₂ * U)) := by
        simp only [Q₂, G₂, Matrix.mul_assoc]
      _ = J₂ * (S₂ᴴ * S₁) := by rw [hU]
      _ = D := rfl

/-- A coefficient factor with `I-DD*` positive gives the Douglas operator
order. -/
theorem douglas_order_of_contractive_factor {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ)
    (D : Matrix (Fin e₂) (Fin e₁) ℂ)
    (hfactor : S₂ * D = S₁)
    (hcontract : ((1 : Matrix (Fin e₂) (Fin e₂) ℂ) - D * Dᴴ).PosSemidef) :
    (S₂ * S₂ᴴ - S₁ * S₁ᴴ).PosSemidef := by
  have h := hcontract.conjTranspose_mul_mul_same S₂ᴴ
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    ← hfactor, Matrix.conjTranspose_mul] using h

set_option maxHeartbeats 800000 in
-- The singular range argument and two Moore--Penrose congruences need extra elaboration.
/-- Douglas converse: the operator order makes the canonical reduced factor a
contraction on the supported coefficient space. -/
theorem contractive_reduced_factor_of_douglas_order {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ)
    (horder : (S₂ * S₂ᴴ - S₁ * S₁ᴴ).PosSemidef) :
    let D := reducedDouglasFactor S₁ S₂
    S₂ * D = S₁ ∧
      ((1 : Matrix (Fin e₂) (Fin e₂) ℂ) - D * Dᴴ).PosSemidef := by
  dsimp only
  let J : Matrix (Fin e₂) (Fin e₂) ℂ := sourceGramPseudoinverse S₂
  let G : Matrix (Fin e₂) (Fin e₂) ℂ := S₂ᴴ * S₂
  let Q : Matrix (Fin e₂) (Fin e₂) ℂ := J * G
  let P : Matrix (Fin h) (Fin h) ℂ := sourceRangeProjection S₂
  let R : Matrix (Fin h) (Fin e₁) ℂ := (1 - P) * S₁
  obtain ⟨hJH, hGJG, hJGJ, hPH, hP2, hPS₂⟩ :=
    sourceGramPseudoinverse_projection S₂
  have hQH : Qᴴ = Q := (sourceCoefficientSupport_properties S₂).1
  have hQ2 : Q * Q = Q := (sourceCoefficientSupport_properties S₂).2.1
  have hS₂starQ : S₂ᴴ * (1 - P) = 0 := by
    have h := congrArg Matrix.conjTranspose hPS₂
    change P * S₂ = S₂ at hPS₂
    change Pᴴ = P at hPH
    rw [Matrix.conjTranspose_mul, hPH] at h
    rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  have hdomR : (S₁ * S₁ᴴ) * R = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    simp only [Matrix.zero_mulVec]
    rw [← Matrix.mulVec_mulVec]
    let z : Fin h → ℂ := R *ᵥ v
    have hz : S₂ᴴ *ᵥ z = 0 := by
      dsimp only [z]
      rw [Matrix.mulVec_mulVec, show S₂ᴴ * R = 0 by
        dsimp only [R]
        rw [← Matrix.mul_assoc, hS₂starQ, Matrix.zero_mul],
        Matrix.zero_mulVec]
    have hgram : star z ⬝ᵥ ((S₂ * S₂ᴴ) *ᵥ z) = 0 := by
      rw [← Matrix.mulVec_mulVec z S₂ S₂ᴴ, hz,
        Matrix.mulVec_zero, dotProduct_zero]
    have hC : (S₁ * S₁ᴴ).PosSemidef :=
      Matrix.posSemidef_self_mul_conjTranspose S₁
    have hnonneg := hC.dotProduct_mulVec_nonneg z
    have hdiff := horder.dotProduct_mulVec_nonneg z
    rw [Matrix.sub_mulVec, dotProduct_sub, hgram, zero_sub] at hdiff
    have hzero : star z ⬝ᵥ ((S₁ * S₁ᴴ) *ᵥ z) = 0 :=
      le_antisymm (neg_nonneg.mp hdiff) hnonneg
    exact (hC.dotProduct_mulVec_zero_iff z).mp hzero
  have hS₁starR : S₁ᴴ * R = 0 :=
    (Matrix.self_mul_conjTranspose_mul_eq_zero S₁ R).mp hdomR
  have hRgram : Rᴴ * R = 0 := by
    have hQH' : (1 - P)ᴴ = 1 - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
    have hQ2' : (1 - P) * (1 - P) = 1 - P := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
        Matrix.mul_one, hP2]
      abel
    calc
      Rᴴ * R = S₁ᴴ * ((1 - P) * ((1 - P) * S₁)) := by
        dsimp only [R]
        rw [Matrix.conjTranspose_mul, hQH']
        simp only [Matrix.mul_assoc]
      _ = S₁ᴴ * (((1 - P) * (1 - P)) * S₁) := by
        rw [Matrix.mul_assoc]
      _ = S₁ᴴ * ((1 - P) * S₁) := by rw [hQ2']
      _ = S₁ᴴ * R := rfl
      _ = 0 := hS₁starR
  have hR : R = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hRgram
  have hPS₁ : P * S₁ = S₁ := by
    dsimp only [R] at hR
    rw [Matrix.sub_mul, Matrix.one_mul] at hR
    exact (sub_eq_zero.mp hR).symm
  have hfactor : S₂ * reducedDouglasFactor S₁ S₂ = S₁ := by
    simpa only [P, sourceRangeProjection, reducedDouglasFactor,
      Matrix.mul_assoc] using hPS₁
  have hIQ : ((1 : Matrix (Fin e₂) (Fin e₂) ℂ) - Q).PosSemidef := by
    have heq : (1 - Q)ᴴ * (1 - Q) = (1 : Matrix (Fin e₂) (Fin e₂) ℂ) - Q := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQH,
        Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hQ2]
      abel
    rw [← heq]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  let X : Matrix (Fin h) (Fin e₂) ℂ := S₂ * J
  have hcongr : (Q - reducedDouglasFactor S₁ S₂ *
      (reducedDouglasFactor S₁ S₂)ᴴ).PosSemidef := by
    have hp := horder.conjTranspose_mul_mul_same X
    have hfirst : Xᴴ * (S₂ * S₂ᴴ) * X = Q := by
      calc
        Xᴴ * (S₂ * S₂ᴴ) * X = Q * Q := by
          dsimp only [X]
          rw [Matrix.conjTranspose_mul, hJH]
          simp only [Matrix.mul_assoc]
          change J * (S₂ᴴ * (S₂ * (S₂ᴴ * (S₂ * J)))) = Q * Q
          calc
            _ = (J * G) * (G * J) := by
              simp only [G, Matrix.mul_assoc]
            _ = (J * G) * (J * G) := by
              rw [sourceGramPseudoinverse_commutes S₂]
            _ = Q * Q := rfl
        _ = Q := hQ2
    have hsecond : Xᴴ * (S₁ * S₁ᴴ) * X =
        reducedDouglasFactor S₁ S₂ *
          (reducedDouglasFactor S₁ S₂)ᴴ := by
      dsimp only [X, J, reducedDouglasFactor]
      rw [Matrix.conjTranspose_mul, hJH, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH]
      simp only [Matrix.mul_assoc]
    have heq : Xᴴ * (S₂ * S₂ᴴ - S₁ * S₁ᴴ) * X =
        Q - reducedDouglasFactor S₁ S₂ *
          (reducedDouglasFactor S₁ S₂)ᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hfirst, hsecond]
    rw [← heq]
    exact hp
  have hcontract : ((1 : Matrix (Fin e₂) (Fin e₂) ℂ) -
      reducedDouglasFactor S₁ S₂ *
        (reducedDouglasFactor S₁ S₂)ᴴ).PosSemidef := by
    have hadd := hIQ.add hcongr
    convert hadd using 1 <;> abel
  exact ⟨hfactor, hcontract⟩

/-- Full finite Douglas order equivalence, with the coefficient contraction
expressed as `I-DD* ⪰ 0` (equivalent to Euclidean operator norm at most one). -/
theorem douglas_order_equivalence {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) :
    (S₂ * S₂ᴴ - S₁ * S₁ᴴ).PosSemidef ↔
      ∃ D : Matrix (Fin e₂) (Fin e₁) ℂ,
        S₂ * D = S₁ ∧
          ((1 : Matrix (Fin e₂) (Fin e₂) ℂ) - D * Dᴴ).PosSemidef := by
  constructor
  · intro horder
    exact ⟨reducedDouglasFactor S₁ S₂,
      contractive_reduced_factor_of_douglas_order S₁ S₂ horder⟩
  · rintro ⟨D, hfactor, hcontract⟩
    exact douglas_order_of_contractive_factor S₁ S₂ D hfactor hcontract
end NCG
