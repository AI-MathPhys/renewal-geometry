/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointSourceNormalizedTransportAndShort

/-!
# Simultaneous nuisance short

This file proves the singular Moore--Penrose form of the simultaneous
nuisance short.  Both declared sources are projected away from one common
nuisance range; the resulting two-by-two block is its Gram matrix and the
universal variational short of the three-family Gram.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- The synthesis obtained by removing the range of a common nuisance map. -/
noncomputable def nuisanceShortedSource {h e f : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (X : Matrix (Fin h) (Fin e) ℂ) :
    Matrix (Fin h) (Fin e) ℂ :=
  (1 - sourceRangeProjection N) * X

/-- Every pairwise Gram block is shortened by the same Moore--Penrose
correction when both sources use the common nuisance projector. -/
theorem nuisanceShortedSource_pair {h e₁ e₂ f : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ)
    (X : Matrix (Fin h) (Fin e₁) ℂ)
    (Y : Matrix (Fin h) (Fin e₂) ℂ) :
    (nuisanceShortedSource N X)ᴴ * nuisanceShortedSource N Y =
      Xᴴ * Y - (Nᴴ * X)ᴴ * sourceGramPseudoinverse N * (Nᴴ * Y) := by
  let P := sourceRangeProjection N
  obtain ⟨hPH, hP2, _⟩ :=
    (sourceGramPseudoinverse_projection N).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  simp only [nuisanceShortedSource, Matrix.conjTranspose_mul]
  change Xᴴ * (1 - P)ᴴ * ((1 - P) * Y) = _
  rw [hQH]
  rw [Matrix.conjTranspose_conjTranspose]
  calc
    Xᴴ * (1 - P) * ((1 - P) * Y)
        = Xᴴ * (((1 - P) * (1 - P)) * Y) := by
            simp only [Matrix.mul_assoc]
    _ = Xᴴ * ((1 - P) * Y) := by rw [hQ2]
    _ = Xᴴ * Y - Xᴴ * N * sourceGramPseudoinverse N *
        (Nᴴ * Y) := by
      simp only [P, sourceRangeProjection, Matrix.sub_mul, Matrix.one_mul,
        Matrix.mul_sub, Matrix.mul_assoc]

/-- The complete hatted two-source block is the Gram matrix of the jointly
shorted synthesis and is therefore positive semidefinite. -/
theorem simultaneousNuisanceShort_blockGram {h e f n : ℕ}
    (A : Matrix (Fin h) (Fin e) ℂ)
    (S : Matrix (Fin h) (Fin f) ℂ)
    (N : Matrix (Fin h) (Fin n) ℂ) :
    let Â := nuisanceShortedSource N A
    let Ŝ := nuisanceShortedSource N S
    (Matrix.fromBlocks (Âᴴ * Â) (Âᴴ * Ŝ) (Ŝᴴ * Â) (Ŝᴴ * Ŝ)).PosSemidef := by
  dsimp only
  rw [show Matrix.fromBlocks
      ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N A)
      ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N S)
      ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N A)
      ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N S) =
      (Matrix.fromCols (nuisanceShortedSource N A)
        (nuisanceShortedSource N S))ᴴ *
      Matrix.fromCols (nuisanceShortedSource N A)
        (nuisanceShortedSource N S) from by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The Schur residual of the concatenated completed--Euler source is exactly
the two-by-two Gram block of the simultaneously nuisance-shorted sources. -/
theorem simultaneousNuisanceShort_residualBlock {h e f n : ℕ}
    (A : Matrix (Fin h) (Fin e) ℂ)
    (S : Matrix (Fin h) (Fin f) ℂ)
    (N : Matrix (Fin h) (Fin n) ℂ) :
    (Matrix.fromCols A S)ᴴ * (1 - sourceRangeProjection N) *
        Matrix.fromCols A S =
      Matrix.fromBlocks
        ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N A)
        ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N S)
        ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N A)
        ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N S) := by
  let Q : Matrix (Fin h) (Fin h) ℂ := 1 - sourceRangeProjection N
  obtain ⟨hPH, hP2, _⟩ :=
    (sourceGramPseudoinverse_projection N).2.2.2
  have hQH : Qᴴ = Q := by
    dsimp only [Q]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : Q * Q = Q := by
    dsimp only [Q]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  change (Matrix.fromCols A S)ᴴ * Q * Matrix.fromCols A S = _
  have hgram : (Matrix.fromCols A S)ᴴ * Q * Matrix.fromCols A S =
      (Q * Matrix.fromCols A S)ᴴ * (Q * Matrix.fromCols A S) := by
    rw [Matrix.conjTranspose_mul, hQH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q, hQ2]
  rw [hgram]
  rw [Matrix.mul_fromCols]
  simp only [nuisanceShortedSource, Q]
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols]

/-- The simultaneous block is the Anderson--Trapp short of the full
three-family Gram: it is the universal lower bound and is attained at the
Moore--Penrose least-squares nuisance compensation. -/
theorem simultaneousNuisance_andersonTrapp_short {h e f n : ℕ}
    (A : Matrix (Fin h) (Fin e) ℂ)
    (S : Matrix (Fin h) (Fin f) ℂ)
    (N : Matrix (Fin h) (Fin n) ℂ) :
    let T := Matrix.fromCols A S
    let G := Tᴴ * T
    let G_N := Nᴴ * N
    let C_N := Nᴴ * T
    let Z := sourceGramPseudoinverse N * C_N
    let M := Matrix.fromBlocks G C_Nᴴ C_N G_N
    (G - Zᴴ * G_N * Z).PosSemidef ∧
      (∀ (x : (Fin e ⊕ Fin f) → ℂ) (y : Fin n → ℂ),
        star x ⬝ᵥ ((G - Zᴴ * G_N * Z) *ᵥ x) ≤
          star (Sum.elim x y) ⬝ᵥ (M *ᵥ Sum.elim x y)) ∧
      (∀ x : (Fin e ⊕ Fin f) → ℂ,
        star (Sum.elim x (-(Z *ᵥ x))) ⬝ᵥ
            (M *ᵥ Sum.elim x (-(Z *ᵥ x))) =
          star x ⬝ᵥ ((G - Zᴴ * G_N * Z) *ᵥ x)) := by
  dsimp only
  let T := Matrix.fromCols A S
  let G_N := Nᴴ * N
  let C_N := Nᴴ * T
  let J := sourceGramPseudoinverse N
  let Z : Matrix (Fin n) (Fin e ⊕ Fin f) ℂ := J * C_N
  obtain ⟨hJH, _, _, _, _, hPN⟩ :=
    sourceGramPseudoinverse_projection N
  change Jᴴ = J at hJH
  have hNJG : N * J * G_N = N := by
    change (N * J * Nᴴ) * N = N at hPN
    simpa only [G_N, Matrix.mul_assoc] using hPN
  have hGJN : G_N * J * Nᴴ = Nᴴ := by
    have ht := congrArg Matrix.conjTranspose hNJG
    have ht' : G_Nᴴ * Jᴴ * Nᴴ = Nᴴ := by
      simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using ht
    have hGH : G_Nᴴ = G_N := by
      dsimp only [G_N]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hGH, hJH] at ht'
    exact ht'
  have hZ : G_N * Z = (C_Nᴴ)ᴴ := by
    calc
      G_N * Z = (G_N * J * Nᴴ) * T := by
        dsimp only [Z, C_N]
        simp only [Matrix.mul_assoc]
      _ = Nᴴ * T := by rw [hGJN]
      _ = (C_Nᴴ)ᴴ := by
        dsimp only [C_N]
        rw [Matrix.conjTranspose_conjTranspose]
  have hblock : (Matrix.fromCols T N)ᴴ * Matrix.fromCols T N =
      Matrix.fromBlocks (Tᴴ * T) C_Nᴴ C_N G_N := by
    dsimp only [C_N, G_N]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols]
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hM : (Matrix.fromBlocks (Tᴴ * T) C_Nᴴ C_N G_N).PosSemidef := by
    rw [← hblock]
    exact Matrix.posSemidef_conjTranspose_mul_self (Matrix.fromCols T N)
  have hM' :
      (Matrix.fromBlocks (Tᴴ * T) C_Nᴴ (C_Nᴴ)ᴴ G_N).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hM
  simpa only [T, G_N, C_N, J, Z,
    Matrix.conjTranspose_conjTranspose] using
    (schur_short (Tᴴ * T) C_Nᴴ G_N Z hZ hM')

/-- An explicit marginal-only failure: zeroing the two diagonal marginals
while retaining a unit cross block gives eigenvalues `1` and `-1`, hence is
not positive semidefinite. -/
theorem marginalOnlyShort_with_oldCross_not_posSemidef :
    ¬ (!![(0 : ℂ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := by
  intro h
  have hnonneg := h.dotProduct_mulVec_nonneg ![(1 : ℂ), -1]
  norm_num [Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Fin.sum_univ_two] at hnonneg

/-- `thm:simultaneous-nuisance-short`: all three Moore--Penrose block
identities and positivity of the common nuisance short. -/
theorem simultaneous_nuisance_short_exact {h e f n : ℕ}
    (A : Matrix (Fin h) (Fin e) ℂ)
    (S : Matrix (Fin h) (Fin f) ℂ)
    (N : Matrix (Fin h) (Fin n) ℂ) :
    ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N A =
      Aᴴ * A - (Nᴴ * A)ᴴ * sourceGramPseudoinverse N * (Nᴴ * A)) ∧
    ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N S =
      Sᴴ * S - (Nᴴ * S)ᴴ * sourceGramPseudoinverse N * (Nᴴ * S)) ∧
    ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N S =
      Aᴴ * S - (Nᴴ * A)ᴴ * sourceGramPseudoinverse N * (Nᴴ * S)) ∧
    (Matrix.fromBlocks
      ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N A)
      ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N S)
      ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N A)
      ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N S)).PosSemidef :=
  ⟨nuisanceShortedSource_pair N A A,
    nuisanceShortedSource_pair N S S,
    nuisanceShortedSource_pair N A S,
    simultaneousNuisanceShort_blockGram A S N⟩

end NCG
