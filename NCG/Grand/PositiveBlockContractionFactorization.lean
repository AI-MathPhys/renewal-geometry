/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MarginalsOrientation
import NCG.Grand.SingularPolarData

/-!
# Positive block matrices and support contractions

This file gives the singular-support form of the positive two-by-two block
factorization.  No marginal is assumed invertible: the relative orientation
is obtained from the partial isometries in the polar decompositions of source
factors and is extended by zero off the faithful supports.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false

private theorem projectionComplement_posSemidef {I : Type*}
    [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ)
    (hPH : Pᴴ = P) (hP2 : P * P = P) :
    ((1 : Matrix I I ℂ) - P).PosSemidef := by
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hgram : (1 - P)ᴴ * (1 - P) = 1 - P := by rw [hQH, hQ2]
  rw [← hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

private theorem partialIsometry_initial_complement_posSemidef
    {H : Type*} [Fintype H] {e : ℕ}
    (U : Matrix H (Fin e) ℂ)
    (hU : U * (Uᴴ * U) = U) :
    ((1 : Matrix (Fin e) (Fin e) ℂ) - Uᴴ * U).PosSemidef := by
  have hPH : (Uᴴ * U)ᴴ = Uᴴ * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hP2 : (Uᴴ * U) * (Uᴴ * U) = Uᴴ * U := by
    calc
      (Uᴴ * U) * (Uᴴ * U) = Uᴴ * (U * (Uᴴ * U)) := by
        simp only [Matrix.mul_assoc]
      _ = Uᴴ * U := by rw [hU]
  exact projectionComplement_posSemidef (Uᴴ * U) hPH hP2

private theorem partialIsometry_final_complement_posSemidef
    {H : Type*} [Fintype H] [DecidableEq H] {e : ℕ}
    (U : Matrix H (Fin e) ℂ)
    (hU : U * (Uᴴ * U) = U) :
    ((1 : Matrix H H ℂ) - U * Uᴴ).PosSemidef := by
  have hQH : (U * Uᴴ)ᴴ = U * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hQ2 : (U * Uᴴ) * (U * Uᴴ) = U * Uᴴ := by
    calc
      (U * Uᴴ) * (U * Uᴴ) = (U * (Uᴴ * U)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
      _ = U * Uᴴ := by rw [hU]
  exact projectionComplement_posSemidef (U * Uᴴ) hQH hQ2

/-- Cross transport between two partial isometries is a contraction. -/
theorem partialIsometry_cross_contraction
    {H : Type*} [Fintype H] [DecidableEq H] {n m : ℕ}
    (U₁ : Matrix H (Fin n) ℂ) (U₂ : Matrix H (Fin m) ℂ)
    (hU₁ : U₁ * (U₁ᴴ * U₁) = U₁)
    (hU₂ : U₂ * (U₂ᴴ * U₂) = U₂) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) -
      (U₂ᴴ * U₁)ᴴ * (U₂ᴴ * U₁)).PosSemidef := by
  have hsplit : (1 : Matrix (Fin n) (Fin n) ℂ) -
      (U₂ᴴ * U₁)ᴴ * (U₂ᴴ * U₁) =
      (1 - U₁ᴴ * U₁) + U₁ᴴ * (1 - U₂ * U₂ᴴ) * U₁ := by
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.mul_one,
      Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [hsplit]
  have hinit : ((1 : Matrix (Fin n) (Fin n) ℂ) - U₁ᴴ * U₁).PosSemidef :=
    partialIsometry_initial_complement_posSemidef U₁ hU₁
  have hfinal : ((1 : Matrix H H ℂ) - U₂ * U₂ᴴ).PosSemidef :=
    partialIsometry_final_complement_posSemidef U₂ hU₂
  exact hinit.add (hfinal.conjTranspose_mul_mul_same U₁)

set_option maxHeartbeats 2000000 in
-- Two singular polar decompositions and their support projections require extra elaboration.
/-- Two arbitrary finite source maps have a square-root cross-Gram
factorization by a contraction.  Singular coefficient directions are handled
by the initial projections of the polar partial isometries. -/
theorem sourceCrossGram_contractionFactorization
    {H : Type*} [Fintype H] [DecidableEq H] {n m : ℕ}
    (S₁ : Matrix H (Fin n) ℂ)
    (S₂ : Matrix H (Fin m) ℂ) :
    ∃ K : Matrix (Fin m) (Fin n) ℂ,
      ((1 : Matrix (Fin n) (Fin n) ℂ) - Kᴴ * K).PosSemidef ∧
      S₂ᴴ * S₁ = CFC.sqrt (S₂ᴴ * S₂) * K * CFC.sqrt (S₁ᴴ * S₁) := by
  rcases exists_singular_polar_data S₁ with
    ⟨U₁, P₁, _, hP₁, hS₁, hP₁2, hU₁, _, _, _⟩
  rcases exists_singular_polar_data S₂ with
    ⟨U₂, P₂, _, hP₂, hS₂, hP₂2, hU₂, _, _, _⟩
  have hP₁sqrt : CFC.sqrt (S₁ᴴ * S₁) = P₁ :=
    (CFC.sqrt_eq_iff (S₁ᴴ * S₁) P₁
      (Matrix.posSemidef_conjTranspose_mul_self S₁).nonneg hP₁.nonneg).2 hP₁2
  have hP₂sqrt : CFC.sqrt (S₂ᴴ * S₂) = P₂ :=
    (CFC.sqrt_eq_iff (S₂ᴴ * S₂) P₂
      (Matrix.posSemidef_conjTranspose_mul_self S₂).nonneg hP₂.nonneg).2 hP₂2
  let K : Matrix (Fin m) (Fin n) ℂ := U₂ᴴ * U₁
  have hK : ((1 : Matrix (Fin n) (Fin n) ℂ) - Kᴴ * K).PosSemidef := by
    exact partialIsometry_cross_contraction U₁ U₂ hU₁ hU₂
  refine ⟨K, hK, ?_⟩
  rw [hP₁sqrt, hP₂sqrt]
  calc
    S₂ᴴ * S₁ = (U₂ * P₂)ᴴ * (U₁ * P₁) := by rw [← hS₁, ← hS₂]
    _ = P₂ * (U₂ᴴ * U₁) * P₁ := by
      rw [Matrix.conjTranspose_mul, hP₂.isHermitian]
      simp only [Matrix.mul_assoc]
    _ = P₂ * K * P₁ := rfl

/-- Every positive semidefinite finite block matrix is the Gram matrix of the
two column restrictions of its positive square root. -/
private theorem positiveBlock_sourceRealization {n m : ℕ}
    {G₁ : Matrix (Fin n) (Fin n) ℂ}
    {G₂ : Matrix (Fin m) (Fin m) ℂ}
    (C₂₁ : Matrix (Fin m) (Fin n) ℂ)
    (hM : (Matrix.fromBlocks G₁ C₂₁ᴴ C₂₁ G₂).PosSemidef) :
    ∃ (S₁ : Matrix (Fin n ⊕ Fin m) (Fin n) ℂ)
      (S₂ : Matrix (Fin n ⊕ Fin m) (Fin m) ℂ),
      S₁ᴴ * S₁ = G₁ ∧ S₂ᴴ * S₂ = G₂ ∧ S₂ᴴ * S₁ = C₂₁ := by
  let M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ :=
    Matrix.fromBlocks G₁ C₂₁ᴴ C₂₁ G₂
  let T := CFC.sqrt M
  let S₁ : Matrix (Fin n ⊕ Fin m) (Fin n) ℂ :=
    fun i j => T i (Sum.inl j)
  let S₂ : Matrix (Fin n ⊕ Fin m) (Fin m) ℂ :=
    fun i j => T i (Sum.inr j)
  have hTgram : Tᴴ * T = M := by
    rw [sqrt_isHermitian]
    exact sqrt_mul_self_eq M hM
  refine ⟨S₁, S₂, ?_, ?_, ?_⟩
  · ext i j
    have hij := congrArg (fun X => X (Sum.inl i) (Sum.inl j)) hTgram
    change (∑ k, star (T k (Sum.inl i)) * T k (Sum.inl j)) = G₁ i j
    simpa only [M, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.fromBlocks_apply₁₁] using hij
  · ext i j
    have hij := congrArg (fun X => X (Sum.inr i) (Sum.inr j)) hTgram
    change (∑ k, star (T k (Sum.inr i)) * T k (Sum.inr j)) = G₂ i j
    simpa only [M, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.fromBlocks_apply₂₂] using hij
  · ext i j
    have hij := congrArg (fun X => X (Sum.inr i) (Sum.inl j)) hTgram
    change (∑ k, star (T k (Sum.inr i)) * T k (Sum.inl j)) = C₂₁ i j
    simpa only [M, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.fromBlocks_apply₂₁] using hij

/-- `cth:marginals-no-relative-orientation`, including non-faithful
marginals: positive block completions are exactly the square-root
factorizations by contractions (extended by zero off the faithful supports). -/
theorem positiveBlock_iff_contractionFactorization {n m : ℕ}
    {G₁ : Matrix (Fin n) (Fin n) ℂ}
    {G₂ : Matrix (Fin m) (Fin m) ℂ}
    (hG₁ : G₁.PosSemidef) (hG₂ : G₂.PosSemidef)
    (C₂₁ : Matrix (Fin m) (Fin n) ℂ) :
    (Matrix.fromBlocks G₁ C₂₁ᴴ C₂₁ G₂).PosSemidef ↔
      ∃ K : Matrix (Fin m) (Fin n) ℂ,
        ((1 : Matrix (Fin n) (Fin n) ℂ) - Kᴴ * K).PosSemidef ∧
        C₂₁ = CFC.sqrt G₂ * K * CFC.sqrt G₁ := by
  constructor
  · intro hM
    rcases positiveBlock_sourceRealization C₂₁ hM with
      ⟨S₁, S₂, hG₁', hG₂', hC⟩
    rcases sourceCrossGram_contractionFactorization S₁ S₂ with ⟨K, hK, hfac⟩
    refine ⟨K, hK, ?_⟩
    rw [hG₁', hG₂'] at hfac
    exact hC ▸ hfac
  · rintro ⟨K, hK, rfl⟩
    let Q : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
      Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) K Kᴴ
        (1 : Matrix (Fin n) (Fin n) ℂ)
    have hQ : Q.PosSemidef := by
      letI : Invertible (1 : Matrix (Fin m) (Fin m) ℂ) := invertibleOne
      have honeinv : (1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ = 1 := by
        have h := Matrix.mul_inv_of_invertible
          (1 : Matrix (Fin m) (Fin m) ℂ)
        simpa only [Matrix.one_mul] using h
      dsimp only [Q]
      rw [(Matrix.PosDef.one : (1 : Matrix (Fin m) (Fin m) ℂ).PosDef).fromBlocks₁₁ K
        (1 : Matrix (Fin n) (Fin n) ℂ)]
      simpa only [honeinv, Matrix.mul_one] using hK
    have hcenter : (Matrix.fromBlocks
        (1 : Matrix (Fin n) (Fin n) ℂ) Kᴴ K
        (1 : Matrix (Fin m) (Fin m) ℂ)).PosSemidef :=
      (fromBlocks_posSemidef_swap_iff
        (1 : Matrix (Fin n) (Fin n) ℂ) Kᴴ K
        (1 : Matrix (Fin m) (Fin m) ℂ)).2 hQ
    let W : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ :=
      Matrix.fromBlocks (CFC.sqrt G₁) 0 0 (CFC.sqrt G₂)
    have hconj := hcenter.conjTranspose_mul_mul_same W
    have hW : Wᴴ = W := by
      dsimp only [W]
      simp only [Matrix.fromBlocks_conjTranspose, sqrt_isHermitian,
        Matrix.conjTranspose_zero]
    have hs₁ : CFC.sqrt G₁ * CFC.sqrt G₁ = G₁ :=
      sqrt_mul_self_eq G₁ hG₁
    have hs₂ : CFC.sqrt G₂ * CFC.sqrt G₂ = G₂ :=
      sqrt_mul_self_eq G₂ hG₂
    rw [hW] at hconj
    dsimp only [W] at hconj
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add,
      hs₁, hs₂] at hconj
    simpa only [Matrix.conjTranspose_mul, sqrt_isHermitian,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hconj

end NCG
