/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Simultaneous nuisance short
  (`thm:simultaneous-nuisance-short`, Gran-Tensor manuscript)

* `simultaneous_nuisance_short`: projecting the completed and
  Euler syntheses off the common nuisance range gives the three
  boxed hatted blocks
  `M̂ = M - C_MᴴG_N⁻¹C_M`, `Ê = 𝔼 - C_EᴴG_N⁻¹C_E`,
  `B̂ = B - C_MᴴG_N⁻¹C_E`, and the hatted two-by-two block Gram
  is positive semidefinite (it is the Gram of the projected
  joint synthesis) — the short of the three-family Gram to the
  completed–Euler coefficient space.

Rendering disclosed: the nuisance Gram is rendered invertible
(faithful nuisance family; the pseudo-inverse case is the
manuscript's general form); that shorting the two marginals
separately while keeping `B` is inconsistent is the
manuscript's following counter-clause.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false

/-- Projected pair identity: the hatted cross Gram is the
nuisance-shorted block. -/
private lemma nuisance_pair {H eN eX eY : Type*} [Fintype H]
    [Fintype eN] [Fintype eX] [Fintype eY]
    [DecidableEq H] [DecidableEq eN]
    (N : Matrix H eN ℂ) [Invertible (Nᴴ * N)]
    (X : Matrix H eX ℂ) (Y : Matrix H eY ℂ) :
    ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * X)ᴴ
        * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * Y)
      = Xᴴ * Y - (Nᴴ * X)ᴴ * (Nᴴ * N)⁻¹ * (Nᴴ * Y) := by
  have hGherm : (Nᴴ * N)ᴴ = Nᴴ * N := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hGinvherm : ((Nᴴ * N)⁻¹)ᴴ = (Nᴴ * N)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGherm]
  have hPherm : (1 - N * (Nᴴ * N)⁻¹ * Nᴴ)ᴴ
      = 1 - N * (Nᴴ * N)⁻¹ * Nᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hGinvherm, Matrix.conjTranspose_conjTranspose]
    congr 1
    simp only [Matrix.mul_assoc]
  have hPidem : (1 - N * (Nᴴ * N)⁻¹ * Nᴴ)
      * (1 - N * (Nᴴ * N)⁻¹ * Nᴴ)
      = 1 - N * (Nᴴ * N)⁻¹ * Nᴴ := by
    have hcore : N * (Nᴴ * N)⁻¹ * Nᴴ
        * (N * (Nᴴ * N)⁻¹ * Nᴴ)
        = N * (Nᴴ * N)⁻¹ * Nᴴ := by
      calc N * (Nᴴ * N)⁻¹ * Nᴴ * (N * (Nᴴ * N)⁻¹ * Nᴴ)
          = N * ((Nᴴ * N)⁻¹ * ((Nᴴ * N)
              * ((Nᴴ * N)⁻¹ * Nᴴ))) := by
            simp only [Matrix.mul_assoc]
        _ = N * ((Nᴴ * N)⁻¹ * Nᴴ) := by
            rw [show (Nᴴ * N) * ((Nᴴ * N)⁻¹ * Nᴴ)
                = ((Nᴴ * N) * (Nᴴ * N)⁻¹) * Nᴴ from by
              simp only [Matrix.mul_assoc],
              Matrix.mul_inv_of_invertible, Matrix.one_mul]
        _ = N * (Nᴴ * N)⁻¹ * Nᴴ := by
            simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [hcore]
    abel
  rw [Matrix.conjTranspose_mul, hPherm]
  calc Xᴴ * (1 - N * (Nᴴ * N)⁻¹ * Nᴴ)
      * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * Y)
      = Xᴴ * (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ)
          * (1 - N * (Nᴴ * N)⁻¹ * Nᴴ)) * Y) := by
        simp only [Matrix.mul_assoc]
    _ = Xᴴ * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * Y) := by
        rw [hPidem]
    _ = Xᴴ * Y - (Nᴴ * X)ᴴ * (Nᴴ * N)⁻¹ * (Nᴴ * Y) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
          Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
        congr 1
        simp only [Matrix.mul_assoc]

/-- `thm:simultaneous-nuisance-short`: the three hatted blocks
and the positivity of the shorted joint Gram. -/
theorem simultaneous_nuisance_short {H eA eS eN : Type*}
    [Fintype H] [Fintype eA] [Fintype eS] [Fintype eN]
    [DecidableEq H] [DecidableEq eN]
    (A : Matrix H eA ℂ) (S : Matrix H eS ℂ)
    (N : Matrix H eN ℂ) [Invertible (Nᴴ * N)] :
    (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A)ᴴ
        * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A)
      = Aᴴ * A - (Nᴴ * A)ᴴ * (Nᴴ * N)⁻¹ * (Nᴴ * A))
    ∧ (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S)ᴴ
        * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S)
      = Sᴴ * S - (Nᴴ * S)ᴴ * (Nᴴ * N)⁻¹ * (Nᴴ * S))
    ∧ (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A)ᴴ
        * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S)
      = Aᴴ * S - (Nᴴ * A)ᴴ * (Nᴴ * N)⁻¹ * (Nᴴ * S))
    ∧ (Matrix.fromBlocks
        (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A)ᴴ
          * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A))
        (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A)ᴴ
          * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S))
        (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S)ᴴ
          * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A))
        (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S)ᴴ
          * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S))).PosSemidef := by
  refine ⟨nuisance_pair N A A, nuisance_pair N S S,
    nuisance_pair N A S, ?_⟩
  rw [show Matrix.fromBlocks
      (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A)ᴴ
        * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A))
      (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A)ᴴ
        * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S))
      (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S)ᴴ
        * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A))
      (((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S)ᴴ
        * ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S))
      = (Matrix.fromCols ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A)
          ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S))ᴴ
        * Matrix.fromCols ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * A)
          ((1 - N * (Nᴴ * N)⁻¹ * Nᴴ) * S) from by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end NCG
