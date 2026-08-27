/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandScoreCross

/-!
# Assembled score-cross channel and intrinsic Kossakowski line

This file combines the two equal `1/4` bridge contributions and formalizes the one-dimensional
Kossakowski operator and its canonical minimal row.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- The two score-square bridge words assemble to the advertised half-weight cross maps. -/
theorem scoreCross_assembled
    {l r : Type*} [Fintype l] [Fintype r] [DecidableEq l] [DecidableEq r]
    (F : Matrix r l ℂ) (T : Matrix r r ℂ) (S : Matrix l l ℂ) :
    (1 / 4 : ℂ) •
        (Matrix.fromBlocks (0 : Matrix l l ℂ) Fᴴ F 0
          * Matrix.fromBlocks 0 0 0 T
          * Matrix.fromBlocks (0 : Matrix l l ℂ) Fᴴ F 0)
      + (1 / 4 : ℂ) •
        (Matrix.fromBlocks (0 : Matrix l l ℂ) ((-Complex.I) • Fᴴ) (Complex.I • F) 0
          * Matrix.fromBlocks 0 0 0 T
          * Matrix.fromBlocks (0 : Matrix l l ℂ) ((-Complex.I) • Fᴴ) (Complex.I • F) 0)
      = Matrix.fromBlocks ((1 / 2 : ℂ) • (Fᴴ * T * F)) 0 0 0
    ∧ (1 / 4 : ℂ) •
        (Matrix.fromBlocks (0 : Matrix l l ℂ) Fᴴ F 0
          * Matrix.fromBlocks S 0 0 0
          * Matrix.fromBlocks (0 : Matrix l l ℂ) Fᴴ F 0)
      + (1 / 4 : ℂ) •
        (Matrix.fromBlocks (0 : Matrix l l ℂ) ((-Complex.I) • Fᴴ) (Complex.I • F) 0
          * Matrix.fromBlocks S 0 0 0
          * Matrix.fromBlocks (0 : Matrix l l ℂ) ((-Complex.I) • Fᴴ) (Complex.I • F) 0)
      = Matrix.fromBlocks 0 0 0 ((1 / 2 : ℂ) • (F * S * Fᴴ)) := by
  obtain ⟨hXT, hYT, hXS, hYS, _⟩ := sm_score_cross F T S
  constructor
  · rw [hXT, hYT]
    rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    congr 1 <;> module
  · rw [hXS, hYS]
    rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    congr 1 <;> module

/-- Both absorbed effects are fixed to one half for a unitary bridge. -/
theorem scoreCross_absorbed_effects
    {l r : Type*} [Fintype l] [Fintype r] [DecidableEq l] [DecidableEq r]
    (F : Matrix r l ℂ) (hleft : Fᴴ * F = 1) (hright : F * Fᴴ = 1) :
    (1 / 2 : ℂ) • (Fᴴ * (1 : Matrix r r ℂ) * F)
        = (1 / 2 : ℂ) • (1 : Matrix l l ℂ)
      ∧ (1 / 2 : ℂ) • (F * (1 : Matrix l l ℂ) * Fᴴ)
        = (1 / 2 : ℂ) • (1 : Matrix r r ℂ) := by
  simp [hleft, hright]

/-- Unit vector on the intrinsic one-dimensional bridge-mode space. -/
def scoreBridgeUnit : Fin 1 → ℂ := fun _ ↦ 1

/-- The intrinsic Kossakowski operator is `1/2 |e_br⟩⟨e_br|`. -/
noncomputable def scoreBridgeKossakowski : Matrix (Fin 1) (Fin 1) ℂ :=
  (1 / 2 : ℂ) • Matrix.vecMulVec scoreBridgeUnit (star scoreBridgeUnit)

/-- The canonical minimal coefficient row is the scalar `1/√2`, and its Gram is exactly the
intrinsic Kossakowski operator. -/
noncomputable def scoreBridgeMinimalRow : Matrix (Fin 1) (Fin 1) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ)

theorem scoreBridgeMinimalRow_gram :
    scoreBridgeMinimalRowᴴ * scoreBridgeMinimalRow = scoreBridgeKossakowski := by
  ext i j
  fin_cases i
  fin_cases j
  simp [scoreBridgeMinimalRow, scoreBridgeKossakowski, scoreBridgeUnit,
    Matrix.mul_apply, Matrix.vecMulVec_apply]
  field_simp
  change (2 : ℂ) = (Real.sqrt 2 : ℂ) ^ 2
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem scoreBridgeKossakowski_posSemidef : scoreBridgeKossakowski.PosSemidef := by
  rw [← scoreBridgeMinimalRow_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end NCG



