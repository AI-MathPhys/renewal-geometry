/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PsdBlockSchurExact

/-!
# Localizer extension floor

Exact encoding of `thm:GT-localizer-extension-floor` (NL.4k–NL.4n) from the
Moore–Penrose Schur criterion of `PsdBlockSchurExact`.

For the enlarged localizer `Λ⁺ = [[A, B], [B^*, D]]` and `δ ≥ 0`, with
`A_δ = A - δ I`, `S_δ = D - δ I - B^* A_δ^† B`:

* `shifted_block`: `Λ⁺ - δ I = [[A_δ, B], [B^*, D - δ I]]`;
* `extension_floor_iff` (NL.4k ⇔ NL.4l): `Λ⁺ ⪰ δ I` iff `A_δ ⪰ 0`,
  `Ran B ⊆ Ran A_δ` (`A_δ A_δ^† B = B`) and `S_δ ⪰ 0`;
* `extension_floor_square` (NL.4m): the completion of the square under the
  range condition;
* `soft_word_witness` (NL.4n): a negative direction `y` of `S_δ` returns the
  explicit soft-word witness `(-A_δ^† B y, y)` of negative shifted energy;
* `range_obstruction`: if the range condition fails, a kernel vector of `A_δ`
  coupled to `B y` returns the range obstruction.
-/

open Matrix NCG.GeometricThresholdBank NCG.SourceCoercivityInfluence NCG.PsdBlockSchur
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace LocalizerExtensionFloor

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]

omit [Fintype m] [Fintype p] in
/-- The shifted block matrix `Λ⁺ - δ I`. -/
theorem shifted_block (A : Matrix m m ℂ) (B : Matrix m p ℂ) (D : Matrix p p ℂ) (δ : ℝ) :
    fromBlocks A B Bᴴ D - (δ : ℂ) • (1 : Matrix (m ⊕ p) (m ⊕ p) ℂ)
      = fromBlocks (A - (δ : ℂ) • 1) B Bᴴ (D - (δ : ℂ) • 1) := by
  rw [← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

omit [Fintype m] in
theorem shifted_isHermitian {A : Matrix m m ℂ} (hA : A.IsHermitian) (δ : ℝ) :
    (A - (δ : ℂ) • 1).IsHermitian := by
  change (A - (δ : ℂ) • 1)ᴴ = A - (δ : ℂ) • 1
  rw [conjTranspose_sub, hA.eq, conjTranspose_smul, conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal]

omit [DecidableEq m] [DecidableEq p] in
/-- A positive block matrix has positive diagonal blocks. -/
theorem posSemidef_left_of_fromBlocks {A : Matrix m m ℂ} {B : Matrix m p ℂ} {D : Matrix p p ℂ}
    (hM : (fromBlocks A B Bᴴ D).PosSemidef) : A.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨(isHermitian_fromBlocks_iff.mp hM.1).1, fun x => ?_⟩
  have := hM.dotProduct_mulVec_nonneg (Sum.elim x 0)
  rw [block_form] at this
  simpa using this

/-- **(NL.4k ⇔ NL.4l)**: the extension floor criterion. -/
theorem extension_floor_iff {A : Matrix m m ℂ} (hA : A.IsHermitian) (B : Matrix m p ℂ)
    {D : Matrix p p ℂ} (hD : D.IsHermitian) (δ : ℝ) :
    (fromBlocks A B Bᴴ D - (δ : ℂ) • (1 : Matrix (m ⊕ p) (m ⊕ p) ℂ)).PosSemidef ↔
      (A - (δ : ℂ) • 1).PosSemidef ∧
        (A - (δ : ℂ) • 1) * pinv (shifted_isHermitian hA δ) * B = B ∧
        (D - (δ : ℂ) • 1 - Bᴴ * pinv (shifted_isHermitian hA δ) * B).PosSemidef := by
  rw [shifted_block]
  constructor
  · intro hM
    have hAδ : (A - (δ : ℂ) • 1).PosSemidef := posSemidef_left_of_fromBlocks hM
    have hcrit := (posSemidef_block_iff hAδ B (D - (δ : ℂ) • 1) (shifted_isHermitian hD δ)).mp hM
    exact ⟨hAδ, hcrit.1, hcrit.2⟩
  · rintro ⟨hAδ, hrange, hS⟩
    exact (posSemidef_block_iff hAδ B (D - (δ : ℂ) • 1) (shifted_isHermitian hD δ)).mpr
      ⟨hrange, hS⟩

/-- **(NL.4m)**: completion of the square for the shifted localizer. -/
theorem extension_floor_square {A : Matrix m m ℂ} (hA : A.IsHermitian) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (δ : ℝ) (hAδ : (A - (δ : ℂ) • 1).PosSemidef)
    (hrange : (A - (δ : ℂ) • 1) * pinv (shifted_isHermitian hA δ) * B = B) (x : m → ℂ)
    (y : p → ℂ) :
    star (Sum.elim x y) ⬝ᵥ ((fromBlocks A B Bᴴ D - (δ : ℂ) • 1) *ᵥ Sum.elim x y)
      = star (x + pinv (shifted_isHermitian hA δ) *ᵥ (B *ᵥ y))
          ⬝ᵥ ((A - (δ : ℂ) • 1) *ᵥ (x + pinv (shifted_isHermitian hA δ) *ᵥ (B *ᵥ y)))
        + star y ⬝ᵥ ((D - (δ : ℂ) • 1 - Bᴴ * pinv (shifted_isHermitian hA δ) * B) *ᵥ y) := by
  rw [shifted_block]
  exact completion_of_square hAδ B (D - (δ : ℂ) • 1) hrange x y

/-- **(NL.4n)**: a negative direction of `S_δ` gives the explicit soft-word
witness `(-A_δ^† B y, y)` of negative shifted energy. -/
theorem soft_word_witness {A : Matrix m m ℂ} (hA : A.IsHermitian) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (δ : ℝ) (hAδ : (A - (δ : ℂ) • 1).PosSemidef)
    (hrange : (A - (δ : ℂ) • 1) * pinv (shifted_isHermitian hA δ) * B = B) (y : p → ℂ)
    (hneg : (star y ⬝ᵥ ((D - (δ : ℂ) • 1 - Bᴴ * pinv (shifted_isHermitian hA δ) * B) *ᵥ y)).re
      < 0) :
    (star (Sum.elim (-(pinv (shifted_isHermitian hA δ) *ᵥ (B *ᵥ y))) y)
      ⬝ᵥ ((fromBlocks A B Bᴴ D - (δ : ℂ) • 1)
        *ᵥ Sum.elim (-(pinv (shifted_isHermitian hA δ) *ᵥ (B *ᵥ y))) y)).re < 0 := by
  rw [shifted_block]
  exact negative_witness hAδ B (D - (δ : ℂ) • 1) hrange y hneg

/-- **Range obstruction**: if `Ran B ⊄ Ran A_δ`, a kernel vector of `A_δ`
coupled to `B y` has negative shifted energy. -/
theorem range_obstruction {A : Matrix m m ℂ} (hA : A.IsHermitian) (B : Matrix m p ℂ)
    (D : Matrix p p ℂ) (δ : ℝ) (hAδ : (A - (δ : ℂ) • 1).PosSemidef)
    (hfail : (A - (δ : ℂ) • 1) * pinv (shifted_isHermitian hA δ) * B ≠ B) :
    ∃ z : m ⊕ p → ℂ,
      (star z ⬝ᵥ ((fromBlocks A B Bᴴ D - (δ : ℂ) • 1) *ᵥ z)).re < 0 := by
  rw [shifted_block]
  exact range_obstruction_witness hAδ B (D - (δ : ℂ) • 1) hfail

end LocalizerExtensionFloor
end NCG
