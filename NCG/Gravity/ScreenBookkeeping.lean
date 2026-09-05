/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Screen normalization bookkeeping
  (`lem:screen-normalization`, GR_emergence)

With metric area per screen cell `a_ε ≍ ε²`, dimensionless entropy
per cell `η_cell = η_scr·a_ε`, and a split collar of fixed bond
dimension `D` independent of `ε` and of the screen:

* `cell_entropy_density` — the continuum entropy density per unit
  metric area is recovered per cell: `η_cell/a_ε = η_scr`;
* `cell_curvature_scale` — the dimensionless curvature seen by one
  cell is sandwiched at order `ε²`:
  `c₁ε²|ℛ| ≤ a_ε|ℛ| ≤ c₂ε²|ℛ|`, and likewise for `|K|²`;
* `continuity_constant_uniform` — the conditional-entropy
  continuity constant is `log D`, uniformly bounded in `ε` and the
  screen: `O(log D) = O(1)`.
-/

namespace NCG

/-- The continuum entropy density is recovered from the per-cell
entropy: `η_cell/a_ε = η_scr`. -/
theorem cell_entropy_density (etaScr aEps : ℝ) (ha : aEps ≠ 0) :
    etaScr * aEps / aEps = etaScr := by
  field_simp

/-- The dimensionless curvature per cell is sandwiched at order
`ε²`: if `c₁ε² ≤ a_ε ≤ c₂ε²` then
`c₁ε²·|ℛ| ≤ a_ε·|ℛ| ≤ c₂ε²·|ℛ|`, and likewise for `|K|²`. -/
theorem cell_curvature_scale (c1 c2 aEps eps R K2 : ℝ)
    (hlow : c1 * eps ^ 2 ≤ aEps) (hhigh : aEps ≤ c2 * eps ^ 2)
    (hR : 0 ≤ R) (hK : 0 ≤ K2) :
    (c1 * eps ^ 2 * R ≤ aEps * R ∧ aEps * R ≤ c2 * eps ^ 2 * R)
      ∧ (c1 * eps ^ 2 * K2 ≤ aEps * K2
        ∧ aEps * K2 ≤ c2 * eps ^ 2 * K2) := by
  exact ⟨⟨mul_le_mul_of_nonneg_right hlow hR,
      mul_le_mul_of_nonneg_right hhigh hR⟩,
    ⟨mul_le_mul_of_nonneg_right hlow hK,
      mul_le_mul_of_nonneg_right hhigh hK⟩⟩

/-- With fixed bond dimension `D` (independent of `ε` and of the
screen), the conditional-entropy continuity constant `log D` is
uniformly bounded: `O(log D) = O(1)`. -/
theorem continuity_constant_uniform {Screen : Type*}
    (D : ℕ) (const : ℝ → Screen → ℝ)
    (hfix : ∀ eps scr, const eps scr = Real.log D) :
    ∃ C : ℝ, ∀ eps scr, const eps scr ≤ C :=
  ⟨Real.log D, fun eps scr => (hfix eps scr).le⟩

end NCG
