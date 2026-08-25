/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MoorePenroseSchurExact

/-!
# Chronology-complete terminal short and dynamic source-head promotion

Machinery for `thm:NS-dynamic-terminal-short`.  For a terminal response `R : X →L[ℝ] Y`, a
represented history head `H ≤ X` and its complement `T ≤ X`, with `R_H = R|_H`, `R_T = R|_T`:

* (NS.3) the assembled terminal Gram `[[A, B], [B*, D]]` with blocks `A = R_H* R_H`,
  `B = R_H* R_T`, `D = R_T* R_T` is positive: its quadratic form is `‖R_H h + R_T t‖²`
  (`assembledGram_eq`, `assembledGram_nonneg`);
* (NS.4) the dynamically represented-head short `S = D - B* A† B = R_T* (I - P_{ran R_H}) R_T ⪰ 0`
  (`short_eq`, `short_isPositive`);
* (NS.5) for the irreducible response `R^irr = (I - P_{ran R_H}) R_T` with compliance
  `C = R^irr (R^irr)*` and an assembled defect `δ`, the source-minimal action
  `d = ⟨δ^irr, C† δ^irr⟩ = min_{R^irr q = -δ^irr} ‖q‖²` (`irrAction_eq_min`);
* (NS.6) nested heads: `‖(I - Π_L) y‖² = ‖(Π_M - Π_L) y‖² + ‖(I - Π_M) y‖²` (`nested_residual`);
* (NS.7) the complete geometry action is the quadratic form of the mixed Gram
  `A_{ξζ} = ⟨δ^ξ, C† δ^ζ⟩` (`geometry_action_eq`).
-/

open ContinuousLinearMap Submodule NCG.MoorePenrose
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace NSTerminalShort

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [CompleteSpace Y]

variable (R : X →L[ℝ] Y) (H T : Submodule ℝ X)

/-- The head response `R_H = R|_H`. -/
noncomputable def headMap : H →L[ℝ] Y := R ∘L H.subtypeL

/-- The tail response `R_T = R|_T`. -/
noncomputable def tailMap : T →L[ℝ] Y := R ∘L T.subtypeL

omit [CompleteSpace X] [FiniteDimensional ℝ Y] in
/-- **(NS.3)**: the assembled terminal Gram `[[A, B], [B*, D]]` is positive: its quadratic form on
a pair `(h, t)` is `‖R_H h + R_T t‖²`. -/
theorem assembledGram_eq (h : H) (t : T) :
    ⟪gram (headMap R H) h, h⟫ + 2 * ⟪crossGram (headMap R H) (tailMap R T) t, h⟫
      + ⟪gram (tailMap R T) t, t⟫ = ‖headMap R H h + tailMap R T t‖ ^ 2 := by
  simp only [gram_apply, crossGram, comp_apply]
  rw [adjoint_inner_left, adjoint_inner_left, adjoint_inner_left, norm_add_sq_real,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm (tailMap R T t)]

omit [CompleteSpace X] [FiniteDimensional ℝ Y] in
theorem assembledGram_nonneg (h : H) (t : T) :
    0 ≤ ⟪gram (headMap R H) h, h⟫ + 2 * ⟪crossGram (headMap R H) (tailMap R T) t, h⟫
      + ⟪gram (tailMap R T) t, t⟫ := by
  rw [assembledGram_eq]; exact sq_nonneg _

/-- The dynamically represented-head short `S = D - B* A† B`. -/
noncomputable def short : T →L[ℝ] T :=
  gram (tailMap R T) -
    (crossGram (headMap R H) (tailMap R T))† ∘L gramPinv (headMap R H) ∘L
      crossGram (headMap R H) (tailMap R T)

/-- The irreducible response `R^irr = (I - P_{ran R_H}) R_T`. -/
noncomputable def irrResponse : T →L[ℝ] Y := residual (headMap R H) (tailMap R T)

omit [CompleteSpace X] in
/-- **(NS.4)**: the short is the Gram of the irreducible response. -/
theorem short_eq : short R H T = (tailMap R T)† ∘L irrResponse R H T :=
  schur_innovation (headMap R H) (tailMap R T)

omit [CompleteSpace X] in
theorem short_isPositive : (short R H T).IsPositive := by
  rw [short_eq]
  exact innovation_isPositive _ _

/-- The compliance `C = R^irr (R^irr)*`. -/
noncomputable def compliance : Y →L[ℝ] Y := gram ((irrResponse R H T)†)

omit [CompleteSpace X] [FiniteDimensional ℝ Y] in
theorem compliance_eq : compliance R H T = irrResponse R H T ∘L (irrResponse R H T)† :=
  gram_adjoint_eq _

/-- The irreducible defect `δ^irr = (I - P_{ran R_H}) δ`. -/
noncomputable def irrDefect (δ : Y) : Y :=
  δ - (LinearMap.range (headMap R H).toLinearMap).starProjection δ

/-- The source-minimal action `d = ⟨δ^irr, C† δ^irr⟩`. -/
noncomputable def irrAction (δ : Y) : ℝ :=
  ⟪irrDefect R H δ, gramPinv ((irrResponse R H T)†) (irrDefect R H δ)⟫

omit [CompleteSpace X] in
/-- **(NS.5)**: the Moore–Penrose Thomson principle — the source-minimal action is the minimal
squared norm of a source `q` with `R^irr q = -δ^irr`, attained. -/
theorem irrAction_eq_min {δ : Y}
    (hsolv : -irrDefect R H δ ∈ LinearMap.range (irrResponse R H T).toLinearMap) :
    ∃ q₀ : T, irrResponse R H T q₀ = -irrDefect R H δ ∧
      ‖q₀‖ ^ 2 = irrAction R H T δ ∧
      ∀ q : T, irrResponse R H T q = -irrDefect R H δ → ‖q₀‖ ≤ ‖q‖ := by
  refine ⟨minNormSolution (irrResponse R H T) (-irrDefect R H δ),
    minNormSolution_apply _ hsolv, ?_, fun q hq => norm_minNormSolution_le _ hq⟩
  rw [norm_sq_minNormSolution _ hsolv, irrAction, map_neg, inner_neg_left, inner_neg_right,
    neg_neg]

/-! ### Nested heads (NS.6) -/

omit [FiniteDimensional ℝ X] [CompleteSpace X] [FiniteDimensional ℝ Y] [CompleteSpace Y] in
/-- Nested source cores have nested terminal head images. -/
theorem headRange_mono {H₁ H₂ : Submodule ℝ X} (h : H₁ ≤ H₂) :
    LinearMap.range (headMap R H₁).toLinearMap ≤ LinearMap.range (headMap R H₂).toLinearMap := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x, h x.2⟩, rfl⟩

omit [FiniteDimensional ℝ Y] [CompleteSpace Y] in
/-- **(NS.6)**: the nested-projection Pythagoras
`‖(I - Π_L) y‖² = ‖(Π_M - Π_L) y‖² + ‖(I - Π_M) y‖²`. -/
theorem nested_residual {U V : Submodule ℝ Y} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hUV : U ≤ V) (y : Y) :
    ‖y - U.starProjection y‖ ^ 2
      = ‖V.starProjection y - U.starProjection y‖ ^ 2 + ‖y - V.starProjection y‖ ^ 2 := by
  have hmem : V.starProjection y - U.starProjection y ∈ V :=
    V.sub_mem (V.starProjection_apply_mem y) (hUV (U.starProjection_apply_mem y))
  have horth : ⟪V.starProjection y - U.starProjection y, y - V.starProjection y⟫ = 0 := by
    rw [real_inner_comm]
    exact V.starProjection_inner_eq_zero y _ hmem
  have hdecomp : y - U.starProjection y
      = (V.starProjection y - U.starProjection y) + (y - V.starProjection y) := by abel
  rw [hdecomp, pow_two, pow_two, pow_two]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_real horth

/-! ### The mixed geometry Gram (NS.7) -/

omit [CompleteSpace X] in
/-- **(NS.7)**: for `δ^irr = ∑_ξ δ^ξ`, the action is the quadratic form `𝟙* 𝔸 𝟙` of the mixed
Gram `𝔸_{ξζ} = ⟨δ^ξ, C† δ^ζ⟩`. -/
theorem geometry_action_eq {ι : Type*} (s : Finset ι) (δ : ι → Y) :
    ⟪∑ ξ ∈ s, δ ξ, gramPinv ((irrResponse R H T)†) (∑ ζ ∈ s, δ ζ)⟫
      = ∑ ξ ∈ s, ∑ ζ ∈ s, ⟪δ ξ, gramPinv ((irrResponse R H T)†) (δ ζ)⟫ := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [inner_sum]

omit [CompleteSpace X] in
/-- **`thm:NS-dynamic-terminal-short`**: (NS.3) positivity of the assembled Gram, (NS.4) the
short as the irreducible-response Gram, (NS.5) the Thomson principle, (NS.6) nested-head
Pythagoras and nesting of head images, (NS.7) the mixed geometry Gram. -/
theorem ns_dynamic_terminal_short :
    (∀ (h : H) (t : T), ⟪gram (headMap R H) h, h⟫
        + 2 * ⟪crossGram (headMap R H) (tailMap R T) t, h⟫ + ⟪gram (tailMap R T) t, t⟫
        = ‖headMap R H h + tailMap R T t‖ ^ 2) ∧
      short R H T = (tailMap R T)† ∘L irrResponse R H T ∧ (short R H T).IsPositive ∧
      (∀ δ : Y, -irrDefect R H δ ∈ LinearMap.range (irrResponse R H T).toLinearMap →
        ∃ q₀ : T, irrResponse R H T q₀ = -irrDefect R H δ ∧ ‖q₀‖ ^ 2 = irrAction R H T δ ∧
          ∀ q : T, irrResponse R H T q = -irrDefect R H δ → ‖q₀‖ ≤ ‖q‖) ∧
      (∀ {H₁ H₂ : Submodule ℝ X}, H₁ ≤ H₂ →
        LinearMap.range (headMap R H₁).toLinearMap ≤ LinearMap.range (headMap R H₂).toLinearMap) ∧
      (∀ (U V : Submodule ℝ Y) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection], U ≤ V →
        ∀ y : Y, ‖y - U.starProjection y‖ ^ 2
          = ‖V.starProjection y - U.starProjection y‖ ^ 2 + ‖y - V.starProjection y‖ ^ 2) ∧
      ∀ {ι : Type} (s : Finset ι) (δ : ι → Y),
        ⟪∑ ξ ∈ s, δ ξ, gramPinv ((irrResponse R H T)†) (∑ ζ ∈ s, δ ζ)⟫
          = ∑ ξ ∈ s, ∑ ζ ∈ s, ⟪δ ξ, gramPinv ((irrResponse R H T)†) (δ ζ)⟫ :=
  ⟨assembledGram_eq R H T, short_eq R H T, short_isPositive R H T,
    fun _ hsolv => irrAction_eq_min R H T hsolv, fun h => headRange_mono R h,
    fun _ _ _ _ hUV y => nested_residual hUV y, fun s δ => geometry_action_eq R H T s δ⟩

end NSTerminalShort
end NCG
