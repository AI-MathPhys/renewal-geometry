/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ExactEasy67
import NCG.Grand.ExactEasy62
import NCG.Grand.HeadTailEnclosure
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Exact EASY 68: sharp positive head--tail operator enclosure

This file upgrades the already proved scalar two-by-two estimate to the
manuscript's operator-norm statement.  The block quadratic form is bounded by
the scalar comparison matrix, and positivity lets the Rayleigh quotient
recover the operator norm without an absolute-value loss.
-/

open Matrix Real
open scoped ComplexOrder Norms.L2Operator

namespace NCG

lemma abs_re_star_dot_mulVec_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    |(star x ⬝ᵥ (M *ᵥ y)).re| ≤
      ‖M‖ * ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  let xE : EuclideanSpace ℂ m := WithLp.toLp 2 x
  let yE : EuclideanSpace ℂ n := WithLp.toLp 2 y
  have hinner : star x ⬝ᵥ (M *ᵥ y) =
      inner ℂ xE (Matrix.toEuclideanLin M yE) := by
    simp only [xE, yE,
      Matrix.toEuclideanLin_apply_piLp_toLp,
      EuclideanSpace.inner_toLp_toLp]
    rw [dotProduct_comm]
  rw [hinner]
  calc
    |(inner ℂ xE (Matrix.toEuclideanLin M yE)).re| ≤
        ‖inner ℂ xE (Matrix.toEuclideanLin M yE)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖xE‖ * ‖Matrix.toEuclideanLin M yE‖ := norm_inner_le_norm _ _
    _ ≤ ‖xE‖ * (‖M‖ * ‖yE‖) := by
      exact mul_le_mul_of_nonneg_left
        (Matrix.l2_opNorm_mulVec M yE) (norm_nonneg xE)
    _ = ‖M‖ * ‖xE‖ * ‖yE‖ := by ring

lemma block_reApplyInnerSelf_eq {h t : Type*} [Fintype h] [Fintype t]
    [DecidableEq h] [DecidableEq t]
    (A : Matrix h h ℂ) (B : Matrix h t ℂ) (D : Matrix t t ℂ)
    (z : EuclideanSpace ℂ (h ⊕ t)) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (Matrix.fromBlocks A B Bᴴ D)).reApplyInnerSelf z
      = ((star (WithLp.ofLp (leftPart z)) ⬝ᵥ
            (A *ᵥ WithLp.ofLp (leftPart z)))
        + (star (WithLp.ofLp (leftPart z)) ⬝ᵥ
            (B *ᵥ WithLp.ofLp (rightPart z)))
        + (star (WithLp.ofLp (rightPart z)) ⬝ᵥ
            (Bᴴ *ᵥ WithLp.ofLp (leftPart z)))
        + (star (WithLp.ofLp (rightPart z)) ⬝ᵥ
            (D *ᵥ WithLp.ofLp (rightPart z)))).re := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM]
  rw [dotProduct_comm]
  have hz : WithLp.ofLp z = Sum.elim
      (WithLp.ofLp (leftPart z)) (WithLp.ofLp (rightPart z)) := by
    funext i
    cases i <;> rfl
  rw [hz]
  exact congrArg Complex.re
    (head_tail_block_expansion A B D
      (WithLp.ofLp (leftPart z)) (WithLp.ofLp (rightPart z)))

lemma left_right_norm_sq {h t : Type*} [Fintype h] [Fintype t]
    (z : EuclideanSpace ℂ (h ⊕ t)) :
    ‖leftPart z‖ ^ 2 + ‖rightPart z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, leftPart, rightPart,
    Fintype.sum_sum_type]

/-- The missing operator clause of `thm:sharp-positive-head-tail`. -/
theorem sharp_positive_head_tail_opNorm {h t : Type*}
    [Fintype h] [Fintype t] [DecidableEq h] [DecidableEq t]
    (A : Matrix h h ℂ) (B : Matrix h t ℂ) (D : Matrix t t ℂ)
    (hH : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    ‖Matrix.fromBlocks A B Bᴴ D‖ ≤
      (‖A‖ + ‖D‖ + Real.sqrt ((‖A‖ - ‖D‖) ^ 2 + 4 * ‖B‖ ^ 2)) / 2 := by
  let H : Matrix (h ⊕ t) (h ⊕ t) ℂ := Matrix.fromBlocks A B Bᴴ D
  let T : EuclideanSpace ℂ (h ⊕ t) →L[ℂ] EuclideanSpace ℂ (h ⊕ t) :=
    Matrix.toEuclideanCLM (𝕜 := ℂ) H
  let Λ : ℝ :=
    (‖A‖ + ‖D‖ + Real.sqrt ((‖A‖ - ‖D‖) ^ 2 + 4 * ‖B‖ ^ 2)) / 2
  have hTpos : T.IsPositive := by
    rw [← ContinuousLinearMap.isPositive_toLinearMap_iff]
    change (Matrix.toEuclideanLin H).IsPositive
    exact Matrix.isPositive_toEuclideanLin_iff.mpr hH
  have hΛ : 0 ≤ Λ := by
    dsimp [Λ]
    positivity
  have hquad : ∀ z, T.reApplyInnerSelf z ≤ Λ * ‖z‖ ^ 2 := by
    intro z
    let x : h → ℂ := WithLp.ofLp (leftPart z)
    let y : t → ℂ := WithLp.ofLp (rightPart z)
    have hA := abs_re_star_dot_mulVec_le A x x
    have hB := abs_re_star_dot_mulVec_le B x y
    have hBH := abs_re_star_dot_mulVec_le Bᴴ y x
    have hD := abs_re_star_dot_mulVec_le D y y
    have hscalar := sharp_positive_head_tail.1
      ‖A‖ ‖B‖ ‖D‖ ‖leftPart z‖ ‖rightPart z‖
      (norm_nonneg A) (norm_nonneg B) (norm_nonneg D)
    rw [block_reApplyInnerSelf_eq A B D]
    dsimp only [x, y] at hA hB hBH hD
    have hterms :
        ((star (WithLp.ofLp (leftPart z)) ⬝ᵥ
              (A *ᵥ WithLp.ofLp (leftPart z)))
          + (star (WithLp.ofLp (leftPart z)) ⬝ᵥ
              (B *ᵥ WithLp.ofLp (rightPart z)))
          + (star (WithLp.ofLp (rightPart z)) ⬝ᵥ
              (Bᴴ *ᵥ WithLp.ofLp (leftPart z)))
          + (star (WithLp.ofLp (rightPart z)) ⬝ᵥ
              (D *ᵥ WithLp.ofLp (rightPart z)))).re
        ≤ ‖A‖ * ‖leftPart z‖ ^ 2
          + 2 * ‖B‖ * ‖leftPart z‖ * ‖rightPart z‖
          + ‖D‖ * ‖rightPart z‖ ^ 2 := by
      simp only [Complex.add_re]
      calc
        _ ≤ |(star (WithLp.ofLp (leftPart z)) ⬝ᵥ
                (A *ᵥ WithLp.ofLp (leftPart z))).re|
            + |(star (WithLp.ofLp (leftPart z)) ⬝ᵥ
                (B *ᵥ WithLp.ofLp (rightPart z))).re|
            + |(star (WithLp.ofLp (rightPart z)) ⬝ᵥ
                (Bᴴ *ᵥ WithLp.ofLp (leftPart z))).re|
            + |(star (WithLp.ofLp (rightPart z)) ⬝ᵥ
                (D *ᵥ WithLp.ofLp (rightPart z))).re| := by
              gcongr <;> exact le_abs_self _
        _ ≤ (‖A‖ * ‖leftPart z‖ * ‖leftPart z‖)
            + (‖B‖ * ‖leftPart z‖ * ‖rightPart z‖)
            + (‖Bᴴ‖ * ‖rightPart z‖ * ‖leftPart z‖)
            + (‖D‖ * ‖rightPart z‖ * ‖rightPart z‖) := by
              exact add_le_add (add_le_add (add_le_add hA hB) hBH) hD
        _ = _ := by
          rw [Matrix.l2_opNorm_conjTranspose]
          ring
    calc
      _ ≤ ‖A‖ * ‖leftPart z‖ ^ 2
          + 2 * ‖B‖ * ‖leftPart z‖ * ‖rightPart z‖
          + ‖D‖ * ‖rightPart z‖ ^ 2 := hterms
      _ ≤ Λ * (‖leftPart z‖ ^ 2 + ‖rightPart z‖ ^ 2) := hscalar
      _ = Λ * ‖z‖ ^ 2 := by rw [left_right_norm_sq]
  have hray : ∀ z, T.rayleighQuotient z ≤ Λ := by
    intro z
    by_cases hz : z = 0
    · subst z
      simpa using hΛ
    · change T.reApplyInnerSelf z / ‖z‖ ^ 2 ≤ Λ
      rw [div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz))]
      exact hquad z
  change ‖H‖ ≤ Λ
  rw [Matrix.cstar_norm_def]
  change ‖T‖ ≤ Λ
  rw [T.norm_eq_iSup_rayleighQuotient hTpos.isSymmetric]
  apply ciSup_le
  intro z
  rw [abs_of_nonneg]
  · exact hray z
  · by_cases hz : z = 0
    · subst z
      simp
    · change 0 ≤ T.reApplyInnerSelf z / ‖z‖ ^ 2
      exact div_nonneg (hTpos.2 z) (sq_nonneg _)

/-- Full exact package: operator enclosure plus the already proved sharp
strict-contraction criterion. -/
theorem sharp_positive_head_tail_exact {h t : Type*}
    [Fintype h] [Fintype t] [DecidableEq h] [DecidableEq t]
    (A : Matrix h h ℂ) (B : Matrix h t ℂ) (D : Matrix t t ℂ)
    (hH : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    ‖Matrix.fromBlocks A B Bᴴ D‖ ≤
        (‖A‖ + ‖D‖ + Real.sqrt ((‖A‖ - ‖D‖) ^ 2 + 4 * ‖B‖ ^ 2)) / 2
    ∧ (‖A‖ < 1 → ‖D‖ < 1 →
      ((‖A‖ + ‖D‖ + Real.sqrt
          ((‖A‖ - ‖D‖) ^ 2 + 4 * ‖B‖ ^ 2)) / 2 < 1
        ↔ ‖B‖ ^ 2 < (1 - ‖A‖) * (1 - ‖D‖))) := by
  refine ⟨sharp_positive_head_tail_opNorm A B D hH, ?_⟩
  intro hA hD
  exact sharp_positive_head_tail.2 ‖A‖ ‖B‖ ‖D‖ (norm_nonneg B) hA hD

end NCG
