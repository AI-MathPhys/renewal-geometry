/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteWeightedSchurNorm
import NCG.Grand.WeightedLocalInverseSquareRootAndTargetContactExact

/-!
# Quasilocal connected operators after OS whitening

This file isolates the deterministic second half of
`thm:GTLOC-local-connected-OS`: once the inverse square root of the supported
Gram has the manuscript's weighted-Schur bound, two-sided whitening preserves
weighted locality and gives the claimed off-diagonal estimate.
-/

namespace NCG
namespace WeightedLocalConnectedOS

open FiniteWeightedSchurNorm
open WordHead.MatrixSeries

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

/-- The represented connected operator `H C H`, where `H = G⁻¹ᐟ²`. -/
def connectedOperator (H C : Matrix Λ Λ ℂ) : Matrix Λ Λ ℂ := H * C * H

/-- Compression to rows in `X` and columns in `Y`. -/
noncomputable def subsetCompression (X Y : Set Λ) (T : Matrix Λ Λ ℂ) :
    Matrix Λ Λ ℂ := by
  classical
  exact fun x y => if x ∈ X ∧ y ∈ Y then T x y else 0

/-- Two applications of weighted-Schur submultiplicativity. -/
theorem connectedOperator_schurNorm_le (μ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (H C : Matrix Λ Λ ℂ) :
    schurNorm μ d (connectedOperator H C) ≤
      (schurNorm μ d H) ^ 2 * schurNorm μ d C := by
  unfold connectedOperator
  calc
    schurNorm μ d (H * C * H)
        ≤ schurNorm μ d (H * C) * schurNorm μ d H :=
      schurNorm_mul_le μ d hμ hd _ _
    _ ≤ (schurNorm μ d H * schurNorm μ d C) * schurNorm μ d H :=
      mul_le_mul_of_nonneg_right (schurNorm_mul_le μ d hμ hd H C)
        (schurNorm_nonneg μ d H)
    _ = (schurNorm μ d H) ^ 2 * schurNorm μ d C := by ring

/-- The exact locality estimate in `thm:GTLOC-local-connected-OS`. -/
theorem connectedOperator_schurNorm_le_of_invSqrtBound
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (hη : η < 1) (H C : Matrix Λ Λ ℂ)
    (hH : schurNorm μ d H ≤ (Real.sqrt (1 - η))⁻¹) :
    schurNorm μ d (connectedOperator H C) ≤
      schurNorm μ d C / (1 - η) := by
  have hspos : 0 < Real.sqrt (1 - η) := Real.sqrt_pos.mpr (sub_pos.mpr hη)
  have hsq : ((Real.sqrt (1 - η))⁻¹) ^ 2 = (1 - η)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (sub_nonneg.mpr hη.le)]
  calc
    schurNorm μ d (connectedOperator H C)
        ≤ (schurNorm μ d H) ^ 2 * schurNorm μ d C :=
      connectedOperator_schurNorm_le μ d hμ hd H C
    _ ≤ ((Real.sqrt (1 - η))⁻¹) ^ 2 * schurNorm μ d C := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (schurNorm_nonneg μ d H) hH 2)
        (schurNorm_nonneg μ d C)
    _ = schurNorm μ d C / (1 - η) := by
      rw [hsq, div_eq_mul_inv]
      ring

/-- A weighted Schur bound gives exponential operator-norm decay between two
sets separated by distance at least `δ`. -/
theorem opNorm_subsetCompression_le_exp_neg_separation
    (μ δ : ℝ) (d : Λ → Λ → ℝ) (hμ : 0 ≤ μ)
    (T : Matrix Λ Λ ℂ) (X Y : Set Λ)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ d x y) :
    opNorm (subsetCompression X Y T) ≤
      Real.exp (-μ * δ) * schurNorm μ d T := by
  classical
  have hentry : ∀ x ∈ X, ∀ y ∈ Y,
      ‖T x y‖ ≤ Real.exp (-μ * δ) *
        (Real.exp (μ * d x y) * ‖T x y‖) := by
    intro x hx y hy
    have hexp : Real.exp (-μ * d x y) ≤ Real.exp (-μ * δ) :=
      Real.exp_le_exp.mpr (by nlinarith [hsep x hx y hy])
    have hid : ‖T x y‖ = Real.exp (-μ * d x y) *
        (Real.exp (μ * d x y) * ‖T x y‖) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    calc
      ‖T x y‖ = Real.exp (-μ * d x y) *
          (Real.exp (μ * d x y) * ‖T x y‖) := hid
      _ ≤ Real.exp (-μ * δ) *
          (Real.exp (μ * d x y) * ‖T x y‖) :=
        mul_le_mul_of_nonneg_right hexp
          (mul_nonneg (Real.exp_pos _).le (norm_nonneg (T x y)))
  have hrow : ∀ x, ∑ y, ‖subsetCompression X Y T x y‖ ≤
      Real.exp (-μ * δ) * schurNorm μ d T := by
    intro x
    by_cases hx : x ∈ X
    · calc
        ∑ y, ‖subsetCompression X Y T x y‖
            ≤ ∑ y, Real.exp (-μ * δ) *
                (Real.exp (μ * d x y) * ‖T x y‖) := by
              apply Finset.sum_le_sum
              intro y hy
              by_cases hyY : y ∈ Y
              · simpa [subsetCompression, hx, hyY] using hentry x hx y hyY
              · simp [subsetCompression, hx, hyY]
                positivity
        _ = Real.exp (-μ * δ) * schurRow μ d T x := by
              unfold schurRow
              rw [Finset.mul_sum]
        _ ≤ Real.exp (-μ * δ) * schurNorm μ d T :=
              mul_le_mul_of_nonneg_left (schurRow_le_schurNorm μ d T x)
                (Real.exp_pos _).le
    · simp [subsetCompression, hx,
        mul_nonneg (Real.exp_pos _).le (schurNorm_nonneg μ d T)]
  have hcol : ∀ y, ∑ x, ‖subsetCompression X Y T x y‖ ≤
      Real.exp (-μ * δ) * schurNorm μ d T := by
    intro y
    by_cases hy : y ∈ Y
    · calc
        ∑ x, ‖subsetCompression X Y T x y‖
            ≤ ∑ x, Real.exp (-μ * δ) *
                (Real.exp (μ * d x y) * ‖T x y‖) := by
              apply Finset.sum_le_sum
              intro x hx
              by_cases hxX : x ∈ X
              · simpa [subsetCompression, hxX, hy] using hentry x hxX y hy
              · simp [subsetCompression, hxX]
                positivity
        _ = Real.exp (-μ * δ) * schurCol μ d T y := by
              unfold schurCol
              rw [Finset.mul_sum]
        _ ≤ Real.exp (-μ * δ) * schurNorm μ d T :=
              mul_le_mul_of_nonneg_left (schurCol_le_schurNorm μ d T y)
                (Real.exp_pos _).le
    · simp [subsetCompression, hy,
        mul_nonneg (Real.exp_pos _).le (schurNorm_nonneg μ d T)]
  simpa using opNorm_le_max_rowCol (subsetCompression X Y T)
    (Real.exp (-μ * δ) * schurNorm μ d T)
    (Real.exp (-μ * δ) * schurNorm μ d T) hrow hcol
    (mul_nonneg (Real.exp_pos _).le (schurNorm_nonneg μ d T))
    (mul_nonneg (Real.exp_pos _).le (schurNorm_nonneg μ d T))

/-- The exact separated-support estimate for the whitened connected operator. -/
theorem connectedOperator_offDiagonal_le_of_invSqrtBound
    (μ η δ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (hη : η < 1) (H C : Matrix Λ Λ ℂ)
    (hH : schurNorm μ d H ≤ (Real.sqrt (1 - η))⁻¹)
    (X Y : Set Λ) (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ d x y) :
    opNorm (subsetCompression X Y (connectedOperator H C)) ≤
      Real.exp (-μ * δ) / (1 - η) * schurNorm μ d C := by
  have hoff := opNorm_subsetCompression_le_exp_neg_separation
    μ δ d hμ (connectedOperator H C) X Y hsep
  have hschur := connectedOperator_schurNorm_le_of_invSqrtBound
    μ η d hμ hd hη H C hH
  calc
    opNorm (subsetCompression X Y (connectedOperator H C))
        ≤ Real.exp (-μ * δ) * schurNorm μ d (connectedOperator H C) := hoff
    _ ≤ Real.exp (-μ * δ) * (schurNorm μ d C / (1 - η)) :=
      mul_le_mul_of_nonneg_left hschur (Real.exp_pos _).le
    _ = Real.exp (-μ * δ) / (1 - η) * schurNorm μ d C := by ring

/-- The connected operator formed with the canonical positive inverse square
root of the normalized word Gram. -/
noncomputable def canonicalConnectedOperator
    (E C : Matrix Λ Λ ℂ) : Matrix Λ Λ ℂ :=
  connectedOperator (invSqrtMatrixSeries E) C

/-- Canonical OS whitening preserves the weighted-Schur locality bound. -/
theorem canonicalConnectedOperator_schurNorm_le
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (hdiag : ∀ x, d x x = 0)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E C : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η) :
    schurNorm μ d (canonicalConnectedOperator E C) ≤
      schurNorm μ d C / (1 - η) := by
  apply connectedOperator_schurNorm_le_of_invSqrtBound
    μ η d hμ hd hη1 (invSqrtMatrixSeries E) C
  exact schurNorm_invSqrtMatrixSeries_le
    μ η d hμ hd0 hd hdiag hη0 hη1 E hE

/-- Canonical OS whitening gives exponential operator-norm decay between
separated word-support sets. -/
theorem canonicalConnectedOperator_offDiagonal_le
    (μ η δ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (hdiag : ∀ x, d x x = 0)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E C : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η)
    (X Y : Set Λ) (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ d x y) :
    opNorm (subsetCompression X Y (canonicalConnectedOperator E C)) ≤
      Real.exp (-μ * δ) / (1 - η) * schurNorm μ d C := by
  apply connectedOperator_offDiagonal_le_of_invSqrtBound
    μ η δ d hμ hd hη1 (invSqrtMatrixSeries E) C
  · exact schurNorm_invSqrtMatrixSeries_le
      μ η d hμ hd0 hd hdiag hη0 hη1 E hE
  · exact hsep

/-- **Quasilocal connected operator on the OS quotient.**  Both the
weighted-Schur estimate and its separated-support consequence hold for the
canonical positive OS whitening. -/
theorem localConnectedOS
    (μ η δ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (hdiag : ∀ x, d x x = 0)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E C : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η)
    (X Y : Set Λ) (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ d x y) :
    schurNorm μ d (canonicalConnectedOperator E C) ≤
        schurNorm μ d C / (1 - η) ∧
      opNorm (subsetCompression X Y (canonicalConnectedOperator E C)) ≤
        Real.exp (-μ * δ) / (1 - η) * schurNorm μ d C := by
  exact ⟨canonicalConnectedOperator_schurNorm_le
      μ η d hμ hd0 hd hdiag hη0 hη1 E C hE,
    canonicalConnectedOperator_offDiagonal_le
      μ η δ d hμ hd0 hd hdiag hη0 hη1 E C hE X Y hsep⟩

end WeightedLocalConnectedOS
end NCG
