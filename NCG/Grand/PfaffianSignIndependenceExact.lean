/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pfaffian sign data are not determined by determinant-square data

This file proves the finite counterexample content of
thm:SMQG-Pfaffian-sign.  The real skew two-by-two family has Pfaffian t and
determinant t squared.  It therefore exhibits the missing chart sign and zero
crossing parity.  A one-edge real sign line gives two locally square-identical
systems with opposite loop holonomy.
-/

open Matrix

namespace NCG
namespace PfaffianSignIndependence

/-- The universal real two-by-two skew block. -/
def skewBlock (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, t; -t, 0]

/-- In dimension two the Pfaffian is the upper-right entry. -/
def pfaffianTwo (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  A 0 1

@[simp] theorem pfaffianTwo_skewBlock (t : ℝ) :
    pfaffianTwo (skewBlock t) = t := by
  simp [pfaffianTwo, skewBlock]

theorem skewBlock_transpose (t : ℝ) :
    (skewBlock t)ᵀ = -skewBlock t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewBlock]

theorem det_skewBlock (t : ℝ) :
    (skewBlock t).det = t ^ 2 := by
  simp [skewBlock, Matrix.det_fin_two]
  ring

/-- Pfaffian squared equals the determinant on the universal two-dimensional
skew family. -/
theorem pfaffian_sq_eq_det (t : ℝ) :
    pfaffianTwo (skewBlock t) ^ 2 = (skewBlock t).det := by
  rw [pfaffianTwo_skewBlock, det_skewBlock]

/-- Determinant-square data do not determine a real Pfaffian sign. -/
theorem determinantSquare_not_injective :
    ¬ Function.Injective (fun q : ℝ => q ^ 2) := by
  intro h
  have heq : (1 : ℝ) = -1 := h (by norm_num)
  norm_num at heq

theorem opposite_pfaffian_same_determinant {t : ℝ} (ht : t ≠ 0) :
    (skewBlock t).det = (skewBlock (-t)).det ∧
      pfaffianTwo (skewBlock t) ≠ pfaffianTwo (skewBlock (-t)) := by
  constructor
  · simp [det_skewBlock]
  · simp only [pfaffianTwo_skewBlock]
    exact fun h => ht (by linarith)

/-- The path through the skew divisor has a Pfaffian sign crossing while its
determinant is the nonnegative square. -/
theorem skewBlock_zero_crossing :
    pfaffianTwo (skewBlock (-1)) < 0 ∧
      pfaffianTwo (skewBlock 0) = 0 ∧
      0 < pfaffianTwo (skewBlock 1) ∧
      (∀ t : ℝ, 0 ≤ (skewBlock t).det) := by
  refine ⟨by simp, by simp, by simp, fun t => ?_⟩
  rw [det_skewBlock]
  exact sq_nonneg t

/-! ## A finite real-line holonomy witness -/

/-- A one-edge loop is enough to retain an independent real orientation
holonomy. -/
abbrev OneEdgeLoop := Fin 1

/-- Local determinant-square data of real transition signs. -/
def localSquares (s : OneEdgeLoop → ℝ) : OneEdgeLoop → ℝ :=
  fun e => (s e) ^ 2

/-- Product of the real transition signs around the loop. -/
def loopHolonomy (s : OneEdgeLoop → ℝ) : ℝ :=
  ∏ e, s e

def positiveFrame : OneEdgeLoop → ℝ := fun _ => 1
def negativeFrame : OneEdgeLoop → ℝ := fun _ => -1

theorem frames_have_same_local_squares :
    localSquares positiveFrame = localSquares negativeFrame := by
  funext e
  fin_cases e
  norm_num [localSquares, positiveFrame, negativeFrame]

theorem frames_have_opposite_holonomy :
    loopHolonomy positiveFrame = 1 ∧
      loopHolonomy negativeFrame = -1 := by
  constructor <;> simp [loopHolonomy, positiveFrame, negativeFrame]

/-- Complete finite certificate for thm:SMQG-Pfaffian-sign: determinant-square
data fail to determine the chart sign, the parity of the displayed zero
crossing, and the real-line loop holonomy. -/
theorem pfaffian_sign_remains_independent :
    (¬ Function.Injective (fun q : ℝ => q ^ 2)) ∧
      (pfaffianTwo (skewBlock (-1)) < 0 ∧
        pfaffianTwo (skewBlock 0) = 0 ∧
        0 < pfaffianTwo (skewBlock 1)) ∧
      localSquares positiveFrame = localSquares negativeFrame ∧
      loopHolonomy positiveFrame ≠ loopHolonomy negativeFrame := by
  refine ⟨determinantSquare_not_injective, ?_, frames_have_same_local_squares, ?_⟩
  · simpa using skewBlock_zero_crossing.1
  · rw [frames_have_opposite_holonomy.1, frames_have_opposite_holonomy.2]
    norm_num

end PfaffianSignIndependence
end NCG
