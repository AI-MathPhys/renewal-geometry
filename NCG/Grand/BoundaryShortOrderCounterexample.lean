/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTBoundaryShort

/-!
# Boundary shorting has no uniform multiplicative comparison

The scalar packet is represented by its literal positive `2 × 2` complete
Gram.  Its retained Schur complement is computed from the matrix blocks, and
the resulting ratio is proved unbounded.
-/

open Matrix

namespace NCG

/-- Complete Gram for `A = B = 0`, `C = 1`, `D_H = 1`, `D_T = t`. -/
def scalarBoundaryCompleteGram (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, t; t, 1 + t ^ 2]

/-- The retained scalar Schur complement of a `2 × 2` block matrix, with
coordinate `1` eliminated. -/
noncomputable def retainedScalarSchur (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  M 0 0 - M 0 1 * (M 1 1)⁻¹ * M 1 0

/-- The complete scalar packet is positive semidefinite. -/
theorem scalarBoundaryCompleteGram_posSemidef (t : ℝ) :
    (scalarBoundaryCompleteGram t).PosSemidef := by
  have hfactor : scalarBoundaryCompleteGram t =
      (!![1; t] : Matrix (Fin 2) (Fin 1) ℝ) *
          (!![1; t] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ
        + (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ) *
          (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [scalarBoundaryCompleteGram, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_one] <;> ring
  rw [hfactor]
  exact (Matrix.posSemidef_self_mul_conjTranspose
    (!![1; t] : Matrix (Fin 2) (Fin 1) ℝ)).add
      (Matrix.posSemidef_self_mul_conjTranspose
        (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ))

/-- The four entries of the complete scalar packet. -/
theorem scalarBoundaryCompleteGram_entries (t : ℝ) :
    scalarBoundaryCompleteGram t 0 0 = 1 ∧
      scalarBoundaryCompleteGram t 0 1 = t ∧
      scalarBoundaryCompleteGram t 1 0 = t ∧
      scalarBoundaryCompleteGram t 1 1 = 1 + t ^ 2 := by
  norm_num [scalarBoundaryCompleteGram]

/-- The boxed boundary-complete value is derived from the literal Schur
complement of the complete Gram. -/
theorem scalarBoundaryCompleteGram_short (t : ℝ) :
    retainedScalarSchur (scalarBoundaryCompleteGram t) = (1 + t ^ 2)⁻¹ := by
  obtain ⟨h00, h01, h10, h11⟩ := scalarBoundaryCompleteGram_entries t
  rw [retainedScalarSchur, h00, h01, h10, h11]
  have hne : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The frozen harmonic lift has the boxed naive value `1`. -/
theorem scalarBoundaryNaive_value (t : ℝ) :
    (0 : ℝ) + 1 ^ 2 = 1 := by ring

/-- `cth:GT-boundary-short-order`, fully quantified: no real constant
uniformly dominates the frozen value by the boundary-complete short. -/
theorem no_uniform_boundary_short_multiplicative_control :
    ¬ ∃ c : ℝ, ∀ t : ℝ,
      1 ≤ c * retainedScalarSchur (scalarBoundaryCompleteGram t) := by
  rintro ⟨c, hc⟩
  by_cases hc0 : c < 0
  · have h := hc 0
    rw [scalarBoundaryCompleteGram_short] at h
    norm_num at h
    linarith
  · have hc_nonneg : 0 ≤ c := le_of_not_gt hc0
    have h := hc (c + 1)
    rw [scalarBoundaryCompleteGram_short] at h
    have hden : 0 < 1 + (c + 1) ^ 2 := by positivity
    have hlt : c / (1 + (c + 1) ^ 2) < 1 := by
      rw [div_lt_one hden]
      nlinarith [sq_nonneg c]
    have heq : c * (1 + (c + 1) ^ 2)⁻¹ =
        c / (1 + (c + 1) ^ 2) := by
      rw [div_eq_mul_inv]
    rw [heq] at h
    linarith

end NCG
