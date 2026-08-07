/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cross-support extraction from a CP generator
  (`thm:SM-cross-support-generator`, Gran-Tensor manuscript)

* `cross_support_generator`: under the GKSL insertion, the
  `L←R` compression of the commutator and anticommutator terms
  vanishes (`P_LP_R = 0`), and only the boxed support-changing
  jump amplitudes survive:
  `P_L V (P_R X P_R) Vᴴ P_L = (P_LVP_R) X (P_RVᴴP_L)`; the
  compressed map is completely positive (Kraus form).

Rendering disclosed: the operational small-time limit
`t⁻¹P_L T_t(·)P_L → Φ` is the differentiability of the matrix
semigroup at zero (the manuscript's analytic clause); GKSL
coordinate independence is the statement that the compression
is defined from the generator itself.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:SM-cross-support-generator`. -/
theorem cross_support_generator {n : Type*} [Fintype n]
    (PL PR : Matrix n n ℂ) (hLR : PL * PR = 0)
    (hRL : PR * PL = 0) (H V X : Matrix n n ℂ) :
    -- (1) the Hamiltonian commutator dies under compression
    (PL * (H * (PR * X * PR) - (PR * X * PR) * H) * PL = 0)
    -- (2) the anticommutator term dies under compression
    ∧ (PL * ((Vᴴ * V) * (PR * X * PR)
        + (PR * X * PR) * (Vᴴ * V)) * PL = 0)
    -- (3) only the jump amplitudes survive
    ∧ (PL * (V * (PR * X * PR) * Vᴴ) * PL
        = (PL * V * PR) * X * (PR * Vᴴ * PL))
    -- (4) the compressed map is completely positive
    ∧ (∀ Y : Matrix n n ℂ, Y.PosSemidef →
        ((PL * V * PR) * Y * (PL * V * PR)ᴴ).PosSemidef) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : PL * (H * (PR * X * PR)) * PL
        = (PL * H * PR) * (X * (PR * PL)) := by
      simp only [Matrix.mul_assoc]
    have h2 : PL * ((PR * X * PR) * H) * PL
        = (PL * PR) * (X * (PR * H * PL)) := by
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2, hRL, hLR]
    simp
  · have h1 : PL * ((Vᴴ * V) * (PR * X * PR)) * PL
        = (PL * (Vᴴ * V) * PR) * (X * (PR * PL)) := by
      simp only [Matrix.mul_assoc]
    have h2 : PL * ((PR * X * PR) * (Vᴴ * V)) * PL
        = (PL * PR) * (X * (PR * (Vᴴ * V) * PL)) := by
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2, hRL, hLR]
    simp
  · simp only [Matrix.mul_assoc]
  · intro Y hY
    exact hY.mul_mul_conjTranspose_same (PL * V * PR)

end NCG
