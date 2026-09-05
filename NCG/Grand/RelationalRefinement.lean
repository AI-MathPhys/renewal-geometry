/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact harmonic lift and common-screen handoff
  (`thm:relational-refinement-handoff`,
  Gran-Tensor manuscript)

* `relational_refinement_handoff`: in block coordinates
  `fine = coarse ⊕ detail` with fine action
  `M_Y = [[A, B], [B*, D]]`, the harmonic lift RC.18
  `𝓗u = Ju - KD⁻¹B*u = u ⊕ (-D⁻¹B*u)`
  (i) attains exactly the effective old action — the boxed
      RC.19 `⟨𝓗u, M_Y 𝓗u⟩ = ⟨u, S_{Y/X}u⟩` with
      `S_{Y/X} = A - BD⁻¹B*`; and
  (ii) minimizes the fine energy over all detail
      completions: for every detail choice `y` the fine
      energy exceeds the effective action by the exact
      positive square
      `(y + D⁻¹B*u)* D (y + D⁻¹B*u)` (completion of the
      square), which is PSD whenever `D` is.

So `σ_{Y/X} = 0` is exact effective old-sector transport.
The pseudoinverse/range-condition formulation, the RC.20
cofinal summability giving the common-screen limit of
forms, resolvents, projections, Hodge complexes and
traces, and the constructive failure branches are the
manuscript's Part I-B layer.  The boundary-complete
refinement RC.21 is the boundary-complete short
(`NCG.gt_boundary_complete_short`) applied to the
refinement packet.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:relational-refinement-handoff` (RC.18–RC.19 and
the fine-energy minimization). -/
theorem relational_refinement_handoff {p q m : Type}
    [Fintype p] [Fintype q] [DecidableEq q]
    (A : Matrix p p ℂ) (B : Matrix p q ℂ)
    (D : Matrix q q ℂ) [Invertible D] (hD : Dᴴ = D)
    (u : Matrix p m ℂ) :
    -- (ii) completion of the square over all detail
    -- completions
    (∀ y : Matrix q m ℂ,
      uᴴ * A * u + uᴴ * B * y + yᴴ * (Bᴴ * u)
          + yᴴ * D * y
        = uᴴ * (A - B * D⁻¹ * Bᴴ) * u
          + (y + D⁻¹ * (Bᴴ * u))ᴴ * D
            * (y + D⁻¹ * (Bᴴ * u)))
    -- (i) the boxed RC.19: the harmonic lift attains the
    -- effective old action exactly
    ∧ (uᴴ * A * u + uᴴ * B * (-(D⁻¹ * (Bᴴ * u)))
        + (-(D⁻¹ * (Bᴴ * u)))ᴴ * (Bᴴ * u)
        + (-(D⁻¹ * (Bᴴ * u)))ᴴ * D
          * (-(D⁻¹ * (Bᴴ * u)))
        = uᴴ * (A - B * D⁻¹ * Bᴴ) * u) := by
  have hDinvH : (D⁻¹)ᴴ = D⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hD]
  have hwH : (D⁻¹ * (Bᴴ * u))ᴴ = uᴴ * (B * D⁻¹) := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hDinvH,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hw1 : D * (D⁻¹ * (Bᴴ * u)) = Bᴴ * u :=
    Matrix.mul_inv_cancel_left_of_invertible _ _
  have hw2 : uᴴ * (B * D⁻¹) * D = uᴴ * B := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.inv_mul_of_invertible, Matrix.mul_one]
  have key : ∀ y : Matrix q m ℂ,
      uᴴ * A * u + uᴴ * B * y + yᴴ * (Bᴴ * u)
          + yᴴ * D * y
        = uᴴ * (A - B * D⁻¹ * Bᴴ) * u
          + (y + D⁻¹ * (Bᴴ * u))ᴴ * D
            * (y + D⁻¹ * (Bᴴ * u)) := by
    intro y
    rw [Matrix.conjTranspose_add, hwH]
    simp only [Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    rw [hw1, Matrix.inv_mul_cancel_left_of_invertible]
    abel
  refine ⟨key, ?_⟩
  have h := key (-(D⁻¹ * (Bᴴ * u)))
  rw [neg_add_cancel] at h
  simp only [Matrix.conjTranspose_zero,
    Matrix.zero_mul, Matrix.mul_zero, add_zero] at h
  exact h

end NCG
