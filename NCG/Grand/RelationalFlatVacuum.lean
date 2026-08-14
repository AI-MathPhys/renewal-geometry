/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Explicit conservative flat-vacuum branch
  (`cor:relational-flat-vacuum`, Gran-Tensor manuscript)

* `relational_flat_vacuum`: the core of the boxed RC.13 —
  the twelve oriented `A₃` roots `±eᵢ ± eⱼ` form a tight
  frame: `∑ ρρᵀ = 8·I₃`, so with rate `1/(8h²)` per root
  the effective spatial metric is exactly `𝓑_h = I₃`; and
  the conductance arithmetic — vertex mass `h³` at rate
  `1/(8h²)` gives every undirected root-edge conductance
  exactly `h/8`.

The lattice-cylinder packaging (`ϱ_h = 1`, `N_h = 1`,
`β_h = 0`, vanishing depth-four residuals, the Store
cylinder recovery), the convergence of the spatial
generators to `½Δ_{𝕋³}` along cofinal scalar-period
sequences, and the boxed RC.14 Lorentzian vacuum limit
are the manuscript's Part I construction on top of this
frame identity.
-/

open Matrix Finset

namespace NCG

/-- The twelve oriented `A₃` roots. -/
def a3Roots : Fin 12 → (Fin 3 → ℝ) :=
  ![![1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 0],
    ![1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, -1],
    ![0, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, -1]]

/-- `cor:relational-flat-vacuum` (the RC.13 frame identity
and the conductance arithmetic). -/
theorem relational_flat_vacuum :
    -- the boxed 𝓑_h = I₃ tight-frame identity
    ((∑ r, vecMulVec (a3Roots r) (a3Roots r))
      = (8 : ℝ) • 1)
    -- the boxed conductance: mass h³ at rate 1/(8h²)
    -- yields h/8 per root edge
    ∧ (∀ h : ℝ, h ≠ 0 →
        h ^ 3 * (1 / (8 * h ^ 2)) = h / 8) := by
  constructor
  · ext i j
    rw [Matrix.sum_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [a3Roots, Matrix.vecMulVec_apply,
        Fin.sum_univ_succ, Matrix.smul_apply,
        Matrix.one_apply]
  · intro h hh
    field_simp

end NCG
