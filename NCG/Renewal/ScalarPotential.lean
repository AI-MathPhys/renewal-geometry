/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Worked reversible reset-diffusion residue

**Proposition `prop:renewal-scalar-potential`**: the ground-state
transform `Θψ = ρ^{1/2}ψ` of the reversible reset-diffusion generator
removes the gradient drift and leaves the bounded scalar residue

`V_ren = D·ρ^{−1/2}Δρ^{1/2} = D·(½·Δρ/ρ − ¼·|∇ρ|²/ρ²)`.

Proved cores (with `s = √ρ`, so `ρ = s²`, and the chain-rule values
`(√ρ)' = ρ'/(2s)`, `(√ρ)'' = ρ''/(2s) − ρ'²/(4ρs)`):

* `NCG.ground_state_potential` — the residual `s''/s` is exactly
  `ρ''/(2ρ) − ρ'²/(4ρ²)`;
* `NCG.potential_bound` — the sup bound
  `|V_ren| ≤ D(‖Δρ‖∞/(2ρ₋) + ‖∇ρ‖∞²/(4ρ₋²))` under the two-sided
  density bounds.

The `C²_b` PDE-level conjugation identity is the noted step.
-/

namespace NCG

/-- **Proposition `prop:renewal-scalar-potential` (residue
formula)**: with `s = √ρ` (`ρ = s²`) and the chain-rule second
derivative `s'' = ρ''/(2s) − ρ'²/(4ρs)`, the ground-state residual is
exactly `s''/s = ρ''/(2ρ) − ρ'²/(4ρ²)`. -/
theorem ground_state_potential (s ρ' ρ'' : ℝ) (hs : 0 < s) :
    (ρ'' / (2 * s) - ρ' ^ 2 / (4 * (s * s) * s)) / s
      = ρ'' / (2 * (s * s)) - ρ' ^ 2 / (4 * (s * s) ^ 2) := by
  field_simp

/-- **Proposition `prop:renewal-scalar-potential` (sup bound)**: under
the two-sided density bound `ρ ≥ ρ₋ > 0` and derivative bounds
`|Δρ| ≤ B₂`, `|∇ρ| ≤ B₁`, the residue is bounded by
`D(B₂/(2ρ₋) + B₁²/(4ρ₋²))`. -/
theorem potential_bound (D ρ B1 B2 ρm ρ' ρ'' : ℝ) (hD : 0 ≤ D)
    (hρm : 0 < ρm) (hρ : ρm ≤ ρ) (h2 : |ρ''| ≤ B2) (h1 : |ρ'| ≤ B1) :
    |D * (ρ'' / (2 * ρ) - ρ' ^ 2 / (4 * ρ ^ 2))|
      ≤ D * (B2 / (2 * ρm) + B1 ^ 2 / (4 * ρm ^ 2)) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hρm hρ
  have hB2 : 0 ≤ B2 := le_trans (abs_nonneg _) h2
  rw [abs_mul, abs_of_nonneg hD]
  refine mul_le_mul_of_nonneg_left ?_ hD
  have e1 : |ρ'' / (2 * ρ)| = |ρ''| / (2 * ρ) := by
    rw [abs_div, abs_of_pos (show (0:ℝ) < 2 * ρ by positivity)]
  have e2 : |ρ' ^ 2 / (4 * ρ ^ 2)| = ρ' ^ 2 / (4 * ρ ^ 2) := by
    rw [abs_of_nonneg (by positivity)]
  have hstep : |ρ'' / (2 * ρ) - ρ' ^ 2 / (4 * ρ ^ 2)|
      ≤ |ρ'' / (2 * ρ)| + |ρ' ^ 2 / (4 * ρ ^ 2)| := by
    rw [sub_eq_add_neg]
    calc |ρ'' / (2 * ρ) + -(ρ' ^ 2 / (4 * ρ ^ 2))|
        ≤ |ρ'' / (2 * ρ)| + |-(ρ' ^ 2 / (4 * ρ ^ 2))| := abs_add_le _ _
      _ = |ρ'' / (2 * ρ)| + |ρ' ^ 2 / (4 * ρ ^ 2)| := by rw [abs_neg]
  calc |ρ'' / (2 * ρ) - ρ' ^ 2 / (4 * ρ ^ 2)|
      ≤ |ρ'' / (2 * ρ)| + |ρ' ^ 2 / (4 * ρ ^ 2)| := hstep
    _ = |ρ''| / (2 * ρ) + ρ' ^ 2 / (4 * ρ ^ 2) := by rw [e1, e2]
    _ ≤ B2 / (2 * ρm) + B1 ^ 2 / (4 * ρm ^ 2) := by
        have hsq : ρ' ^ 2 ≤ B1 ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        gcongr

end NCG
