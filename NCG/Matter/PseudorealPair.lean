/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pseudoreal pair (`lem:pseudoreal-pair`, SM manuscript)

The weak doublet `W ≅ ℂ²` carries the quaternionic antiunitary
`ε_W = iσ₂𝖪` with `ε_W² = −1`.  For every `H = (h₁, h₂)ᵀ`, the
partner `H̃ = ε_W H = (h̄₂, −h̄₁)ᵀ` is orthogonal to `H` and
`ε_W H̃ = −H`: one reality-complete primitive scalar orbit supplies
exactly two independent weak-singlet contraction directions
(exhausting the doublet, since `dim_ℂ W = 2`).
-/

open ComplexConjugate

namespace NCG

/-- The quaternionic antiunitary `ε_W = iσ₂𝖪` on the weak doublet:
`(h₁, h₂) ↦ (h̄₂, −h̄₁)`. -/
def epsilonW (H : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![conj (H 1), -conj (H 0)]

/-- `lem:pseudoreal-pair`: the partner `H̃ = ε_W H` is orthogonal
to `H` and `ε_W H̃ = −H`. -/
theorem pseudoreal_pair (H : Fin 2 → ℂ) (_hH : H ≠ 0) :
    (∑ i : Fin 2, conj (H i) * epsilonW H i) = 0 ∧
      epsilonW (epsilonW H) = -H := by
  constructor
  · rw [Fin.sum_univ_two]
    simp only [epsilonW, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · funext i
    fin_cases i <;>
      simp [epsilonW]

end NCG
