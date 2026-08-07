/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Global-record obstruction to local saturation
  (`thm:global-record-saturation-obstruction`,
   Gran-Tensor manuscript)

* `global_record_saturation_obstruction`: if a unitary `U` fixes
  the source vector `Ω` and every primitive writer, then every
  `U`-eigenvector with nontrivial character `χ ≠ 1` is
  orthogonal to the writer closure `span(𝔅Ω)` — a source sector
  carrying a nontrivial global record character cannot be
  recovered after the record is discarded from the primitive
  interface.

Rendering disclosed: `U` is rendered by its inner-product
preservation (the unitarity clause used); the closure is the
span (finite-dimensional carriers).
-/

open InnerProductSpace

namespace NCG

/-- `thm:global-record-saturation-obstruction`. -/
theorem global_record_saturation_obstruction {V ι : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : V →ₗ[ℂ] V) (hU : ∀ x y : V, ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Om : V) (b : ι → (V →ₗ[ℂ] V))
    (hfix : ∀ i, U (b i Om) = b i Om)
    (v : V) (χ : ℂ) (hχ : χ ≠ 1) (hv : U v = χ • v) :
    (∀ i, ⟪v, b i Om⟫_ℂ = 0)
    ∧ (∀ w ∈ Submodule.span ℂ (Set.range fun i => b i Om),
        ⟪v, w⟫_ℂ = 0) := by
  have hχ' : (starRingEnd ℂ) χ ≠ 1 := by
    intro h
    apply hχ
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have hone : ∀ i, ⟪v, b i Om⟫_ℂ = 0 := by
    intro i
    have h1 : ⟪v, b i Om⟫_ℂ = ⟪U v, U (b i Om)⟫_ℂ :=
      (hU v (b i Om)).symm
    rw [hfix i, hv, inner_smul_left] at h1
    have h2 : (1 - (starRingEnd ℂ) χ) * ⟪v, b i Om⟫_ℂ = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (by linear_combination -h) hχ'
    · exact h
  refine ⟨hone, ?_⟩
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hone i
  | zero => exact inner_zero_right v
  | add x y hx hy ihx ihy =>
      rw [inner_add_right, ihx, ihy, add_zero]
  | smul c x hx ihx =>
      rw [inner_smul_right, ihx, mul_zero]

end NCG
