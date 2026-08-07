/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConstraintCharacter

/-!
# Exact solution count
  (`corollary:exact-solution-count`, Gran-Tensor manuscript)

* `exact_solution_count`: the constrained system `Ax = b` over a
  finite abelian group has exactly `|Ker A|` solutions when `b`
  is in the range of `A`, and none otherwise.

Rendering disclosed: the manuscript derives this from the
constraint–character duality with unit weights and character
orthogonality on `Gᵐ/Ran A`; the rendered content is the exact
count itself, proved by the kernel-coset bijection (the finite
rank–nullity identity supplying the factor `|Ker A|`).  The
constraint group is written multiplicatively as in
`constraint_character`.
-/

namespace NCG

/-- `corollary:exact-solution-count`: `#{x : Ax = b}` is
`|Ker A|` if `b ∈ Ran A` and `0` otherwise. -/
theorem exact_solution_count {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] {n m : ℕ}
    (A : (Fin n → G) →* (Fin m → G)) (b : Fin m → G) :
    Nat.card {x : Fin n → G // A x = b}
      = if ∃ x₀, A x₀ = b
        then Nat.card {x : Fin n → G // A x = 1}
        else 0 := by
  by_cases hb : ∃ x₀, A x₀ = b
  · rw [if_pos hb]
    obtain ⟨x₀, hx₀⟩ := hb
    refine Nat.card_congr ⟨fun x => ⟨x₀⁻¹ * x.1, ?_⟩,
      fun k => ⟨x₀ * k.1, ?_⟩, ?_, ?_⟩
    · rw [map_mul, map_inv, hx₀, x.2, inv_mul_cancel]
    · rw [map_mul, hx₀, k.2, mul_one]
    · intro x
      exact Subtype.ext (by simp)
    · intro k
      exact Subtype.ext (by simp)
  · rw [if_neg hb]
    have : IsEmpty {x : Fin n → G // A x = b} :=
      ⟨fun x => hb ⟨x.1, x.2⟩⟩
    exact Nat.card_of_isEmpty
end NCG
