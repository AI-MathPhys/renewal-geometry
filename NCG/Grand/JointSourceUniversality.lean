/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical joint-source universality
  (`thm:joint-source-universality`, Gran-Tensor manuscript)

* `joint_source_universality`: for any Gram factor `S` of the
  joint block Gram (`SᴴS = G`): the realization inner product
  reproduces the Gram (`⟨Su, Sv⟩ = u*Gv`); the Gram kernel is
  exactly the realization kernel (well-definedness of the
  quotient); two factors of the same Gram have identical
  kernels, so the source-fixing correspondence `Su ↦ Tu` is
  well defined and inner-preserving (the uniqueness unitary on
  ranges); and the realization dimension is exactly `rank G`.

Rendering disclosed: the quotient space `(E₁⊕E₂)/Ker G` and its
universal unitary are the linear-algebra packaging of these
proved identities (well-definedness, inner preservation, and
the rank clause); invariance under support-minimal Stinespring
gauge and unread refinements is the manuscript's reading of the
Gram-only dependence proved here.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Realization inner products reproduce the Gram. -/
theorem gram_realization_inner {h e : Type*} [Fintype h]
    [Fintype e] (M : Matrix h e ℂ) (u v : e → ℂ) :
    star (M *ᵥ u) ⬝ᵥ (M *ᵥ v)
      = star u ⬝ᵥ ((Mᴴ * M) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]

/-- `thm:joint-source-universality`. -/
theorem joint_source_universality {h h' e : Type*} [Fintype h]
    [Fintype h'] [Fintype e] (S : Matrix h e ℂ)
    (T : Matrix h' e ℂ) (G : Matrix e e ℂ)
    (hS : Sᴴ * S = G) (hT : Tᴴ * T = G) :
    (∀ u v : e → ℂ,
      star (S *ᵥ u) ⬝ᵥ (S *ᵥ v) = star u ⬝ᵥ (G *ᵥ v))
    ∧ (∀ u : e → ℂ,
        star u ⬝ᵥ (G *ᵥ u) = 0 ↔ S *ᵥ u = 0)
    ∧ (∀ u u' : e → ℂ, S *ᵥ u = S *ᵥ u' → T *ᵥ u = T *ᵥ u')
    ∧ (∀ u v : e → ℂ,
        star (S *ᵥ u) ⬝ᵥ (S *ᵥ v)
          = star (T *ᵥ u) ⬝ᵥ (T *ᵥ v))
    ∧ G.rank = S.rank := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    rw [gram_realization_inner, hS]
  · intro u
    rw [← hS, ← gram_realization_inner]
    exact dotProduct_star_self_eq_zero
  · intro u u' hSu
    have hd : S *ᵥ (u - u') = 0 := by
      rw [Matrix.mulVec_sub, hSu, sub_self]
    have hG : star (u - u') ⬝ᵥ (G *ᵥ (u - u')) = 0 := by
      rw [← hS, ← gram_realization_inner, hd]
      simp
    have hTd : T *ᵥ (u - u') = 0 := by
      have h2 : star (T *ᵥ (u - u'))
          ⬝ᵥ (T *ᵥ (u - u')) = 0 := by
        rw [gram_realization_inner, hT]
        exact hG
      exact dotProduct_star_self_eq_zero.mp h2
    rw [Matrix.mulVec_sub] at hTd
    exact sub_eq_zero.mp hTd
  · intro u v
    rw [gram_realization_inner, hS, gram_realization_inner, hT]
  · rw [← hS, Matrix.rank_conjTranspose_mul_self]

end NCG
