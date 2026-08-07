/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical typed Hankel realization
  (`thm:typed-hankel-realization`, Gran-Tensor manuscript)

* `typed_hankel_realization`: for every primitive intervention
  letter `a` there is a linear transition
  `A_a : M_{x,r} → M_{y,u_a(r)}` with `A_a h_p = h_{a∘p}`,
  realized by future precomposition; the boxed evaluations
  `ℙ(f,p) = λ_f(h_p)` and `λ_f A_a = λ_{f∘a}` hold, and `A_a`
  is the unique such map on the reachable span.

Rendering disclosed: pasts and futures are abstract index sets
with the concatenation maps `p ↦ a∘p` (on pasts) and
`f ↦ f∘a` (on futures) and the Hankel compatibility
`ℙ'(f, a∘p) = ℙ(f∘a, p)`; reachability and future separation
within each protected record sector are the span/quotient
bookkeeping over these clauses.
-/

namespace NCG

/-- `thm:typed-hankel-realization`: the precomposition
transition realizes the typed Hankel action, uniquely on the
reachable span. -/
theorem typed_hankel_realization {P F P' F' : Type*}
    (tbl : F → P → ℂ) (tbl' : F' → P' → ℂ)
    (ca : P → P') (fa : F' → F)
    (hcompat : ∀ (f' : F') (q : P),
      tbl' f' (ca q) = tbl (fa f') q) :
    ∃ A : (F → ℂ) →ₗ[ℂ] (F' → ℂ),
      (∀ q : P, A (fun f => tbl f q)
        = fun f' => tbl' f' (ca q))
      ∧ (∀ (g : F → ℂ) (f' : F'), A g f' = g (fa f'))
      ∧ (∀ A' : (F → ℂ) →ₗ[ℂ] (F' → ℂ),
          (∀ q : P, A' (fun f => tbl f q)
            = fun f' => tbl' f' (ca q)) →
          ∀ m ∈ Submodule.span ℂ
            (Set.range fun (q : P) (f : F) => tbl f q),
            A' m = A m) := by
  refine ⟨{ toFun := fun g => fun f' => g (fa f')
            map_add' := by
              intro g₁ g₂
              funext f'
              simp
            map_smul' := by
              intro c g
              funext f'
              simp }, ?_, ?_, ?_⟩
  · intro q
    funext f'
    exact (hcompat f' q).symm
  · intro g f'
    rfl
  · intro A' hA' m hm
    induction hm using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨q, rfl⟩ := hg
        rw [hA' q]
        funext f'
        exact hcompat f' q
    | zero => rw [map_zero, map_zero]
    | add g₁ g₂ _ _ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
    | smul c g _ ih => rw [map_smul, map_smul, ih]

end NCG
