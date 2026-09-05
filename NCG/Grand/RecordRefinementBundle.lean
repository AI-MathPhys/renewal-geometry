/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MinimalRecord

/-!
# Unread refinements and the correct bundle decomposition
  (`thm:record-refinement-bundle`, Gran-Tensor manuscript)

* `record_refinement_bundle`: an unread refinement (a surjection
  whose admitted responses are exactly pullbacks) induces a
  canonical bijection of minimal records; the fine function
  algebra decomposes fibrewise (`R̃ ≃ Σ_ρ F_ρ`, hence
  `C(R̃) ≅ ⊕_ρ C(F_ρ)`); the pullback subalgebra is exactly the
  fibrewise-constant functions; and a base-preserving tensor
  split exists iff every fibre has the same cardinality as `D`.

Rendering disclosed: the noncanonicity of the split (choice of
fibre trivializations) and the extra dynamical compatibility
condition are the manuscript's remarks on the proved
equal-cardinality criterion.
-/

namespace NCG

/-- `thm:record-refinement-bundle`. -/
theorem record_refinement_bundle {R' R Sig : Type*}
    (π : R' → R) (hπ : Function.Surjective π)
    (sig : R → Sig) :
    -- (1) canonical bijection of minimal records
    Nonempty (MinRec (sig ∘ π) ≃ MinRec sig)
    -- (2) fibrewise decomposition of the fine record space
    ∧ Nonempty ((Σ ρ : MinRec sig,
        {r : R // Quotient.mk (minRecSetoid sig) r = ρ}) ≃ R)
    -- (3) pullbacks are exactly the fibrewise-constant
    --     functions
    ∧ (∀ f : R → ℂ,
        (∃ g : MinRec sig → ℂ,
          ∀ r, g (Quotient.mk (minRecSetoid sig) r) = f r)
        ↔ (∀ r r', sig r = sig r' → f r = f r'))
    -- (4) base-preserving tensor split iff equal fibre
    --     cardinalities
    ∧ (∀ (D : Type) [Finite D] [Finite R],
        ((∀ ρ : MinRec sig, Nonempty
          ({r : R // Quotient.mk (minRecSetoid sig) r = ρ} ≃ D))
        ↔ (∀ ρ : MinRec sig, Nat.card
            {r : R // Quotient.mk (minRecSetoid sig) r = ρ}
            = Nat.card D))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the induced map on quotients is a bijection
    refine ⟨Equiv.ofBijective
      (Quotient.lift
        (fun r' => Quotient.mk (minRecSetoid sig) (π r'))
        (fun a b h => Quotient.sound h)) ⟨?_, ?_⟩⟩
    · intro x y hxy
      induction x using Quotient.ind with | _ a =>
      induction y using Quotient.ind with | _ b =>
      have h2 : Quotient.mk (minRecSetoid sig) (π a)
          = Quotient.mk (minRecSetoid sig) (π b) := hxy
      have h3 : sig (π a) = sig (π b) := Quotient.exact h2
      exact Quotient.sound h3
    · intro y
      induction y using Quotient.ind with
      | _ r =>
          obtain ⟨r', rfl⟩ := hπ r
          exact ⟨Quotient.mk (minRecSetoid (sig ∘ π)) r', rfl⟩
  · exact ⟨Equiv.sigmaFiberEquiv
      (Quotient.mk (minRecSetoid sig))⟩
  · intro f
    constructor
    · rintro ⟨g, hg⟩ r r' hrr
      rw [← hg r, ← hg r']
      congr 1
      exact Quotient.sound hrr
    · intro hconst
      exact ⟨Quotient.lift f (fun a b h => hconst a b h),
        fun r => rfl⟩
  · intro D _ _
    constructor
    · intro h ρ
      exact Nat.card_congr (h ρ).some
    · intro h ρ
      classical
      letI := Fintype.ofFinite R
      letI := Fintype.ofFinite D
      letI : Fintype
          {r : R // Quotient.mk (minRecSetoid sig) r = ρ} :=
        Fintype.ofFinite _
      refine ⟨Fintype.equivOfCardEq ?_⟩
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact h ρ

end NCG
