/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SemanticStripping
import NCG.Grand.GeneratedMinimalRecord

/-!
# Reconstruction-level semantic stripping

This file completes `thm:renewal-semantic-stripping` at the reconstruction
level.  Rather than assuming that a restricted table is unchanged, it derives
equality of the complete past--future Hankel table from the label-marginal
identity.  The canonical minimal record and Hankel response space therefore
agree, and in fact every construction depending only on the renewal table has
the same value before and after the conservative loading.
-/

namespace NCG

/-- A finite renewal word, with its length retained in the type. -/
abbrev RenewalWord (Alphabet : Type*) := Σ n : ℕ, Fin n → Alphabet

/-- Concatenation of finite renewal words. -/
def appendRenewalWord {Alphabet : Type*}
    (p f : RenewalWord Alphabet) : RenewalWord Alphabet :=
  ⟨p.1 + f.1, Fin.addCases p.2 f.2⟩

/-- Complete renewal-native past--future cylinder table. -/
def renewalHankelTable {Alphabet State : Type*}
    [Fintype State] [DecidableEq State]
    (T : Alphabet → Matrix State State ℝ) (α : State → ℝ) :
    RenewalWord Alphabet → RenewalWord Alphabet → ℂ :=
  fun f p ↦ branchCylP T α (appendRenewalWord p f).2

/-- The renewal table obtained from a label-resolved loading after forgetting
all added labels. -/
def labelMarginalHankelTable {Alphabet Label State : Type*}
    [Fintype Label] [Fintype State] [DecidableEq State]
    (T' : Alphabet × Label → Matrix State State ℝ) (α : State → ℝ) :
    RenewalWord Alphabet → RenewalWord Alphabet → ℂ :=
  fun f p ↦ ∑ labels : Fin (appendRenewalWord p f).1 → Label,
    branchCylP T' α
      (fun i ↦ ((appendRenewalWord p f).2 i, labels i))

/-- A point's complete future signature is its column in the renewal Hankel
table. -/
def renewalFutureSignature {Past Future : Type*}
    (table : Future → Past → ℂ) (p : Past) : Future → ℂ :=
  fun f ↦ table f p

/-- Forgetting conservative labels gives literal equality of the complete
past--future table, not merely equality of a selected marginal. -/
theorem labelMarginalHankelTable_eq_renewalHankelTable
    {Alphabet Label State : Type*}
    [Fintype Label] [Fintype State] [DecidableEq State]
    (T' : Alphabet × Label → Matrix State State ℝ)
    (T : Alphabet → Matrix State State ℝ)
    (hmarg : ∀ a : Alphabet, ∑ l : Label, T' (a, l) = T a)
    (α : State → ℝ) :
    labelMarginalHankelTable T' α = renewalHankelTable T α := by
  funext f p
  unfold labelMarginalHankelTable renewalHankelTable
  exact_mod_cast semantic_stripping_marginal T' T hmarg α
    (appendRenewalWord p f).2

/-- Exact reconstruction package for semantic stripping.  The table equality
is derived from the physical label marginal; the quotient equivalences and the
invariance of every table-native reconstruction follow from that derived
equality. -/
theorem renewal_semantic_stripping_exact
    {Alphabet Label State : Type*}
    [Fintype Label] [Fintype State] [DecidableEq State]
    (T' : Alphabet × Label → Matrix State State ℝ)
    (T : Alphabet → Matrix State State ℝ)
    (hmarg : ∀ a : Alphabet, ∑ l : Label, T' (a, l) = T a)
    (α : State → ℝ) :
    let loaded := labelMarginalHankelTable T' α
    let native := renewalHankelTable T α
    loaded = native
      ∧ Nonempty
        (MinRec (renewalFutureSignature loaded) ≃
          MinRec (renewalFutureSignature native))
      ∧ Nonempty (HankelResponseSpace loaded ≃ₗ[ℂ]
          HankelResponseSpace native)
      ∧ (∀ (Output : Type*)
          (reconstruct :
            (RenewalWord Alphabet → RenewalWord Alphabet → ℂ) → Output),
          reconstruct loaded = reconstruct native) := by
  dsimp only
  have htable :=
    labelMarginalHankelTable_eq_renewalHankelTable T' T hmarg α
  refine ⟨htable, ?_, ?_, ?_⟩
  · rw [htable]
    exact ⟨Equiv.refl _⟩
  · rw [htable]
    exact ⟨LinearEquiv.refl ℂ _⟩
  · intro Output reconstruct
    rw [htable]

end NCG
