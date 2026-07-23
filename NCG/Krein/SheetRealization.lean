/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Realized reversible sheet classes form a subgroup

Covers `lem:realized-reversible-subgroup` from `manuscripts/lorentzian_emergence/lorentzian_emergence.tex`:
in the signed-cover model a class `α ∈ H` is *realized reversibly*
when some predictive unit — an invertible transformation of the cover
belonging to the given group `S` of units preserving the recurrent
algebra and the clock — acts as a lift over a base automorphism whose
sheet action is the geometric sheet shift by `α`.

The lemma's dynamical content is **derived**, not assumed: the
identity unit realizes `0` (`isLiftOver_refl`), the composite of two
units realizes the *sum* of their classes because sheet shifts add
under composition (`isLiftOver_comp`), and the inverse unit realizes
the negative (`isLiftOver_inv`).  Hence the realized classes form an
additive subgroup `K_rev ≤ H` (`realizedSubgroup`).
-/

namespace NCG

variable {V : Type*} {H : Type*} [AddCommGroup H]

/-- A cover transformation `f` is a **lift over** the base
automorphism `b` with **sheet action** `α` when
`f (v, η) = (b v, η + α)` — a clock-compatible signed lift whose
sheet component is the geometric sheet shift by `α`. -/
def IsLiftOver (f : Equiv.Perm (V × H)) (b : Equiv.Perm V)
    (α : H) : Prop :=
  ∀ v η, f (v, η) = (b v, η + α)

/-- The identity unit is a lift over the identity with sheet action
`0`. -/
theorem isLiftOver_refl :
    IsLiftOver (1 : Equiv.Perm (V × H)) (1 : Equiv.Perm V) 0 := by
  intro v η
  simp

/-- **Sheet actions add under composition**: composing units composes
the base automorphisms and adds the sheet shifts. -/
theorem isLiftOver_comp {f g : Equiv.Perm (V × H)}
    {b c : Equiv.Perm V} {α β : H}
    (hf : IsLiftOver f b α) (hg : IsLiftOver g c β) :
    IsLiftOver (f * g) (b * c) (β + α) := by
  intro v η
  show f (g (v, η)) = _
  rw [hg v η, hf (c v) (η + β)]
  show (b (c v), η + β + α) = (b (c v), η + (β + α))
  rw [add_assoc]

/-- **Sheet actions negate under inversion**: the inverse unit is a
lift over the inverse base with sheet action `−α`. -/
theorem isLiftOver_inv {f : Equiv.Perm (V × H)} {b : Equiv.Perm V}
    {α : H} (hf : IsLiftOver f b α) :
    IsLiftOver f⁻¹ b⁻¹ (-α) := by
  intro v η
  apply f.injective
  show f (f⁻¹ (v, η)) = f (b⁻¹ v, η + -α)
  rw [show f⁻¹ = f.symm from rfl, Equiv.apply_symm_apply,
    hf (b⁻¹ v) (η + -α)]
  show (v, η) = (b (b⁻¹ v), η + -α + α)
  rw [show b⁻¹ = b.symm from rfl, Equiv.apply_symm_apply,
    add_assoc, neg_add_cancel, add_zero]

/-- **Definition `def:realized-reversible-subgroup`**: the classes
realized reversibly by units of the given group `S` (the predictive
units preserving the recurrent algebra and the clock). -/
def realizedClasses (S : Subgroup (Equiv.Perm (V × H))) : Set H :=
  {α | ∃ f ∈ S, ∃ b : Equiv.Perm V, IsLiftOver f b α}

/-- **Lemma `lem:realized-reversible-subgroup`**: `K_rev ≤ H` — the
realized reversible classes form an additive subgroup.  The closure
facts are the derived dynamical statements: the identity realizes
`0`, composites realize sums (sheet shifts add), inverses realize
negatives. -/
def realizedSubgroup (S : Subgroup (Equiv.Perm (V × H))) :
    AddSubgroup H where
  carrier := realizedClasses S
  zero_mem' := ⟨1, S.one_mem, 1, isLiftOver_refl⟩
  add_mem' := by
    rintro α β ⟨f, hfS, b, hf⟩ ⟨g, hgS, c, hg⟩
    exact ⟨g * f, S.mul_mem hgS hfS, c * b,
      by simpa [add_comm] using isLiftOver_comp hg hf⟩
  neg_mem' := by
    rintro α ⟨f, hfS, b, hf⟩
    exact ⟨f⁻¹, S.inv_mem hfS, b⁻¹, isLiftOver_inv hf⟩

theorem mem_realizedSubgroup {S : Subgroup (Equiv.Perm (V × H))}
    {α : H} :
    α ∈ realizedSubgroup (V := V) S ↔
      ∃ f ∈ S, ∃ b : Equiv.Perm V, IsLiftOver f b α := Iff.rfl

end NCG
