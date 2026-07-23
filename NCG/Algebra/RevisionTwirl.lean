/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.RevisionCocycle

/-!
# The internal revision twirl

**Theorem `thm:revision-twirl-main`** (invariance core): the twirl
`X ↦ Σ_α R_α X R_α⁻¹` over a projective revision family is
**Ad-invariant**: conjugating by any implementer permutes the terms —
the `{±1}` multiplier cancels inside `Ad` — so the twirl lands in the
fixed algebra of the revision action
(`NCG.twirl_ad_invariant`).  The commutant-scalar identification
(Schur's lemma for the irreducible primitive representation, giving
`twirl X = (Tr X/2^m)·1`) is the noted analytic step. -/

namespace NCG

variable {A : Type*} [Ring A] {L : Type*} [AddCommGroup L] [Fintype L]

/-- The **internal revision twirl** `X ↦ Σ_α R_α X R_α⁻¹`
(Theorem `thm:revision-twirl-main`). -/
noncomputable def twirl (F : RevisionFamily Aˣ L) (X : A) : A :=
  ∑ α : L, (F.R α : A) * X * ((F.R α)⁻¹ : Aˣ)

/-- Conjugation composes through unit products. -/
theorem conj_conj (u v : Aˣ) (Y : A) :
    (u : A) * ((v : A) * Y * ((v⁻¹ : Aˣ) : A)) * ((u⁻¹ : Aˣ) : A)
      = ((u * v : Aˣ) : A) * Y * (((u * v)⁻¹ : Aˣ) : A) := by
  simp only [Units.val_mul, mul_inv_rev, mul_assoc]

/-- A unit whose coercion commutes with everything conjugates
trivially. -/
theorem central_unit_conj (c : Aˣ)
    (hc : ∀ x : A, (c : A) * x = x * (c : A)) (Y : A) :
    (c : A) * Y * ((c⁻¹ : Aˣ) : A) = Y := by
  rw [hc Y, mul_assoc, Units.mul_inv, mul_one]

/-- **Theorem `thm:revision-twirl-main`** (Ad-invariance): the twirl is
invariant under conjugation by every implementer — the projective sign
cancels inside `Ad`, and left addition permutes the label group.  With
Schur's lemma on the irreducible primitive block this forces
`twirl X = (Tr X/2^m)·1`; the invariance proved here is the algebraic
half. -/
theorem twirl_ad_invariant (F : RevisionFamily Aˣ L)
    (hε : ∀ x : A, (F.ε : A) * x = x * (F.ε : A)) (X : A) (β : L) :
    (F.R β : A) * twirl F X * ((F.R β)⁻¹ : Aˣ) = twirl F X := by
  have hεpow : ∀ (s : ZMod 2) (x : A),
      ((sgnPow F.ε s : Aˣ) : A) * x = x * ((sgnPow F.ε s : Aˣ) : A) := by
    intro s x
    have hcases : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rcases hcases s with rfl | rfl
    · simp [sgnPow, ZMod.val_zero]
    · simpa [sgnPow, ZMod.val_one, Units.val_pow_eq_pow_val, pow_one]
        using hε x
  unfold twirl
  rw [Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ α : L,
      (F.R β : A) * ((F.R α : A) * X * ((F.R α)⁻¹ : Aˣ))
        * ((F.R β)⁻¹ : Aˣ)
      = (F.R (β + α) : A) * X * ((F.R (β + α))⁻¹ : Aˣ) := by
    intro α
    rw [conj_conj, F.hmul β α, ← conj_conj]
    exact central_unit_conj _ (hεpow _) _
  calc ∑ α : L, (F.R β : A)
        * ((F.R α : A) * X * ((F.R α)⁻¹ : Aˣ)) * ((F.R β)⁻¹ : Aˣ)
      = ∑ α : L, (F.R (β + α) : A) * X * ((F.R (β + α))⁻¹ : Aˣ) :=
        Finset.sum_congr rfl fun α _ => hterm α
    _ = ∑ γ : L, (F.R γ : A) * X * ((F.R γ)⁻¹ : Aˣ) :=
        Fintype.sum_equiv (Equiv.addLeft β) _ _ fun α => rfl

end NCG
