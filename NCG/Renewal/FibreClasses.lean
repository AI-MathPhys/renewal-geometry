/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.PredictiveQuotient

/-!
# The regular finite-fibre classes (A)–(D)

The finite-fibre assumption `ass:fibres` holds automatically in the
regular classes of the manuscript:

* **Proposition `prop:fibres-automata`** (graded finite-type automata):
  prepending a reset raises the quotient length by at most one —
  `Λ([σw]) ≤ Λ([w]) + 1` unconditionally
  (`NCG.RenewalMemory.quotLength_shift_le`); with the graded-automaton
  hypothesis the increment is exactly one and fibres are the
  `σ`-predecessor sets, bounded by the backward branching.

* **Proposition `prop:fibres-cp`** (commuting CP channels): a
  cancellative commutative channel monoid has *singleton* shift fibres
  (`NCG.RenewalMemory.shift_injective_of_cancel` — the finite
  presentation ⟹ finite generation reduction is not formalised).

* **Proposition `prop:fibres-quotient`** (bounded rank distortion): a
  quotient with `|Λ'∘π − Λ| ≤ D` turns increments `≤ C` into increments
  `≤ C + 2D` (`NCG.rank_distortion_increment`); the fibre-count
  composition bound is the product bound noted in the manuscript. -/

namespace NCG.RenewalMemory

variable {E M : Type*} [Monoid M] (R : RenewalMemory E M)

/-- **Proposition `prop:fibres-automata`, increment bound**: prepending
one reset raises the quotient length by at most one,
`Λ_min([σw]) ≤ Λ_min([w]) + 1` — the upper half of the elementary-cover
property, with no hypotheses at all. -/
theorem quotLength_shift_le (σ : E) (x : R.PredictiveQuotient) :
    R.quotLength (R.shift σ x) ≤ R.quotLength x + 1 := by
  obtain ⟨w, rfl, hlen⟩ := R.exists_quotLength_rep x
  rw [shift_mkQ]
  have h := R.quotLength_mkQ_le (FreeMonoid.of σ * w)
  rw [FreeMonoid.length_mul, FreeMonoid.length_of] at h
  omega

/-- **Proposition `prop:fibres-cp`** (commuting CP channels with
cancellative channel monoid): the descended shifts have singleton
fibres — a commutative cancellative monoid is left-cancellative, so
`NCG.RenewalMemory.shift_injective` applies. -/
theorem shift_injective_of_cancel {M' : Type*} [CommMonoid M']
    [IsCancelMul M'] (R' : RenewalMemory E M') (σ : E) :
    Function.Injective (R'.shift σ) :=
  R'.shift_injective σ

end NCG.RenewalMemory

namespace NCG

/-- **Proposition `prop:fibres-quotient`, increment bound** (bounded
rank distortion): if the quotient rank differs from the original by at
most `D` and the original increment is at most `C`, the quotient
increment is at most `C + 2D`. -/
theorem rank_distortion_increment {a b a' b' C D : ℤ}
    (hab : |a - b| ≤ C) (ha : |a' - a| ≤ D) (hb : |b' - b| ≤ D) :
    |a' - b'| ≤ C + 2 * D := by
  rw [abs_le] at *
  constructor <;> linarith

end NCG
