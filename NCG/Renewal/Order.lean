/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.PredictiveQuotient

/-!
# The predictive divisibility order

This file formalizes the order-theoretic layer of the positive sector
(manuscript, §"Predictive order and renewal resolvent"):

* the **predictive divisibility preorder** on a channel monoid `ℳ`
  (Definition `def:predictive-order`): `a ≼ b` iff `b = a * ψ` for some
  `ψ ∈ ℳ` — i.e. `b` is reachable from `a` by further renewal evolution
  (recall multiplication is diagrammatic, so `a * ψ` is "`a`, then `ψ`");
  this is exactly right-divisibility `a ∣ b`;
* the **predictive poset** `𝔓 = ℳ/≈` (Lemma `lem:poset`): quotienting the
  preorder by mutual divisibility yields a partial order.  In Lean this is
  Mathlib's `Antisymmetrization`, so Lemma `lem:poset` is provided by the
  `PartialOrder` instance on `Antisymmetrization`.

The causal-set reading of this order (Proposition `prop:causal-skeleton`)
and the chain-counting renewal resolvent (Proposition `prop:incidence-zeta`)
are developed in `NCG/Renewal/CausalSkeleton.lean` and
`NCG/Renewal/IncidenceZeta.lean`.
-/

namespace NCG

variable {M : Type*}

/-- Type synonym equipping a monoid with its **predictive divisibility
preorder** (Definition `def:predictive-order`): `a ≤ b` iff `a ∣ b`, i.e.
`b = a * ψ` for some channel `ψ`. -/
def DivisibilityOrder (M : Type*) := M

namespace DivisibilityOrder

/-- Interpret a monoid element in the divisibility order. -/
def toDiv : M ≃ DivisibilityOrder M := Equiv.refl M

/-- Recover the monoid element underlying a point of the divisibility
order. -/
def ofDiv : DivisibilityOrder M ≃ M := Equiv.refl M

@[simp]
theorem toDiv_ofDiv (a : DivisibilityOrder M) : toDiv (ofDiv a) = a := rfl

@[simp]
theorem ofDiv_toDiv (a : M) : ofDiv (toDiv a) = a := rfl

/-- The predictive divisibility preorder: `a ≼ b` iff `b` is obtained from
`a` by further renewal evolution. -/
instance instPreorder [Monoid M] : Preorder (DivisibilityOrder M) where
  le a b := ofDiv a ∣ ofDiv b
  le_refl a := dvd_refl _
  le_trans a b c hab hbc := dvd_trans hab hbc

theorem le_iff_dvd [Monoid M] (a b : DivisibilityOrder M) :
    a ≤ b ↔ ofDiv a ∣ ofDiv b :=
  Iff.rfl

theorem le_iff_exists [Monoid M] (a b : DivisibilityOrder M) :
    a ≤ b ↔ ∃ ψ : M, ofDiv b = ofDiv a * ψ :=
  Iff.rfl

end DivisibilityOrder

/-- The **predictive poset** `𝔓 = ℳ/≈` (Definition `def:predictive-order`):
the divisibility preorder modulo mutual divisibility.  Mathlib's
`Antisymmetrization` provides the `PartialOrder` instance, which is exactly
the content of Lemma `lem:poset` (quotienting a preorder by its symmetric
part yields a partial order). -/
abbrev PredictivePoset (M : Type*) [Monoid M] :=
  Antisymmetrization (DivisibilityOrder M) (· ≤ ·)

/-- **Lemma `lem:poset`** (poset reflection): the predictive poset is a
partial order.  This is definitionally Mathlib's partial-order instance on
the antisymmetrization of a preorder. -/
example (M : Type*) [Monoid M] : PartialOrder (PredictivePoset M) :=
  inferInstance

end NCG
