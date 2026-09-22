/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The realized reversible sign subgroup

**Definition `def:realized-reversible-subgroup`** (encoding): a class
`α ∈ H¹(G, ℤ/2)` is *realized reversibly* when it is represented by a
predictive unit preserving the recurrent algebra with a
clock-preserving signed lift.  The datum is encoded as a predicate on
the cohomology module together with its dynamical closure properties
(`NCG.RealizedReversibleData`): the identity channel realizes `0`,
composition realizes sums, and inversion realizes negatives.

**Lemma `lem:realized-reversible-subgroup`**: the realized classes
form a subgroup `K_rev ≤ H` — proved by packaging the closure
properties into an `AddSubgroup`
(`NCG.RealizedReversibleData.toAddSubgroup`).
-/

namespace NCG

/-- **Definition `def:realized-reversible-subgroup`** (encoding): the
realized-reversible datum on the sign-cohomology module `H`: a
realization predicate together with the dynamical closure properties
(identity channel, composition of predictive units, inversion). -/
structure RealizedReversibleData (H : Type*) [AddCommGroup H] where
  /-- `realized α` — `α` is represented by a predictive unit with a
  clock-preserving signed lift whose sheet action is the geometric
  sheet shift of `α`. -/
  realized : H → Prop
  /-- The identity channel realizes the zero class. -/
  zero_realized : realized 0
  /-- Composing realizing revisions realizes the sum of classes. -/
  add_realized : ∀ {a b : H}, realized a → realized b → realized (a + b)
  /-- The inverse predictive unit realizes the negative class. -/
  neg_realized : ∀ {a : H}, realized a → realized (-a)

/-- **Lemma `lem:realized-reversible-subgroup`**: the realized
reversible classes form a subgroup `K_rev ≤ H = H¹(G, ℤ/2)`. -/
def RealizedReversibleData.toAddSubgroup {H : Type*} [AddCommGroup H]
    (K : RealizedReversibleData H) : AddSubgroup H where
  carrier := {a | K.realized a}
  zero_mem' := K.zero_realized
  add_mem' := K.add_realized
  neg_mem' := K.neg_realized

theorem RealizedReversibleData.mem_toAddSubgroup {H : Type*}
    [AddCommGroup H] (K : RealizedReversibleData H) (a : H) :
    a ∈ K.toAddSubgroup ↔ K.realized a := Iff.rfl

end NCG
