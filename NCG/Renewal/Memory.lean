/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CPMap

/-!
# Renewal memories

This file defines the primitive object of renewal spectral geometry
(manuscript, Definition `def:renewal-memory`): a **renewal memory** over a
reset alphabet `E`, i.e. a family of channels `Φ_σ` indexed by `σ : E`.

At this layer the channels take values in an arbitrary monoid `M`; the
completely positive realization is obtained by instantiating
`M := NCG.UCPMap A` (see `NCG.CPRenewalMemory`).  All of the predictive
quotient theory (`NCG.Renewal.PredictiveQuotient`) only uses the monoid
structure, exactly as in the manuscript where the predictive quotient is a
quotient of the free monoid of histories by a channel-kernel congruence.

## Conventions

Multiplication in the channel monoid `M` is **diagrammatic**: `a * b` means
"first `a`, then `b`".  A history `w = σ₁ ⋯ σ_k` (with `σ₁` acting first) is
an element of the free monoid `FreeMonoid E`, and its accumulated channel is
`Φ_{σ₁} * ⋯ * Φ_{σ_k}` — in composition order this is
`Φ_{σ_k} ∘ ⋯ ∘ Φ_{σ₁}`, matching the manuscript's
`Φ_w = Φ_{σ_k} ∘ ⋯ ∘ Φ_{σ₁}` and `Φ_{σ w} = Φ_w ∘ Φ_σ`.

## Main definitions

* `NCG.RenewalMemory E M` — a renewal memory with channels in `M`;
* `NCG.RenewalMemory.History` — histories as elements of `FreeMonoid E`;
* `NCG.RenewalMemory.acc` — the accumulated-channel monoid homomorphism
  `FreeMonoid E →* M`;
* `NCG.CPRenewalMemory E A` — the completely positive realization.
-/

namespace NCG

/-- A **renewal memory** over the reset alphabet `E`, with channels valued in
the monoid `M` (Definition `def:renewal-memory`; the manuscript's finite CP
case is `M := UCPMap A` with `E` finite and `A` finite-dimensional). -/
structure RenewalMemory (E : Type*) (M : Type*) [Monoid M] where
  /-- The channel attached to each reset symbol. -/
  channel : E → M

/-- A finite **completely positive** renewal memory on the internal algebra
`A`: the manuscript's Definition `def:renewal-memory` proper. -/
abbrev CPRenewalMemory (E : Type*) (A : Type*) [Ring A] [PartialOrder A]
    [StarRing A] [StarOrderedRing A] [Algebra ℂ A] :=
  RenewalMemory E (UCPMap A)

namespace RenewalMemory

/-- A **history** is a word in the reset alphabet, i.e. an element of the
free monoid on `E`.  The empty history is `1` and concatenation is `*`. -/
abbrev History (E : Type*) := FreeMonoid E

variable {E : Type*} {M : Type*} [Monoid M] (R : RenewalMemory E M)

/-- The **accumulated channel** of a history (Definition
`def:renewal-memory`): the unique monoid homomorphism `FreeMonoid E →* M`
sending the one-letter history `σ` to `Φ_σ`. -/
def acc : History E →* M := FreeMonoid.lift R.channel

@[simp]
theorem acc_of (σ : E) : R.acc (FreeMonoid.of σ) = R.channel σ := by
  simp [acc]

@[simp]
theorem acc_one : R.acc 1 = 1 := map_one _

theorem acc_mul (w w' : History E) : R.acc (w * w') = R.acc w * R.acc w' :=
  map_mul _ _ _

/-- Prepending a reset symbol multiplies the accumulated channel on the left
(diagrammatic order); in composition order this is the manuscript's
`Φ_{σw} = Φ_w ∘ Φ_σ`. -/
theorem acc_of_mul (σ : E) (w : History E) :
    R.acc (FreeMonoid.of σ * w) = R.channel σ * R.acc w := by
  simp [acc_mul]

end RenewalMemory

end NCG
