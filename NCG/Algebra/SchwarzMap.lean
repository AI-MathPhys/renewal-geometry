/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.Memory

/-!
# Schwarz maps and the predictive-unit theorem

The updated manuscript's **predictive-unit theorem** (`thm:predictive-unit`)
states that a unital completely positive map on a finite-dimensional
C⋆-algebra with a UCP inverse is a `*`-automorphism; consequently the unit
group `𝖴_pred` of the predictive channel monoid
(Definition `def:predictive-channel-monoid`) consists of `*`-automorphisms
of the internal algebra.  This is what later converts reversible signed
revisions into automorphisms and feeds the *automatic projective lift*
(`thm:spatial-multiplier-scalar-main`, see `NCG.Algebra.ProjectiveDefect`).

This file formalizes the order-theoretic heart of that proof:

* `NCG.IsSchwarzMap` — the Kadison–Schwarz inequality
  `φ(x)⋆ φ(x) ≤ φ(x⋆ x)`;
* `NCG.IsPositiveMap.mono` — positive linear maps are monotone;
* `NCG.schwarz_sandwich_eq` — the **sandwich equality**: if `Θ` is a
  positive Schwarz left inverse of the Schwarz map `Ψ`, then
  `Θ(Ψ(x)⋆ Ψ(x)) = x⋆ x` — the two Kadison–Schwarz estimates collapse to
  equality (the displayed chain in the manuscript's proof of
  `thm:predictive-unit`);
* `NCG.UCPMap.unit` API — units of the channel monoid `UCPMap A` are pairs
  of mutually inverse UCP maps, so the sandwich equality applies to every
  predictive unit.

The remaining steps of `thm:predictive-unit` — that complete positivity
implies the Schwarz inequality (Kadison–Schwarz, via 2-positivity), and that
equality in the Schwarz inequality places `x` in the multiplicative domain
(Choi) — are proved in `NCG/Algebra/KadisonSchwarz.lean`.
-/

namespace NCG

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [Algebra ℂ A]

/-- A linear map satisfies the **Schwarz inequality** (Kadison–Schwarz) when
`φ(x)⋆ φ(x) ≤ φ(x⋆ x)` for every `x`.  Unital completely positive maps on
C⋆-algebras satisfy this (via 2-positivity); here it is taken as the defining
estimate. -/
def IsSchwarzMap (φ : A →ₗ[ℂ] A) : Prop :=
  ∀ x : A, star (φ x) * φ x ≤ φ (star x * x)

/-- Positive linear maps are monotone. -/
theorem IsPositiveMap.mono {φ : A →ₗ[ℂ] A} (hφ : IsPositiveMap φ) {a b : A}
    (h : a ≤ b) : φ a ≤ φ b := by
  have h0 : 0 ≤ b - a := sub_nonneg.mpr h
  have h1 : 0 ≤ φ (b - a) := hφ _ h0
  rw [map_sub] at h1
  exact sub_nonneg.mp h1

/-- **The sandwich equality** (core of the predictive-unit theorem
`thm:predictive-unit`): if `Θ` is a positive Schwarz left inverse of the
Schwarz map `Ψ`, then

`Θ(Ψ(x)⋆ Ψ(x)) = x⋆ x`.

One Kadison–Schwarz estimate applied through the monotone inverse gives `≤`,
the other gives `≥`.  In the manuscript this equality (together with its
`x x⋆` twin) places every `x` in the multiplicative domain of `Ψ`, making a
UCP-invertible UCP map a `*`-automorphism. -/
theorem schwarz_sandwich_eq {Ψ Θ : A →ₗ[ℂ] A} (hΨ : IsSchwarzMap Ψ)
    (hΘ : IsSchwarzMap Θ) (hΘpos : IsPositiveMap Θ)
    (hinv : ∀ x, Θ (Ψ x) = x) (x : A) :
    Θ (star (Ψ x) * Ψ x) = star x * x := by
  apply le_antisymm
  · -- apply the monotone `Θ` to Kadison–Schwarz for `Ψ`
    have h1 : star (Ψ x) * Ψ x ≤ Ψ (star x * x) := hΨ x
    have h2 := hΘpos.mono h1
    rwa [hinv] at h2
  · -- Kadison–Schwarz for `Θ` at the point `Ψ x`
    have h3 : star (Θ (Ψ x)) * Θ (Ψ x) ≤ Θ (star (Ψ x) * Ψ x) := hΘ (Ψ x)
    rwa [hinv] at h3

namespace UCPMap

/-- Applying a unit of the channel monoid and then its inverse returns the
input: with diagrammatic multiplication, `u.val * u.inv = 1` evaluates to
`u.inv (u.val a) = a`. -/
theorem inv_val_apply (u : (UCPMap A)ˣ) (a : A) :
    (u.inv : UCPMap A) ((u.val : UCPMap A) a) = a := by
  rw [← mul_apply u.val u.inv a, u.val_inv, one_apply]

/-- Applying the inverse of a unit and then the unit returns the input. -/
theorem val_inv_apply (u : (UCPMap A)ˣ) (a : A) :
    (u.val : UCPMap A) ((u.inv : UCPMap A) a) = a := by
  rw [← mul_apply u.inv u.val a, u.inv_val, one_apply]

/-- **The sandwich equality for predictive units** (`thm:predictive-unit`
via Definition `def:predictive-channel-monoid`): if both components of a
unit `u` of the channel monoid `UCPMap A` satisfy the Schwarz inequality,
then

`u⁻¹(u(x)⋆ u(x)) = x⋆ x`.

Together with the multiplicative-domain step
(`NCG/Algebra/KadisonSchwarz.lean`) this makes every
predictive unit a `*`-automorphism: `𝖴_pred ⊆ Aut(𝒜_int)`. -/
theorem unit_sandwich_eq (u : (UCPMap A)ˣ)
    (hval : IsSchwarzMap (u.val : UCPMap A).toLinearMap)
    (hinv : IsSchwarzMap (u.inv : UCPMap A).toLinearMap) (x : A) :
    (u.inv : UCPMap A)
        (star ((u.val : UCPMap A) x) * (u.val : UCPMap A) x)
      = star x * x :=
  schwarz_sandwich_eq hval hinv (u.inv : UCPMap A).isPositiveMap
    (inv_val_apply u) x

end UCPMap

end NCG
