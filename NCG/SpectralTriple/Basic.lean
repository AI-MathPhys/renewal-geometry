/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spectral triples

The central notion of Connes' noncommutative geometry: a **spectral triple**
`(𝒜, ℋ, D)` consists of a `*`-algebra `𝒜` represented on a Hilbert space
`ℋ`, together with an (unbounded) self-adjoint operator `D` — the **Dirac
operator** — such that

1. `D` has compact resolvent (the noncommutative counterpart of compactness
   of the underlying space), and
2. the commutators `[D, π(a)]` are bounded for `a` in a dense subalgebra
   (the Lipschitz condition: observables have metrically controlled
   variation).

For a compact Riemannian spin manifold `X`, the model example is
`(C^∞(X), L²(X, S), D_X)` with `D_X` the classical Dirac operator; the
metric is recovered from the spectral data (Connes' distance formula).

The unbounded operator `D` is a Mathlib `LinearPMap` (a partially defined
linear map).  Self-adjointness is expressed through symmetry plus the
resolvent data; the compact-resolvent condition is expressed by exhibiting a
two-sided compact inverse of `D - i`.

This file provides the *definitions*; the manuscript's positive predictive
triple (Theorem `thm:triple`) is the target instance, whose algebraic core
is developed in `NCG.Operator.Diagonal` and whose analytic realization on
`ℓ²(𝒲_CP)` is a roadmap item.

## Main definitions

* `NCG.CommutatorBounded` — the Lipschitz condition for a bounded operator
  against an unbounded one;
* `NCG.SpectralTriple` — spectral triples over a fixed algebra and Hilbert
  space.
-/

namespace NCG

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The **Lipschitz condition** of noncommutative geometry: the bounded
operator `T` preserves the domain of the (partially defined) operator `D`,
and the commutator `[D, T]` is bounded on that domain.  In a spectral triple
this is required of every represented algebra element. -/
def CommutatorBounded (D : H →ₗ.[ℂ] H) (T : H →L[ℂ] H) : Prop :=
  ∃ hpres : ∀ x, x ∈ D.domain → T x ∈ D.domain, ∃ C : ℝ,
    ∀ x : D.domain, ‖D ⟨T x, hpres x x.2⟩ - T (D x)‖ ≤ C * ‖(x : H)‖

/-- A **spectral triple** `(𝒜, ℋ, D)` over the algebra `A` and Hilbert
space `H`:

* `rep` — a `*`-representation of `A` by bounded operators on `H`;
* `dirac` — a densely defined symmetric operator `D`;
* `compact_resolvent` — a two-sided compact inverse `R = (D - i)⁻¹`,
  encoding self-adjointness (surjectivity of `D - i`) together with
  compactness of the resolvent;
* `lipschitz` — bounded commutators `[D, π(a)]` for all `a` in the
  distinguished dense subalgebra `smoothAlgebra`.

The abstract axioms follow Connes; the manuscript's positive predictive
triple (`Theorem thm:triple`) and signed modular triple
(`Theorem thm:signed-dirac`, in Krein form) are the intended instances. -/
structure SpectralTriple (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The representation of the coordinate algebra by bounded operators. -/
  rep : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  /-- The Dirac operator, an unbounded densely defined operator. -/
  dirac : H →ₗ.[ℂ] H
  /-- The domain of the Dirac operator is dense. -/
  dense_domain : Dense (dirac.domain : Set H)
  /-- The Dirac operator is symmetric on its domain. -/
  symmetric : ∀ x y : dirac.domain,
    ⟪dirac x, (y : H)⟫ = ⟪(x : H), dirac y⟫
  /-- Compact resolvent: a compact two-sided inverse of `D - i`.  This
  simultaneously encodes self-adjointness (both deficiency conditions) and
  the compactness axiom of a spectral triple. -/
  compact_resolvent :
    ∃ (R : H →L[ℂ] H) (hmem : ∀ y : H, R y ∈ dirac.domain),
      IsCompactOperator (R : H → H) ∧
      (∀ y : H, dirac ⟨R y, hmem y⟩ - Complex.I • R y = y) ∧
      (∀ x : dirac.domain, R (dirac x - Complex.I • (x : H)) = x)
  /-- The distinguished dense subalgebra of "smooth" elements. -/
  smoothAlgebra : StarSubalgebra ℂ A
  /-- The Lipschitz condition: bounded commutators with the Dirac operator
  for all smooth algebra elements. -/
  lipschitz : ∀ a ∈ smoothAlgebra, CommutatorBounded dirac (rep a)

namespace SpectralTriple

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : SpectralTriple A H)

/-- The resolvent of the Dirac operator at `i`, packaged from the
`compact_resolvent` field. -/
noncomputable def resolvent : H →L[ℂ] H :=
  S.compact_resolvent.choose

theorem resolvent_mem_domain (y : H) : S.resolvent y ∈ S.dirac.domain :=
  S.compact_resolvent.choose_spec.choose y

theorem resolvent_isCompact : IsCompactOperator (S.resolvent : H → H) :=
  S.compact_resolvent.choose_spec.choose_spec.1

theorem resolvent_right_inverse (y : H) :
    S.dirac ⟨S.resolvent y, S.resolvent_mem_domain y⟩
      - Complex.I • S.resolvent y = y :=
  S.compact_resolvent.choose_spec.choose_spec.2.1 y

theorem resolvent_left_inverse (x : S.dirac.domain) :
    S.resolvent (S.dirac x - Complex.I • (x : H)) = x :=
  S.compact_resolvent.choose_spec.choose_spec.2.2 x

end SpectralTriple

end NCG
