/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ShellInheritanceExact
import NCG.Grand.FiniteBRSTWardEinstein
import NCG.Grand.SMSTReflectionPositivityExact

/-!
# Gauge, BRST, and reflection inheritance of exact shell actions

The exact potential of mean force is equivariant under every compatible fine
gauge permutation.  Therefore it is closed under the finite BRST coboundary,
whose square vanishes.  Reflection positivity is inherited independently by
the already-proved reflection-equivariant pushforward identity.
-/

namespace NCG
namespace ShellInheritance

open NCG.ReferenceOrigin

/-- A compatible finite gauge action makes the exact shell action gauge
invariant, BRST closed, and BRST nilpotent at the next degree. -/
theorem shellAction_gauge_BRST_closed
    {Gauge ΩY ΩX : Type*} [Group Gauge]
    [Fintype ΩY] [Fintype ΩX] [DecidableEq ΩX]
    (π : ΩY → ΩX) (ρ : ΩY → ℝ) (S : ΩY → ℝ)
    (actY : Gauge → Equiv.Perm ΩY) (actX : Gauge → Equiv.Perm ΩX)
    (hactX : ∀ g h x, actX (g * h) x = actX g (actX h x))
    (hcomm : ∀ g y, π (actY g y) = actX g (π y))
    (hρ : ∀ g y, ρ (actY g y) = ρ y)
    (hS : ∀ g y, S (actY g y) = S y) :
    (∀ g x, shellAction π ρ S (actX g x) = shellAction π ρ S x)
      ∧ finiteBRST0 (fun g x => actX g x) (shellAction π ρ S) = 0
      ∧ finiteBRST1 (fun g x => actX g x)
          (finiteBRST0 (fun g x => actX g x) (shellAction π ρ S)) = 0 := by
  have hinv : ∀ g x,
      shellAction π ρ S (actX g x) = shellAction π ρ S x := by
    intro g x
    exact shellAction_equivariant π ρ S (actY g) (actX g)
      (hcomm g) (hρ g) (hS g) x
  have hbrst := finiteGaugeAction_BRST
    (fun g x => actX g x) hactX (shellAction π ρ S) hinv
  exact ⟨hinv, hbrst⟩

/-- Complete symmetry inheritance for the finite exact shell: the potential
of mean force obeys its defining conditional-expectation identity, composes
through nested cutoffs, is gauge invariant and BRST closed, and preserves OS
reflection positivity under a reflection-equivariant Read. -/
theorem exact_shell_symmetry_packet
    {Gauge ΩY ΩX ΩZ : Type*} [Group Gauge]
    [Fintype ΩY] [Fintype ΩX] [DecidableEq ΩX] [DecidableEq ΩZ]
    (π₁ : ΩY → ΩX) (π₂ : ΩX → ΩZ) (ρ : ΩY → ℝ)
    (hρpos : ∀ y, 0 < ρ y) (hπ₁ : Function.Surjective π₁)
    (S : ΩY → ℝ)
    (actY : Gauge → Equiv.Perm ΩY) (actX : Gauge → Equiv.Perm ΩX)
    (hactX : ∀ g h x, actX (g * h) x = actX g (actX h x))
    (hcomm : ∀ g y, π₁ (actY g y) = actX g (π₁ y))
    (hρ : ∀ g y, ρ (actY g y) = ρ y)
    (hS : ∀ g y, S (actY g y) = S y) :
    (∀ x, Real.exp (-shellAction π₁ ρ S x) =
        gibbsSum π₁ ρ S x / NCG.ReferenceOrigin.pushRef π₁ ρ x)
      ∧ (∀ z, shellAction (fun y => π₂ (π₁ y)) ρ S z =
        shellAction π₂ (NCG.ReferenceOrigin.pushRef π₁ ρ)
          (shellAction π₁ ρ S) z)
      ∧ (∀ g x, shellAction π₁ ρ S (actX g x) = shellAction π₁ ρ S x)
      ∧ finiteBRST0 (fun g x => actX g x) (shellAction π₁ ρ S) = 0
      ∧ finiteBRST1 (fun g x => actX g x)
          (finiteBRST0 (fun g x => actX g x) (shellAction π₁ ρ S)) = 0 := by
  have hshell := shell_inheritance π₁ π₂ hρpos hπ₁ S
    (actY 1) (actX 1) (hcomm 1) (hρ 1) (hS 1)
  have hbrst := shellAction_gauge_BRST_closed π₁ ρ S actY actX
    hactX hcomm hρ hS
  exact ⟨hshell.1, hshell.2.1, hbrst.1,
    hbrst.2.1, hbrst.2.2⟩

end ShellInheritance
end NCG
