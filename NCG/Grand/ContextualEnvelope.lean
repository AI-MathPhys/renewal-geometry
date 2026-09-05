/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The universal contextual history envelope
  (`thm:contextual-envelope-universal`, Gran-Tensor manuscript)

* `contextualNull`: the contextual future-null space
  `𝒩 = {q | R_i(u·q·v) = 0 for all contexts}`.
* `contextual_null_absorption`: `𝒩` is a two-sided ideal (zero,
  add, neg, and both one-sided multiplicative absorptions) — the
  abstract-ring form of `lem:contextual-null-ideal` (whose
  matrix form is `NCG.contextual_null_ideal` in
  `GrandNullIdeal.lean`).
* `contextual_envelope_universal`: if every contextual Read
  factors through a quotient `π : A ↠ B`, then `Ker π ⊆ 𝒩`;
  every map killing `𝒩` factors through `π` (the canonical
  surjection `B ↠ A/𝒩`); and when `B` is contextually future
  separated the factoring map is injective (the `*`-isomorphism
  clause).

Rendering disclosed: contexts are rendered as an additive family
of scalar Reads with two-sided word insertions (the `*`-stability
family is the manuscript's second closed family and is subsumed
by quantifying over all contexts); the `C*`-quotient `A/𝒩` is
rendered by its universal property (factorization through every
`𝒩`-killing homomorphism) rather than a quotient object.
-/

namespace NCG

/-- The contextual future-null space. -/
def contextualNull {A : Type*} [Ring A] {ι : Type*}
    (R : ι → A →+ ℂ) : Set A :=
  {q | ∀ (i : ι) (u v : A), R i (u * q * v) = 0}

/-- The contextual null space is a two-sided ideal
(abstract-ring form of `lem:contextual-null-ideal`). -/
theorem contextual_null_absorption {A : Type*} [Ring A] {ι : Type*}
    (R : ι → A →+ ℂ) :
    ((0 : A) ∈ contextualNull R)
    ∧ (∀ p q, p ∈ contextualNull R → q ∈ contextualNull R →
        p + q ∈ contextualNull R)
    ∧ (∀ q, q ∈ contextualNull R → -q ∈ contextualNull R)
    ∧ (∀ (a q : A), q ∈ contextualNull R →
        a * q ∈ contextualNull R)
    ∧ (∀ (a q : A), q ∈ contextualNull R →
        q * a ∈ contextualNull R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i u v
    rw [mul_zero, zero_mul, map_zero]
  · intro p q hp hq i u v
    rw [mul_add, add_mul, map_add, hp i u v, hq i u v,
      add_zero]
  · intro q hq i u v
    rw [mul_neg, neg_mul, map_neg, hq i u v, neg_zero]
  · intro a q hq i u v
    rw [show u * (a * q) = u * a * q from (mul_assoc u a q).symm]
    exact hq i (u * a) v
  · intro a q hq i u v
    rw [show u * (q * a) * v = u * q * (a * v) from by
      rw [← mul_assoc u q a, mul_assoc (u * q) a v]]
    exact hq i u (a * v)

/-- `thm:contextual-envelope-universal`: kernel inclusion,
universal factorization, and injectivity on separated
quotients. -/
theorem contextual_envelope_universal {A B C : Type*} [Ring A]
    [Ring B] [Ring C] {ι : Type*} (R : ι → A →+ ℂ)
    (π : A →+* B) (hπ : Function.Surjective π)
    (R' : ι → B →+ ℂ) (hfact : ∀ i x, R i x = R' i (π x)) :
    (∀ x, π x = 0 → x ∈ contextualNull R)
    ∧ (∀ θ : A →+* C, (∀ x ∈ contextualNull R, θ x = 0) →
        ∃ ψ : B →+* C, ∀ x, ψ (π x) = θ x)
    ∧ (∀ θ : A →+* C, (∀ x, θ x = 0 ↔ x ∈ contextualNull R) →
        (∀ b : B, (∀ (i : ι) (u v : B), R' i (u * b * v) = 0) →
          b = 0) →
        ∀ ψ : B →+* C, (∀ x, ψ (π x) = θ x) →
          Function.Injective ψ) := by
  have hker : ∀ x, π x = 0 → x ∈ contextualNull R := by
    intro x hx i u v
    rw [hfact, map_mul π, map_mul π, hx, mul_zero, zero_mul,
      map_zero]
  refine ⟨hker, ?_, ?_⟩
  · intro θ hθ
    have hle : RingHom.ker π ≤ RingHom.ker θ := by
      intro x hx
      rw [RingHom.mem_ker] at hx ⊢
      exact hθ x (hker x hx)
    refine ⟨π.liftOfSurjective hπ ⟨θ, hle⟩, fun x => ?_⟩
    exact π.liftOfRightInverse_comp_apply _ _ ⟨θ, hle⟩ x
  · intro θ hθiff hsep ψ hψ b1 b2 heq
    have hsub : ∀ b : B, ψ b = 0 → b = 0 := by
      intro b hb
      obtain ⟨x, rfl⟩ := hπ b
      rw [hψ] at hb
      have hxN : x ∈ contextualNull R := (hθiff x).mp hb
      refine hsep (π x) ?_
      intro i u v
      obtain ⟨a, rfl⟩ := hπ u
      obtain ⟨c, rfl⟩ := hπ v
      rw [← map_mul π, ← map_mul π, ← hfact]
      exact hxN i a c
    have h0 : ψ (b1 - b2) = 0 := by
      rw [map_sub, heq, sub_self]
    have := hsub _ h0
    exact sub_eq_zero.mp this

end NCG
