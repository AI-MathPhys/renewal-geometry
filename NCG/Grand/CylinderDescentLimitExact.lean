/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cylinder descent: the algebraic order-unit limit state

Third machinery layer for `thm:global-cylinder-descent` — the algebraic
content of (G7) and of the converse extension clause, on the directed system
of finite closed-tester spaces over the cutoff order `ℕ`:

* `limit_state_exists` (G7): a compatible family of finite closed-tester
  functionals is the family of exact restrictions of **one** functional on
  the algebraic cylinder limit;
* `limit_state_unique` / `limit_state_existsUnique` (converse): an exactly
  compatible family extends **uniquely** — two limit functionals agreeing on
  every finite tester coincide;
* `exists_separating_tester` (converse, failure witness): two distinct limit
  functionals are separated by one finite tester at one finite cutoff.

The `C^*`/order-theoretic completion of (G7) — extending the algebraic state
to the AF or quasilocal norm closure — is analytic content beyond this layer
and is disclosed at the record level.
-/

namespace NCG
namespace CylinderDescentLimit

variable {G : ℕ → Type*} [∀ n, AddCommGroup (G n)] [∀ n, Module ℂ (G n)]
variable (f : ∀ i j : ℕ, i ≤ j → G i →ₗ[ℂ] G j)

/-- **(G7), algebraic part**: a compatible family of finite closed-tester
functionals is the family of exact restrictions of one functional on the
algebraic cylinder limit. -/
theorem limit_state_exists (φ : ∀ n, G n →ₗ[ℂ] ℂ)
    (Hφ : ∀ i j hij x, φ j (f i j hij x) = φ i x) :
    ∃ Φ : Module.DirectLimit G f →ₗ[ℂ] ℂ,
      ∀ n x, Φ (Module.DirectLimit.of ℂ ℕ G f n x) = φ n x := by
  refine ⟨Module.DirectLimit.lift ℂ ℕ G f φ Hφ, fun n x => ?_⟩
  simp

/-- **(converse), uniqueness**: two limit functionals agreeing on every
finite tester coincide. -/
theorem limit_state_unique {Φ Ψ : Module.DirectLimit G f →ₗ[ℂ] ℂ}
    (h : ∀ n x, Φ (Module.DirectLimit.of ℂ ℕ G f n x)
      = Ψ (Module.DirectLimit.of ℂ ℕ G f n x)) : Φ = Ψ :=
  Module.DirectLimit.hom_ext fun n => LinearMap.ext fun x => h n x

/-- **(G7) + (converse), bundled**: an exactly compatible family of finite
cylinder tester functionals extends uniquely to the algebraic cylinder
limit. -/
theorem limit_state_existsUnique (φ : ∀ n, G n →ₗ[ℂ] ℂ)
    (Hφ : ∀ i j hij x, φ j (f i j hij x) = φ i x) :
    ∃! Φ : Module.DirectLimit G f →ₗ[ℂ] ℂ,
      ∀ n x, Φ (Module.DirectLimit.of ℂ ℕ G f n x) = φ n x := by
  obtain ⟨Φ, hΦ⟩ := limit_state_exists f φ Hφ
  exact ⟨Φ, hΦ, fun Ψ hΨ =>
    limit_state_unique f fun n x => (hΨ n x).trans (hΦ n x).symm⟩

/-- **(converse), the finite witness**: a failure of compatibility between two
purported limit extensions is witnessed by one finite tester at one finite
cutoff whose value differs. -/
theorem exists_separating_tester {Φ Ψ : Module.DirectLimit G f →ₗ[ℂ] ℂ}
    (h : Φ ≠ Ψ) :
    ∃ n x, Φ (Module.DirectLimit.of ℂ ℕ G f n x)
      ≠ Ψ (Module.DirectLimit.of ℂ ℕ G f n x) := by
  by_contra hc
  apply h
  apply limit_state_unique
  intro n x
  by_contra hne
  exact hc ⟨n, x, hne⟩

end CylinderDescentLimit
end NCG
