/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Inductive-limit machinery: AF states, quasilocal completion,
  and joint-source universality
  (`thm:AF-limit-state`, `thm:quasilocal-completion`,
  `thm:joint-source-inductive-limit`, Gran-Tensor manuscript)

Machinery on the algebraic inductive limit of an ℕ-indexed
directed system of `ℂ`-algebras (Mathlib's explicit
`DirectLimit` for directed systems):

* `limit_functional` / `limit_functional_of`: every compatible
  family of linear functionals `ω_{n+1}∘ι = ω_n` extends to the
  inductive limit, restricting to `ω_n` on stage `n` — the
  existence half of the unique state `ω_∞`;
* `limit_functional_unique`: two functionals agreeing with the
  same compatible family on every stage are equal — the
  uniqueness half;
* `limit_functional_unital`: unital families extend unitally,
  `ω_∞(1) = 1`;
* `limit_positive_on_stages`: stagewise positivity persists on
  the exhaustion — `ω_∞` is nonnegative on every positive stage
  element;
* `stage_exhaustion`: every element of the limit comes from a
  finite stage — the quasilocal algebra is exhausted by its
  local subalgebras;
* `limit_map_extension` / `limit_map_extension_of`: every
  compatible family of stage maps `Φ_n` (commuting with the
  embeddings) extends to the limit;
* `limit_map_semigroup`: extension is multiplicative in
  composition — if the local maps form a semigroup, so do the
  extensions (`(Φ∘Ψ)_∞ = Φ_∞ ∘ Ψ_∞`).

Rendering disclosed: the C*-completion (sup-norm on the
algebraic limit, GNS boundedness `‖π(a)‖ ≤ ‖a‖`, and UCP-norm
contractivity of the extended maps) is the remaining
operator-norm layer for the AF-state theorem.  The Hilbert-space
completion, common-carrier isometries, and cross-transport defect criterion
for the joint-source theorem are proved in
`NCG.Grand.JointSourceHilbertInductiveLimit`; the algebraic inductive limit,
the unique unital positive functional extension, the exhaustion,
and the semigroup map extension are proved here on Mathlib's
directed-system colimit.
-/

open DirectLimit

namespace NCG

variable {G : ℕ → Type*} [∀ n, AddCommMonoid (G n)]
  [∀ n, Module ℂ (G n)]
  {f : ∀ i j : ℕ, i ≤ j → (G i →ₗ[ℂ] G j)}
  [DirectedSystem G (fun i j h => f i j h)]

/-- Existence: a compatible family of stage functionals extends
to the inductive limit. -/
noncomputable def limit_functional (φ : ∀ n, G n →ₗ[ℂ] ℂ)
    (hφ : ∀ i j hij x, φ j (f i j hij x) = φ i x) :
    (DirectLimit G fun i j h => f i j h) →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ ℕ G (fun i j h => f i j h) φ hφ

/-- The extension restricts to `ω_n` on stage `n`. -/
theorem limit_functional_of (φ : ∀ n, G n →ₗ[ℂ] ℂ)
    (hφ : ∀ i j hij x, φ j (f i j hij x) = φ i x) (n : ℕ)
    (x : G n) :
    limit_functional φ hφ
      (DirectLimit.Module.of ℂ ℕ G (fun i j h => f i j h) n x)
    = φ n x :=
  DirectLimit.Module.lift_of φ hφ x

/-- Uniqueness: two functionals agreeing with the same stage
family are equal. -/
theorem limit_functional_unique
    (Φ₁ Φ₂ : (DirectLimit G fun i j h => f i j h) →ₗ[ℂ] ℂ)
    (h : ∀ n, Φ₁ ∘ₗ
        DirectLimit.Module.of ℂ ℕ G (fun i j h => f i j h) n
      = Φ₂ ∘ₗ
        DirectLimit.Module.of ℂ ℕ G (fun i j h => f i j h) n) :
    Φ₁ = Φ₂ :=
  DirectLimit.Module.hom_ext h

/-- Every element of the limit comes from a finite stage — the
quasilocal exhaustion. -/
theorem stage_exhaustion
    (z : DirectLimit G fun i j h => f i j h) :
    ∃ (n : ℕ) (x : G n),
      z = DirectLimit.Module.of ℂ ℕ G
        (fun i j h => f i j h) n x := by
  induction z using DirectLimit.induction with
  | _ n x => exact ⟨n, x, rfl⟩

/-- Stagewise positivity persists on the exhaustion. -/
theorem limit_positive_on_stages (φ : ∀ n, G n →ₗ[ℂ] ℂ)
    (hφ : ∀ i j hij x, φ j (f i j hij x) = φ i x)
    (P : ∀ n, Set (G n)) (hpos : ∀ n, ∀ x ∈ P n, 0 ≤ (φ n x).re)
    (n : ℕ) (x : G n) (hx : x ∈ P n) :
    0 ≤ (limit_functional φ hφ
      (DirectLimit.Module.of ℂ ℕ G
        (fun i j h => f i j h) n x)).re := by
  rw [limit_functional_of]
  exact hpos n x hx

/-- Compatible stage maps extend to the limit. -/
noncomputable def limit_map_extension
    (Φ : ∀ n, G n →ₗ[ℂ] G n)
    (hΦ : ∀ i j hij x,
      Φ j (f i j hij x) = f i j hij (Φ i x)) :
    (DirectLimit G fun i j h => f i j h) →ₗ[ℂ]
      (DirectLimit G fun i j h => f i j h) :=
  DirectLimit.Module.lift ℂ ℕ G (fun i j h => f i j h)
    (fun n => (DirectLimit.Module.of ℂ ℕ G
      (fun i j h => f i j h) n) ∘ₗ Φ n)
    (fun i j hij x => by
      simp only [LinearMap.comp_apply]
      rw [hΦ i j hij x, DirectLimit.Module.of_f])

/-- The extension restricts to `Φ_n` on stage `n`. -/
theorem limit_map_extension_of (Φ : ∀ n, G n →ₗ[ℂ] G n)
    (hΦ : ∀ i j hij x,
      Φ j (f i j hij x) = f i j hij (Φ i x)) (n : ℕ) (x : G n) :
    limit_map_extension Φ hΦ
      (DirectLimit.Module.of ℂ ℕ G (fun i j h => f i j h) n x)
    = DirectLimit.Module.of ℂ ℕ G (fun i j h => f i j h) n
        (Φ n x) :=
  DirectLimit.Module.lift_of _ _ x

/-- Semigroup law: composition of compatible families extends
to composition of extensions. -/
theorem limit_map_semigroup (Φ Ψ : ∀ n, G n →ₗ[ℂ] G n)
    (hΦ : ∀ i j hij x, Φ j (f i j hij x) = f i j hij (Φ i x))
    (hΨ : ∀ i j hij x, Ψ j (f i j hij x) = f i j hij (Ψ i x))
    (hΦΨ : ∀ i j hij x,
      (Φ j ∘ₗ Ψ j) (f i j hij x) = f i j hij ((Φ i ∘ₗ Ψ i) x)) :
    limit_map_extension (fun n => Φ n ∘ₗ Ψ n) hΦΨ
      = (limit_map_extension Φ hΦ) ∘ₗ
        (limit_map_extension Ψ hΨ) := by
  refine DirectLimit.Module.hom_ext fun n => ?_
  ext x
  simp only [LinearMap.comp_apply]
  rw [limit_map_extension_of, limit_map_extension_of,
    limit_map_extension_of]
  rfl

/-- Unitality: with a distinguished stage-compatible unit
vector, unital families extend unitally. -/
theorem limit_functional_unital (φ : ∀ n, G n →ₗ[ℂ] ℂ)
    (hφ : ∀ i j hij x, φ j (f i j hij x) = φ i x)
    (u : ∀ n, G n) (hone : ∀ n, φ n (u n) = 1) (n : ℕ) :
    limit_functional φ hφ
      (DirectLimit.Module.of ℂ ℕ G
        (fun i j h => f i j h) n (u n)) = 1 := by
  rw [limit_functional_of]
  exact hone n

end NCG
