/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical full-cell orbit and Hodge-to-commutator transfer
  (`thm:SMST-orbit-Hodge-transfer`,
  Gran-Tensor manuscript)

* `orbit_source_kernel`: the boxed conjugation-orbit source
  `𝒥_G(A) = ([G₁,A], …, [G_m,A])` has kernel exactly the
  commutant of the generating tuple.

* `orbit_commutant_descent`: the boxed descent
  `c ⊆ C*(G)`, `ℳ ⊆ C*(G)'`, `C*(c)' = ℳ ⟹ C*(G)' = ℳ`:
  an equivariant finite export cannot enlarge the
  commutant, so exactness of the action commutant forces
  exactness of the full-cell commutant.

* `hodge_commutator_transfer`: the boxed Loewner bootstrap
  `ℝ ⪯ C₀ℍ + αI`, `ℍ ⪯ Λℂ + ε²ℝ`, `C₀ε² < 1`
  `⟹ ℝ ⪯ (C₀Λ/(1-C₀ε²))ℂ + (α/(1-C₀ε²))I`:
  a Hodge floor transfers to the commutator form with an
  explicitly renormalized constant.

The differentiation step `𝒥_c = D_orb Φ_G 𝒥_G` for an
equivariant export `Φ` (and the identification of `ℍ`, `ℂ`,
`ℝ` with the shorted Hodge, commutator, and residual forms
on the unprotected operator space) is the manuscript's
export layer over these algebraic facts.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- `thm:SMST-orbit-Hodge-transfer`, the orbit source and
its kernel. -/
theorem orbit_source_kernel {n ι : Type*} [Fintype n]
    (G : ι → Matrix n n ℂ) :
    ∀ X : Matrix n n ℂ,
      (∀ j, G j * X - X * G j = 0)
        ↔ ∀ j, G j * X = X * G j := by
  intro X
  constructor
  · intro h j
    exact sub_eq_zero.mp (h j)
  · intro h j
    rw [h j, sub_self]

/-- `thm:SMST-orbit-Hodge-transfer`, commutant descent. -/
theorem orbit_commutant_descent {n ι κ : Type*}
    [Fintype n] (G : ι → Matrix n n ℂ)
    (c : κ → Matrix n n ℂ) (M : Set (Matrix n n ℂ))
    -- the action tuple is exported from the full cell
    (hexp : ∀ (X : Matrix n n ℂ),
      (∀ i, G i * X = X * G i) → ∀ k, c k * X = X * c k)
    -- the protected algebra commutes with the full cell
    (hMG : ∀ X ∈ M, ∀ i, G i * X = X * G i)
    -- exactness of the action commutant
    (hcM : {X : Matrix n n ℂ | ∀ k, c k * X = X * c k}
      = M) :
    -- the boxed conclusion
    {X : Matrix n n ℂ | ∀ i, G i * X = X * G i} = M := by
  apply Set.Subset.antisymm
  · intro X hX
    have : X ∈ {X : Matrix n n ℂ |
        ∀ k, c k * X = X * c k} := hexp X hX
    rwa [hcM] at this
  · intro X hX
    exact hMG X hX

/-- `thm:SMST-orbit-Hodge-transfer`, the boxed Loewner
bootstrap (quadratic-form version). -/
theorem hodge_commutator_transfer (C₀ Λ α ε : ℝ)
    (hC₀ : 0 < C₀) (hcontr : C₀ * ε ^ 2 < 1) :
    ∀ r h c nn : ℝ, 0 ≤ nn →
      r ≤ C₀ * h + α * nn →
      h ≤ Λ * c + ε ^ 2 * r →
      r ≤ (C₀ * Λ / (1 - C₀ * ε ^ 2)) * c
        + (α / (1 - C₀ * ε ^ 2)) * nn := by
  intro r h c nn _ h1 h2
  have hden : 0 < 1 - C₀ * ε ^ 2 := by linarith
  have hkey : (1 - C₀ * ε ^ 2) * r
      ≤ C₀ * Λ * c + α * nn := by
    nlinarith [h1, h2, hC₀]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
    le_div_iff₀ hden]
  linarith

end NCG
