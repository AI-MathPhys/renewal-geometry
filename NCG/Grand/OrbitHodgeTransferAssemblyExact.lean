/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConjugationOrbitDerivative

/-!
# Exact full-cell orbit and Hodge-to-commutator assembly

This file packages the orbit kernel, differentiated equivariant export, commutant descent, and
renormalized Hodge/commutator form estimate into the single theorem stated in the manuscript.
-/

namespace NCG

/-- **Canonical full-cell orbit and Hodge-to-commutator transfer
(`thm:SMST-orbit-Hodge-transfer`).** -/
theorem canonicalFullCellOrbit_hodgeToCommutatorTransfer
    {A : Type*} [CStarAlgebra A]
    {I K : Type*} [Fintype I] [Fintype K]
    (X : A) (G : I → A) (c : K → A)
    (Φ : (I → A) → (K → A))
    (D : (I → A) →L[ℂ] (K → A))
    (hΦ : HasFDerivAt Φ D G)
    (hequiv : ∀ t : ℂ,
      Φ (conjugationOrbit X G t) = conjugationOrbit X c t)
    {n ι κ : Type*} [Fintype n]
    (Gm : ι → Matrix n n ℂ) (cm : κ → Matrix n n ℂ)
    (M : Set (Matrix n n ℂ))
    (hexp : ∀ (Y : Matrix n n ℂ),
      (∀ i, Gm i * Y = Y * Gm i) → ∀ k, cm k * Y = Y * cm k)
    (hMG : ∀ Y ∈ M, ∀ i, Gm i * Y = Y * Gm i)
    (hcM : {Y : Matrix n n ℂ | ∀ k, cm k * Y = Y * cm k} = M)
    (C₀ Λ α ε r h q nn : ℝ)
    (hC₀ : 0 < C₀) (hcontr : C₀ * ε ^ 2 < 1)
    (hnn : 0 ≤ nn) (hRH : r ≤ C₀ * h + α * nn)
    (hHC : h ≤ Λ * q + ε ^ 2 * r) :
    D (orbitCommutator X G) = orbitCommutator X c
    ∧ (∃! v : K → A,
        HasDerivAt (fun t : ℂ => Φ (conjugationOrbit X G t)) v 0)
    ∧ (∀ Y : Matrix n n ℂ,
        (∀ j, Gm j * Y - Y * Gm j = 0)
          ↔ ∀ j, Gm j * Y = Y * Gm j)
    ∧ {Y : Matrix n n ℂ | ∀ i, Gm i * Y = Y * Gm i} = M
    ∧ r ≤ (C₀ * Λ / (1 - C₀ * ε ^ 2)) * q
        + (α / (1 - C₀ * ε ^ 2)) * nn := by
  exact ⟨equivariant_orbit_derivative X G c Φ D hΦ hequiv,
    equivariant_orbit_derivative_unique X G c Φ D hΦ hequiv,
    orbit_source_kernel Gm,
    orbit_commutant_descent Gm cm M hexp hMG hcM,
    hodge_commutator_transfer C₀ Λ α ε hC₀ hcontr r h q nn hnn hRH hHC⟩

end NCG
