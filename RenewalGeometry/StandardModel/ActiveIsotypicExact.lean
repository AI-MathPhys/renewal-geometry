/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.ExternalIsotypicKroneckerExact
import RenewalGeometry.StandardModel.ActiveResidualCensusExact
import RenewalGeometry.Commutant.PrivateLineCommutantWedderburnExact

/-!
# External isotypic algebra and multiplicity census (assembly)

`thm:active-isotypic` of the spacetime–gauge duality paper, assembled from its
clauses:

* the general clause at every finite word depth — for every unitary matrix
  representation `ρ` of a finite group on a finite carrier, the isotypic
  decomposition `eq:word-depth-isotypic`, Burnside fullness and irreducibility of the
  external factors, Schur separation of the sectors, `eq:external-isotypic`
  (`Wᴴ C^*(ρ(G)) W = ⊕_b M_{I b}(ℂ) ⊗ 1`), `eq:external-isotypic-commutant`
  (`Wᴴ C^*(ρ(G))' W = ⊕_b 1 ⊗ M_{J b}(ℂ)`) and the consequence that a unital
  `M_m(ℂ)` in the relative commutant needs an external multiplicity `≥ m`
  (`ExternalIsotypic.external_isotypic`);
* the degree-one census `(1, 2, 1, 1)` on the categorical carrier
  (`ActiveResidualCensus.degree_one_multiplicity_census`) and
  `eq:degree-one-commutant`: `𝒜'_{ext,1} ≅ ℂ ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ`
  (`DegreeOneWedderburn.degreeOneCommutantEquiv`, dimension `7`);
* the private-line census `(2, 2, 1, 1)`
  (`ActiveResidualCensus.private_line_multiplicity_census`) and
  `eq:degree-one-private-commutant`: the relative commutant on `E ⊕ ℂ` is
  `M₂(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ` (`PrivateLineWedderburn.privateLineCommutantEquiv`,
  dimension `10`);
* neither algebra contains a unital copy of `M₃(ℂ)`
  (`DegreeOneColourNoGo.degree_one_colour_no_go`).
-/

open Matrix Kronecker Module RenewalGeometry.ActiveResidual RenewalGeometry.ActiveResidualCensus
  RenewalGeometry.DegreeOneColourNoGo RenewalGeometry.DegreeOneWedderburn
  RenewalGeometry.PrivateLineWedderburn RenewalGeometry.ExternalIsotypic

namespace RenewalGeometry
namespace ActiveIsotypic

/-- **`thm:active-isotypic`** (external isotypic algebra and multiplicity census). -/
theorem active_isotypic :
    -- general clause, at every finite word depth (`eq:word-depth-isotypic`,
    -- `eq:external-isotypic`, `eq:external-isotypic-commutant`, and the `M_n` consequence)
    (∀ (G : Type) [Group G] [Fintype G] (n : Type) [Fintype n] [DecidableEq n]
        (ρ : G →* Matrix n n ℂ), (∀ g, (ρ g)ᴴ = ρ g⁻¹) →
        ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (I J : ι → Type)
          (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
          (_ : ∀ b, Fintype (J b)) (_ : ∀ b, DecidableEq (J b))
          (W : Matrix n (Σ b, I b × J b) ℂ) (ρb : ∀ b, G →* Matrix (I b) (I b) ℂ),
          Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (∀ b, Nonempty (I b)) ∧ (∀ b, Nonempty (J b)) ∧
          (∀ g, Wᴴ * ρ g * W =
            blockDiagonal' fun b => ρb b g ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) ∧
          (∀ b, Submodule.span ℂ (Set.range (ρb b)) = ⊤) ∧
          (∀ b (U : Submodule ℂ (I b → ℂ)),
            (∀ g, ∀ x ∈ U, ρb b g *ᵥ x ∈ U) → U = ⊥ ∨ U = ⊤) ∧
          (∀ b b', b ≠ b' → ∀ T : Matrix (I b) (I b') ℂ,
            (∀ g, T * ρb b' g = ρb b g * T) → T = 0) ∧
          (fun x => Wᴴ * x * W) ''
              (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) = actionBlockSet I J ∧
          (fun x => Wᴴ * x * W) ''
              matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) =
            multBlockSet I J ∧
          (∀ (m : ℕ) [NeZero m] (φ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix n n ℂ),
            (∀ a, φ a ∈ matCommutant
              (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ))) →
            ∀ b, m ≤ Fintype.card (J b))) ∧
    -- degree-one census `(1, 2, 1, 1)`: `χ_E = χ_1 + 2 χ_W + χ_{V₂} + χ_{W ⊗ sgn}`
    (∀ σ : Equiv.Perm V,
      (Pm σ).trace = 1 + 2 * (chiW σ : ℂ) + (chiV2 σ : ℂ) + (chiWsgn σ : ℂ)) ∧
    -- `eq:degree-one-commutant`
    Nonempty (Coord ≃ₐ[ℂ] degreeOneCommutant) ∧ finrank ℂ degreeOneCommutant = 7 ∧
    -- private-line census `(2, 2, 1, 1)`
    (∀ σ : Equiv.Perm V,
      (PmPlus σ).trace = 2 * 1 + 2 * (chiW σ : ℂ) + (chiV2 σ : ℂ) + (chiWsgn σ : ℂ)) ∧
    -- `eq:degree-one-private-commutant`
    Nonempty (Coord' ≃ₐ[ℂ] privateLineCommutant) ∧ finrank ℂ privateLineCommutant = 10 ∧
    -- neither algebra contains a unital copy of `M₃(ℂ)`
    (¬ ∃ _ : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] degreeOneCommutant, True) ∧
    (¬ ∃ _ : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] privateLineCommutant, True) :=
  ⟨fun _ _ _ _ _ _ ρ hunit => external_isotypic ρ hunit,
    degree_one_multiplicity_census, ⟨degreeOneCommutantEquiv⟩, finrank_degreeOneCommutant,
    private_line_multiplicity_census, ⟨privateLineCommutantEquiv⟩,
    finrank_privateLineCommutant, degree_one_colour_no_go.1, degree_one_colour_no_go.2⟩

end ActiveIsotypic
end RenewalGeometry
