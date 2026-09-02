/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.SourceKernelMinimalUniqueness

/-!
# Positive source-minimal carrier of finite spectral commutators

For a finite Dirac matrix and any finite selected coefficient family, the
vectorized commutators form a concrete synthesis matrix.  Its Gram is
positive semidefinite, detects exactly the vanishing commutator combinations,
and its positive square root realizes the smallest possible carrier rank.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG.FiniteSpectralCommutatorGramCarrierExact

noncomputable section

variable {H K : Type} [Fintype H] [Fintype K] [DecidableEq K]

/-- Matrix commutator in the selected finite Hilbert carrier. -/
def spectralCommutator (D R : Matrix H H ℂ) : Matrix H H ℂ :=
  D * R - R * D

/-- Synthesis matrix whose `a`-th column is the vectorized commutator
`[D, ρ(a)]`. -/
def commutatorSynthesis (D : Matrix H H ℂ)
    (ρ : K → Matrix H H ℂ) : Matrix (H × H) K ℂ :=
  fun p a => spectralCommutator D (ρ a) p.1 p.2

/-- Hilbert--Schmidt Gram matrix of the selected commutators. -/
def commutatorGram (D : Matrix H H ℂ)
    (ρ : K → Matrix H H ℂ) : Matrix K K ℂ :=
  (commutatorSynthesis D ρ)ᴴ * commutatorSynthesis D ρ

theorem commutatorGram_apply (D : Matrix H H ℂ)
    (ρ : K → Matrix H H ℂ) (a b : K) :
    commutatorGram D ρ a b =
      ∑ p : H × H,
        star (spectralCommutator D (ρ a) p.1 p.2) *
          spectralCommutator D (ρ b) p.1 p.2 := by
  simp [commutatorGram, commutatorSynthesis, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

/-- Positivity of the finite commutator Gram. -/
theorem commutatorGram_posSemidef (D : Matrix H H ℂ)
    (ρ : K → Matrix H H ℂ) :
    (commutatorGram D ρ).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self
    (commutatorSynthesis D ρ)

/-- The Gram null space is exactly the space of coefficient combinations
whose represented commutator vanishes. -/
theorem commutatorGram_mulVec_eq_zero_iff
    (D : Matrix H H ℂ) (ρ : K → Matrix H H ℂ) (c : K → ℂ) :
    commutatorGram D ρ *ᵥ c = 0 ↔
      commutatorSynthesis D ρ *ᵥ c = 0 := by
  exact Matrix.conjTranspose_mul_self_mulVec_eq_zero
    (commutatorSynthesis D ρ) c

/-- The canonical square-root realization is source-minimal: it realizes the
Gram, every other finite realization has at least its rank, and its own rank
is exactly the Gram rank. -/
theorem commutatorGram_sourceMinimal
    (D : Matrix H H ℂ) (ρ : K → Matrix H H ℂ) :
    let G := commutatorGram D ρ
    G = (CFC.sqrt G)ᴴ * CFC.sqrt G ∧
    (∀ {C : Type} [Fintype C] (S : Matrix C K ℂ),
      G = Sᴴ * S → G.rank ≤ Fintype.card C) ∧
    (CFC.sqrt G).rank = G.rank := by
  dsimp only
  have h := NCG.source_kernel_realization_minimal_unique
    (commutatorGram D ρ) (commutatorGram_posSemidef D ρ)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Combined positive, faithful-null, source-minimal commutator certificate. -/
theorem finite_spectral_commutator_gram_carrier_exact
    (D : Matrix H H ℂ) (ρ : K → Matrix H H ℂ) :
    (commutatorGram D ρ).PosSemidef ∧
    (∀ c : K → ℂ, commutatorGram D ρ *ᵥ c = 0 ↔
      commutatorSynthesis D ρ *ᵥ c = 0) ∧
    (let G := commutatorGram D ρ;
      G = (CFC.sqrt G)ᴴ * CFC.sqrt G ∧
      (∀ {C : Type} [Fintype C] (S : Matrix C K ℂ),
        G = Sᴴ * S → G.rank ≤ Fintype.card C) ∧
      (CFC.sqrt G).rank = G.rank) := by
  exact ⟨commutatorGram_posSemidef D ρ,
    commutatorGram_mulVec_eq_zero_iff D ρ,
    commutatorGram_sourceMinimal D ρ⟩

end

end NCG.FiniteSpectralCommutatorGramCarrierExact
