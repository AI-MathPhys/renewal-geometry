/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Record-algebra structures of the renewal collapse account
  (`definition:record-algebra`, `definition:regenerative-record`,
   `ass:pointer-record`, `definition:predictive-branch-weight`,
   `def:regular-weight`, `definition:renewal-pointer-basis`,
   `definition:redundant-renewal-record`, wavefunction)

Formal encodings of the definitional records, in the finite-dimensional
matrix model used throughout the wavefunction ledger:

* `branchWeight` — `w(i) = Tr(E_i ρ)`;
* `PointerRecord` — a predictively sufficient pointer record
  (positive effects, resolution of identity, orthogonal labels,
  additive weights on disjoint coarse grainings — additivity is a
  consequence of trace linearity, recorded as `branchWeight_additive`);
* `RegularWeight` — the five clauses of the regular predictive
  amplitude weight (positivity, orthogonal additivity, tensor
  multiplicativity against a paired weight, channel-equivalent
  unitary invariance, ray regularity);
* `RegenerativeRecord` — the sector factorization
  `Φ_future ∘ Φ_record = Φ_future^{(i)} ∘ Π_i` (exact form of the
  predictive-quotient equivalence);
* `RenewalPointerBasis` — sector preservation
  `ℰ(P_i ρ P_i) ∈ P_i 𝓑 P_i`;
* `RedundantRecord` — fragment subalgebra inference maps agreeing on
  the sector label.

These are `statement_encoded` records: the definitions carry no
theorem content beyond `branchWeight_additive`; the "up to decaying
errors" clauses are encoded in their exact predictive-quotient form.
-/

namespace NCG

open Matrix

open scoped ComplexOrder

variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- `definition:predictive-branch-weight`: `w(i) = Tr(E_i ρ)`. -/
noncomputable def branchWeight (E rho : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (E * rho).trace

/-- `ass:pointer-record` (`definition:record-algebra` effects): a
predictively sufficient pointer record — positive orthogonal effects
resolving the identity. -/
structure PointerRecord (n : ℕ) (I : Type*) [Fintype I] where
  /-- the record effects -/
  E : I → Matrix (Fin n) (Fin n) ℂ
  /-- positivity of each effect -/
  pos : ∀ i, (E i).PosSemidef
  /-- resolution of identity -/
  complete : (∑ i, E i) = 1
  /-- distinguishable orthogonal labels -/
  orthogonal : ∀ i j, i ≠ j → E i * E j = 0

/-- Weights are automatically additive under disjoint coarse
graining (trace linearity) — the clause (iv) of `ass:pointer-record`
is not an independent postulate in the encoded model. -/
theorem branchWeight_additive (E1 E2 rho : Matrix (Fin n) (Fin n) ℂ) :
    branchWeight (E1 + E2) rho
      = branchWeight E1 rho + branchWeight E2 rho := by
  unfold branchWeight
  rw [Matrix.add_mul, Matrix.trace_add]

/-- `def:regular-weight`: the five clauses of a regular predictive
amplitude weight, on a finite-dimensional predictive module `H` with
a paired weight `W₂` on the composite `H ⊗ H`. -/
structure RegularWeight (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- the branch-weight functional -/
  W : H → ℝ
  /-- the composite weight on independent pairs -/
  W2 : TensorProduct ℂ H H → ℝ
  /-- (i) positivity -/
  zero : W 0 = 0
  pos : ∀ ψ : H, ψ ≠ 0 → 0 < W ψ
  /-- (ii) additivity on orthogonal record sectors -/
  additive : ∀ ψ φ : H, inner ℂ ψ φ = 0 → W (ψ + φ) = W ψ + W φ
  /-- (iii) multiplicativity under independent composition -/
  multiplicative : ∀ ψ φ : H,
    W2 (TensorProduct.tmul ℂ ψ φ) = W ψ * W φ
  /-- the channel-equivalent phase/deck transformations -/
  deck : Set (H ≃ₗᵢ[ℂ] H)
  /-- (iv) invariance under channel-equivalent phase/deck unitaries -/
  deck_invariant : ∀ u ∈ deck, ∀ ψ, W (u ψ) = W ψ
  /-- (v) weak regularity on one nontrivial ray -/
  ray_regular : ∃ ψ : H, ψ ≠ 0 ∧
    Continuous fun t : ℝ => W ((t : ℂ) • ψ)

/-- `definition:regenerative-record`: the record sector factorizes
the future predictive evolution through its projection. -/
structure RegenerativeRecord (n : ℕ) where
  /-- the sector projection channel -/
  Pi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ
  /-- the recorded channel -/
  record : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ
  /-- the future channel -/
  future : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ
  /-- the sector future channel -/
  futureSector : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ
  /-- the projection property -/
  idem : Pi.comp Pi = Pi
  /-- `Φ_future ∘ Φ_record = Φ_future^{(i)} ∘ Π_i` -/
  factorizes : future.comp record = futureSector.comp Pi

/-- `definition:renewal-pointer-basis`: repeated instrument
application preserves the diagonal sectors. -/
def RenewalPointerBasis (n : ℕ) (I : Type*) [Fintype I]
    (P : I → Matrix (Fin n) (Fin n) ℂ)
    (instr : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  (∀ i j, i ≠ j → P i * P j = 0) ∧ (∑ i, P i) = 1 ∧
    ∀ i (rho : Matrix (Fin n) (Fin n) ℂ), ∃ sigma,
      instr (P i * rho * P i) = P i * sigma * P i

/-- `definition:redundant-renewal-record`: fragment inference maps
agree on the sector label. -/
structure RedundantRecord (n N : ℕ) (I : Type*) where
  /-- the fragment observables available to observer `k` -/
  fragment : Fin N → Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)
  /-- each fragment infers the sector label -/
  infer : Fin N → Matrix (Fin n) (Fin n) ℂ → I
  /-- the true sector label read off the state -/
  label : Matrix (Fin n) (Fin n) ℂ → I
  /-- agreement of conditional predictions on overlaps -/
  agree : ∀ k (rho : Matrix (Fin n) (Fin n) ℂ),
    infer k rho = label rho

end NCG
