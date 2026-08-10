/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SourceIdealSplit

/-!
# Isotypic localization of endpoint coherence

This module completes `cor:endpoint-defect-symmetry` by assembling the
single-isotypic commutant calculation over a finite family of irreducible
types.
-/

open Matrix
open scoped Kronecker

namespace NCG

variable {τ : Type*} [Fintype τ] [DecidableEq τ]
  {m v : τ → Type*} [∀ π, Fintype (m π)] [∀ π, Fintype (v π)]
  [∀ π, DecidableEq (m π)] [∀ π, DecidableEq (v π)]

/-- The central projection onto one isotypic summand. -/
def endpointIsotypicProjection (π : τ) :
    Matrix (Σ ρ, m ρ × v ρ) (Σ ρ, m ρ × v ρ) ℂ :=
  Matrix.diagonal fun i => if i.1 = π then 1 else 0

/-- The diagonal block of an endpoint operator on one isotypic summand. -/
def endpointIsotypicBlock
    (C : Matrix (Σ ρ, m ρ × v ρ) (Σ ρ, m ρ × v ρ) ℂ) (π : τ) :
    Matrix (m π × v π) (m π × v π) ℂ :=
  fun i j => C ⟨π, i⟩ ⟨π, j⟩

/-- Commutation with the central isotypic projections kills every cross-type
block. -/
theorem endpointDefect_crossIsotypic_zero
    (C : Matrix (Σ ρ, m ρ × v ρ) (Σ ρ, m ρ × v ρ) ℂ)
    (hcentral : ∀ π, C * endpointIsotypicProjection π
      = endpointIsotypicProjection π * C) :
    ∀ {π ρ : τ}, π ≠ ρ → ∀ i : m π × v π, ∀ j : m ρ × v ρ,
      C ⟨π, i⟩ ⟨ρ, j⟩ = 0 := by
  intro π ρ hπρ i j
  have h := congr_fun (congr_fun (hcentral π) ⟨π, i⟩) ⟨ρ, j⟩
  simp only [endpointIsotypicProjection, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at h
  simp at h
  exact (h (Ne.symm hπρ)).symm

/-- Full isotypic assembly: after cross blocks are removed by the central
projections, Schur's lemma on each irreducible carrier gives
`C = ⊕π Cπ ⊗ I_{Vπ}`. -/
theorem endpointDefect_isotypic_form
    (C : Matrix (Σ ρ, m ρ × v ρ) (Σ ρ, m ρ × v ρ) ℂ)
    (hv : ∀ π, Nonempty (v π))
    (hcentral : ∀ π, C * endpointIsotypicProjection π
      = endpointIsotypicProjection π * C)
    (hirr : ∀ π (B : Matrix (v π) (v π) ℂ),
      endpointIsotypicBlock C π *
          ((1 : Matrix (m π) (m π) ℂ) ⊗ₖ B)
        = ((1 : Matrix (m π) (m π) ℂ) ⊗ₖ B) *
          endpointIsotypicBlock C π) :
    ∃ A : ∀ π, Matrix (m π) (m π) ℂ,
      (∀ π, endpointIsotypicBlock C π =
        A π ⊗ₖ (1 : Matrix (v π) (v π) ℂ))
      ∧ (∀ {π ρ : τ}, π ≠ ρ →
          ∀ i : m π × v π, ∀ j : m ρ × v ρ,
            C ⟨π, i⟩ ⟨ρ, j⟩ = 0) := by
  classical
  have hblock : ∀ π, ∃ A : Matrix (m π) (m π) ℂ,
      endpointIsotypicBlock C π =
        A ⊗ₖ (1 : Matrix (v π) (v π) ℂ) := by
    intro π
    letI : Nonempty (v π) := hv π
    exact endpoint_defect_symmetry (endpointIsotypicBlock C π) (hirr π)
  choose A hA using hblock
  exact ⟨A, hA, endpointDefect_crossIsotypic_zero C hcentral⟩

/-- With a single multiplicity coordinate, the commutant is scalar: the full
transverse endpoint response is one complex visibility. -/
theorem endpointDefect_irreducible_visibility {κ : Type*} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (C : Matrix κ κ ℂ)
    (hcomm : ∀ B : Matrix κ κ ℂ, C * B = B * C) :
    ∃ c : ℂ, C = c • (1 : Matrix κ κ ℂ) := by
  let C' : Matrix (Unit × κ) (Unit × κ) ℂ :=
    fun i j => C i.2 j.2
  have hcomm' : ∀ B : Matrix κ κ ℂ,
      C' * ((1 : Matrix Unit Unit ℂ) ⊗ₖ B)
        = ((1 : Matrix Unit Unit ℂ) ⊗ₖ B) * C' := by
    intro B
    ext ⟨u, i⟩ ⟨v, j⟩
    cases u
    cases v
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    simpa [C', Matrix.kroneckerMap_apply, Matrix.mul_apply]
      using congr_fun (congr_fun (hcomm B) i) j
  obtain ⟨A, hA⟩ := endpoint_defect_symmetry C' hcomm'
  refine ⟨A () (), ?_⟩
  ext i j
  have h := congr_fun (congr_fun hA ((), i)) ((), j)
  simpa [C', Matrix.kroneckerMap_apply, Matrix.smul_apply] using h

end NCG
