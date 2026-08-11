/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EndpointRefinementCoequalizer
import NCG.Grand.ExactSourceSchurResidual

/-!
# Finite endpoint coequalizer and capacity reconstruction

This file proves `prop:endpoint-capacity-reconstruction`.  A finite relation
ledger reconstructs the generated endpoint equivalence and retains explicit
equivalence-chain witnesses.  The efficient edge matrix is the exact
Moore--Penrose Schur short, and its full two-sided Gram is invariant under an
arbitrary nuisance-valued correction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

namespace FiniteEndpointCapacity

open EndpointRefinementCoequalizer

/-- The finite reconstructed ledger of endpoint pairs identified by the face
matches.  This is the mathematical output of a terminating finite union--find
pass; membership retains the generated equivalence-chain proof. -/
noncomputable def endpointEquivalenceLedger
    {X : Type*} [Fintype X] (matchRel : X → X → Prop) : Finset (X × X) := by
  classical
  exact Finset.univ.filter fun xy => Relation.EqvGen matchRel xy.1 xy.2

theorem mem_endpointEquivalenceLedger_iff
    {X : Type*} [Fintype X] (matchRel : X → X → Prop) (x y : X) :
    (x, y) ∈ endpointEquivalenceLedger matchRel ↔
      Relation.EqvGen matchRel x y := by
  classical
  simp [endpointEquivalenceLedger]

/-- The finite ledger reconstructs precisely equality in the endpoint
coequalizer. -/
theorem mem_endpointEquivalenceLedger_iff_quotient_eq
    {X : Type*} [Fintype X] (matchRel : X → X → Prop) (x y : X) :
    (x, y) ∈ endpointEquivalenceLedger matchRel ↔
      quotientMap matchRel x = quotientMap matchRel y := by
  rw [mem_endpointEquivalenceLedger_iff, quotientMap_eq_iff]

/-- A local-cell collapse is an explicit pair of distinct local endpoints and
the generated equivalence chain which identifies them. -/
def CellCollapseWitness {X Cell : Type*} (matchRel : X → X → Prop)
    (cell : X → Cell) : Prop :=
  ∃ x y, x ≠ y ∧ cell x = cell y ∧ Relation.EqvGen matchRel x y

theorem cellCollapseWitness_iff_ledger
    {X Cell : Type*} [Fintype X]
    (matchRel : X → X → Prop) (cell : X → Cell) :
    CellCollapseWitness matchRel cell ↔
      ∃ x y, x ≠ y ∧ cell x = cell y ∧
        (x, y) ∈ endpointEquivalenceLedger matchRel := by
  simp only [CellCollapseWitness, mem_endpointEquivalenceLedger_iff]

/-- Every failure predicate on endpoint pairs has a finite witness ledger.
This covers face over-incidence, orientation, and vertex-link Read failures
once their finite predicates are supplied. -/
noncomputable def endpointFailureLedger
    {X : Type*} [Fintype X] (bad : X → X → Prop) : Finset (X × X) := by
  classical
  exact Finset.univ.filter fun xy => bad xy.1 xy.2

theorem endpointFailureLedger_nonempty_iff
    {X : Type*} [Fintype X] (bad : X → X → Prop) :
    (endpointFailureLedger bad).Nonempty ↔ ∃ x y, bad x y := by
  classical
  constructor
  · rintro ⟨xy, hxy⟩
    have hbad : bad xy.1 xy.2 := by
      simpa [endpointFailureLedger] using hxy
    exact ⟨xy.1, xy.2, hbad⟩
  · rintro ⟨x, y, hxy⟩
    refine ⟨(x, y), ?_⟩
    simp [endpointFailureLedger, hxy]

/-- The endpoint coequalizer of a finite endpoint ledger is finite. -/
theorem endpointCoequalizer_finite
    {X : Type*} [Fintype X] (matchRel : X → X → Prop) :
    Finite (Coequalizer matchRel) := by
  exact Finite.of_surjective (quotientMap matchRel)
    (quotientMap_surjective matchRel)

/-- Efficient edge-current Gram after orthogonally shorting all nuisance
directions. -/
noncomputable def efficientEdgeCapacityMatrix {h e n : ℕ}
    (N : Matrix (Fin h) (Fin n) ℂ) (S : Matrix (Fin h) (Fin e) ℂ) :
    Matrix (Fin e) (Fin e) ℂ :=
  Sᴴ * (1 - sourceRangeProjection N) * S

/-- Physical capacity extracted from the diagonal of the efficient edge
matrix. -/
noncomputable def efficientEdgeCapacity {h e n : ℕ}
    (scale : ℝ) (N : Matrix (Fin h) (Fin n) ℂ)
    (S : Matrix (Fin h) (Fin e) ℂ) (edge : Fin e) : ℝ :=
  scale * (efficientEdgeCapacityMatrix N S edge edge).re

/-- The reconstructed efficient edge matrix is exactly the Moore--Penrose
source Schur short and is positive semidefinite. -/
theorem efficientEdgeCapacityMatrix_eq_schurShort_and_posSemidef
    {h e n : ℕ} (N : Matrix (Fin h) (Fin n) ℂ)
    (S : Matrix (Fin h) (Fin e) ℂ) :
    efficientEdgeCapacityMatrix N S = sourceSchurResidual N S
      ∧ (efficientEdgeCapacityMatrix N S).PosSemidef := by
  have heq : efficientEdgeCapacityMatrix N S = sourceSchurResidual N S := by
    rw [sourceSchurResidual_eq_orthogonalResidual]
    rfl
  exact ⟨heq, heq ▸ sourceSchurResidual_posSemidef N S⟩

/-- Full two-sided nuisance invariance of the efficient Gram, with no
invertibility assumption on the nuisance source. -/
theorem efficientEdgeCapacityMatrix_nuisanceInvariant
    {h e n : ℕ} (N : Matrix (Fin h) (Fin n) ℂ)
    (S : Matrix (Fin h) (Fin e) ℂ) (L : Matrix (Fin n) (Fin e) ℂ) :
    efficientEdgeCapacityMatrix N (S + N * L) =
      efficientEdgeCapacityMatrix N S := by
  let P := sourceRangeProjection N
  let Q : Matrix (Fin h) (Fin h) ℂ := 1 - P
  obtain ⟨hPH, -, hPN⟩ :=
    (sourceGramPseudoinverse_projection N).2.2.2
  change Pᴴ = P at hPH
  change P * N = N at hPN
  have hQN : Q * N = 0 := by
    dsimp only [Q]
    rw [Matrix.sub_mul, Matrix.one_mul, hPN, sub_self]
  have hNQ : Nᴴ * Q = 0 := by
    have ht := congrArg conjTranspose hQN
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH] at ht
    change Nᴴ * (1 - P) = 0
    exact ht
  have hQNL : Q * (N * L) = 0 := by
    rw [← Matrix.mul_assoc, hQN, Matrix.zero_mul]
  have hNLQ : (N * L)ᴴ * Q = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hNQ, Matrix.mul_zero]
  change (S + N * L)ᴴ * Q * (S + N * L) = Sᴴ * Q * S
  rw [Matrix.conjTranspose_add, Matrix.add_mul, hNLQ, add_zero,
    Matrix.mul_add]
  have hcross : Sᴴ * Q * (N * L) = 0 := by
    rw [Matrix.mul_assoc, hQNL, Matrix.mul_zero]
  rw [hcross, add_zero]

/-- Consequently every diagonal physical capacity is nuisance invariant. -/
theorem efficientEdgeCapacity_nuisanceInvariant
    {h e n : ℕ} (scale : ℝ) (N : Matrix (Fin h) (Fin n) ℂ)
    (S : Matrix (Fin h) (Fin e) ℂ) (L : Matrix (Fin n) (Fin e) ℂ)
    (edge : Fin e) :
    efficientEdgeCapacity scale N (S + N * L) edge =
      efficientEdgeCapacity scale N S edge := by
  unfold efficientEdgeCapacity
  rw [efficientEdgeCapacityMatrix_nuisanceInvariant]

end FiniteEndpointCapacity
end NCG
