/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperationalRecordCompletionFunctoriality
import NCG.Grand.OperationalCompletionConservativity
import NCG.Grand.MinimalRecordAudit
import NCG.Grand.SimultaneousNuisanceUniversalShort
import NCG.Grand.JointSourceRangeUnitary

/-!
# Conservative relational completion

This module is the exact finite assembly for
`thm:relational-completion`.  It gives the literal stochastic-kernel branch
of (RC.3), proves the boxed forgetful identity (RC.6), propagates that identity
through every finite word, and packages the already checked minimal-record,
history-algebra, word-Gram, simultaneous-short, and source-uniqueness layers.
-/

open Matrix
open scoped BigOperators ComplexOrder Kronecker

namespace NCG.RelationalCompletion

/-- A finite relational kernel in the orientation
`weight o gamma xi target source`. -/
structure Kernel (O Γ Ξ Z : Type*) [Fintype Γ] [Fintype Ξ] [Fintype Z] where
  weight : O → Γ → Ξ → Z → Z → ℝ
  nonnegative : ∀ o γ ξ z' z, 0 ≤ weight o γ ξ z' z
  normalized : ∀ o z, ∑ z', ∑ γ, ∑ ξ, weight o γ ξ z' z = 1

/-- Block-state relation forgetting: sum all persistent relation sectors. -/
def forgetRelation {Z d : Type*} [Fintype Z]
    (ρ : Z → Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ z, ρ z

/-- The literal branch (RC.3): the old CP branch is multiplied by the
nonnegative relational kernel and summed over the source relation state. -/
noncomputable def branch
    {O Γ Ξ Z d : Type*} [Fintype Γ] [Fintype Ξ] [Fintype Z]
    (K : Kernel O Γ Ξ Z)
    (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (o : O) (γ : Γ) (ξ : Ξ) :
    (Z → Matrix d d ℂ) →ₗ[ℂ] (Z → Matrix d d ℂ) where
  toFun ρ z' :=
    ∑ z, (K.weight o γ ξ z' z : ℂ) • Φ o (ρ z)
  map_add' ρ σ := by
    funext z'
    change (∑ z, (K.weight o γ ξ z' z : ℂ) • Φ o (ρ z + σ z)) =
      (∑ z, (K.weight o γ ξ z' z : ℂ) • Φ o (ρ z)) +
        ∑ z, (K.weight o γ ξ z' z : ℂ) • Φ o (σ z)
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c ρ := by
    funext z'
    change (∑ z, (K.weight o γ ξ z' z : ℂ) • Φ o (c • ρ z)) =
      c • ∑ z, (K.weight o γ ξ z' z : ℂ) • Φ o (ρ z)
    simp only [map_smul, smul_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [mul_comm]

/-- Summing the resolved marks of (RC.3) produces the total relationally
refined old branch. -/
noncomputable def totalBranch
    {O Γ Ξ Z d : Type*} [Fintype Γ] [Fintype Ξ] [Fintype Z]
    (K : Kernel O Γ Ξ Z)
    (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (o : O) (ρ : Z → Matrix d d ℂ) : Z → Matrix d d ℂ :=
  fun z' => ∑ γ, ∑ ξ, branch K Φ o γ ξ ρ z'

/-- The definition of `totalBranch` is the sum of all resolved relational
branches, with no hidden independence or product-state hypothesis. -/
theorem totalBranch_apply
    {O Γ Ξ Z d : Type*} [Fintype Γ] [Fintype Ξ] [Fintype Z]
    (K : Kernel O Γ Ξ Z)
    (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (o : O) (ρ : Z → Matrix d d ℂ) (z' : Z) :
    totalBranch K Φ o ρ z' =
      ∑ z, ∑ γ, ∑ ξ,
        (K.weight o γ ξ z' z : ℂ) • Φ o (ρ z) := by
  classical
  simp only [totalBranch, branch, LinearMap.coe_mk, AddHom.coe_mk]
  calc
    ∑ γ, ∑ ξ, ∑ z, (K.weight o γ ξ z' z : ℂ) • Φ o (ρ z)
        = ∑ γ, ∑ z, ∑ ξ,
            (K.weight o γ ξ z' z : ℂ) • Φ o (ρ z) := by
          apply Finset.sum_congr rfl
          intro γ _
          rw [Finset.sum_comm]
    _ = ∑ z, ∑ γ, ∑ ξ,
          (K.weight o γ ξ z' z : ℂ) • Φ o (ρ z) := Finset.sum_comm

/-- Boxed equation (RC.6): forgetting the persistent relation packet after
summing all resolved marks recovers the old branch exactly. -/
theorem forget_totalBranch
    {O Γ Ξ Z d : Type*} [Fintype Γ] [Fintype Ξ] [Fintype Z]
    (K : Kernel O Γ Ξ Z)
    (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (o : O) (ρ : Z → Matrix d d ℂ) :
    forgetRelation (totalBranch K Φ o ρ) =
      Φ o (forgetRelation ρ) := by
  classical
  simp only [forgetRelation, totalBranch_apply]
  rw [Finset.sum_comm]
  calc
    ∑ z, ∑ z', ∑ γ, ∑ ξ,
          (K.weight o γ ξ z' z : ℂ) • Φ o (ρ z)
        = ∑ z, ((∑ z', ∑ γ, ∑ ξ,
            K.weight o γ ξ z' z : ℝ) : ℂ) • Φ o (ρ z) := by
          apply Finset.sum_congr rfl
          intro z _
          simp only [Complex.ofReal_sum, Finset.sum_smul]
    _ = ∑ z, Φ o (ρ z) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [K.normalized]
          simp
    _ = Φ o (∑ z, ρ z) := by
          rw [map_sum]

/-- One-step forgetful intertwining propagates to every finite branch word.
Consequently every old cylinder and every statistic factoring through its old
payload is preserved by the relational completion. -/
theorem forget_intertwines_every_word
    {O Old New : Type*}
    (oldStep : O → Old → Old) (newStep : O → New → New)
    (forget : New → Old)
    (hstep : ∀ o x, forget (newStep o x) = oldStep o (forget x)) :
    ∀ (word : List O) (x : New),
      forget (word.foldl (fun state o => newStep o state) x) =
        word.foldl (fun state o => oldStep o state) (forget x) := by
  intro word
  induction word with
  | nil => intro x; rfl
  | cons o word ih =>
      intro x
      simp only [List.foldl_cons]
      rw [ih, hstep]

/-- Finite Kraus/Choi certificate for each resolved relational branch.  The
writer may depend on the source relation sector, so this covers the general
same-history conditional extension rather than only a tensor spectator. -/
theorem resolvedBranch_choi_pos
    {Z d κ : Type} [Fintype Z] [Fintype d] [Fintype κ]
    (writer : Z → Matrix Z Z ℂ) (oldKraus : Z → κ → Matrix d d ℂ) :
    (∑ j : Z × κ, Matrix.vecMulVec
      (fun p : (Z × d) × (Z × d) =>
        (writer j.1 ⊗ₖ oldKraus j.1 j.2) p.2 p.1)
      (star fun p : (Z × d) × (Z × d) =>
        (writer j.1 ⊗ₖ oldKraus j.1 j.2) p.2 p.1)).PosSemidef :=
  (comb_tomography (m := Z × d)).2.1
    (fun j : Z × κ => writer j.1 ⊗ₖ oldKraus j.1 j.2)

/-- Clause (C3): the generated all-future quotient is a right congruence,
has unique descended updates and Reads, and is the unique surjective target of
every finite future-sufficient persistent record. -/
theorem future_minimality
    {A R D V : Type*} (M : WordRecordMachine A R D V) :
    M.MinimalRecordExact :=
  M.minimal_record_exact

/-- Clause (C4), old-history part: relation forgetting embeds the complete
old finite history algebra as a unital injective star subalgebra. -/
theorem old_history_algebra_survives
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    [DecidableEq r] [Nonempty r] :
    (∀ (A : Matrix d d ℂ) (W : Matrix r r ℂ),
      W.trace = 1 →
      partialTraceRight (dA := d) (dK := r) (A ⊗ₖ W) = A)
    ∧ (∀ a b : Matrix d d ℂ,
        (a * b) ⊗ₖ (1 : Matrix r r ℂ) =
          (a ⊗ₖ (1 : Matrix r r ℂ)) *
            (b ⊗ₖ (1 : Matrix r r ℂ)))
    ∧ ((1 : Matrix d d ℂ) ⊗ₖ (1 : Matrix r r ℂ) =
        (1 : Matrix (d × r) (d × r) ℂ))
    ∧ (∀ a : Matrix d d ℂ,
        aᴴ ⊗ₖ (1 : Matrix r r ℂ) =
          (a ⊗ₖ (1 : Matrix r r ℂ))ᴴ)
    ∧ (∀ a b : Matrix d d ℂ,
        a ⊗ₖ (1 : Matrix r r ℂ) = b ⊗ₖ (1 : Matrix r r ℂ) →
        a = b) :=
  sm_completion_conservative (d := d) (r := r)

/-- Clause (C4), word-Gram part: every old word Gram is the compression of
the relationally completed word Gram along the canonical inclusion. -/
theorem old_wordGram_is_compression
    {wOld wRel m : Type*} [Fintype wRel] [Fintype m]
    (VRel : Matrix m wRel ℂ) (includeOld : Matrix wRel wOld ℂ) :
    (VRel * includeOld)ᴴ * (VRel * includeOld) =
      includeOldᴴ * (VRelᴴ * VRel) * includeOld :=
  operationalCompletion_physicalWordGram_transport VRel includeOld

/-- Clause (C5): the single joint event law yields the two within-source
blocks and their mixed block, and common nuisance projection is exactly the
simultaneous Moore--Penrose/Anderson--Trapp short. -/
theorem joint_covariance_and_simultaneous_short
    {h e f n : ℕ}
    (A : Matrix (Fin h) (Fin e) ℂ)
    (S : Matrix (Fin h) (Fin f) ℂ)
    (N : Matrix (Fin h) (Fin n) ℂ) :
    ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N A =
      Aᴴ * A - (Nᴴ * A)ᴴ * sourceGramPseudoinverse N * (Nᴴ * A)) ∧
    ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N S =
      Sᴴ * S - (Nᴴ * S)ᴴ * sourceGramPseudoinverse N * (Nᴴ * S)) ∧
    ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N S =
      Aᴴ * S - (Nᴴ * A)ᴴ * sourceGramPseudoinverse N * (Nᴴ * S)) ∧
    (Matrix.fromBlocks
      ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N A)
      ((nuisanceShortedSource N A)ᴴ * nuisanceShortedSource N S)
      ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N A)
      ((nuisanceShortedSource N S)ᴴ * nuisanceShortedSource N S)).PosSemidef :=
  simultaneous_nuisance_short_exact A S N

/-- Final uniqueness clause: equal complete source Grams determine the unique
source-fixing, inner-product-preserving unitary between minimal source ranges. -/
theorem source_fixing_unitary_unique
    {h h' e : Type*} [Fintype h] [Fintype h'] [Fintype e]
    (S : Matrix h e ℂ) (T : Matrix h' e ℂ)
    (hGram : Sᴴ * S = Tᴴ * T) :
    ∃! U : LinearMap.range S.mulVecLin ≃ₗ[ℂ]
      LinearMap.range T.mulVecLin,
      (∀ u : e → ℂ,
        U (S.mulVecLin.rangeRestrict u) = T.mulVecLin.rangeRestrict u)
      ∧ (∀ x y : LinearMap.range S.mulVecLin,
        star (x : h → ℂ) ⬝ᵥ (y : h → ℂ) =
          star (U x : h' → ℂ) ⬝ᵥ (U y : h' → ℂ)) :=
  joint_source_unique_range_unitary S T hGram

end NCG.RelationalCompletion
