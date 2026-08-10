/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CombDilation
import NCG.Grand.OccurrenceChoiSource
import NCG.Grand.JointSourceRangeUnitary

/-!
# Canonical prefix purifications and their unique memory gauge

For a positive finite Choi prefix `J`, the canonical purification factor is
`sqrt J` and its memory is the range of that factor.  This module proves that
the memory has dimension `rank J` and that every other factor of the same Gram
is related to it by the unique source-fixing, inner-product-preserving linear
equivalence.  This is the minimal-purification uniqueness step used in the
comb-to-memory induction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- Canonical square-root factor of a positive Choi prefix. -/
noncomputable def canonicalPrefixFactor {d : Type*} [Fintype d] [DecidableEq d]
    (J : Matrix d d ℂ) : Matrix d d ℂ :=
  CFC.sqrt J

/-- The support-minimal memory carried by a positive Choi prefix. -/
noncomputable abbrev CanonicalPrefixMemory {d : Type*} [Fintype d] [DecidableEq d]
    (J : Matrix d d ℂ) : Submodule ℂ (d → ℂ) :=
  LinearMap.range (canonicalPrefixFactor J).mulVecLin

/-- The canonical prefix factor has Gram exactly `J`. -/
theorem canonicalPrefixFactor_gram {d : Type*} [Fintype d] [DecidableEq d]
    (J : Matrix d d ℂ) (hJ : J.PosSemidef) :
    (canonicalPrefixFactor J)ᴴ * canonicalPrefixFactor J = J := by
  rw [canonicalPrefixFactor, sqrt_isHermitian, sqrt_mul_self_eq J hJ]

/-- The canonical memory dimension is exactly the Choi support rank. -/
theorem canonicalPrefixMemory_finrank {d : Type*} [Fintype d] [DecidableEq d]
    (J : Matrix d d ℂ) (hJ : J.PosSemidef) :
    Module.finrank ℂ (CanonicalPrefixMemory J) = J.rank := by
  change (canonicalPrefixFactor J).rank = J.rank
  calc
    (canonicalPrefixFactor J).rank
        = ((canonicalPrefixFactor J)ᴴ * canonicalPrefixFactor J).rank :=
          (Matrix.rank_conjTranspose_mul_self (canonicalPrefixFactor J)).symm
    _ = J.rank := congrArg Matrix.rank (canonicalPrefixFactor_gram J hJ)

/-- Existence package for the canonical support-minimal prefix dilation: the
chosen factor has terminal Gram `J` and its range memory has minimal dimension
`rank J`. -/
theorem canonicalPrefixDilation_exists
    {d : Type*} [Fintype d] [DecidableEq d]
    (J : Matrix d d ℂ) (hJ : J.PosSemidef) :
    ∃ S : Matrix d d ℂ,
      Sᴴ * S = J
      ∧ Module.finrank ℂ (LinearMap.range S.mulVecLin) = J.rank := by
  refine ⟨canonicalPrefixFactor J, canonicalPrefixFactor_gram J hJ, ?_⟩
  exact canonicalPrefixMemory_finrank J hJ

/-- Minimal-purification uniqueness: any factor of the same positive prefix
Gram is linked to the canonical square-root memory by a unique source-fixing
inner-product-preserving equivalence. -/
theorem canonicalPrefixPurification_unique
    {d h : Type*} [Fintype d] [Fintype h] [DecidableEq d]
    (J : Matrix d d ℂ) (hJ : J.PosSemidef) (T : Matrix h d ℂ)
    (hT : Tᴴ * T = J) :
    ∃! U : CanonicalPrefixMemory J ≃ₗ[ℂ] LinearMap.range T.mulVecLin,
      (∀ u : d → ℂ,
        U ((canonicalPrefixFactor J).mulVecLin.rangeRestrict u)
          = T.mulVecLin.rangeRestrict u)
      ∧ (∀ x y : CanonicalPrefixMemory J,
        star (x : d → ℂ) ⬝ᵥ (y : d → ℂ)
          = star (U x : h → ℂ) ⬝ᵥ (U y : h → ℂ)) := by
  apply joint_source_unique_range_unitary (canonicalPrefixFactor J) T
  exact (canonicalPrefixFactor_gram J hJ).trans hT.symm

/-- Two support-minimal factors of a prefix Gram carry canonically equivalent
memories; the equivalence is unique on all generated source vectors. -/
theorem supportMinimalPrefixMemories_unique
    {d h h' : Type*} [Fintype d] [Fintype h] [Fintype h']
    (S : Matrix h d ℂ) (T : Matrix h' d ℂ)
    (hGram : Sᴴ * S = Tᴴ * T) :
    ∃! U : LinearMap.range S.mulVecLin ≃ₗ[ℂ]
        LinearMap.range T.mulVecLin,
      (∀ u : d → ℂ,
        U (S.mulVecLin.rangeRestrict u) = T.mulVecLin.rangeRestrict u)
      ∧ (∀ x y : LinearMap.range S.mulVecLin,
        star (x : h → ℂ) ⬝ᵥ (y : h → ℂ)
          = star (U x : h' → ℂ) ⬝ᵥ (U y : h' → ℂ)) :=
  joint_source_unique_range_unitary S T hGram

end NCG
