/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandResetAudit
import NCG.Grand.SqrtPolar
import NCG.Grand.ProtectedRecordMapStinespringHull

/-!
# Common-Hodge transport of protected record maps

This file completes the functional-calculus and minimal-factor clauses of
`thm:SM-common-Hodge-Dirac`.  A two-sided unitary equivalence transports the
positive matrix square root, hence transports the protected record map by
conjugation.  Pointwise-intertwining record representations also carry the
canonical cyclic Stinespring hull exactly onto the residue hull.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- Conjugation by a two-sided finite unitary preserves multiplication. -/
theorem twoSidedUnitary_conjugation_mul
    {occ res : Type*} [Fintype occ] [DecidableEq occ]
    [Fintype res] [DecidableEq res]
    (J : Matrix res occ ℂ) (hJl : Jᴴ * J = 1)
    (A B : Matrix occ occ ℂ) :
    (J * A * Jᴴ) * (J * B * Jᴴ) = J * (A * B) * Jᴴ := by
  calc
    (J * A * Jᴴ) * (J * B * Jᴴ)
        = J * A * (Jᴴ * J) * B * Jᴴ := by
            simp only [Matrix.mul_assoc]
    _ = J * (A * B) * Jᴴ := by rw [hJl]; simp only [Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]

/-- The same conjugation intertwines the natural action on vectors. -/
theorem twoSidedUnitary_conjugation_mulVec
    {occ res : Type*} [Fintype occ] [DecidableEq occ]
    [Fintype res] [DecidableEq res]
    (J : Matrix res occ ℂ) (hJl : Jᴴ * J = 1)
    (A : Matrix occ occ ℂ) (x : occ → ℂ) :
    (J * A * Jᴴ) *ᵥ (J *ᵥ x) = J *ᵥ (A *ᵥ x) := by
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hJl, Matrix.mul_one]

/-- Positive square roots commute with a two-sided unitary change of finite
carrier. -/
theorem positiveSquareRoot_unitaryTransport
    {occ res : Type*} [Fintype occ] [DecidableEq occ]
    [Fintype res] [DecidableEq res]
    (J : Matrix res occ ℂ) (hJl : Jᴴ * J = 1) (hJr : J * Jᴴ = 1)
    (Kocc : Matrix occ occ ℂ) (Kres : Matrix res res ℂ)
    (hKocc : Kocc.PosSemidef) (hK : Kres = J * Kocc * Jᴴ) :
    CFC.sqrt Kres = J * CFC.sqrt Kocc * Jᴴ := by
  let B : Matrix res res ℂ := J * CFC.sqrt Kocc * Jᴴ
  have hB : B.PosSemidef := by
    simpa [B, Matrix.conjTranspose_conjTranspose] using
      (sqrt_posSemidef Kocc).conjTranspose_mul_mul_same Jᴴ
  have hBsq : B * B = Kres := by
    dsimp [B]
    calc
      (J * CFC.sqrt Kocc * Jᴴ) * (J * CFC.sqrt Kocc * Jᴴ)
          = J * (CFC.sqrt Kocc * CFC.sqrt Kocc) * Jᴴ := by
              rw [show (J * CFC.sqrt Kocc * Jᴴ) *
                    (J * CFC.sqrt Kocc * Jᴴ) =
                    J * CFC.sqrt Kocc * (Jᴴ * J) *
                      CFC.sqrt Kocc * Jᴴ by
                  simp only [Matrix.mul_assoc], hJl]
              simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = J * Kocc * Jᴴ := by rw [sqrt_mul_self_eq Kocc hKocc]
      _ = Kres := hK.symm
  exact sqrt_unique' hB hBsq

/-- Transport of the positive root and of the represented record coefficient
implies exact conjugation transport of the one-matrix protected record map. -/
theorem commonHodge_protectedRecordMap_transport
    {occ res : Type*} [Fintype occ] [DecidableEq occ]
    [Fintype res] [DecidableEq res]
    (J : Matrix res occ ℂ) (hJl : Jᴴ * J = 1) (hJr : J * Jᴴ = 1)
    (Kocc : Matrix occ occ ℂ) (Kres : Matrix res res ℂ)
    (Cocc : Matrix occ occ ℂ) (Cres : Matrix res res ℂ)
    (hKocc : Kocc.PosSemidef) (hK : Kres = J * Kocc * Jᴴ)
    (hC : Cres = J * Cocc * Jᴴ) :
    CFC.sqrt Kres * Cres * CFC.sqrt Kres =
      J * (CFC.sqrt Kocc * Cocc * CFC.sqrt Kocc) * Jᴴ := by
  rw [positiveSquareRoot_unitaryTransport J hJl hJr Kocc Kres hKocc hK,
    hC]
  rw [twoSidedUnitary_conjugation_mul J hJl,
    twoSidedUnitary_conjugation_mul J hJl]

/-- A record-intertwining unitary carries cyclic generators exactly onto
cyclic generators. -/
theorem commonHodge_recordCyclicVectors_image
    {R occ res : Type*} [Semiring R] [StarRing R] [Algebra ℂ R]
    [Fintype occ] [DecidableEq occ]
    [Fintype res] [DecidableEq res]
    (πocc : R →⋆ₐ[ℂ] Matrix occ occ ℂ)
    (πres : R →⋆ₐ[ℂ] Matrix res res ℂ)
    (J : Matrix res occ ℂ) (hJl : Jᴴ * J = 1) (hJr : J * Jᴴ = 1)
    (Socc : Matrix occ occ ℂ) (Sres : Matrix res res ℂ)
    (hπ : ∀ c, πres c = J * πocc c * Jᴴ)
    (hS : Sres = J * Socc * Jᴴ) :
    J.mulVecLin '' recordCyclicVectors πocc Socc =
      recordCyclicVectors πres Sres := by
  ext v
  constructor
  · rintro ⟨w, ⟨c, x, rfl⟩, rfl⟩
    refine ⟨c, J *ᵥ x, ?_⟩
    rw [Matrix.mulVecLin_apply, hπ, hS]
    rw [twoSidedUnitary_conjugation_mulVec J hJl,
      twoSidedUnitary_conjugation_mulVec J hJl]
  · rintro ⟨c, y, rfl⟩
    refine ⟨πocc c *ᵥ (Socc *ᵥ (Jᴴ *ᵥ y)), ?_, ?_⟩
    · exact ⟨c, Jᴴ *ᵥ y, rfl⟩
    · rw [Matrix.mulVecLin_apply, hπ, hS]
      simp only [Matrix.mulVec_mulVec]
      rw [twoSidedUnitary_conjugation_mul J hJl]
      simp only [Matrix.mul_assoc]

/-- The common-Hodge unitary identifies the occurrence and residue minimal
record-sufficient Stinespring spaces. -/
theorem commonHodge_recordCyclicHull_transport
    {R occ res : Type*} [Semiring R] [StarRing R] [Algebra ℂ R]
    [Fintype occ] [DecidableEq occ]
    [Fintype res] [DecidableEq res]
    (πocc : R →⋆ₐ[ℂ] Matrix occ occ ℂ)
    (πres : R →⋆ₐ[ℂ] Matrix res res ℂ)
    (J : Matrix res occ ℂ) (hJl : Jᴴ * J = 1) (hJr : J * Jᴴ = 1)
    (Socc : Matrix occ occ ℂ) (Sres : Matrix res res ℂ)
    (hπ : ∀ c, πres c = J * πocc c * Jᴴ)
    (hS : Sres = J * Socc * Jᴴ) :
    Submodule.map J.mulVecLin (protectedRecordCyclicHull πocc Socc) =
      protectedRecordCyclicHull πres Sres := by
  rw [protectedRecordCyclicHull, protectedRecordCyclicHull,
    Submodule.map_span,
    commonHodge_recordCyclicVectors_image πocc πres J hJl hJr Socc Sres hπ hS]

/-- Exact common-Hodge record-map packet: vanishing generator residual gives
conjugation transport on generators, positive functional calculus transports
the Kossakowski root, the record maps agree, and their unique minimal cyclic
factors are identified by the same unitary. -/
theorem commonHodgeRecordMap_exact
    {R occ res : Type*} [Semiring R] [StarRing R] [Algebra ℂ R]
    [Fintype occ] [DecidableEq occ]
    [Fintype res] [DecidableEq res]
    (πocc : R →⋆ₐ[ℂ] Matrix occ occ ℂ)
    (πres : R →⋆ₐ[ℂ] Matrix res res ℂ)
    (J : Matrix res occ ℂ) (hJl : Jᴴ * J = 1) (hJr : J * Jᴴ = 1)
    (Kocc : Matrix occ occ ℂ) (Kres : Matrix res res ℂ)
    (hKocc : Kocc.PosSemidef) (hK : Kres = J * Kocc * Jᴴ)
    (hπ : ∀ c, πres c = J * πocc c * Jᴴ) :
    CFC.sqrt Kres = J * CFC.sqrt Kocc * Jᴴ
    ∧ (∀ c,
        CFC.sqrt Kres * πres c * CFC.sqrt Kres =
          J * (CFC.sqrt Kocc * πocc c * CFC.sqrt Kocc) * Jᴴ)
    ∧ Submodule.map J.mulVecLin
          (protectedRecordCyclicHull πocc (CFC.sqrt Kocc)) =
        protectedRecordCyclicHull πres (CFC.sqrt Kres) := by
  have hsqrt := positiveSquareRoot_unitaryTransport
    J hJl hJr Kocc Kres hKocc hK
  refine ⟨hsqrt, ?_, ?_⟩
  · intro c
    exact commonHodge_protectedRecordMap_transport
      J hJl hJr Kocc Kres (πocc c) (πres c) hKocc hK (hπ c)
  · exact commonHodge_recordCyclicHull_transport
      πocc πres J hJl hJr (CFC.sqrt Kocc) (CFC.sqrt Kres)
      hπ hsqrt

end NCG
