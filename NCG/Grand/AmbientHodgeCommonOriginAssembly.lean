/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CommonHodgeRecordMapTransport

/-!
# Ambient-Hodge compression and common-origin record transport

This file removes the two disclosed interfaces in
`thm:SM-common-Hodge-Dirac`.  The covariance of the residue Kossakowski Gram
is derived from two orthogonal coordinate systems for the same ambient Hodge
square, rather than assumed.  Intertwining on an algebra-generating record
family is extended to the whole record algebra.  Finally the physical cross
Gram is exhibited and all Schur, unitary, and record defects are proved to
vanish.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace AmbientHodgeCommonOrigin

/-- The positive Gram of a finite ambient Hodge derivation. -/
def hodgeGram {H K : Type*} [Fintype K]
    (D : Matrix K H ℂ) : Matrix H H ℂ := Dᴴ * D

/-- Orthogonal compression of an ambient operator to a finite carrier. -/
def compress {H E : Type*} [Fintype H]
    (I : Matrix H E ℂ) (K : Matrix H H ℂ) : Matrix E E ℂ :=
  Iᴴ * K * I

theorem hodgeGram_posSemidef {H K : Type*} [Fintype H] [Fintype K]
    (D : Matrix K H ℂ) : (hodgeGram D).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self D

theorem compress_posSemidef
    {H E : Type*} [Fintype H] [Fintype E]
    (I : Matrix H E ℂ) {K : Matrix H H ℂ} (hK : K.PosSemidef) :
    (compress I K).PosSemidef := by
  simpa [compress, Matrix.mul_assoc] using hK.conjTranspose_mul_mul_same I

/-- Two coordinate isometries of the same ambient Hodge carrier give the
conjugation identity `K_res = J K_occ J*`. -/
theorem ambient_compressions_conjugate
    {H occ res : Type*}
    [Fintype H] [Fintype occ] [Fintype res]
    [DecidableEq occ] [DecidableEq res]
    (Iocc : Matrix H occ ℂ) (Ires : Matrix H res ℂ)
    (J : Matrix res occ ℂ)
    (hI : Iocc = Ires * J)
    (hJr : J * Jᴴ = 1)
    (K : Matrix H H ℂ) :
    compress Ires K = J * compress Iocc K * Jᴴ := by
  symm
  calc
    J * compress Iocc K * Jᴴ
        = J * (Jᴴ * Iresᴴ * K * (Ires * J)) * Jᴴ := by
            rw [compress, hI, Matrix.conjTranspose_mul]
    _ = (J * Jᴴ) * Iresᴴ * K * Ires * (J * Jᴴ) := by
          simp only [Matrix.mul_assoc]
    _ = compress Ires K := by
          rw [hJr]
          simp [compress]

/-- Intertwining on an algebra-generating family extends to every represented
record.  The generating set is allowed to contain adjoints, so ordinary
`Algebra.adjoin` is exactly the finite `*`-closed generating packet used in
the manuscript. -/
theorem generator_intertwining_extends
    {R occ res : Type*} [Semiring R] [Algebra ℂ R]
    [Fintype occ] [Fintype res] [DecidableEq occ] [DecidableEq res]
    (πocc : R →ₐ[ℂ] Matrix occ occ ℂ)
    (πres : R →ₐ[ℂ] Matrix res res ℂ)
    (J : Matrix res occ ℂ)
    (S : Set R) (hgen : Algebra.adjoin ℂ S = ⊤)
    (hS : ∀ c ∈ S, J * πocc c = πres c * J) :
    ∀ c, J * πocc c = πres c * J := by
  intro c
  have hc : c ∈ Algebra.adjoin ℂ S := by
    rw [hgen]
    trivial
  induction hc using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap r =>
      ext i j
      simp [Matrix.mul_apply, algebraMap_matrix_apply, mul_comm]
  | add x y _ _ hx hy =>
      simpa only [map_add, Matrix.mul_add, Matrix.add_mul] using congrArg₂ (· + ·) hx hy
  | mul x y _ _ hx hy =>
      rw [map_mul, map_mul]
      calc
        J * (πocc x * πocc y) = (J * πocc x) * πocc y :=
          (Matrix.mul_assoc _ _ _).symm
        _ = (πres x * J) * πocc y := congrArg (fun Z => Z * πocc y) hx
        _ = πres x * (J * πocc y) := Matrix.mul_assoc _ _ _
        _ = πres x * (πres y * J) := congrArg (fun Z => πres x * Z) hy
        _ = (πres x * πres y) * J := (Matrix.mul_assoc _ _ _).symm

/-- The direct record-constrained common-origin residual: one cross Gram,
the Hodge Schur defect, two unitary defects, and all record commutators. -/
def CommonOriginResidual
    {R occ res : Type*} [Semiring R] [Algebra ℂ R]
    [Fintype occ] [Fintype res] [DecidableEq occ] [DecidableEq res]
    (πocc : R →ₐ[ℂ] Matrix occ occ ℂ)
    (πres : R →ₐ[ℂ] Matrix res res ℂ)
    (J : Matrix res occ ℂ)
    (Kocc : Matrix occ occ ℂ) (Kres : Matrix res res ℂ)
    (X : Matrix occ res ℂ) : Prop :=
  X = Kocc * Jᴴ ∧
  Kres - J * Kocc * Jᴴ = 0 ∧
  Jᴴ * J - 1 = 0 ∧ J * Jᴴ - 1 = 0 ∧
  ∀ c, J * πocc c - πres c * J = 0

/-- Complete common-Hodge finite-Dirac branch.  Every conclusion is derived
from a single ambient Hodge map, compatible coordinate isometries, and a
generating record family. -/
theorem common_hodge_finite_dirac_from_ambient
    {R H K occ res : Type*}
    [Semiring R] [StarRing R] [Algebra ℂ R]
    [Fintype H] [DecidableEq H] [Fintype K]
    [Fintype occ] [DecidableEq occ]
    [Fintype res] [DecidableEq res]
    (D : Matrix K H ℂ)
    (Iocc : Matrix H occ ℂ) (Ires : Matrix H res ℂ)
    (J : Matrix res occ ℂ)
    (hI : Iocc = Ires * J)
    (hJl : Jᴴ * J = 1) (hJr : J * Jᴴ = 1)
    (πocc : R →⋆ₐ[ℂ] Matrix occ occ ℂ)
    (πres : R →⋆ₐ[ℂ] Matrix res res ℂ)
    (S : Set R) (hgen : Algebra.adjoin ℂ S = ⊤)
    (hS : ∀ c ∈ S, J * πocc c = πres c * J) :
    let Kocc := compress Iocc (hodgeGram D)
    let Kres := compress Ires (hodgeGram D)
    Kres = J * Kocc * Jᴴ ∧
    CFC.sqrt Kres = J * CFC.sqrt Kocc * Jᴴ ∧
    (∀ c,
      CFC.sqrt Kres * πres c * CFC.sqrt Kres =
        J * (CFC.sqrt Kocc * πocc c * CFC.sqrt Kocc) * Jᴴ) ∧
    Submodule.map J.mulVecLin
        (protectedRecordCyclicHull πocc (CFC.sqrt Kocc)) =
      protectedRecordCyclicHull πres (CFC.sqrt Kres) ∧
    ∃ X : Matrix occ res ℂ,
      CommonOriginResidual πocc.toAlgHom πres.toAlgHom J Kocc Kres X := by
  dsimp only
  let Kocc := compress Iocc (hodgeGram D)
  let Kres := compress Ires (hodgeGram D)
  have hK : Kres = J * Kocc * Jᴴ :=
    ambient_compressions_conjugate Iocc Ires J hI hJr (hodgeGram D)
  have hKocc : Kocc.PosSemidef :=
    compress_posSemidef Iocc (hodgeGram_posSemidef D)
  have hπ : ∀ c, J * πocc c = πres c * J :=
    generator_intertwining_extends (R := R)
      πocc.toAlgHom πres.toAlgHom J S hgen hS
  have hπconj : ∀ c, πres c = J * πocc c * Jᴴ := by
    intro c
    calc
      πres c = πres c * (J * Jᴴ) := by rw [hJr, Matrix.mul_one]
      _ = (πres c * J) * Jᴴ := by rw [Matrix.mul_assoc]
      _ = J * πocc c * Jᴴ := by rw [hπ c]
  obtain ⟨hsqrt, htheta, hhull⟩ :=
    commonHodgeRecordMap_exact πocc πres J hJl hJr Kocc Kres hKocc hK hπconj
  refine ⟨hK, hsqrt, htheta, hhull, Kocc * Jᴴ, ?_⟩
  refine ⟨rfl, sub_eq_zero.mpr hK, sub_eq_zero.mpr hJl,
    sub_eq_zero.mpr hJr, ?_⟩
  intro c
  exact sub_eq_zero.mpr (hπ c)

end AmbientHodgeCommonOrigin
end NCG
