/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteUnitaryPeterWeyl
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.TransferInstance

/-!
# Hilbert carriers for finite Peter--Weyl blocks

The Artin--Wedderburn matrices are algebraically irreducible.  This module
puts each block on a distinct carrier whose Hilbert structure is induced by
the explicit group-averaged Hermitian form.  Thus the matrices act by genuine
linear isometries without conflicting with the standard coordinate norm.
-/

namespace NCG.FinitePeterWeyl

variable {G : Type*} [Group G] [Fintype G]

/-- A type-distinct copy of one irreducible Artin--Wedderburn block. -/
structure UnitaryBlockCarrier (D : MatrixBlockDecomposition G)
    (i : Fin D.count) where
  coord : Fin (D.dimension i) → ℂ
/-- The underlying coordinate equivalence used to transport the algebraic
vector-space structure. -/
@[ext]
theorem UnitaryBlockCarrier.ext
    {D : MatrixBlockDecomposition G} {i : Fin D.count}
    {x y : UnitaryBlockCarrier D i} (h : x.coord = y.coord) : x = y := by
  cases x
  cases y
  simp_all

def unitaryBlockEquiv (D : MatrixBlockDecomposition G)
    (i : Fin D.count) :
    UnitaryBlockCarrier D i ≃ (Fin (D.dimension i) → ℂ) where
  toFun := UnitaryBlockCarrier.coord
  invFun := UnitaryBlockCarrier.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance unitaryBlockAddCommGroup (D : MatrixBlockDecomposition G)
    (i : Fin D.count) : AddCommGroup (UnitaryBlockCarrier D i) :=
  (unitaryBlockEquiv D i).addCommGroup

instance unitaryBlockModule (D : MatrixBlockDecomposition G)
    (i : Fin D.count) : Module ℂ (UnitaryBlockCarrier D i) :=
  (unitaryBlockEquiv D i).module ℂ

/-- Coordinate identification of the wrapped block with its matrix carrier. -/
def unitaryBlockCoordEquiv (D : MatrixBlockDecomposition G)
    (i : Fin D.count) :
    UnitaryBlockCarrier D i ≃ₗ[ℂ] (Fin (D.dimension i) → ℂ) :=
  (unitaryBlockEquiv D i).linearEquiv ℂ

/-- The averaged Hermitian form transported to the type-distinct carrier. -/
@[instance_reducible] noncomputable def unitaryBlockInnerProductCore
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    InnerProductSpace.Core ℂ (UnitaryBlockCarrier D i) where
  inner x y := blockAveragedInner D i x.coord y.coord
  conj_inner_symm x y :=
    (blockAveragedInner_conj_symm D i x.coord y.coord).symm
  re_inner_nonneg x := by
    rw [blockAveragedInner_self]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact blockAveragedNormSq_nonneg D i x.coord
  add_left x y z := by
    change blockAveragedInner D i (x.coord + y.coord) z.coord =
      blockAveragedInner D i x.coord z.coord +
        blockAveragedInner D i y.coord z.coord
    calc
      blockAveragedInner D i (x.coord + y.coord) z.coord =
          star (blockAveragedInner D i z.coord (x.coord + y.coord)) :=
        blockAveragedInner_conj_symm D i (x.coord + y.coord) z.coord
      _ = star (blockAveragedInner D i z.coord x.coord +
          blockAveragedInner D i z.coord y.coord) := by
        rw [blockAveragedInner_add_right]
      _ = star (blockAveragedInner D i z.coord x.coord) +
          star (blockAveragedInner D i z.coord y.coord) := by simp
      _ = blockAveragedInner D i x.coord z.coord +
          blockAveragedInner D i y.coord z.coord := by
        rw [← blockAveragedInner_conj_symm D i x.coord z.coord,
          ← blockAveragedInner_conj_symm D i y.coord z.coord]
  smul_left x y c := by
    change blockAveragedInner D i (c • x.coord) y.coord =
      star c * blockAveragedInner D i x.coord y.coord
    calc
      blockAveragedInner D i (c • x.coord) y.coord =
          star (blockAveragedInner D i y.coord (c • x.coord)) :=
        blockAveragedInner_conj_symm D i (c • x.coord) y.coord
      _ = star (c * blockAveragedInner D i y.coord x.coord) := by
        rw [blockAveragedInner_smul_right]
      _ = star c * star (blockAveragedInner D i y.coord x.coord) := by simp
      _ = star c * blockAveragedInner D i x.coord y.coord := by
        rw [← blockAveragedInner_conj_symm D i x.coord y.coord]
  definite x hx := by
    apply UnitaryBlockCarrier.ext
    have hcoord :
        blockAveragedInner D i x.coord x.coord = 0 := hx
    have hz := (blockAveragedInner_self_eq_zero_iff D i x.coord).mp hcoord
    change x.coord = 0
    exact hz
noncomputable instance unitaryBlockCore
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    InnerProductSpace.Core ℂ (UnitaryBlockCarrier D i) :=
  unitaryBlockInnerProductCore D i

noncomputable instance unitaryBlockNormedAddCommGroup
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    NormedAddCommGroup (UnitaryBlockCarrier D i) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ
    (UnitaryBlockCarrier D i) _ _ _ (unitaryBlockInnerProductCore D i)

noncomputable instance unitaryBlockInnerProductSpace
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    InnerProductSpace ℂ (UnitaryBlockCarrier D i) :=
  @InnerProductSpace.ofCore ℂ (UnitaryBlockCarrier D i) _ _ _
    (inferInstance : PreInnerProductSpace.Core ℂ (UnitaryBlockCarrier D i))


theorem unitaryBlock_inner_apply
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (x y : UnitaryBlockCarrier D i) :
    inner ℂ x y = blockAveragedInner D i x.coord y.coord := rfl

/-- The defining block action on its averaged Hilbert carrier. -/
noncomputable def unitaryBlockAction (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (h : G) :
    UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D i :=
  (unitaryBlockCoordEquiv D i).symm.toLinearMap.comp
    ((blockMatrix D i h).mulVecLin.comp
      (unitaryBlockCoordEquiv D i).toLinearMap)

@[simp]
theorem unitaryBlockAction_coord (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (h : G) (x : UnitaryBlockCarrier D i) :
    (unitaryBlockAction D i h x).coord =
      (blockMatrix D i h).mulVec x.coord := rfl

theorem unitaryBlockAction_inner (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (h : G) (x y : UnitaryBlockCarrier D i) :
    inner ℂ (unitaryBlockAction D i h x) (unitaryBlockAction D i h y) =
      inner ℂ x y := by
  simp only [unitaryBlock_inner_apply, unitaryBlockAction_coord]
  exact blockAveragedInner_invariant D i h x.coord y.coord

/-- Every defining block matrix is a genuine linear isometry for the averaged
Hilbert structure. -/
noncomputable def unitaryBlockActionIsometry
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (h : G) :
    UnitaryBlockCarrier D i →ₗᵢ[ℂ] UnitaryBlockCarrier D i :=
  (unitaryBlockAction D i h).isometryOfInner
    (unitaryBlockAction_inner D i h)

@[simp]
theorem unitaryBlockAction_one (D : MatrixBlockDecomposition G)
    (i : Fin D.count) :
    unitaryBlockAction D i (1 : G) = LinearMap.id := by
  ext x
  simp [unitaryBlockAction_coord, blockMatrix_one]

@[simp]
theorem unitaryBlockAction_mul (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (g h : G) :
    unitaryBlockAction D i (g * h) =
      (unitaryBlockAction D i g).comp (unitaryBlockAction D i h) := by
  ext x
  simp [unitaryBlockAction_coord, Matrix.mulVec_mulVec, blockMatrix_mul]
noncomputable instance unitaryBlockFiniteDimensional
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    FiniteDimensional ℂ (UnitaryBlockCarrier D i) :=
  FiniteDimensional.of_injective (unitaryBlockCoordEquiv D i).toLinearMap
    (unitaryBlockCoordEquiv D i).injective

theorem unitaryBlock_finrank (D : MatrixBlockDecomposition G)
    (i : Fin D.count) :
    Module.finrank ℂ (UnitaryBlockCarrier D i) = D.dimension i := by
  calc
    Module.finrank ℂ (UnitaryBlockCarrier D i) =
        Module.finrank ℂ (Fin (D.dimension i) → ℂ) :=
      LinearEquiv.finrank_eq (unitaryBlockCoordEquiv D i)
    _ = D.dimension i := by simp

/-- An orthonormal basis indexed by the declared irreducible dimension. -/
noncomputable def unitaryBlockOrthonormalBasis
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    OrthonormalBasis (Fin (D.dimension i)) ℂ (UnitaryBlockCarrier D i) :=
  (stdOrthonormalBasis ℂ (UnitaryBlockCarrier D i)).reindex
    (finCongr (unitaryBlock_finrank D i))

/-- Matrix of the unitary block action in its averaged orthonormal basis. -/
noncomputable def normalizedBlockMatrix
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (g : G) :
    Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ :=
  LinearMap.toMatrix (unitaryBlockOrthonormalBasis D i).toBasis
    (unitaryBlockOrthonormalBasis D i).toBasis (unitaryBlockAction D i g)

@[simp]
theorem normalizedBlockMatrix_one
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    normalizedBlockMatrix D i (1 : G) = 1 := by
  rw [normalizedBlockMatrix, unitaryBlockAction_one,
    LinearMap.toMatrix_id]

@[simp]
theorem normalizedBlockMatrix_mul
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (g h : G) :
    normalizedBlockMatrix D i (g * h) =
      normalizedBlockMatrix D i g * normalizedBlockMatrix D i h := by
  classical
  rw [normalizedBlockMatrix, unitaryBlockAction_mul]
  exact LinearMap.toMatrix_comp
    (unitaryBlockOrthonormalBasis D i).toBasis
    (unitaryBlockOrthonormalBasis D i).toBasis
    (unitaryBlockOrthonormalBasis D i).toBasis _ _
theorem unitaryBlockAction_surjective
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (h : G) :
    Function.Surjective (unitaryBlockActionIsometry D i h) := by
  intro x
  refine ⟨unitaryBlockAction D i h⁻¹ x, ?_⟩
  apply UnitaryBlockCarrier.ext
  simp [unitaryBlockActionIsometry, unitaryBlockAction_coord,
    Matrix.mulVec_mulVec, ← blockMatrix_mul]

/-- The block action is a unitary linear equivalence, with inverse supplied by
the inverse group element. -/
noncomputable def unitaryBlockActionEquiv
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (h : G) :
    UnitaryBlockCarrier D i ≃ₗᵢ[ℂ] UnitaryBlockCarrier D i :=
  LinearIsometryEquiv.ofSurjective (unitaryBlockActionIsometry D i h)
    (unitaryBlockAction_surjective D i h)

/-- In the averaged orthonormal basis, every normalized block matrix is
unitary in the standard matrix sense. -/
theorem normalizedBlockMatrix_mem_unitary
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (h : G) :
    normalizedBlockMatrix D i h ∈
      Matrix.unitaryGroup (Fin (D.dimension i)) ℂ := by
  have hmap : (unitaryBlockActionEquiv D i h).toLinearMap =
      unitaryBlockAction D i h := by
    ext x
    rfl
  rw [normalizedBlockMatrix, ← hmap]
  exact (unitaryBlockActionEquiv D i h).toMatrix_mem_unitaryGroup
    (unitaryBlockOrthonormalBasis D i)
    (unitaryBlockOrthonormalBasis D i)
theorem normalizedBlockMatrix_mul_star
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (h : G) :
    normalizedBlockMatrix D i h * star (normalizedBlockMatrix D i h) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (normalizedBlockMatrix_mem_unitary D i h)

theorem normalizedBlockMatrix_star_mul
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (h : G) :
    star (normalizedBlockMatrix D i h) * normalizedBlockMatrix D i h = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (normalizedBlockMatrix_mem_unitary D i h)

@[simp]
theorem normalizedBlockMatrix_inv_eq_star
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (h : G) :
    normalizedBlockMatrix D i h⁻¹ = star (normalizedBlockMatrix D i h) := by
  calc
    normalizedBlockMatrix D i h⁻¹ =
        normalizedBlockMatrix D i h⁻¹ * 1 := by rw [mul_one]
    _ = normalizedBlockMatrix D i h⁻¹ *
        (normalizedBlockMatrix D i h * star (normalizedBlockMatrix D i h)) := by
      rw [normalizedBlockMatrix_mul_star]
    _ = (normalizedBlockMatrix D i h⁻¹ * normalizedBlockMatrix D i h) *
        star (normalizedBlockMatrix D i h) := by rw [Matrix.mul_assoc]
    _ = star (normalizedBlockMatrix D i h) := by
      rw [← normalizedBlockMatrix_mul, inv_mul_cancel, normalizedBlockMatrix_one,
        one_mul]

theorem normalizedBlockMatrix_endpoint
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (ht g hs : G) :
    normalizedBlockMatrix D i (ht * g * hs⁻¹) =
      normalizedBlockMatrix D i ht * normalizedBlockMatrix D i g *
        star (normalizedBlockMatrix D i hs) := by
  rw [normalizedBlockMatrix_mul, normalizedBlockMatrix_mul,
    normalizedBlockMatrix_inv_eq_star]
theorem normalizedBlockMatrix_endpoint_apply
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (ht g hs : G) (row col : Fin (D.dimension i)) :
    normalizedBlockMatrix D i (ht * g * hs⁻¹) row col =
      ∑ q : Fin (D.dimension i), ∑ p : Fin (D.dimension i),
        normalizedBlockMatrix D i ht row p *
          normalizedBlockMatrix D i g p q *
          normalizedBlockMatrix D i hs⁻¹ q col := by
  rw [normalizedBlockMatrix_mul, normalizedBlockMatrix_mul,
    Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [Matrix.mul_apply]
  rw [Finset.sum_mul]
end NCG.FinitePeterWeyl
