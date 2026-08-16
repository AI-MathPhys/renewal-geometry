/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteUnitaryBlockCarrier
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite Schur orthogonality for normalized Peter--Weyl blocks

This file extends the unitary action of each group element to the full
complex group algebra in the averaged orthonormal block basis.  Surjectivity
onto every full endomorphism algebra and separation of distinct
Artin--Wedderburn blocks provide the algebraic Schur-lemma input for exact
matrix-coefficient orthogonality.
-/

namespace NCG.FinitePeterWeyl

variable {G : Type*} [Group G] [Fintype G]


/-- Evaluation commutes with a finite sum of matrices. -/
theorem matrix_fintype_sum_apply
    {X m n : Type*} [Fintype X]
    (f : X → Matrix m n ℂ) (i : m) (j : n) :
    (∑ x : X, f x) i j = ∑ x : X, f x i j := by
  classical
  change (Finset.univ.sum f) i j = Finset.univ.sum (fun x => f x i j)
  induction (Finset.univ : Finset X) using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => simp [hx, ih]

/-- Action of an arbitrary group-algebra element on the wrapped unitary
carrier of one irreducible block. -/
noncomputable def unitaryBlockAlgebraAction
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (x : RegularCarrier G) :
    UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D i :=
  (unitaryBlockCoordEquiv D i).symm.toLinearMap.comp
    (((blockAlgHom D i x).mulVecLin).comp
      (unitaryBlockCoordEquiv D i).toLinearMap)

/-- Matrix of the full group-algebra action in the averaged orthonormal
basis. -/
noncomputable def normalizedBlockAlgebraMatrix
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (x : RegularCarrier G) :
    Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ :=
  LinearMap.toMatrix (unitaryBlockOrthonormalBasis D i).toBasis
    (unitaryBlockOrthonormalBasis D i).toBasis
    (unitaryBlockAlgebraAction D i x)

@[simp] theorem unitaryBlockAlgebraAction_single
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (g : G) :
    unitaryBlockAlgebraAction D i (MonoidAlgebra.single g 1) =
      unitaryBlockAction D i g := by
  rfl

@[simp] theorem normalizedBlockAlgebraMatrix_single
    (D : MatrixBlockDecomposition G) (i : Fin D.count) (g : G) :
    normalizedBlockAlgebraMatrix D i (MonoidAlgebra.single g 1) =
      normalizedBlockMatrix D i g := by
  rfl

@[simp] theorem unitaryBlockAlgebraAction_zero
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    unitaryBlockAlgebraAction D i 0 = 0 := by
  ext v a
  simp [unitaryBlockAlgebraAction]

@[simp] theorem unitaryBlockAlgebraAction_one
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    unitaryBlockAlgebraAction D i 1 = LinearMap.id := by
  rw [show (1 : RegularCarrier G) = MonoidAlgebra.single 1 1 from
    MonoidAlgebra.one_def]
  simp

@[simp] theorem normalizedBlockAlgebraMatrix_zero
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    normalizedBlockAlgebraMatrix D i 0 = 0 := by
  simp [normalizedBlockAlgebraMatrix]

@[simp] theorem normalizedBlockAlgebraMatrix_one
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    normalizedBlockAlgebraMatrix D i 1 = 1 := by
  rw [normalizedBlockAlgebraMatrix, unitaryBlockAlgebraAction_one]
  exact LinearMap.toMatrix_id
    (unitaryBlockOrthonormalBasis D i).toBasis


/-- Every endomorphism of one unitary block is the action of a suitable
group-algebra element. -/
theorem unitaryBlockAlgebraAction_surjective
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    Function.Surjective (unitaryBlockAlgebraAction D i) := by
  intro T
  let coordinateT : (Fin (D.dimension i) → ℂ) →ₗ[ℂ]
      (Fin (D.dimension i) → ℂ) :=
    (unitaryBlockCoordEquiv D i).toLinearMap.comp
      (T.comp (unitaryBlockCoordEquiv D i).symm.toLinearMap)
  let A : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ :=
    LinearMap.toMatrixAlgEquiv' coordinateT
  obtain ⟨x, hx⟩ := blockAlgHom_surjective D i A
  refine ⟨x, ?_⟩
  apply LinearMap.ext
  intro v
  apply UnitaryBlockCarrier.ext
  change (blockAlgHom D i x).mulVec v.coord = (T v).coord
  rw [hx]
  change (Matrix.toLinAlgEquiv' A) v.coord = coordinateT v.coord
  rw [show Matrix.toLinAlgEquiv' A = coordinateT from
    Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' coordinateT]

/-- A prescribed matrix block, with every other Artin--Wedderburn block
zero, pulled back to the group algebra. -/
noncomputable def isolatedBlockElement
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (A : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ) :
    RegularCarrier G :=
  D.blockEquiv.symm (Function.update 0 i A)

@[simp] theorem blockAlgHom_isolatedBlockElement_same
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (A : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ) :
    blockAlgHom D i (isolatedBlockElement D i A) = A := by
  simp [blockAlgHom, isolatedBlockElement]

@[simp] theorem blockAlgHom_isolatedBlockElement_of_ne
    (D : MatrixBlockDecomposition G) {i j : Fin D.count} (hji : j ≠ i)
    (A : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ) :
    blockAlgHom D j (isolatedBlockElement D i A) = 0 := by
  simp [blockAlgHom, isolatedBlockElement, hji]


/-- The full block action is additive in the group-algebra argument. -/
theorem unitaryBlockAlgebraAction_add
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (x y : RegularCarrier G) :
    unitaryBlockAlgebraAction D i (x + y) =
      unitaryBlockAlgebraAction D i x + unitaryBlockAlgebraAction D i y := by
  ext v a
  simp [unitaryBlockAlgebraAction]

/-- The full block action is complex-linear in the group-algebra argument. -/
theorem unitaryBlockAlgebraAction_smul
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (c : ℂ) (x : RegularCarrier G) :
    unitaryBlockAlgebraAction D i (c • x) =
      c • unitaryBlockAlgebraAction D i x := by
  ext v a
  simp [unitaryBlockAlgebraAction]

/-- An isolated identity block acts identically on its selected carrier. -/
theorem unitaryBlockAlgebraAction_isolated_one_same
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    unitaryBlockAlgebraAction D i (isolatedBlockElement D i 1) =
      LinearMap.id := by
  ext v a
  simp [unitaryBlockAlgebraAction]

/-- An isolated block annihilates every distinct irreducible carrier. -/
theorem unitaryBlockAlgebraAction_isolated_of_ne
    (D : MatrixBlockDecomposition G) {i j : Fin D.count} (hji : j ≠ i)
    (A : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ) :
    unitaryBlockAlgebraAction D j (isolatedBlockElement D i A) = 0 := by
  ext v a
  simp [unitaryBlockAlgebraAction, hji]

/-- A map intertwining every group element intertwines the action of every
complex group-algebra element. -/
theorem intertwines_unitaryBlockAlgebraAction
    (D : MatrixBlockDecomposition G) (i j : Fin D.count)
    (T : UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D j)
    (hT : ∀ g : G,
      T.comp (unitaryBlockAction D i g) =
        (unitaryBlockAction D j g).comp T) :
    ∀ x : RegularCarrier G,
      T.comp (unitaryBlockAlgebraAction D i x) =
        (unitaryBlockAlgebraAction D j x).comp T := by
  intro x
  apply MonoidAlgebra.induction_on x
  · intro g
    simpa using hT g
  · intro x y hx hy
    rw [unitaryBlockAlgebraAction_add, unitaryBlockAlgebraAction_add]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [map_add]
    have hxv := LinearMap.congr_fun hx v
    have hyv := LinearMap.congr_fun hy v
    simp only [LinearMap.comp_apply] at hxv hyv
    rw [hxv, hyv]
  · intro c x hx
    rw [unitaryBlockAlgebraAction_smul, unitaryBlockAlgebraAction_smul]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [map_smul]
    have hxv := LinearMap.congr_fun hx v
    simp only [LinearMap.comp_apply] at hxv
    rw [hxv]

/-- Schur separation: an intertwiner between two distinct
Artin--Wedderburn blocks is zero. -/
theorem unitaryBlockIntertwiner_eq_zero_of_ne
    (D : MatrixBlockDecomposition G) {i j : Fin D.count} (hji : j ≠ i)
    (T : UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D j)
    (hT : ∀ g : G,
      T.comp (unitaryBlockAction D i g) =
        (unitaryBlockAction D j g).comp T) :
    T = 0 := by
  have hz := intertwines_unitaryBlockAlgebraAction D i j T hT
    (isolatedBlockElement D j 1)
  rw [unitaryBlockAlgebraAction_isolated_of_ne D
      (i := j) (j := i) hji.symm,
    unitaryBlockAlgebraAction_isolated_one_same D j] at hz
  simpa using hz.symm


/-- Same-block Schur lemma: every intertwiner of one irreducible unitary
block is a scalar multiple of the identity. -/
theorem unitaryBlockIntertwiner_eq_smul_id
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (T : UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D i)
    (hT : ∀ g : G,
      T.comp (unitaryBlockAction D i g) =
        (unitaryBlockAction D i g).comp T) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  classical
  let b := (unitaryBlockOrthonormalBasis D i).toBasis
  let M := LinearMap.toMatrixAlgEquiv b T
  have hscalar : M ∈ Set.range (Matrix.scalar (Fin (D.dimension i))) := by
    apply Matrix.mem_range_scalar_of_commute_single
    intro p q hpq
    let S : UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D i :=
      (LinearMap.toMatrixAlgEquiv b).symm (Matrix.single p q 1)
    obtain ⟨x, hx⟩ := unitaryBlockAlgebraAction_surjective D i S
    have hintertwine := intertwines_unitaryBlockAlgebraAction D i i T hT x
    rw [hx] at hintertwine
    have hm := congrArg (LinearMap.toMatrixAlgEquiv b) hintertwine
    rw [LinearMap.toMatrixAlgEquiv_comp,
      LinearMap.toMatrixAlgEquiv_comp] at hm
    show Matrix.single p q 1 * M = M * Matrix.single p q 1
    simpa [M, S] using hm.symm
  obtain ⟨c, hc⟩ := hscalar
  refine ⟨c, ?_⟩
  apply (LinearMap.toMatrixAlgEquiv b).injective
  change M = (LinearMap.toMatrixAlgEquiv b) (c • LinearMap.id)
  rw [← hc]
  simp only [map_smul, LinearMap.toMatrixAlgEquiv_id]
  rw [Matrix.scalar_apply]
  ext p q
  by_cases hpq : p = q
  · subst q; simp
  · rw [Matrix.diagonal_apply_ne _ hpq, Matrix.smul_apply,
      Matrix.one_apply_ne hpq, smul_zero]


@[simp] theorem unitaryBlockAction_mul_apply
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (g h : G) (v : UnitaryBlockCarrier D i) :
    unitaryBlockAction D i g (unitaryBlockAction D i h v) =
      unitaryBlockAction D i (g * h) v :=
  (LinearMap.congr_fun (unitaryBlockAction_mul D i g h) v).symm


/-- Group average of a linear map between two unitary irreducible blocks. -/
noncomputable def schurAverageMap
    (D : MatrixBlockDecomposition G) (i j : Fin D.count)
    (T : UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D j) :
    UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D j :=
  ∑ g : G,
    (unitaryBlockAction D j g).comp
      (T.comp (unitaryBlockAction D i g⁻¹))

/-- The group average is an intertwiner. -/
theorem schurAverageMap_intertwines
    (D : MatrixBlockDecomposition G) (i j : Fin D.count)
    (T : UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D j)
    (h : G) :
    (schurAverageMap D i j T).comp (unitaryBlockAction D i h) =
      (unitaryBlockAction D j h).comp (schurAverageMap D i j T) := by
  apply LinearMap.ext
  intro v
  simp only [schurAverageMap, LinearMap.sum_apply, LinearMap.comp_apply,
    map_sum]
  have hpoint : ∀ g : G,
      unitaryBlockAction D j (h * g)
          (T (unitaryBlockAction D i (h * g)⁻¹
            (unitaryBlockAction D i h v))) =
        unitaryBlockAction D j h
          (unitaryBlockAction D j g
            (T (unitaryBlockAction D i g⁻¹ v))) := by
    intro g
    simp only [unitaryBlockAction_mul_apply]
    congr 3
    group
  calc
    _ = ∑ g : G,
        unitaryBlockAction D j (h * g)
          (T (unitaryBlockAction D i (h * g)⁻¹
            (unitaryBlockAction D i h v))) := by
      symm
      exact Fintype.sum_bijective (fun g : G => h * g)
        (Group.mulLeft_bijective h)
        (fun g => unitaryBlockAction D j (h * g)
          (T (unitaryBlockAction D i (h * g)⁻¹
            (unitaryBlockAction D i h v))))
        (fun g => unitaryBlockAction D j g
          (T (unitaryBlockAction D i g⁻¹
            (unitaryBlockAction D i h v))))
        (fun _ => rfl)
    _ = _ := by simp_rw [hpoint]


/-- Distinct-block Schur averaging vanishes. -/
theorem schurAverageMap_eq_zero_of_ne
    (D : MatrixBlockDecomposition G) {i j : Fin D.count} (hji : j ≠ i)
    (T : UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D j) :
    schurAverageMap D i j T = 0 :=
  unitaryBlockIntertwiner_eq_zero_of_ne D hji _
    (schurAverageMap_intertwines D i j T)

/-- Same-block Schur averaging is scalar. -/
theorem schurAverageMap_eq_smul_id
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (T : UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D i) :
    ∃ c : ℂ, schurAverageMap D i i T = c • LinearMap.id :=
  unitaryBlockIntertwiner_eq_smul_id D i _
    (schurAverageMap_intertwines D i i T)

/-- Matrix-unit endomorphism in the averaged orthonormal block basis. -/
noncomputable def unitaryBlockMatrixUnit
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (p q : Fin (D.dimension i)) :
    UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D i :=
  (LinearMap.toMatrixAlgEquiv
    (unitaryBlockOrthonormalBasis D i).toBasis).symm
      (Matrix.single p q 1)

@[simp] theorem unitaryBlockMatrixUnit_toMatrix
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (p q : Fin (D.dimension i)) :
    LinearMap.toMatrixAlgEquiv
        (unitaryBlockOrthonormalBasis D i).toBasis
        (unitaryBlockMatrixUnit D i p q) =
      Matrix.single p q 1 := by
  exact (LinearMap.toMatrixAlgEquiv
    (unitaryBlockOrthonormalBasis D i).toBasis).apply_symm_apply _


/-- Rectangular matrix unit from block `i` to block `j` in their averaged
orthonormal bases. -/
noncomputable def unitaryBlockRectMatrixUnit
    (D : MatrixBlockDecomposition G) (i j : Fin D.count)
    (p : Fin (D.dimension j)) (q : Fin (D.dimension i)) :
    UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D j :=
  Matrix.toLin (unitaryBlockOrthonormalBasis D i).toBasis
    (unitaryBlockOrthonormalBasis D j).toBasis
    (Matrix.single p q 1)

@[simp] theorem unitaryBlockRectMatrixUnit_toMatrix
    (D : MatrixBlockDecomposition G) (i j : Fin D.count)
    (p : Fin (D.dimension j)) (q : Fin (D.dimension i)) :
    LinearMap.toMatrix (unitaryBlockOrthonormalBasis D i).toBasis
        (unitaryBlockOrthonormalBasis D j).toBasis
        (unitaryBlockRectMatrixUnit D i j p q) =
      Matrix.single p q 1 := by
  exact LinearMap.toMatrix_toLin _ _ _


/-- Matrix of the Schur average in the two orthonormal block bases. -/
theorem schurAverageMap_toMatrix
    (D : MatrixBlockDecomposition G) (i j : Fin D.count)
    (T : UnitaryBlockCarrier D i →ₗ[ℂ] UnitaryBlockCarrier D j) :
    LinearMap.toMatrix (unitaryBlockOrthonormalBasis D i).toBasis
        (unitaryBlockOrthonormalBasis D j).toBasis
        (schurAverageMap D i j T) =
      ∑ g : G,
        normalizedBlockMatrix D j g *
          LinearMap.toMatrix (unitaryBlockOrthonormalBasis D i).toBasis
            (unitaryBlockOrthonormalBasis D j).toBasis T *
          normalizedBlockMatrix D i g⁻¹ := by
  classical
  unfold schurAverageMap
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [LinearMap.toMatrix_comp
      (unitaryBlockOrthonormalBasis D i).toBasis
      (unitaryBlockOrthonormalBasis D j).toBasis
      (unitaryBlockOrthonormalBasis D j).toBasis,
    LinearMap.toMatrix_comp
      (unitaryBlockOrthonormalBasis D i).toBasis
      (unitaryBlockOrthonormalBasis D i).toBasis
      (unitaryBlockOrthonormalBasis D j).toBasis]
  rw [Matrix.mul_assoc]
  rfl

/-- Schur orthogonality between matrix coefficients belonging to distinct
Artin--Wedderburn blocks. -/
theorem normalizedBlockMatrix_cross_orthogonality
    (D : MatrixBlockDecomposition G) {i j : Fin D.count} (hji : j ≠ i)
    (a b : Fin (D.dimension i)) (c d : Fin (D.dimension j)) :
    (∑ g : G, star (normalizedBlockMatrix D i g a b) *
      normalizedBlockMatrix D j g c d) = 0 := by
  let T := unitaryBlockRectMatrixUnit D i j d b
  classical
  have havg : schurAverageMap D i j T = 0 :=
    schurAverageMap_eq_zero_of_ne D hji T
  have hmatrix := congrArg
    (LinearMap.toMatrix (unitaryBlockOrthonormalBasis D i).toBasis
      (unitaryBlockOrthonormalBasis D j).toBasis) havg
  rw [schurAverageMap_toMatrix] at hmatrix
  simp only [T, unitaryBlockRectMatrixUnit_toMatrix] at hmatrix
  simp only [map_zero] at hmatrix
  have hentry := Matrix.ext_iff.mpr hmatrix c a
  simp only [Matrix.zero_apply] at hentry
  have hterm : ∀ x : G,
      (normalizedBlockMatrix D j x * Matrix.single d b (1 : ℂ) *
        star (normalizedBlockMatrix D i x)) c a =
        star (normalizedBlockMatrix D i x a b) *
          normalizedBlockMatrix D j x c d := by
    intro x
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [Matrix.mul_single_apply_same]
      simp [mul_comm]
    · intro k _ hkb
      rw [Matrix.mul_single_apply_of_ne]
      · simp
      · exact hkb
    · simp
  rw [matrix_fintype_sum_apply] at hentry
  simp_rw [normalizedBlockMatrix_inv_eq_star] at hentry
  simpa only [hterm] using hentry


/-- Trace is unchanged by conjugation with a normalized unitary block
matrix. -/
theorem trace_normalizedBlock_conjugate
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (g : G)
    (A : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ) :
    Matrix.trace (normalizedBlockMatrix D i g * A *
      normalizedBlockMatrix D i g⁻¹) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle]
  rw [← normalizedBlockMatrix_mul,
    inv_mul_cancel, normalizedBlockMatrix_one, Matrix.one_mul]

/-- Trace of the averaged matrix unit, determining the scalar in the
same-block Schur lemma. -/
theorem trace_schurAverage_matrixUnit
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (d b : Fin (D.dimension i)) :
    Matrix.trace
        (LinearMap.toMatrixAlgEquiv
          (unitaryBlockOrthonormalBasis D i).toBasis
          (schurAverageMap D i i (unitaryBlockMatrixUnit D i d b))) =
      (Fintype.card G : ℂ) * (if d = b then 1 else 0) := by
  rw [show LinearMap.toMatrixAlgEquiv
      (unitaryBlockOrthonormalBasis D i).toBasis
      (schurAverageMap D i i (unitaryBlockMatrixUnit D i d b)) =
    LinearMap.toMatrix (unitaryBlockOrthonormalBasis D i).toBasis
      (unitaryBlockOrthonormalBasis D i).toBasis
      (schurAverageMap D i i (unitaryBlockMatrixUnit D i d b)) from rfl,
    schurAverageMap_toMatrix]
  have hunit :
      LinearMap.toMatrix (unitaryBlockOrthonormalBasis D i).toBasis
          (unitaryBlockOrthonormalBasis D i).toBasis
          (unitaryBlockMatrixUnit D i d b) =
        Matrix.single d b 1 := by
    change LinearMap.toMatrixAlgEquiv
      (unitaryBlockOrthonormalBasis D i).toBasis
      (unitaryBlockMatrixUnit D i d b) = Matrix.single d b 1
    exact unitaryBlockMatrixUnit_toMatrix D i d b
  rw [hunit]
  rw [Matrix.trace_sum]
  simp_rw [trace_normalizedBlock_conjugate]
  by_cases hdb : d = b
  · subst d
    simp
  · rw [Matrix.trace_single_eq_of_ne d b (1 : ℂ) hdb]
    simp [hdb]


/-- Same-block Schur orthogonality with its exact finite-group constant. -/
theorem normalizedBlockMatrix_same_orthogonality
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (a b c d : Fin (D.dimension i)) :
    (∑ g : G, star (normalizedBlockMatrix D i g a b) *
      normalizedBlockMatrix D i g c d) =
      ((Fintype.card G : ℂ) / D.dimension i) *
        (if a = c ∧ b = d then 1 else 0) := by
  classical
  let T := unitaryBlockMatrixUnit D i d b
  obtain ⟨z, hz⟩ := schurAverageMap_eq_smul_id D i T
  have hmatrix := congrArg
    (LinearMap.toMatrixAlgEquiv
      (unitaryBlockOrthonormalBasis D i).toBasis) hz
  have hleft : LinearMap.toMatrixAlgEquiv
      (unitaryBlockOrthonormalBasis D i).toBasis
      (schurAverageMap D i i T) =
      ∑ g : G, normalizedBlockMatrix D i g *
        Matrix.single d b 1 * normalizedBlockMatrix D i g⁻¹ := by
    rw [show LinearMap.toMatrixAlgEquiv
        (unitaryBlockOrthonormalBasis D i).toBasis
        (schurAverageMap D i i T) =
      LinearMap.toMatrix (unitaryBlockOrthonormalBasis D i).toBasis
        (unitaryBlockOrthonormalBasis D i).toBasis
        (schurAverageMap D i i T) from rfl,
      schurAverageMap_toMatrix]
    simp only [T]
    have hu : LinearMap.toMatrix
        (unitaryBlockOrthonormalBasis D i).toBasis
        (unitaryBlockOrthonormalBasis D i).toBasis
        (unitaryBlockMatrixUnit D i d b) = Matrix.single d b 1 := by
      change LinearMap.toMatrixAlgEquiv
        (unitaryBlockOrthonormalBasis D i).toBasis
        (unitaryBlockMatrixUnit D i d b) = Matrix.single d b 1
      exact unitaryBlockMatrixUnit_toMatrix D i d b
    rw [hu]
  rw [hleft] at hmatrix
  simp only [map_smul, LinearMap.toMatrixAlgEquiv_id] at hmatrix
  have hztrace := congrArg Matrix.trace hmatrix
  have hknown := trace_schurAverage_matrixUnit D i d b
  rw [hleft] at hknown
  have hdim : (D.dimension i : ℂ) ≠ 0 := by
    exact_mod_cast (D.dimension_neZero i).out
  have hzvalue : z = (Fintype.card G : ℂ) / D.dimension i *
      (if d = b then 1 else 0) := by
    have hztrace' :
        (Fintype.card G : ℂ) * (if d = b then 1 else 0) =
          Matrix.trace (z • (1 : Matrix (Fin (D.dimension i))
            (Fin (D.dimension i)) ℂ)) :=
      hknown.symm.trans hztrace
    simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at hztrace'
    rw [show (Fintype.card G : ℂ) / D.dimension i *
      (if d = b then 1 else 0) =
      ((Fintype.card G : ℂ) * (if d = b then 1 else 0)) /
        D.dimension i by ring]
    rw [eq_div_iff hdim]
    change (Fintype.card G : ℂ) * (if d = b then 1 else 0) =
      z * (D.dimension i : ℂ) at hztrace'
    exact hztrace'.symm
  have hentry := Matrix.ext_iff.mpr hmatrix c a
  rw [matrix_fintype_sum_apply] at hentry
  simp only [Matrix.smul_apply, Matrix.one_apply] at hentry
  simp_rw [normalizedBlockMatrix_inv_eq_star] at hentry
  have hterm : ∀ x : G,
      (normalizedBlockMatrix D i x * Matrix.single d b (1 : ℂ) *
        star (normalizedBlockMatrix D i x)) c a =
        star (normalizedBlockMatrix D i x a b) *
          normalizedBlockMatrix D i x c d := by
    intro x
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [Matrix.mul_single_apply_same]
      simp [mul_comm]
    · intro k _ hkb
      rw [Matrix.mul_single_apply_of_ne]
      · simp
      · exact hkb
    · simp
  simp only [hterm] at hentry
  rw [hzvalue] at hentry
  by_cases hac : a = c
  · subst c
    by_cases hbd : b = d
    · subst d
      simpa using hentry
    · have hdb : d ≠ b := Ne.symm hbd
      simpa [hbd, hdb] using hentry
  · have hca : c ≠ a := Ne.symm hac
    simpa [hac, hca] using hentry

end NCG.FinitePeterWeyl
