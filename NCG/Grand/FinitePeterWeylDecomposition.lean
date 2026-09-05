/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic

/-!
# Finite Peter--Weyl: algebraic regular decomposition

For a finite group over `ℂ`, Maschke's theorem makes the group algebra a
semisimple module over itself.  The finite semisimple decomposition theorem
therefore writes the left regular representation as a finite direct sum of
simple submodules.  Each summand is an irreducible representation.

This is the algebraic completeness layer needed by the finite spin-network
theorem.  Normalized matrix-coefficient orthogonality and the graphwise vertex
contraction are developed on top of this decomposition.
-/

open scoped MonoidAlgebra

namespace NCG.FinitePeterWeyl

variable {G : Type*} [Group G] [Fintype G]

/-- The complex group algebra carrying the left regular representation. -/
abbrev RegularCarrier (G : Type*) [Group G] := MonoidAlgebra ℂ G

/-- Every finite complex left regular representation is a finite direct sum
of simple group-algebra submodules.  This is the algebraic finite
Peter--Weyl decomposition, obtained from Maschke without assuming a list of
irreducibles. -/
theorem exists_regular_simple_decomposition :
    ∃ (n : ℕ) (S : Fin n → Submodule (RegularCarrier G) (RegularCarrier G))
      (_ : RegularCarrier G ≃ₗ[RegularCarrier G] Π₀ i : Fin n, S i),
      ∀ i, IsSimpleModule (RegularCarrier G) (S i) := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast (Nat.ne_of_gt (Nat.card_pos : 0 < Nat.card G))⟩
  exact IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp
    (RegularCarrier G) (RegularCarrier G)

/-- Every summand delivered by the regular decomposition is a simple
group-algebra module (equivalently, an irreducible complex representation). -/
theorem summand_isSimpleModule {n : ℕ}
    (S : Fin n → Submodule (RegularCarrier G) (RegularCarrier G))
    (hsimple : ∀ i, IsSimpleModule (RegularCarrier G) (S i)) (i : Fin n) :
    IsSimpleModule (RegularCarrier G) (S i) :=
  hsimple i

/-- Bundled algebraic Peter--Weyl data chosen from the existence theorem. -/
structure Decomposition (G : Type*) [Group G] [Fintype G] where
  count : ℕ
  summand : Fin count → Submodule (RegularCarrier G) (RegularCarrier G)
  split : RegularCarrier G ≃ₗ[RegularCarrier G] Π₀ i : Fin count, summand i
  simple : ∀ i, IsSimpleModule (RegularCarrier G) (summand i)

/- Peter--Weyl decomposition data exist for every finite group. -/
theorem decomposition_nonempty (G : Type*) [Group G] [Fintype G] :
    Nonempty (Decomposition G) := by
  classical
  obtain ⟨n, S, e, hs⟩ := exists_regular_simple_decomposition (G := G)
  exact ⟨⟨n, S, e, hs⟩⟩

/- The finite Peter--Weyl decomposition can be chosen for every finite group. -/
noncomputable def chooseDecomposition (G : Type*) [Group G] [Fintype G] :
    Decomposition G :=
  Classical.choice (decomposition_nonempty G)

/-- All chosen summands are simple group-algebra modules. -/
theorem chooseDecomposition_simple
    (i : Fin (chooseDecomposition G).count) :
    IsSimpleModule (RegularCarrier G) ((chooseDecomposition G).summand i) :=
  (chooseDecomposition G).simple i


/-! ## Full Artin--Wedderburn block form -/

/-- The finite complex group algebra as a product of full matrix blocks.
The block index is the finite set of irreducible representation classes and
`dimension i` is the dimension of the corresponding irreducible carrier. -/
structure MatrixBlockDecomposition (G : Type*) [Group G] [Fintype G] where
  count : ℕ
  dimension : Fin count → ℕ
  dimension_neZero : ∀ i, NeZero (dimension i)
  blockEquiv : RegularCarrier G ≃ₐ[ℂ]
    Π i, Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ

/-- Full Artin--Wedderburn data exist for every finite complex group algebra. -/
theorem matrixBlockDecomposition_nonempty
    (G : Type*) [Group G] [Fintype G] :
    Nonempty (MatrixBlockDecomposition G) := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast (Nat.ne_of_gt (Nat.card_pos : 0 < Nat.card G))⟩
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
      ℂ (RegularCarrier G)
  exact ⟨⟨n, d, hd, e⟩⟩

/-- A canonical (choice-dependent) full matrix-block decomposition. -/
noncomputable def chooseMatrixBlockDecomposition
    (G : Type*) [Group G] [Fintype G] :
    MatrixBlockDecomposition G :=
  Classical.choice (matrixBlockDecomposition_nonempty G)


/-- Projection of the group algebra onto one full Peter--Weyl matrix block. -/
noncomputable def blockAlgHom (D : MatrixBlockDecomposition G)
    (i : Fin D.count) :
    RegularCarrier G →ₐ[ℂ]
      Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ :=
  (Pi.evalAlgHom ℂ
    (fun j => Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) ℂ) i).comp
      D.blockEquiv.toAlgHom

/-- Every matrix in an irreducible block is generated by the group algebra. -/
theorem blockAlgHom_surjective (D : MatrixBlockDecomposition G)
    (i : Fin D.count) : Function.Surjective (blockAlgHom D i) := by
  classical
  intro A
  let target : Π j, Matrix (Fin (D.dimension j))
      (Fin (D.dimension j)) ℂ :=
    Function.update 0 i A
  obtain ⟨x, hx⟩ := D.blockEquiv.surjective target
  refine ⟨x, ?_⟩
  simp [blockAlgHom, hx, target]

/-- Matrix of a group element in one Peter--Weyl block. -/
noncomputable def blockMatrix (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (g : G) :
    Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ :=
  blockAlgHom D i (MonoidAlgebra.single g 1)

@[simp] theorem blockMatrix_one (D : MatrixBlockDecomposition G)
    (i : Fin D.count) : blockMatrix D i 1 = 1 := by
  have hone : (MonoidAlgebra.single 1 1 : RegularCarrier G) = 1 := MonoidAlgebra.one_def.symm
  rw [blockMatrix, hone]
  exact map_one (blockAlgHom D i)

@[simp] theorem blockMatrix_mul (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (g h : G) :
    blockMatrix D i (g * h) = blockMatrix D i g * blockMatrix D i h := by
  change blockAlgHom D i (MonoidAlgebra.single (g * h) 1) = _
  calc
    _ = blockAlgHom D i (MonoidAlgebra.single g 1 *
        MonoidAlgebra.single h 1) := by simp
    _ = _ := map_mul (blockAlgHom D i) _ _

@[simp] theorem blockMatrix_inv_mul (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (g : G) :
    blockMatrix D i g⁻¹ * blockMatrix D i g = 1 := by
  rw [← blockMatrix_mul, inv_mul_cancel g, blockMatrix_one]

/-- Concrete cyclicity/irreducibility certificate: from any nonzero vector,
the image of the group algebra reaches every vector in the block carrier. -/
theorem block_cyclic (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (v w : Fin (D.dimension i) → ℂ) (hv : v ≠ 0) :
    ∃ a : RegularCarrier G, (blockAlgHom D i a).mulVec v = w := by
  classical
  have hcoord : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hcoord
  let A : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ :=
    fun p q => if q = j then w p / v j else 0
  obtain ⟨a, ha⟩ := blockAlgHom_surjective D i A
  refine ⟨a, ?_⟩
  rw [ha]
  ext p
  simp only [Matrix.mulVec, A, dotProduct]
  rw [Finset.sum_eq_single j]
  · simpa using div_mul_cancel₀ (w p) hj
  · intro q hq hqj
    simp [hqj]
  · simp



/-- A standard matrix unit supported in one Artin--Wedderburn block. -/
noncomputable def blockUnit (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (a b : Fin (D.dimension i)) :
    Π j, Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) ℂ :=
  Function.update 0 i (Matrix.single a b 1)

/-- Pulling a standard block matrix unit back to the group algebra gives one
algebraic Peter--Weyl matrix-coefficient vector. -/
noncomputable def coefficientElement (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (a b : Fin (D.dimension i)) : RegularCarrier G :=
  D.blockEquiv.symm (blockUnit D i a b)

@[simp] theorem blockEquiv_coefficientElement
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (a b : Fin (D.dimension i)) :
    D.blockEquiv (coefficientElement D i a b) = blockUnit D i a b := by
  simp [coefficientElement]

/-! ## The one-edge Peter--Weyl basis -/

/-- A block label together with its row and column matrix indices. -/
abbrev CoefficientIndex (D : MatrixBlockDecomposition G) :=
  (i : Fin D.count) ×
    (Fin (D.dimension i) × Fin (D.dimension i))

/-- Currying identifies scalar coordinates indexed by block/row/column with
the dependent product of full matrix blocks. -/
noncomputable def coefficientFlattening (D : MatrixBlockDecomposition G) :
    (CoefficientIndex D → ℂ) ≃ₗ[ℂ]
      Π i, Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ :=
  (LinearEquiv.piCurry ℂ
      (fun (_i : Fin D.count) (_ab : Fin (D.dimension _i) ×
        Fin (D.dimension _i)) => ℂ)).trans
    (LinearEquiv.piCongrRight (fun i =>
      LinearEquiv.curry ℂ ℂ (Fin (D.dimension i))
        (Fin (D.dimension i))))

/-- The flattened coordinate transform followed by inverse
Artin--Wedderburn is the exact one-edge spin transform. -/
noncomputable def coefficientLinearEquiv (D : MatrixBlockDecomposition G) :
    (CoefficientIndex D → ℂ) ≃ₗ[ℂ] RegularCarrier G :=
  (coefficientFlattening D).trans D.blockEquiv.symm.toLinearEquiv

/-- The pulled-back matrix units form a genuine basis of the one-edge
holonomy space. -/
noncomputable def coefficientBasis (D : MatrixBlockDecomposition G) :
    Module.Basis (CoefficientIndex D) ℂ (RegularCarrier G) :=
  (Pi.basisFun ℂ (CoefficientIndex D)).map (coefficientLinearEquiv D)

@[simp] theorem coefficientFlattening_single
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (a b : Fin (D.dimension i)) :
    coefficientFlattening D (Pi.single ⟨i, (a, b)⟩ 1) =
      blockUnit D i a b := by
  classical
  ext j p q
  change (((Pi.single ⟨i, (a, b)⟩ (1 : ℂ)) :
      CoefficientIndex D → ℂ) ⟨j, (p, q)⟩) =
    ((Function.update
      (0 : Π j, Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) ℂ)
      i (Matrix.single a b 1)) j) p q
  by_cases hij : j = i
  · subst j
    simp [Pi.single_apply, Matrix.single_apply, Sigma.ext_iff, eq_comm]
  · simp [hij]

@[simp] theorem coefficientBasis_apply
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (a b : Fin (D.dimension i)) :
    coefficientBasis D ⟨i, (a, b)⟩ = coefficientElement D i a b := by
  rw [coefficientBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  simp only [coefficientLinearEquiv, LinearEquiv.trans_apply]
  rw [coefficientFlattening_single]
  rfl

/-! ## Left and right representation laws -/

/-- In its own irreducible block, a pulled-back coefficient element is the
corresponding standard matrix unit. -/
@[simp] theorem blockAlgHom_coefficientElement_same
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (a b : Fin (D.dimension i)) :
    blockAlgHom D i (coefficientElement D i a b) =
      Matrix.single a b 1 := by
  simp [blockAlgHom, blockEquiv_coefficientElement, blockUnit]

/-- Every other irreducible block annihilates that coefficient element. -/
@[simp] theorem blockAlgHom_coefficientElement_of_ne
    (D : MatrixBlockDecomposition G) {i j : Fin D.count} (hji : j ≠ i)
    (a b : Fin (D.dimension i)) :
    blockAlgHom D j (coefficientElement D i a b) = 0 := by
  simp [blockAlgHom, blockEquiv_coefficientElement, blockUnit, hji]

/-- Left translation acts on the row index by the defining irreducible block
matrix. -/
theorem blockAlgHom_left_translate_coefficient
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (g : G) (a b : Fin (D.dimension i)) :
    blockAlgHom D i
        (MonoidAlgebra.single g 1 * coefficientElement D i a b) =
      blockMatrix D i g * Matrix.single a b 1 := by
  rw [map_mul, blockAlgHom_coefficientElement_same]
  rfl

/-- Right translation acts on the column index; using the inverse gives the
dual representation occurring at an outgoing half-edge. -/
theorem blockAlgHom_right_translate_coefficient
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (g : G) (a b : Fin (D.dimension i)) :
    blockAlgHom D i
        (coefficientElement D i a b * MonoidAlgebra.single g⁻¹ 1) =
      Matrix.single a b 1 * blockMatrix D i g⁻¹ := by
  rw [map_mul, blockAlgHom_coefficientElement_same]
  rfl

/-- Combined endpoint gauge transport is the defining action on the row and
the dual action on the column. -/
theorem blockAlgHom_endpoint_translate_coefficient
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (ht hs : G) (a b : Fin (D.dimension i)) :
    blockAlgHom D i
        (MonoidAlgebra.single ht 1 * coefficientElement D i a b *
          MonoidAlgebra.single hs⁻¹ 1) =
      blockMatrix D i ht * Matrix.single a b 1 *
        blockMatrix D i hs⁻¹ := by
  rw [map_mul, map_mul, blockAlgHom_coefficientElement_same]
  rfl

/-! ## Tensoring the coefficient basis over graph edges -/

/-- Algebraic tensor product of one regular carrier for every edge. -/
abbrev EdgeTensorSpace (G : Type*) [Group G] (E : Type*) :=
  PiTensorProduct ℂ (fun _ : E => RegularCarrier G)

/-- Tensoring the one-edge Peter--Weyl bases gives the complete edge-labelled
basis before imposing vertex gauge invariance. -/
noncomputable def edgeCoefficientBasis (D : MatrixBlockDecomposition G)
    (E : Type*) [Finite E] :
    Module.Basis (E → CoefficientIndex D) ℂ (EdgeTensorSpace G E) :=
  Basis.piTensorProduct (fun _ : E => coefficientBasis D)

@[simp] theorem edgeCoefficientBasis_apply
    (D : MatrixBlockDecomposition G) (E : Type*) [Finite E]
    (label : E → CoefficientIndex D) :
    edgeCoefficientBasis D E label =
      ⨂ₜ[ℂ] e : E,
        coefficientElement D (label e).1 (label e).2.1 (label e).2.2 := by
  rw [edgeCoefficientBasis, Basis.piTensorProduct_apply]
  congr 1
  funext e
  obtain ⟨i, a, b⟩ := label e
  exact coefficientBasis_apply D i a b

/-- The pure group-element tensors form the holonomy basis of the edge tensor
product. -/
noncomputable def edgeHolonomyTensorBasis (G : Type*) [Group G]
    (E : Type*) [Finite E] :
    Module.Basis (E → G) ℂ (EdgeTensorSpace G E) :=
  Basis.piTensorProduct (fun _ : E => MonoidAlgebra.basis G ℂ)

/-- Identify the tensor product of edge group algebras with scalar functions
on the finite configuration space `G^E`, sending a pure group history to its
delta function. -/
noncomputable def edgeTensorToHolonomyFunctions
    (G : Type*) [Group G] [Fintype G]
    (E : Type*) [Fintype E] :
    EdgeTensorSpace G E ≃ₗ[ℂ] ((E → G) → ℂ) :=
  (edgeHolonomyTensorBasis G E).equiv
    (Pi.basisFun ℂ (E → G)) (Equiv.refl (E → G))

@[simp] theorem edgeTensorToHolonomyFunctions_group_history
    (G : Type*) [Group G] [Fintype G]
    (E : Type*) [Fintype E] (g : E → G) :
    edgeTensorToHolonomyFunctions G E
        (⨂ₜ[ℂ] e : E, MonoidAlgebra.single (g e) 1) =
      (Pi.basisFun ℂ (E → G)) g := by
  have ht : (⨂ₜ[ℂ] e : E, MonoidAlgebra.single (g e) 1) =
      edgeHolonomyTensorBasis G E g := by
    rw [edgeHolonomyTensorBasis, Basis.piTensorProduct_apply]
    congr 1
  rw [ht]
  exact Module.Basis.equiv_apply
    (edgeHolonomyTensorBasis G E) g (Pi.basisFun ℂ (E → G)) _

/-- Complete Peter--Weyl edge basis rendered as functions on `G^E`. -/
noncomputable def edgePeterWeylBasis (D : MatrixBlockDecomposition G)
    (E : Type*) [Fintype E] :
    Module.Basis (E → CoefficientIndex D) ℂ ((E → G) → ℂ) :=
  (edgeCoefficientBasis D E).map (edgeTensorToHolonomyFunctions G E)

@[simp] theorem edgePeterWeylBasis_apply
    (D : MatrixBlockDecomposition G) (E : Type*) [Fintype E]
    (label : E → CoefficientIndex D) :
    edgePeterWeylBasis D E label = edgeTensorToHolonomyFunctions G E
      (⨂ₜ[ℂ] e : E,
        coefficientElement D (label e).1 (label e).2.1 (label e).2.2) := by
  rw [edgePeterWeylBasis, Module.Basis.map_apply,
    edgeCoefficientBasis_apply]

/-- Exact inverse Peter--Weyl transform: every full group-algebra history is
the finite sum of its matrix-block coordinates against the pulled-back matrix
units. -/
theorem coefficientElement_expansion (D : MatrixBlockDecomposition G)
    (x : RegularCarrier G) :
    x = ∑ i : Fin D.count,
      ∑ a : Fin (D.dimension i),
        ∑ b : Fin (D.dimension i),
          (D.blockEquiv x i a b) • coefficientElement D i a b := by
  classical
  apply D.blockEquiv.injective
  ext j p q
  simp only [map_sum, map_smul, blockEquiv_coefficientElement]
  rw [Fintype.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp only [Fintype.sum_apply, Pi.smul_apply, Matrix.smul_apply]
    simpa [blockUnit] using congrArg
      (fun M : Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) ℂ => M p q)
      (Matrix.matrix_eq_sum_single (D.blockEquiv x j))
  · intro i hi hij
    simp [blockUnit, hij.symm, Fintype.sum_apply]
  · simp

/-- The pulled-back matrix coefficients are linearly independent and span;
equivalently, their coordinate expansion is unique. -/
theorem coefficientElement_coordinates_unique (D : MatrixBlockDecomposition G)
    (x y : RegularCarrier G) (h : D.blockEquiv x = D.blockEquiv y) : x = y :=
  D.blockEquiv.injective h

/-- Completeness of the matrix blocks: the sum of the squared irreducible
dimensions is exactly the order of the finite group. -/
theorem matrixBlock_dimension_count (D : MatrixBlockDecomposition G) :
    Nat.card G = ∑ i : Fin D.count, (D.dimension i) ^ 2 := by
  have h := LinearEquiv.finrank_eq D.blockEquiv.toLinearEquiv
  have hcoeff := LinearEquiv.finrank_eq
    (MonoidAlgebra.coeffLinearEquiv ℂ :
      RegularCarrier G ≃ₗ[ℂ] G →₀ ℂ)
  have h' := hcoeff.symm.trans h
  rw [Module.finrank_pi_fintype ℂ] at h'
  simpa [Module.finrank_finsupp_self, Module.finrank_matrix, pow_two]
    using h'

/-- The chosen Peter--Weyl blocks exhaust all functions on the group. -/
theorem chooseMatrixBlock_dimension_count :
    Nat.card G = ∑ i : Fin (chooseMatrixBlockDecomposition G).count,
      ((chooseMatrixBlockDecomposition G).dimension i) ^ 2 :=
  matrixBlock_dimension_count (chooseMatrixBlockDecomposition G)
end NCG.FinitePeterWeyl
