/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteEdgePeterWeylOrthonormalBasis
import NCG.Grand.VertexIntertwinerContraction

/-!
# Explicit finite spin-network orthonormality

This module supplies the Hilbert-space normalization missing from the raw
vertex-contraction construction.  Counting-measure Peter--Weyl coefficients
are contracted against the chosen orthonormal local invariant tensors.
-/

namespace NCG.FiniteSpinNetwork

open NCG.FinitePeterWeyl
open scoped PiTensorProduct

variable {G V E : Type*} [Group G] [Fintype G] [Fintype V]
  [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Assemble one edge-representation field and one local intertwiner at every
vertex into the manuscript's spin-network label. -/
def labelOf (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (a : (v : V) → IntertwinerIndex D t s π v) :
    Label D t s where
  edgeRepresentation := π
  vertexIntertwiner := a

@[simp] theorem labelOf_edgeRepresentation
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (a : (v : V) → IntertwinerIndex D t s π v) :
    (labelOf D t s π a).edgeRepresentation = π := rfl

@[simp] theorem labelOf_vertexIntertwiner
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (a : (v : V) → IntertwinerIndex D t s π v) (v : V) :
    (labelOf D t s π a).vertexIntertwiner v = a v := rfl
/-- Coordinate tensor obtained by multiplying the chosen invariant bra at
every vertex in one fixed edge-representation block. -/
noncomputable def vertexContractionCoordinates
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (a : (v : V) → IntertwinerIndex D t s π v)
    (row col : (e : E) → Fin (D.dimension (π e))) : ℂ :=
  ∏ v : V, star ((vertexIntertwinerBasis D t s π v (a v)).1.ofLp
    (vertexTensorIndexOf D t s π row col v))

@[simp] theorem vertexContraction_labelOf
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (a : (v : V) → IntertwinerIndex D t s π v)
    (row col : (e : E) → Fin (D.dimension (π e))) :
    vertexContraction D t s (labelOf D t s π a) row col =
      vertexContractionCoordinates D t s π a row col := rfl


/-- Coordinate form of orthonormality for one vertex intertwiner basis. -/
theorem vertexIntertwiner_coordinate_inner
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V)
    (a b : IntertwinerIndex D t s π v) :
    (∑ rowIndex : IncomingIndex D t π v,
      ∑ colIndex : OutgoingIndex D s π v,
        (vertexIntertwinerBasis D t s π v a).1.ofLp
            (rowIndex, colIndex) *
          star ((vertexIntertwinerBasis D t s π v b).1.ofLp
            (rowIndex, colIndex))) =
      if a = b then 1 else 0 := by
  have hlocal := orthonormal_iff_ite.mp
    (vertexIntertwinerBasis D t s π v).orthonormal b a
  rw [Submodule.coe_inner] at hlocal
  simp only [PiLp.inner_apply, RCLike.inner_apply'] at hlocal
  rw [Fintype.sum_prod_type] at hlocal
  calc
    _ = ∑ rowIndex : IncomingIndex D t π v,
        ∑ colIndex : OutgoingIndex D s π v,
          star ((vertexIntertwinerBasis D t s π v b).1.ofLp
            (rowIndex, colIndex)) *
            (vertexIntertwinerBasis D t s π v a).1.ofLp
              (rowIndex, colIndex) := by
      apply Finset.sum_congr rfl
      intro rowIndex _
      apply Finset.sum_congr rfl
      intro colIndex _
      ring
    _ = if b = a then 1 else 0 := hlocal
    _ = if a = b then 1 else 0 := by
      by_cases h : a = b
      · subst b
        simp
      · have h' : b ≠ a := Ne.symm h
        simp [h, h']

set_option maxHeartbeats 1000000 in
/-- Scalar Kronecker-delta identity for products of the conjugated local
intertwiner coordinates in one fixed edge-representation block. -/
theorem vertexContraction_inner
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (a b : (v : V) → IntertwinerIndex D t s π v) :
    (∑ rc :
        ((e : E) → Fin (D.dimension (π e))) ×
        ((e : E) → Fin (D.dimension (π e))),
      star (vertexContractionCoordinates D t s π a rc.1 rc.2) *
        vertexContractionCoordinates D t s π b rc.1 rc.2) =
      if a = b then 1 else 0 := by
  classical
  have hstar : ∀
      (row col : (e : E) → Fin (D.dimension (π e))),
      star (vertexContractionCoordinates D t s π a row col) =
        ∏ v : V,
          (vertexIntertwinerBasis D t s π v (a v)).1.ofLp
            (vertexTensorIndexOf D t s π row col v) := by
    intro row col
    simp [vertexContractionCoordinates]
  rw [Fintype.sum_prod_type]
  simp_rw [hstar]
  simp only [vertexContractionCoordinates]
  simp_rw [← Finset.prod_mul_distrib]
  calc
    (∑ row : (e : E) → Fin (D.dimension (π e)),
      ∑ col : (e : E) → Fin (D.dimension (π e)),
        ∏ v : V,
          (vertexIntertwinerBasis D t s π v (a v)).1.ofLp
              (vertexTensorIndexOf D t s π row col v) *
            star ((vertexIntertwinerBasis D t s π v (b v)).1.ofLp
              (vertexTensorIndexOf D t s π row col v))) =
      ∑ rowFamily : (v : V) → IncomingIndex D t π v,
        ∑ colFamily : (v : V) → OutgoingIndex D s π v,
          ∏ v : V,
            (vertexIntertwinerBasis D t s π v (a v)).1.ofLp
                (rowFamily v, colFamily v) *
              star ((vertexIntertwinerBasis D t s π v (b v)).1.ofLp
                (rowFamily v, colFamily v)) := by
      rw [← (rowVertexEquiv D t π).symm.sum_comp]
      simp_rw [← (colVertexEquiv D s π).symm.sum_comp]
      simp only [vertexTensorIndexOf_regroup, Equiv.apply_symm_apply]
    _ = ∏ v : V,
        ∑ rowIndex : IncomingIndex D t π v,
          ∑ colIndex : OutgoingIndex D s π v,
            (vertexIntertwinerBasis D t s π v (a v)).1.ofLp
                (rowIndex, colIndex) *
              star ((vertexIntertwinerBasis D t s π v (b v)).1.ofLp
                (rowIndex, colIndex)) := by
      exact sum_pi_pair_prod (V := V) (fun v rowIndex colIndex =>
        (vertexIntertwinerBasis D t s π v (a v)).1.ofLp
            (rowIndex, colIndex) *
          star ((vertexIntertwinerBasis D t s π v (b v)).1.ofLp
            (rowIndex, colIndex)))
    _ = ∏ v : V, if a v = b v then 1 else 0 := by
      apply Finset.prod_congr rfl
      intro v _
      exact vertexIntertwiner_coordinate_inner D t s π v (a v) (b v)
    _ = if a = b then 1 else 0 := by
      by_cases h : a = b
      · subst b
        simp
      · have hpoint : ∃ v, a v ≠ b v := by
          simpa only [Function.ne_iff] using h
        obtain ⟨v, hv⟩ := hpoint
        simp [h, Finset.prod_eq_zero (Finset.mem_univ v), hv]


/-- Inside a fixed edge-representation block, products of the conjugated
local intertwiner coordinates form an orthonormal family. -/
theorem vertexContraction_orthonormal
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) :
    Orthonormal ℂ (fun a : (v : V) → IntertwinerIndex D t s π v =>
      WithLp.toLp 2 (fun rc :
          ((e : E) → Fin (D.dimension (π e))) ×
          ((e : E) → Fin (D.dimension (π e))) =>
        vertexContractionCoordinates D t s π a rc.1 rc.2)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  simpa [mul_comm] using vertexContraction_inner D t s π a b

/-- Row and column indices for one fixed edge-representation field. -/
abbrev EdgeMatrixIndex (D : MatrixBlockDecomposition G)
    (π : EdgeRepresentationLabel D E) :=
  ((e : E) → Fin (D.dimension (π e))) ×
    ((e : E) → Fin (D.dimension (π e)))

/-- Convert a block/row/column tuple into the edgewise coefficient index. -/
def edgeCoefficientIndexOf (D : MatrixBlockDecomposition G)
    (π : EdgeRepresentationLabel D E) (rc : EdgeMatrixIndex D π) :
    E → CoefficientIndex D :=
  fun e => ⟨π e, (rc.1 e, rc.2 e)⟩

theorem edgeCoefficientIndexOf_injective
    (D : MatrixBlockDecomposition G) (π : EdgeRepresentationLabel D E) :
    Function.Injective (edgeCoefficientIndexOf D π) := by
  intro rc rc' h
  apply Prod.ext
  · funext e
    have he := congrFun h e
    have hab : (rc.1 e, rc.2 e) = (rc'.1 e, rc'.2 e) := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
    exact congrArg Prod.fst hab
  · funext e
    have he := congrFun h e
    have hab : (rc.1 e, rc.2 e) = (rc'.1 e, rc'.2 e) := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
    exact congrArg Prod.snd hab

/-- The edge coefficients belonging to one fixed representation field remain
orthonormal after restricting the full edgewise Peter--Weyl basis. -/
theorem fixedBlockEdgeVector_orthonormal
    (D : MatrixBlockDecomposition G) (π : EdgeRepresentationLabel D E) :
    Orthonormal ℂ (fun rc : EdgeMatrixIndex D π =>
      peterWeylEdgeVector D E (edgeCoefficientIndexOf D π rc)) := by
  change Orthonormal ℂ
    (peterWeylEdgeVector D E ∘ edgeCoefficientIndexOf D π)
  exact (peterWeylEdgeVector_orthonormal D E).comp
    (edgeCoefficientIndexOf D π)
    (edgeCoefficientIndexOf_injective D π)

/-- The explicitly normalized contracted vector in the full edge-holonomy
Hilbert space. -/
noncomputable def contractedPeterWeylVector
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s) : EuclideanSpace ℂ (E → G) :=
  ∑ rc : EdgeMatrixIndex D L.edgeRepresentation,
    vertexContraction D t s L rc.1 rc.2 •
      peterWeylEdgeVector D E
        (edgeCoefficientIndexOf D L.edgeRepresentation rc)

@[simp] theorem contractedPeterWeylVector_apply
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s) (g : E → G) :
    contractedPeterWeylVector D t s L g =
      ∑ rc : EdgeMatrixIndex D L.edgeRepresentation,
        vertexContraction D t s L rc.1 rc.2 *
          ∏ e : E, peterWeylCoefficient D
            (L.edgeRepresentation e) (rc.1 e) (rc.2 e) (g e) := by
  simp [contractedPeterWeylVector, edgeCoefficientIndexOf,
    peterWeylEdgeVector_apply]

/-- In one fixed representation block, distinct choices of local
intertwiners give orthonormal contracted vectors. -/
theorem contractedPeterWeylVector_fixedBlock_orthonormal
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) :
    Orthonormal ℂ (fun a : (v : V) → IntertwinerIndex D t s π v =>
      contractedPeterWeylVector D t s (labelOf D t s π a)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  change inner ℂ
      (∑ rc : EdgeMatrixIndex D π,
        vertexContractionCoordinates D t s π a rc.1 rc.2 •
          peterWeylEdgeVector D E (edgeCoefficientIndexOf D π rc))
      (∑ rc : EdgeMatrixIndex D π,
        vertexContractionCoordinates D t s π b rc.1 rc.2 •
          peterWeylEdgeVector D E (edgeCoefficientIndexOf D π rc)) =
    if a = b then 1 else 0
  have hedge := (fixedBlockEdgeVector_orthonormal
    (E := E) D π).inner_sum
      (fun rc : EdgeMatrixIndex D π =>
        vertexContractionCoordinates D t s π a rc.1 rc.2)
      (fun rc : EdgeMatrixIndex D π =>
        vertexContractionCoordinates D t s π b rc.1 rc.2)
      Finset.univ
  have hintertwiner := orthonormal_iff_ite.mp
    (vertexContraction_orthonormal D t s π) a b
  simp only [PiLp.inner_apply, RCLike.inner_apply'] at hintertwiner
  exact hedge.trans hintertwiner


end NCG.FiniteSpinNetwork
