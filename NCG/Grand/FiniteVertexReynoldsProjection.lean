/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSpinNetworkOrthonormalBasis
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite vertex Reynolds projections

The local incoming/dual-outgoing tensor action is bundled as a matrix. Its
finite group average is the local completeness input for the explicit
spin-network basis.
-/

namespace NCG.FiniteSpinNetwork

open NCG.FinitePeterWeyl

variable {G V E : Type*} [Group G] [Fintype G] [Fintype V]
  [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Matrix of the local incoming-defining/outgoing-dual action. -/
noncomputable def vertexActionMatrix (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E) (v : V) (h : G) :
    Matrix (VertexTensorIndex D t s π v)
      (VertexTensorIndex D t s π v) ℂ :=
  fun x y => incomingKernel D t π v h x.1 y.1 *
    outgoingDualKernel D s π v h x.2 y.2

theorem vertexActionMatrix_mulVec (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E) (v : V) (h : G)
    (F : VertexTensorSpace D t s π v) :
    (vertexActionMatrix D t s π v h).mulVec F.ofLp =
      fun x => vertexActionValue D t s π v h F x := by
  rfl

private theorem incomingKernel_mul
    (D : MatrixBlockDecomposition G) (t : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) (h k : G)
    (x z : IncomingIndex D t π v) :
    incomingKernel D t π v (h * k) x z =
      ∑ y : IncomingIndex D t π v,
        incomingKernel D t π v h x y * incomingKernel D t π v k y z := by
  classical
  simp only [incomingKernel, normalizedBlockMatrix_mul, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.prod_mul_distrib]

private theorem outgoingDualKernel_mul
    (D : MatrixBlockDecomposition G) (s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) (h k : G)
    (x z : OutgoingIndex D s π v) :
    outgoingDualKernel D s π v (h * k) x z =
      ∑ y : OutgoingIndex D s π v,
        outgoingDualKernel D s π v h x y *
          outgoingDualKernel D s π v k y z := by
  classical
  simp only [outgoingDualKernel, mul_inv_rev, normalizedBlockMatrix_mul,
    Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  ring

theorem vertexActionMatrix_mul
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) (h k : G) :
    vertexActionMatrix D t s π v (h * k) =
      vertexActionMatrix D t s π v h * vertexActionMatrix D t s π v k := by
  classical
  ext x z
  simp only [vertexActionMatrix, Matrix.mul_apply, incomingKernel_mul,
    outgoingDualKernel_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro yIn _
  apply Finset.sum_congr rfl
  intro yOut _
  ring

@[simp] theorem vertexActionMatrix_one
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) :
    vertexActionMatrix D t s π v (1 : G) = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [vertexActionMatrix, incomingKernel, outgoingDualKernel,
      Matrix.one_apply]
  · have hpart : x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
      apply not_and_or.mp
      intro h
      exact hxy (Prod.ext h.1 h.2)
    rcases hpart with hin | hout
    · have hex : ∃ e, x.1 e ≠ y.1 e := by
        simpa only [Function.ne_iff] using hin
      obtain ⟨e, he⟩ := hex
      rw [Matrix.one_apply, if_neg hxy]
      unfold vertexActionMatrix incomingKernel outgoingDualKernel
      simp only [normalizedBlockMatrix_one]
      rw [mul_eq_zero]
      left
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [Matrix.one_apply, he]
    · have hex : ∃ e, x.2 e ≠ y.2 e := by
        simpa only [Function.ne_iff] using hout
      obtain ⟨e, he⟩ := hex
      rw [Matrix.one_apply, if_neg hxy]
      unfold vertexActionMatrix incomingKernel outgoingDualKernel
      simp only [normalizedBlockMatrix_one]
      rw [mul_eq_zero]
      right
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [Matrix.one_apply, Ne.symm he]

theorem vertexActionMatrix_inv_eq_star
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) (h : G) :
    vertexActionMatrix D t s π v h⁻¹ =
      star (vertexActionMatrix D t s π v h) := by
  classical
  ext x y
  have hin : incomingKernel D t π v h⁻¹ x.1 y.1 =
      star (incomingKernel D t π v h y.1 x.1) := by
    simpa using
      (star_incomingKernel_inv D t π v h⁻¹ y.1 x.1).symm
  have hout : outgoingDualKernel D s π v h⁻¹ x.2 y.2 =
      star (outgoingDualKernel D s π v h y.2 x.2) := by
    simpa using
      (star_outgoingDualKernel_inv D s π v h⁻¹ y.2 x.2).symm
  simp [vertexActionMatrix, hin, hout]

/-- The normalized finite-group Reynolds matrix at one vertex. -/
noncomputable def vertexReynoldsMatrix (D : MatrixBlockDecomposition G)
    (t s : E → V) (π : EdgeRepresentationLabel D E) (v : V) :
    Matrix (VertexTensorIndex D t s π v)
      (VertexTensorIndex D t s π v) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ h : G, vertexActionMatrix D t s π v h

theorem vertexReynoldsMatrix_mulVec_mem
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V)
    (F : VertexTensorSpace D t s π v) :
    WithLp.toLp 2 ((vertexReynoldsMatrix D t s π v).mulVec F.ofLp) ∈
      VertexInvariantSubspace D t s π v := by
  intro k x
  change (vertexActionMatrix D t s π v k).mulVec
      ((vertexReynoldsMatrix D t s π v).mulVec F.ofLp) x =
      (vertexReynoldsMatrix D t s π v).mulVec F.ofLp x
  rw [Matrix.mulVec_mulVec]
  congr 2
  unfold vertexReynoldsMatrix
  rw [Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  rw [show (∑ h : G, vertexActionMatrix D t s π v k *
      vertexActionMatrix D t s π v h) =
      ∑ h : G, vertexActionMatrix D t s π v (k * h) by
        apply Finset.sum_congr rfl
        intro h _
        rw [vertexActionMatrix_mul]]
  exact Fintype.sum_bijective (k * ·) (Group.mulLeft_bijective k)
    _ _ (fun h => rfl)

theorem vertexReynoldsMatrix_mulVec_eq_of_mem
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V)
    (F : VertexTensorSpace D t s π v)
    (hF : F ∈ VertexInvariantSubspace D t s π v) :
    (vertexReynoldsMatrix D t s π v).mulVec F.ofLp = F.ofLp := by
  funext x
  simp only [vertexReynoldsMatrix, Matrix.smul_mulVec, Matrix.sum_mulVec,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [show (∑ h : G, (vertexActionMatrix D t s π v h).mulVec F.ofLp x) =
      ∑ _h : G, F.ofLp x by
        apply Finset.sum_congr rfl
        intro h _
        exact hF h x]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp


/-- The finite Reynolds average is Hermitian. -/
theorem vertexReynoldsMatrix_star
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) :
    star (vertexReynoldsMatrix D t s π v) =
      vertexReynoldsMatrix D t s π v := by
  classical
  unfold vertexReynoldsMatrix
  calc
    star ((Fintype.card G : ℂ)⁻¹ •
        ∑ h : G, vertexActionMatrix D t s π v h) =
      (Fintype.card G : ℂ)⁻¹ •
        ∑ h : G, star (vertexActionMatrix D t s π v h) := by simp
    _ = (Fintype.card G : ℂ)⁻¹ •
        ∑ h : G, vertexActionMatrix D t s π v h⁻¹ := by
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      exact (vertexActionMatrix_inv_eq_star D t s π v h).symm
    _ = (Fintype.card G : ℂ)⁻¹ •
        ∑ h : G, vertexActionMatrix D t s π v h := by
      congr 1
      exact Fintype.sum_bijective Inv.inv inv_bijective
        _ _ (fun h => rfl)

/-- The finite Reynolds average is idempotent. -/
theorem vertexReynoldsMatrix_mul_self
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) :
    vertexReynoldsMatrix D t s π v *
      vertexReynoldsMatrix D t s π v =
        vertexReynoldsMatrix D t s π v := by
  classical
  rw [Matrix.ext_iff_mulVec]
  intro f
  rw [← Matrix.mulVec_mulVec]
  let F : VertexTensorSpace D t s π v := WithLp.toLp 2 f
  let RF : VertexTensorSpace D t s π v :=
    WithLp.toLp 2 ((vertexReynoldsMatrix D t s π v).mulVec f)
  have hmem : RF ∈ VertexInvariantSubspace D t s π v := by
    simpa [F, RF] using
      vertexReynoldsMatrix_mulVec_mem D t s π v F
  simpa [RF] using
    vertexReynoldsMatrix_mulVec_eq_of_mem D t s π v RF hmem

/-- Reynolds averaging as a continuous operator on the local Euclidean
tensor space. -/
noncomputable def vertexReynoldsOperator
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) :
    VertexTensorSpace D t s π v →L[ℂ] VertexTensorSpace D t s π v :=
  (Matrix.toEuclideanCLM
    (n := VertexTensorIndex D t s π v) (𝕜 := ℂ)) (vertexReynoldsMatrix D t s π v)

theorem vertexReynoldsOperator_isStarProjection
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) :
    IsStarProjection (vertexReynoldsOperator D t s π v) := by
  constructor
  · change IsIdempotentElem
      ((Matrix.toEuclideanCLM
        (n := VertexTensorIndex D t s π v) (𝕜 := ℂ))
          (vertexReynoldsMatrix D t s π v))
    simpa [IsIdempotentElem] using congrArg
      (Matrix.toEuclideanCLM
        (n := VertexTensorIndex D t s π v) (𝕜 := ℂ))
      (vertexReynoldsMatrix_mul_self D t s π v)
  · show star (vertexReynoldsOperator D t s π v) =
      vertexReynoldsOperator D t s π v
    simpa only [vertexReynoldsOperator, map_star] using congrArg
      (Matrix.toEuclideanCLM
        (n := VertexTensorIndex D t s π v) (𝕜 := ℂ))
      (vertexReynoldsMatrix_star D t s π v)

theorem vertexReynoldsOperator_range
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) :
    (vertexReynoldsOperator D t s π v).range =
      VertexInvariantSubspace D t s π v := by
  apply le_antisymm
  · rintro _ ⟨F, rfl⟩
    change WithLp.toLp 2
      ((vertexReynoldsMatrix D t s π v).mulVec F.ofLp) ∈ _
    exact vertexReynoldsMatrix_mulVec_mem D t s π v F
  · intro F hF
    refine ⟨F, ?_⟩
    apply WithLp.ofLp_injective 2
    simpa [vertexReynoldsOperator] using
      vertexReynoldsMatrix_mulVec_eq_of_mem D t s π v F hF

/-- The vertex Reynolds operator is exactly orthogonal projection onto the
local invariant tensor subspace. -/
theorem vertexReynoldsOperator_eq_starProjection
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V) :
    vertexReynoldsOperator D t s π v =
      (VertexInvariantSubspace D t s π v).starProjection := by
  have h := isStarProjection_iff_eq_starProjection_range.mp
    (vertexReynoldsOperator_isStarProjection D t s π v)
  rw [vertexReynoldsOperator_range D t s π v] at h
  obtain ⟨_, hEq⟩ := h
  exact hEq

/-- Expansion of the local Reynolds projection in the chosen orthonormal
intertwiner basis. -/
theorem vertexReynolds_mulVec_expansion
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V)
    (F : VertexTensorSpace D t s π v) :
    WithLp.toLp 2 ((vertexReynoldsMatrix D t s π v).mulVec F.ofLp) =
      ∑ a : IntertwinerIndex D t s π v,
        inner ℂ ((vertexIntertwinerBasis D t s π v a :
          VertexInvariantSubspace D t s π v) :
            VertexTensorSpace D t s π v) F •
          ((vertexIntertwinerBasis D t s π v a :
            VertexInvariantSubspace D t s π v) :
              VertexTensorSpace D t s π v) := by
  rw [show WithLp.toLp 2
      ((vertexReynoldsMatrix D t s π v).mulVec F.ofLp) =
      vertexReynoldsOperator D t s π v F by rfl]
  rw [vertexReynoldsOperator_eq_starProjection]
  let S := VertexInvariantSubspace D t s π v
  let b := vertexIntertwinerBasis D t s π v
  calc
    S.starProjection F = S.subtype (S.orthogonalProjectionOnto F) := rfl
    _ = S.subtype (∑ a : IntertwinerIndex D t s π v,
        inner ℂ ((b a : S) : VertexTensorSpace D t s π v) F • b a) := by
      exact congrArg S.subtype (b.orthogonalProjectionOnto_apply_eq_sum F)
    _ = ∑ a : IntertwinerIndex D t s π v,
        inner ℂ ((b a : S) : VertexTensorSpace D t s π v) F •
          ((b a : S) : VertexTensorSpace D t s π v) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_smul]
      rfl

/-- Entrywise projection-kernel formula in the chosen local intertwiner
basis. -/
theorem vertexReynoldsMatrix_entry_expansion
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (v : V)
    (x y : VertexTensorIndex D t s π v) :
    vertexReynoldsMatrix D t s π v x y =
      ∑ a : IntertwinerIndex D t s π v,
        (vertexIntertwinerBasis D t s π v a).1.ofLp x *
          star ((vertexIntertwinerBasis D t s π v a).1.ofLp y) := by
  classical
  let ey : VertexTensorSpace D t s π v :=
    EuclideanSpace.basisFun (VertexTensorIndex D t s π v) ℂ y
  have h := congrArg (fun Z : VertexTensorSpace D t s π v => Z.ofLp x)
    (vertexReynolds_mulVec_expansion D t s π v ey)
  simp only [WithLp.ofLp_toLp, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  have hey : ∀ z : VertexTensorIndex D t s π v,
      ey.ofLp z = if z = y then 1 else 0 := by
    intro z
    simp [ey, EuclideanSpace.basisFun_apply, Pi.single_apply]
  have hleft :
      (vertexReynoldsMatrix D t s π v).mulVec ey.ofLp x =
        vertexReynoldsMatrix D t s π v x y := by
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [hey]
    simp
  have hinner : ∀ a : IntertwinerIndex D t s π v,
      inner ℂ
        (((vertexIntertwinerBasis D t s π v a).1 :
          VertexTensorSpace D t s π v)) ey =
        star ((vertexIntertwinerBasis D t s π v a).1.ofLp y) := by
    intro a
    simp [PiLp.inner_apply, RCLike.inner_apply', hey]
  rw [hleft] at h
  simp_rw [hinner] at h
  simpa [mul_comm] using h


end NCG.FiniteSpinNetwork
