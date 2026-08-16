/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteVertexReynoldsProjection
import NCG.Grand.FiniteEdgePeterWeylBasisCompletion

/-!
# Completeness of the explicit finite spin-network family

Vertex gauge averaging factorizes into the product of the local Reynolds
projections.  Expanding those projections in the chosen local invariant
bases shows that every averaged Peter--Weyl coefficient is a finite linear
combination of the explicit contracted spin networks.
-/

namespace NCG.FiniteSpinNetwork

open NCG.FinitePeterWeyl

variable {G V E : Type*} [Group G] [Fintype G] [Fintype V]
  [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Averaging independent local action kernels over `G^V` is exactly the
product of the normalized local Reynolds kernels. -/
theorem globalVertexAverage_eq_prod_reynolds
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (x y : (v : V) → VertexTensorIndex D t s π v) :
    (Fintype.card (V → G) : ℂ)⁻¹ *
        ∑ h : V → G,
          ∏ v : V, vertexActionMatrix D t s π v (h v) (x v) (y v) =
      ∏ v : V, vertexReynoldsMatrix D t s π v (x v) (y v) := by
  classical
  unfold vertexReynoldsMatrix
  simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply]
  have hentry (v : V) :
      ((∑ h : G, vertexActionMatrix D t s π v h) :
          Matrix (VertexTensorIndex D t s π v)
            (VertexTensorIndex D t s π v) ℂ) (x v) (y v) =
        ∑ h : G, vertexActionMatrix D t s π v h (x v) (y v) := by
    simpa using Matrix.sum_apply (x v) (y v) Finset.univ
      (fun h : G => vertexActionMatrix D t s π v h)
  simp_rw [hentry]
  change (Fintype.card (V → G) : ℂ)⁻¹ *
      (∑ h : V → G, ∏ v : V,
        vertexActionMatrix D t s π v (h v) (x v) (y v)) =
    ∏ v : V, (Fintype.card G : ℂ)⁻¹ *
      ∑ h : G, vertexActionMatrix D t s π v h (x v) (y v)
  rw [Finset.prod_mul_distrib, Fintype.prod_sum]
  rw [Finset.prod_const, Fintype.card_fun]
  simp [← inv_pow]

/-- Product expansion of all local Reynolds kernels in the tensor products
of the selected vertex-intertwiner bases. -/
theorem prod_vertexReynolds_eq_sum_intertwiners
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (x y : (v : V) → VertexTensorIndex D t s π v) :
    (∏ v : V, vertexReynoldsMatrix D t s π v (x v) (y v)) =
      ∑ a : (v : V) → IntertwinerIndex D t s π v,
        (∏ v : V,
          (vertexIntertwinerBasis D t s π v (a v)).1.ofLp (x v)) *
        (∏ v : V,
          star ((vertexIntertwinerBasis D t s π v (a v)).1.ofLp (y v))) := by
  classical
  simp_rw [vertexReynoldsMatrix_entry_expansion]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_mul_distrib]

/-- Move the last index of a finite triple sum to the front. -/
theorem sum_three_last_to_front {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℂ) :
    (∑ a : A, ∑ b : B, ∑ c : C, f a b c) =
      ∑ c : C, ∑ a : A, ∑ b : B, f a b c := by
  calc
    _ = ∑ a : A, ∑ c : C, ∑ b : B, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c : C, ∑ a : A, ∑ b : B, f a b c := Finset.sum_comm

/-- Reverse the order of a finite triple sum. -/
theorem sum_three_reverse {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℂ) :
    (∑ a : A, ∑ b : B, ∑ c : C, f a b c) =
      ∑ c : C, ∑ b : B, ∑ a : A, f a b c := by
  calc
    _ = ∑ a : A, ∑ c : C, ∑ b : B, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c : C, ∑ a : A, ∑ b : B, f a b c := Finset.sum_comm
    _ = ∑ c : C, ∑ b : B, ∑ a : A, f a b c := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

/-- Gauge averaging one raw edge-representation coefficient is exactly a
linear combination of the explicit vertex-intertwiner contractions in that
edge block. -/
theorem gaugeAverage_normalizedEdgeCoefficient
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E)
    (row col : (e : E) → Fin (D.dimension (π e))) (g : E → G) :
    (Fintype.card (V → G) : ℂ)⁻¹ *
        ∑ h : V → G,
          normalizedEdgeCoefficient D π row col (NCG.gaugeAct t s h g) =
      ∑ a : (v : V) → IntertwinerIndex D t s π v,
        (∏ v : V,
          (vertexIntertwinerBasis D t s π v (a v)).1.ofLp
            (vertexTensorIndexOf D t s π row col v)) *
          contractedSpinFunction D t s (labelOf D t s π a) g := by
  classical
  simp_rw [normalizedEdgeCoefficient_gauge_expand]
  simp_rw [edge_transport_product_factor]
  calc
    (Fintype.card (V → G) : ℂ)⁻¹ *
        (∑ h : V → G,
          ∑ q : (e : E) → Fin (D.dimension (π e)),
          ∑ p : (e : E) → Fin (D.dimension (π e)),
            (∏ v : V,
              vertexActionMatrix D t s π v (h v)
                (vertexTensorIndexOf D t s π row col v)
                (vertexTensorIndexOf D t s π p q v)) *
              normalizedEdgeCoefficient D π p q g) =
      ∑ p : (e : E) → Fin (D.dimension (π e)),
      ∑ q : (e : E) → Fin (D.dimension (π e)),
        ((Fintype.card (V → G) : ℂ)⁻¹ *
          ∑ h : V → G, ∏ v : V,
            vertexActionMatrix D t s π v (h v)
              (vertexTensorIndexOf D t s π row col v)
              (vertexTensorIndexOf D t s π p q v)) *
            normalizedEdgeCoefficient D π p q g := by
      simp_rw [Finset.mul_sum]
      rw [sum_three_reverse]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = ∑ p : (e : E) → Fin (D.dimension (π e)),
      ∑ q : (e : E) → Fin (D.dimension (π e)),
        (∏ v : V, vertexReynoldsMatrix D t s π v
          (vertexTensorIndexOf D t s π row col v)
          (vertexTensorIndexOf D t s π p q v)) *
            normalizedEdgeCoefficient D π p q g := by
      simp_rw [globalVertexAverage_eq_prod_reynolds]
    _ = ∑ p : (e : E) → Fin (D.dimension (π e)),
      ∑ q : (e : E) → Fin (D.dimension (π e)),
      ∑ a : (v : V) → IntertwinerIndex D t s π v,
        ((∏ v : V,
          (vertexIntertwinerBasis D t s π v (a v)).1.ofLp
            (vertexTensorIndexOf D t s π row col v)) *
        (∏ v : V,
          star ((vertexIntertwinerBasis D t s π v (a v)).1.ofLp
            (vertexTensorIndexOf D t s π p q v)))) *
          normalizedEdgeCoefficient D π p q g := by
      simp_rw [prod_vertexReynolds_eq_sum_intertwiners, Finset.sum_mul]
    _ = ∑ a : (v : V) → IntertwinerIndex D t s π v,
        (∏ v : V,
          (vertexIntertwinerBasis D t s π v (a v)).1.ofLp
            (vertexTensorIndexOf D t s π row col v)) *
          contractedSpinFunction D t s (labelOf D t s π a) g := by
      rw [sum_three_last_to_front]
      apply Finset.sum_congr rfl
      intro a _
      simp only [contractedSpinFunction, vertexContraction, labelOf]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ac_rfl


/-- Orthogonal group average on the full finite holonomy Hilbert space. -/
noncomputable def gaugeAverageVector (t s : E → V)
    (F : EuclideanSpace ℂ (E → G)) : EuclideanSpace ℂ (E → G) :=
  WithLp.toLp 2 (fun g => (Fintype.card (V → G) : ℂ)⁻¹ *
    ∑ h : V → G, F.ofLp (NCG.gaugeAct t s h g))

/-- Gauge averaging is a linear endomorphism. -/
noncomputable def gaugeAverageLinearMap (t s : E → V) :
    EuclideanSpace ℂ (E → G) →ₗ[ℂ] EuclideanSpace ℂ (E → G) where
  toFun := gaugeAverageVector t s
  map_add' F K := by
    apply WithLp.ofLp_injective 2
    funext g
    simp only [gaugeAverageVector, WithLp.ofLp_toLp, WithLp.ofLp_add,
      Pi.add_apply, Finset.sum_add_distrib]
    rw [mul_add]
  map_smul' c F := by
    apply WithLp.ofLp_injective 2
    funext g
    simp only [gaugeAverageVector, WithLp.ofLp_toLp, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    simp only [RingHom.id_apply]
    ring

theorem gaugeAverageLinearMap_apply (t s : E → V)
    (F : EuclideanSpace ℂ (E → G)) :
    gaugeAverageLinearMap t s F = gaugeAverageVector t s F := rfl

/-- The group average fixes every gauge-invariant vector. -/
theorem gaugeAverageVector_eq_of_invariant (t s : E → V)
    (F : EuclideanSpace ℂ (E → G))
    (hF : ∀ (h : V → G) (g : E → G),
      F.ofLp (NCG.gaugeAct t s h g) = F.ofLp g) :
    gaugeAverageVector t s F = F := by
  apply WithLp.ofLp_injective 2
  exact (NCG.spin_network (G := G) t s).2.2.2 F.ofLp |>.1 hF

/-- Coefficient of a contracted invariant vector when averaging one matrix
coefficient in a fixed edge-representation block. -/
noncomputable def initialIntertwinerCoefficient
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (rc : EdgeMatrixIndex D π)
    (a : (v : V) → IntertwinerIndex D t s π v) : ℂ :=
  ∏ v : V, (vertexIntertwinerBasis D t s π v (a v)).1.ofLp
    (vertexTensorIndexOf D t s π rc.1 rc.2 v)

/-- Exact Hilbert-normalized expansion of the averaged edge Peter--Weyl
coefficient into the contracted invariant family. -/
theorem gaugeAverage_peterWeylEdgeVector_fixedBlock
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (π : EdgeRepresentationLabel D E) (rc : EdgeMatrixIndex D π) :
    gaugeAverageVector t s
        (peterWeylEdgeVector D E (edgeCoefficientIndexOf D π rc)) =
      ∑ a : (v : V) → IntertwinerIndex D t s π v,
        initialIntertwinerCoefficient D t s π rc a •
          contractedPeterWeylVector D t s (labelOf D t s π a) := by
  classical
  apply WithLp.ofLp_injective 2
  funext g
  simp only [gaugeAverageVector, WithLp.ofLp_toLp, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    peterWeylEdgeVector_apply, edgeCoefficientIndexOf]
  change (Fintype.card (V → G) : ℂ)⁻¹ *
      ∑ h : V → G,
        ∏ e : E, peterWeylCoefficient D (π e) (rc.1 e) (rc.2 e)
          (NCG.gaugeAct t s h g e) =
    ∑ a : (v : V) → IntertwinerIndex D t s π v,
      initialIntertwinerCoefficient D t s π rc a *
        contractedPeterWeylVector D t s (labelOf D t s π a) g
  simp_rw [peterWeylEdgeProduct_eq_scale_mul]
  calc
    (Fintype.card (V → G) : ℂ)⁻¹ *
        ∑ h : V → G,
          edgePeterWeylScale D π *
            normalizedEdgeCoefficient D π rc.1 rc.2
              (NCG.gaugeAct t s h g) =
      edgePeterWeylScale D π *
        ((Fintype.card (V → G) : ℂ)⁻¹ *
          ∑ h : V → G,
            normalizedEdgeCoefficient D π rc.1 rc.2
              (NCG.gaugeAct t s h g)) := by
      rw [← Finset.mul_sum]
      ring
    _ = edgePeterWeylScale D π *
        ∑ a : (v : V) → IntertwinerIndex D t s π v,
          initialIntertwinerCoefficient D t s π rc a *
            contractedSpinFunction D t s (labelOf D t s π a) g := by
      rw [gaugeAverage_normalizedEdgeCoefficient]
      rfl
    _ = ∑ a : (v : V) → IntertwinerIndex D t s π v,
      initialIntertwinerCoefficient D t s π rc a *
        contractedPeterWeylVector D t s (labelOf D t s π a) g := by
      simp_rw [contractedPeterWeylVector_eq_scale_mul]
      rw [Finset.mul_sum]
      simp only [labelOf_edgeRepresentation]
      apply Finset.sum_congr rfl
      intro a _
      ac_rfl

/-- Recover the representation component of an arbitrary edgewise
Peter--Weyl coefficient label. -/
def edgeRepresentationOfCoefficientLabel
    (D : MatrixBlockDecomposition G) (label : E → CoefficientIndex D) :
    EdgeRepresentationLabel D E := fun e => (label e).1

/-- Recover all row and column indices of an arbitrary edgewise coefficient
label. -/
def edgeMatrixIndexOfCoefficientLabel
    (D : MatrixBlockDecomposition G) (label : E → CoefficientIndex D) :
    EdgeMatrixIndex D (edgeRepresentationOfCoefficientLabel D label) :=
  ⟨fun e => (label e).2.1, fun e => (label e).2.2⟩

/-- Recombining the recovered block, row, and column data returns the
original edgewise coefficient label. -/
@[simp] theorem edgeCoefficientIndexOf_edgeMatrixIndexOfCoefficientLabel
    (D : MatrixBlockDecomposition G) (label : E → CoefficientIndex D) :
    edgeCoefficientIndexOf D (edgeRepresentationOfCoefficientLabel D label)
      (edgeMatrixIndexOfCoefficientLabel D label) = label := by
  funext e
  simpa [edgeCoefficientIndexOf, edgeRepresentationOfCoefficientLabel,
    edgeMatrixIndexOfCoefficientLabel] using Sigma.eta (label e)

/-- The averaged expansion for an arbitrary edgewise Peter--Weyl label. -/
theorem gaugeAverage_peterWeylEdgeVector
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (label : E → CoefficientIndex D) :
    gaugeAverageVector t s (peterWeylEdgeVector D E label) =
      ∑ a : (v : V) → IntertwinerIndex D t s
          (edgeRepresentationOfCoefficientLabel D label) v,
        initialIntertwinerCoefficient D t s
            (edgeRepresentationOfCoefficientLabel D label)
            (edgeMatrixIndexOfCoefficientLabel D label) a •
          contractedPeterWeylVector D t s
            (labelOf D t s (edgeRepresentationOfCoefficientLabel D label) a) := by
  simpa using gaugeAverage_peterWeylEdgeVector_fixedBlock D t s
    (edgeRepresentationOfCoefficientLabel D label)
    (edgeMatrixIndexOfCoefficientLabel D label)

/-- The averaged Peter--Weyl coefficient, bundled in the invariant subspace
through its explicit intertwiner expansion. -/
noncomputable def averagedPeterWeylInvariantVector
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (label : E → CoefficientIndex D) : GaugeInvariantSubspace (G := G) t s :=
  ∑ a : (v : V) → IntertwinerIndex D t s
      (edgeRepresentationOfCoefficientLabel D label) v,
    initialIntertwinerCoefficient D t s
        (edgeRepresentationOfCoefficientLabel D label)
        (edgeMatrixIndexOfCoefficientLabel D label) a •
      contractedPeterWeylInvariantVector D t s
        (labelOf D t s (edgeRepresentationOfCoefficientLabel D label) a)

/-- The underlying function of the bundled average is the group average. -/
@[simp] theorem averagedPeterWeylInvariantVector_coe
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (label : E → CoefficientIndex D) :
    (averagedPeterWeylInvariantVector D t s label).1 =
      gaugeAverageVector t s (peterWeylEdgeVector D E label) := by
  rw [gaugeAverage_peterWeylEdgeVector D t s label]
  simp [averagedPeterWeylInvariantVector]

/-- Each averaged Peter--Weyl coefficient belongs to the span of the
explicit contracted invariant vectors. -/
theorem averagedPeterWeylInvariantVector_mem_span
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (label : E → CoefficientIndex D) :
    averagedPeterWeylInvariantVector D t s label ∈
      Submodule.span ℂ (Set.range (contractedPeterWeylInvariantVector D t s)) := by
  classical
  unfold averagedPeterWeylInvariantVector
  apply Submodule.sum_mem
  intro a _
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self _)

/-- The explicit contracted spin-network family spans the entire finite
gauge-invariant Hilbert space. -/
theorem contractedPeterWeylInvariantVector_span_eq_top
    (D : MatrixBlockDecomposition G) (t s : E → V) :
    Submodule.span ℂ (Set.range (contractedPeterWeylInvariantVector D t s)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  let b := peterWeylEdgeOrthonormalBasis D E
  let coeff : (E → CoefficientIndex D) → ℂ :=
    fun label => (b.repr f.1).ofLp label
  have hpw :
      (∑ label : E → CoefficientIndex D,
          coeff label • peterWeylEdgeVector D E label) = f.1 := by
    simpa only [coeff, b, peterWeylEdgeOrthonormalBasis_apply] using
      b.sum_repr f.1
  have havg : gaugeAverageVector t s f.1 = f.1 :=
    gaugeAverageVector_eq_of_invariant t s f.1 f.2
  have hfull :
      (∑ label : E → CoefficientIndex D,
          coeff label • gaugeAverageVector t s
            (peterWeylEdgeVector D E label)) = f.1 := by
    calc
      _ = gaugeAverageLinearMap t s
          (∑ label : E → CoefficientIndex D,
            coeff label • peterWeylEdgeVector D E label) := by
              simp [gaugeAverageLinearMap_apply]
      _ = gaugeAverageLinearMap t s f.1 := by rw [hpw]
      _ = f.1 := by simpa [gaugeAverageLinearMap_apply] using havg
  have hsub :
      (∑ label : E → CoefficientIndex D,
          coeff label • averagedPeterWeylInvariantVector D t s label) = f := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul,
      averagedPeterWeylInvariantVector_coe] using hfull
  rw [← hsub]
  apply Submodule.sum_mem
  intro label _
  exact Submodule.smul_mem _ _
    (averagedPeterWeylInvariantVector_mem_span D t s label)


/-- A spin-network label is the dependent pair of its edge representation
field and its vertex-intertwiner field. -/
def labelSigmaEquiv (D : MatrixBlockDecomposition G) (t s : E → V) :
    Label D t s ≃
      Σ π : EdgeRepresentationLabel D E,
        (v : V) → IntertwinerIndex D t s π v where
  toFun L := ⟨L.edgeRepresentation, L.vertexIntertwiner⟩
  invFun x := labelOf D t s x.1 x.2
  left_inv L := by cases L; rfl
  right_inv x := by cases x; rfl

/-- Canonical finite enumeration of the dependent spin-network labels. -/
noncomputable instance labelFintype
    (D : MatrixBlockDecomposition G) (t s : E → V) :
    Fintype (Label D t s) :=
  Fintype.ofEquiv
    (Σ π : EdgeRepresentationLabel D E,
      (v : V) → IntertwinerIndex D t s π v)
    (labelSigmaEquiv D t s).symm

/-- The edge-irrep/vertex-intertwiner labels index an explicit orthonormal
basis of the complete gauge-invariant Hilbert space. -/
noncomputable def contractedPeterWeylInvariantOrthonormalBasis
    (D : MatrixBlockDecomposition G) (t s : E → V) :
    OrthonormalBasis (Label D t s) ℂ (GaugeInvariantSubspace (G := G) t s) :=
  OrthonormalBasis.mk
    (contractedPeterWeylInvariantVector_orthonormal D t s)
    (contractedPeterWeylInvariantVector_span_eq_top D t s).ge

@[simp] theorem contractedPeterWeylInvariantOrthonormalBasis_apply
    (D : MatrixBlockDecomposition G) (t s : E → V) (L : Label D t s) :
    contractedPeterWeylInvariantOrthonormalBasis D t s L =
      contractedPeterWeylInvariantVector D t s L := by
  simp [contractedPeterWeylInvariantOrthonormalBasis]

/-- Unitary coefficient transform in the explicit spin-network basis. -/
noncomputable def explicitSpinNetworkCoefficientTransform
    (D : MatrixBlockDecomposition G) (t s : E → V) :
    GaugeInvariantSubspace (G := G) t s ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Label D t s) :=
  (contractedPeterWeylInvariantOrthonormalBasis D t s).repr

/-- Every invariant function has its exact finite expansion in the explicit
contracted spin-network basis. -/
theorem explicitSpinNetworkExpansion
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (f : GaugeInvariantSubspace (G := G) t s) :
    f = ∑ L : Label D t s,
      ((explicitSpinNetworkCoefficientTransform D t s f).ofLp L) •
        contractedPeterWeylInvariantVector D t s L := by
  simpa only [explicitSpinNetworkCoefficientTransform,
    contractedPeterWeylInvariantOrthonormalBasis_apply] using
      ((contractedPeterWeylInvariantOrthonormalBasis D t s).sum_repr f).symm




end NCG.FiniteSpinNetwork
