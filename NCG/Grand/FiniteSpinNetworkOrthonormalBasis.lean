/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSpinNetworkBasis

/-!
# Global orthonormality of explicit finite spin networks

This module combines fixed-block intertwiner orthonormality with orthogonality
of distinct edge-representation fields.
-/

namespace NCG.FiniteSpinNetwork

open NCG.FinitePeterWeyl

variable {G V E : Type*} [Group G] [Fintype G] [Fintype V]
  [Fintype E] [DecidableEq V] [DecidableEq E]

theorem edgeCoefficientIndexOf_ne_of_representation_ne
    (D : MatrixBlockDecomposition G)
    {π ρ : EdgeRepresentationLabel D E} (hπρ : π ≠ ρ)
    (rc : EdgeMatrixIndex D π) (rc' : EdgeMatrixIndex D ρ) :
    edgeCoefficientIndexOf D π rc ≠ edgeCoefficientIndexOf D ρ rc' := by
  intro h
  apply hπρ
  funext e
  have he := congrFun h e
  exact (Sigma.mk.inj_iff.mp he).1

/-- Contracted vectors in distinct edge-representation blocks are
orthogonal. -/
theorem contractedPeterWeylVector_cross_inner
    (D : MatrixBlockDecomposition G) (t s : E → V)
    {π ρ : EdgeRepresentationLabel D E} (hπρ : π ≠ ρ)
    (a : (v : V) → IntertwinerIndex D t s π v)
    (b : (v : V) → IntertwinerIndex D t s ρ v) :
    inner ℂ
      (contractedPeterWeylVector D t s (labelOf D t s π a))
      (contractedPeterWeylVector D t s (labelOf D t s ρ b)) = 0 := by
  classical
  unfold contractedPeterWeylVector
  simp only [labelOf_edgeRepresentation, vertexContraction_labelOf]
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  have hedge := peterWeylEdgeVector_orthonormal D E
  simp_rw [hedge.inner_eq_zero
    (edgeCoefficientIndexOf_ne_of_representation_ne D hπρ _ _)]
  simp

/-- The explicit edge-irrep/vertex-intertwiner contractions are mutually
orthonormal in the full holonomy Hilbert space. -/
theorem contractedPeterWeylVector_orthonormal
    (D : MatrixBlockDecomposition G) (t s : E → V) :
    Orthonormal ℂ (contractedPeterWeylVector D t s) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨π, a⟩ ⟨ρ, b⟩
  change inner ℂ
      (contractedPeterWeylVector D t s (labelOf D t s π a))
      (contractedPeterWeylVector D t s (labelOf D t s ρ b)) =
    if (labelOf D t s π a) = labelOf D t s ρ b then 1 else 0
  by_cases hπρ : π = ρ
  · subst ρ
    have hfixed := orthonormal_iff_ite.mp
      (contractedPeterWeylVector_fixedBlock_orthonormal D t s π) a b
    rw [hfixed]
    by_cases hab : a = b
    · subst b
      simp
    · have hlabel : (labelOf D t s π a) ≠ labelOf D t s π b := by
        intro h
        apply hab
        cases h
        rfl
      simp [hab, hlabel]
  · rw [contractedPeterWeylVector_cross_inner D t s hπρ a b]
    have hlabel : (labelOf D t s π a) ≠ labelOf D t s ρ b := by
      intro h
      exact hπρ (congrArg Label.edgeRepresentation h)
    simp [hlabel]

/-- Product of the one-edge Peter--Weyl scale factors in a representation
block. -/
noncomputable def edgePeterWeylScale
    (D : MatrixBlockDecomposition G) (π : EdgeRepresentationLabel D E) : ℂ :=
  ∏ e : E, (peterWeylScale D (π e) : ℂ)

theorem peterWeylEdgeProduct_eq_scale_mul
    (D : MatrixBlockDecomposition G) (π : EdgeRepresentationLabel D E)
    (row col : (e : E) → Fin (D.dimension (π e))) (g : E → G) :
    (∏ e : E, peterWeylCoefficient D (π e) (row e) (col e) (g e)) =
      edgePeterWeylScale D π *
        normalizedEdgeCoefficient D π row col g := by
  simp only [peterWeylCoefficient, edgePeterWeylScale,
    normalizedEdgeCoefficient]
  rw [Finset.prod_mul_distrib]

/-- The Hilbert-normalized contraction is the raw gauge-invariant contraction
times the product of the one-edge Peter--Weyl scales. -/
theorem contractedPeterWeylVector_eq_scale_mul
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s) (g : E → G) :
    contractedPeterWeylVector D t s L g =
      edgePeterWeylScale D L.edgeRepresentation *
        contractedSpinFunction D t s L g := by
  rw [contractedPeterWeylVector_apply, Fintype.sum_prod_type]
  unfold contractedSpinFunction
  simp_rw [peterWeylEdgeProduct_eq_scale_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col _
  ring

/-- Every Hilbert-normalized explicit contraction is gauge invariant. -/
theorem contractedPeterWeylVector_gaugeInvariant
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s) (h : V → G) (g : E → G) :
    contractedPeterWeylVector D t s L (NCG.gaugeAct t s h g) =
      contractedPeterWeylVector D t s L g := by
  rw [contractedPeterWeylVector_eq_scale_mul,
    contractedPeterWeylVector_eq_scale_mul,
    contractedSpinFunction_gaugeInvariant]

/-- A normalized explicit spin network bundled in the gauge-invariant Hilbert
subspace. -/
noncomputable def contractedPeterWeylInvariantVector
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s) : GaugeInvariantSubspace (G := G) t s :=
  ⟨contractedPeterWeylVector D t s L,
    contractedPeterWeylVector_gaugeInvariant D t s L⟩

@[simp] theorem contractedPeterWeylInvariantVector_coe
    (D : MatrixBlockDecomposition G) (t s : E → V)
    (L : Label D t s) :
    (contractedPeterWeylInvariantVector D t s L).1 =
      contractedPeterWeylVector D t s L := rfl

/-- The explicit edge-irrep/vertex-intertwiner family is orthonormal inside
the gauge-invariant Hilbert subspace itself. -/
theorem contractedPeterWeylInvariantVector_orthonormal
    (D : MatrixBlockDecomposition G) (t s : E → V) :
    Orthonormal ℂ (contractedPeterWeylInvariantVector D t s) := by
  classical
  rw [orthonormal_iff_ite]
  intro L K
  rw [Submodule.coe_inner]
  exact orthonormal_iff_ite.mp
    (contractedPeterWeylVector_orthonormal D t s) L K

end NCG.FiniteSpinNetwork

