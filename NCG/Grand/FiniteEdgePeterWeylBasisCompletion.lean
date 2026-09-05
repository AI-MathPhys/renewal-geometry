/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteEdgePeterWeylOrthonormalBasis

/-!
# Completeness of the edgewise finite Peter--Weyl basis
-/

namespace NCG.FinitePeterWeyl

variable {G : Type*} [Group G] [Fintype G]

/-- The normalized edgewise products form an explicit orthonormal basis of
all complex functions on the finite configuration space. -/
noncomputable def peterWeylEdgeOrthonormalBasis
    (D : MatrixBlockDecomposition G) (E : Type*) [Fintype E] [DecidableEq E] :
    OrthonormalBasis (E → CoefficientIndex D) ℂ
      (EuclideanSpace ℂ (E → G)) := by
  have hspan :
      Submodule.span ℂ (Set.range (peterWeylEdgeVector D E)) = ⊤ :=
    (peterWeylEdgeVector_orthonormal D E).linearIndependent
      |>.span_eq_top_of_card_eq_finrank'
        (by simp [coefficientIndex_card D, finrank_euclideanSpace])
  exact OrthonormalBasis.mk (peterWeylEdgeVector_orthonormal D E) hspan.ge

@[simp] theorem peterWeylEdgeOrthonormalBasis_apply
    (D : MatrixBlockDecomposition G) (E : Type*) [Fintype E] [DecidableEq E]
    (label : E → CoefficientIndex D) :
    peterWeylEdgeOrthonormalBasis D E label =
      peterWeylEdgeVector D E label := by
  simp [peterWeylEdgeOrthonormalBasis]

end NCG.FinitePeterWeyl

