/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSchurOrthogonality
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Normalized finite Peter--Weyl orthonormal bases

Counting-measure normalization of the Schur-orthogonal matrix coefficients,
followed by the explicit one-edge and finite-edge-set orthonormal bases.
-/

namespace NCG.FinitePeterWeyl

variable {G : Type*} [Group G] [Fintype G]

noncomputable def peterWeylScale
    (D : MatrixBlockDecomposition G) (i : Fin D.count) : ℝ :=
  Real.sqrt ((D.dimension i : ℝ) / Fintype.card G)

theorem peterWeylScale_sq_mul_card_div_dimension
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    ((peterWeylScale D i : ℂ) ^ 2) *
      ((Fintype.card G : ℂ) / D.dimension i) = 1 := by
  have hdimR : (0 : ℝ) < D.dimension i := by
    exact_mod_cast Nat.pos_of_ne_zero (D.dimension_neZero i).out
  have hcardR : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos
  have hsquare : peterWeylScale D i ^ 2 =
      (D.dimension i : ℝ) / Fintype.card G := by
    rw [peterWeylScale, Real.sq_sqrt]
    positivity
  have hsquareC : ((peterWeylScale D i : ℂ) ^ 2) =
      (D.dimension i : ℂ) / Fintype.card G := by
    calc
      ((peterWeylScale D i : ℂ) ^ 2) =
          ((peterWeylScale D i ^ 2 : ℝ) : ℂ) := by norm_num
      _ = (((D.dimension i : ℝ) / Fintype.card G : ℝ) : ℂ) :=
        congrArg (fun x : ℝ => (x : ℂ)) hsquare
      _ = (D.dimension i : ℂ) / Fintype.card G := by norm_num
  have hdimC : (D.dimension i : ℂ) ≠ 0 := by
    exact_mod_cast (D.dimension_neZero i).out
  rw [hsquareC]
  field_simp [hdimC]

/-- A unit-norm matrix coefficient in counting measure. -/
noncomputable def peterWeylCoefficient
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (a b : Fin (D.dimension i)) (g : G) : ℂ :=
  (peterWeylScale D i : ℂ) * normalizedBlockMatrix D i g a b

/-- Exact same-block orthonormality of normalized matrix coefficients. -/
theorem peterWeylCoefficient_same_orthonormality
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (a b c d : Fin (D.dimension i)) :
    (∑ g : G, star (peterWeylCoefficient D i a b g) *
      peterWeylCoefficient D i c d g) =
      if a = c ∧ b = d then 1 else 0 := by
  have hfactor : ∀ g : G,
      star (peterWeylCoefficient D i a b g) *
          peterWeylCoefficient D i c d g =
        ((peterWeylScale D i : ℂ) ^ 2) *
          (star (normalizedBlockMatrix D i g a b) *
            normalizedBlockMatrix D i g c d) := by
    intro g
    simp [peterWeylCoefficient]
    ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum, normalizedBlockMatrix_same_orthogonality]
  by_cases h : a = c ∧ b = d
  · simp only [if_pos h]
    simpa [mul_assoc] using peterWeylScale_sq_mul_card_div_dimension D i
  · simp [h]

/-- Exact cross-block orthogonality of normalized matrix coefficients. -/
theorem peterWeylCoefficient_cross_orthogonality
    (D : MatrixBlockDecomposition G) {i j : Fin D.count} (hji : j ≠ i)
    (a b : Fin (D.dimension i)) (c d : Fin (D.dimension j)) :
    (∑ g : G, star (peterWeylCoefficient D i a b g) *
      peterWeylCoefficient D j c d g) = 0 := by
  have hfactor : ∀ g : G,
      star (peterWeylCoefficient D i a b g) *
          peterWeylCoefficient D j c d g =
        ((peterWeylScale D i : ℂ) * peterWeylScale D j) *
          (star (normalizedBlockMatrix D i g a b) *
            normalizedBlockMatrix D j g c d) := by
    intro g
    simp [peterWeylCoefficient]
    ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum, normalizedBlockMatrix_cross_orthogonality D hji]
  simp

/-! ## The normalized one-edge Peter--Weyl basis -/

/-- A normalized matrix coefficient, regarded as a vector in counting-measure
`L²(G)`. -/
noncomputable def peterWeylVector
    (D : MatrixBlockDecomposition G) (idx : CoefficientIndex D) :
    EuclideanSpace ℂ G :=
  WithLp.toLp 2 (fun g =>
    peterWeylCoefficient D idx.1 idx.2.1 idx.2.2 g)

@[simp] theorem peterWeylVector_apply
    (D : MatrixBlockDecomposition G) (idx : CoefficientIndex D) (g : G) :
    peterWeylVector D idx g =
      peterWeylCoefficient D idx.1 idx.2.1 idx.2.2 g := rfl

/-- All normalized coefficients, across every irreducible block, are mutually
orthonormal in counting measure. -/
theorem peterWeylVector_orthonormal (D : MatrixBlockDecomposition G) :
    Orthonormal ℂ (peterWeylVector D) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, ⟨a, b⟩⟩ ⟨j, ⟨c, d⟩⟩
  simp only [PiLp.inner_apply, peterWeylVector_apply, RCLike.inner_apply']
  change
    (∑ g : G, star (peterWeylCoefficient D i a b g) *
      peterWeylCoefficient D j c d g) =
      if (⟨i, (a, b)⟩ : CoefficientIndex D) = ⟨j, (c, d)⟩ then 1 else 0
  by_cases hij : i = j
  · subst j
    rw [peterWeylCoefficient_same_orthonormality]
    by_cases hab : a = c ∧ b = d
    · obtain ⟨rfl, rfl⟩ := hab
      simp
    · have hidx :
          (⟨i, (a, b)⟩ : CoefficientIndex D) ≠ ⟨i, (c, d)⟩ := by
        simpa [Sigma.mk.inj_iff, Prod.ext_iff] using hab
      simp [hab, hidx]
  · have hji : j ≠ i := Ne.symm hij
    rw [peterWeylCoefficient_cross_orthogonality D hji]
    have hidx :
        (⟨i, (a, b)⟩ : CoefficientIndex D) ≠ ⟨j, (c, d)⟩ := by
      intro h
      exact hij (Sigma.mk.inj_iff.mp h).1
    simp [hidx]

/-- The dependent coefficient index has exactly `|G|` elements. -/
theorem coefficientIndex_card (D : MatrixBlockDecomposition G) :
    Fintype.card (CoefficientIndex D) = Fintype.card G := by
  simpa [Fintype.card_sigma, Fintype.card_prod, pow_two,
    Nat.card_eq_fintype_card] using (matrixBlock_dimension_count D).symm

/-- The normalized matrix coefficients form an explicit orthonormal basis of
all complex functions on the finite group. -/
noncomputable def peterWeylOrthonormalBasis
    (D : MatrixBlockDecomposition G) :
    OrthonormalBasis (CoefficientIndex D) ℂ (EuclideanSpace ℂ G) :=
  by
    have hspan :
        Submodule.span ℂ (Set.range (peterWeylVector D)) = ⊤ :=
      (peterWeylVector_orthonormal D).linearIndependent
        |>.span_eq_top_of_card_eq_finrank'
          (by rw [coefficientIndex_card D, finrank_euclideanSpace])
    exact OrthonormalBasis.mk (peterWeylVector_orthonormal D) hspan.ge

@[simp] theorem peterWeylOrthonormalBasis_apply
    (D : MatrixBlockDecomposition G) (idx : CoefficientIndex D) :
    peterWeylOrthonormalBasis D idx = peterWeylVector D idx := by
  simp [peterWeylOrthonormalBasis]


end NCG.FinitePeterWeyl
