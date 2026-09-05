/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FinitePeterWeylOrthonormalBasis

/-!
# Edgewise finite Peter--Weyl orthonormal basis

Tensor products of the normalized one-edge coefficients over a finite edge set.
-/

namespace NCG.FinitePeterWeyl

variable {G : Type*} [Group G] [Fintype G]

/-- Unified Kronecker-delta form of one-edge coefficient orthonormality. -/
theorem peterWeylCoefficient_inner
    (D : MatrixBlockDecomposition G) (x y : CoefficientIndex D) :
    (∑ g : G,
      star (peterWeylCoefficient D x.1 x.2.1 x.2.2 g) *
        peterWeylCoefficient D y.1 y.2.1 y.2.2 g) =
      if x = y then 1 else 0 := by
  simpa [PiLp.inner_apply, peterWeylVector_apply, RCLike.inner_apply', mul_comm] using
    (orthonormal_iff_ite.mp (peterWeylVector_orthonormal D) x y)

/-- Tensor product of normalized one-edge coefficients on a finite edge set. -/
noncomputable def peterWeylEdgeVector
    (D : MatrixBlockDecomposition G) (E : Type*) [Fintype E] [DecidableEq E]
    (label : E → CoefficientIndex D) :
    EuclideanSpace ℂ (E → G) :=
  WithLp.toLp 2 (fun g =>
    ∏ e : E, peterWeylCoefficient D
      (label e).1 (label e).2.1 (label e).2.2 (g e))

@[simp] theorem peterWeylEdgeVector_apply
    (D : MatrixBlockDecomposition G) (E : Type*) [Fintype E] [DecidableEq E]
    (label : E → CoefficientIndex D) (g : E → G) :
    peterWeylEdgeVector D E label g =
      ∏ e : E, peterWeylCoefficient D
        (label e).1 (label e).2.1 (label e).2.2 (g e) := rfl

/-- Edgewise Peter--Weyl products are an orthonormal family on `Gᴱ`. -/
theorem peterWeylEdgeVector_orthonormal
    (D : MatrixBlockDecomposition G) (E : Type*) [Fintype E] [DecidableEq E] :
    Orthonormal ℂ (peterWeylEdgeVector D E) := by
  classical
  rw [orthonormal_iff_ite]
  intro label label'
  simp only [PiLp.inner_apply, peterWeylEdgeVector_apply, RCLike.inner_apply',
    map_prod]
  simp_rw [← Finset.prod_mul_distrib]
  change
    (∑ g : E → G, ∏ e : E,
      star (peterWeylCoefficient D
        (label e).1 (label e).2.1 (label e).2.2 (g e)) *
      peterWeylCoefficient D
        (label' e).1 (label' e).2.1 (label' e).2.2 (g e)) =
      if label = label' then 1 else 0
  calc
    _ = ∏ e : E, ∑ g : G,
        star (peterWeylCoefficient D
          (label e).1 (label e).2.1 (label e).2.2 g) *
        peterWeylCoefficient D
          (label' e).1 (label' e).2.1 (label' e).2.2 g := by
      symm
      exact Fintype.prod_sum _
    _ = ∏ e : E, if label e = label' e then 1 else 0 := by
      apply Finset.prod_congr rfl
      intro e _
      exact peterWeylCoefficient_inner D (label e) (label' e)
    _ = if label = label' then 1 else 0 := by
      by_cases h : label = label'
      · subst label'
        simp
      · have hpoint : ∃ e, label e ≠ label' e := by
          simpa only [Function.ne_iff] using h
        obtain ⟨e, he⟩ := hpoint
        simp [h, Finset.prod_eq_zero (Finset.mem_univ e), he]


end NCG.FinitePeterWeyl
