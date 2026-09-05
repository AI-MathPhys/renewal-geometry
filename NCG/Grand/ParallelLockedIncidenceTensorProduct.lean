/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LockedOddPauli
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Parallel locked-incidence tensor products

This module supplies the multi-edge clause of
`cor:locked-odd-incidence-factor`.  Each normalized odd route gives a copy of
`M₂(ℂ)` by `LockedOddPauli`.  Here a faithful Hilbert–Schmidt residual on
the two families of matrix units is proved to vanish exactly when the two
factor ranges commute.  The algebra tensor-product universal property then
constructs the simultaneous incidence representation.
-/

namespace NCG

open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The image commutator of a pair of standard matrix units from two proposed
incidence factors. -/
noncomputable def incidenceMatrixUnitCommutator
    (left right : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix n n ℂ)
    (q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) : Matrix n n ℂ :=
  left (Matrix.single q.1.1 q.1.2 1) *
      right (Matrix.single q.2.1 q.2.2 1) -
    right (Matrix.single q.2.1 q.2.2 1) *
      left (Matrix.single q.1.1 q.1.2 1)

/-- Cross-edge residual over complete matrix-unit bases. -/
noncomputable def parallelIncidenceCommutatorDefect
    (left right : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix n n ℂ) : ℂ :=
  ∑ q, (Matrix.conjTranspose (incidenceMatrixUnitCommutator left right q) *
    incidenceMatrixUnitCommutator left right q).trace

theorem parallelIncidenceCommutatorDefect_eq_zero_iff
    (left right : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix n n ℂ) :
    parallelIncidenceCommutatorDefect left right = 0 ↔
      ∀ a b c d : Fin 2,
        Commute (left (Matrix.single a b 1))
          (right (Matrix.single c d 1)) := by
  let D := incidenceMatrixUnitCommutator left right
  have hnonneg : ∀ q ∈
      (Finset.univ : Finset ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))),
      0 ≤ (Matrix.conjTranspose (D q) * D q).trace := by
    intro q _
    exact (Matrix.posSemidef_conjTranspose_mul_self (D q)).trace_nonneg
  constructor
  · intro hzero a b c d
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    have htrace := hall ((a, b), (c, d)) (Finset.mem_univ _)
    have hD : D ((a, b), (c, d)) = 0 :=
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htrace
    exact sub_eq_zero.mp hD
  · intro hcomm
    unfold parallelIncidenceCommutatorDefect
    apply Finset.sum_eq_zero
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _
    have hz : incidenceMatrixUnitCommutator left right ((a, b), (c, d)) = 0 :=
      sub_eq_zero.mpr (hcomm a b c d).eq
    rw [hz]
    simp

/-- Commutation on the complete matrix-unit bases propagates by linearity to
the full two matrix algebras. -/
theorem matrixUnitRanges_commute
    (left right : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix n n ℂ)
    (hbasis : ∀ a b c d : Fin 2,
      Commute (left (Matrix.single a b 1))
        (right (Matrix.single c d 1))) :
    ∀ A B, Commute (left A) (right B) := by
  have hsingle : ∀ a b c d : Fin 2, ∀ x y : ℂ,
      Commute (left (Matrix.single a b x))
        (right (Matrix.single c d y)) := by
    intro a b c d x y
    have hx : Matrix.single a b x = x • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single]
      simp
    have hy : Matrix.single c d y = y • Matrix.single c d (1 : ℂ) := by
      rw [Matrix.smul_single]
      simp
    rw [hx, hy, map_smul, map_smul]
    show Commute (x • left (Matrix.single a b 1))
      (y • right (Matrix.single c d 1))
    have h := (hbasis a b c d).eq
    show (x • left (Matrix.single a b 1)) *
        (y • right (Matrix.single c d 1)) =
      (y • right (Matrix.single c d 1)) *
        (x • left (Matrix.single a b 1))
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [h]
    ring_nf
  intro A B
  rw [Matrix.matrix_eq_sum_single A, map_sum]
  apply Commute.sum_left Finset.univ _ (right B)
  intro a _
  rw [map_sum]
  apply Commute.sum_left Finset.univ _ (right B)
  intro b _
  rw [Matrix.matrix_eq_sum_single B, map_sum]
  apply Commute.sum_right Finset.univ _ (left (Matrix.single a b (A a b)))
  intro c _
  rw [map_sum]
  apply Commute.sum_right Finset.univ _ (left (Matrix.single a b (A a b)))
  intro d _
  exact hsingle a b c d (A a b) (B c d)

/-- Vanishing cross-edge residual canonically produces the simultaneous
algebra representation of the tensor product of the two Pauli factors. -/
noncomputable def parallelLockedIncidenceTensorProductMap
    (left right : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix n n ℂ)
    (hzero : parallelIncidenceCommutatorDefect left right = 0) :
    TensorProduct ℂ (Matrix (Fin 2) (Fin 2) ℂ)
        (Matrix (Fin 2) (Fin 2) ℂ) →ₐ[ℂ] Matrix n n ℂ :=
  Algebra.TensorProduct.lift left right
    (matrixUnitRanges_commute left right
      ((parallelIncidenceCommutatorDefect_eq_zero_iff left right).mp hzero))

theorem parallelLockedIncidenceTensorProductMap_tmul
    (left right : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix n n ℂ)
    (hzero : parallelIncidenceCommutatorDefect left right = 0)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    parallelLockedIncidenceTensorProductMap left right hzero
        (TensorProduct.tmul ℂ A B) = left A * right B := by
  exact Algebra.TensorProduct.lift_tmul left right _ A B

/-- If a third factor commutes with each of two factor ranges, it commutes with
the range of their tensor-product lift.  This is the induction step for any
finite parallel incidence packet. -/
theorem tensorProductLift_range_commutes_third
    (first second third :
      Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix n n ℂ)
    (hfirstSecond : ∀ A B, Commute (first A) (second B))
    (hfirstThird : ∀ A C, Commute (first A) (third C))
    (hsecondThird : ∀ B C, Commute (second B) (third C)) :
    ∀ T C, Commute
      (Algebra.TensorProduct.lift first second hfirstSecond T) (third C) := by
  intro T C
  induction T using TensorProduct.induction_on with
  | zero => exact Commute.zero_left _
  | tmul A B =>
      rw [Algebra.TensorProduct.lift_tmul]
      exact (hfirstThird A C).mul_left (hsecondThird B C)
  | add X Y hX hY =>
      rw [map_add]
      exact hX.add_left hY

/-- Three pairwise-zero cross-edge residuals produce the iterated
three-factor incidence representation.  Repeating the preceding induction
step gives the same construction for every finite number of edges. -/
noncomputable def parallelLockedIncidenceThreeFactorMap
    (first second third :
      Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix n n ℂ)
    (hfirstSecond : parallelIncidenceCommutatorDefect first second = 0)
    (hfirstThird : parallelIncidenceCommutatorDefect first third = 0)
    (hsecondThird : parallelIncidenceCommutatorDefect second third = 0) :
    TensorProduct ℂ
        (TensorProduct ℂ (Matrix (Fin 2) (Fin 2) ℂ)
          (Matrix (Fin 2) (Fin 2) ℂ))
        (Matrix (Fin 2) (Fin 2) ℂ) →ₐ[ℂ] Matrix n n ℂ := by
  let h₁₂ := matrixUnitRanges_commute first second
    ((parallelIncidenceCommutatorDefect_eq_zero_iff first second).mp hfirstSecond)
  let h₁₃ := matrixUnitRanges_commute first third
    ((parallelIncidenceCommutatorDefect_eq_zero_iff first third).mp hfirstThird)
  let h₂₃ := matrixUnitRanges_commute second third
    ((parallelIncidenceCommutatorDefect_eq_zero_iff second third).mp hsecondThird)
  exact Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift first second h₁₂) third
    (tensorProductLift_range_commutes_third first second third h₁₂ h₁₃ h₂₃)

/-- Exact two-edge equivalence: a zero matrix-unit residual is precisely the
condition needed for commuting Pauli factors and hence for the canonical
tensor-product incidence map. -/
theorem parallelLockedIncidenceTensorProductCertificate
    (left right : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix n n ℂ) :
    parallelIncidenceCommutatorDefect left right = 0 ↔
      (∀ A B, Commute (left A) (right B)) := by
  constructor
  · intro hzero
    exact matrixUnitRanges_commute left right
      ((parallelIncidenceCommutatorDefect_eq_zero_iff left right).mp hzero)
  · intro hcomm
    apply (parallelIncidenceCommutatorDefect_eq_zero_iff left right).mpr
    intro a b c d
    exact hcomm _ _

end NCG
