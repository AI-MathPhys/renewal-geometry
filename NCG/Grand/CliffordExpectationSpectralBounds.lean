/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CliffordMatrixSpectralGap
import NCG.Grand.CliffordTwirlMatterAudit

/-!
# Sharp conditional-expectation bounds for Clifford matter

The primitive-cell spectral gap is lifted blockwise over an arbitrary finite
multiplicity carrier.  This proves the sharp conditional-expectation window
appearing in `thm:SMST-Clifford-twirl-matter`.
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace NCG
namespace CliffordExpectationSpectralBounds

open CommonOrigin
open CliffordMatrixSpectralGap
open CliffordTwirlMatterAudit

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

abbrev Block (m : Type*) :=
  Matrix (CliffordCarrier m) (CliffordCarrier m) ℂ

/-- The primitive `4 × 4` block at fixed multiplicity coordinates. -/
def externalSlice (X : Block m) (a b : m) : Matrix SMST4 SMST4 ℂ :=
  fun i j => X (i, a) (j, b)

theorem externalSlice_normalSeparationResidual (X : Block m) (a b : m) :
    externalSlice (NormalBranchPurityMargin.normalSeparationResidual X) a b =
      scalarResidual (externalSlice X a b) := by
  ext i j
  simp [externalSlice, NormalBranchPurityMargin.normalSeparationResidual,
    NormalBranchPurityMargin.normalSeparatedOperator,
    NormalBranchPurityMargin.normalizedNormalPartialTrace,
    scalarResidual, scalarExpectation, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.trace, Fintype.card_prod,
    Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst j
    simp
    ring
  · simp [hij]

theorem externalSlice_representedCommutator (X : Block m) (a b : m)
    (μ : Fin 4) :
    externalSlice (X * representedAxis μ - representedAxis μ * X) a b =
      gammaCommutator (externalSlice X a b) μ := by
  ext i j
  simp [externalSlice, representedAxis, gammaCommutator,
    Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply]

/-- Product-carrier Hilbert--Schmidt energy is the sum of the primitive slice
energies. -/
theorem productHilbertSchmidtInner_eq_sum_slice_trace (X : Block m) :
    NormalBranchPurityMargin.productHilbertSchmidtInner X X =
      ∑ a, ∑ b, Matrix.trace
        ((externalSlice X a b)ᴴ * externalSlice X a b) := by
  classical
  simp [NormalBranchPurityMargin.productHilbertSchmidtInner,
    externalSlice, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_lhs =>
    enter [2, i]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

/-- Sum of represented gamma-commutator Hilbert--Schmidt energies. -/
def representedCommutatorEnergy (X : Block m) : ℂ :=
  ∑ μ, Matrix.trace
    ((X * representedAxis μ - representedAxis μ * X)ᴴ *
      (X * representedAxis μ - representedAxis μ * X))

theorem representedCommutatorEnergy_eq_sum_slice (X : Block m) :
    representedCommutatorEnergy X =
      ∑ a, ∑ b, ∑ μ, Matrix.trace
        ((gammaCommutator (externalSlice X a b) μ)ᴴ *
          gammaCommutator (externalSlice X a b) μ) := by
  unfold representedCommutatorEnergy
  have htrace (μ : Fin 4) :
      Matrix.trace
          ((X * representedAxis μ - representedAxis μ * X)ᴴ *
            (X * representedAxis μ - representedAxis μ * X)) =
        NormalBranchPurityMargin.productHilbertSchmidtInner
          (X * representedAxis μ - representedAxis μ * X)
          (X * representedAxis μ - representedAxis μ * X) :=
    NormalBranchPurityMargin.trace_conjTranspose_mul_eq_productHilbertSchmidtInner _ _
  simp_rw [htrace, productHilbertSchmidtInner_eq_sum_slice_trace,
    externalSlice_representedCommutator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

/-- Sharp spectral window on `ℂ⁴ ⊗ M`. -/
theorem representedCommutatorEnergy_bounds (X : Block m) :
    (4 : ℂ) * commutantExpectationResidual X ≤ representedCommutatorEnergy X ∧
      representedCommutatorEnergy X ≤
        (16 : ℂ) * commutantExpectationResidual X := by
  have hres : commutantExpectationResidual X =
      ∑ a, ∑ b, Matrix.trace
        ((scalarResidual (externalSlice X a b))ᴴ *
          scalarResidual (externalSlice X a b)) := by
    unfold commutantExpectationResidual
    rw [productHilbertSchmidtInner_eq_sum_slice_trace]
    simp_rw [externalSlice_normalSeparationResidual]
  rw [hres, representedCommutatorEnergy_eq_sum_slice]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    exact (gammaCommutator_trace_bounds (externalSlice X a b)).1
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    exact (gammaCommutator_trace_bounds (externalSlice X a b)).2

/-- For an involution, the grading-automorphism residual is the commutator
followed by right multiplication by the unitary grading. -/
theorem representedCommutatorEnergy_eq_trivialResidual
    (J : Block m) (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    representedCommutatorEnergy J = trivialResidual J representedAxis := by
  unfold representedCommutatorEnergy trivialResidual
  apply Finset.sum_congr rfl
  intro μ _
  let C := J * representedAxis μ - representedAxis μ * J
  have hfactor : J * representedAxis μ * J - representedAxis μ = C * J := by
    symm
    unfold C
    rw [Matrix.sub_mul]
    simp only [Matrix.mul_assoc, hJ2, Matrix.mul_one]
  rw [hfactor]
  symm
  rw [Matrix.conjTranspose_mul, hJH]
  calc
    Matrix.trace ((J * Cᴴ) * (C * J)) =
        Matrix.trace (J * (Cᴴ * C) * J) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((J * J) * (Cᴴ * C)) := by
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (Cᴴ * C) := by rw [hJ2, Matrix.one_mul]

/-- Exact sharp expectation window in the normalization of
`thm:SMST-Clifford-twirl-matter`. -/
theorem cliffordExpectationResidual_bounds
    (J : Block m) (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    (Fintype.card (CliffordCarrier m) : ℂ) *
          cliffordProbability J representedAxis ≤
        commutantExpectationResidual J ∧
      commutantExpectationResidual J ≤
        4 * (Fintype.card (CliffordCarrier m) : ℂ) *
          cliffordProbability J representedAxis := by
  have hspectral := representedCommutatorEnergy_bounds J
  rw [representedCommutatorEnergy_eq_trivialResidual J hJH hJ2] at hspectral
  have hresidual :=
    (cliffordResidual_formulas J representedAxis hJH hJ2
      representedAxis_hermitian representedAxis_sq).1
  rw [hresidual] at hspectral
  constructor
  · have h := hspectral.2
    apply le_of_mul_le_mul_left ?_ (show (0 : ℂ) < 16 by norm_num)
    simpa only [mul_assoc] using h
  · have h := hspectral.1
    apply le_of_mul_le_mul_left ?_ (show (0 : ℂ) < 4 by norm_num)
    convert h using 1 <;> ring

end
end CliffordExpectationSpectralBounds
end NCG
