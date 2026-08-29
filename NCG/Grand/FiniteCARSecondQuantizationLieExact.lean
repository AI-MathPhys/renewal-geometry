/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TypedMatterHamiltonianClosure

/-!
# Finite CAR second quantization as a Lie representation

This file proves the algebraic identity used by the matter Hamiltonian layer:
the number-preserving CAR lift of a one-particle matrix preserves
commutators.  The proof is finite and uses only the canonical
anticommutation relations, so it applies to every concrete finite Fock
realization of those relations.
-/

open Matrix Finset

namespace NCG
namespace FiniteCARSecondQuantizationLie

/-- Matrix commutator, restated locally to keep this module reusable. -/
def commutator {d : Type*} [Fintype d]
    (A B : Matrix d d ℂ) : Matrix d d ℂ := A * B - B * A

/-- The scalar Kronecker delta as a scalar matrix. -/
def deltaMatrix {ι d : Type*} [DecidableEq ι] [Fintype d]
    [DecidableEq d]
    (i j : ι) : Matrix d d ℂ := if i = j then 1 else 0

/-- The number-preserving one-body lift `dΓ(A)=Σ Aᵢⱼ cᵢ†cⱼ`. -/
def oneBodyLift {ι d : Type*} [Fintype ι] [Fintype d]
    (create annihilate : ι → Matrix d d ℂ) (A : Matrix ι ι ℂ) :
    Matrix d d ℂ :=
  ∑ i, ∑ j, A i j • (create i * annihilate j)

/-- The commutator of two quadratic CAR monomials. -/
theorem quadratic_commutator
    {ι d : Type*} [Fintype d] [DecidableEq d] [DecidableEq ι]
    (create annihilate : ι → Matrix d d ℂ)
    (hcc : ∀ i k, create k * create i = -(create i * create k))
    (haa : ∀ j l, annihilate l * annihilate j =
      -(annihilate j * annihilate l))
    (hac : ∀ j k, annihilate j * create k =
      deltaMatrix j k - create k * annihilate j)
    (i j k l : ι) :
    commutator (create i * annihilate j) (create k * annihilate l) =
      deltaMatrix j k * (create i * annihilate l) -
        deltaMatrix l i * (create k * annihilate j) := by
  have hquartic :
      create k * (create i * annihilate l * annihilate j) =
        create i * (create k * annihilate j * annihilate l) := by
    rw [Matrix.mul_assoc (create i) (annihilate l) (annihilate j),
      ← Matrix.mul_assoc (create k) (create i), hcc i k,
      Matrix.neg_mul, haa j l, Matrix.mul_neg, neg_neg]
    simp only [Matrix.mul_assoc]
  unfold commutator
  rw [Matrix.mul_assoc (create i) (annihilate j),
    ← Matrix.mul_assoc (annihilate j) (create k), hac j k,
    Matrix.sub_mul, Matrix.mul_sub]
  rw [Matrix.mul_assoc (create k) (annihilate l),
    ← Matrix.mul_assoc (annihilate l) (create i), hac l i,
    Matrix.sub_mul, Matrix.mul_sub]
  rw [hquartic]
  by_cases hjk : j = k <;> by_cases hli : l = i <;>
    simp [deltaMatrix, hjk, hli] <;> module

/-- Commutators distribute over finite sums. -/
theorem commutator_sum_sum
    {α β d : Type*} [Fintype α] [Fintype β] [Fintype d]
    (F : α → Matrix d d ℂ) (G : β → Matrix d d ℂ) :
    commutator (∑ i, F i) (∑ j, G j) =
      ∑ i, ∑ j, commutator (F i) (G j) := by
  change TypedMatterHamiltonianClosure.matrixCommutator (∑ i, F i)
      (∑ j, G j) =
    ∑ i, ∑ j, TypedMatterHamiltonianClosure.matrixCommutator (F i) (G j)
  exact TypedMatterHamiltonianClosure.matrixCommutator_sum_sum F G

/-- Scalar weights factor out of a commutator. -/
theorem commutator_smul_smul
    {d : Type*} [Fintype d] (a b : ℂ) (X Y : Matrix d d ℂ) :
    commutator (a • X) (b • Y) = (a * b) • commutator X Y := by
  change TypedMatterHamiltonianClosure.matrixCommutator (a • X) (b • Y) =
    (a * b) • TypedMatterHamiltonianClosure.matrixCommutator X Y
  exact TypedMatterHamiltonianClosure.matrixCommutator_smul_smul a b X Y

/-- Finite CAR second quantization is a Lie representation:
`[dΓ(A),dΓ(B)] = dΓ([A,B])`. -/
theorem oneBodyLift_commutator
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d]
    [DecidableEq d]
    (create annihilate : ι → Matrix d d ℂ)
    (hcc : ∀ i k, create k * create i = -(create i * create k))
    (haa : ∀ j l, annihilate l * annihilate j =
      -(annihilate j * annihilate l))
    (hac : ∀ j k, annihilate j * create k =
      deltaMatrix j k - create k * annihilate j)
    (A B : Matrix ι ι ℂ) :
    commutator (oneBodyLift create annihilate A)
        (oneBodyLift create annihilate B) =
      oneBodyLift create annihilate (A * B - B * A) := by
  classical
  unfold oneBodyLift
  rw [commutator_sum_sum]
  simp_rw [commutator_sum_sum, commutator_smul_smul,
    quadratic_commutator create annihilate hcc haa hac]
  simp_rw [smul_sub]
  simp only [Finset.sum_sub_distrib]
  simp only [deltaMatrix, ite_mul, Matrix.one_mul, Matrix.zero_mul,
    smul_ite, smul_zero]
  simp
  have hAB :
      (∑ i, ∑ j, ∑ l,
        (A i j * B j l) • (create i * annihilate l)) =
      ∑ i, ∑ l, (A * B) i l • (create i * annihilate l) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Matrix.mul_apply, Finset.sum_smul]
  have hBA :
      (∑ i, ∑ k, ∑ j,
        (A i j * B k i) • (create k * annihilate j)) =
      ∑ k, ∑ j, (B * A) k j • (create k * annihilate j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_apply, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  rw [hAB, hBA]
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

end FiniteCARSecondQuantizationLie
end NCG
