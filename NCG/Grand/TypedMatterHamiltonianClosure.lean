/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.V036MatterLegendre

/-!
# Typed finite matter-Hamiltonian closure

This file supplies the operator bookkeeping omitted from the earlier scalar
Legendre layer of `thm:SMST-matter-Legendre`: expansion of the finite smeared
matter commutator, cancellation of the momentum--momentum and
gradient--gradient blocks, and the determining-current Gram argument forcing
`a_r b_r = 1` species by species.
-/

open Matrix Finset
open scoped Matrix ComplexOrder MatrixOrder

namespace NCG
namespace TypedMatterHamiltonianClosure

/-- Matrix commutator. -/
def matrixCommutator {d : Type*} [Fintype d]
    (A B : Matrix d d ℂ) : Matrix d d ℂ := A * B - B * A

/-- A finite typed matter Hamiltonian with independent positive momentum and
transported-gradient coefficients. -/
def smearedMatterHamiltonian {x d : Type*} [Fintype x] [Fintype d]
    (momentum gradient : x → Matrix d d ℂ) (a b : ℝ) (N : x → ℝ) :
    Matrix d d ℂ :=
  ∑ u, (N u : ℂ) •
    ((a : ℂ) • momentum u + (b : ℂ) • gradient u)

/-- Commutators distribute over two finite operator sums. -/
theorem matrixCommutator_sum_sum
    {x y d : Type*} [Fintype x] [Fintype y] [Fintype d]
    (F : x → Matrix d d ℂ) (G : y → Matrix d d ℂ) :
    matrixCommutator (∑ u, F u) (∑ v, G v) =
      ∑ u, ∑ v, matrixCommutator (F u) (G v) := by
  ext i j
  simp [matrixCommutator, Matrix.mul_apply, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Scalar weights factor out of a matrix commutator. -/
theorem matrixCommutator_smul_smul
    {d : Type*} [Fintype d] (c e : ℂ) (A B : Matrix d d ℂ) :
    matrixCommutator (c • A) (e • B) =
      (c * e) • matrixCommutator A B := by
  ext i j
  simp [matrixCommutator, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro k _ <;> ring

/-- Four-block bilinearity of the matrix commutator. -/
theorem matrixCommutator_add_add
    {d : Type*} [Fintype d]
    (A B C D : Matrix d d ℂ) :
    matrixCommutator (A + B) (C + D) =
      matrixCommutator A C + matrixCommutator A D +
      matrixCommutator B C + matrixCommutator B D := by
  simp [matrixCommutator, Matrix.add_mul, Matrix.mul_add]
  abel

/-- Full four-block expansion of the finite matter commutator. -/
theorem smearedMatterHamiltonian_commutator_expansion
    {x d : Type*} [Fintype x] [Fintype d]
    (momentum gradient : x → Matrix d d ℂ)
    (a b : ℝ) (N M : x → ℝ) :
    matrixCommutator
        (smearedMatterHamiltonian momentum gradient a b N)
        (smearedMatterHamiltonian momentum gradient a b M) =
      ∑ u, ∑ v, ((N u * M v : ℝ) : ℂ) •
        (((a * a : ℝ) : ℂ) • matrixCommutator (momentum u) (momentum v) +
         ((a * b : ℝ) : ℂ) • matrixCommutator (momentum u) (gradient v) +
         ((b * a : ℝ) : ℂ) • matrixCommutator (gradient u) (momentum v) +
         ((b * b : ℝ) : ℂ) • matrixCommutator (gradient u) (gradient v)) := by
  unfold smearedMatterHamiltonian
  rw [matrixCommutator_sum_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [matrixCommutator_smul_smul, matrixCommutator_add_add]
  rw [matrixCommutator_smul_smul, matrixCommutator_smul_smul,
    matrixCommutator_smul_smul, matrixCommutator_smul_smul]
  push_cast
  module

/-- Once like-like local blocks commute, only the two
momentum--gradient commutators remain, with the exact coefficient `a b`. -/
theorem smearedMatterHamiltonian_crossBracket
    {x d : Type*} [Fintype x] [Fintype d]
    (momentum gradient : x → Matrix d d ℂ)
    (a b : ℝ) (N M : x → ℝ)
    (hmomentum : ∀ u v,
      matrixCommutator (momentum u) (momentum v) = 0)
    (hgradient : ∀ u v,
      matrixCommutator (gradient u) (gradient v) = 0) :
    matrixCommutator
        (smearedMatterHamiltonian momentum gradient a b N)
        (smearedMatterHamiltonian momentum gradient a b M) =
      ((a * b : ℝ) : ℂ) •
        ∑ u, ∑ v, ((N u * M v : ℝ) : ℂ) •
          (matrixCommutator (momentum u) (gradient v) +
           matrixCommutator (gradient u) (momentum v)) := by
  rw [smearedMatterHamiltonian_commutator_expansion]
  simp_rw [hmomentum, hgradient, smul_zero, zero_add, add_zero]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  module

/-- The cross-bracket kernel is antisymmetric in its endpoint indices. -/
theorem crossBracketKernel_swap
    {x d : Type*} [Fintype x] [Fintype d]
    (momentum gradient : x → Matrix d d ℂ) (u v : x) :
    matrixCommutator (momentum v) (gradient u) +
        matrixCommutator (gradient v) (momentum u) =
      -(matrixCommutator (momentum u) (gradient v) +
         matrixCommutator (gradient u) (momentum v)) := by
  simp [matrixCommutator]

/-- The measured cross bracket therefore carries the lapse determinant
`N_u M_v - N_v M_u`, the finite form of `N dM - M dN`. -/
theorem crossBracket_lapseAntisymmetrization
    {x d : Type*} [Fintype x] [LinearOrder x] [Fintype d]
    (momentum gradient : x → Matrix d d ℂ) (N M : x → ℝ) :
    ∑ u, ∑ v ∈ Finset.univ.filter (u < ·),
      (((N u * M v - N v * M u : ℝ) : ℂ) •
        (matrixCommutator (momentum u) (gradient v) +
         matrixCommutator (gradient u) (momentum v))) =
      -(∑ u, ∑ v ∈ Finset.univ.filter (u < ·),
        (((M u * N v - M v * N u : ℝ) : ℂ) •
        (matrixCommutator (momentum u) (gradient v) +
         matrixCommutator (gradient u) (momentum v)))) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v _
  module

/-- Positive definiteness of the determining species-current Gram makes the
current synthesis injective. -/
theorem determiningCurrentGram_kernel
    {s r w : Type*} [Fintype s] [Fintype r] [Fintype w]
    [DecidableEq r]
    (D : Matrix s r ℂ) (c : Matrix r w ℂ)
    (hGram : (Dᴴ * D).PosDef) :
    D * c = 0 ↔ c = 0 := by
  haveI := hGram.isUnit.invertible
  constructor
  · intro hDc
    have hGc : (Dᴴ * D) * c = 0 := by
      rw [Matrix.mul_assoc, hDc, Matrix.mul_zero]
    calc
      c = (Dᴴ * D)⁻¹ * ((Dᴴ * D) * c) := by
        rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]
      _ = 0 := by rw [hGc, Matrix.mul_zero]
  · rintro rfl
    exact Matrix.mul_zero _

/-- Under a determining current Gram, equality of the weighted and physical
species-current sums is equivalent to `a_r b_r = 1` for every loaded species. -/
theorem totalMatterClosure_iff_speciesReciprocity
    {s r : Type*} [Fintype s] [Fintype r] [DecidableEq r]
    (D : Matrix s r ℂ) (a b : r → ℝ)
    (hGram : (Dᴴ * D).PosDef) :
    D * (Matrix.of fun i (_ : Fin 1) => (((a i * b i - 1 : ℝ) : ℂ))) = 0 ↔
      ∀ i, a i * b i = 1 := by
  rw [determiningCurrentGram_kernel D _ hGram]
  constructor
  · intro hc i
    have hi := congrFun (congrFun hc i) 0
    simp at hi
    exact_mod_cast sub_eq_zero.mp hi
  · intro hab
    ext i j
    simp only [Matrix.of_apply, Matrix.zero_apply]
    rw [hab i]
    simp

end TypedMatterHamiltonianClosure
end NCG
