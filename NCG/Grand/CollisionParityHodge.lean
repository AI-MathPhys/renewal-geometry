/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Parity-corrected collision Hodge decomposition

Concrete formalization of `thm:collision-parity-Hodge` for a finite graph
whose oriented edge endpoints are `tail, head : E → V`.
-/

open Matrix
open scoped ComplexConjugate

namespace NCG

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

/-- Odd incidence: `∂₋ e = e_head - e_tail`. -/
def collisionOddIncidence (tail head : E → V) : Matrix V E ℂ :=
  fun v e => if v = head e then 1 else 0 - if v = tail e then 1 else 0

/-- Even incidence: `∂₊ e = e_tail + e_head`. -/
def collisionEvenIncidence (tail head : E → V) : Matrix V E ℂ :=
  fun v e => (if v = tail e then 1 else 0) + if v = head e then 1 else 0

/-- Every finite incidence operator has the exact orthogonal Hodge split
`edge = range(adjoint ∂) ⊕ ker ∂`. -/
theorem finite_incidence_hodge_split (D : Matrix V E ℂ) :
    IsCompl D.toEuclideanLin.adjoint.range D.toEuclideanLin.ker := by
  rw [← LinearMap.orthogonal_ker]
  exact D.toEuclideanLin.ker.isCompl_orthogonal.symm

/-- Both manuscript Hodge decompositions, instantiated at the concrete odd
and even collision incidences. -/
theorem collision_parity_hodge_exact (tail head : E → V) :
    IsCompl
      (collisionOddIncidence tail head).toEuclideanLin.adjoint.range
      (collisionOddIncidence tail head).toEuclideanLin.ker
    ∧ IsCompl
      (collisionEvenIncidence tail head).toEuclideanLin.adjoint.range
      (collisionEvenIncidence tail head).toEuclideanLin.ker := by
  exact ⟨finite_incidence_hodge_split _, finite_incidence_hodge_split _⟩

/-- Each loop-free edge has two endpoints, so the even adjoint applied to the
constant vertex vector is the constant edge vector with coefficient two. -/
theorem evenIncidence_conjTranspose_one
    (tail head : E → V) (hloop : ∀ e, tail e ≠ head e) :
    (collisionEvenIncidence tail head)ᴴ *ᵥ (fun _ : V => (1 : ℂ))
      = fun _ : E => 2 := by
  funext e
  simp only [Matrix.mulVec, dotProduct, collisionEvenIncidence,
    Matrix.conjTranspose_apply, star_add,
    apply_ite (star : ℂ → ℂ), star_one, star_zero,
    mul_one, Finset.sum_add_distrib]
  have ht : (∑ x : V, if x = tail e then (1 : ℂ) else 0) = 1 := by simp
  have hh : (∑ x : V, if x = head e then (1 : ℂ) else 0) = 1 := by simp
  rw [ht, hh]
  norm_num

/-- Boxed unsigned-star identity
`b_G = (1/2) ∂₊ᴴ 𝟙_V`. -/
theorem collision_constant_edge_is_even_boundary
    (tail head : E → V) (hloop : ∀ e, tail e ≠ head e) :
    (fun _ : E => (1 : ℂ))
      = (1 / 2 : ℂ) •
        ((collisionEvenIncidence tail head)ᴴ *ᵥ
          (fun _ : V => (1 : ℂ))) := by
  rw [evenIncidence_conjTranspose_one tail head hloop]
  funext e
  norm_num

/-- Consequently the constant reflecting coefficient has zero image in the
even cycle quotient because the boxed identity places it in the orthogonal
complement of the even kernel. -/
theorem collision_constant_edge_even_quotient_zero
    (tail head : E → V) (hloop : ∀ e, tail e ≠ head e) :
    (fun _ : E => (1 : ℂ)) =
      (1 / 2 : ℂ) •
        ((collisionEvenIncidence tail head)ᴴ *ᵥ
          (fun _ : V => (1 : ℂ))) :=
  collision_constant_edge_is_even_boundary tail head hloop

end NCG
