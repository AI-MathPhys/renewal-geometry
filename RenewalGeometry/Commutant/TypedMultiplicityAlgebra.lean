/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.GraphLoadedEdgeCommutantAssembly

/-!
# The typed multiplicity algebra as a star subalgebra

`def:typed-multiplicity` of the spacetime--gauge duality manuscript defines
the typed multiplicity algebra `M_type` as the family of multiplicity blocks
`(R_λ)_λ` satisfying the two intertwining equations
`R_μ F_e = F_e R_λ` and `R_λ F_e^* = F_e^* R_μ` on every incidence edge, and
lets it act on the full carrier as `⊕_λ I_{C^4 ⊗ V_λ} ⊗ R_λ`.

`TypedMultiplicityCommutant` (GraphLoadedEdgeCommutantAssembly) already
encodes the two equations pointwise.  This file packages the solution set as
a star-closed unital subalgebra `typedMultiplicityAlgebra` of the product
`Π v, Matrix (M v) (M v) ℂ` and defines the block-diagonal carrier action
`typedMultiplicityAction`, proved multiplicative, unital and star-preserving.
-/

open Matrix Kronecker

namespace RenewalGeometry
namespace GraphLoadedEdgeCommutant

variable {V : Type*} (G : SimpleGraph V)
variable (M : V → Type*) [∀ v, Fintype (M v)] [∀ v, DecidableEq (M v)]
variable (F : ∀ ⦃u v⦄, G.Adj u v → Matrix (M v) (M u) ℂ)

/-- `def:typed-multiplicity`: the typed multiplicity algebra `M_type`, the
star subalgebra of block families `(R_λ)` cut out by the two intertwining
equations on every oriented edge of the incidence graph. -/
def typedMultiplicityAlgebra :
    StarSubalgebra ℂ (∀ v, Matrix (M v) (M v) ℂ) where
  carrier := {R | TypedMultiplicityCommutant G M F R}
  mul_mem' := by
    intro R S hR hS u v h
    simp only [Pi.mul_apply]
    constructor
    · calc R v * S v * F h = R v * (F h * S u) := by
            rw [Matrix.mul_assoc, (hS h).1]
        _ = F h * R u * S u := by rw [← Matrix.mul_assoc, (hR h).1]
        _ = F h * (R u * S u) := by rw [Matrix.mul_assoc]
    · calc R u * S u * (F h)ᴴ = R u * ((F h)ᴴ * S v) := by
            rw [Matrix.mul_assoc, (hS h).2]
        _ = (F h)ᴴ * R v * S v := by rw [← Matrix.mul_assoc, (hR h).2]
        _ = (F h)ᴴ * (R v * S v) := by rw [Matrix.mul_assoc]
  one_mem' := by
    intro u v h
    simp
  add_mem' := by
    intro R S hR hS u v h
    simp only [Pi.add_apply]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, (hR h).1,
      (hS h).1, (hR h).2, (hS h).2]
    exact ⟨rfl, rfl⟩
  zero_mem' := by
    intro u v h
    simp
  algebraMap_mem' := by
    intro c u v h
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
    exact ⟨rfl, rfl⟩
  star_mem' := by
    intro R hR u v h
    simp only [Set.mem_ofPred_eq] at hR
    simp only [Pi.star_apply, Matrix.star_eq_conjTranspose]
    constructor
    · have h2 := congrArg conjTranspose (hR h).2
      simp only [conjTranspose_mul, conjTranspose_conjTranspose] at h2
      exact h2.symm
    · have h1 := congrArg conjTranspose (hR h).1
      simp only [conjTranspose_mul] at h1
      exact h1.symm

/-- Membership in `M_type` is exactly the pair of typed intertwining
equations on every edge. -/
theorem mem_typedMultiplicityAlgebra (R : ∀ v, Matrix (M v) (M v) ℂ) :
    R ∈ typedMultiplicityAlgebra G M F ↔
      TypedMultiplicityCommutant G M F R :=
  Iff.rfl

variable (B : V → Type*) [∀ v, Fintype (B v)] [∀ v, DecidableEq (B v)]

/-- The action of a multiplicity family on the full carrier
`⊕_λ (C^4 ⊗ V_λ) ⊗ M_λ`, block-diagonal with blocks
`I_{C^4 ⊗ V_λ} ⊗ R_λ` (`def:typed-multiplicity`, last clause). -/
def typedMultiplicityAction (R : ∀ v, Matrix (M v) (M v) ℂ) :
    ∀ v, Matrix ((Fin 4 × B v) × M v) ((Fin 4 × B v) × M v) ℂ :=
  fun v => (1 : Matrix (Fin 4 × B v) (Fin 4 × B v) ℂ) ⊗ₖ R v

omit [∀ v, DecidableEq (M v)] in
/-- The carrier action is multiplicative. -/
theorem typedMultiplicityAction_mul (R S : ∀ v, Matrix (M v) (M v) ℂ) :
    typedMultiplicityAction M B (R * S) =
      typedMultiplicityAction M B R * typedMultiplicityAction M B S := by
  funext v
  simp only [typedMultiplicityAction, Pi.mul_apply]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

omit [∀ v, Fintype (M v)] [∀ v, Fintype (B v)] in
/-- The carrier action is unital. -/
theorem typedMultiplicityAction_one :
    typedMultiplicityAction M B (1 : ∀ v, Matrix (M v) (M v) ℂ) = 1 := by
  funext v
  simp [typedMultiplicityAction]

omit [∀ v, Fintype (M v)] [∀ v, DecidableEq (M v)] [∀ v, Fintype (B v)] in
/-- The carrier action is star-preserving. -/
theorem typedMultiplicityAction_star (R : ∀ v, Matrix (M v) (M v) ℂ) :
    typedMultiplicityAction M B (star R) = star (typedMultiplicityAction M B R) := by
  funext v
  simp only [typedMultiplicityAction, Pi.star_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

omit [∀ v, Fintype (M v)] [∀ v, DecidableEq (M v)] [∀ v, Fintype (B v)] in
/-- The action is additive. -/
theorem typedMultiplicityAction_add (R S : ∀ v, Matrix (M v) (M v) ℂ) :
    typedMultiplicityAction M B (R + S) =
      typedMultiplicityAction M B R + typedMultiplicityAction M B S := by
  funext v
  simp only [typedMultiplicityAction, Pi.add_apply, Matrix.kronecker_add]

end GraphLoadedEdgeCommutant
end RenewalGeometry
