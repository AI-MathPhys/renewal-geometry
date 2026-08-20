/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCommutantPoincareGap
import NCG.Grand.ENNRealBoundedOperatorNormalResolvent

/-!
# The finite joint commutator as a continuous graph operator

The manuscript's relative Howe form is the squared norm of the joint
commutator source.  Finite dimensionality promotes the algebraic source to a
continuous linear map.  Its normal operator is the concrete commutant
Laplacian, and its shifted normal equations imply the weak graph-resolvent
equations used by the Mosco and compact-screen compilers.
-/

open scoped InnerProductSpace

noncomputable section

namespace NCG
open Matrix


/-- The finite joint commutator source as a continuous operator between the
Hilbert--Schmidt Euclidean carriers. -/
noncomputable def jointCommutatorCLM {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    EuclideanSpace ℂ (n × n) →L[ℂ]
      EuclideanSpace ℂ (Fin s × (n × n)) :=
  (jointCommutatorL2 c).toContinuousLinearMap

@[simp] theorem jointCommutatorCLM_apply {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (x : EuclideanSpace ℂ (n × n)) :
    jointCommutatorCLM c x = jointCommutatorL2 c x := rfl

/-- The normal operator of the joint commutator source: the finite
commutant Laplacian. -/
noncomputable def commutantLaplacianCLM {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  ContinuousLinearMap.adjoint (jointCommutatorCLM c) ∘L
    jointCommutatorCLM c

theorem jointCommutatorCLM_norm_sq {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ) (X : Matrix n n ℂ) :
    ‖jointCommutatorCLM c (matrixL2 X)‖ ^ 2 =
      ∑ j, (((c j * X - X * c j)ᴴ *
        (c j * X - X * c j)).trace).re := by
  exact jointCommutatorL2_norm_sq c X

/-- The continuous joint commutator has exactly the matrix commutant as its
kernel. -/
theorem matrixL2_mem_jointCommutatorCLM_ker_iff
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (X : Matrix n n ℂ) :
    matrixL2 X ∈ LinearMap.ker (jointCommutatorCLM c).toLinearMap ↔
      ∀ j, c j * X = X * c j := by
  exact matrixL2_mem_jointCommutator_ker_iff c X

/-- The bounded-operator graph energy is literally the manuscript's summed
Hilbert--Schmidt commutator form. -/
theorem ennrealJointCommutatorEnergy_matrixL2
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (X : Matrix n n ℂ) :
    NCG.VaryingHilbert.ennrealBoundedOperatorEnergy
      (jointCommutatorCLM c) (matrixL2 X) =
        ENNReal.ofReal
          (∑ j, (((c j * X - X * c j)ᴴ *
            (c j * X - X * c j)).trace).re) := by
  rw [NCG.VaryingHilbert.ennrealBoundedOperatorEnergy,
    jointCommutatorCLM_norm_sq]

/-- A strong shifted commutant-Laplacian equation is precisely sufficient for
the weak graph-resolvent equation of the joint commutator energy. -/
theorem jointCommutator_resolventEquation_of_laplacianEquation
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ)
    (f x : EuclideanSpace ℂ (n × n))
    (h : commutantLaplacianCLM c x + (lam : ℂ) • x = f) :
    NCG.VaryingHilbert.OperatorGraphResolventEquation
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (n × n)))
      (NCG.VaryingHilbert.boundedOperatorGraphMap (jointCommutatorCLM c))
      lam f x := by
  apply NCG.VaryingHilbert.boundedOperatorGraph_resolventEquation_of_normalEquation
    (jointCommutatorCLM c) lam f x
  change commutantLaplacianCLM c x + (lam : ℂ) • x = f
  exact h


end NCG
