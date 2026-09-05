/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianSemigroupToResolvent
import NCG.Grand.OperatorGraphResolventHeatLaplace

/-!
# Strong resolvents from convergence to canonical graph heat

This module specializes the abstract semigroup-to-resolvent Laplace compiler
to the canonical heat family built from one weak graph resolvent.  The limit
Laplace hypothesis is discharged automatically by continuous functional
calculus.
-/

open Matrix Set
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v x

variable {iota : ℕ → Type u}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type x} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Convergence of finite Hermitian heat semigroups to the canonical heat
family of one graph resolvent implies strong convergence of every positive
shifted resolvent. -/
theorem StrongOperatorConverges.of_finiteHermitian_canonicalOperatorGraphHeat
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (iota n)))
    (G : ∀ n, Matrix (iota n) (iota n) ℂ)
    (hG : ∀ n, (G n).PosSemidef)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (R : ℝ → H →L[ℂ] H)
    (hequation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b : ℝ) (hb : 0 < b)
    (hsemigroup : ∀ s : Set ℝ, IsCompact s → (∀ t ∈ s, 0 < t) →
      J.StrongOperatorConvergesUniformlyOn
        (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n)))
        (fun t ↦ NCG.VaryingHilbert.operatorGraphResolventHeat
          (R b) b t) s) :
    ∀ lam, 0 < lam →
      J.StrongOperatorConverges J
        (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
          (G n) lam)
        (R lam) := by
  apply StrongOperatorConverges.of_finiteHermitianSemigroups
    J G hG
    (fun t ↦ NCG.VaryingHilbert.operatorGraphResolventHeat (R b) b t)
    R hsemigroup
  intro lam hlam f
  exact
    NCG.VaryingHilbert.integral_smul_operatorGraphResolventHeat_apply_eq_resolvent
      D A R hequation b lam hb hlam f

end NCG.VaryingHilbert.System
