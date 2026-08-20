/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedOperatorNormalResolventFamily
import NCG.Grand.JointCommutatorCofinalMoscoFromDenseSources

/-!
# Joint-commutator Mosco convergence to a bounded continuum operator

The finite and continuum resolvent families are both canonical inverses of
their shifted normal operators.  Thus convergence at one positive shift on
compatible lifts of a dense source set is the only resolvent hypothesis needed
for cofinal Mosco convergence.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Dense-core convergence of one canonical finite resolvent to the canonical
bounded continuum resolvent implies cofinal Mosco convergence. -/
theorem jointCommutatorEnergy_cofinalMoscoConverges_to_boundedOperator_of_denseSources
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ x ∈ D, J.StronglyConverges (source x) x)
    (hcore : ∀ x ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam0 cutoff
        (source x cutoff))
      (boundedOperatorNormalResolventFamily A lam0 x)) :
    J.CofinalMoscoConverges
      (fun cutoff ↦ ennrealBoundedOperatorEnergy
        (NCG.jointCommutatorCLM (c cutoff)))
      (ennrealBoundedOperatorEnergy A) := by
  apply J.jointCommutatorEnergy_cofinalMoscoConverges_of_denseSources
    c A (boundedOperatorNormalResolventFamily A)
    lam0 hlam0 D hD source hsource hcore
  exact boundedOperatorNormalResolventFamily_normalEquation A

end NCG.VaryingHilbert.System
