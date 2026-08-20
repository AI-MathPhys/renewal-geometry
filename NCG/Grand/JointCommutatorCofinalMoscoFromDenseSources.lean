/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorCofinalMoscoFromOneStrongResolvent
import NCG.Grand.JointCommutatorResolventDenseSourceConvergence
import NCG.Grand.VaryingHilbertAsymptoticDensityFromDenseSources

/-!
# Cofinal Mosco convergence from dense joint-commutator sources

The canonical resolvent bound promotes convergence on compatible lifts of a
dense source set to cofinal strong operator convergence.  The one-shift normal
resolvent compiler then yields cofinal Mosco convergence of the finite
joint-commutator energies.
-/

open Filter Set Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Dense-source convergence at one positive shift implies cofinal Mosco
convergence of the canonical finite joint-commutator energies. -/
theorem jointCommutatorEnergy_cofinalMoscoConverges_of_denseSources
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (A : H →L[ℂ] F) (T : ℝ → H →L[ℂ] H)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ x ∈ D, J.StronglyConverges (source x) x)
    (hcore : ∀ x ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam0 cutoff
        (source x cutoff))
      (T lam0 x))
    (hlimitNormal : ∀ lam, 0 < lam → ∀ f : H,
      (A† ∘L A) (T lam f) + (lam : ℂ) • T lam f = f) :
    J.CofinalMoscoConverges
      (fun cutoff ↦ ennrealBoundedOperatorEnergy
        (NCG.jointCommutatorCLM (c cutoff)))
      (ennrealBoundedOperatorEnergy A) := by
  apply J.jointCommutatorEnergy_cofinalMoscoConverges_of_oneStrongResolvent
    c A T (J.isAsymptoticallyDense_of_denseSources D hD source hsource)
      lam0 hlam0
  · exact J.jointCommutatorResolvent_cofinalStrongOperatorConverges_of_denseSources
      c (T lam0) lam0 hlam0 D hD source hsource hcore
  · exact hlimitNormal

end NCG.VaryingHilbert.System
