/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorResolventFamily
import NCG.Grand.ENNRealBoundedOperatorCofinalNormalResolvent

/-!
# Cofinal Mosco convergence for joint-commutator cutoffs

This is the cofinal model specialization needed by the compact heat and Riesz
projection compilers.  Every finite-stage normal equation is automatic; the
analytic input is cofinal strong convergence at one positive shift together
with the limiting bounded normal equation.
-/

open Filter
open scoped ENNReal InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Cofinal one-shift convergence of the canonical commutant-Laplacian
resolvents implies cofinal Mosco convergence of the joint-commutator energies. -/
theorem jointCommutatorEnergy_cofinalMoscoConverges_of_oneStrongResolvent
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (A : H →L[ℂ] F) (T : ℝ → H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      (J.reindex φ).StrongOperatorConverges (J.reindex φ)
        (fun cutoff ↦
          NCG.jointCommutatorResolventFamily c lam0 (φ cutoff))
        (T lam0))
    (hlimitNormal : ∀ lam, 0 < lam → ∀ f : H,
      (A† ∘L A) (T lam f) + (lam : ℂ) • T lam f = f) :
    J.CofinalMoscoConverges
      (fun cutoff ↦ ennrealBoundedOperatorEnergy
        (NCG.jointCommutatorCLM (c cutoff)))
      (ennrealBoundedOperatorEnergy A) := by
  apply J.ennrealBoundedOperatorEnergy_cofinalMoscoConverges_of_oneStrongResolvent_of_normalEquation
    (fun cutoff ↦ NCG.jointCommutatorCLM (c cutoff)) A
    (NCG.jointCommutatorResolventFamily c) T hdense lam0 hlam0 hT0
  · intro lam hlam cutoff f
    change NCG.commutantLaplacianCLM (c cutoff)
        (NCG.jointCommutatorResolventFamily c lam cutoff f) +
      (lam : ℂ) • NCG.jointCommutatorResolventFamily c lam cutoff f = f
    simpa [NCG.jointCommutatorResolventFamily,
      NCG.jointCommutatorResolventAllShifts, dif_pos hlam] using
      NCG.jointCommutatorResolvent_laplacianEquation
        (c cutoff) lam hlam f
  · exact hlimitNormal

end NCG.VaryingHilbert.System
