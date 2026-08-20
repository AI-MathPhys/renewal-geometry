/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorResolventFamily
import NCG.Grand.ENNRealBoundedOperatorNormalResolvent

/-!
# Mosco convergence of joint-commutator energies from one resolvent

For the finite joint-commutator cutoffs, the canonical resolvents already
solve every positive shifted normal equation.  Consequently, convergence of
one positive resolvent shift, together with the continuum normal equations,
implies Mosco convergence of the squared commutator energies.
-/

open scoped ENNReal InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- One-shift strong convergence of the canonical finite commutant-Laplacian
resolvents implies Mosco convergence of the finite joint-commutator energies.

All finite-stage normal equations are consequences of the canonical inverse;
the remaining analytic inputs concern only the varying-Hilbert embeddings and
the limiting bounded operator. -/
theorem jointCommutatorEnergy_moscoConverges_of_oneStrongResolvent
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (A : H →L[ℂ] F) (T : ℝ → H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : J.StrongOperatorConverges J
      (NCG.jointCommutatorResolventFamily c lam0) (T lam0))
    (hlimitNormal : ∀ lam, 0 < lam → ∀ f : H,
      (A† ∘L A) (T lam f) + (lam : ℂ) • T lam f = f) :
    J.MoscoConverges
      (fun cutoff ↦ ennrealBoundedOperatorEnergy
        (NCG.jointCommutatorCLM (c cutoff)))
      (ennrealBoundedOperatorEnergy A) := by
  apply J.ennrealBoundedOperatorEnergy_moscoConverges_of_oneStrongResolvent_of_normalEquation
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
