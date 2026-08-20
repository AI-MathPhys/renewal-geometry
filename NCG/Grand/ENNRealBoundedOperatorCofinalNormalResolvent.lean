/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealBoundedOperatorNormalResolvent
import NCG.Grand.ResolventMoscoConverse
import NCG.Grand.ENNRealMoscoResolventConvergence

/-!
# Cofinal Mosco convergence from bounded normal resolvents

The one-shift bounded-operator Mosco compiler can be applied after every
cofinal reindexing.  This module packages that argument, so downstream compact
and spectral theorems can consume `CofinalMoscoConverges` directly.
-/

open Filter
open scoped ENNReal InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {F₀ : Type z} [NormedAddCommGroup F₀] [InnerProductSpace K F₀]
  [CompleteSpace F₀]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
  [∀ n, CompleteSpace (Fn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Cofinal strong convergence at one positive shift, together with the stage
and limit normal equations, implies cofinal Mosco convergence of the squared
bounded-operator energies. -/
theorem ennrealBoundedOperatorEnergy_cofinalMoscoConverges_of_oneStrongResolvent_of_normalEquation
    (An : ∀ n, Hn n →L[K] Fn n) (A : H →L[K] F₀)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      (J.reindex φ).StrongOperatorConverges (J.reindex φ)
        (fun n ↦ Tn lam0 (φ n)) (T lam0))
    (hstageNormal : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      ((An n)† ∘L (An n)) (Tn lam n f) +
          ((lam : ℝ) : K) • Tn lam n f = f)
    (hlimitNormal : ∀ lam, 0 < lam → ∀ f : H,
      (A† ∘L A) (T lam f) + ((lam : ℝ) : K) • T lam f = f) :
    J.CofinalMoscoConverges
      (fun n ↦ ennrealBoundedOperatorEnergy (An n))
      (ennrealBoundedOperatorEnergy A) := by
  intro φ hφ
  apply
    ennrealBoundedOperatorEnergy_moscoConverges_of_oneStrongResolvent_of_normalEquation
      (J.reindex φ)
    (fun n ↦ An (φ n)) A (fun lam n ↦ Tn lam (φ n)) T
    (hdense.reindex J φ hφ) lam0 hlam0 (hT0 φ hφ)
  · intro lam hlam n f
    exact hstageNormal lam hlam (φ n) f
  · exact hlimitNormal

end NCG.VaryingHilbert.System
