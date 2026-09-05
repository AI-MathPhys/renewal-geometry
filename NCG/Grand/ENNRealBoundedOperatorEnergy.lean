/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealOperatorGraphMoscoConverseCanonicalRealification

/-!
# Extended energies of bounded operators

A continuous linear operator has full domain, so its squared energy is finite and continuous.
This module records the comparison with the general graph-energy construction and specializes the
one-shift Mosco converse without separate lower-semicontinuity or density assumptions.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]

/-- The squared `ENNReal` energy of a bounded linear operator. -/
def ennrealBoundedOperatorEnergy (A : E →L[K] F) (x : E) : ENNReal :=
  ENNReal.ofReal (‖A x‖ ^ 2)

/-- Regard a bounded operator as an algebraic operator on the full submodule. -/
def boundedOperatorGraphMap (A : E →L[K] F) : (⊤ : Submodule K E) →ₗ[K] F :=
  A.toLinearMap.domRestrict ⊤

@[simp] theorem boundedOperatorGraphMap_apply (A : E →L[K] F)
    (x : (⊤ : Submodule K E)) :
    boundedOperatorGraphMap A x = A x :=
  rfl

@[simp] theorem ennrealOperatorGraphEnergy_top_eq
    (A : E →L[K] F) (x : E) :
    ennrealOperatorGraphEnergy (⊤ : Submodule K E) (boundedOperatorGraphMap A) x =
      ennrealBoundedOperatorEnergy A x := by
  simp [ennrealOperatorGraphEnergy, ennrealBoundedOperatorEnergy, boundedOperatorGraphMap]

theorem ennrealOperatorGraphEnergy_top (A : E →L[K] F) :
    ennrealOperatorGraphEnergy (⊤ : Submodule K E) (boundedOperatorGraphMap A) =
      ennrealBoundedOperatorEnergy A := by
  funext x
  exact ennrealOperatorGraphEnergy_top_eq A x

/-- Bounded-operator energy is continuous as an `ENNReal`-valued function. -/
theorem continuous_ennrealBoundedOperatorEnergy (A : E →L[K] F) :
    Continuous (ennrealBoundedOperatorEnergy A) := by
  exact ENNReal.continuous_ofReal.comp (A.continuous.norm.pow 2)

/-- Bounded-operator energy is automatically lower semicontinuous. -/
theorem lowerSemicontinuous_ennrealBoundedOperatorEnergy (A : E →L[K] F) :
    LowerSemicontinuous (ennrealBoundedOperatorEnergy A) :=
  (continuous_ennrealBoundedOperatorEnergy A).lowerSemicontinuous

/-- The full-domain graph presentation of a bounded operator is lower semicontinuous. -/
theorem lowerSemicontinuous_ennrealOperatorGraphEnergy_top (A : E →L[K] F) :
    LowerSemicontinuous
      (ennrealOperatorGraphEnergy (⊤ : Submodule K E) (boundedOperatorGraphMap A)) := by
  rw [ennrealOperatorGraphEnergy_top A]
  exact lowerSemicontinuous_ennrealBoundedOperatorEnergy A

namespace System

universe z

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {F₀ : Type z} [NormedAddCommGroup F₀] [InnerProductSpace K F₀]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- One positive-shift strong resolvent limit and the weak resolvent equations imply Mosco
convergence for squared energies of bounded operators.  Full-domain density and lower
semicontinuity are automatic. -/
theorem ennrealBoundedOperatorEnergy_moscoConverges_of_oneStrongResolvent
    (An : ∀ n, Hn n →L[K] Fn n) (A : H →L[K] F₀)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      OperatorGraphResolventEquation (⊤ : Submodule K (Hn n))
        (boundedOperatorGraphMap (An n)) lam f (Tn lam n f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation (⊤ : Submodule K H)
        (boundedOperatorGraphMap A) lam f (T lam f)) :
    J.MoscoConverges
      (fun n ↦ ennrealBoundedOperatorEnergy (An n))
      (ennrealBoundedOperatorEnergy A) := by
  have hgraph :=
    ennrealOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent_canonicalReal J
      (fun _ ↦ (⊤ : Submodule K (Hn _))) (fun n ↦ boundedOperatorGraphMap (An n))
      (⊤ : Submodule K H) (boundedOperatorGraphMap A) Tn T hdense lam0 hlam0 hT0
      hstageEquation hlimitEquation
      (lowerSemicontinuous_ennrealOperatorGraphEnergy_top A) dense_univ
  have hstageEnergy :
      (fun n ↦ ennrealOperatorGraphEnergy (⊤ : Submodule K (Hn n))
        (boundedOperatorGraphMap (An n))) =
        (fun n ↦ ennrealBoundedOperatorEnergy (An n)) := by
    funext n
    exact ennrealOperatorGraphEnergy_top (An n)
  rw [hstageEnergy, ennrealOperatorGraphEnergy_top A] at hgraph
  exact hgraph

end System
end NCG.VaryingHilbert
