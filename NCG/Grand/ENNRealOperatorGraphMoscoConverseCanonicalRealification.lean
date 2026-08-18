/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealOperatorGraphMoscoConverseFromOneShiftWeakEquation

/-!
# Operator-graph Mosco converse with canonical realification

Every `RCLike` Hilbert space has a canonical real inner product obtained by taking the real part.
This wrapper installs those structures locally, eliminating all realification instances and
compatibility equalities from the model-facing graph-form theorem.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace K F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Canonically realified version of the one-shift weak-equation graph-energy Mosco converse. -/
theorem ennrealOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent_canonicalReal
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (D : Submodule K H) (A : D →ₗ[K] F)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Tn lam n f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (T lam f))
    (hls : LowerSemicontinuous (ennrealOperatorGraphEnergy D A))
    (hdom : Dense (D : Set H)) :
    J.MoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A) := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal K H
  haveI : IsScalarTower ℝ K H := IsScalarTower.restrictScalars ℝ K H
  letI : ∀ n, InnerProductSpace ℝ (Hn n) :=
    fun n ↦ InnerProductSpace.rclikeToReal K (Hn n)
  letI : ∀ n, IsScalarTower ℝ K (Hn n) :=
    fun n ↦ IsScalarTower.restrictScalars ℝ K (Hn n)
  letI : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal K F
  haveI : IsScalarTower ℝ K F := IsScalarTower.restrictScalars ℝ K F
  letI : ∀ n, InnerProductSpace ℝ (Fn n) :=
    fun n ↦ InnerProductSpace.rclikeToReal K (Fn n)
  letI : ∀ n, IsScalarTower ℝ K (Fn n) :=
    fun n ↦ IsScalarTower.restrictScalars ℝ K (Fn n)
  exact ennrealOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent_of_weakEquation J
    Dn An D A Tn T hdense lam0 hlam0 hT0 hstageEquation hlimitEquation hls hdom
      (fun x y ↦ real_inner_eq_re_inner K x y)

end NCG.VaryingHilbert.System
