/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealClosedConvexQuadraticMoscoConverseFromOneShift
import NCG.Grand.ENNRealOperatorGraphEnergy

/-!
# Operator-graph ENNReal Mosco converse from one shift

This specializes the assumption-reduced quadratic converse to energies `‖A x‖²` on linear
operator domains and `∞` outside.  Effective-domain identification, two-homogeneity, and convexity
are discharged automatically from the graph operators.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ K H] [CompleteSpace H]
variable {F : Type z} [NormedAddCommGroup F] [NormedSpace K F]
  [NormedSpace ℝ F] [IsScalarTower ℝ K F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ K (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, NormedSpace K (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ K (Fn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- One positive-shift strong resolvent limit gives Mosco convergence for squared graph energies.
Only closedness/density of the limit graph energy and the concrete variational resolvent data
remain model-specific. -/
theorem ennrealOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (D : Submodule K H) (A : D →ₗ[K] F)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hstageRange : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      Tn lam n f ∈ Dn n)
    (hlimitRange : ∀ lam, 0 < lam → ∀ f : H,
      T lam f ∈ D)
    (hstageMin : ∀ lam, 0 < lam → ∀ n (f z : Hn n),
      z ∈ Dn n →
        resolventObjective (K := K)
            (fun x ↦ (ennrealOperatorGraphEnergy (Dn n) (An n) x).toReal)
            lam f (Tn lam n f) ≤
          resolventObjective (K := K)
            (fun x ↦ (ennrealOperatorGraphEnergy (Dn n) (An n) x).toReal)
            lam f z)
    (hlimitMin : ∀ lam, 0 < lam → ∀ (f z : H),
      z ∈ D →
        resolventObjective (K := K)
            (fun x ↦ (ennrealOperatorGraphEnergy D A x).toReal)
            lam f (T lam f) ≤
          resolventObjective (K := K)
            (fun x ↦ (ennrealOperatorGraphEnergy D A x).toReal)
            lam f z)
    (hls : LowerSemicontinuous (ennrealOperatorGraphEnergy D A))
    (hdom : Dense (D : Set H))
    (hrealInner : ∀ x y : H,
      inner ℝ x y = RCLike.re (inner K x y)) :
    J.MoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A) := by
  let q : (n : ℕ) → Hn n → ENNReal :=
    fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n)
  let qlim : H → ENNReal := ennrealOperatorGraphEnergy D A
  have hstageFinite : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      q n (Tn lam n f) ≠ ∞ := by
    intro lam hlam n f
    exact (ennrealOperatorGraphEnergy_ne_top_iff (Dn n) (An n) _).2
      (hstageRange lam hlam n f)
  have hlimitFinite : ∀ lam, 0 < lam → ∀ f : H,
      qlim (T lam f) ≠ ∞ := by
    intro lam hlam f
    exact (ennrealOperatorGraphEnergy_ne_top_iff D A _).2
      (hlimitRange lam hlam f)
  have hstageConvex : ∀ n,
      ConvexOn ℝ {z : Hn n | q n z ≠ ∞} (fun z ↦ (q n z).toReal) := by
    intro n
    exact convexOn_ennrealOperatorGraphEnergy (Dn n) (An n)
  have hlimitConvex :
      ConvexOn ℝ {z : H | qlim z ≠ ∞} (fun z ↦ (qlim z).toReal) :=
    convexOn_ennrealOperatorGraphEnergy D A
  have hdomainEq : {z : H | qlim z ≠ ∞} = (D : Set H) := by
    ext z
    exact ennrealOperatorGraphEnergy_ne_top_iff D A z
  have hdom' : Dense {z : H | qlim z ≠ ∞} := by
    rw [hdomainEq]
    exact hdom
  exact ennrealMoscoConverges_of_oneStrongResolvent_of_closedConvexQuadratic J
    q qlim Tn T hdense lam0 hlam0 hT0 hstageFinite hlimitFinite
      (fun n ↦ isENNRealTwoHomogeneous_operatorGraphEnergy (Dn n) (An n))
      (isENNRealTwoHomogeneous_operatorGraphEnergy D A)
      hstageConvex hlimitConvex
      (fun lam hlam n f z hz ↦ hstageMin lam hlam n f z
        ((ennrealOperatorGraphEnergy_ne_top_iff (Dn n) (An n) z).1 hz))
      (fun lam hlam f z hz ↦ hlimitMin lam hlam f z
        ((ennrealOperatorGraphEnergy_ne_top_iff D A z).1 hz))
      hls hdom' hrealInner

end NCG.VaryingHilbert.System
