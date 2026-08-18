/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealClosedConvexMoscoConverseFromOneShiftEnergy
import NCG.Grand.ENNRealQuadraticEulerIdentity

/-!
# Closed convex quadratic ENNReal Mosco converse from one shift

For two-homogeneous extended forms, scalar variations of the minimizer derive the Euler energy
identities.  Combining this with the previous automatic reductions leaves only one positive-shift
strong limit and the standard closed-convex variational characterization.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ K H] [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Strong convergence at one positive shift implies genuine ENNReal Mosco convergence for
closed densely defined convex two-homogeneous forms.  Euler identities, operator bounds,
resolvent identities, envelope duality, and recovery are all derived. -/
theorem ennrealMoscoConverges_of_oneStrongResolvent_of_closedConvexQuadratic
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hstageFinite : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      q n (Tn lam n f) ≠ ∞)
    (hlimitFinite : ∀ lam, 0 < lam → ∀ f : H,
      qlim (T lam f) ≠ ∞)
    (hstageQuadratic : ∀ n, IsENNRealTwoHomogeneous (K := K) (q n))
    (hlimitQuadratic : IsENNRealTwoHomogeneous (K := K) qlim)
    (hstageConvex : ∀ n,
      ConvexOn ℝ {z : Hn n | q n z ≠ ∞} (fun z ↦ (q n z).toReal))
    (hlimitConvex :
      ConvexOn ℝ {z : H | qlim z ≠ ∞} (fun z ↦ (qlim z).toReal))
    (hstageMin : ∀ lam, 0 < lam → ∀ n (f z : Hn n),
      q n z ≠ ∞ →
        resolventObjective (K := K) (fun x ↦ (q n x).toReal)
            lam f (Tn lam n f) ≤
          resolventObjective (K := K) (fun x ↦ (q n x).toReal) lam f z)
    (hlimitMin : ∀ lam, 0 < lam → ∀ (f z : H),
      qlim z ≠ ∞ →
        resolventObjective (K := K) (fun x ↦ (qlim x).toReal)
            lam f (T lam f) ≤
          resolventObjective (K := K) (fun x ↦ (qlim x).toReal) lam f z)
    (hls : LowerSemicontinuous qlim)
    (hdom : Dense {z : H | qlim z ≠ ∞})
    (hrealInner : ∀ x y : H,
      inner ℝ x y = RCLike.re (inner K x y)) :
    J.MoscoConverges q qlim := by
  have hstageEnergy : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      (q n (Tn lam n f)).toReal + lam * ‖Tn lam n f‖ ^ 2 =
        RCLike.re (inner K (Tn lam n f) f) := by
    intro lam hlam n f
    exact ennrealResolvent_energy_eq_inner_of_twoHomogeneous
      (q n) (hstageQuadratic n) (Tn lam n) lam hlam
        (hstageFinite lam hlam n) (hstageMin lam hlam n) f
  have hlimitEnergy : ∀ lam, 0 < lam → ∀ f : H,
      (qlim (T lam f)).toReal + lam * ‖T lam f‖ ^ 2 =
        RCLike.re (inner K (T lam f) f) := by
    intro lam hlam f
    exact ennrealResolvent_energy_eq_inner_of_twoHomogeneous
      qlim hlimitQuadratic (T lam) lam hlam
        (hlimitFinite lam hlam) (hlimitMin lam hlam) f
  exact ennrealMoscoConverges_of_oneStrongResolvent_of_closedConvexEnergy J
    q qlim Tn T hdense lam0 hlam0 hT0
      hstageFinite hlimitFinite hstageConvex hlimitConvex
      hstageEnergy hlimitEnergy hstageMin hlimitMin hls hdom hrealInner

end NCG.VaryingHilbert.System
