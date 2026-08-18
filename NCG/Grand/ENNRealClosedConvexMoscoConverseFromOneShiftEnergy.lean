/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealClosedConvexMoscoConverseFromOneShiftMinimizers
import NCG.Grand.ENNRealResolventOperatorBound

/-!
# Closed convex ENNReal Mosco converse from one shift and Euler identities

This is the most assumption-reduced one-shift converse.  The Euler identities give the sharp
positive-shift operator bounds; convex minimizers give the second resolvent identities; closed
convexity gives shifted envelope duality; and lower semicontinuity with dense domain gives the
Yosida recovery core.
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

/-- Strong convergence at one positive shift plus the standard closed-convex variational and
Euler data imply genuine ENNReal Mosco convergence.  No separate operator bounds, resolvent
identities, envelope duality, or recovery core are required. -/
theorem ennrealMoscoConverges_of_oneStrongResolvent_of_closedConvexEnergy
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hstageFinite : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      q n (Tn lam n f) ≠ ∞)
    (hlimitFinite : ∀ lam, 0 < lam → ∀ f : H,
      qlim (T lam f) ≠ ∞)
    (hstageConvex : ∀ n,
      ConvexOn ℝ {z : Hn n | q n z ≠ ∞} (fun z ↦ (q n z).toReal))
    (hlimitConvex :
      ConvexOn ℝ {z : H | qlim z ≠ ∞} (fun z ↦ (qlim z).toReal))
    (hstageEnergy : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      (q n (Tn lam n f)).toReal + lam * ‖Tn lam n f‖ ^ 2 =
        RCLike.re (inner K (Tn lam n f) f))
    (hlimitEnergy : ∀ lam, 0 < lam → ∀ f : H,
      (qlim (T lam f)).toReal + lam * ‖T lam f‖ ^ 2 =
        RCLike.re (inner K (T lam f) f))
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
  have hbound : ∀ lam, 0 < lam → ∃ C : ℝ, ∀ n, ‖Tn lam n‖ ≤ C := by
    intro lam hlam
    refine ⟨1 / lam, ?_⟩
    intro n
    exact ennrealResolvent_opNorm_le_inv
      (q n) (Tn lam n) lam hlam (hstageEnergy lam hlam n)
  exact ennrealMoscoConverges_of_oneStrongResolvent_of_closedConvexMinimizers J
    q qlim Tn T hdense lam0 hlam0 hT0 hbound
      hstageFinite hlimitFinite hstageConvex hlimitConvex
      hstageEnergy hlimitEnergy hstageMin hlimitMin hls hdom hrealInner

end NCG.VaryingHilbert.System
