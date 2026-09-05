/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealClosedFormResolventMoscoConverse
import NCG.Grand.ENNRealResolventEnvelopeDualityFromConvexity
import NCG.Grand.ENNRealResolventIdentityFromConvexity
import NCG.Grand.PositiveRealResolventShiftPropagation

/-!
# Closed convex ENNReal Mosco converse from one shift and minimizers

This version derives both shifted envelope duality and every positive-shift second resolvent
identity.  Its operator input is only strong convergence at one positive shift, uniform positive-
shift bounds, and the usual convex variational characterization of the resolvents.
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

/-- One positive strongly convergent resolvent shift implies genuine ENNReal Mosco convergence
for closed densely defined convex forms.  The variational minimizer hypotheses automatically
supply the second resolvent identities, shifted duality, and the Yosida recovery core. -/
theorem ennrealMoscoConverges_of_oneStrongResolvent_of_closedConvexMinimizers
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hbound : ∀ lam, 0 < lam → ∃ C : ℝ, ∀ n, ‖Tn lam n‖ ≤ C)
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
  have hstageResolvent : ∀ a b, 0 < a → 0 < b → ∀ n,
      Tn b n - Tn a n =
        (((a - b : ℝ) : K)) • ((Tn b n).comp (Tn a n)) := by
    intro a b ha hb n
    exact realSecondResolventIdentity_of_convexMinimizers
      (q n) (fun lam ↦ Tn lam n) (hstageConvex n)
        (fun lam hlam ↦ hstageFinite lam hlam n)
        (fun lam hlam ↦ hstageMin lam hlam n) b a hb ha
  have hlimitResolvent : ∀ a b, 0 < a → 0 < b →
      T a - T b = (((b - a : ℝ) : K)) • ((T a).comp (T b)) := by
    intro a b ha hb
    exact realSecondResolventIdentity_of_convexMinimizers
      qlim T hlimitConvex hlimitFinite hlimitMin a b ha hb
  have hT : ∀ lam, 0 < lam →
      J.StrongOperatorConverges J (Tn lam) (T lam) :=
    StrongOperatorConverges.allPositiveRealResolventShifts J Tn T
      lam0 hlam0 hdense hT0 hbound hstageResolvent hlimitResolvent
  have hdual := hasENNRealResolventEnvelopeDuality_of_closedConvex
    qlim T hls hlimitConvex hdom hrealInner hlimitFinite hlimitEnergy
  exact ennrealMoscoConverges_of_strongResolvents_of_closedForm J
    q qlim Tn T hdense hT hstageFinite hlimitFinite hstageEnergy hlimitEnergy
      hstageMin hlimitMin hdual.isDeterminedByENNRealResolventEnvelopes hls hdom

end NCG.VaryingHilbert.System
