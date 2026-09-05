/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealClosedFormMoscoConverseFromOneShiftAndDuality
import NCG.Grand.ENNRealResolventEnvelopeDualityFromConvexity

/-!
# Closed convex ENNReal Mosco converse from one resolvent shift

This removes the abstract envelope-duality premise from the one-shift converse.  Closed
convexity and dense effective domain construct the dual witnesses automatically.
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
variable (J : System (K := K) (H := H) (Hn := Hn))

omit [IsScalarTower ℝ K H] in
/-- One strongly convergent resolvent shift implies genuine ENNReal Mosco convergence for
closed densely defined convex forms.  Shifted envelope duality and recovery are both derived. -/
theorem ennrealMoscoConverges_of_oneStrongResolvent_of_closedConvexForm
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hbound : ∀ lam, ∃ C : ℝ, ∀ n, ‖Tn lam n‖ ≤ C)
    (hstageResolvent : ∀ a b n,
      Tn b n - Tn a n =
        (((a - b : ℝ) : K)) • ((Tn b n).comp (Tn a n)))
    (hlimitResolvent : ∀ a b,
      T a - T b = (((b - a : ℝ) : K)) • ((T a).comp (T b)))
    (hstageFinite : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      q n (Tn lam n f) ≠ ∞)
    (hlimitFinite : ∀ lam, 0 < lam → ∀ f : H,
      qlim (T lam f) ≠ ∞)
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
    (hconvex : ConvexOn ℝ {z : H | qlim z ≠ ∞}
      (fun z ↦ (qlim z).toReal))
    (hdom : Dense {z : H | qlim z ≠ ∞})
    (hrealInner : ∀ x y : H,
      inner ℝ x y = RCLike.re (inner K x y)) :
    J.MoscoConverges q qlim := by
  have hdual := hasENNRealResolventEnvelopeDuality_of_closedConvex
    qlim T hls hconvex hdom hrealInner hlimitFinite hlimitEnergy
  exact ennrealMoscoConverges_of_oneStrongResolvent_of_closedForm_of_duality J
    q qlim Tn T hdense lam0 hT0 hbound hstageResolvent hlimitResolvent
    hstageFinite hlimitFinite hstageEnergy hlimitEnergy hstageMin hlimitMin
    hdual hls hdom

end NCG.VaryingHilbert.System
