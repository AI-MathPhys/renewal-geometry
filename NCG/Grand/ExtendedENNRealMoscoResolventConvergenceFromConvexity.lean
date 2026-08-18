/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExtendedENNRealMoscoResolventConvergence
import NCG.Grand.RestrictedResolventObjectiveStrongConvexity

/-!
# Extended Mosco resolvent convergence from domain convexity

For convex effective domains and convex finite parts, positive resolvent shifts automatically
supply both the coercive stage gap and uniqueness of the finite-energy limit minimizer.
-/

open scoped ENNReal

open Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ K H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- The manuscript-facing forward implication for genuinely extended nonnegative convex forms. -/
theorem strongOperatorConverges_resolvents_of_extendedCofinalMosco_minimizers
    (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : H → ℝ≥0∞)
    (hmosco : J.CofinalMoscoConverges q qlim)
    (lam : ℝ) (hlam : 0 < lam)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hq0 : ∀ n, q n 0 = 0)
    (hstageFinite : ∀ n (f : Hn n), q n (Tn n f) ≠ ∞)
    (hlimitFinite : ∀ f : H, qlim (T f) ≠ ∞)
    (hstageConvex : ∀ n,
      ConvexOn ℝ {z : Hn n | q n z ≠ ∞} (fun z ↦ (q n z).toReal))
    (hlimitConvex :
      ConvexOn ℝ {z : H | qlim z ≠ ∞} (fun z ↦ (qlim z).toReal))
    (hstageMin : ∀ n (f z : Hn n), q n z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f (Tn n f) ≤
        resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f z)
    (hlimitMin : ∀ (f z : H), qlim z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (qlim w).toReal) lam f (T f) ≤
        resolventObjective (K := K) (fun w ↦ (qlim w).toReal) lam f z) :
    J.StrongOperatorConverges J Tn T := by
  apply strongOperatorConverges_resolvents_of_extendedCofinalMosco J (c := lam / 2)
    q qlim hmosco lam hlam Tn T hq0 hstageFinite hlimitFinite hstageMin
  · intro f y hy hobj
    exact resolventObjective_unique_minimizerOn
      {z : H | qlim z ≠ ∞} (fun z ↦ (qlim z).toReal) hlimitConvex
      lam hlam f (T f) (hlimitFinite f) (hlimitMin f) y hy hobj
  · exact div_pos hlam (by norm_num)
  · intro n f z hz
    have hgap := coercive_objective_gap_on_of_strongConvexOn
      (resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f)
      (2 * lam)
      (resolventObjective_strongConvexOn_subset
        {w : Hn n | q n w ≠ ∞} (fun w ↦ (q n w).toReal)
          (hstageConvex n) lam f)
      (Tn n f) z (hstageFinite n f) hz (hstageMin n f)
    convert hgap using 1
    all_goals ring

end NCG.VaryingHilbert.System
