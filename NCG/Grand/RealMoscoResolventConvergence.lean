/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MoscoResolventStrongConvergence
import NCG.Grand.VaryingHilbertRealMosco

/-!
# Strong resolvent convergence from real Mosco convergence

This is the operator-level forward implication.  Cofinal real Mosco convergence of convex
nonnegative forms, together with the variational characterizations of the stage and limit
resolvents, implies varying-space strong operator convergence of the resolvent family.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Cofinal real Mosco convergence sends the associated resolvents to their limit in the
varying-space strong operator topology. -/
theorem strongOperatorConverges_resolvents_of_realMosco
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (hmosco : J.RealMoscoConverges q qlim)
    (lam : ℝ) (hlam : 0 < lam)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hqconvex : ∀ n, ConvexOn ℝ univ (q n))
    (hq0 : ∀ n, q n 0 = 0)
    (hqNonneg : ∀ n (z : Hn n), 0 ≤ q n z)
    (hstageMin : ∀ n (f z : Hn n),
      resolventObjective (K := K) (q n) lam f (Tn n f) ≤
        resolventObjective (K := K) (q n) lam f z)
    (hlimitUnique : ∀ (f y : H),
      resolventObjective (K := K) qlim lam f y ≤
        resolventObjective (K := K) qlim lam f (T f) → y = T f) :
    J.StrongOperatorConverges J Tn T := by
  intro f flim hf
  obtain ⟨recovery, hrecoveryStrong, hrecoveryEnergy⟩ := hmosco.recovery (T flim)
  apply resolventMinimizers_stronglyConverge_of_formLiminf J
    q qlim lam hlam f (fun n ↦ Tn n (f n)) recovery flim (T flim)
      hqconvex hq0 (fun n ↦ hqNonneg n _) hf
      (fun n z ↦ hstageMin n (f n) z)
      hrecoveryStrong hrecoveryEnergy
  · intro ns hns ψ hψ y hweak
    exact hmosco.liminf_le_subsequence ns hns ψ hψ
      (fun n ↦ Tn n (f n)) y hweak
  · exact hlimitUnique flim

/-- Operator-level real Mosco convergence assuming only that the displayed stage and limit
operators are global minimizers; uniqueness of the limit minimizer is automatic. -/
theorem strongOperatorConverges_resolvents_of_realMosco_minimizers
    [InnerProductSpace ℝ H] [IsScalarTower ℝ K H]
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (hmosco : J.RealMoscoConverges q qlim)
    (lam : ℝ) (hlam : 0 < lam)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hqconvex : ∀ n, ConvexOn ℝ univ (q n))
    (hqlimConvex : ConvexOn ℝ univ qlim)
    (hq0 : ∀ n, q n 0 = 0)
    (hqNonneg : ∀ n (z : Hn n), 0 ≤ q n z)
    (hstageMin : ∀ n (f z : Hn n),
      resolventObjective (K := K) (q n) lam f (Tn n f) ≤
        resolventObjective (K := K) (q n) lam f z)
    (hlimitMin : ∀ (f z : H),
      resolventObjective (K := K) qlim lam f (T f) ≤
        resolventObjective (K := K) qlim lam f z) :
    J.StrongOperatorConverges J Tn T := by
  apply strongOperatorConverges_resolvents_of_realMosco J
    q qlim hmosco lam hlam Tn T hqconvex hq0 hqNonneg hstageMin
  intro f y hy
  exact resolventObjective_unique_minimizer qlim hqlimConvex lam hlam
    f (T f) (hlimitMin f) y hy

end NCG.VaryingHilbert.System
