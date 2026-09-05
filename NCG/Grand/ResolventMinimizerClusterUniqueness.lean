/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventMinimizerBounds
import NCG.Grand.VariationalMinimizerClusterUniqueness

/-!
# Weak-cluster uniqueness for resolvent minimizers

This specialization combines the generic variational liminf/recovery argument with the automatic
completed-square lower bound for nonnegative resolvent objectives.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- The Mosco lower bound for the full quadratic objectives and one convergent recovery
competitor identify all weak clusters of the resolvent minimizers. -/
theorem resolventMinimizer_weakCluster_unique
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (f x recovery : ∀ n, Hn n) (flim xlim : H)
    (F : ℝ) (hF : 0 ≤ F) (hf : ∀ n, ‖f n‖ ≤ F)
    (hqx : ∀ n, 0 ≤ q n (x n))
    (hmin : ∀ n,
      resolventObjective (K := K) (q n) lam (f n) (x n) ≤
        resolventObjective (K := K) (q n) lam (f n) (recovery n))
    (hrecovery : Tendsto
      (fun n ↦ resolventObjective (K := K) (q n) lam (f n) (recovery n)) atTop
      (𝓝 (resolventObjective (K := K) qlim lam flim xlim)))
    (hclusterLower : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        resolventObjective (K := K) qlim lam flim y ≤
          liminf (fun k ↦ resolventObjective (K := K)
            (q (ns (ψ k))) lam (f (ns (ψ k))) (x (ns (ψ k)))) atTop)
    (hunique : ∀ y : H,
      resolventObjective (K := K) qlim lam flim y ≤
        resolventObjective (K := K) qlim lam flim xlim → y = xlim) :
    ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        y = xlim := by
  apply weakCluster_unique_of_variational_minimizers J
    (fun n ↦ resolventObjective (K := K) (q n) lam (f n))
    (resolventObjective (K := K) qlim lam flim)
    x recovery xlim hmin hrecovery (-(F ^ 2) / lam)
  · exact uniformlyBoundedBelow_resolventObjectives
      q lam hlam f x F hF hf hqx
  · exact hclusterLower
  · exact hunique

end NCG.VaryingHilbert.System
