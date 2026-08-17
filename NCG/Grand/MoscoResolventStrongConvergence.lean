/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CoerciveObjectiveStrongConvergence
import NCG.Grand.ResolventMinimizerWeakPrecompactness
import NCG.Grand.ResolventObjectiveLiminf
import NCG.Grand.ResolventObjectiveStrongConvexity
import NCG.Grand.VaryingHilbertStrongBoundedness

/-!
# Strong convergence of varying-space resolvent minimizers

This file assembles the reusable forward Mosco argument.  A strongly convergent moving source,
a recovery vector with convergent form energy, the full objective liminf inequality, and
uniqueness of the limit minimizer imply strong convergence of the stage minimizers.  Coercivity,
weak precompactness, convergence of minimum values, and the norm upgrade are derived internally.
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

/-- Closed forward variational theorem for resolvent minimizers on varying Hilbert spaces. -/
theorem resolventMinimizers_stronglyConverge
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (f x recovery : ∀ n, Hn n) (flim xlim : H)
    (hqconvex : ∀ n, ConvexOn ℝ univ (q n))
    (hq0 : ∀ n, q n 0 = 0) (hqx : ∀ n, 0 ≤ q n (x n))
    (hf : J.StronglyConverges f flim)
    (hmin : ∀ n z,
      resolventObjective (K := K) (q n) lam (f n) (x n) ≤
        resolventObjective (K := K) (q n) lam (f n) z)
    (hrecoveryStrong : J.StronglyConverges recovery xlim)
    (hrecoveryEnergy : Tendsto (fun n ↦ q n (recovery n)) atTop (𝓝 (qlim xlim)))
    (hclusterLower : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        resolventObjective (K := K) qlim lam flim y ≤
          liminf (fun k ↦ resolventObjective (K := K)
            (q (ns (ψ k))) lam (f (ns (ψ k))) (x (ns (ψ k)))) atTop)
    (hunique : ∀ y : H,
      resolventObjective (K := K) qlim lam flim y ≤
        resolventObjective (K := K) qlim lam flim xlim → y = xlim) :
    J.StronglyConverges x xlim := by
  obtain ⟨F, hF, hfBound⟩ := hf.exists_pos_uniform_norm_bound J
  have hcompact : J.IsSequentiallyWeaklyPrecompact x :=
    resolventMinimizers_isSequentiallyWeaklyPrecompact J q lam hlam f x F hfBound
      hq0 hqx (fun n ↦ hmin n 0)
  have hrecoveryValue := resolventObjective_tendsto_of_recovery J q qlim lam
    f recovery flim xlim hrecoveryStrong hf hrecoveryEnergy
  have hbelow : ∀ n, -(F ^ 2) / lam ≤
      resolventObjective (K := K) (q n) lam (f n) (x n) :=
    uniformlyBoundedBelow_resolventObjectives q lam hlam f x F hF.le hfBound hqx
  have hstrong : ∀ n, StrongConvexOn univ (2 * lam)
      (resolventObjective (K := K) (q n) lam (f n)) := fun n ↦
    resolventObjective_strongConvexOn (q n) (hqconvex n) lam (f n)
  apply stronglyConverges_of_variational_minimizers_of_strongConvex J
    (fun n ↦ resolventObjective (K := K) (q n) lam (f n))
    (resolventObjective (K := K) qlim lam flim)
    x recovery xlim hcompact hmin hrecoveryStrong hrecoveryValue
      (-(F ^ 2) / lam) hbelow hclusterLower hunique
      (2 * lam) (mul_pos (by norm_num) hlam) hstrong

/-- The forward theorem with the manuscript-facing form liminf hypothesis.  The full objective
liminf inequality is derived automatically from weak norm lower semicontinuity and source-pairing
convergence. -/
theorem resolventMinimizers_stronglyConverge_of_formLiminf
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (f x recovery : ∀ n, Hn n) (flim xlim : H)
    (hqconvex : ∀ n, ConvexOn ℝ univ (q n))
    (hq0 : ∀ n, q n 0 = 0) (hqx : ∀ n, 0 ≤ q n (x n))
    (hf : J.StronglyConverges f flim)
    (hmin : ∀ n z,
      resolventObjective (K := K) (q n) lam (f n) (x n) ≤
        resolventObjective (K := K) (q n) lam (f n) z)
    (hrecoveryStrong : J.StronglyConverges recovery xlim)
    (hrecoveryEnergy : Tendsto (fun n ↦ q n (recovery n)) atTop (𝓝 (qlim xlim)))
    (hformClusterLower : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        qlim y ≤ liminf (fun k ↦ q (ns (ψ k)) (x (ns (ψ k)))) atTop)
    (hunique : ∀ y : H,
      resolventObjective (K := K) qlim lam flim y ≤
        resolventObjective (K := K) qlim lam flim xlim → y = xlim) :
    J.StronglyConverges x xlim := by
  obtain ⟨F, hF, hfBound⟩ := hf.exists_pos_uniform_norm_bound J
  let C : ℝ := 2 * F / lam
  have hxBound : ∀ n, ‖x n‖ ≤ C :=
    uniformlyBounded_resolventMinimizers q lam hlam f x F hfBound
      hq0 hqx (fun n ↦ hmin n 0)
  have hqUpper : ∀ n, q n (x n) ≤ 2 * C * F :=
    uniformlyBoundedAbove_resolventMinimizerEnergies q lam hlam.le f x C F
      (by dsimp [C]; positivity) hxBound hfBound hq0 (fun n ↦ hmin n 0)
  have hobjectiveClusterLower : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        resolventObjective (K := K) qlim lam flim y ≤
          liminf (fun k ↦ resolventObjective (K := K)
            (q (ns (ψ k))) lam (f (ns (ψ k))) (x (ns (ψ k)))) atTop := by
    intro ns hns ψ hψ y hweak
    apply resolventObjective_le_liminf (J.reindex (ns ∘ ψ))
      (fun k ↦ q (ns (ψ k))) qlim lam hlam
      (fun k ↦ f (ns (ψ k))) (fun k ↦ x (ns (ψ k))) flim y
      C F (2 * C * F) hweak
    · exact hf.reindex J (hns.comp hψ.tendsto_atTop)
    · exact fun k ↦ hxBound (ns (ψ k))
    · exact fun k ↦ hfBound (ns (ψ k))
    · exact fun k ↦ hqx (ns (ψ k))
    · exact fun k ↦ hqUpper (ns (ψ k))
    · exact hformClusterLower ns hns ψ hψ y hweak
  exact resolventMinimizers_stronglyConverge J q qlim lam hlam
    f x recovery flim xlim hqconvex hq0 hqx hf hmin
      hrecoveryStrong hrecoveryEnergy hobjectiveClusterLower hunique

end NCG.VaryingHilbert.System
