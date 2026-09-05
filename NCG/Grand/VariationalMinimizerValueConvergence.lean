/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VariationalMinimizerClusterUniqueness

/-!
# Convergence of variational minimum values

Weak precompactness, the variational liminf inequality, and one convergent recovery competitor
force the stage minimum values to converge to the unique limit minimum.  This is the scalar
compactness step shared by Mosco--resolvent arguments on varying Hilbert spaces.
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

/-- Variational minimum values converge once minimizers are weakly precompact and every weak
cluster point satisfies the lower bound identifying the unique limit minimizer. -/
theorem minimizerValue_tendsto_of_weakPrecompact
    (Fn : (n : ℕ) → Hn n → ℝ) (Flim : H → ℝ)
    (x recovery : ∀ n, Hn n) (xlim : H)
    (hcompact : J.IsSequentiallyWeaklyPrecompact x)
    (hmin : ∀ n, Fn n (x n) ≤ Fn n (recovery n))
    (hrecovery : Tendsto (fun n ↦ Fn n (recovery n)) atTop (𝓝 (Flim xlim)))
    (B : ℝ) (hbelow : ∀ n, B ≤ Fn n (x n))
    (hclusterLower : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        Flim y ≤ liminf (fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))) atTop)
    (hunique : ∀ y : H, Flim y ≤ Flim xlim → y = xlim) :
    Tendsto (fun n ↦ Fn n (x n)) atTop (𝓝 (Flim xlim)) := by
  have hclusterUnique := weakCluster_unique_of_variational_minimizers J
    Fn Flim x recovery xlim hmin hrecovery B hbelow hclusterLower hunique
  refine Filter.tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨y, ψ, hψ, hweak⟩ := hcompact ns hns
  have hy : y = xlim := hclusterUnique ns hns ψ hψ y hweak
  subst y
  refine ⟨ψ, ?_⟩
  let u : ℕ → ℝ := fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))
  let r : ℕ → ℝ := fun k ↦ Fn (ns (ψ k)) (recovery (ns (ψ k)))
  have hrecoverySub : Tendsto r atTop (𝓝 (Flim xlim)) := by
    exact hrecovery.comp (hns.comp hψ.tendsto_atTop)
  have hle : ∀ k, u k ≤ r k := fun k ↦ hmin (ns (ψ k))
  have hlower : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of ⟨B, fun k ↦ hbelow (ns (ψ k))⟩
  have hupper : IsBoundedUnder (· ≤ ·) atTop u :=
    hrecoverySub.isBoundedUnder_le.mono_le (Eventually.of_forall hle)
  have hinf : Flim xlim ≤ liminf u atTop := by
    simpa [u] using hclusterLower ns hns ψ hψ xlim hweak
  have hsup : limsup u atTop ≤ Flim xlim := by
    calc
      limsup u atTop ≤ limsup r atTop :=
        limsup_le_limsup (Eventually.of_forall hle)
          hlower.isCobounded_flip hrecoverySub.isBoundedUnder_le
      _ = Flim xlim := hrecoverySub.limsup_eq
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup hupper hlower

end NCG.VaryingHilbert.System
