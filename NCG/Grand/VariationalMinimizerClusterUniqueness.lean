/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertWeakCompactnessUpgrade
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Identifying weak cluster points of variational minimizers

The Mosco lower bound and a convergent recovery competitor identify every weak cluster point of
stage minimizers with the unique limit minimizer.  This file isolates the order-theoretic argument
from the concrete form and resolvent construction.
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

/-- Stagewise minimality against one convergent recovery competitor, together with the weak
liminf inequality and uniqueness of the limit minimizer, forces every weak cluster point of the
stage minimizers to equal the prescribed limit. -/
theorem weakCluster_unique_of_variational_minimizers
    (Fn : (n : ℕ) → Hn n → ℝ) (Flim : H → ℝ)
    (x recovery : ∀ n, Hn n) (xlim : H)
    (hmin : ∀ n, Fn n (x n) ≤ Fn n (recovery n))
    (hrecovery : Tendsto (fun n ↦ Fn n (recovery n)) atTop (𝓝 (Flim xlim)))
    (B : ℝ) (hbelow : ∀ n, B ≤ Fn n (x n))
    (hclusterLower : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        Flim y ≤ liminf (fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))) atTop)
    (hunique : ∀ y : H, Flim y ≤ Flim xlim → y = xlim) :
    ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        y = xlim := by
  intro ns hns ψ hψ y hweak
  apply hunique y
  have hrecoverySub :
      Tendsto (fun k ↦ Fn (ns (ψ k)) (recovery (ns (ψ k)))) atTop
        (𝓝 (Flim xlim)) :=
    hrecovery.comp (hns.comp hψ.tendsto_atTop)
  have hboundedBelow :
      IsBoundedUnder (· ≥ ·) atTop
        (fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))) :=
    isBoundedUnder_of ⟨B, fun k ↦ hbelow (ns (ψ k))⟩
  have hliminf :
      liminf (fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))) atTop ≤ Flim xlim := by
    apply liminf_le_of_le hboundedBelow
    intro b hb
    apply ge_of_tendsto hrecoverySub
    filter_upwards [hb] with k hk
    exact hk.trans (hmin (ns (ψ k)))
  exact (hclusterLower ns hns ψ hψ y hweak).trans hliminf

end NCG.VaryingHilbert.System
