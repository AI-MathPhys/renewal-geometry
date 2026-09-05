/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CoerciveObjectiveStrongConvergence

/-!
# Variational convergence from direct cluster uniqueness

Extended-valued problems often establish uniqueness only for weak cluster points known to lie in
the finite-energy domain.  These variants accept that conclusion directly, avoiding a global
real-valued surrogate outside the domain.
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

/-- Minimum values converge when uniqueness of all actual weak cluster points is supplied
directly. -/
theorem minimizerValue_tendsto_of_weakPrecompact_of_clusterUnique
    (Fn : (n : ℕ) → Hn n → ℝ) (Flim : H → ℝ)
    (x recovery : ∀ n, Hn n) (xlim : H)
    (hcompact : J.IsSequentiallyWeaklyPrecompact x)
    (hmin : ∀ n, Fn n (x n) ≤ Fn n (recovery n))
    (hrecovery : Tendsto (fun n ↦ Fn n (recovery n)) atTop (𝓝 (Flim xlim)))
    (B : ℝ) (hbelow : ∀ n, B ≤ Fn n (x n))
    (hclusterLower : ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ y : H,
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        Flim y ≤ liminf (fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))) atTop)
    (hclusterUnique : ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ y : H,
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        y = xlim) :
    Tendsto (fun n ↦ Fn n (x n)) atTop (𝓝 (Flim xlim)) := by
  refine Filter.tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨y, ψ, hψ, hweak⟩ := hcompact ns hns
  have hy := hclusterUnique ns hns ψ hψ y hweak
  subst y
  refine ⟨ψ, ?_⟩
  let u : ℕ → ℝ := fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))
  let r : ℕ → ℝ := fun k ↦ Fn (ns (ψ k)) (recovery (ns (ψ k)))
  have hrecoverySub : Tendsto r atTop (𝓝 (Flim xlim)) :=
    hrecovery.comp (hns.comp hψ.tendsto_atTop)
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

/-- Direct cluster uniqueness plus a coercive recovery gap gives strong convergence of the
minimizers. -/
theorem stronglyConverges_of_variational_minimizers_of_coercive_gap_of_clusterUnique
    (Fn : (n : ℕ) → Hn n → ℝ) (Flim : H → ℝ)
    (x recovery : ∀ n, Hn n) (xlim : H)
    (hcompact : J.IsSequentiallyWeaklyPrecompact x)
    (hmin : ∀ n, Fn n (x n) ≤ Fn n (recovery n))
    (hrecoveryStrong : J.StronglyConverges recovery xlim)
    (hrecoveryValue : Tendsto (fun n ↦ Fn n (recovery n)) atTop (𝓝 (Flim xlim)))
    (B : ℝ) (hbelow : ∀ n, B ≤ Fn n (x n))
    (hclusterLower : ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ y : H,
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        Flim y ≤ liminf (fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))) atTop)
    (hclusterUnique : ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ y : H,
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        y = xlim)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ n, c * ‖x n - recovery n‖ ^ 2 ≤
      Fn n (recovery n) - Fn n (x n)) :
    J.StronglyConverges x xlim := by
  have hvalue := minimizerValue_tendsto_of_weakPrecompact_of_clusterUnique J
    Fn Flim x recovery xlim hcompact hmin hrecoveryValue B hbelow
      hclusterLower hclusterUnique
  exact stronglyConverges_of_recovery_of_coercive_objective_gap J
    Fn x recovery xlim (Flim xlim) c hc hrecoveryStrong
      hvalue hrecoveryValue hgap

end NCG.VaryingHilbert.System
