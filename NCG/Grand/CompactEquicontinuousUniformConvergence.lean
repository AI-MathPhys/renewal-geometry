/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniformSemigroupApproximation
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform convergence on compact parameter sets

This file packages the compactness step that upgrades pointwise convergence of an
equicontinuous family to uniform convergence.  Its varying-Hilbert specialization turns
pointwise strong operator convergence of semigroup trajectories into convergence uniform on a
compact time set.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v w

/-- On a compact set, pointwise convergence of an equicontinuous family is uniform.

The limit function need not be included separately in the equicontinuous family: this is the
filter-convergence form of the Ascoli theorem, which obtains the necessary regularity of the
limit from pointwise convergence. -/
theorem IsCompact.tendstoUniformlyOn_of_equicontinuousOn
    {X : Type u} [TopologicalSpace X] {Y : Type v} [UniformSpace Y]
    {ι : Type w} {l : Filter ι} {F : ι → X → Y} {f : X → Y} {s : Set X}
    (hs : IsCompact s) (heq : EquicontinuousOn F s)
    (hpoint : ∀ x ∈ s, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    TendstoUniformlyOn F f l s := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hpi : Tendsto (s.restrict ∘ F) l (𝓝 (fun x : s ↦ f x)) := by
    rw [tendsto_pi_nhds]
    intro x
    exact hpoint x x.property
  have huniform :
      Tendsto (UniformFun.ofFun ∘ s.restrict ∘ F) l
        (𝓝 (UniformFun.ofFun (fun x : s ↦ f x))) :=
    (((equicontinuous_restrict_iff F).mpr heq).tendsto_uniformFun_iff_pi l
      (fun x : s ↦ f x)).2 hpi
  rw [tendstoUniformlyOn_iff_restrict]
  exact UniformFun.tendsto_iff_tendstoUniformly.mp huniform

namespace VaryingHilbert.System

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : VaryingHilbert.System (K := K) (H := H) (Hn := Hn))

/-- Pointwise strong operator convergence on a compact parameter set is uniform when every
embedded trajectory family arising from a strongly convergent input is equicontinuous there.

For semigroups, the equicontinuity hypothesis is normally supplied by a common time-regularity
estimate, while the pointwise hypothesis comes from the Euler-resolvent approximation theorem. -/
theorem StrongOperatorConvergesUniformlyOn.of_compact_of_equicontinuousOn
    {τ : Type*} [TopologicalSpace τ]
    (Sn : ∀ n, τ → Hn n →L[K] Hn n) (S : τ → H →L[K] H) (s : Set τ)
    (hs : IsCompact s)
    (hpoint : ∀ t ∈ s, J.StrongOperatorConverges J (fun n ↦ Sn n t) (S t))
    (heq : ∀ (x : ∀ n, Hn n) (xlim : H), J.StronglyConverges x xlim →
      EquicontinuousOn (fun n t ↦ J.embedding n (Sn n t (x n))) s) :
    J.StrongOperatorConvergesUniformlyOn Sn S s := by
  intro x xlim hx
  exact NCG.IsCompact.tendstoUniformlyOn_of_equicontinuousOn hs (heq x xlim hx)
    (fun t ht ↦ hpoint t ht x xlim hx)

/-- A common Lipschitz constant for all embedded trajectories is a concrete sufficient condition
for uniform strong convergence on a compact parameter set. -/
theorem StrongOperatorConvergesUniformlyOn.of_compact_of_lipschitzOn
    {τ : Type*} [PseudoMetricSpace τ]
    (Sn : ∀ n, τ → Hn n →L[K] Hn n) (S : τ → H →L[K] H) (s : Set τ)
    (hs : IsCompact s)
    (hpoint : ∀ t ∈ s, J.StrongOperatorConverges J (fun n ↦ Sn n t) (S t))
    (hLip : ∀ (x : ∀ n, Hn n) (xlim : H), J.StronglyConverges x xlim →
      ∃ L : NNReal, ∀ n,
        LipschitzOnWith L (fun t ↦ J.embedding n (Sn n t (x n))) s) :
    J.StrongOperatorConvergesUniformlyOn Sn S s := by
  apply StrongOperatorConvergesUniformlyOn.of_compact_of_equicontinuousOn
    J Sn S s hs hpoint
  intro x xlim hx
  obtain ⟨L, hL⟩ := hLip x xlim hx
  exact (LipschitzOnWith.uniformEquicontinuousOn
    (fun n t ↦ J.embedding n (Sn n t (x n))) L hL).equicontinuousOn

end VaryingHilbert.System

end NCG
