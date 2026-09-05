/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertSemigroupApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform-on-time semigroup approximation

The pointwise three-epsilon approximation theorem is upgraded to uniform convergence on an
arbitrary parameter set.  Applied to compact time intervals, it is the abstract Euler/Trotter
step in the uniform semigroup clause of the Mosco--resolvent--semigroup theorem.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v

/-- A uniform-on-set three-epsilon theorem for cutoff families obtained as uniform limits of
fixed-order approximants. -/
theorem tendstoUniformlyOn_of_eventually_uniform_approximants
    {X : Type u} [PseudoMetricSpace X] {τ : Type v}
    (f : ℕ → τ → X) (g : ℕ → ℕ → τ → X) (b : ℕ → τ → X) (a : τ → X)
    (s : Set τ)
    (hfixed : ∀ m, TendstoUniformlyOn (g m) (b m) atTop s)
    (hlimit : TendstoUniformlyOn b a atTop s)
    (happrox : ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop,
      ∀ t ∈ s, dist (f n t) (g m n t) < ε) :
    TendstoUniformlyOn f a atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmLimit := (Metric.tendstoUniformlyOn_iff.mp hlimit) (ε / 3) (by positivity)
  have hmApprox := happrox (ε / 3) (by positivity)
  obtain ⟨m, hmApproxN, hmLimit⟩ := (hmApprox.and hmLimit).exists
  have hnFixed := (Metric.tendstoUniformlyOn_iff.mp (hfixed m))
    (ε / 3) (by positivity)
  filter_upwards [hmApproxN, hnFixed] with n hnApprox hnFixed
  intro t ht
  calc
    dist (a t) (f n t) ≤
        dist (a t) (b m t) + dist (b m t) (g m n t) +
          dist (g m n t) (f n t) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact hmLimit t ht
      · exact hnFixed t ht
      · simpa [dist_comm] using hnApprox t ht
    _ = ε := by ring

namespace VaryingHilbert.System

universe w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : VaryingHilbert.System (K := K) (H := H) (Hn := Hn))

/-- Strong operator convergence uniformly on a parameter set (typically a compact time
interval), tested on every strongly convergent dependent input sequence. -/
def StrongOperatorConvergesUniformlyOn {τ : Type*}
    (Sn : ∀ n, τ → Hn n →L[K] Hn n) (S : τ → H →L[K] H) (s : Set τ) : Prop :=
  ∀ (x : ∀ n, Hn n) (xlim : H), J.StronglyConverges x xlim →
    TendstoUniformlyOn
      (fun n t ↦ J.embedding n (Sn n t (x n)))
      (fun t ↦ S t xlim) atTop s

/-- Uniform strong convergence of target semigroup families follows from fixed-order uniform
convergence and cutoff-uniform approximation, uniformly on the same time set. -/
theorem StrongOperatorConvergesUniformlyOn.of_approximants {τ : Type*}
    (Sn : ∀ n, τ → Hn n →L[K] Hn n) (S : τ → H →L[K] H)
    (An : ℕ → ∀ n, τ → Hn n →L[K] Hn n)
    (A : ℕ → τ → H →L[K] H) (s : Set τ)
    (hA : ∀ m, J.StrongOperatorConvergesUniformlyOn (An m) (A m) s)
    (hAlimit : ∀ x : H,
      TendstoUniformlyOn (fun m t ↦ A m t x) (fun t ↦ S t x) atTop s)
    (happrox : ∀ (x : ∀ n, Hn n) (xlim : H), J.StronglyConverges x xlim →
      ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, ∀ t ∈ s,
        dist (J.embedding n (Sn n t (x n)))
          (J.embedding n (An m n t (x n))) < ε) :
    J.StrongOperatorConvergesUniformlyOn Sn S s := by
  intro x xlim hx
  exact tendstoUniformlyOn_of_eventually_uniform_approximants
    (fun n t ↦ J.embedding n (Sn n t (x n)))
    (fun m n t ↦ J.embedding n (An m n t (x n)))
    (fun m t ↦ A m t xlim) (fun t ↦ S t xlim) s
    (fun m ↦ hA m x xlim hx) (hAlimit xlim) (happrox x xlim hx)

end VaryingHilbert.System

end NCG
