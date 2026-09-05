/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco

/-!
# Semigroup convergence from varying-space approximants

This file supplies the three-epsilon passage used after resolvent convergence.  Fixed Euler or
resolvent-polynomial approximants may converge strongly at every approximation order; if the
approximants converge to the target operators uniformly in the cutoff and their limit-space
counterparts converge, then the target operator family converges strongly as well.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u

/-- A metric three-epsilon lemma for a sequence obtained as a cutoff-uniform limit of convergent
approximating sequences. -/
theorem tendsto_of_eventually_uniform_approximants
    {X : Type u} [PseudoMetricSpace X]
    (f : ℕ → X) (g : ℕ → ℕ → X) (b : ℕ → X) (a : X)
    (hfixed : ∀ m, Tendsto (g m) atTop (𝓝 (b m)))
    (hlimit : Tendsto b atTop (𝓝 a))
    (happrox : ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop,
      dist (f n) (g m n) < ε) :
    Tendsto f atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmLimit : ∀ᶠ m in atTop, dist (b m) a < ε / 3 :=
    (Metric.tendsto_atTop.mp hlimit) (ε / 3) (by positivity) |>
      fun ⟨N, hN⟩ ↦ eventually_atTop.mpr ⟨N, hN⟩
  have hmApprox := happrox (ε / 3) (by positivity)
  obtain ⟨m, hmApproxN, hmLimit⟩ := (hmApprox.and hmLimit).exists
  have hnFixed : ∀ᶠ n in atTop, dist (g m n) (b m) < ε / 3 :=
    (Metric.tendsto_atTop.mp (hfixed m)) (ε / 3) (by positivity) |>
      fun ⟨N, hN⟩ ↦ eventually_atTop.mpr ⟨N, hN⟩
  rw [eventually_atTop] at hmApproxN hnFixed
  obtain ⟨N₁, hN₁⟩ := hmApproxN
  obtain ⟨N₂, hN₂⟩ := hnFixed
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  calc
    dist (f n) a ≤ dist (f n) (g m n) + dist (g m n) (b m) + dist (b m) a :=
      (dist_triangle4 (f n) (g m n) (b m) a)
    _ < ε / 3 + ε / 3 + ε / 3 :=
      add_lt_add (add_lt_add (hN₁ n ((le_max_left _ _).trans hn))
        (hN₂ n ((le_max_right _ _).trans hn))) hmLimit
    _ = ε := by ring

namespace VaryingHilbert.System

universe v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : VaryingHilbert.System (K := K) (H := H) (Hn := Hn))

/-- Strong convergence of target operators follows from strongly convergent fixed-order
approximants and cutoff-uniform approximation.  This is the abstract Euler/Trotter passage from
resolvents to semigroups on varying Hilbert spaces. -/
theorem StrongOperatorConverges.of_approximants
    (Sn : ∀ n, Hn n →L[K] Hn n) (S : H →L[K] H)
    (An : ℕ → ∀ n, Hn n →L[K] Hn n) (A : ℕ → H →L[K] H)
    (hA : ∀ m, J.StrongOperatorConverges J (An m) (A m))
    (hAlimit : ∀ x : H, Tendsto (fun m ↦ A m x) atTop (𝓝 (S x)))
    (happrox : ∀ (x : ∀ n, Hn n) (xlim : H), J.StronglyConverges x xlim →
      ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop,
        dist (J.embedding n (Sn n (x n)))
          (J.embedding n (An m n (x n))) < ε) :
    J.StrongOperatorConverges J Sn S := by
  intro x xlim hx
  apply tendsto_of_eventually_uniform_approximants
    (fun n ↦ J.embedding n (Sn n (x n)))
    (fun m n ↦ J.embedding n (An m n (x n)))
    (fun m ↦ A m xlim) (S xlim)
  · intro m
    exact hA m x xlim hx
  · exact hAlimit xlim
  · exact happrox x xlim hx

end VaryingHilbert.System

end NCG
