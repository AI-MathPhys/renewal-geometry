/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EulerResolventSemigroupConvergence
import NCG.Grand.CompactEquicontinuousUniformConvergence

/-!
# Uniform semigroup convergence through Euler resolvent powers

This file joins the fixed-power resolvent calculus, compact equicontinuity upgrade, and uniform
three-epsilon approximation.  It is the abstract uniform-on-compact-time Euler/Trotter step in
the Mosco--resolvent--semigroup equivalence.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Uniform strong convergence of target semigroup families obtained from Euler powers of
pointwise strongly convergent resolvents.

For each fixed Euler order, compactness and equicontinuity upgrade the algebraic pointwise
convergence of resolvent powers to uniform convergence in time.  The uniform three-epsilon
theorem then removes the Euler cutoff. -/
theorem StrongOperatorConvergesUniformlyOn.of_eulerResolventApproximants
    {τ : Type z} [TopologicalSpace τ]
    (Sn : ∀ n, τ → Hn n →L[K] Hn n) (S : τ → H →L[K] H)
    (Rn : ℕ → ∀ n, τ → Hn n →L[K] Hn n)
    (R : ℕ → τ → H →L[K] H) (a : ℕ → τ → K) (s : Set τ)
    (hs : IsCompact s)
    (hR : ∀ m, ∀ t ∈ s,
      J.StrongOperatorConverges J (fun n ↦ Rn m n t) (R m t))
    (hfixedEq : ∀ m, ∀ (x : ∀ n, Hn n) (xlim : H),
      J.StronglyConverges x xlim →
        EquicontinuousOn
          (fun n t ↦ J.embedding n (((a m t • Rn m n t) ^ m) (x n))) s)
    (hEulerLimit : ∀ x : H,
      TendstoUniformlyOn
        (fun m t ↦ ((a m t • R m t) ^ m) x)
        (fun t ↦ S t x) atTop s)
    (hEulerApprox : ∀ (x : ∀ n, Hn n) (xlim : H),
      J.StronglyConverges x xlim →
        ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, ∀ t ∈ s,
          dist (J.embedding n (Sn n t (x n)))
            (J.embedding n (((a m t • Rn m n t) ^ m) (x n))) < ε) :
    J.StrongOperatorConvergesUniformlyOn Sn S s := by
  apply StrongOperatorConvergesUniformlyOn.of_approximants J Sn S
    (fun m n t ↦ (a m t • Rn m n t) ^ m)
    (fun m t ↦ (a m t • R m t) ^ m) s
  · intro m
    apply StrongOperatorConvergesUniformlyOn.of_compact_of_equicontinuousOn
      J (fun n t ↦ (a m t • Rn m n t) ^ m)
        (fun t ↦ (a m t • R m t) ^ m) s hs
    · intro t ht
      exact (hR m t ht).eulerResolventPower J (a m t) m
    · exact hfixedEq m
  · exact hEulerLimit
  · exact hEulerApprox

end NCG.VaryingHilbert.System
