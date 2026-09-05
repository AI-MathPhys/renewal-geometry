/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertSemigroupApproximation

/-!
# Semigroup convergence through Euler resolvent powers

Strong convergence of one resolvent family is stable under every fixed scaled power.  Combining
those Euler powers with cutoff-uniform approximation and convergence of the limit-space Euler
scheme gives strong convergence of the target semigroups by a three-epsilon argument.
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

/-- Every fixed Euler power of a scaled strongly convergent resolvent family converges strongly. -/
theorem StrongOperatorConverges.eulerResolventPower
    {Rn : ∀ n, Hn n →L[K] Hn n} {R : H →L[K] H}
    (hR : J.StrongOperatorConverges J Rn R) (a : K) (m : ℕ) :
    J.StrongOperatorConverges J
      (fun n ↦ (a • Rn n) ^ m) ((a • R) ^ m) :=
  NCG.VaryingHilbert.StrongOperatorConverges.pow J
    (NCG.VaryingHilbert.StrongOperatorConverges.smul J a hR) m

/-- Strong convergence of target semigroups follows when their approximants are fixed Euler
powers of strongly convergent scaled resolvents.  The only remaining inputs are convergence of
the limit-space Euler scheme and a cutoff-uniform Euler error estimate. -/
theorem StrongOperatorConverges.of_eulerResolventApproximants
    (Sn : ∀ n, Hn n →L[K] Hn n) (S : H →L[K] H)
    (Rn : ℕ → ∀ n, Hn n →L[K] Hn n) (R : ℕ → H →L[K] H)
    (a : ℕ → K)
    (hR : ∀ m, J.StrongOperatorConverges J (Rn m) (R m))
    (hEulerLimit : ∀ x : H,
      Tendsto (fun m ↦ ((a m • R m) ^ m) x) atTop (𝓝 (S x)))
    (hEulerApprox : ∀ (x : ∀ n, Hn n) (xlim : H),
      J.StronglyConverges x xlim →
        ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop,
          dist (J.embedding n (Sn n (x n)))
            (J.embedding n (((a m • Rn m n) ^ m) (x n))) < ε) :
    J.StrongOperatorConverges J Sn S := by
  apply StrongOperatorConverges.of_approximants J Sn S
    (fun m n ↦ (a m • Rn m n) ^ m) (fun m ↦ (a m • R m) ^ m)
  · intro m
    exact (hR m).eulerResolventPower J (a m) m
  · exact hEulerLimit
  · exact hEulerApprox

end NCG.VaryingHilbert.System
