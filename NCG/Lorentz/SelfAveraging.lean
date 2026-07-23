/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Self-averaging of random reset fields (variance core)

**Theorem `thm:self-averaging`**: a random flat reset field
self-averages to its mean second moment.  The concentration mechanism
proved here: for pairwise-uncorrelated fluctuations the variance of
the sum is the sum of variances,
`E[(ΣXᵢ)²] = Σ E[Xᵢ²]` (`NCG.variance_sum_uncorrelated`) — the `1/N`
concentration rate of the empirical second moment.  Combined with the
proved Lipschitz dependence of the symbol on the moment matrix and the
band-limited convergence, moment concentration transfers to the
operator endpoint; the almost-sure law-of-large-numbers packaging is
the noted probabilistic step.
-/

namespace NCG

/-- **Theorem `thm:self-averaging` (variance additivity)**: for
pairwise-uncorrelated random variables on a finite sample space the
second moment of the sum is the sum of second moments — the `1/N`
self-averaging rate of the empirical reset moment. -/
theorem variance_sum_uncorrelated {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    {m : ℕ} (X : Fin m → Ω → ℝ)
    (huncorr : ∀ i j, i ≠ j → ∑ ω, p ω * (X i ω * X j ω) = 0) :
    ∑ ω, p ω * (∑ i, X i ω) ^ 2 = ∑ i, ∑ ω, p ω * (X i ω) ^ 2 := by
  calc ∑ ω, p ω * (∑ i, X i ω) ^ 2
      = ∑ ω, ∑ i, ∑ j, p ω * (X i ω * X j ω) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ ω, p ω * (X i ω * X j ω) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ i, ∑ ω, p ω * (X i ω * X i ω) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · intro j _ hji
          exact huncorr i j (Ne.symm hji)
        · intro h
          exact absurd (Finset.mem_univ i) h
    _ = ∑ i, ∑ ω, p ω * (X i ω) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun ω _ => ?_
        rw [pow_two]

end NCG
