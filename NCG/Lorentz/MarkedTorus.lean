/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Twisted momentum gap on the marked torus

**Theorem `thm:marked-torus-band-limit`** (momentum-gap core): on a
marking-twisted torus direction the admissible momenta are the
half-integer frequencies `2π(n + 1/2)`, `n ∈ ℤ`, and every such
frequency has absolute value at least `π`, with `π` attained at
`n = 0` (`NCG.twisted_momentum_gap`,
`NCG.twisted_momentum_gap_attained`).  Summing over directions, the
minimal twisted momentum squared is bounded below by
`π² · #{marked directions}` (`NCG.marked_gap_sq`) — the spectral gap
that separates the marked band from the unmarked one in the
band-limited convergence theorem.
-/

namespace NCG

/-- Half-integer gap: `|n + 1/2| ≥ 1/2` for every integer `n`. -/
theorem half_integer_gap (n : ℤ) : (1:ℝ)/2 ≤ |(n:ℝ) + 1/2| := by
  rcases le_or_gt 0 n with hn | hn
  · have h : (0:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have h : (n:ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **Theorem `thm:marked-torus-band-limit` (momentum-gap core)**: on a
marked direction every twisted momentum `2π(n + 1/2)` has absolute
value at least `π`. -/
theorem twisted_momentum_gap (n : ℤ) :
    Real.pi ≤ |2 * Real.pi * ((n:ℝ) + 1/2)| := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have h := half_integer_gap n
  nlinarith [Real.pi_pos]

/-- The gap `π` is attained at the fundamental twisted mode `n = 0`. -/
theorem twisted_momentum_gap_attained :
    |2 * Real.pi * (((0:ℤ):ℝ) + 1/2)| = Real.pi := by
  have h : 2 * Real.pi * (((0:ℤ):ℝ) + 1/2) = Real.pi := by
    push_cast
    ring
  rw [h, abs_of_nonneg Real.pi_pos.le]

/-- **Theorem `thm:marked-torus-band-limit` (gap additivity)**: over a
marking `ρ ∈ (ℤ/2)^d` the squared momentum of every twisted mode is at
least `π²` times the number of marked directions — the marked band sits
at squared energy `≥ π²·|ρ|₀` above the unmarked ground band. -/
theorem marked_gap_sq (d : ℕ) (ρ : Fin d → ZMod 2) (n : Fin d → ℤ) :
    Real.pi ^ 2 * ((Finset.univ.filter fun k => ρ k = 1).card : ℝ)
      ≤ ∑ k, (2 * Real.pi * ((n k : ℝ) + ((ρ k).val : ℝ) / 2)) ^ 2 := by
  calc Real.pi ^ 2 * ((Finset.univ.filter fun k => ρ k = 1).card : ℝ)
      = ∑ _k ∈ Finset.univ.filter fun k => ρ k = 1, Real.pi ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ Finset.univ.filter fun k => ρ k = 1,
          (2 * Real.pi * ((n k : ℝ) + ((ρ k).val : ℝ) / 2)) ^ 2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hρ : ρ k = 1 := (Finset.mem_filter.mp hk).2
        have h1 : (1 : ZMod 2).val = 1 := by decide
        have hval : ((ρ k).val : ℝ) = 1 := by
          rw [hρ, h1, Nat.cast_one]
        rw [hval]
        have hgap := twisted_momentum_gap (n k)
        have habs : |2 * Real.pi * ((n k : ℝ) + 1/2)| ^ 2
            = (2 * Real.pi * ((n k : ℝ) + 1/2)) ^ 2 := sq_abs _
        nlinarith [Real.pi_pos, abs_nonneg (2 * Real.pi * ((n k : ℝ) + 1/2))]
    _ ≤ ∑ k, (2 * Real.pi * ((n k : ℝ) + ((ρ k).val : ℝ) / 2)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => sq_nonneg _

end NCG
