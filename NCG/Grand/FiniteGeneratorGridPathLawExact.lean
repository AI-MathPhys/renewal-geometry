/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteGeneratorTransitionSemigroupExact
import NCG.Grand.YMDoobKoopmanPathLawExact

/-!
# Exact finite-grid path laws for continuous-time generators

Sampling the matrix-exponential transition semigroup at a nonnegative step
produces a genuine Markov cylinder law on every finite one-sided time grid.
This file proves normalization and right Kolmogorov consistency and identifies
all `n`-step kernels with the continuous-time semigroup at time `n * delta`.
-/

open Matrix Finset
open scoped BigOperators

noncomputable section

namespace NCG.FiniteGeneratorGridPathLaw

variable {S : Type*} [Fintype S] [DecidableEq S]

open FiniteGeneratorTransitionSemigroup

/-- A normalized, nonnegative, right-consistent cylinder law on a one-sided
finite time grid. -/
structure GridCylinderLaw (p : S → ℝ) (L : Matrix S S ℝ) (delta : ℝ) where
  weight : List S → ℝ
  weight_eq : weight = YMDoobKoopman.pathWeight p (transition L delta)
  nonnegative : ∀ xs, 0 ≤ weight xs
  empty : weight [] = 1
  singleton_normalized : ∑ x, weight [x] = 1
  extend_right : ∀ xs, xs ≠ [] →
    ∑ y, weight (xs ++ [y]) = weight xs

/-- Every finite generator and initial probability vector determine a genuine
one-sided path cylinder law at each nonnegative sampling step. -/
theorem gridCylinderLaw_exists
    (p : S → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    Nonempty (GridCylinderLaw p L delta) := by
  have hP := transition_rowStochastic L hL hdelta
  refine ⟨{
    weight := YMDoobKoopman.pathWeight p (transition L delta)
    weight_eq := rfl
    nonnegative := ?_
    empty := rfl
    singleton_normalized := ?_
    extend_right := YMDoobKoopman.pathWeight_append_sum
      p (transition L delta) hP.2 }⟩
  · intro xs
    cases xs with
    | nil => simp [YMDoobKoopman.pathWeight]
    | cons x tail =>
        exact mul_nonneg (hp x)
          (YMDoobKoopman.transitionWeight_nonnegative
            (transition L delta) hP.1 x tail)
  · simpa [YMDoobKoopman.pathWeight,
      YMDoobKoopman.transitionWeight] using hp1

/-- `n` grid steps are exactly the continuous transition at elapsed time
`n * delta`. -/
theorem transition_nat_mul (L : Matrix S S ℝ) (delta : ℝ) :
    ∀ n : ℕ, transition L ((n : ℝ) * delta) = transition L delta ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      have htime : ((n : ℝ) + 1) * delta = (n : ℝ) * delta + delta := by
        ring
      rw [htime, transition_add, ih, pow_succ]

/-- The endpoint marginal of an `n`-step grid cylinder is governed by the
same continuous-time transition kernel at time `n * delta`. -/
theorem nstep_kernel_eq_transition (L : Matrix S S ℝ) (delta : ℝ) (n : ℕ) :
    transition L delta ^ n = transition L ((n : ℝ) * delta) :=
  (transition_nat_mul L delta n).symm

end NCG.FiniteGeneratorGridPathLaw

