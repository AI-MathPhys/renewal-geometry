/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperationalLightConeExponential
import NCG.Grand.FiniteMarkovHeatKernel

/-!
# Finite-range influence exponentials and Poisson tails

This file supplies the finite-propagation part of
`thm:SMFS-Dobrushin-gap`.  A range-`R` nonnegative influence matrix has no
`n`-step entry beyond distance `nR`.  Combining this exact support statement
with a uniform column-sum bound turns the influence exponential into the
corresponding Poisson tail.
-/

open scoped BigOperators

noncomputable section

namespace NCG
namespace DobrushinInfluencePoissonTail

open OperationalLightConeExponential

/-- The influence series is literally the entrywise exponential of `sC`. -/
theorem influenceExponentialEntry_eq_exponentialEntry_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (s : ℝ) (j i : ι) :
    influenceExponentialEntry C s j i =
      Matrix.exponentialEntry (s • C) j i := by
  unfold influenceExponentialEntry Matrix.exponentialEntry
  apply tsum_congr
  intro n
  rw [smul_pow]
  change (s ^ n / n.factorial) * (C ^ n) j i =
    (1 / n.factorial) * (s ^ n * (C ^ n) j i)
  ring

theorem influence_power_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : ∀ j i, 0 ≤ C j i) :
    ∀ n j i, 0 ≤ (C ^ n) j i := by
  intro n
  induction n with
  | zero =>
      intro j i
      by_cases hji : j = i <;> simp [hji]
  | succ n ih =>
      intro j i
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih j l) (hC l i)

/-- A column-sum bound controls every entry of every matrix power. -/
theorem influence_power_le_columnBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (α : ℝ)
    (hC : ∀ j i, 0 ≤ C j i) (hα : 0 ≤ α)
    (hcol : ∀ i, ∑ j, C j i ≤ α) :
    ∀ n j i, (C ^ n) j i ≤ α ^ n := by
  let d0 : ι → ι → ℝ := fun _ _ => 0
  intro n j i
  have h := influence_power_combesThomas C d0 0 α hC
    (fun _ => rfl) (fun _ _ _ => by norm_num [d0])
    (le_refl 0) hα
    (by
      intro x
      simpa [d0] using hcol x)
    n j i
  simpa [d0] using h

/-- Range-`R` matrices have exact finite propagation: an `n`-step entry
vanishes beyond distance `nR`. -/
theorem influence_power_eq_zero_of_distance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (dist : ι → ι → ℕ) (R : ℕ)
    (hdrefl : ∀ i, dist i i = 0)
    (hdtri : ∀ i l j, dist i j ≤ dist i l + dist l j)
    (hlocal : ∀ j i, R < dist i j → C j i = 0) :
    ∀ n j i, n * R < dist i j → (C ^ n) j i = 0 := by
  intro n
  induction n with
  | zero =>
      intro j i hfar
      have hji : j ≠ i := by
        intro hji
        subst j
        simp [hdrefl] at hfar
      simp [Matrix.one_apply_ne hji]
  | succ n ih =>
      intro j i hfar
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : R < dist i l
      · rw [hlocal l i hil, mul_zero]
      · have hil' : dist i l ≤ R := Nat.le_of_not_gt hil
        by_cases hlj : n * R < dist l j
        · rw [ih j l hlj, zero_mul]
        · have hlj' : dist l j ≤ n * R := Nat.le_of_not_gt hlj
          have hreach : dist i j ≤ (n + 1) * R := by
            calc
              dist i j ≤ dist i l + dist l j := hdtri i l j
              _ ≤ R + n * R := Nat.add_le_add hil' hlj'
              _ = (n + 1) * R := by rw [Nat.succ_mul, Nat.add_comm]
          exact ((Nat.not_lt_of_ge hreach) hfar).elim

/-- The upper tail of the scalar exponential series.  Multiplication by
`exp (-s)` turns this into the usual Poisson tail when `α = 1`. -/
noncomputable def exponentialTail (s α : ℝ) (N : ℕ) : ℝ :=
  ∑' n : ℕ, if N ≤ n then (s * α) ^ n / n.factorial else 0

theorem exponentialTail_summable (s α : ℝ) (N : ℕ) :
    Summable (fun n : ℕ => if N ≤ n then
      (s * α) ^ n / n.factorial else 0) := by
  have h := Real.summable_pow_div_factorial (s * α)
  have heq :
      (fun n : ℕ => if N ≤ n then (s * α) ^ n / n.factorial else 0) =
        Set.indicator {n : ℕ | N ≤ n}
          (fun n : ℕ => (s * α) ^ n / n.factorial) := by
    funext n
    by_cases hn : N ≤ n <;> simp [Set.indicator, hn]
  rw [heq]
  exact h.indicator {n : ℕ | N ≤ n}

/-- Vanishing of all entries before step `N`, together with a column bound,
dominates the influence exponential by the scalar exponential tail. -/
theorem influenceExponentialEntry_le_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (α s : ℝ) (N : ℕ) (j i : ι)
    (hC : ∀ j i, 0 ≤ C j i) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hcol : ∀ i, ∑ j, C j i ≤ α)
    (hvanish : ∀ n < N, (C ^ n) j i = 0) :
    influenceExponentialEntry C s j i ≤ exponentialTail s α N := by
  let term : ℕ → ℝ := fun n => (s ^ n / n.factorial) * (C ^ n) j i
  let major : ℕ → ℝ := fun n => (s * α) ^ n / n.factorial
  let tail : ℕ → ℝ := fun n => if N ≤ n then major n else 0
  have hpow0 := influence_power_nonneg C hC
  have hpowBound := influence_power_le_columnBound C α hC hα hcol
  have hmajor : Summable major := Real.summable_pow_div_factorial _
  have hterm0 : ∀ n, 0 ≤ term n := fun n =>
    mul_nonneg (by positivity) (hpow0 n j i)
  have htermMajor : ∀ n, term n ≤ major n := by
    intro n
    dsimp only [term, major]
    calc
      (s ^ n / n.factorial) * (C ^ n) j i ≤
          (s ^ n / n.factorial) * α ^ n :=
        mul_le_mul_of_nonneg_left (hpowBound n j i) (by positivity)
      _ = (s * α) ^ n / n.factorial := by rw [mul_pow]; ring
  have htermSum : Summable term :=
    Summable.of_nonneg_of_le hterm0 htermMajor hmajor
  have htailSum : Summable tail := by
    dsimp only [tail, major]
    exact exponentialTail_summable s α N
  have htermTail : ∀ n, term n ≤ tail n := by
    intro n
    by_cases hn : N ≤ n
    · simp only [tail, if_pos hn]
      exact htermMajor n
    · have hn' : n < N := Nat.lt_of_not_ge hn
      simp only [tail, if_neg hn]
      dsimp only [term]
      rw [hvanish n hn', mul_zero]
  rw [influenceExponentialEntry, exponentialTail]
  exact htermSum.tsum_le_tsum htermTail htailSum

/-- Finite interaction range supplies the vanishing premise of the preceding
tail theorem. -/
theorem finiteRange_influenceExponentialEntry_le_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (dist : ι → ι → ℕ) (R : ℕ)
    (α s : ℝ) (N : ℕ) (j i : ι)
    (hC : ∀ j i, 0 ≤ C j i) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hcol : ∀ i, ∑ j, C j i ≤ α)
    (hdrefl : ∀ i, dist i i = 0)
    (hdtri : ∀ i l j, dist i j ≤ dist i l + dist l j)
    (hlocal : ∀ j i, R < dist i j → C j i = 0)
    (hfar : ∀ n < N, n * R < dist i j) :
    influenceExponentialEntry C s j i ≤ exponentialTail s α N := by
  apply influenceExponentialEntry_le_tail C α s N j i hC hα hs hcol
  intro n hn
  exact influence_power_eq_zero_of_distance C dist R hdrefl hdtri hlocal
    n j i (hfar n hn)

/-- Dobrushin's continuous-time uniformization kernel. -/
noncomputable def dobrushinKernelEntry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (ρ t : ℝ) (j i : ι) : ℝ :=
  Real.exp (-(ρ * t)) * influenceExponentialEntry C (ρ * t) j i

/-- Exact uniformization form of `exp(-ρt(I-C))`, entry by entry. -/
theorem dobrushinKernelEntry_eq_uniformized_exponential
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (ρ t : ℝ) (j i : ι) :
    dobrushinKernelEntry C ρ t j i =
      (Real.exp (-(ρ * t)) •
        Matrix.exponentialEntry ((ρ * t) • C)) j i := by
  rw [dobrushinKernelEntry,
    influenceExponentialEntry_eq_exponentialEntry_smul]
  rfl

theorem finiteRange_dobrushinKernelEntry_le_poissonTail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (dist : ι → ι → ℕ) (R : ℕ)
    (α ρ t : ℝ) (N : ℕ) (j i : ι)
    (hC : ∀ j i, 0 ≤ C j i) (hα : 0 ≤ α)
    (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hcol : ∀ i, ∑ j, C j i ≤ α)
    (hdrefl : ∀ i, dist i i = 0)
    (hdtri : ∀ i l j, dist i j ≤ dist i l + dist l j)
    (hlocal : ∀ j i, R < dist i j → C j i = 0)
    (hfar : ∀ n < N, n * R < dist i j) :
    dobrushinKernelEntry C ρ t j i ≤
      Real.exp (-(ρ * t)) * exponentialTail (ρ * t) α N := by
  unfold dobrushinKernelEntry
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  exact finiteRange_influenceExponentialEntry_le_tail C dist R α (ρ * t)
    N j i hC hα (mul_nonneg hρ ht) hcol hdrefl hdtri hlocal hfar

end DobrushinInfluencePoissonTail
end NCG
