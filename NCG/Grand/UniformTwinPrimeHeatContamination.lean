/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.TwinHeat
import NCG.Grand.VonMangoldtProperPrimePowerCorrelations
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Uniform proper-prime-power bound for the twin-prime heat selector

This file discharges the contamination hypothesis in `TwinHeat`.  The
unheated exceptional coefficient has partial sums
`O(√X log X)`, by the von Mangoldt correlation estimate.  Abel summation (in
the packaged L-series criterion) therefore makes the coefficient divided by
`n` summable.  The heat kernel is at most one, so this supplies a single
uniform bound for every positive heat time.
-/

open Finset ArithmeticFunction Set Filter Asymptotics

namespace NCG

/-- The unheated twin correlation coefficient restricted to pairs with a
proper-prime-power coordinate. -/
noncomputable def twinProperPrimePowerCoefficient (n : ℕ) : ℝ :=
  if (IsPrimePow n ∧ ¬ n.Prime) ∨
      (IsPrimePow (n + 2) ∧ ¬ (n + 2).Prime)
    then Λ n * Λ (n + 2) else 0

theorem twinProperPrimePowerCoefficient_nonneg (n : ℕ) :
    0 ≤ twinProperPrimePowerCoefficient n := by
  rw [twinProperPrimePowerCoefficient]
  split_ifs
  · exact mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
  · exact le_rfl

/-- The exceptional coefficient has partial sums `O(X^(3/4))`; this slightly
weaker power form is convenient for the L-series convergence criterion. -/
theorem twinProperPrimePowerCoefficient_partialSum_bigO :
    (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X,
      twinProperPrimePowerCoefficient n)
      =O[Filter.atTop] fun X : ℕ => (X : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hcorr⟩ :=
    exists_properPrimePower_shift_correlation_bound
  refine isBigO_iff.mpr ⟨4 * C * (3 : ℝ) ^ (3 / 4 : ℝ), ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with X hX
  have hsum : (∑ n ∈ Finset.Icc 1 X,
      twinProperPrimePowerCoefficient n)
      ≤ C * Real.sqrt (X + 2) * Real.log (X + 2) := by
    have h := hcorr 2 X hX
    rw [Finset.sum_filter] at h
    norm_num at h
    simpa only [twinProperPrimePowerCoefficient] using h
  have hY0 : (0 : ℝ) ≤ X + 2 := by positivity
  have hlog : Real.log ((X : ℝ) + 2)
      ≤ 4 * ((X : ℝ) + 2) ^ (1 / 4 : ℝ) := by
    calc
      Real.log ((X : ℝ) + 2)
          ≤ ((X : ℝ) + 2) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
            Real.log_le_rpow_div hY0 (by norm_num)
      _ = 4 * ((X : ℝ) + 2) ^ (1 / 4 : ℝ) := by ring
  have hrootlog : Real.sqrt ((X : ℝ) + 2) * Real.log ((X : ℝ) + 2)
      ≤ 4 * ((X : ℝ) + 2) ^ (3 / 4 : ℝ) := by
    calc
      Real.sqrt ((X : ℝ) + 2) * Real.log ((X : ℝ) + 2)
          ≤ Real.sqrt ((X : ℝ) + 2) *
              (4 * ((X : ℝ) + 2) ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)
      _ = 4 * ((X : ℝ) + 2) ^ (3 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            calc
              ((X : ℝ) + 2) ^ (1 / 2 : ℝ) *
                    (4 * ((X : ℝ) + 2) ^ (1 / 4 : ℝ))
                  = 4 * (((X : ℝ) + 2) ^ (1 / 2 : ℝ) *
                    ((X : ℝ) + 2) ^ (1 / 4 : ℝ)) := by ring
              _ = 4 * ((X : ℝ) + 2) ^ (3 / 4 : ℝ) := by
                rw [← Real.rpow_add (by positivity : (0 : ℝ) < (X : ℝ) + 2)]
                congr 2
                norm_num
  have hshift : ((X : ℝ) + 2) ^ (3 / 4 : ℝ)
      ≤ (3 : ℝ) ^ (3 / 4 : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) := by
    have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hle : (X : ℝ) + 2 ≤ 3 * X := by linarith
    calc
      ((X : ℝ) + 2) ^ (3 / 4 : ℝ)
          ≤ (3 * (X : ℝ)) ^ (3 / 4 : ℝ) := by
            exact Real.rpow_le_rpow hY0 hle (by norm_num)
      _ = (3 : ℝ) ^ (3 / 4 : ℝ) *
            (X : ℝ) ^ (3 / 4 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) (by positivity)]
  have hsum0 : 0 ≤ ∑ n ∈ Finset.Icc 1 X,
      twinProperPrimePowerCoefficient n :=
    Finset.sum_nonneg fun n _ => twinProperPrimePowerCoefficient_nonneg n
  rw [Real.norm_of_nonneg hsum0,
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc
    (∑ n ∈ Finset.Icc 1 X, twinProperPrimePowerCoefficient n)
        ≤ C * (Real.sqrt ((X : ℝ) + 2) *
            Real.log ((X : ℝ) + 2)) := by
          simpa only [Nat.cast_add, Nat.cast_ofNat, mul_assoc] using hsum
    _ ≤ C * (4 * ((X : ℝ) + 2) ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hrootlog hC
    _ ≤ 4 * C * ((3 : ℝ) ^ (3 / 4 : ℝ) *
          (X : ℝ) ^ (3 / 4 : ℝ)) := by
          nlinarith [hshift, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (3 / 4 : ℝ)]
    _ = (4 * C * (3 : ℝ) ^ (3 / 4 : ℝ)) *
          (X : ℝ) ^ (3 / 4 : ℝ) := by ring

/-- Dividing the exceptional coefficient by `n` gives a convergent series. -/
theorem twinProperPrimePowerCoefficient_div_summable :
    Summable (fun n : ℕ => twinProperPrimePowerCoefficient n / (n : ℝ)) := by
  have hLS : LSeriesSummable
      (fun n : ℕ => (twinProperPrimePowerCoefficient n : ℂ)) (1 : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (r := (3 / 4 : ℝ)) (s := (1 : ℂ))
      twinProperPrimePowerCoefficient_partialSum_bigO
      twinProperPrimePowerCoefficient_nonneg
      (by norm_num) (by norm_num)
  rw [LSeriesSummable] at hLS
  apply Complex.summable_ofReal.mp
  exact hLS.congr (fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [twinProperPrimePowerCoefficient]
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      simp)

/-- A single finite constant controlling the exceptional twin-heat mass. -/
noncomputable def twinPrimePowerContaminationBound : ℝ :=
  ∑' n : ℕ, twinProperPrimePowerCoefficient n / (n : ℝ)

/-- The non-twin contribution to the heat selector is uniformly bounded for
all positive heat times.  Terms not supported on two prime powers vanish; if
both von Mangoldt factors are nonzero and the pair is not a twin-prime pair,
one coordinate is a proper prime power. -/
theorem twin_heat_contamination_uniform (t : ℝ) (ht : 0 ≤ t) :
    (∑' n : ℕ, if ¬ (n.Prime ∧ (n + 2).Prime)
      then twinTerm t n else 0)
      ≤ twinPrimePowerContaminationBound := by
  let badTerm : ℕ → ℝ := fun n =>
    if ¬ (n.Prime ∧ (n + 2).Prime) then twinTerm t n else 0
  let majorant : ℕ → ℝ := fun n =>
    twinProperPrimePowerCoefficient n / (n : ℝ)
  have hmajorant : Summable majorant :=
    twinProperPrimePowerCoefficient_div_summable
  have hnonneg : ∀ n, 0 ≤ badTerm n := by
    intro n
    by_cases hp : n.Prime ∧ (n + 2).Prime
    · dsimp [badTerm]
      rw [if_neg (not_not_intro hp)]
    · dsimp [badTerm]
      rw [if_pos hp]
      exact twinTerm_nonneg t n
  have hle : ∀ n, badTerm n ≤ majorant n := by
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [badTerm, majorant, twinTerm,
        twinProperPrimePowerCoefficient]
    by_cases hp : n.Prime ∧ (n + 2).Prime
    · have hbadzero : badTerm n = 0 := by
        dsimp [badTerm]
        rw [if_neg (not_not_intro hp)]
      rw [hbadzero]
      exact div_nonneg (twinProperPrimePowerCoefficient_nonneg n)
        (Nat.cast_nonneg n)
    have hbadeq : badTerm n = twinTerm t n := by
      dsimp [badTerm]
      rw [if_pos hp]
    rw [hbadeq]
    by_cases hΛ1 : Λ n = 0
    · rw [twinTerm, hΛ1]
      simp only [zero_mul, zero_div]
      exact div_nonneg (twinProperPrimePowerCoefficient_nonneg n)
        (Nat.cast_nonneg n)
    by_cases hΛ2 : Λ (n + 2) = 0
    · rw [twinTerm, hΛ2]
      simp only [mul_zero, zero_div, zero_mul]
      exact div_nonneg (twinProperPrimePowerCoefficient_nonneg n)
        (Nat.cast_nonneg n)
    have hpp1 : IsPrimePow n := vonMangoldt_ne_zero_iff.mp hΛ1
    have hpp2 : IsPrimePow (n + 2) := vonMangoldt_ne_zero_iff.mp hΛ2
    have hproper : (IsPrimePow n ∧ ¬ n.Prime) ∨
        (IsPrimePow (n + 2) ∧ ¬ (n + 2).Prime) := by
      by_cases hpn : n.Prime
      · exact Or.inr ⟨hpp2, fun hp2 => hp ⟨hpn, hp2⟩⟩
      · exact Or.inl ⟨hpp1, hpn⟩
    have hterm := twinTerm_le_const t ht n hn
    simpa [majorant, twinProperPrimePowerCoefficient, hproper] using hterm
  have hbadSummable : Summable badTerm :=
    Summable.of_nonneg_of_le hnonneg hle hmajorant
  change (∑' n, badTerm n) ≤ ∑' n, majorant n
  exact hbadSummable.tsum_le_tsum hle hmajorant

/-- If the genuine twin-prime set is finite, the full heat selector has a
uniform bound, now with no assumed contamination estimate. -/
theorem twin_heat_bounded_of_finite_exact
    (hfin : {n : ℕ | n.Prime ∧ (n + 2).Prime}.Finite) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → twinHeat t ≤ C := by
  exact twin_heat_bounded_of_finite twinPrimePowerContaminationBound hfin
    (fun t ht _ => twin_heat_contamination_uniform t ht.le)

/-- `thm:twin-heat`: divergence as `t ↓ 0` forces infinitely many twin-prime
pairs.  The proper-prime-power bound is proved internally. -/
theorem twin_heat_sufficiency_exact
    (hdiv : ∀ C : ℝ, ∃ t : ℝ,
      0 < t ∧ t ≤ 1 ∧ C < twinHeat t) :
    {n : ℕ | n.Prime ∧ (n + 2).Prime}.Infinite := by
  exact twin_heat_sufficiency twinPrimePowerContaminationBound
    (fun t ht _ => twin_heat_contamination_uniform t ht.le) hdiv

end NCG
