/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.OperationalLightCone

/-!
# Exponential operational light cone and Combes--Thomas screen

The finite-time propagators below are written by their convergent power
series.  This makes the passage from the per-power corner estimate to the
influence-matrix exponential and to the weighted Combes--Thomas estimate
literal.
-/

open Matrix
open scoped Norms.L2Operator

namespace NCG
namespace OperationalLightConeExponential

/-- The `(j,i)` corner of the bounded-generator exponential, displayed as its
absolutely convergent series. -/
noncomputable def generatorCornerSeries {H ι : Type*} [Fintype H]
    [DecidableEq H] (Q : ι → Matrix H H ℂ) (L : Matrix H H ℂ)
    (t : ℝ) (j i : ι) : Matrix H H ℂ :=
  ∑' n : ℕ, ((t ^ n / n.factorial : ℝ) : ℂ) • (Q j * L ^ n * Q i)

/-- The entrywise influence-matrix exponential, displayed as its nonnegative
power series. -/
noncomputable def influenceExponentialEntry {ι : Type*} [Fintype ι]
    [DecidableEq ι] (C : Matrix ι ι ℝ) (s : ℝ) (j i : ι) : ℝ :=
  ∑' n : ℕ, (s ^ n / n.factorial) * (C ^ n) j i

/-- Weighted column control propagates through every path length. -/
theorem weighted_influence_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (d : ι → ι → ℝ) (mu kappa : ℝ)
    (hC : ∀ j i, 0 ≤ C j i)
    (hdrefl : ∀ i, d i i = 0)
    (hdtri : ∀ i l j, d i j ≤ d i l + d l j)
    (hmu : 0 ≤ mu) (hkappa : 0 ≤ kappa)
    (hcol : ∀ i, ∑ j, Real.exp (mu * d i j) * C j i ≤ kappa) :
    ∀ n j i,
      Real.exp (mu * d i j) * (C ^ n) j i ≤ kappa ^ n := by
  have hpow_nonneg : ∀ n j i, 0 ≤ (C ^ n) j i := by
    intro n
    induction n with
    | zero =>
        intro j i
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
    | succ n ih =>
        intro j i
        rw [pow_succ, Matrix.mul_apply]
        exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih j l) (hC l i))
  intro n
  induction n with
  | zero =>
      intro j i
      by_cases hji : j = i
      · subst j
        simp [hdrefl]
      · simp [Matrix.one_apply_ne hji]
  | succ n ih =>
      intro j i
      rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
      calc
        ∑ l, Real.exp (mu * d i j) * ((C ^ n) j l * C l i)
            ≤ ∑ l, (Real.exp (mu * d l j) * (C ^ n) j l) *
                (Real.exp (mu * d i l) * C l i) := by
              apply Finset.sum_le_sum
              intro l _
              have hdist : mu * d i j ≤ mu * d l j + mu * d i l := by
                nlinarith [mul_le_mul_of_nonneg_left (hdtri i l j) hmu]
              have hexp := Real.exp_le_exp.mpr hdist
              rw [Real.exp_add] at hexp
              calc
                Real.exp (mu * d i j) * ((C ^ n) j l * C l i)
                    ≤ (Real.exp (mu * d l j) * Real.exp (mu * d i l)) *
                        ((C ^ n) j l * C l i) :=
                      mul_le_mul_of_nonneg_right hexp
                        (mul_nonneg (hpow_nonneg n j l) (hC l i))
                _ = (Real.exp (mu * d l j) * (C ^ n) j l) *
                    (Real.exp (mu * d i l) * C l i) := by ring
        _ ≤ ∑ l, kappa ^ n * (Real.exp (mu * d i l) * C l i) := by
              apply Finset.sum_le_sum
              intro l _
              exact mul_le_mul_of_nonneg_right (ih j l)
                (mul_nonneg (Real.exp_nonneg _) (hC l i))
        _ = kappa ^ n * ∑ l, Real.exp (mu * d i l) * C l i := by
              rw [Finset.mul_sum]
        _ ≤ kappa ^ n * kappa :=
              mul_le_mul_of_nonneg_left (hcol i) (pow_nonneg hkappa n)
        _ = kappa ^ (n + 1) := by rw [pow_succ]

/-- Removing the exponential weight gives the usual pathwise
Combes--Thomas estimate. -/
theorem influence_power_combesThomas {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (d : ι → ι → ℝ) (mu kappa : ℝ)
    (hC : ∀ j i, 0 ≤ C j i)
    (hdrefl : ∀ i, d i i = 0)
    (hdtri : ∀ i l j, d i j ≤ d i l + d l j)
    (hmu : 0 ≤ mu) (hkappa : 0 ≤ kappa)
    (hcol : ∀ i, ∑ j, Real.exp (mu * d i j) * C j i ≤ kappa) :
    ∀ n j i,
      (C ^ n) j i ≤ Real.exp (-mu * d i j) * kappa ^ n := by
  intro n j i
  have h := weighted_influence_power C d mu kappa hC hdrefl hdtri
    hmu hkappa hcol n j i
  calc
    (C ^ n) j i = Real.exp (-mu * d i j) *
        (Real.exp (mu * d i j) * (C ^ n) j i) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    _ ≤ Real.exp (-mu * d i j) * kappa ^ n :=
      mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)

/-- Summing the pathwise bounds gives the bounded-generator
Combes--Thomas light cone.  The left side is the literal operator exponential
series and the right side is the closed scalar exponential. -/
theorem generatorCornerSeries_combesThomas {H ι : Type*}
    [Fintype H] [DecidableEq H] [Fintype ι]
    (Q : ι → Matrix H H ℂ) (L : Matrix H H ℂ)
    (hsum : ∑ l, Q l = 1)
    (hproj : ∀ l, Q l * Q l = Q l)
    (hnorm : ∀ l, ‖Q l‖ ≤ 1)
    (horth : ∀ l l', l ≠ l' → Q l * Q l' = 0)
    (d : ι → ι → ℝ) (mu kappa : ℝ)
    (hdrefl : ∀ i, d i i = 0)
    (hdtri : ∀ i l j, d i j ≤ d i l + d l j)
    (hmu : 0 ≤ mu) (hkappa : 0 ≤ kappa)
    (hcol : ∀ i, ∑ j, Real.exp (mu * d i j) *
      ‖Q j * L * Q i‖ ≤ kappa)
    (t : ℝ) (j i : ι) :
    ‖generatorCornerSeries Q L t j i‖ ≤
      Real.exp (-mu * d i j + |t| * kappa) := by
  classical
  let C : Matrix ι ι ℝ := Matrix.of fun a b => ‖Q a * L * Q b‖
  have hC : ∀ a b, 0 ≤ C a b := by
    intro a b
    simp only [C, Matrix.of_apply]
    exact norm_nonneg _
  have hpow : ∀ n a b, ‖Q a * L ^ n * Q b‖ ≤ (C ^ n) a b :=
    operational_light_cone Q L hsum hproj hnorm horth
  have hCT : ∀ n a b,
      (C ^ n) a b ≤ Real.exp (-mu * d b a) * kappa ^ n :=
    influence_power_combesThomas C d mu kappa hC hdrefl hdtri hmu hkappa
      (by simpa only [C, Matrix.of_apply] using hcol)
  let major : ℕ → ℝ := fun n =>
    Real.exp (-mu * d i j) * ((|t| * kappa) ^ n / n.factorial)
  have hmajor : Summable major := by
    dsimp only [major]
    exact (Real.summable_pow_div_factorial (|t| * kappa)).mul_left _
  have hterm : ∀ n : ℕ,
      ‖((t ^ n / n.factorial : ℝ) : ℂ) • (Q j * L ^ n * Q i)‖ ≤ major n := by
    intro n
    rw [norm_smul]
    have hcoef : ‖((t ^ n / n.factorial : ℝ) : ℂ)‖ =
        |t| ^ n / n.factorial := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow]
      simp
    rw [hcoef]
    have hnfac : 0 ≤ |t| ^ n / (n.factorial : ℝ) := by positivity
    calc
      (|t| ^ n / n.factorial) * ‖Q j * L ^ n * Q i‖
          ≤ (|t| ^ n / n.factorial) * (C ^ n) j i :=
            mul_le_mul_of_nonneg_left (hpow n j i) hnfac
      _ ≤ (|t| ^ n / n.factorial) *
          (Real.exp (-mu * d i j) * kappa ^ n) :=
            mul_le_mul_of_nonneg_left (hCT n j i) hnfac
      _ = major n := by
            dsimp only [major]
            rw [mul_pow]
            ring
  have hseries : Summable fun n : ℕ =>
      ((t ^ n / n.factorial : ℝ) : ℂ) • (Q j * L ^ n * Q i) :=
    Summable.of_norm (Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) hterm hmajor)
  rw [generatorCornerSeries]
  calc
    ‖∑' n : ℕ, ((t ^ n / n.factorial : ℝ) : ℂ) •
        (Q j * L ^ n * Q i)‖
        ≤ ∑' n : ℕ, ‖((t ^ n / n.factorial : ℝ) : ℂ) •
          (Q j * L ^ n * Q i)‖ := norm_tsum_le_tsum_norm hseries.norm
    _ ≤ ∑' n : ℕ, major n := hseries.norm.tsum_le_tsum hterm hmajor
    _ = Real.exp (-mu * d i j) * Real.exp (|t| * kappa) := by
      dsimp only [major]
      rw [tsum_mul_left]
      congr 1
      have hexp : (∑' n : ℕ, (|t| * kappa) ^ n / n.factorial) =
          Real.exp (|t| * kappa) := by
        rw [Real.exp_eq_exp_ℝ,
          congrFun (NormedSpace.exp_eq_tsum ℝ) (|t| * kappa)]
        apply tsum_congr
        intro n
        simp only [smul_eq_mul]
        rw [div_eq_mul_inv]
        ring
      exact hexp
    _ = Real.exp (-mu * d i j + |t| * kappa) := by
      rw [Real.exp_add]

/-- Direct summation of the per-power path estimate gives the exact
influence-matrix exponential entry.  The auxiliary column bound is only the
automatic finite-dimensional summability certificate. -/
theorem generatorCornerSeries_le_influenceExponential {H ι : Type*}
    [Fintype H] [DecidableEq H] [Fintype ι] [DecidableEq ι]
    (Q : ι → Matrix H H ℂ) (L : Matrix H H ℂ)
    (hsum : ∑ l, Q l = 1)
    (hproj : ∀ l, Q l * Q l = Q l)
    (hnorm : ∀ l, ‖Q l‖ ≤ 1)
    (horth : ∀ l l', l ≠ l' → Q l * Q l' = 0)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hcol : ∀ i, ∑ j, ‖Q j * L * Q i‖ ≤ kappa)
    (t : ℝ) (j i : ι) :
    ‖generatorCornerSeries Q L t j i‖ ≤
      influenceExponentialEntry
        (Matrix.of fun a b : ι => ‖Q a * L * Q b‖) |t| j i := by
  classical
  let C : Matrix ι ι ℝ := Matrix.of fun a b => ‖Q a * L * Q b‖
  have hC : ∀ a b, 0 ≤ C a b := by
    intro a b
    simp only [C, Matrix.of_apply]
    exact norm_nonneg _
  have hCpow : ∀ n a b, 0 ≤ (C ^ n) a b := by
    intro n
    induction n with
    | zero =>
        intro a b
        by_cases hab : a = b <;> simp [hab]
    | succ n ih =>
        intro a b
        rw [pow_succ, Matrix.mul_apply]
        exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih a l) (hC l b))
  have hpow : ∀ n a b, ‖Q a * L ^ n * Q b‖ ≤ (C ^ n) a b :=
    operational_light_cone Q L hsum hproj hnorm horth
  have hCbound : ∀ n a b, (C ^ n) a b ≤ kappa ^ n := by
    let d0 : ι → ι → ℝ := fun _ _ => 0
    intro n a b
    have h := influence_power_combesThomas C d0 0 kappa hC
      (fun _ => rfl) (fun _ _ _ => by dsimp only [d0]; norm_num)
      (le_refl 0) hkappa
      (by
        intro x
        simpa only [d0, zero_mul, Real.exp_zero, one_mul, C,
          Matrix.of_apply] using hcol x)
      n a b
    simpa only [d0, zero_mul, neg_zero, Real.exp_zero, one_mul] using h
  let term : ℕ → ℝ := fun n =>
    (|t| ^ n / n.factorial) * (C ^ n) j i
  let major : ℕ → ℝ := fun n => (|t| * kappa) ^ n / n.factorial
  have hmajor : Summable major := Real.summable_pow_div_factorial _
  have hterm_nonneg : ∀ n, 0 ≤ term n := by
    intro n
    exact mul_nonneg (by positivity) (hCpow n j i)
  have hterm_major : ∀ n, term n ≤ major n := by
    intro n
    dsimp only [term, major]
    have hc := hCbound n j i
    have hcoef : 0 ≤ |t| ^ n / (n.factorial : ℝ) := by positivity
    calc
      (|t| ^ n / n.factorial) * (C ^ n) j i
          ≤ (|t| ^ n / n.factorial) * kappa ^ n :=
            mul_le_mul_of_nonneg_left hc hcoef
      _ = (|t| * kappa) ^ n / n.factorial := by
            rw [mul_pow]
            ring
  have hterm_sum : Summable term :=
    Summable.of_nonneg_of_le hterm_nonneg hterm_major hmajor
  have hop_bound : ∀ n : ℕ,
      ‖((t ^ n / n.factorial : ℝ) : ℂ) • (Q j * L ^ n * Q i)‖ ≤ term n := by
    intro n
    rw [norm_smul]
    have hcoef : ‖((t ^ n / n.factorial : ℝ) : ℂ)‖ =
        |t| ^ n / n.factorial := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow]
      simp
    rw [hcoef]
    exact mul_le_mul_of_nonneg_left (hpow n j i) (by positivity)
  have hop_sum : Summable fun n : ℕ =>
      ((t ^ n / n.factorial : ℝ) : ℂ) • (Q j * L ^ n * Q i) :=
    Summable.of_norm (Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) hop_bound hterm_sum)
  rw [generatorCornerSeries]
  change _ ≤ influenceExponentialEntry C |t| j i
  rw [influenceExponentialEntry]
  calc
    ‖∑' n : ℕ, ((t ^ n / n.factorial : ℝ) : ℂ) •
        (Q j * L ^ n * Q i)‖
        ≤ ∑' n : ℕ, ‖((t ^ n / n.factorial : ℝ) : ℂ) •
          (Q j * L ^ n * Q i)‖ := norm_tsum_le_tsum_norm hop_sum.norm
    _ ≤ ∑' n : ℕ, term n := hop_sum.norm.tsum_le_tsum hop_bound hterm_sum
    _ = ∑' n : ℕ, (|t| ^ n / n.factorial) * (C ^ n) j i := rfl

end OperationalLightConeExponential
end NCG
