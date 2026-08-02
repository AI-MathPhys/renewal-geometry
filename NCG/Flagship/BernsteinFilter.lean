/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Inter-cluster Bernstein filter
  (`thm:cluster-Bernstein-filter-master`, flagship manuscript)

For a `[0,1]`-valued cluster indicator `f` on `[λ₋, λ₊]` with
Lipschitz constant `Δ⁻¹` (inverse inter-cluster separation), the
Bernstein polynomial of degree `n` in the normalized variable
`x = (λ - λ₋)/R` satisfies the two boxed bounds:

* positivity `0 ≤ p_{a,n}(λ) ≤ 1`
  (`bernstein_filter_mem_unit`, convex weights);
* the error bound `|p_{a,n}(λ) - f(λ)| ≤ R/(2Δ√n)` at every
  `λ ∈ [λ₋, λ₊]` (`cluster_bernstein_filter`, via the Bernstein
  variance identity, Cauchy–Schwarz, and `x(1-x) ≤ 1/4`).

The filter degree depends on the inter-cluster separation only —
the prose consequence about merging in-cluster collisions is
interpretive.  We reuse Mathlib's `bernstein` basis on the unit
interval together with `bernstein.probability` and
`bernstein.variance`.
-/

open Finset
open scoped unitInterval

namespace NCG

/-- Convex-weight positivity: a Bernstein filter with grid values
in `[0,1]` stays in `[0,1]`. -/
theorem bernstein_filter_mem_unit {n : ℕ} (x : I)
    (g : Fin (n + 1) → ℝ)
    (hg : ∀ k, g k ∈ Set.Icc (0 : ℝ) 1) :
    (∑ k : Fin (n + 1), g k * bernstein n k x) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hg k).1 bernstein_nonneg
  · calc ∑ k : Fin (n + 1), g k * bernstein n k x
        ≤ ∑ k : Fin (n + 1), bernstein n k x :=
          Finset.sum_le_sum fun k _ =>
            mul_le_of_le_one_left bernstein_nonneg (hg k).2
    _ = 1 := bernstein.probability n x

/-- Core quantitative Bernstein bound: if the grid values differ
from `c` by at most `L·|x - k/n|`, the filter differs from `c` by
at most `L/(2√n)`. -/
theorem bernstein_filter_error {n : ℕ} (hn : n ≠ 0) (x : I)
    (g : Fin (n + 1) → ℝ) (c L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ k : Fin (n + 1),
      |g k - c| ≤ L * |(x : ℝ) - (k : ℝ) / n|) :
    |(∑ k : Fin (n + 1), g k * bernstein n k x) - c|
      ≤ L / (2 * Real.sqrt n) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hdiff : (∑ k : Fin (n + 1), g k * bernstein n k x) - c
      = ∑ k : Fin (n + 1), (g k - c) * bernstein n k x := by
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      bernstein.probability n x, mul_one]
  set S : ℝ :=
    ∑ k : Fin (n + 1), |(x : ℝ) - (k : ℝ) / n| * bernstein n k x
    with hSdef
  have hS0 : 0 ≤ S :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg _) bernstein_nonneg
  have habs : |(∑ k : Fin (n + 1), g k * bernstein n k x) - c| ≤ L * S := by
    rw [hdiff]
    calc |∑ k : Fin (n + 1), (g k - c) * bernstein n k x|
        ≤ ∑ k : Fin (n + 1), |(g k - c) * bernstein n k x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin (n + 1), L * (|(x : ℝ) - (k : ℝ) / n| * bernstein n k x)
          := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_nonneg
            (bernstein_nonneg (n := n) (ν := k) (x := x)),
            ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hg k)
            bernstein_nonneg
      _ = L * S := by rw [hSdef, Finset.mul_sum]
  have hvar := bernstein.variance hn x
  have hCS : S ^ 2 ≤ (x : ℝ) * (1 - x) / n := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k : Fin (n + 1) =>
        |(x : ℝ) - (k : ℝ) / n| * Real.sqrt (bernstein n k x))
      (fun k : Fin (n + 1) => Real.sqrt (bernstein n k x))
    have h2 : ∀ k : Fin (n + 1),
        (|(x : ℝ) - (k : ℝ) / n| * Real.sqrt (bernstein n k x))
            * Real.sqrt (bernstein n k x)
          = |(x : ℝ) - (k : ℝ) / n| * bernstein n k x := by
      intro k
      rw [mul_assoc, Real.mul_self_sqrt bernstein_nonneg]
    have h3 : ∀ k : Fin (n + 1),
        (|(x : ℝ) - (k : ℝ) / n| * Real.sqrt (bernstein n k x))
            ^ 2
          = ((x : ℝ) - (k : ℝ) / n) ^ 2 * bernstein n k x := by
      intro k
      rw [mul_pow, sq_abs, Real.sq_sqrt bernstein_nonneg]
    have h4 : ∀ k : Fin (n + 1),
        Real.sqrt (bernstein n k x) ^ 2 = bernstein n k x :=
      fun k => Real.sq_sqrt bernstein_nonneg
    rw [Finset.sum_congr rfl fun k _ => h2 k,
      Finset.sum_congr rfl fun k _ => h3 k,
      Finset.sum_congr rfl fun k _ => h4 k] at h1
    calc S ^ 2
        ≤ (∑ k : Fin (n + 1),
            ((x : ℝ) - (k : ℝ) / n) ^ 2 * bernstein n k x)
          * (∑ k : Fin (n + 1), bernstein n k x) := h1
      _ = (x : ℝ) * (1 - x) / n := by
          rw [bernstein.probability n x, mul_one, ← hvar]
          exact Finset.sum_congr rfl fun k _ => by
            simp [bernstein.z]
  have hquarter : (x : ℝ) * (1 - x) / n ≤ 1 / (4 * n) := by
    have hx0 : (0 : ℝ) ≤ x := x.2.1
    have hx1 : (x : ℝ) ≤ 1 := x.2.2
    have h5 : (x : ℝ) * (1 - x) ≤ 1 / 4 := by
      nlinarith [sq_nonneg ((x : ℝ) - 1 / 2)]
    have h6 : (x : ℝ) * (1 - x) / n ≤ (1 / 4) / n := by gcongr
    calc (x : ℝ) * (1 - x) / n ≤ (1 / 4) / n := h6
      _ = 1 / (4 * n) := by ring
  have hSle : S ≤ 1 / (2 * Real.sqrt n) := by
    have h6 : S = Real.sqrt (S ^ 2) := (Real.sqrt_sq hS0).symm
    have h7 : Real.sqrt (S ^ 2) ≤ Real.sqrt (1 / (4 * n)) :=
      Real.sqrt_le_sqrt (hCS.trans hquarter)
    have h8 : Real.sqrt (1 / (4 * n))
        = 1 / (2 * Real.sqrt n) := by
      rw [show (1 : ℝ) / (4 * n)
          = (1 / (2 * Real.sqrt n)) ^ 2 from by
        rw [div_pow, mul_pow, Real.sq_sqrt hnpos.le]
        norm_num]
      exact Real.sqrt_sq (by positivity)
    rw [h6]
    rw [h8] at h7
    exact h7
  calc |(∑ k : Fin (n + 1), g k * bernstein n k x) - c| ≤ L * S := habs
    _ ≤ L * (1 / (2 * Real.sqrt n)) :=
        mul_le_mul_of_nonneg_left hSle hL
    _ = L / (2 * Real.sqrt n) := by ring

/-- `thm:cluster-Bernstein-filter-master`, both boxed bounds:
the Bernstein filter of a `Δ⁻¹`-Lipschitz `[0,1]`-valued cluster
indicator stays in `[0,1]` and approximates it within
`R/(2Δ√n)` on the whole window. -/
theorem cluster_bernstein_filter {n : ℕ} (hn : n ≠ 0)
    (lamlo lamhi Δ : ℝ) (hlt : lamlo < lamhi) (hΔ : 0 < Δ)
    (f : ℝ → ℝ)
    (hf01 : ∀ t ∈ Set.Icc lamlo lamhi, f t ∈ Set.Icc (0 : ℝ) 1)
    (hlip : ∀ s t, s ∈ Set.Icc lamlo lamhi →
      t ∈ Set.Icc lamlo lamhi → |f s - f t| ≤ Δ⁻¹ * |s - t|)
    (lam : ℝ) (hlam : lam ∈ Set.Icc lamlo lamhi) (x : I)
    (hx : (x : ℝ) = (lam - lamlo) / (lamhi - lamlo)) :
    (∑ k : Fin (n + 1),
        f (lamlo + (lamhi - lamlo) * ((k : ℝ) / n))
          * bernstein n k x) ∈ Set.Icc (0 : ℝ) 1
    ∧ |(∑ k : Fin (n + 1),
          f (lamlo + (lamhi - lamlo) * ((k : ℝ) / n))
            * bernstein n k x) - f lam|
        ≤ (lamhi - lamlo) / (2 * Δ * Real.sqrt n) := by
  have hR : 0 < lamhi - lamlo := sub_pos.mpr hlt
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hgrid : ∀ k : Fin (n + 1),
      lamlo + (lamhi - lamlo) * ((k : ℝ) / n)
        ∈ Set.Icc lamlo lamhi := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
    have hk1 : (k : ℝ) / n ≤ 1 := by
      rw [div_le_one hnpos]
      exact_mod_cast k.is_le
    exact ⟨by nlinarith, by nlinarith⟩
  refine ⟨bernstein_filter_mem_unit x _
    (fun k => hf01 _ (hgrid k)), ?_⟩
  have hlam_eq : lam = lamlo + (lamhi - lamlo) * (x : ℝ) := by
    rw [hx, mul_div_cancel₀ _ hR.ne']
    ring
  have hg : ∀ k : Fin (n + 1),
      |f (lamlo + (lamhi - lamlo) * ((k : ℝ) / n)) - f lam|
        ≤ ((lamhi - lamlo) / Δ)
            * |(x : ℝ) - (k : ℝ) / n| := by
    intro k
    have h1 := hlip _ _ (hgrid k) hlam
    have h2 : lamlo + (lamhi - lamlo) * ((k : ℝ) / n) - lam
        = (lamhi - lamlo) * ((k : ℝ) / n - (x : ℝ)) := by
      rw [hlam_eq]
      ring
    calc |f (lamlo + (lamhi - lamlo) * ((k : ℝ) / n)) - f lam|
        ≤ Δ⁻¹ * |lamlo + (lamhi - lamlo) * ((k : ℝ) / n) - lam|
          := h1
      _ = ((lamhi - lamlo) / Δ) * |(x : ℝ) - (k : ℝ) / n| := by
          rw [h2, abs_mul, abs_of_pos hR,
            abs_sub_comm ((k : ℝ) / n) (x : ℝ)]
          ring
  have herr := bernstein_filter_error hn x
    (fun k => f (lamlo + (lamhi - lamlo) * ((k : ℝ) / n)))
    (f lam) ((lamhi - lamlo) / Δ)
    (div_nonneg hR.le hΔ.le) hg
  calc |(∑ k : Fin (n + 1),
        f (lamlo + (lamhi - lamlo) * ((k : ℝ) / n))
          * bernstein n k x) - f lam|
      ≤ ((lamhi - lamlo) / Δ) / (2 * Real.sqrt n) := herr
    _ = (lamhi - lamlo) / (2 * Δ * Real.sqrt n) := by
        ring

end NCG
