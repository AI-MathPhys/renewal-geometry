/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Abel reduction of the one-variable tensor
  (`prop:old-abel`, `cor:old-zero`, arithmetic monograph)

* `tail_integral` — `∫_n^∞ x^{-s-1} dx = n^{-s}/s` for `Re s > 0`;
* `abel_reduction` — the Abel/Mellin interchange: for an absolutely
  `n^{-Re s}`-summable coefficient sequence,
  `∫_1^∞ (Σ_{n≤x} c(n)) x^{-s-1} dx = (1/s) Σ_n c(n) n^{-s}`
  (the summand indexed by `n` contributes exactly for `x ≥ n`);
* `abel_reduction_shifted` — the shifted-product instantiation
  `c(n) = a_i(n) a_j(n+h)` of the display (`h ≥ 0`; negative shifts
  relabel the two ports);
* `old_zero` — `cor:old-zero`: at shift `h = 0` with
  `a_i = Λ·ρ_i`, the diagonal slice is
  `(1/s) Σ Λ(n)² ρ_i(n) ρ_j(n) n^{-s}` — the coefficient is
  `Λ²ρ_iρ_j`, not the `a_i·conj a_j` of a Hermitian Gram entry
  (the non-identification with `L` or `-L'/L` is the disclosed
  prose clause).

The manuscript assumes only `s ≠ 0`; the tail integrals require
`Re s > 0`, which is the hypothesis used here.
-/

namespace NCG

open MeasureTheory Set Complex

open scoped ArithmeticFunction

noncomputable section

/-- The window accumulation `A(x) = Σ_{n ≤ x} c(n)`. -/
def windowSum (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, if (n : ℝ) ≤ x then c n else 0

/-- `∫_n^∞ x^{-s-1} dx = n^{-s}/s` for `Re s > 0`. -/
theorem tail_integral {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    (∫ x : ℝ in Ioi (n : ℝ), (x : ℂ) ^ (-s - 1))
      = (n : ℂ) ^ (-s) / s := by
  have ha : (-s - 1).re < -1 := by
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hc : (0 : ℝ) < n := by exact_mod_cast hn
  rw [integral_Ioi_cpow_of_lt ha hc,
    show (-s - 1 + 1 : ℂ) = -s from by ring, neg_div_neg_eq]
  norm_cast

private lemma cpow_integrableOn_Ioi {s : ℂ} (hs : 0 < s.re) {c : ℝ}
    (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi c) := by
  refine integrableOn_Ioi_cpow_of_lt ?_ hc
  rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
  linarith

private lemma tail_set_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (hn : 1 ≤ n) :
    ∀ g : ℝ → E, IntegrableOn g (Ioi (n : ℝ)) →
      (∫ x : ℝ in Ioi (1 : ℝ) ∩ Ici (n : ℝ), g x)
        = ∫ x : ℝ in Ioi (n : ℝ), g x := by
  intro g _
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hset : Ioi (1 : ℝ) ∩ Ici ((1 : ℕ) : ℝ) = Ioi (1 : ℝ) := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ici, Nat.cast_one]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.le⟩
    rw [hset]
    norm_num
  · have hset : Ioi (1 : ℝ) ∩ Ici (n : ℝ) = Ici (n : ℝ) := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ici]
      constructor
      · exact fun h => h.2
      · intro h
        have h2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
        exact ⟨by linarith, h⟩
    rw [hset, integral_Ici_eq_integral_Ioi]

/-- `prop:old-abel` (Abel reduction): for `Re s > 0` and an
absolutely summable coefficient sequence,
`∫_1^∞ (Σ_{n≤x} c(n)) x^{-s-1} dx = (1/s) Σ_n c(n) n^{-s}`. -/
theorem abel_reduction (c : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re)
    (hc0 : c 0 = 0)
    (hsum : Summable fun n : ℕ => ‖c n‖ * (n : ℝ) ^ (-s.re)) :
    (∫ x : ℝ in Ioi (1 : ℝ), windowSum c x * (x : ℂ) ^ (-s - 1))
      = (1 / s) * ∑' n : ℕ, c n * (n : ℂ) ^ (-s) := by
  have hsne : s ≠ 0 := fun h => by simp [h] at hs
  -- the summand family
  set f : ℕ → ℝ → ℂ := fun n x =>
    (if (n : ℝ) ≤ x then c n else 0) * (x : ℂ) ^ (-s - 1) with hfdef
  -- pointwise: the integrand is the series of the `f n`
  have hpt : ∀ x : ℝ, windowSum c x * (x : ℂ) ^ (-s - 1)
      = ∑' n : ℕ, f n x := by
    intro x
    rw [windowSum, ← tsum_mul_right]
  -- the base integrable majorants on `(1, ∞)`
  have hbase : ∀ n : ℕ, Integrable
      (fun x : ℝ => c n * (x : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi (1 : ℝ))) :=
    fun n => (cpow_integrableOn_Ioi hs one_pos).const_mul (c n)
  have hshape : ∀ n : ℕ, f n = fun x : ℝ =>
      (Ici (n : ℝ)).indicator
        (fun x => c n * (x : ℂ) ^ (-s - 1)) x := by
    intro n
    funext x
    rw [hfdef, Set.indicator]
    simp only [mem_Ici]
    split_ifs <;> simp
  -- each `f n` is integrable on `(1, ∞)` by domination
  have hint : ∀ n : ℕ,
      Integrable (f n) (volume.restrict (Ioi (1 : ℝ))) := by
    intro n
    refine MeasureTheory.Integrable.mono' (hbase n).norm ?_ ?_
    · rw [hshape n]
      exact ((hbase n).aestronglyMeasurable.indicator
        measurableSet_Ici)
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [hshape n]
      exact norm_indicator_le_norm_self _ _
  -- per-`n` evaluation
  have hval : ∀ n : ℕ, (∫ x : ℝ in Ioi (1 : ℝ), f n x)
      = c n * (n : ℂ) ^ (-s) / s := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | h1
    · subst h0
      have hz : f 0 = fun _ => 0 := by
        funext x
        rw [hfdef]
        simp [hc0]
      rw [hz, hc0]
      simp
    · rw [MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => congrFun (hshape n) x),
        MeasureTheory.setIntegral_indicator measurableSet_Ici,
        tail_set_eq h1 _ ((cpow_integrableOn_Ioi hs
          (by exact_mod_cast h1)).const_mul (c n)),
        MeasureTheory.integral_const_mul, tail_integral hs h1]
      ring
  -- exact norm integrals
  have hnorm : ∀ n : ℕ, (∫ x : ℝ in Ioi (1 : ℝ), ‖f n x‖)
      ≤ ‖c n‖ * (n : ℝ) ^ (-s.re) / s.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | h1
    · subst h0
      have hz : f 0 = fun _ => 0 := by
        funext x
        rw [hfdef]
        simp [hc0]
      rw [hz]
      simp only [norm_zero]
      rw [MeasureTheory.integral_zero]
      positivity
    · have heq : ∀ x ∈ Ioi (1 : ℝ), ‖f n x‖
          = (Ici (n : ℝ)).indicator
              (fun x => ‖c n‖ * x ^ (-s.re - 1)) x := by
        intro x hx
        rw [hfdef, Set.indicator]
        simp only [mem_Ici, mem_Ioi] at hx ⊢
        split_ifs with h
        · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos
            (by linarith),
            show (-s - 1).re = -s.re - 1 by
              rw [Complex.sub_re, Complex.neg_re, Complex.one_re]]
        · simp
      have hrint : IntegrableOn
          (fun x : ℝ => ‖c n‖ * x ^ (-s.re - 1))
          (Ioi ((n : ℕ) : ℝ)) := by
        have hlt : (-s.re - 1 : ℝ) < -1 := by linarith
        exact (integrableOn_Ioi_rpow_of_lt hlt
          (by exact_mod_cast h1)).const_mul ‖c n‖
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq,
        MeasureTheory.setIntegral_indicator measurableSet_Ici,
        tail_set_eq h1 _ hrint,
        MeasureTheory.integral_const_mul]
      have htail : (∫ x : ℝ in Ioi ((n : ℕ) : ℝ),
          x ^ (-s.re - 1)) = ((n : ℕ) : ℝ) ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith)
          (by exact_mod_cast h1),
          show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq]
      rw [htail, mul_div_assoc]
  have hsum2 : Summable fun n : ℕ =>
      ∫ x : ℝ in Ioi (1 : ℝ), ‖f n x‖ := by
    refine Summable.of_nonneg_of_le
      (fun n => MeasureTheory.integral_nonneg fun x => norm_nonneg _)
      hnorm ?_
    exact hsum.div_const s.re
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall hpt),
    ← MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum2]
  rw [tsum_congr hval]
  rw [show (∑' n : ℕ, c n * (n : ℂ) ^ (-s) / s)
      = (∑' n : ℕ, c n * (n : ℂ) ^ (-s)) / s from
    tsum_div_const]
  rw [div_eq_mul_inv, one_div, mul_comm]

/-- `prop:old-abel` (shifted-product form): the display instance
`c(n) = a_i(n)·a_j(n+h)` for a nonnegative shift (negative shifts
relabel the two ports). -/
theorem abel_reduction_shifted (a b : ℕ → ℂ) (h : ℕ) {s : ℂ}
    (hs : 0 < s.re) (ha0 : a 0 = 0)
    (hsum : Summable fun n : ℕ =>
      ‖a n * b (n + h)‖ * (n : ℝ) ^ (-s.re)) :
    (∫ x : ℝ in Ioi (1 : ℝ),
        windowSum (fun n => a n * b (n + h)) x * (x : ℂ) ^ (-s - 1))
      = (1 / s) * ∑' n : ℕ, a n * b (n + h) * (n : ℂ) ^ (-s) :=
  abel_reduction _ hs (by rw [ha0, zero_mul]) hsum

/-- `cor:old-zero`: the zero-shift slice with `a_i = Λ·ρ_i` has
coefficient `Λ(n)²ρ_i(n)ρ_j(n)` — a squared, unconjugated weight,
not a Hermitian Gram entry. -/
theorem old_zero (ρi ρj : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable fun n : ℕ =>
      ‖(Λ n : ℂ) * ρi n * ((Λ n : ℂ) * ρj n)‖ * (n : ℝ) ^ (-s.re)) :
    (∫ x : ℝ in Ioi (1 : ℝ),
        windowSum (fun n => (Λ n : ℂ) * ρi n * ((Λ n : ℂ) * ρj n)) x
          * (x : ℂ) ^ (-s - 1))
      = (1 / s) * ∑' n : ℕ,
          (Λ n : ℂ) ^ 2 * ρi n * ρj n * (n : ℂ) ^ (-s) := by
  rw [abel_reduction _ hs (by simp) hsum]
  congr 1
  refine tsum_congr fun n => ?_
  ring

end

end NCG
