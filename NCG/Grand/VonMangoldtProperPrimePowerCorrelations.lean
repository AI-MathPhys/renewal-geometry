/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.PrimePowerHL

/-!
# Von Mangoldt bounds for proper-prime-power correlations

This file proves `lem:ar-prime-power` from the Gran-Tensor manuscript.  The
total von Mangoldt mass on proper prime powers is exactly Chebyshev's
`ψ - θ`, hence is `O(√Y)`.  Bounding the other von Mangoldt factor by `log Y`
then gives the two stated correlation estimates.
-/

open Finset ArithmeticFunction

namespace NCG

/-- Total von Mangoldt mass carried by proper prime powers up to `Y`. -/
noncomputable def properPrimePowerMangoldtWeight (Y : ℕ) : ℝ :=
  ∑ n ∈ properPrimePows Y, Λ n

/-- The proper-prime-power Mangoldt mass is exactly `ψ(Y) - θ(Y)`. -/
theorem properPrimePowerMangoldtWeight_eq_psi_sub_theta (Y : ℕ) :
    properPrimePowerMangoldtWeight Y =
      Chebyshev.psi Y - Chebyshev.theta Y := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  classical
  rw [properPrimePowerMangoldtWeight, properPrimePows]
  rw [← Finset.sum_filter_ne_zero
    ((Finset.Ioc 0 ⌊(Y : ℝ)⌋₊).filter fun n => ¬ n.Prime)]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc,
      Nat.floor_natCast]
    constructor
    · rintro ⟨⟨hn1, hnY⟩, hpp, hnp⟩
      exact ⟨⟨⟨by omega, hnY⟩, hnp⟩,
        vonMangoldt_ne_zero_iff.mpr hpp⟩
    · rintro ⟨⟨⟨hn0, hnY⟩, hnp⟩, hne⟩
      exact ⟨⟨by omega, hnY⟩,
        vonMangoldt_ne_zero_iff.mp hne, hnp⟩
  · intro n hn
    rfl

/-- Chebyshev's estimate gives a universal square-root bound for the total
proper-prime-power von Mangoldt mass. -/
theorem properPrimePowerMangoldtWeight_le_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℕ,
      properPrimePowerMangoldtWeight Y ≤ C * Real.sqrt Y := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 0, le_max_right _ _, fun Y => ?_⟩
  rw [properPrimePowerMangoldtWeight_eq_psi_sub_theta]
  exact (hC Y).trans (mul_le_mul_of_nonneg_right
    (le_max_left _ _) (Real.sqrt_nonneg _))

private theorem vonMangoldt_le_log_window {n Y : ℕ}
    (hn : n ≤ Y) (hY : 1 ≤ Y) : Λ n ≤ Real.log Y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [ArithmeticFunction.map_zero]
    exact Real.log_nonneg (by exact_mod_cast hY)
  · exact vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hn))

/-- Universal correlation form: if `f` is injective on the summation window
and both coordinates lie below `Y`, the terms with a proper-prime-power
coordinate have mass `O(√Y log Y)`. -/
theorem exists_properPrimePowerCorrelationBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y : ℕ) (f : ℕ → ℕ),
      Set.InjOn f ↑(Finset.Icc 1 X) →
      (∀ n ∈ Finset.Icc 1 X, n ≤ Y ∧ f n ≤ Y) →
      1 ≤ Y →
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n =>
          (IsPrimePow n ∧ ¬ n.Prime) ∨
            (IsPrimePow (f n) ∧ ¬ (f n).Prime)),
        Λ n * Λ (f n))
        ≤ C * Real.sqrt Y * Real.log Y := by
  obtain ⟨C₀, hC₀, hweight⟩ := properPrimePowerMangoldtWeight_le_sqrt
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro X Y f hf hfY hY
  classical
  let A := (Finset.Icc 1 X).filter fun n =>
    IsPrimePow n ∧ ¬ n.Prime
  let B := (Finset.Icc 1 X).filter fun n =>
    IsPrimePow (f n) ∧ ¬ (f n).Prime
  have hlog : 0 ≤ Real.log Y :=
    Real.log_nonneg (by exact_mod_cast hY)
  have hA_sub : A ⊆ properPrimePows Y := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnY := (hfY n hn'.1).1
    rw [properPrimePows, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(Finset.mem_Icc.mp hn'.1).1, hnY⟩, hn'.2⟩
  have hB_image_sub : B.image f ⊆ properPrimePows Y := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    have hn' := Finset.mem_filter.mp hn
    have hfnY := (hfY n hn'.1).2
    rw [properPrimePows, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn'.2.1.one_lt.le, hfnY⟩, hn'.2⟩
  have hsumA : (∑ n ∈ A, Λ n * Λ (f n))
      ≤ C₀ * Real.sqrt Y * Real.log Y := by
    calc
      (∑ n ∈ A, Λ n * Λ (f n))
          ≤ ∑ n ∈ A, Λ n * Real.log Y := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hnIcc := (Finset.mem_filter.mp hn).1
              exact mul_le_mul_of_nonneg_left
                (vonMangoldt_le_log_window (hfY n hnIcc).2 hY)
                vonMangoldt_nonneg
      _ = (∑ n ∈ A, Λ n) * Real.log Y := by
            rw [Finset.sum_mul]
      _ ≤ properPrimePowerMangoldtWeight Y * Real.log Y := by
            refine mul_le_mul_of_nonneg_right ?_ hlog
            rw [properPrimePowerMangoldtWeight]
            exact Finset.sum_le_sum_of_subset_of_nonneg hA_sub
              (fun n _ _ => vonMangoldt_nonneg)
      _ ≤ (C₀ * Real.sqrt Y) * Real.log Y := by
            exact mul_le_mul_of_nonneg_right (hweight Y) hlog
      _ = C₀ * Real.sqrt Y * Real.log Y := rfl
  have hfB : Set.InjOn f ↑B :=
    hf.mono (fun n hn => (Finset.mem_filter.mp hn).1)
  have hsumB : (∑ n ∈ B, Λ n * Λ (f n))
      ≤ C₀ * Real.sqrt Y * Real.log Y := by
    calc
      (∑ n ∈ B, Λ n * Λ (f n))
          ≤ ∑ n ∈ B, Real.log Y * Λ (f n) := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hnIcc := (Finset.mem_filter.mp hn).1
              exact mul_le_mul_of_nonneg_right
                (vonMangoldt_le_log_window (hfY n hnIcc).1 hY)
                vonMangoldt_nonneg
      _ = Real.log Y * ∑ n ∈ B, Λ (f n) := by
            rw [Finset.mul_sum]
      _ = Real.log Y * ∑ q ∈ B.image f, Λ q := by
            rw [Finset.sum_image]
            exact hfB
      _ ≤ Real.log Y * properPrimePowerMangoldtWeight Y := by
            refine mul_le_mul_of_nonneg_left ?_ hlog
            rw [properPrimePowerMangoldtWeight]
            exact Finset.sum_le_sum_of_subset_of_nonneg hB_image_sub
              (fun n _ _ => vonMangoldt_nonneg)
      _ ≤ Real.log Y * (C₀ * Real.sqrt Y) := by
            exact mul_le_mul_of_nonneg_left (hweight Y) hlog
      _ = C₀ * Real.sqrt Y * Real.log Y := by ring
  rw [Finset.filter_or]
  change (∑ n ∈ A ∪ B, Λ n * Λ (f n))
      ≤ 2 * C₀ * Real.sqrt Y * Real.log Y
  have hdecomp : A ∪ B = A ∪ (B \ A) := by ext n; simp
  have hdisj : Disjoint A (B \ A) := by
    rw [Finset.disjoint_left]
    intro n hnA hnBA
    exact (Finset.mem_sdiff.mp hnBA).2 hnA
  rw [hdecomp, Finset.sum_union hdisj]
  have hsdiff : (∑ n ∈ B \ A, Λ n * Λ (f n))
      ≤ ∑ n ∈ B, Λ n * Λ (f n) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun n _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
  nlinarith

/-- Shifted-correlation form of `lem:ar-prime-power`.  The constant is
universal, and therefore in particular may be regarded as depending on the
fixed shift `h`. -/
theorem exists_properPrimePower_shift_correlation_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h X : ℕ), 1 ≤ X →
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n =>
          (IsPrimePow n ∧ ¬ n.Prime) ∨
            (IsPrimePow (n + h) ∧ ¬ (n + h).Prime)),
        Λ n * Λ (n + h))
        ≤ C * Real.sqrt (X + h) * Real.log (X + h) := by
  obtain ⟨C, hC, hmaster⟩ := exists_properPrimePowerCorrelationBound
  refine ⟨C, hC, ?_⟩
  intro h X hX
  simpa only [Nat.cast_add] using hmaster X (X + h) (· + h)
    (fun a _ b _ hab => by simpa using hab)
    (fun n hn => by
      have hnX := (Finset.mem_Icc.mp hn).2
      omega)
    (by omega)

/-- Fixed-sum form of `lem:ar-prime-power`: among the positive solutions
`m + n = N`, the terms with a proper-prime-power coordinate contribute at
most `C √N log N`. -/
theorem exists_properPrimePower_fixed_sum_correlation_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ m ∈ (Finset.Icc 1 (N - 1)).filter (fun m =>
          (IsPrimePow m ∧ ¬ m.Prime) ∨
            (IsPrimePow (N - m) ∧ ¬ (N - m).Prime)),
        Λ m * Λ (N - m))
        ≤ C * Real.sqrt N * Real.log N := by
  obtain ⟨C, hC, hmaster⟩ := exists_properPrimePowerCorrelationBound
  refine ⟨C, hC, ?_⟩
  intro N hN
  exact hmaster (N - 1) N (N - ·)
    (fun a ha b hb hab => by
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      simp only at hab
      omega)
    (fun n hn => by
      have hn' := Finset.mem_Icc.mp hn
      omega)
    hN

end NCG
