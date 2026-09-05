/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.ArithParity
import NCG.Arithmetic.SignedSeparator

/-!
# Prime-power contamination and the Hardy–Littlewood route
  (`lem:prime-power`, `thm:HL-sufficient`,
  `thm:v003-four-additive-routes`, arithmetic monograph)

* `properPrimePows_card_le` — the proper prime powers in `[1, Y]`
  number at most `√Y·log₂Y` (base–exponent injection);
* `prime_power_contamination` — for any injective target map the
  von Mangoldt correlation mass carried by proper-prime-power
  coordinates is at most `4√Y(log Y)³` (the crude polylog form of
  the `O(√X log X)` display, sufficient for every downstream use);
* `HL_twin` / `HL_goldbach` — the classical sufficiency: a
  Hardy–Littlewood asymptotic with positive singular series and
  square-root-power error forces infinitely many twin primes,
  resp. binary Goldbach for all large even `N`;
* `four_additive_routes` — the assembled ledger (A1)–(A4): the
  signed closures (`twin_closure`, `goldbach_closure`), parity
  recovery (`parity_recovery`), and the Hardy–Littlewood route,
  plus the semiprime-bulk witness that positive degree-`≤2` mass
  alone forces no prime.
-/

namespace NCG

open Finset ArithmeticFunction

open scoped ArithmeticFunction

noncomputable section

/-! ## Proper prime powers -/

/-- The proper prime powers in the window `[1, Y]`. -/
def properPrimePows (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter fun n => IsPrimePow n ∧ ¬ n.Prime

/-- Base–exponent injection: at most `√Y · log₂ Y` proper prime
powers up to `Y`. -/
theorem properPrimePows_card_le (Y : ℕ) :
    (properPrimePows Y).card ≤ Nat.sqrt Y * Nat.log 2 Y := by
  classical
  have hmap : ∀ n ∈ properPrimePows Y,
      (n.minFac, n.factorization n.minFac)
        ∈ (Finset.Icc 2 (Nat.sqrt Y)) ×ˢ
            (Finset.Icc 2 (Nat.log 2 Y)) := by
    intro n hn
    rw [properPrimePows, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnY⟩, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hpN : p.Prime := hp.nat_prime
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · have hk1 : k = 1 := by omega
        subst hk1
        rw [pow_one] at hnp
        exact absurd hpN hnp
      · exact h
    have hminfac : (p ^ k).minFac = p :=
      hpN.pow_minFac (by omega)
    have hfact : (p ^ k).factorization p = k := by
      rw [hpN.factorization_pow, Finsupp.single_eq_same]
    have hpair : ((p ^ k).minFac,
        (p ^ k).factorization ((p ^ k).minFac)) = (p, k) := by
      rw [hminfac, hfact]
    rw [hpair, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨hpN.two_le, ?_⟩, hk2, ?_⟩
    · rw [Nat.le_sqrt]
      calc p * p = p ^ 2 := (sq p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hpN.pos hk2
      _ ≤ Y := hnY
    · refine Nat.le_log_of_pow_le one_lt_two ?_
      calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hpN.two_le k
      _ ≤ Y := hnY
  have hinj : Set.InjOn
      (fun n : ℕ => (Nat.minFac n, Nat.factorization n (Nat.minFac n)))
      ↑(properPrimePows Y) := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [properPrimePows, Finset.mem_filter] at ha hb
    obtain ⟨-, hppa, -⟩ := ha
    obtain ⟨-, hppb, -⟩ := hb
    obtain ⟨p, k, hp, hk, rfl⟩ := hppa
    obtain ⟨q, l, hq, hl, rfl⟩ := hppb
    have hpN : p.Prime := hp.nat_prime
    have hqN : q.Prime := hq.nat_prime
    have h1 : (p ^ k).minFac = p := hpN.pow_minFac (by omega)
    have h2 : (q ^ l).minFac = q := hqN.pow_minFac (by omega)
    have h3 : (p ^ k).factorization p = k := by
      rw [hpN.factorization_pow, Finsupp.single_eq_same]
    have h4 : (q ^ l).factorization q = l := by
      rw [hqN.factorization_pow, Finsupp.single_eq_same]
    simp only [Prod.mk.injEq, h1, h2] at hab
    obtain ⟨hpq, hkl⟩ := hab
    subst hpq
    rw [h3, h4] at hkl
    rw [hkl]
  calc (properPrimePows Y).card
      ≤ ((Finset.Icc 2 (Nat.sqrt Y)) ×ˢ
          (Finset.Icc 2 (Nat.log 2 Y))).card :=
        Finset.card_le_card_of_injOn _ hmap hinj
  _ ≤ Nat.sqrt Y * Nat.log 2 Y := by
      rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
      exact Nat.mul_le_mul (by omega) (by omega)

/-- Real form of the count: `#PP(Y) ≤ √Y · 2 log Y`. -/
theorem properPrimePows_card_le_real {Y : ℕ} (hY : 1 ≤ Y) :
    ((properPrimePows Y).card : ℝ)
      ≤ Real.sqrt Y * (2 * Real.log Y) := by
  have h1 : ((Nat.sqrt Y : ℝ)) ≤ Real.sqrt Y := by
    have hnat : Nat.sqrt Y ^ 2 ≤ Y := Nat.sqrt_le' Y
    have hreal : (Nat.sqrt Y : ℝ) ^ 2 ≤ (Y : ℝ) := by
      exact_mod_cast hnat
    rw [show ((Nat.sqrt Y : ℝ)) = Real.sqrt ((Nat.sqrt Y : ℝ) ^ 2) by
      rw [Real.sqrt_sq (Nat.cast_nonneg _)]]
    exact Real.sqrt_le_sqrt hreal
  have h2 : ((Nat.log 2 Y : ℝ)) ≤ 2 * Real.log Y := by
    have hpow : (2 : ℕ) ^ Nat.log 2 Y ≤ Y :=
      Nat.pow_log_le_self 2 (by omega)
    have hlog : (Nat.log 2 Y : ℝ) * Real.log 2 ≤ Real.log Y := by
      have hc : ((2 : ℕ) ^ Nat.log 2 Y : ℝ) ≤ (Y : ℝ) := by
        exact_mod_cast hpow
      have := Real.log_le_log
        (show (0 : ℝ) < ((2 : ℕ) ^ Nat.log 2 Y : ℝ) by positivity) hc
      rwa [show ((2 : ℕ) ^ Nat.log 2 Y : ℝ) = (2 : ℝ) ^ Nat.log 2 Y by
        push_cast; ring, Real.log_pow] at this
    nlinarith [Real.log_two_gt_d9,
      (by positivity : (0 : ℝ) ≤ (Nat.log 2 Y : ℝ))]
  calc ((properPrimePows Y).card : ℝ)
      ≤ (Nat.sqrt Y * Nat.log 2 Y : ℕ) := by
        exact_mod_cast properPrimePows_card_le Y
  _ = ((Nat.sqrt Y : ℝ)) * ((Nat.log 2 Y : ℝ)) := by push_cast; ring
  _ ≤ Real.sqrt Y * (2 * Real.log Y) := by
      refine mul_le_mul h1 h2 (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

/-! ## The contamination bound (`lem:prime-power`) -/

private lemma vonMangoldt_window_le {m Y : ℕ} (hm : m ≤ Y)
    (hY : 1 ≤ Y) : Λ m ≤ Real.log Y := by
  rcases Nat.eq_zero_or_pos m with h0 | h1
  · subst h0
    rw [ArithmeticFunction.map_zero]
    exact Real.log_nonneg (by exact_mod_cast hY)
  · refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast hm)

/-- `lem:prime-power` (master form): for an injective target map into
`[1, Y]`, the von Mangoldt correlation mass carried by
proper-prime-power coordinates is at most `4√Y(log Y)³` — the crude
polylog form of the `O(√X log X)` display, sufficient for every
downstream use. -/
theorem prime_power_contamination (X Y : ℕ) (f : ℕ → ℕ)
    (hf : Set.InjOn f ↑(Finset.Icc 1 X))
    (hfY : ∀ n ∈ Finset.Icc 1 X, n ≤ Y ∧ f n ≤ Y) (hY : 1 ≤ Y) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n =>
        (IsPrimePow n ∧ ¬ n.Prime)
          ∨ (IsPrimePow (f n) ∧ ¬ (f n).Prime)),
      Λ n * Λ (f n))
      ≤ 4 * Real.sqrt Y * Real.log Y ^ 3 := by
  classical
  set F := (Finset.Icc 1 X).filter fun n =>
    (IsPrimePow n ∧ ¬ n.Prime) ∨ (IsPrimePow (f n) ∧ ¬ (f n).Prime)
    with hF
  have hterm : ∀ n ∈ F, Λ n * Λ (f n) ≤ Real.log Y ^ 2 := by
    intro n hn
    have hnmem : n ∈ Finset.Icc 1 X := Finset.mem_of_mem_filter n hn
    obtain ⟨hnY, hfnY⟩ := hfY n hnmem
    calc Λ n * Λ (f n) ≤ Real.log Y * Real.log Y :=
          mul_le_mul (vonMangoldt_window_le hnY hY)
            (vonMangoldt_window_le hfnY hY)
            ArithmeticFunction.vonMangoldt_nonneg
            (Real.log_nonneg (by exact_mod_cast hY))
    _ = Real.log Y ^ 2 := (sq (Real.log Y)).symm
  have hc1 : ((Finset.Icc 1 X).filter fun n =>
      IsPrimePow n ∧ ¬ n.Prime).card ≤ (properPrimePows Y).card := by
    refine Finset.card_le_card fun n hn => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1n, hnX⟩, hprop⟩ := hn
    have hnY := (hfY n (Finset.mem_Icc.mpr ⟨h1n, hnX⟩)).1
    rw [properPrimePows, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨h1n, hnY⟩, hprop⟩
  have hc2 : ((Finset.Icc 1 X).filter fun n =>
      IsPrimePow (f n) ∧ ¬ (f n).Prime).card
      ≤ (properPrimePows Y).card := by
    refine Finset.card_le_card_of_injOn f (fun n hn => ?_) ?_
    · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1n, hnX⟩, hpp, hnp⟩ := hn
      have hfnY := (hfY n (Finset.mem_Icc.mpr ⟨h1n, hnX⟩)).2
      rw [Finset.mem_coe, properPrimePows, Finset.mem_filter,
        Finset.mem_Icc]
      have h2f : 2 ≤ f n := hpp.two_le
      exact ⟨⟨by omega, hfnY⟩, hpp, hnp⟩
    · exact hf.mono (by
        intro n hn
        rw [Finset.mem_coe, Finset.mem_filter] at hn
        exact Finset.mem_coe.mpr hn.1)
  have hcard : (F.card : ℝ)
      ≤ 2 * (Real.sqrt Y * (2 * Real.log Y)) := by
    have hsub : F ⊆ ((Finset.Icc 1 X).filter fun n =>
        IsPrimePow n ∧ ¬ n.Prime)
        ∪ ((Finset.Icc 1 X).filter fun n =>
            IsPrimePow (f n) ∧ ¬ (f n).Prime) := by
      intro n hn
      rw [hF, Finset.mem_filter] at hn
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      tauto
    have hnat : F.card ≤ 2 * (properPrimePows Y).card := by
      calc F.card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ 2 * (properPrimePows Y).card := by omega
    calc (F.card : ℝ) ≤ 2 * ((properPrimePows Y).card : ℝ) := by
          exact_mod_cast hnat
    _ ≤ 2 * (Real.sqrt Y * (2 * Real.log Y)) := by
        have := properPrimePows_card_le_real hY
        linarith
  calc (∑ n ∈ F, Λ n * Λ (f n))
      ≤ F.card • Real.log Y ^ 2 :=
        Finset.sum_le_card_nsmul F _ _ hterm
  _ = (F.card : ℝ) * Real.log Y ^ 2 := by rw [nsmul_eq_mul]
  _ ≤ 2 * (Real.sqrt Y * (2 * Real.log Y)) * Real.log Y ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
  _ = 4 * Real.sqrt Y * Real.log Y ^ 3 := by ring

/-! ## The Hardy–Littlewood sufficiency (`thm:HL-sufficient`) -/

private lemma eventually_dominates {S C B : ℝ} (hS : 0 < S) {δ : ℝ}
    (_hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2) :
    ∀ᶠ X : ℕ in Filter.atTop,
      C * (X : ℝ) ^ ((1 : ℝ) / 2 + δ) + B
        + 4 * Real.sqrt ((X : ℝ) + 2) * Real.log ((X : ℝ) + 2) ^ 3
      < S * X := by
  have hcore : Filter.Tendsto
      (fun u : ℝ => Real.log u ^ 3 / Real.sqrt u)
      Filter.atTop (nhds 0) := by
    have hlo := (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 6)).pow (n := 3) (by norm_num)
    have hlo2 : (fun x : ℝ => Real.log x ^ 3) =o[Filter.atTop]
        fun x : ℝ => Real.sqrt x := by
      refine hlo.congr' (Filter.Eventually.of_forall fun x => rfl) ?_
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 6)) 3,
        ← Real.rpow_mul hx]
      norm_num
    exact hlo2.tendsto_div_nhds_zero
  have h1 : Filter.Tendsto
      (fun x : ℝ => C * x ^ ((1 : ℝ) / 2 + δ) / x)
      Filter.atTop (nhds 0) := by
    have hexp : Filter.Tendsto
        (fun x : ℝ => x ^ ((1 : ℝ) / 2 + δ - 1))
        Filter.atTop (nhds 0) := by
      have h := tendsto_rpow_neg_atTop
        (y := 1 - ((1 : ℝ) / 2 + δ)) (by linarith)
      refine h.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      congr 1
      ring
    have h2 := hexp.const_mul C
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    rw [mul_div_assoc]
    congr 1
    rw [show x ^ ((1 : ℝ) / 2 + δ) / x
        = x ^ ((1 : ℝ) / 2 + δ) / x ^ ((1 : ℝ)) by
      rw [Real.rpow_one], ← Real.rpow_sub hx]
  have h2 : Filter.Tendsto (fun x : ℝ => B / x) Filter.atTop
      (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have h3 : Filter.Tendsto
      (fun x : ℝ => 4 * Real.sqrt (x + 2) * Real.log (x + 2) ^ 3 / x)
      Filter.atTop (nhds 0) := by
    have hcomp : Filter.Tendsto
        (fun x : ℝ => 8 * (Real.log (x + 2) ^ 3 / Real.sqrt (x + 2)))
        Filter.atTop (nhds 0) := by
      have h := (hcore.comp
        (Filter.tendsto_atTop_add_const_right _ 2
          Filter.tendsto_id)).const_mul (8 : ℝ)
      rwa [mul_zero] at h
    refine squeeze_zero' ?_ ?_ hcomp
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
      have hlog : (0 : ℝ) ≤ Real.log (x + 2) :=
        Real.log_nonneg (by linarith)
      positivity
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
      have hx2 : (0 : ℝ) < x + 2 := by linarith
      have hsq : Real.sqrt (x + 2) * Real.sqrt (x + 2) = x + 2 :=
        Real.mul_self_sqrt hx2.le
      have hsqpos : 0 < Real.sqrt (x + 2) := Real.sqrt_pos.mpr hx2
      have hlog : 0 ≤ Real.log (x + 2) ^ 3 := by
        have : (0 : ℝ) ≤ Real.log (x + 2) :=
          Real.log_nonneg (by linarith)
        positivity
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < x),
        show (8 : ℝ) * (Real.log (x + 2) ^ 3 / Real.sqrt (x + 2)) * x
          = 8 * Real.log (x + 2) ^ 3 * x / Real.sqrt (x + 2) by ring,
        le_div_iff₀ hsqpos]
      nlinarith [hsq, hsqpos, hlog]
  have hsum : Filter.Tendsto
      (fun x : ℝ => (C * x ^ ((1 : ℝ) / 2 + δ) + B
        + 4 * Real.sqrt (x + 2) * Real.log (x + 2) ^ 3) / x)
      Filter.atTop (nhds 0) := by
    have h := (h1.add h2).add h3
    rw [add_zero, add_zero] at h
    refine h.congr ?_
    intro x
    ring
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      (C * x ^ ((1 : ℝ) / 2 + δ) + B
        + 4 * Real.sqrt (x + 2) * Real.log (x + 2) ^ 3) / x < S :=
    hsum.eventually_lt_const hS
  have hreal : ∀ᶠ x : ℝ in Filter.atTop,
      C * x ^ ((1 : ℝ) / 2 + δ) + B
        + 4 * Real.sqrt (x + 2) * Real.log (x + 2) ^ 3 < S * x := by
    filter_upwards [hev, Filter.eventually_gt_atTop (0 : ℝ)]
      with x hx hxpos
    calc C * x ^ ((1 : ℝ) / 2 + δ) + B
        + 4 * Real.sqrt (x + 2) * Real.log (x + 2) ^ 3
        = (C * x ^ ((1 : ℝ) / 2 + δ) + B
          + 4 * Real.sqrt (x + 2) * Real.log (x + 2) ^ 3) / x * x := by
          field_simp
    _ < S * x := by
        exact mul_lt_mul_of_pos_right hx hxpos
  exact tendsto_natCast_atTop_atTop.eventually hreal

/-- `thm:HL-sufficient` (twin half): a Hardy–Littlewood asymptotic
with positive singular series and square-root-power error forces
infinitely many twin primes. -/
theorem HL_twin {S₂ C δ : ℝ} {X₀ : ℕ} (hS : 0 < S₂) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1 / 2)
    (hasym : ∀ X : ℕ, X₀ ≤ X →
      |(∑ n ∈ Finset.Icc 1 X, Λ n * Λ (n + 2)) - S₂ * X|
        ≤ C * (X : ℝ) ^ ((1 : ℝ) / 2 + δ)) :
    {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite := by
  classical
  by_contra hfin
  rw [Set.not_infinite] at hfin
  set B : ℝ := ∑ p ∈ hfin.toFinset, Λ p * Λ (p + 2) with hB
  have hsplit : ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, Λ n * Λ (n + 2))
      ≤ B + 4 * Real.sqrt ((X : ℝ) + 2)
          * Real.log ((X : ℝ) + 2) ^ 3 := by
    intro X
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 X)
      (fun n => n.Prime ∧ (n + 2).Prime)]
    have hA : (∑ n ∈ (Finset.Icc 1 X).filter
        (fun n => n.Prime ∧ (n + 2).Prime), Λ n * Λ (n + 2)) ≤ B := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun n _ _ => mul_nonneg
          ArithmeticFunction.vonMangoldt_nonneg
          ArithmeticFunction.vonMangoldt_nonneg)
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [Set.Finite.mem_toFinset]
      exact hn.2
    have hBpart : (∑ n ∈ (Finset.Icc 1 X).filter
        (fun n => ¬ (n.Prime ∧ (n + 2).Prime)), Λ n * Λ (n + 2))
        ≤ 4 * Real.sqrt ((X : ℝ) + 2)
          * Real.log ((X : ℝ) + 2) ^ 3 := by
      have hsubsum : (∑ n ∈ (Finset.Icc 1 X).filter
          (fun n => ¬ (n.Prime ∧ (n + 2).Prime)), Λ n * Λ (n + 2))
          ≤ ∑ n ∈ (Finset.Icc 1 X).filter (fun n =>
              (IsPrimePow n ∧ ¬ n.Prime)
                ∨ (IsPrimePow (n + 2) ∧ ¬ (n + 2).Prime)),
            Λ n * Λ (n + 2) := by
        rw [← Finset.sum_filter_ne_zero ((Finset.Icc 1 X).filter
          (fun n => ¬ (n.Prime ∧ (n + 2).Prime)))]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun n _ _ => mul_nonneg
            ArithmeticFunction.vonMangoldt_nonneg
            ArithmeticFunction.vonMangoldt_nonneg)
        intro n hn
        rw [Finset.mem_filter, Finset.mem_filter] at hn
        obtain ⟨⟨hnmem, hnotP⟩, hne⟩ := hn
        rw [Finset.mem_filter]
        refine ⟨hnmem, ?_⟩
        have hn1 : Λ n ≠ 0 := fun h => hne (by rw [h, zero_mul])
        have hn2 : Λ (n + 2) ≠ 0 := fun h => hne (by rw [h, mul_zero])
        rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hn1 hn2
        rcases Classical.em n.Prime with hp | hp
        · rcases Classical.em (n + 2).Prime with hq | hq
          · exact absurd ⟨hp, hq⟩ hnotP
          · exact Or.inr ⟨hn2, hq⟩
        · exact Or.inl ⟨hn1, hp⟩
      have hbound := prime_power_contamination X (X + 2) (· + 2)
        (fun a _ b _ h => by simp only [] at h; omega)
        (fun n hn => by
          rw [Finset.mem_Icc] at hn
          omega)
        (by omega)
      push_cast at hbound
      exact hsubsum.trans hbound
    linarith
  -- eventual contradiction
  have hev := eventually_dominates (S := S₂) (C := C) (B := B)
    hS hδ0 hδ
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  set X := max X₀ X₁ with hX
  have hup := hasym X (le_max_left _ _)
  have hdom := hX₁ X (le_max_right _ _)
  have hlow : S₂ * X - C * (X : ℝ) ^ ((1 : ℝ) / 2 + δ)
      ≤ ∑ n ∈ Finset.Icc 1 X, Λ n * Λ (n + 2) := by
    have := abs_le.mp hup
    linarith [this.1]
  linarith [hsplit X]

/-- `thm:HL-sufficient` (Goldbach half): a Hardy–Littlewood
asymptotic with uniformly positive singular series forces binary
Goldbach for all sufficiently large (even) `N`. -/
theorem HL_goldbach {Sinf C δ : ℝ} {N₀ : ℕ} (hS : 0 < Sinf)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hasym : ∀ N : ℕ, N₀ ≤ N → Even N →
      Sinf * N - C * (N : ℝ) ^ ((1 : ℝ) / 2 + δ)
        ≤ ∑ n ∈ Finset.Icc 1 N, Λ n * Λ (N - n)) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  classical
  have hev := eventually_dominates (S := Sinf) (C := C) (B := 0)
    hS hδ0 hδ
  filter_upwards [hev, Filter.eventually_ge_atTop N₀,
    Filter.eventually_ge_atTop 4] with N hdom hN₀ hN4 heven
  by_contra hno
  push Not at hno
  -- with no prime pair, every nonzero term has a proper-power
  -- coordinate
  have hsubsum : (∑ n ∈ Finset.Icc 1 N, Λ n * Λ (N - n))
      ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n =>
          (IsPrimePow n ∧ ¬ n.Prime)
            ∨ (IsPrimePow (N - n) ∧ ¬ (N - n).Prime)),
        Λ n * Λ (N - n) := by
    rw [← Finset.sum_filter_ne_zero (Finset.Icc 1 N)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun n _ _ => mul_nonneg
        ArithmeticFunction.vonMangoldt_nonneg
        ArithmeticFunction.vonMangoldt_nonneg)
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnmem, hne⟩ := hn
    rw [Finset.mem_filter]
    refine ⟨hnmem, ?_⟩
    have hn1 : Λ n ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hn2 : Λ (N - n) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hn1 hn2
    rcases Classical.em n.Prime with hp | hp
    · rcases Classical.em (N - n).Prime with hq | hq
      · exfalso
        rw [Finset.mem_Icc] at hnmem
        exact hno n (N - n) hp hq (by omega)
      · exact Or.inr ⟨hn2, hq⟩
    · exact Or.inl ⟨hn1, hp⟩
  have hbound := prime_power_contamination N (N + 2) (N - ·)
    (fun a ha b hb h => by
      rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
      simp only [] at h
      omega)
    (fun n hn => by
      rw [Finset.mem_Icc] at hn
      omega)
    (by omega)
  have hcontra := hasym N hN₀ heven
  have hchain : Sinf * N - C * (N : ℝ) ^ ((1 : ℝ) / 2 + δ)
      ≤ 4 * Real.sqrt ((N : ℝ) + 2) * Real.log ((N : ℝ) + 2) ^ 3 := by
    push_cast at hbound
    exact hcontra.trans (hsubsum.trans hbound)
  simp only [add_zero] at hdom
  linarith

/-! ## The four additive routes (`thm:v003-four-additive-routes`) -/

/-- `thm:v003-four-additive-routes`: (A1)–(A3) are the signed
closures and parity recovery, (A4) is the Hardy–Littlewood route
(`HL_twin`, `HL_goldbach`), and positive degree-`≤2` mass alone
forces no prime — the semiprime bulk can carry it all. -/
theorem four_additive_routes :
    (∀ {S : Finset ℕ}, (∀ p ∈ S, p.Prime) → ∀ J : ℕ → ℝ,
      (∀ p ∈ S, J (p + 2) ≤ if (p + 2).Prime then 1 else 0) →
      0 < ∑ p ∈ S, Real.log p * J (p + 2) →
      ∃ p ∈ S, p.Prime ∧ (p + 2).Prime)
    ∧ (∀ (N : ℕ) {S : Finset ℕ}, (∀ p ∈ S, p.Prime) →
      (∀ p ∈ S, p ≤ N) → ∀ J : ℕ → ℝ,
      (∀ p ∈ S, J (N - p) ≤ if (N - p).Prime then 1 else 0) →
      0 < ∑ p ∈ S, Real.log p * J (N - p) →
      ∃ p ∈ S, p.Prime ∧ (N - p).Prime ∧ p + (N - p) = N)
    ∧ (∀ P1 P2 M J delta : ℝ, M = P1 + P2 → J = -P1 + P2 →
      J ≤ (1 - 2 * delta) * M → delta * M ≤ P1)
    ∧ (∃ n : ℕ, ¬ n.Prime ∧ 0 < packetPle2 1 n) := by
  refine ⟨fun {S} hS J hm hp => twin_closure hS J hm hp,
    fun N {S} hS hSN J hm hp => goldbach_closure N hS hSN J hm hp,
    fun P1 P2 M J delta h1 h2 h3 =>
      (parity_recovery P1 P2 M J delta h1 h2).2.2 h3,
    ⟨6, by norm_num, ?_⟩⟩
  rw [show (6 : ℕ) = 2 * 3 by norm_num,
    packet_semiprime Nat.prime_two Nat.prime_three (by norm_num)]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  positivity

end

end NCG
