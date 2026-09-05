/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.GoldbachHeat

/-!
# Sharp proper-prime-power contamination for the Goldbach heat selector

This file sharpens the proper-prime-power count used by
`NCG.goldbach_heat_contamination`.  A proper prime power `p^k`, with `k ≥ 2`,
is encoded by

`(k mod 2, p^(k / 2))`.

The second coordinate is at most `√N`.  The encoding is injective: its prime
base and half-exponent are recovered from the second coordinate, while the
first coordinate recovers the parity of the exponent.  Consequently there
are at most `2(⌊√N⌋+1)` proper prime powers below `N`, with no logarithmic
loss.  Combined with the endpoint-packing estimate from `GoldbachHeat`, this
gives the manuscript's `O(N⁻¹/⁴ (log N)²)` contamination scale.
-/

open Finset ArithmeticFunction

namespace NCG

/-- The parity/half-power code for a natural number's prime-power data. -/
private def properPrimePowerCode (m : ℕ) : Fin 2 × ℕ :=
  let k := m.factorization m.minFac
  (⟨k % 2, Nat.mod_lt _ (by omega)⟩, m.minFac ^ (k / 2))

/-- Sharp count of proper prime powers in `(0,N)`: the parity/half-power
encoding places them in two copies of `{0, …, ⌊√N⌋}`. -/
theorem proper_prime_pow_card_le_two_sqrt (N : ℕ) :
    ((Finset.Ioo 0 N).filter
      (fun m => IsPrimePow m ∧ ¬ m.Prime)).card
      ≤ 2 * (Nat.sqrt N + 1) := by
  classical
  let source := (Finset.Ioo 0 N).filter
    (fun m => IsPrimePow m ∧ ¬ m.Prime)
  let target := (Finset.univ : Finset (Fin 2)) ×ˢ
    Finset.Icc 0 (Nat.sqrt N)
  refine le_trans (Finset.card_le_card_of_injOn
    (t := target) properPrimePowerCode ?_ ?_) ?_
  · intro m hm
    have hmem := Finset.mem_filter.mp hm
    have hmIoo := Finset.mem_Ioo.mp hmem.1
    have hpp : IsPrimePow m := hmem.2.1
    have hnp : ¬ m.Prime := hmem.2.2
    have hm1 : m ≠ 1 := hpp.one_lt.ne'
    have hp : m.minFac.Prime := Nat.minFac_prime hm1
    let k := m.factorization m.minFac
    have hpk : m.minFac ^ k = m :=
      hpp.minFac_pow_factorization_eq
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hk | hk
      · have hcase : k = 0 ∨ k = 1 := by omega
        rcases hcase with h | h
        · rw [h, pow_zero] at hpk
          exact absurd hpk.symm hm1
        · rw [h, pow_one] at hpk
          exact absurd (hpk ▸ hp) hnp
      · exact hk
    dsimp [target]
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    constructor
    · simp [properPrimePowerCode]
    · rw [Finset.mem_Icc]
      refine ⟨Nat.zero_le _, Nat.le_sqrt.mpr ?_⟩
      calc
        (m.minFac ^ (k / 2)) * (m.minFac ^ (k / 2))
            = m.minFac ^ (2 * (k / 2)) := by rw [← pow_add]; congr; omega
        _ ≤ m.minFac ^ k :=
          Nat.pow_le_pow_right hp.one_lt.le (by omega)
        _ = m := hpk
        _ ≤ N := hmIoo.2.le
  · intro m₁ hm₁ m₂ hm₂ heq
    have hmem₁ := Finset.mem_filter.mp hm₁
    have hmem₂ := Finset.mem_filter.mp hm₂
    have hpp₁ : IsPrimePow m₁ := hmem₁.2.1
    have hpp₂ : IsPrimePow m₂ := hmem₂.2.1
    have hm₁1 : m₁ ≠ 1 := hpp₁.one_lt.ne'
    have hm₂1 : m₂ ≠ 1 := hpp₂.one_lt.ne'
    have hp₁ : m₁.minFac.Prime := Nat.minFac_prime hm₁1
    have hp₂ : m₂.minFac.Prime := Nat.minFac_prime hm₂1
    let k₁ := m₁.factorization m₁.minFac
    let k₂ := m₂.factorization m₂.minFac
    have hk₁2 : 2 ≤ k₁ := by
      have hpk := hpp₁.minFac_pow_factorization_eq
      change m₁.minFac ^ k₁ = m₁ at hpk
      rcases Nat.lt_or_ge k₁ 2 with hk | hk
      · have hcase : k₁ = 0 ∨ k₁ = 1 := by omega
        rcases hcase with h | h
        · rw [h, pow_zero] at hpk
          exact absurd hpk.symm hm₁1
        · rw [h, pow_one] at hpk
          exact absurd (hpk ▸ hp₁) hmem₁.2.2
      · exact hk
    have hk₂2 : 2 ≤ k₂ := by
      have hpk := hpp₂.minFac_pow_factorization_eq
      change m₂.minFac ^ k₂ = m₂ at hpk
      rcases Nat.lt_or_ge k₂ 2 with hk | hk
      · have hcase : k₂ = 0 ∨ k₂ = 1 := by omega
        rcases hcase with h | h
        · rw [h, pow_zero] at hpk
          exact absurd hpk.symm hm₂1
        · rw [h, pow_one] at hpk
          exact absurd (hpk ▸ hp₂) hmem₂.2.2
      · exact hk
    change
      ((⟨k₁ % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2),
          m₁.minFac ^ (k₁ / 2)) =
        ((⟨k₂ % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2),
          m₂.minFac ^ (k₂ / 2)) at heq
    have hcoords :
        (⟨k₁ % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) =
            ⟨k₂ % 2, Nat.mod_lt _ (by omega)⟩ ∧
          m₁.minFac ^ (k₁ / 2) = m₂.minFac ^ (k₂ / 2) := by
      simpa only [Prod.mk.injEq] using heq
    have hhalf₁ : 0 < k₁ / 2 := by omega
    have hhalf₂ : 0 < k₂ / 2 := by omega
    have hbase : m₁.minFac = m₂.minFac := by
      have := congrArg Nat.minFac hcoords.2
      simpa [hp₁.pow_minFac hhalf₁.ne',
        hp₂.pow_minFac hhalf₂.ne'] using this
    have hhalf : k₁ / 2 = k₂ / 2 := by
      rw [hbase] at hcoords
      exact Nat.pow_right_injective hp₂.two_le hcoords.2
    have hparity : k₁ % 2 = k₂ % 2 := by
      exact congrArg Fin.val hcoords.1
    have hk : k₁ = k₂ := by omega
    rw [← hpp₁.minFac_pow_factorization_eq,
      ← hpp₂.minFac_pow_factorization_eq]
    exact congrArg₂ (· ^ ·) hbase hk
  · dsimp [target]
    simp [Nat.card_Icc]

/-- Sharp count of pairs contaminated in either summand. -/
theorem goldbachBad_card_le_four_sqrt (N : ℕ) :
    (goldbachBad N).card ≤ 4 * (Nat.sqrt N + 1) := by
  classical
  rw [goldbachBad, Finset.filter_or]
  refine le_trans (Finset.card_union_le _ _) ?_
  have hA := proper_prime_pow_card_le_two_sqrt N
  have hB : ((Finset.Ioo 0 N).filter
      (fun m => IsPrimePow (N - m) ∧ ¬ (N - m).Prime)).card
      ≤ 2 * (Nat.sqrt N + 1) := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun m => N - m) ?_ ?_) hA
    · intro m hm
      have h2 := Finset.mem_filter.mp hm
      have hmIoo := Finset.mem_Ioo.mp h2.1
      refine Finset.mem_filter.mpr ⟨?_, h2.2⟩
      simp only [Finset.mem_Ioo]
      have h3 := h2.2.1.one_lt
      omega
    · intro a ha b hb hab
      have haIoo := Finset.mem_Ioo.mp
        (Finset.mem_filter.mp ha).1
      have hbIoo := Finset.mem_Ioo.mp
        (Finset.mem_filter.mp hb).1
      simp only at hab
      omega
  omega

/-- The contaminated heat sum, bounded using the sharp prime-power count. -/
theorem goldbach_heat_contamination_sharp_count (N : ℕ) (t : ℝ)
    (ht : 0 ≤ t) :
    ∑ m ∈ goldbachBad N,
      Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        * Real.exp (-t * (Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2))
      ≤ Real.log N ^ 2
        * (6 * Real.sqrt (4 * (Nat.sqrt N + 1)) / Real.sqrt N) := by
  classical
  have hsub : goldbachBad N ⊆ Finset.Ioo 0 N :=
    Finset.filter_subset _ _
  have hterm : ∀ m ∈ goldbachBad N,
      Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        * Real.exp (-t * (Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2))
      ≤ Real.log N ^ 2
        * (1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))) := by
    intro m hm
    have hmIoo := Finset.mem_Ioo.mp (hsub hm)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmIoo.1
    have hmN : (m : ℝ) < N := by exact_mod_cast hmIoo.2
    have hNm1 : (1 : ℝ) ≤ (N : ℝ) - m := by
      have h1 : (m : ℝ) + 1 ≤ N := by exact_mod_cast hmIoo.2
      linarith
    have hsqrt : (0 : ℝ)
        < Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) :=
      Real.sqrt_pos.mpr (by nlinarith)
    have hcast : ((N - m : ℕ) : ℝ) = (N : ℝ) - m := by
      exact_mod_cast Nat.cast_sub hmIoo.2.le
    have hΛ1 : Λ m ≤ Real.log N := by
      refine le_trans vonMangoldt_le_log ?_
      refine Real.log_le_log (by linarith) ?_
      linarith
    have hΛ2 : Λ (N - m) ≤ Real.log N := by
      refine le_trans vonMangoldt_le_log ?_
      rw [hcast]
      refine Real.log_le_log (by linarith) ?_
      linarith
    have hexp : Real.exp (-t * (Real.log m ^ 2
        + Real.log ((N : ℝ) - m) ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h2 : (0 : ℝ) ≤ Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2 := by positivity
      nlinarith
    have hΛ1n : (0 : ℝ) ≤ Λ m := vonMangoldt_nonneg
    have hΛ2n : (0 : ℝ) ≤ Λ (N - m) := vonMangoldt_nonneg
    calc
      Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
          * Real.exp (-t * (Real.log m ^ 2
            + Real.log ((N : ℝ) - m) ^ 2))
          ≤ Λ m * Λ (N - m)
            / Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) * 1 := by
              refine mul_le_mul_of_nonneg_left hexp ?_
              positivity
      _ = Λ m * Λ (N - m)
            / Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) := mul_one _
      _ ≤ Real.log N * Real.log N
            / Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) := by
              gcongr
      _ = Real.log N ^ 2
            * (1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))) := by
              rw [pow_two]
              ring
  calc
    ∑ m ∈ goldbachBad N,
        Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
          * Real.exp (-t * (Real.log m ^ 2
            + Real.log ((N : ℝ) - m) ^ 2))
        ≤ ∑ m ∈ goldbachBad N, Real.log N ^ 2
            * (1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))) :=
          Finset.sum_le_sum hterm
    _ = Real.log N ^ 2 * ∑ m ∈ goldbachBad N,
          1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) := by
          rw [Finset.mul_sum]
    _ ≤ Real.log N ^ 2
          * (6 * Real.sqrt (goldbachBad N).card / Real.sqrt N) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_inv_sqrt_pair_le N _ hsub
    _ ≤ Real.log N ^ 2
          * (6 * Real.sqrt (4 * (Nat.sqrt N + 1)) / Real.sqrt N) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hcard : ((goldbachBad N).card : ℝ)
              ≤ 4 * ((Nat.sqrt N : ℝ) + 1) := by
            exact_mod_cast goldbachBad_card_le_four_sqrt N
          gcongr

/-- Exact manuscript-scale contamination estimate.  Its denominator is
`√(√N) = N^(1/4)`, so the right side is
`18 · N⁻¹/⁴ · (log N)²`, uniformly for every `t ≥ 0`. -/
theorem goldbach_heat_contamination_quarter_power (N : ℕ) (t : ℝ)
    (hN : 0 < N) (ht : 0 ≤ t) :
    ∑ m ∈ goldbachBad N,
      Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        * Real.exp (-t * (Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2))
      ≤ Real.log N ^ 2 * (18 / Real.sqrt (Real.sqrt N)) := by
  refine (goldbach_heat_contamination_sharp_count N t ht).trans ?_
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsNpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hssNpos : (0 : ℝ) < Real.sqrt (Real.sqrt N) :=
    Real.sqrt_pos.mpr hsNpos
  have hsNat : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := by
    have hsqNat : ((Nat.sqrt N : ℝ)) ^ 2 ≤ (N : ℝ) := by
      have hs := Nat.sqrt_le N
      have hs' : (Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hs
      simpa only [pow_two] using hs'
    have hsquare := Real.sq_sqrt hNr.le
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hone : (1 : ℝ) ≤ Real.sqrt N := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.sq_sqrt hNr.le, Real.sqrt_nonneg (N : ℝ)]
  have hinside : (4 : ℝ) * ((Nat.sqrt N : ℝ) + 1)
      ≤ 8 * Real.sqrt N := by nlinarith
  have hsqrtInside : Real.sqrt (4 * ((Nat.sqrt N : ℝ) + 1))
      ≤ 3 * Real.sqrt (Real.sqrt N) := by
    have hleft := Real.sqrt_le_sqrt hinside
    have hright : Real.sqrt (8 * Real.sqrt N)
        ≤ 3 * Real.sqrt (Real.sqrt N) := by
      have hsquared := Real.sq_sqrt (Real.sqrt_nonneg (N : ℝ))
      have hnonneg := Real.sqrt_nonneg (Real.sqrt N)
      have h8nonneg : (0 : ℝ) ≤ 8 * Real.sqrt N := by positivity
      have hroot8 := Real.sq_sqrt h8nonneg
      nlinarith [Real.sqrt_nonneg (8 * Real.sqrt N)]
    exact hleft.trans hright
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hNr) hssNpos).2
  calc
    6 * Real.sqrt (4 * ((Nat.sqrt N : ℝ) + 1))
          * Real.sqrt (Real.sqrt N)
        ≤ 6 * (3 * Real.sqrt (Real.sqrt N))
          * Real.sqrt (Real.sqrt N) := by
            gcongr
    _ = 18 * (Real.sqrt (Real.sqrt N) ^ 2) := by ring
    _ = 18 * Real.sqrt N := by
      rw [Real.sq_sqrt (Real.sqrt_nonneg _)]

/-- A heat value above the sharp quarter-power contamination envelope forces
a representation by two primes. -/
theorem goldbach_heat_sufficiency_quarter_power (N : ℕ) (t c : ℝ)
    (hN : 0 < N) (ht : 0 ≤ t)
    (hc : Real.log N ^ 2 * (18 / Real.sqrt (Real.sqrt N)) < c)
    (hheat : c ≤ goldbachHeat N t) :
    ∃ m, 0 < m ∧ m < N ∧ m.Prime ∧ (N - m).Prime := by
  classical
  by_contra hno
  have hno' : ∀ m, 0 < m → m < N →
      ¬ (m.Prime ∧ (N - m).Prime) := by
    intro m h1 h2 h3
    exact hno ⟨m, h1, h2, h3.1, h3.2⟩
  have hzero : ∀ m ∈ Finset.Ioo 0 N, m ∉ goldbachBad N →
      Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        * Real.exp (-t * (Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2)) = 0 := by
    intro m hm hbad
    have hmIoo := Finset.mem_Ioo.mp hm
    have hnb : ¬ ((IsPrimePow m ∧ ¬ m.Prime)
        ∨ (IsPrimePow (N - m) ∧ ¬ (N - m).Prime)) := by
      intro h
      exact hbad (Finset.mem_filter.mpr ⟨hm, h⟩)
    by_cases hΛ1 : Λ m = 0
    · rw [hΛ1]
      simp
    by_cases hΛ2 : Λ (N - m) = 0
    · rw [hΛ2]
      simp
    have hpp1 : IsPrimePow m := vonMangoldt_ne_zero_iff.mp hΛ1
    have hpp2 : IsPrimePow (N - m) :=
      vonMangoldt_ne_zero_iff.mp hΛ2
    have hp1 : m.Prime := by
      by_contra hnp
      exact hnb (Or.inl ⟨hpp1, hnp⟩)
    have hp2 : (N - m).Prime := by
      by_contra hnp
      exact hnb (Or.inr ⟨hpp2, hnp⟩)
    exact absurd ⟨hp1, hp2⟩ (hno' m hmIoo.1 hmIoo.2)
  have hsum : goldbachHeat N t
      = ∑ m ∈ goldbachBad N,
          Λ m * Λ (N - m)
            / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
            * Real.exp (-t * (Real.log m ^ 2
              + Real.log ((N : ℝ) - m) ^ 2)) :=
    (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
  have hcontam := goldbach_heat_contamination_quarter_power N t hN ht
  rw [hsum] at hheat
  linarith

/-- The explicit quarter-power contamination envelope tends to zero. -/
theorem goldbach_quarter_power_envelope_tendsto_zero :
    Filter.Tendsto
      (fun N : ℕ => Real.log N ^ 2 *
        (18 / Real.sqrt (Real.sqrt N)))
      Filter.atTop (nhds 0) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < (1 / 4 : ℝ))).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hscaled := hnat.const_mul (18 : ℝ)
  simpa only [mul_zero] using hscaled.congr' (by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hNr : (0 : ℝ) ≤ N := by positivity
    have hlog : (0 : ℝ) ≤ Real.log N :=
      Real.log_nonneg (by exact_mod_cast hN)
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hNr]
    norm_num [Real.rpow_natCast, hlog]
    ring)

/-- `thm:Goldbach-heat`: if a positive lower bound for the heat selector holds
for all sufficiently large even integers (at arbitrary positive times), then
all sufficiently large even integers are sums of two primes. -/
theorem goldbach_heat_eventually_two_primes
    (time : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (htime : ∀ᶠ N in Filter.atTop, 0 < time N)
    (hheat : ∀ᶠ N in Filter.atTop,
      Even N → c ≤ goldbachHeat N (time N)) :
    ∀ᶠ N in Filter.atTop,
      Even N → ∃ m, 0 < m ∧ m < N ∧ m.Prime ∧ (N - m).Prime := by
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop,
      Real.log N ^ 2 * (18 / Real.sqrt (Real.sqrt N)) < c :=
    goldbach_quarter_power_envelope_tendsto_zero.eventually
      (Iio_mem_nhds hc)
  filter_upwards [htime, hheat, hsmall,
    Filter.eventually_gt_atTop (0 : ℕ)] with N ht hH hbound hN
  intro hEven
  exact goldbach_heat_sufficiency_quarter_power N (time N) c
    hN ht.le hbound (hH hEven)

end NCG
