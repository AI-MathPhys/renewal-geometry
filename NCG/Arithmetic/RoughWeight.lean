/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pointwise support of the rough weight
  (`lem:v003-rough-weight-support`, arithmetic monograph)

The rough sieve weight
`w_κ(n;x) = 1[P⁻(n) ≥ x^κ] − 1[Ω(n) ≥ 2]·1[P⁻(n) ≥ x^τ]
  + 1[Ω(n) ≥ 3]·1[P⁻(n) ≥ x^τ] − 1[Ω(n) ≥ 3]·1[P⁻(n) ≥ x^κ]`
is formalized as `roughWeight a b n` with the two thresholds
`a = x^κ ≤ b = x^τ` as real parameters.  `rough_weight_support`
computes it exactly: under `1 < a ≤ b` and `b² ≤ n` (the form the
manuscript's "`n ≍ x`, `x` large, `τ < 1/2`" hypotheses take in the
proof), the weight is `1` precisely when `n` is prime or `n = rq`
with distinct primes `r < q` and `a ≤ r < b`, and `0` otherwise.
-/

open ArithmeticFunction

namespace NCG

/-- The rough weight `w_κ(n;x)` with thresholds `a = x^κ`, `b = x^τ`:
`1[P⁻(n) ≥ a] − 1[Ω(n) ≥ 2]·1[P⁻(n) ≥ b]
  + 1[Ω(n) ≥ 3]·1[P⁻(n) ≥ b] − 1[Ω(n) ≥ 3]·1[P⁻(n) ≥ a]`. -/
noncomputable def roughWeight (a b : ℝ) (n : ℕ) : ℤ :=
  (if a ≤ (n.minFac : ℝ) then 1 else 0)
    - (if 2 ≤ cardFactors n then 1 else 0)
        * (if b ≤ (n.minFac : ℝ) then 1 else 0)
    + (if 3 ≤ cardFactors n then 1 else 0)
        * (if b ≤ (n.minFac : ℝ) then 1 else 0)
    - (if 3 ≤ cardFactors n then 1 else 0)
        * (if a ≤ (n.minFac : ℝ) then 1 else 0)

open scoped Classical in
/-- `lem:v003-rough-weight-support`: for `1 < a ≤ b` and `b² ≤ n`,
the rough weight equals `1` exactly when `n` is prime or `n = rq`
with distinct primes `r < q`, `a ≤ r < b`; otherwise it vanishes. -/
theorem rough_weight_support {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    {n : ℕ} (hn : b * b ≤ (n : ℝ)) :
    roughWeight a b n
      = if n.Prime ∨ ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ r < q ∧ n = r * q
            ∧ a ≤ (r : ℝ) ∧ (r : ℝ) < b
        then 1 else 0 := by
  classical
  have hb1 : (1 : ℝ) < b := lt_of_lt_of_le ha hab
  have hn1 : 1 < n := by
    have h1 : (1 : ℝ) < b * b := by nlinarith
    have h2 : (1 : ℝ) < (n : ℝ) := lt_of_lt_of_le h1 hn
    exact_mod_cast h2
  simp only [roughWeight]
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  set m := n / p with hmdef
  have hnm : n = p * m := (Nat.mul_div_cancel' hpdvd).symm
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, mul_zero] at hnm
    omega
  have hΩsplit : cardFactors n = 1 + cardFactors m := by
    conv_lhs => rw [hnm]
    rw [cardFactors_mul hp.pos.ne' hm0, cardFactors_apply_prime hp]
  -- any distinct-prime factorization has the least prime first
  have hrepr : ∀ r q : ℕ, r.Prime → q.Prime → r < q → n = r * q →
      r = p := by
    intro r q hr hq hrq hn'
    have hrdvd : r ∣ n := ⟨q, hn'⟩
    have h1 : p ≤ r := Nat.minFac_le_of_dvd hr.two_le hrdvd
    have h2 : p ∣ r * q := hn' ▸ hpdvd
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
    · exact ((Nat.prime_dvd_prime_iff_eq hp hr).mp h).symm
    · have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
      omega
  clear_value p m
  by_cases hm1 : m = 1
  · -- depth one: `n = p` is prime
    have hnp : n = p := by rw [hnm, hm1, mul_one]
    have hΩ1 : cardFactors n = 1 := by
      rw [hΩsplit, hm1, cardFactors_one]
    have hprime : n.Prime := hnp ▸ hp
    have hap : a ≤ (p : ℝ) := by
      have h2 : a ≤ (n : ℝ) := by nlinarith
      exact hnp ▸ h2
    have hc2 : ¬ 2 ≤ cardFactors n := by omega
    have hc3 : ¬ 3 ≤ cardFactors n := by omega
    rw [if_pos hap, if_neg hc2, if_neg hc3, if_pos (Or.inl hprime)]
    ring
  · have hm2 : 2 ≤ m := by omega
    set q1 := m.minFac with hq1def
    have hq1 : q1.Prime := Nat.minFac_prime (by omega)
    have hq1dvd : q1 ∣ m := Nat.minFac_dvd m
    set m2 := m / q1 with hm2def
    have hmq : m = q1 * m2 := (Nat.mul_div_cancel' hq1dvd).symm
    have hm20 : m2 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hmq
      omega
    have hΩm : cardFactors m = 1 + cardFactors m2 := by
      conv_lhs => rw [hmq]
      rw [cardFactors_mul hq1.pos.ne' hm20, cardFactors_apply_prime hq1]
    clear_value q1 m2
    by_cases hm21 : m2 = 1
    · -- depth two: `n = p·m` with `m` prime
      have hmq1 : m = q1 := by rw [hmq, hm21, mul_one]
      have hΩ2 : cardFactors n = 2 := by
        rw [hΩsplit, hΩm, hm21, cardFactors_one]
      have hmprime : m.Prime := hmq1 ▸ hq1
      have hnprime : ¬ n.Prime := by
        intro hpr
        have := cardFactors_eq_one_iff_prime.mpr hpr
        omega
      by_cases hbp : b ≤ (p : ℝ)
      · -- least factor at or above the upper threshold: weight `0`
        have hap : a ≤ (p : ℝ) := le_trans hab hbp
        have hRHS : ¬(n.Prime ∨ ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ r < q
            ∧ n = r * q ∧ a ≤ (r : ℝ) ∧ (r : ℝ) < b) := by
          rintro (hpr | ⟨r, q, hr, hq, hrq, hn', _, hrb⟩)
          · exact hnprime hpr
          · rw [hrepr r q hr hq hrq hn'] at hrb
            linarith
        have hc2 : 2 ≤ cardFactors n := by omega
        have hc3 : ¬ 3 ≤ cardFactors n := by omega
        rw [if_pos hap, if_pos hbp, if_pos hc2, if_neg hc3, if_neg hRHS]
        ring
      · rw [not_le] at hbp
        by_cases hap : a ≤ (p : ℝ)
        · -- the sieved semiprime window: weight `1`
          have hpm : p < m := by
            by_contra hle
            rw [not_lt] at hle
            have h1 : (m : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
            have h2 : (n : ℝ) = (p : ℝ) * (m : ℝ) := by
              exact_mod_cast hnm
            nlinarith [Nat.cast_nonneg (α := ℝ) m]
          have hc2 : 2 ≤ cardFactors n := by omega
          have hc3 : ¬ 3 ≤ cardFactors n := by omega
          have hRHS : n.Prime ∨ ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ r < q
              ∧ n = r * q ∧ a ≤ (r : ℝ) ∧ (r : ℝ) < b :=
            Or.inr ⟨p, m, hp, hmprime, hpm, hnm, hap, hbp⟩
          rw [if_pos hap, if_neg (not_le.mpr hbp), if_pos hc2,
            if_neg hc3, if_pos hRHS]
          ring
        · rw [not_le] at hap
          have hRHS : ¬(n.Prime ∨ ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ r < q
              ∧ n = r * q ∧ a ≤ (r : ℝ) ∧ (r : ℝ) < b) := by
            rintro (hpr | ⟨r, q, hr, hq, hrq, hn', har, _⟩)
            · exact hnprime hpr
            · rw [hrepr r q hr hq hrq hn'] at har
              linarith
          have hc2 : 2 ≤ cardFactors n := by omega
          have hc3 : ¬ 3 ≤ cardFactors n := by omega
          rw [if_neg (not_le.mpr hap), if_neg (not_le.mpr hbp),
            if_pos hc2, if_neg hc3, if_neg hRHS]
          ring
    · -- depth at least three: the two deep terms cancel everything
      have hm22 : 2 ≤ m2 := by omega
      have hΩm2pos : 1 ≤ cardFactors m2 := by
        have hq2 : m2.minFac.Prime := Nat.minFac_prime (by omega)
        have hdvd2 : m2.minFac ∣ m2 := Nat.minFac_dvd m2
        have h2 : m2 = m2.minFac * (m2 / m2.minFac) :=
          (Nat.mul_div_cancel' hdvd2).symm
        have h20 : m2 / m2.minFac ≠ 0 := by
          intro h
          rw [h, mul_zero] at h2
          omega
        have h3 : cardFactors m2 = 1 + cardFactors (m2 / m2.minFac) := by
          conv_lhs => rw [h2]
          rw [cardFactors_mul hq2.pos.ne' h20, cardFactors_apply_prime hq2]
        omega
      have hΩ3 : 3 ≤ cardFactors n := by
        rw [hΩsplit, hΩm]
        omega
      have hRHS : ¬(n.Prime ∨ ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ r < q
          ∧ n = r * q ∧ a ≤ (r : ℝ) ∧ (r : ℝ) < b) := by
        rintro (hpr | ⟨r, q, hr, hq, hrq, hn', _, _⟩)
        · have := cardFactors_eq_one_iff_prime.mpr hpr
          omega
        · have h2 : cardFactors n = 2 := by
            rw [hn', cardFactors_mul hr.pos.ne' hq.pos.ne',
              cardFactors_apply_prime hr, cardFactors_apply_prime hq]
          omega
      have hc2 : 2 ≤ cardFactors n := by omega
      rw [if_pos hc2, if_pos hΩ3, if_neg hRHS]
      ring

end NCG
