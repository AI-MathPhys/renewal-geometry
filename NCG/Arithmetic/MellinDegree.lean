/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact Mellin-degree coefficients of the squarefree port
  (`thm:v003-mellin-degree`, arithmetic monograph)

For the squarefree Mellin port
`𝔈_{z,X}(n) = μ²(n)·Π_{ℓ|n}(ℓ^{z/L} - 1)`, realized as the formal
power series `mellinSeries L n = Π_{ℓ|n}(rescale (log ℓ/L) exp - 1)`
in `z`, and the generalized von Mangoldt function
`Λ_j(n) = Σ_{d|n} μ(d)(log(n/d))^j`:

* `mellin_degree_coeff` — for squarefree `n` the exact coefficient
  identity `B_{j,X}(n) = Λ_j(n)/(j!·L^j)`;
* `mellin_degree` — the ledger form with the `μ²` projector, valid
  for every `n`;
* `mellin_low_degree_vanish` / `lambdaJ_vanish` — coefficients of
  degree `j < ω(n)` vanish (the product is divisible by `X^ω`);
* `lambdaJ_nonneg` — all `Λ_j(n) ≥ 0` for squarefree `n`
  (nonnegative-coefficient product);
* `lambdaJ_prime` / `lambdaJ_semiprime_two` /
  `lambdaJ_semiprime_three` — the exact low-degree values
  `Λ_j(p) = (log p)^j`, `Λ₂(pq) = 2·log p·log q`,
  `Λ₃(pq) = 3·log p·log q·(log p + log q)`.
-/

namespace NCG

open Finset

/-- The generalized von Mangoldt function
`Λ_j(n) = Σ_{d|n} μ(d)·(log(n/d))^j`. -/
noncomputable def lambdaJ (j : ℕ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)
      * (Real.log n - Real.log d) ^ j

/-- The squarefree Mellin port as a formal power series in the
Mellin variable: `Π_{ℓ|n}(ℓ^{z/L} - 1)`. -/
noncomputable def mellinSeries (L : ℝ) (n : ℕ) : PowerSeries ℝ :=
  ∏ p ∈ n.primeFactors,
    (PowerSeries.rescale (Real.log p / L) (PowerSeries.exp ℝ) - 1)

/-- Products of rescaled exponentials add the rescaling factors. -/
lemma prod_rescale_exp {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∏ i ∈ s, PowerSeries.rescale (a i) (PowerSeries.exp ℝ))
      = PowerSeries.rescale (∑ i ∈ s, a i) (PowerSeries.exp ℝ) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty,
      PowerSeries.rescale_zero]
    simp [PowerSeries.constantCoeff_exp]
  | cons i s hi ih =>
    rw [Finset.prod_cons, ih, PowerSeries.exp_mul_exp_eq_exp_add,
      Finset.sum_cons]

/-- Inclusion–exclusion expansion of the port coefficients over
subsets of the prime support. -/
lemma coeff_mellinSeries (L : ℝ) (n : ℕ) (j : ℕ) :
    PowerSeries.coeff j (mellinSeries L n)
      = ∑ t ∈ n.primeFactors.powerset,
          (-1 : ℝ) ^ (n.primeFactors.card - t.card)
            * ((∑ p ∈ t, Real.log p / L) ^ j / j.factorial) := by
  classical
  rw [mellinSeries]
  have hsub : ∀ p ∈ n.primeFactors,
      PowerSeries.rescale (Real.log p / L) (PowerSeries.exp ℝ) - 1
        = PowerSeries.rescale (Real.log p / L) (PowerSeries.exp ℝ)
          + PowerSeries.C (R := ℝ) (-1) := by
    intro p _
    rw [map_neg, map_one, sub_eq_add_neg]
  rw [Finset.prod_congr rfl hsub, Finset.prod_add, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_const, ← map_pow, prod_rescale_exp,
    PowerSeries.coeff_mul_C, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp]
  have hcs : (n.primeFactors \ t).card
      = n.primeFactors.card - t.card := by
    rw [Finset.card_sdiff,
      Finset.inter_eq_left.mpr (Finset.mem_powerset.mp ht)]
  rw [hcs, show (algebraMap ℚ ℝ) ((1 : ℚ) / j.factorial)
      = 1 / (j.factorial : ℝ) from by
    rw [eq_ratCast]
    push_cast
    ring]
  ring

/-- Reindexing a powerset sum by complements. -/
lemma sum_powerset_compl {α β : Type*} [DecidableEq α]
    [AddCommMonoid β] (P : Finset α) (g : Finset α → β) :
    ∑ t ∈ P.powerset, g t = ∑ t ∈ P.powerset, g (P \ t) := by
  apply Finset.sum_nbij' (i := fun t => P \ t)
    (j := fun t => P \ t) <;> intros <;>
    simp_all [Finset.mem_powerset, Finset.sdiff_subset]

/-- Divisor sums over a squarefree integer are powerset sums over
its prime support. -/
lemma sum_divisors_squarefree_powerset {n : ℕ} (hn : Squarefree n)
    {β : Type*} [AddCommMonoid β] (f : ℕ → β) :
    ∑ d ∈ n.divisors, f d
      = ∑ t ∈ n.primeFactors.powerset, f (∏ p ∈ t, p) := by
  classical
  rw [← Nat.divisors_filter_squarefree_of_squarefree hn,
    Nat.sum_divisors_filter_squarefree hn.ne_zero]
  have hfac : (UniqueFactorizationMonoid.normalizedFactors n).toFinset
      = n.primeFactors := by
    rw [Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors]
  rw [hfac]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_val, Function.id_def]

/-- The subproduct of a subset of the prime support is squarefree
and its Möbius value is `(-1)^|t|`. -/
lemma moebius_prod_subset {n : ℕ} (hn : Squarefree n)
    {t : Finset ℕ} (ht : t ⊆ n.primeFactors) :
    ((ArithmeticFunction.moebius (∏ p ∈ t, p) : ℤ) : ℝ)
      = (-1 : ℝ) ^ t.card := by
  have htp : ∀ p ∈ t, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactors (ht hp)
  have hdvd : (∏ p ∈ t, p) ∣ n := by
    have h1 : (∏ p ∈ t, p) ∣ ∏ p ∈ n.primeFactors, p :=
      Finset.prod_dvd_prod_of_subset t n.primeFactors _ ht
    rwa [Nat.prod_primeFactors_of_squarefree hn] at h1
  have hsq : Squarefree (∏ p ∈ t, p) := hn.squarefree_of_dvd hdvd
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
  have hcard : ArithmeticFunction.cardFactors (∏ p ∈ t, p)
      = t.card := by
    rw [← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
        hsq.ne_zero).mpr hsq,
      ArithmeticFunction.cardDistinctFactors_apply,
      ← List.card_toFinset, Nat.toFinset_factors,
      Nat.primeFactors_prod htp]
  rw [hcard]
  push_cast
  ring

/-- The log of a squarefree integer is the sum of the logs of its
prime factors. -/
lemma log_squarefree {n : ℕ} (hn : Squarefree n) :
    Real.log n = ∑ p ∈ n.primeFactors, Real.log p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  exact Nat.cast_ne_zero.mpr
    (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- Powerset form of the generalized von Mangoldt function on
squarefree integers. -/
lemma lambdaJ_squarefree (j : ℕ) {n : ℕ} (hn : Squarefree n) :
    lambdaJ j n = ∑ t ∈ n.primeFactors.powerset,
      (-1 : ℝ) ^ t.card
        * (∑ p ∈ n.primeFactors \ t, Real.log p) ^ j := by
  classical
  rw [lambdaJ, sum_divisors_squarefree_powerset hn]
  apply Finset.sum_congr rfl
  intro t ht
  have hsub := Finset.mem_powerset.mp ht
  have htp : ∀ p ∈ t, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactors (hsub hp)
  rw [moebius_prod_subset hn hsub]
  congr 1
  have hlogt : Real.log ((∏ p ∈ t, p : ℕ) : ℝ)
      = ∑ p ∈ t, Real.log p := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (htp p hp).ne_zero
  rw [log_squarefree hn, hlogt,
    ← Finset.sum_sdiff hsub, add_sub_cancel_right]

/-- `thm:v003-mellin-degree` (squarefree core): the exact
Mellin-degree coefficients `B_{j,X}(n) = Λ_j(n)/(j!·L_X^j)`. -/
theorem mellin_degree_coeff {L : ℝ} (hL : L ≠ 0) {n : ℕ}
    (hn : Squarefree n) (j : ℕ) :
    PowerSeries.coeff j (mellinSeries L n)
      = lambdaJ j n / (j.factorial * L ^ j) := by
  classical
  rw [coeff_mellinSeries, lambdaJ_squarefree j hn,
    sum_powerset_compl n.primeFactors, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t ht
  have hsub := Finset.mem_powerset.mp ht
  have hcs : (n.primeFactors \ t).card
      = n.primeFactors.card - t.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  have hct : n.primeFactors.card
      - (n.primeFactors.card - t.card) = t.card := by
    have := Finset.card_le_card hsub
    omega
  rw [hcs, hct]
  rw [show (∑ p ∈ n.primeFactors \ t, Real.log p / L)
      = (∑ p ∈ n.primeFactors \ t, Real.log p) / L from
      (Finset.sum_div _ _ _).symm, div_pow]
  have hfac : (j.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hLj : L ^ j ≠ 0 := pow_ne_zero j hL
  field_simp

/-- `thm:v003-mellin-degree` (ledger form): with the `μ²`
projector, `μ²(n)·B_{j,X}(n) = μ²(n)·Λ_j(n)/(j!·L_X^j)` for every
`n`; both sides vanish on nonsquarefree targets. -/
theorem mellin_degree {L : ℝ} (hL : L ≠ 0) (n : ℕ) (j : ℕ) :
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2
        * PowerSeries.coeff j (mellinSeries L n)
      = ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2
          * lambdaJ j n / (j.factorial * L ^ j) := by
  by_cases hsq : Squarefree n
  · rw [mellin_degree_coeff hL hsq j]
    ring
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    push_cast
    ring

/-- Coefficients of degree below the prime multiplicity vanish:
the port is divisible by `X^{ω(n)}`. -/
theorem mellin_low_degree_vanish (L : ℝ) (n : ℕ) {j : ℕ}
    (hj : j < n.primeFactors.card) :
    PowerSeries.coeff j (mellinSeries L n) = 0 := by
  classical
  have hdvd : (PowerSeries.X : PowerSeries ℝ) ^ n.primeFactors.card
      ∣ mellinSeries L n := by
    rw [mellinSeries, ← Finset.prod_const]
    apply Finset.prod_dvd_prod_of_dvd
    intro p _
    rw [PowerSeries.X_dvd_iff, map_sub, map_one]
    rw [show PowerSeries.constantCoeff
        (PowerSeries.rescale (Real.log p / L) (PowerSeries.exp ℝ))
        = 1 from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      simp]
    ring
  exact PowerSeries.X_pow_dvd_iff.mp hdvd j hj

/-- `Λ_j(n) = 0` for squarefree `n` with more than `j` prime
factors. -/
theorem lambdaJ_vanish {n : ℕ} (hn : Squarefree n) {j : ℕ}
    (hjk : j < n.primeFactors.card) : lambdaJ j n = 0 := by
  have h := mellin_degree_coeff (L := 1) one_ne_zero hn j
  rw [mellin_low_degree_vanish 1 n hjk] at h
  have hfac : (j.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have h2 := h.symm
  rw [div_eq_zero_iff] at h2
  rcases h2 with h2 | h2
  · exact h2
  · exact absurd h2 (by positivity)

/-- Each factor of the port has the explicit coefficients
`a^k/k! - [k = 0]`. -/
lemma coeff_factor (a : ℝ) (k : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.rescale a (PowerSeries.exp ℝ) - 1)
      = a ^ k / k.factorial - if k = 0 then 1 else 0 := by
  rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    PowerSeries.coeff_one]
  congr 1
  rw [show (algebraMap ℚ ℝ) ((1 : ℚ) / k.factorial)
      = 1 / (k.factorial : ℝ) from by
    rw [eq_ratCast]
    push_cast
    ring]
  ring

/-- The port coefficients are nonnegative for `L > 0`: every factor
has nonnegative coefficients. -/
theorem coeff_mellinSeries_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ)
    (j : ℕ) : 0 ≤ PowerSeries.coeff j (mellinSeries L n) := by
  classical
  have H := Finset.prod_induction (s := n.primeFactors)
    (fun p : ℕ =>
      PowerSeries.rescale (Real.log p / L) (PowerSeries.exp ℝ) - 1)
    (fun φ : PowerSeries ℝ => ∀ k, 0 ≤ PowerSeries.coeff k φ)
    (fun f g hf hg k => by
      rw [PowerSeries.coeff_mul]
      exact Finset.sum_nonneg fun ij _ =>
        mul_nonneg (hf ij.1) (hg ij.2))
    (fun k => by
      rw [PowerSeries.coeff_one]
      split <;> norm_num)
    (fun p hp k => by
      rw [coeff_factor]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        norm_num
      · rw [if_neg hk.ne']
        have hlog : 0 ≤ Real.log p :=
          Real.log_nonneg (by
            exact_mod_cast
              (Nat.prime_of_mem_primeFactors hp).one_lt.le)
        have ha : 0 ≤ Real.log p / L := div_nonneg hlog hL.le
        rw [sub_zero]
        exact div_nonneg (pow_nonneg ha k) (Nat.cast_nonneg _))
  rw [mellinSeries]
  exact H j

/-- `Λ_j(n) ≥ 0` for squarefree `n`. -/
theorem lambdaJ_nonneg {n : ℕ} (hn : Squarefree n) (j : ℕ) :
    0 ≤ lambdaJ j n := by
  have h := mellin_degree_coeff (L := 1) one_ne_zero hn j
  have hpos := coeff_mellinSeries_nonneg (L := 1) one_pos n j
  rw [h] at hpos
  have hfac : (0 : ℝ) < (j.factorial : ℝ) * 1 ^ j := by positivity
  rcases div_nonneg_iff.mp hpos with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h1
  · linarith

/-- `Λ_j(p) = (log p)^j` at a prime, for `j ≥ 1`. -/
theorem lambdaJ_prime {j : ℕ} (hj : 1 ≤ j) {p : ℕ}
    (hp : p.Prime) : lambdaJ j p = (Real.log p) ^ j := by
  have h := mellin_degree_coeff (L := 1) one_ne_zero
    hp.squarefree j
  have hser : mellinSeries 1 p
      = PowerSeries.rescale (Real.log p / 1) (PowerSeries.exp ℝ)
        - 1 := by
    rw [mellinSeries, Nat.Prime.primeFactors hp,
      Finset.prod_singleton]
  rw [hser, coeff_factor, if_neg (by omega)] at h
  have hfac : (j.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr j.factorial_ne_zero
  rw [div_one, sub_zero] at h
  field_simp at h
  simp only [one_pow, mul_one] at h
  linarith [h]

/-- The port of a squarefree semiprime is the two-factor
product. -/
lemma mellinSeries_semiprime (L : ℝ) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) :
    mellinSeries L (p * q)
      = (PowerSeries.rescale (Real.log p / L) (PowerSeries.exp ℝ)
          - 1)
        * (PowerSeries.rescale (Real.log q / L)
            (PowerSeries.exp ℝ) - 1) := by
  rw [mellinSeries, Nat.primeFactors_mul hp.ne_zero hq.ne_zero,
    Nat.Prime.primeFactors hp, Nat.Prime.primeFactors hq,
    Finset.singleton_union, Finset.prod_pair hne]

/-- `Λ₂(pq) = 2·log p·log q` at a squarefree semiprime. -/
theorem lambdaJ_semiprime_two {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) :
    lambdaJ 2 (p * q) = 2 * Real.log p * Real.log q := by
  have hsq : Squarefree (p * q) := by
    rw [Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hne)]
    exact ⟨hp.squarefree, hq.squarefree⟩
  have h := mellin_degree_coeff (L := 1) one_ne_zero hsq 2
  rw [mellinSeries_semiprime 1 hp hq hne,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    coeff_factor, div_one] at h
  norm_num at h
  have hfac : ((2 : ℕ).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 2)
  field_simp at h
  nlinarith [h]

/-- `Λ₃(pq) = 3·log p·log q·(log p + log q)` at a squarefree
semiprime. -/
theorem lambdaJ_semiprime_three {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) :
    lambdaJ 3 (p * q)
      = 3 * Real.log p * Real.log q
          * (Real.log p + Real.log q) := by
  have hsq : Squarefree (p * q) := by
    rw [Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hne)]
    exact ⟨hp.squarefree, hq.squarefree⟩
  have h := mellin_degree_coeff (L := 1) one_ne_zero hsq 3
  rw [mellinSeries_semiprime 1 hp hq hne,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    coeff_factor, div_one] at h
  norm_num at h
  field_simp at h
  nlinarith [h]

end NCG
