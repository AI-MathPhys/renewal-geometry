/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.MellinDegree

/-!
# The degree-≤2 packet, atom–bulk split, and the signed separator
  (`prop:v003-Ple2-values`, `cor:v003-atom-bulk`,
   `thm:v003-signed-separator`, `cor:v003-signed-additive-closure`,
   arithmetic monograph)

With `B_{j,X}(n) = μ²(n)Λ_j(n)/(j!L^j)` (`mellinB`, exact by
`mellin_degree`):

* `packet_prime` / `packet_semiprime` / `packet_other` — the
  degree-`≤2` packet `𝔓_{≤2} = B₁ + B₂` equals `α + α²/2` at a
  prime, `α₁α₂` at a squarefree semiprime, and `0` otherwise;
* `atom_bulk` — the Selberg-type split
  `𝔓_{≤2}(n) = μ²Λ/L·(1 + log n/2L) + μ²/(2L²)·(Λ₁*Λ₁)(n)`,
  whose first term is the prime atom and whose second is the
  semiprime bulk;
* `separator_prime_value` / `separator_minorant` — the signed
  separator `𝔍 = (6/7)(B₁+B₂-(2/α)B₃)` equals
  `(6/7)α + (1/7)α²` at a prime, vanishes at squarefree
  semiprimes, and satisfies the pointwise minorant
  `𝔍(n) ≤ 1_ℙ(n)`;
* `signed_additive_closure` / `twin_closure` / `goldbach_closure` —
  positivity of a nonnegatively weighted sum of separator values
  forces a prime target (fixed-gap and fixed-sum forms).
-/

namespace NCG

open Finset

/-- The exact Mellin coefficient `B_{j,X}(n) = μ²(n)Λ_j(n)/(j!L^j)`
(the coefficient identity is `NCG.mellin_degree`). -/
noncomputable def mellinB (L : ℝ) (j n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 * lambdaJ j n
    / (j.factorial * L ^ j)

/-- The degree-`≤2` squarefree port `𝔓_{≤2,X} = B₁ + B₂`. -/
noncomputable def packetPle2 (L : ℝ) (n : ℕ) : ℝ :=
  mellinB L 1 n + mellinB L 2 n

/-- The autocorrelation `(Λ₁*Λ₁)(n)`. -/
noncomputable def lambdaConv (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, lambdaJ 1 d * lambdaJ 1 (n / d)

/-- `μ²(n) = 1` on squarefree `n`. -/
lemma moebius_sq_of_squarefree {n : ℕ} (hn : Squarefree n) :
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- `Λ_j(1) = 0` for `j ≥ 1`. -/
lemma lambdaJ_one_eq_zero {j : ℕ} (hj : 1 ≤ j) : lambdaJ j 1 = 0 := by
  rw [lambdaJ, Nat.divisors_one, Finset.sum_singleton]
  simp [zero_pow (by omega : j ≠ 0)]

/-- The prime support of a squarefree semiprime. -/
lemma primeFactors_semiprime {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) :
    (p * q).primeFactors = insert p {q} := by
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,
    Nat.Prime.primeFactors hp, Nat.Prime.primeFactors hq,
    Finset.singleton_union]

/-- `Λ₁` vanishes off primes on the squarefree stratum. -/
lemma lambdaJ_one_ne_prime {d : ℕ} (hd : Squarefree d)
    (hnp : ¬ d.Prime) : lambdaJ 1 d = 0 := by
  rcases eq_or_ne d 1 with h1 | h1
  · subst h1
    exact lambdaJ_one_eq_zero le_rfl
  · have hcard : 1 < d.primeFactors.card := by
      by_contra hle
      push Not at hle
      interval_cases h : d.primeFactors.card
      · have := Finset.card_eq_zero.mp h
        rcases Nat.primeFactors_eq_empty.mp this with h0 | h0
        · exact hd.ne_zero h0
        · exact h1 h0
      · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
        have hdr : d = r := by
          have hprod := Nat.prod_primeFactors_of_squarefree hd
          rw [hr, Finset.prod_singleton] at hprod
          exact hprod.symm
        have : r.Prime := Nat.prime_of_mem_primeFactors
          (hr ▸ Finset.mem_singleton_self r)
        exact hnp (hdr ▸ this)
    exact lambdaJ_vanish hd hcard

/-- Squarefree integers `≥ 2` are primes, squarefree semiprimes,
or have at least three prime factors. -/
lemma squarefree_card_cases {n : ℕ} (hn : Squarefree n)
    (h2 : 2 ≤ n) :
    n.Prime
      ∨ (∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q)
      ∨ 3 ≤ n.primeFactors.card := by
  have hk1 : 1 ≤ n.primeFactors.card := by
    by_contra hk
    push Not at hk
    have h0 : n.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
    rcases Nat.primeFactors_eq_empty.mp h0 with h | h <;> omega
  rcases Nat.lt_or_ge n.primeFactors.card 3 with hlt | hge
  · interval_cases h : n.primeFactors.card
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
      have hnp : n = p := by
        have hprod := Nat.prod_primeFactors_of_squarefree hn
        rw [hp, Finset.prod_singleton] at hprod
        exact hprod.symm
      exact Or.inl (hnp ▸ Nat.prime_of_mem_primeFactors
        (hp ▸ Finset.mem_singleton_self p))
    · obtain ⟨p, q, hne, hpq⟩ := Finset.card_eq_two.mp h
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors
        (hpq ▸ Finset.mem_insert_self p {q})
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors
        (hpq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
      have hnpq : n = p * q := by
        have hprod := Nat.prod_primeFactors_of_squarefree hn
        rw [hpq, Finset.prod_pair hne] at hprod
        exact hprod.symm
      exact Or.inr (Or.inl ⟨p, q, hpp, hqp, hne, hnpq⟩)
  · exact Or.inr (Or.inr hge)

/-- `prop:v003-Ple2-values` (prime): `𝔓_{≤2}(p) = α + α²/2`. -/
theorem packet_prime {L : ℝ} (hL : L ≠ 0) {p : ℕ} (hp : p.Prime) :
    packetPle2 L p
      = Real.log p / L + (Real.log p / L) ^ 2 / 2 := by
  rw [packetPle2, mellinB, mellinB,
    moebius_sq_of_squarefree hp.squarefree,
    lambdaJ_prime le_rfl hp, lambdaJ_prime (by norm_num) hp]
  rw [Nat.factorial_one, Nat.factorial_two]
  push_cast
  field_simp

/-- `prop:v003-Ple2-values` (semiprime): `𝔓_{≤2}(p₁p₂) = α₁α₂`. -/
theorem packet_semiprime {L : ℝ} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    packetPle2 L (p * q)
      = (Real.log p / L) * (Real.log q / L) := by
  have hsq : Squarefree (p * q) := by
    rw [Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hne)]
    exact ⟨hp.squarefree, hq.squarefree⟩
  have hcard : (p * q).primeFactors.card = 2 := by
    rw [primeFactors_semiprime hp hq, Finset.card_insert_of_notMem
      (by simp [hne]), Finset.card_singleton]
  rw [packetPle2, mellinB, mellinB, moebius_sq_of_squarefree hsq,
    lambdaJ_vanish hsq (by omega), lambdaJ_semiprime_two hp hq hne]
  rw [Nat.factorial_two]
  push_cast
  field_simp
  ring

/-- `prop:v003-Ple2-values` (otherwise): the packet vanishes off
primes and squarefree semiprimes. -/
theorem packet_other {L : ℝ} (hL : L ≠ 0) {n : ℕ} (h2 : 2 ≤ n)
    (hnp : ¬ n.Prime)
    (hnsp : ¬ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) :
    packetPle2 L n = 0 := by
  by_cases hsq : Squarefree n
  · rcases squarefree_card_cases hsq h2 with h | h | h
    · exact absurd h hnp
    · exact absurd h hnsp
    · rw [packetPle2, mellinB, mellinB,
        lambdaJ_vanish hsq (by omega : 1 < n.primeFactors.card),
        lambdaJ_vanish hsq (by omega : 2 < n.primeFactors.card)]
      simp
  · rw [packetPle2, mellinB, mellinB,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    push_cast
    simp

/-- The autocorrelation vanishes at primes. -/
lemma lambdaConv_prime {p : ℕ} (hp : p.Prime) :
    lambdaConv p = 0 := by
  rw [lambdaConv, Nat.Prime.divisors hp,
    Finset.sum_pair hp.one_lt.ne]
  rw [Nat.div_one, Nat.div_self hp.pos,
    lambdaJ_one_eq_zero le_rfl]
  ring

/-- Powerset sums over an unordered pair, expanded. -/
lemma sum_powerset_pair {β : Type*} [AddCommMonoid β] {p q : ℕ}
    (hne : p ≠ q) (g : Finset ℕ → β) :
    ∑ t ∈ (insert p {q} : Finset ℕ).powerset, g t
      = g ∅ + g {q} + (g {p} + g (insert p {q})) := by
  classical
  have hpq : p ∉ ({q} : Finset ℕ) := by simp [hne]
  have hdisj : Disjoint (({q} : Finset ℕ).powerset)
      ((({q} : Finset ℕ).powerset).image (insert p)) := by
    rw [Finset.disjoint_left]
    intro u hu hu2
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu2
    have hpu : p ∈ insert p v := Finset.mem_insert_self p v
    have hsub := Finset.mem_powerset.mp hu
    exact hne (Finset.mem_singleton.mp (hsub hpu))
  have hinj : Set.InjOn (insert p)
      ((({q} : Finset ℕ).powerset) : Set (Finset ℕ)) := by
    intro u hu v hv huv
    have hu' := Finset.mem_powerset.mp (by exact_mod_cast hu)
    have hv' := Finset.mem_powerset.mp (by exact_mod_cast hv)
    have hup : p ∉ u := fun hc => hpq (hu' hc)
    have hvp : p ∉ v := fun hc => hpq (hv' hc)
    rw [← Finset.erase_insert hup, ← Finset.erase_insert hvp, huv]
  rw [Finset.powerset_insert, Finset.sum_union hdisj,
    Finset.sum_image hinj]
  have hsing : ({q} : Finset ℕ).powerset = {∅, {q}} := by
    rw [show ({q} : Finset ℕ) = insert q ∅ from rfl,
      Finset.powerset_insert, Finset.powerset_empty]
    rfl
  rw [hsing, Finset.sum_insert (by simp), Finset.sum_singleton,
    Finset.sum_insert (by simp), Finset.sum_singleton]
  rw [Finset.insert_empty]

/-- The autocorrelation at a squarefree semiprime is
`2·log p·log q`. -/
lemma lambdaConv_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) :
    lambdaConv (p * q) = 2 * Real.log p * Real.log q := by
  have hsq : Squarefree (p * q) := by
    rw [Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hne)]
    exact ⟨hp.squarefree, hq.squarefree⟩
  rw [lambdaConv, sum_divisors_squarefree_powerset hsq,
    primeFactors_semiprime hp hq, sum_powerset_pair hne]
  rw [Finset.prod_empty, Finset.prod_singleton,
    Finset.prod_singleton, Finset.prod_insert (by simp [hne]),
    Finset.prod_singleton]
  rw [Nat.div_one, Nat.mul_div_cancel p hq.pos,
    Nat.mul_div_cancel_left q hp.pos,
    Nat.div_self (Nat.mul_pos hp.pos hq.pos)]
  rw [lambdaJ_one_eq_zero le_rfl, lambdaJ_prime le_rfl hp,
    lambdaJ_prime le_rfl hq, lambdaJ_one_ne_prime hsq
      (Nat.not_prime_mul hp.one_lt.ne' hq.one_lt.ne')]
  ring

/-- The autocorrelation vanishes on squarefree integers with at
least three prime factors. -/
lemma lambdaConv_deep {n : ℕ} (hn : Squarefree n)
    (h3 : 3 ≤ n.primeFactors.card) : lambdaConv n = 0 := by
  rw [lambdaConv]
  apply Finset.sum_eq_zero
  intro d hd
  have hddvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  by_cases h1 : lambdaJ 1 d = 0
  · rw [h1, zero_mul]
  by_cases hq2 : lambdaJ 1 (n / d) = 0
  · rw [hq2, mul_zero]
  exfalso
  have hdp : d.Prime := by
    by_contra hnp
    exact h1 (lambdaJ_one_ne_prime (hn.squarefree_of_dvd hddvd) hnp)
  have hqp : (n / d).Prime := by
    by_contra hnp
    exact hq2 (lambdaJ_one_ne_prime
      (hn.squarefree_of_dvd (Nat.div_dvd_of_dvd hddvd)) hnp)
  have hnd : d * (n / d) = n := Nat.mul_div_cancel' hddvd
  have hle : n.primeFactors.card ≤ 2 := by
    rw [← hnd, Nat.primeFactors_mul hdp.ne_zero hqp.ne_zero,
      Nat.Prime.primeFactors hdp, Nat.Prime.primeFactors hqp]
    exact le_trans (Finset.card_union_le _ _) (by simp)
  omega

/-- `cor:v003-atom-bulk`: the exact Selberg-type split of the
degree-`≤2` packet into the prime atom and the semiprime bulk. -/
theorem atom_bulk {L : ℝ} (hL : L ≠ 0) {n : ℕ} (h2 : 2 ≤ n) :
    packetPle2 L n
      = ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2
            * lambdaJ 1 n / L * (1 + Real.log n / (2 * L))
        + ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2
            / (2 * L ^ 2) * lambdaConv n := by
  by_cases hsq : Squarefree n
  · have hsel : lambdaJ 2 n
        = lambdaJ 1 n * Real.log n + lambdaConv n := by
      rcases squarefree_card_cases hsq h2 with h | h | h
      · rw [lambdaJ_prime le_rfl h, lambdaJ_prime (by norm_num) h,
          lambdaConv_prime h]
        ring
      · obtain ⟨p, q, hp, hq, hne, rfl⟩ := h
        have hcard : (p * q).primeFactors.card = 2 := by
          rw [primeFactors_semiprime hp hq,
            Finset.card_insert_of_notMem (by simp [hne]),
            Finset.card_singleton]
        rw [lambdaJ_semiprime_two hp hq hne,
          lambdaJ_vanish hsq (by omega),
          lambdaConv_semiprime hp hq hne]
        ring
      · rw [lambdaJ_vanish hsq (by omega : 1 < n.primeFactors.card),
          lambdaJ_vanish hsq (by omega : 2 < n.primeFactors.card),
          lambdaConv_deep hsq h]
        ring
    rw [packetPle2, mellinB, mellinB, hsel,
      Nat.factorial_one, Nat.factorial_two]
    push_cast
    field_simp
    ring
  · rw [packetPle2, mellinB, mellinB,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    push_cast
    simp

/-- The signed separator
`𝔍_X = (6/7)(B₁ + B₂ - (2/α)B₃)`, `α = log n / L`. -/
noncomputable def separatorJ (L : ℝ) (n : ℕ) : ℝ :=
  6 / 7 * (mellinB L 1 n + mellinB L 2 n
    - 2 / (Real.log n / L) * mellinB L 3 n)

/-- `thm:v003-signed-separator` (prime value):
`𝔍(p) = (6/7)α + (1/7)α²`. -/
theorem separator_prime_value {L : ℝ} (hL : 0 < L) {p : ℕ}
    (hp : p.Prime) :
    separatorJ L p
      = 6 / 7 * (Real.log p / L)
        + 1 / 7 * (Real.log p / L) ^ 2 := by
  have hlog : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [separatorJ, mellinB, mellinB, mellinB,
    moebius_sq_of_squarefree hp.squarefree,
    lambdaJ_prime le_rfl hp, lambdaJ_prime (by norm_num) hp,
    lambdaJ_prime (by norm_num) hp,
    Nat.factorial_one, Nat.factorial_two]
  rw [show (3 : ℕ).factorial = 6 from rfl]
  push_cast
  field_simp
  ring

/-- `thm:v003-signed-separator` (semiprime cancellation):
`𝔍(pq) = 0`. -/
theorem separator_semiprime {L : ℝ} (hL : 0 < L) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    separatorJ L (p * q) = 0 := by
  have hsq : Squarefree (p * q) := by
    rw [Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hne)]
    exact ⟨hp.squarefree, hq.squarefree⟩
  have hcard : (p * q).primeFactors.card = 2 := by
    rw [primeFactors_semiprime hp hq,
      Finset.card_insert_of_notMem (by simp [hne]),
      Finset.card_singleton]
  have ha : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast hq.one_lt)
  have hlog : Real.log ((p * q : ℕ) : ℝ)
      = Real.log p + Real.log q := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
  rw [separatorJ, mellinB, mellinB, mellinB,
    moebius_sq_of_squarefree hsq,
    lambdaJ_vanish hsq (by omega),
    lambdaJ_semiprime_two hp hq hne,
    lambdaJ_semiprime_three hp hq hne, hlog,
    Nat.factorial_one, Nat.factorial_two]
  rw [show (3 : ℕ).factorial = 6 from rfl]
  push_cast
  field_simp
  ring

/-- `thm:v003-signed-separator` (pointwise prime minorant):
`𝔍(n) ≤ 1_ℙ(n)` for `2 ≤ n` and `log n ≤ L`. -/
theorem separator_minorant {L : ℝ} (hL : 0 < L) {n : ℕ}
    (h2 : 2 ≤ n) (halpha : Real.log n ≤ L) :
    separatorJ L n ≤ (if n.Prime then 1 else 0) := by
  have hlogn : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast h2)
  by_cases hprime : n.Prime
  · rw [if_pos hprime, separator_prime_value hL hprime]
    have halpha1 : Real.log n / L ≤ 1 :=
      (div_le_one hL).mpr halpha
    have halpha0 : 0 < Real.log n / L := div_pos hlogn hL
    nlinarith
  · rw [if_neg hprime]
    by_cases hsq : Squarefree n
    · rcases squarefree_card_cases hsq h2 with h | h | h
      · exact absurd h hprime
      · obtain ⟨p, q, hp, hq, hne, rfl⟩ := h
        rw [separator_semiprime hL hp hq hne]
      · have hB3 : 0 ≤ mellinB L 3 n := by
          rw [mellinB, moebius_sq_of_squarefree hsq]
          have := lambdaJ_nonneg hsq 3
          positivity
        have halphapos : 0 < Real.log n / L := div_pos hlogn hL
        rw [separatorJ, mellinB, mellinB,
          lambdaJ_vanish hsq (by omega : 1 < n.primeFactors.card),
          lambdaJ_vanish hsq (by omega : 2 < n.primeFactors.card)]
        have hterm : 0 ≤ 2 / (Real.log n / L) * mellinB L 3 n := by
          positivity
        simp only [mul_zero, zero_mul, zero_div, zero_add,
          mul_div_assoc]
        nlinarith
    · rw [separatorJ, mellinB, mellinB, mellinB,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      push_cast
      simp

/-- `cor:v003-signed-additive-closure` (abstract form): a positive
nonnegatively-weighted sum of minorant values forces a prime
target. -/
theorem signed_additive_closure {S : Finset ℕ} (w J : ℕ → ℝ)
    (g : ℕ → ℕ) (hw : ∀ p ∈ S, 0 ≤ w p)
    (hminor : ∀ p ∈ S, J (g p) ≤ if (g p).Prime then 1 else 0)
    (hpos : 0 < ∑ p ∈ S, w p * J (g p)) :
    ∃ p ∈ S, (g p).Prime := by
  by_contra hall
  push Not at hall
  have hnonpos : ∀ p ∈ S, w p * J (g p) ≤ 0 := by
    intro p hp
    have hm := hminor p hp
    rw [if_neg (hall p hp)] at hm
    exact mul_nonpos_iff.mpr (Or.inr ⟨hw p hp, hm⟩)
  exact absurd (Finset.sum_nonpos hnonpos) (not_le.mpr hpos)

/-- `cor:v003-signed-additive-closure` (fixed gap): positivity of
the twin correlation forces a twin-prime pair. -/
theorem twin_closure {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (J : ℕ → ℝ)
    (hminor : ∀ p ∈ S, J (p + 2) ≤ if (p + 2).Prime then 1 else 0)
    (hpos : 0 < ∑ p ∈ S, Real.log p * J (p + 2)) :
    ∃ p ∈ S, p.Prime ∧ (p + 2).Prime := by
  obtain ⟨p, hp, hprime⟩ := signed_additive_closure
    (fun p => Real.log p) J (· + 2)
    (fun p hp => Real.log_nonneg
      (by exact_mod_cast (hS p hp).one_lt.le)) hminor hpos
  exact ⟨p, hp, hS p hp, hprime⟩

/-- `cor:v003-signed-additive-closure` (fixed sum): positivity of
the Goldbach correlation forces a prime decomposition of `N`. -/
theorem goldbach_closure (N : ℕ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hSN : ∀ p ∈ S, p ≤ N) (J : ℕ → ℝ)
    (hminor : ∀ p ∈ S, J (N - p) ≤ if (N - p).Prime then 1 else 0)
    (hpos : 0 < ∑ p ∈ S, Real.log p * J (N - p)) :
    ∃ p ∈ S, p.Prime ∧ (N - p).Prime ∧ p + (N - p) = N := by
  obtain ⟨p, hp, hprime⟩ := signed_additive_closure
    (fun p => Real.log p) J (N - ·)
    (fun p hp => Real.log_nonneg
      (by exact_mod_cast (hS p hp).one_lt.le)) hminor hpos
  exact ⟨p, hp, hS p hp, hprime, by
    have := hSN p hp
    omega⟩

end NCG
