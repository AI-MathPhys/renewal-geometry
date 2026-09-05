/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Parity-current algebra on a `P₁ ∪ P₂` carrier
  (`thm:parity-recovery`, `thm:twin-chain`, `thm:gold-chain`,
   `prop:v003-matching-energy`, `prop:v003-negative-temperature`,
   `prop:v003-ratio-conversion`,
   `prop:v003-minimal-singular-series`, `prop:phase-firewall`,
   arithmetic monograph)

* `parity_recovery` — on a depth-`≤2` carrier with mass
  `M = P₁ + P₂` and Möbius current `𝒥 = -P₁ + P₂`:
  `P₁ = (M-𝒥)/2`, `P₂ = (M+𝒥)/2`, and `𝒥 ≤ (1-2δ)M ⇒ P₁ ≥ δM`;
* `carrier_prime_mass` / `twin_chain` / `gold_chain` — the
  conditional additive-closure chains: a positive carrier with
  small Möbius current has positive prime-fibre mass, hence a
  supported twin pair (resp. Goldbach pair) exists;
* `matching_identity` / `matching_energy` — `2XY = X+Y-(X-Y)²` on
  binaries and the weighted decomposition `2ℰ_w = 𝒱_w - 𝒟_w`;
* `mellin_negative_temperature` — the exact positive/negative
  temperature identity `n^c·𝔈_{-c}(n) = μ(n)·𝔈_c(n)` for the
  squarefree Mellin port;
* `ratio_conversion` — `r ≤ q^a ⇒ log r/log(rq) ≤ a/(1+a)` and
  `log q/log(rq) ≥ 1/(1+a)`;
* `minimal_singular_series` — `Sing(d) ≥ Sing(2)` with equality
  iff `d` has no odd prime divisor;
* `phase_firewall` — a global relative phase leaves the endpoint
  density matrix unchanged while `‖a-b‖² = 2‖a‖²(1-cos φ)`.
-/

namespace NCG

open Finset

/-- `thm:parity-recovery`: exact depth-one recovery from mass and
Möbius current, with the quantitative positivity clause. -/
theorem parity_recovery (P1 P2 M J delta : ℝ)
    (hM : M = P1 + P2) (hJ : J = -P1 + P2) :
    P1 = (M - J) / 2 ∧ P2 = (M + J) / 2
      ∧ (J ≤ (1 - 2 * delta) * M → delta * M ≤ P1) := by
  refine ⟨by rw [hM, hJ]; ring, by rw [hM, hJ]; ring, ?_⟩
  intro hbound
  nlinarith [hbound]

/-- A positive carrier whose Möbius grading current is at most
`(1-2δ)·M` while the mass is at least `m₀ > 0` has strictly
positive prime-fibre mass: some target of positive weight is
prime. -/
theorem carrier_prime_mass {C : Type*} [Fintype C]
    (w : C → ℝ) (tgt : C → ℕ) (m0 delta : ℝ)
    (hw : ∀ c, 0 ≤ w c) (hm0 : 0 < m0) (hdelta : 0 < delta)
    (hM : m0 ≤ ∑ c, w c)
    (hJ : ∑ c, w c * (if Nat.Prime (tgt c) then (-1 : ℝ) else 1)
      ≤ (1 - 2 * delta) * ∑ c, w c) :
    ∃ c, 0 < w c ∧ Nat.Prime (tgt c) := by
  classical
  have hMJ : (∑ c, w c)
      - (∑ c, w c * (if Nat.Prime (tgt c) then (-1 : ℝ) else 1))
      = 2 * ∑ c ∈ Finset.univ.filter
          (fun c => Nat.Prime (tgt c)), w c := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : Nat.Prime (tgt c)
    · rw [if_pos hc, if_pos hc]
      ring
    · rw [if_neg hc, if_neg hc]
      ring
  have hP1 : delta * m0 ≤ ∑ c ∈ Finset.univ.filter
      (fun c => Nat.Prime (tgt c)), w c := by
    nlinarith [hMJ, hJ, hM,
      mul_le_mul_of_nonneg_left hM hdelta.le]
  have hpos : 0 < ∑ c ∈ Finset.univ.filter
      (fun c => Nat.Prime (tgt c)), w c := by
    nlinarith
  by_contra hcon
  push Not at hcon
  have hzero : (∑ c ∈ Finset.univ.filter
      (fun c => Nat.Prime (tgt c)), w c) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_filter] at hc
    have := hcon c
    have hle : w c ≤ 0 := by
      by_contra hlt
      push Not at hlt
      exact absurd hc.2 (this hlt)
    linarith [hw c]
  linarith

/-- `thm:twin-chain` (finite-carrier form): a positive twin carrier
(`targets p+2` of depth `≤ 2`) with mass `≥ m₀` and Möbius current
`≤ (1-2δ)M` supports a twin-prime pair. -/
theorem twin_chain {C : Type*} [Fintype C]
    (w : C → ℝ) (p : C → ℕ) (m0 delta : ℝ)
    (hw : ∀ c, 0 ≤ w c) (hm0 : 0 < m0) (hdelta : 0 < delta)
    (hp : ∀ c, Nat.Prime (p c))
    (hM : m0 ≤ ∑ c, w c)
    (hJ : ∑ c, w c
        * (if Nat.Prime (p c + 2) then (-1 : ℝ) else 1)
      ≤ (1 - 2 * delta) * ∑ c, w c) :
    ∃ c, 0 < w c ∧ Nat.Prime (p c) ∧ Nat.Prime (p c + 2) := by
  obtain ⟨c, hc, hprime⟩ := carrier_prime_mass w
    (fun c => p c + 2) m0 delta hw hm0 hdelta hM hJ
  exact ⟨c, hc, hp c, hprime⟩

/-- `thm:gold-chain` (finite-carrier form): a positive Goldbach
carrier for even `N` (targets `N - p`) with mass `≥ m₀` and Möbius
current `≤ (1-2δ)M` represents `N` as a sum of two primes. -/
theorem gold_chain {C : Type*} [Fintype C]
    (w : C → ℝ) (p : C → ℕ) (N : ℕ) (m0 delta : ℝ)
    (hw : ∀ c, 0 ≤ w c) (hm0 : 0 < m0) (hdelta : 0 < delta)
    (hp : ∀ c, Nat.Prime (p c)) (hsum : ∀ c, p c ≤ N)
    (hM : m0 ≤ ∑ c, w c)
    (hJ : ∑ c, w c
        * (if Nat.Prime (N - p c) then (-1 : ℝ) else 1)
      ≤ (1 - 2 * delta) * ∑ c, w c) :
    ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ a + b = N := by
  obtain ⟨c, -, hprime⟩ := carrier_prime_mass w
    (fun c => N - p c) m0 delta hw hm0 hdelta hM hJ
  have := hsum c
  exact ⟨p c, N - p c, hp c, hprime, by omega⟩

/-- The binary matching identity `2XY = X + Y - (X-Y)²`. -/
theorem matching_identity (X Y : ℝ) (hX : X ^ 2 = X)
    (hY : Y ^ 2 = Y) :
    2 * (X * Y) = X + Y - (X - Y) ^ 2 := by
  linear_combination hX + hY

/-- `prop:v003-matching-energy`: the weighted decomposition
`2ℰ_w = 𝒱_w - 𝒟_w` for binary coordinates. -/
theorem matching_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (X Y : ι → κ → ℝ)
    (hX : ∀ n j, X n j ^ 2 = X n j)
    (hY : ∀ n j, Y n j ^ 2 = Y n j) :
    2 * ∑ n, w n * ∑ j, X n j * Y n j
      = (∑ n, w n * ∑ j, (X n j + Y n j))
        - ∑ n, w n * ∑ j, (X n j - Y n j) ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [show w n * ∑ j, (X n j + Y n j)
      - w n * ∑ j, (X n j - Y n j) ^ 2
    = w n * ((∑ j, (X n j + Y n j))
      - ∑ j, (X n j - Y n j) ^ 2) from by ring]
  rw [show (2 : ℝ) * (w n * ∑ j, X n j * Y n j)
    = w n * (2 * ∑ j, X n j * Y n j) from by ring]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination hX n j + hY n j

/-- The squarefree Mellin port `𝔈_c(n) = μ²(n)·Π_{ℓ|n}(ℓ^c - 1)`. -/
noncomputable def mellinPort (c : ℝ) (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2
    * ∏ ℓ ∈ n.primeFactors, ((ℓ : ℝ) ^ c - 1)

/-- `prop:v003-negative-temperature`: the exact positive/negative
temperature identity `n^c·𝔈_{-c}(n) = μ(n)·𝔈_c(n)`. -/
theorem mellin_negative_temperature (c : ℝ) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ c * mellinPort (-c) n
      = ((ArithmeticFunction.moebius n : ℤ) : ℝ)
        * mellinPort c n := by
  by_cases hsq : Squarefree n
  · have hprim : ∀ ℓ ∈ n.primeFactors, (0 : ℝ) < (ℓ : ℝ) := by
      intro ℓ hl
      exact_mod_cast (Nat.prime_of_mem_primeFactors hl).pos
    have hprod : (∏ ℓ ∈ n.primeFactors, (ℓ : ℝ)) = (n : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    have hnpow : (n : ℝ) ^ c
        = ∏ ℓ ∈ n.primeFactors, (ℓ : ℝ) ^ c := by
      rw [← hprod, ← Real.finsetProd_rpow _ _
        (fun ℓ hl => (hprim ℓ hl).le)]
    have hcard : ArithmeticFunction.cardFactors n
        = n.primeFactors.card := by
      rw [← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
        hn.ne').mpr hsq]
      exact ArithmeticFunction.cardDistinctFactors_apply
    have hmu : ((ArithmeticFunction.moebius n : ℤ) : ℝ)
        = (-1 : ℝ) ^ n.primeFactors.card := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, hcard]
      push_cast
      ring
    have hmu2 : ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2
        = 1 := by
      rw [hmu, ← pow_mul, mul_comm, pow_mul]
      norm_num
    unfold mellinPort
    rw [hmu2, hnpow, hmu]
    rw [show (∏ ℓ ∈ n.primeFactors, (ℓ : ℝ) ^ c)
        * (1 * ∏ ℓ ∈ n.primeFactors, ((ℓ : ℝ) ^ (-c) - 1))
      = ∏ ℓ ∈ n.primeFactors,
          ((ℓ : ℝ) ^ c * ((ℓ : ℝ) ^ (-c) - 1)) from by
        rw [one_mul, ← Finset.prod_mul_distrib]]
    rw [show (∏ ℓ ∈ n.primeFactors,
        ((ℓ : ℝ) ^ c * ((ℓ : ℝ) ^ (-c) - 1)))
      = ∏ ℓ ∈ n.primeFactors,
          (-1 * ((ℓ : ℝ) ^ c - 1)) from ?_]
    · rw [Finset.prod_mul_distrib, Finset.prod_const]
      ring
    · apply Finset.prod_congr rfl
      intro ℓ hl
      have hpos := hprim ℓ hl
      rw [mul_sub, ← Real.rpow_add hpos, add_neg_cancel,
        Real.rpow_zero]
      ring
  · have hmu0 : (ArithmeticFunction.moebius n : ℤ) = 0 := by
      exact_mod_cast
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    unfold mellinPort
    rw [hmu0]
    push_cast
    ring

/-- `prop:v003-ratio-conversion`: if `1 ≤ r ≤ q^a` with `q ≥ 2`,
then `log r/log(rq) ≤ a/(1+a)` and `log q/log(rq) ≥ 1/(1+a)`. -/
theorem ratio_conversion (r q : ℕ) (a : ℝ) (hr : 1 ≤ r)
    (hq : 2 ≤ q) (ha : 0 ≤ a) (hle : (r : ℝ) ≤ (q : ℝ) ^ a) :
    Real.log r / Real.log (r * q) ≤ a / (1 + a)
      ∧ 1 / (1 + a) ≤ Real.log q / Real.log (r * q) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hqpos : (0 : ℝ) < q := by positivity
  have hLq : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast hq)
  have hLr : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  have hLrq : Real.log ((r : ℝ) * q) = Real.log r + Real.log q :=
    Real.log_mul (ne_of_gt hrpos) (ne_of_gt hqpos)
  have hbound : Real.log r ≤ a * Real.log q := by
    calc Real.log r ≤ Real.log ((q : ℝ) ^ a) :=
          Real.log_le_log hrpos hle
    _ = a * Real.log q := Real.log_rpow hqpos a
  have hden : (0 : ℝ) < Real.log r + Real.log q := by linarith
  have h1a : (0 : ℝ) < 1 + a := by linarith
  constructor
  · rw [hLrq, div_le_div_iff₀ hden h1a]
    nlinarith
  · rw [hLrq, div_le_div_iff₀ h1a hden]
    nlinarith

/-- `prop:v003-minimal-singular-series`: the gap-`2` singular
series is minimal among even gaps, `Sing(d) ≥ Sing(2)`, with
equality iff `d` has no odd prime divisor. -/
theorem minimal_singular_series (Sing2 : ℝ) (hS : 0 < Sing2)
    (S : Finset ℕ) (hodd : ∀ ℓ ∈ S, 3 ≤ ℓ) :
    Sing2 ≤ Sing2 * ∏ ℓ ∈ S, ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2)
      ∧ (Sing2 * ∏ ℓ ∈ S, ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) = Sing2
        ↔ S = ∅) := by
  have hfac : ∀ ℓ ∈ S, (1 : ℝ) < ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) := by
    intro ℓ hl
    have h3 : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hodd ℓ hl
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hprod : (1 : ℝ) ≤ ∏ ℓ ∈ S, ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) := by
    calc (1 : ℝ) = ∏ _ℓ ∈ S, (1 : ℝ) := by
          rw [Finset.prod_const_one]
    _ ≤ ∏ ℓ ∈ S, ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) :=
          Finset.prod_le_prod (fun _ _ => zero_le_one)
            (fun ℓ hl => (hfac ℓ hl).le)
  constructor
  · nlinarith
  · constructor
    · intro heq
      by_contra hne
      have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨l0, hl0⟩ := hSne
      have hrest : (1 : ℝ) ≤ ∏ ℓ ∈ S.erase l0,
          ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) := by
        calc (1 : ℝ) = ∏ _ℓ ∈ S.erase l0, (1 : ℝ) := by
              rw [Finset.prod_const_one]
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
              (fun ℓ hl =>
                (hfac ℓ (Finset.mem_of_mem_erase hl)).le)
      have hsplit : (∏ ℓ ∈ S, ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2))
          = ((l0 : ℝ) - 1) / ((l0 : ℝ) - 2)
            * ∏ ℓ ∈ S.erase l0, ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) :=
        (Finset.mul_prod_erase S _ hl0).symm
      have hl0fac := hfac l0 hl0
      have hgt : (1 : ℝ)
          < ∏ ℓ ∈ S, ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) := by
        rw [hsplit]
        nlinarith [mul_le_mul_of_nonneg_left hrest
          (le_of_lt (lt_trans zero_lt_one hl0fac))]
      nlinarith [hgt, hS]
    · intro h
      rw [h, Finset.prod_empty, mul_one]

/-- `prop:phase-firewall`: a global relative phase leaves the
rank-one endpoint density matrix unchanged, yet the
relative-history distance is `‖a-b‖² = 2‖a‖²(1-cos φ)`. -/
theorem phase_firewall {ι : Type*} [Fintype ι] (a : ι → ℂ)
    (phi : ℝ) :
    Matrix.vecMulVec (fun i => Complex.exp (phi * Complex.I) * a i)
        (star fun i => Complex.exp (phi * Complex.I) * a i)
      = Matrix.vecMulVec a (star a)
      ∧ ∑ i, Complex.normSq
          (a i - Complex.exp (phi * Complex.I) * a i)
        = 2 * (1 - Real.cos phi) * ∑ i, Complex.normSq (a i) := by
  constructor
  · ext i j
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, star_mul']
    rw [show Complex.exp (phi * Complex.I) * a i
        * (star (Complex.exp (phi * Complex.I)) * star (a j))
      = (Complex.exp (phi * Complex.I)
          * star (Complex.exp (phi * Complex.I)))
        * (a i * star (a j)) from by ring]
    rw [show star (Complex.exp (phi * Complex.I))
      = Complex.exp (-(phi * Complex.I)) from by
        rw [show star (Complex.exp ((phi : ℂ) * Complex.I))
          = (starRingEnd ℂ) (Complex.exp ((phi : ℂ) * Complex.I))
          from rfl, ← Complex.exp_conj]
        congr 1
        simp]
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
      one_mul]
  · have hfac : ∀ i : ι,
        Complex.normSq (a i - Complex.exp (phi * Complex.I) * a i)
        = (2 * (1 - Real.cos phi)) * Complex.normSq (a i) := by
      intro i
      rw [show a i - Complex.exp (phi * Complex.I) * a i
        = (1 - Complex.exp (phi * Complex.I)) * a i from by ring]
      rw [Complex.normSq_mul]
      congr 1
      rw [Complex.exp_ofReal_mul_I, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      nlinarith [Real.sin_sq_add_cos_sq phi]
    simp only [hfac]
    rw [← Finset.mul_sum]


/-- The signed permutation sum vanishes for `k ≥ 2`: even and odd
histories pair and cancel. -/
theorem perm_sign_sum_eq_zero (k : ℕ) (hk : 2 ≤ k) :
    (∑ π : Equiv.Perm (Fin k), (Equiv.Perm.sign π : ℤ)) = 0 := by
  classical
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  set i : Fin k := ⟨0, h0⟩
  set j : Fin k := ⟨1, h1⟩
  have hij : i ≠ j := by
    simp [i, j, Fin.ext_iff]
  set sigma := Equiv.swap i j with hsigma
  have hsign : Equiv.Perm.sign sigma = -1 :=
    Equiv.Perm.sign_swap hij
  have hmap : (∑ π : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign (sigma * π) : ℤ)))
      = ∑ π : Equiv.Perm (Fin k), (Equiv.Perm.sign π : ℤ) :=
    Fintype.sum_bijective (Equiv.mulLeft sigma)
      (Equiv.mulLeft sigma).bijective _ _ (fun π => rfl)
  have hneg : ∀ π : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign (sigma * π) : ℤ))
        = -(Equiv.Perm.sign π : ℤ) := by
    intro π
    rw [Equiv.Perm.sign_mul, hsign]
    push_cast
    ring
  have hflip : (∑ π : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign (sigma * π) : ℤ)))
      = -∑ π : Equiv.Perm (Fin k), (Equiv.Perm.sign π : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun π _ => hneg π
  omega

/-- `thm:car-prime`: the CAR endpoint on the permutation-symmetric
ordered-history source is an exact depth filter — it returns the
target for one-step histories and annihilates every deeper
symmetric history. -/
theorem car_prime_endpoint {W : Type*} [AddCommGroup W]
    [Module ℂ W] (k : ℕ)
    (E : (Equiv.Perm (Fin k) → ℂ) →ₗ[ℂ] W) (v : W)
    (hE : ∀ π, E (Pi.single π 1)
      = ((Equiv.Perm.sign π : ℤ) : ℂ) • v) :
    (2 ≤ k → E (fun _ => 1) = 0)
      ∧ (k = 1 → E (fun _ => 1) = v) := by
  classical
  constructor
  · intro hk
    have hone : (fun _ : Equiv.Perm (Fin k) => (1 : ℂ))
        = ∑ π : Equiv.Perm (Fin k), Pi.single π 1 := by
      funext ρ
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single ρ]
      · simp
      · intro π _ hπ
        simp [hπ]
      · intro h
        exact absurd (Finset.mem_univ ρ) h
    rw [hone, map_sum]
    rw [show (∑ π : Equiv.Perm (Fin k), E (Pi.single π 1))
      = ∑ π : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign π : ℤ) : ℂ) • v from
      Finset.sum_congr rfl fun π _ => hE π]
    rw [← Finset.sum_smul]
    rw [show (∑ π : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign π : ℤ) : ℂ))
      = ((∑ π : Equiv.Perm (Fin k),
          (Equiv.Perm.sign π : ℤ) : ℤ) : ℂ) from by push_cast; rfl]
    rw [perm_sign_sum_eq_zero k hk]
    simp
  · intro hk
    subst hk
    have hone : (fun _ : Equiv.Perm (Fin 1) => (1 : ℂ))
        = Pi.single (1 : Equiv.Perm (Fin 1)) 1 := by
      funext π
      rw [Subsingleton.elim π 1]
      simp
    rw [hone, hE 1]
    simp

end NCG
