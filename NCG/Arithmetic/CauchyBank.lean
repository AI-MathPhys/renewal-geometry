/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.SignedSeparator

/-!
# The stable finite Cauchy evaluation bank
  (`thm:v003-cauchy-minorant`, arithmetic monograph)

The entire squarefree Mellin port
`𝔈_{z,X}(n) = Σ_{j≥1} B_{j,X}(n) zʲ` (the Taylor series of
`μ²(n)Π_{ℓ|n}(ℓ^{z/L}-1)`; the coefficient identity is
`NCG.mellin_degree`) is realized as the absolutely convergent series
`packetE`, and the finite root-of-unity evaluation bank
`𝔇⁽ʲ⁾ = (1/mrʲ) Σ_v ζ_m^{-jv} 𝔈_{rζ_m^v}` is aliased and dominated:

* `mellinB_abs_le` / `packet_norm_summable` — factorial decay of the
  Mellin coefficients, absolute convergence at every radius;
* `rootsum` — the exact root-of-unity filter
  `Σ_{v<m} ζ^{vk} = m·1_{m|k}`;
* `bank_alias` — the aliasing identity
  `𝔇⁽ʲ⁾ = Σ_{d≡j (m)} B_d r^{d}/r^{j}` (`eq:v003-cauchy-alias`);
* `cauchy_minorant` — the stable sandwich: with `ϑ = (r/s)^m`,
  `C_s = 1/s + 1/s²` and `𝔠 = 𝔇⁽¹⁾ + 𝔇⁽²⁾ − ϑC_s𝔈_s`,
  `0 ≤ 𝔓_{≤2} − 𝔠 ≤ ϑC_s𝔈_s` pointwise, by coefficientwise
  domination `0 ≤ 1_{d∈{1,2}} − κ_d ≤ ϑC_s s^d` against the
  nonnegative coefficients `B_d`;
* `bank_weight` — the total absolute coefficient weight of each bank
  is `r⁻ʲ`, independently of `m` (so the display total is
  `r⁻¹ + r⁻² + ϑC_s`).
-/

namespace NCG

open Finset

noncomputable section

/-! ## Coefficient bounds and absolute convergence -/

private lemma abs_moebius_le (d : ℕ) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
  by_cases hd : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hd]
    push_cast
    rw [abs_pow, abs_neg, abs_one, one_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num

private lemma lambdaJ_abs_le {n : ℕ} (_hn : 1 ≤ n) (j : ℕ) :
    |lambdaJ j n| ≤ n.divisors.card * Real.log n ^ j := by
  rw [lambdaJ]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ d ∈ n.divisors,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (Real.log n - Real.log d) ^ j| ≤ Real.log n ^ j := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdn : d ≤ n := Nat.divisor_le hd
    have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
    have hlogle : Real.log d ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast hd1) (by exact_mod_cast hdn)
    rw [abs_mul, abs_pow, abs_of_nonneg
      (show (0 : ℝ) ≤ Real.log n - Real.log d by linarith)]
    calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)|
        * (Real.log n - Real.log d) ^ j
        ≤ 1 * Real.log n ^ j := by
          refine mul_le_mul (abs_moebius_le d) ?_ (by positivity)
            zero_le_one
          exact pow_le_pow_left₀ (by linarith) (by linarith) j
    _ = Real.log n ^ j := one_mul _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- Factorial decay of the Mellin coefficients. -/
private lemma mellinB_abs_le {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n)
    (j : ℕ) :
    |mellinB L j n|
      ≤ n.divisors.card * ((Real.log n / L) ^ j / j.factorial) := by
  rw [mellinB, abs_div, abs_mul]
  have hden : |(j.factorial : ℝ) * L ^ j| = j.factorial * L ^ j := by
    rw [abs_of_pos (by positivity)]
  rw [hden]
  have hmu : |((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_moebius_le n)
  calc |((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2| * |lambdaJ j n|
      / ((j.factorial : ℝ) * L ^ j)
      ≤ 1 * (n.divisors.card * Real.log n ^ j)
        / ((j.factorial : ℝ) * L ^ j) := by
        have hnum : |((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2|
            * |lambdaJ j n|
            ≤ 1 * (n.divisors.card * Real.log n ^ j) :=
          mul_le_mul hmu (lambdaJ_abs_le hn j) (abs_nonneg _) zero_le_one
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum (by positivity)
  _ = n.divisors.card * ((Real.log n / L) ^ j / j.factorial) := by
      rw [one_mul, div_pow]
      field_simp

/-- Absolute convergence of the packet at every radius. -/
private lemma packet_norm_summable {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun j : ℕ => |mellinB L j n| * R ^ j := by
  have hsum := (Real.summable_pow_div_factorial (Real.log n / L * R)).mul_left
    (n.divisors.card : ℝ)
  refine hsum.of_nonneg_of_le
    (fun j => mul_nonneg (abs_nonneg _) (pow_nonneg hR j)) fun j => ?_
  calc |mellinB L j n| * R ^ j
      ≤ n.divisors.card * ((Real.log n / L) ^ j / j.factorial) * R ^ j := by
        exact mul_le_mul_of_nonneg_right (mellinB_abs_le hL hn j)
          (pow_nonneg hR j)
  _ = (n.divisors.card : ℝ) * ((Real.log n / L * R) ^ j / j.factorial) := by
      rw [mul_pow]
      ring

/-- Nonnegativity of the Mellin coefficients. -/
private lemma mellinB_nonneg {L : ℝ} (hL : 0 < L) (j n : ℕ) :
    0 ≤ mellinB L j n := by
  by_cases hsq : Squarefree n
  · rw [mellinB]
    refine div_nonneg (mul_nonneg (sq_nonneg _) (lambdaJ_nonneg hsq j))
      (by positivity)
  · rw [mellinB, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    norm_num

/-! ## The packet, the roots of unity, and the bank -/

/-- The entire squarefree Mellin port `𝔈_{z,X}(n)` as its absolutely
convergent Taylor series (the product display is the formal identity
`NCG.mellin_degree`). -/
def packetE (L : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' j : ℕ, (mellinB L j n : ℂ) * z ^ j

/-- The real packet `𝔈_{s,X}(n)` at a real radius. -/
def packetEs (L s : ℝ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, mellinB L j n * s ^ j

/-- The `m`-th root-of-unity power `ζ_m^t`. -/
def zetaPow (m : ℕ) (t : ℤ) : ℂ :=
  Complex.exp (((2 * Real.pi * t / m : ℝ) : ℂ) * Complex.I)

/-- The finite Cauchy evaluation bank `𝔇⁽ʲ⁾_{m,r,X}(n)`
(`eq:v003-cauchy-D`). -/
def bankD (L : ℝ) (m : ℕ) (r : ℝ) (j n : ℕ) : ℂ :=
  ((m : ℂ) * (r : ℂ) ^ j)⁻¹
    * ∑ v ∈ Finset.range m,
        zetaPow m (-(j * v)) * packetE L n ((r : ℂ) * zetaPow m v)

/-- The aliased (real) form of the bank. -/
def bankAlias (L : ℝ) (m : ℕ) (r : ℝ) (j n : ℕ) : ℝ :=
  ∑' dd : ℕ, if (m : ℤ) ∣ ((dd : ℤ) - j)
    then mellinB L dd n * r ^ dd / r ^ j else 0

private lemma zetaPow_mul_pow (m : ℕ) (v d j : ℕ) :
    zetaPow m (-(j * v)) * zetaPow m v ^ d
      = zetaPow m ((d : ℤ) - j) ^ v := by
  rw [zetaPow, zetaPow, zetaPow, ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma norm_zetaPow (m : ℕ) (t : ℤ) : ‖zetaPow m t‖ = 1 := by
  rw [zetaPow, Complex.norm_exp_ofReal_mul_I]

private lemma frac_cancel {m : ℕ} (hm : 0 < m) (x : ℝ) :
    2 * Real.pi * ((m : ℝ) * x) / m = x * (2 * Real.pi) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hmm : (m : ℝ) * ((m : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hm0
  calc 2 * Real.pi * ((m : ℝ) * x) / m
      = x * (2 * Real.pi) * ((m : ℝ) * ((m : ℝ))⁻¹) := by
        rw [div_eq_mul_inv]
        ring
  _ = x * (2 * Real.pi) := by rw [hmm, mul_one]

/-- The exact root-of-unity filter: `Σ_{v<m} ζ^{vk} = m·1_{m|k}`. -/
private lemma rootsum {m : ℕ} (hm : 0 < m) (k : ℤ) :
    (∑ v ∈ Finset.range m, zetaPow m k ^ v)
      = if (m : ℤ) ∣ k then (m : ℂ) else 0 := by
  by_cases hdvd : (m : ℤ) ∣ k
  · rw [if_pos hdvd]
    obtain ⟨t, rfl⟩ := hdvd
    have hone : zetaPow m ((m : ℤ) * t) = 1 := by
      rw [zetaPow]
      rw [show ((2 * Real.pi * (((m : ℤ) * t : ℤ) : ℝ) / m : ℝ) : ℂ)
          * Complex.I = (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        from ?_]
      · exact Complex.exp_int_mul_two_pi_mul_I t
      · rw [show (((m : ℤ) * t : ℤ) : ℝ) = (m : ℝ) * (t : ℝ) by
            push_cast; ring,
          frac_cancel hm]
        push_cast
        ring
    rw [hone]
    simp
  · rw [if_neg hdvd]
    have hne : zetaPow m k ≠ 1 := by
      intro heq
      rw [zetaPow, Complex.exp_eq_one_iff] at heq
      obtain ⟨t, ht⟩ := heq
      have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      have hcancelI : ((2 * Real.pi * k / m : ℝ) : ℂ)
          = (t : ℂ) * (2 * Real.pi) := by
        have h2 : (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
            = ((t : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
          ring
        rw [h2] at ht
        exact mul_right_cancel₀ Complex.I_ne_zero ht
      have hR : (2 * Real.pi * k / m : ℝ) = t * (2 * Real.pi) := by
        exact_mod_cast hcancelI
      have h1 : 2 * Real.pi * (k : ℝ) = t * (2 * Real.pi) * m := by
        have hmul := congrArg (· * (m : ℝ)) hR
        rwa [div_mul_cancel₀ _ hm0] at hmul
      have h2 : 2 * Real.pi * (k : ℝ)
          = 2 * Real.pi * ((t : ℝ) * m) := by
        linear_combination h1
      have hk : (k : ℝ) = (t : ℝ) * m :=
        mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h2
      have hkz : k = t * m := by exact_mod_cast hk
      exact hdvd ⟨t, by rw [hkz]; ring⟩
    have hpow : zetaPow m k ^ m = 1 := by
      rw [zetaPow, ← Complex.exp_nat_mul]
      have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      have hfr : (m : ℝ) * (2 * Real.pi * k / m)
          = (k : ℝ) * (2 * Real.pi) := by
        have := frac_cancel hm ((k : ℝ) * (2 * Real.pi)
          / (2 * Real.pi))
        calc (m : ℝ) * (2 * Real.pi * k / m)
            = 2 * Real.pi * ((m : ℝ) * (k : ℝ)) / m := by ring
        _ = (k : ℝ) * (2 * Real.pi) := frac_cancel hm (k : ℝ)
      have harg : (m : ℂ) * ((((2 * Real.pi * k / m : ℝ)) : ℂ)
          * Complex.I) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        calc (m : ℂ) * ((((2 * Real.pi * k / m : ℝ)) : ℂ) * Complex.I)
            = ((((m : ℝ) * (2 * Real.pi * k / m) : ℝ)) : ℂ)
              * Complex.I := by
              push_cast
              ring
        _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
            rw [hfr]
            push_cast
            ring
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-! ## The aliasing identity -/

private lemma packet_summable_complex {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : 1 ≤ n) (z : ℂ) :
    Summable fun j : ℕ => (mellinB L j n : ℂ) * z ^ j := by
  refine Summable.of_norm ?_
  refine (packet_norm_summable hL hn (norm_nonneg z)).congr fun j => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

private lemma alias_term_summable {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (m j : ℕ) :
    Summable fun dd : ℕ => if (m : ℤ) ∣ ((dd : ℤ) - j)
      then mellinB L dd n * r ^ dd / r ^ j else 0 := by
  refine Summable.of_norm ?_
  refine ((packet_norm_summable hL hn hr.le).mul_right
    ((r ^ j)⁻¹)).of_nonneg_of_le (fun dd => norm_nonneg _) fun dd => ?_
  rw [Real.norm_eq_abs]
  by_cases hd : (m : ℤ) ∣ ((dd : ℤ) - j)
  · rw [if_pos hd, abs_div, abs_mul, abs_of_pos (pow_pos hr j),
      abs_of_pos (pow_pos hr dd), div_eq_mul_inv]
  · rw [if_neg hd, abs_zero]
    positivity

/-- `eq:v003-cauchy-alias`: root-of-unity orthogonality aliases the
bank onto the residue class `d ≡ j (mod m)`. -/
theorem bank_alias {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n) {m : ℕ}
    (hm : 0 < m) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    bankD L m r j n = ((bankAlias L m r j n : ℝ) : ℂ) := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hrC : ((r : ℂ)) ^ j ≠ 0 :=
    pow_ne_zero j (Complex.ofReal_ne_zero.mpr hr.ne')
  rw [bankD]
  have hnode : ∀ v ∈ Finset.range m,
      zetaPow m (-(j * v)) * packetE L n ((r : ℂ) * zetaPow m v)
      = ∑' dd : ℕ, (mellinB L dd n : ℂ) * (r : ℂ) ^ dd
          * zetaPow m ((dd : ℤ) - j) ^ v := by
    intro v _
    rw [packetE, ← tsum_mul_left]
    refine tsum_congr fun dd => ?_
    rw [mul_pow, ← zetaPow_mul_pow]
    ring
  rw [Finset.sum_congr rfl hnode]
  have hvsum : ∀ v ∈ Finset.range m,
      Summable fun dd : ℕ => (mellinB L dd n : ℂ) * (r : ℂ) ^ dd
        * zetaPow m ((dd : ℤ) - j) ^ v := by
    intro v _
    refine Summable.of_norm ?_
    refine (packet_norm_summable hL hn hr.le).congr fun dd => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_zetaPow, one_pow,
      mul_one, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  rw [← Summable.tsum_finsetSum hvsum]
  have hcollapse : ∀ dd : ℕ,
      (∑ v ∈ Finset.range m, (mellinB L dd n : ℂ) * (r : ℂ) ^ dd
        * zetaPow m ((dd : ℤ) - j) ^ v)
      = (mellinB L dd n : ℂ) * (r : ℂ) ^ dd
          * (if (m : ℤ) ∣ ((dd : ℤ) - j) then (m : ℂ) else 0) := by
    intro dd
    rw [← Finset.mul_sum, rootsum hm]
  rw [tsum_congr hcollapse]
  -- push the constant and convert to the real aliased series
  have hR : ((bankAlias L m r j n : ℝ) : ℂ)
      = ∑' dd : ℕ, ((if (m : ℤ) ∣ ((dd : ℤ) - j)
          then mellinB L dd n * r ^ dd / r ^ j else 0 : ℝ) : ℂ) := by
    rw [bankAlias]
    exact Complex.ofRealCLM.map_tsum (alias_term_summable hL hn hr m j)
  rw [hR, ← tsum_mul_left]
  refine tsum_congr fun dd => ?_
  by_cases hd : (m : ℤ) ∣ ((dd : ℤ) - j)
  · rw [if_pos hd, if_pos hd]
    push_cast
    field_simp
  · rw [if_neg hd, if_neg hd]
    simp

/-! ## Coefficient domination and the stable sandwich -/

private lemma pow_tail_le {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (_hs1 : s < 1) {m : ℕ} (_hm : 3 ≤ m) {d j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j ≤ 2) (hd : 3 ≤ d) (hdvd : (m : ℤ) ∣ ((d : ℤ) - j)) :
    r ^ d / r ^ j ≤ (r / s) ^ m * (1 / s + 1 / s ^ 2) * s ^ d := by
  have hs : 0 < s := hr.trans hrs
  have hθ0 : 0 < (r / s) ^ m := by positivity
  have hθ1 : r / s < 1 := (div_lt_one hs).mpr hrs
  -- extract the positive multiple
  have hdN : m ∣ d - j := by
    have h1 : ((d - j : ℕ) : ℤ) = (d : ℤ) - j := by
      omega
    exact_mod_cast (Int.natCast_dvd_natCast (m := m) (n := d - j)).mp
      (by rw [h1]; exact hdvd)
  obtain ⟨ℓ, hℓ⟩ := hdN
  have hℓ1 : 1 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | h1
    · subst h0
      omega
    · exact h1
  -- r^{d-j} = θ^ℓ s^{d-j} ≤ θ s^{d-j}
  have hpow1 : r ^ d / r ^ j = r ^ (d - j) := by
    rw [div_eq_iff (pow_ne_zero j hr.ne'), ← pow_add]
    congr 1
    omega
  have hpow2 : r ^ (d - j) = ((r / s) ^ m) ^ ℓ * s ^ (d - j) := by
    rw [← pow_mul, ← hℓ, ← mul_pow, div_mul_cancel₀ _ hs.ne']
  have hθℓ : ((r / s) ^ m) ^ ℓ ≤ (r / s) ^ m := by
    calc ((r / s) ^ m) ^ ℓ ≤ ((r / s) ^ m) ^ 1 :=
          pow_le_pow_of_le_one hθ0.le
            (pow_le_one₀ (by positivity) hθ1.le) hℓ1
    _ = (r / s) ^ m := pow_one _
  -- s^{d-j} ≤ C_s s^d for j ∈ {1,2}
  have hCs : s ^ (d - j) ≤ (1 / s + 1 / s ^ 2) * s ^ d := by
    have e1 : s ^ (d - 1) = s ^ d / s := by
      rw [eq_div_iff hs.ne', ← pow_succ]
      congr 1
      omega
    have e2 : s ^ (d - 2) = s ^ d / s ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hs.ne'), ← pow_add]
      congr 1
      omega
    have hsplit : (1 / s + 1 / s ^ 2) * s ^ d
        = s ^ (d - 1) + s ^ (d - 2) := by
      rw [e1, e2]
      ring
    rw [hsplit]
    interval_cases j
    · nlinarith [pow_nonneg hs.le (d - 2)]
    · nlinarith [pow_nonneg hs.le (d - 1)]
  calc r ^ d / r ^ j = ((r / s) ^ m) ^ ℓ * s ^ (d - j) := by
        rw [hpow1, hpow2]
  _ ≤ (r / s) ^ m * s ^ (d - j) :=
      mul_le_mul_of_nonneg_right hθℓ (by positivity)
  _ ≤ (r / s) ^ m * ((1 / s + 1 / s ^ 2) * s ^ d) :=
      mul_le_mul_of_nonneg_left hCs hθ0.le
  _ = (r / s) ^ m * (1 / s + 1 / s ^ 2) * s ^ d := by ring

private lemma not_dvd_small {m : ℕ} (hm : 3 ≤ m) {k : ℤ}
    (hne : k ≠ 0) (hlt : k < 3) (hgt : -3 < k) : ¬ (m : ℤ) ∣ k := by
  intro h
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 := Int.le_of_dvd (by omega) (dvd_neg.mpr h)
    omega
  · have h1 := Int.le_of_dvd hpos h
    omega

/-- The coefficient domination `0 ≤ 1_{d∈{1,2}} − κ_d ≤ ϑC_s s^d`. -/
private lemma coef_cases {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hs1 : s < 1) {m : ℕ} (hm : 3 ≤ m) (d : ℕ) :
    0 ≤ ((if d = 1 then (1 : ℝ) else 0) + (if d = 2 then (1 : ℝ) else 0)
        - ((if (m : ℤ) ∣ ((d : ℤ) - 1) then r ^ d / r ^ 1 else 0)
          + (if (m : ℤ) ∣ ((d : ℤ) - 2) then r ^ d / r ^ 2 else 0)
          - (r / s) ^ m * (1 / s + 1 / s ^ 2) * s ^ d))
    ∧ ((if d = 1 then (1 : ℝ) else 0) + (if d = 2 then (1 : ℝ) else 0)
        - ((if (m : ℤ) ∣ ((d : ℤ) - 1) then r ^ d / r ^ 1 else 0)
          + (if (m : ℤ) ∣ ((d : ℤ) - 2) then r ^ d / r ^ 2 else 0)
          - (r / s) ^ m * (1 / s + 1 / s ^ 2) * s ^ d))
      ≤ (r / s) ^ m * (1 / s + 1 / s ^ 2) * s ^ d := by
  have hs : 0 < s := hr.trans hrs
  have hθC : 0 ≤ (r / s) ^ m * (1 / s + 1 / s ^ 2) * s ^ d := by
    positivity
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · interval_cases d
    · rw [if_neg (by omega), if_neg (by omega),
        if_neg (not_dvd_small hm (by norm_num) (by norm_num)
          (by norm_num)),
        if_neg (not_dvd_small hm (by norm_num) (by norm_num)
          (by norm_num))]
      constructor <;> linarith [hθC]
    · rw [if_pos (by norm_num), if_neg (by omega),
        if_pos (by norm_num : (m : ℤ) ∣ (((1 : ℕ) : ℤ) - 1)),
        if_neg (not_dvd_small hm (by norm_num) (by norm_num)
          (by norm_num)),
        pow_one, div_self hr.ne']
      constructor <;> linarith [hθC]
    · rw [if_neg (by omega), if_pos (by norm_num),
        if_neg (not_dvd_small hm (by norm_num) (by norm_num)
          (by norm_num)),
        if_pos (by norm_num : (m : ℤ) ∣ (((2 : ℕ) : ℤ) - 2)),
        div_self (pow_ne_zero 2 hr.ne')]
      constructor <;> linarith [hθC]
  · rw [if_neg (by omega), if_neg (by omega)]
    by_cases h1 : (m : ℤ) ∣ ((d : ℤ) - 1)
    · have h2 : ¬ (m : ℤ) ∣ ((d : ℤ) - 2) := by
        intro h2
        have hone : (m : ℤ) ∣ 1 := by
          have := dvd_sub h1 h2
          simpa using this
        have := Int.le_of_dvd one_pos hone
        omega
      rw [if_pos h1, if_neg h2]
      have htail := pow_tail_le hr hrs hs1 hm le_rfl (by norm_num)
        hd3 h1
      have hpos : 0 ≤ r ^ d / r ^ 1 := by positivity
      constructor <;> linarith
    · by_cases h2 : (m : ℤ) ∣ ((d : ℤ) - 2)
      · rw [if_neg h1, if_pos h2]
        have htail := pow_tail_le hr hrs hs1 hm (by norm_num) le_rfl
          hd3 h2
        have hpos : 0 ≤ r ^ d / r ^ 2 := by positivity
        constructor <;> linarith
      · rw [if_neg h1, if_neg h2]
        constructor <;> linarith [hθC]

private lemma packetEs_summable {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    Summable fun d : ℕ => mellinB L d n * s ^ d := by
  refine Summable.of_norm ?_
  refine (packet_norm_summable hL hn hs).congr fun d => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hs]

/-- `thm:v003-cauchy-minorant` (stable sandwich): with
`𝔠 = 𝔇⁽¹⁾ + 𝔇⁽²⁾ − ϑC_s𝔈_s` in aliased form,
`0 ≤ 𝔓_{≤2} − 𝔠 ≤ ϑC_s𝔈_s` pointwise, so
`𝔠 ≤ 𝔓_{≤2}` with aliasing error at most `ϑC_s𝔈_s`. -/
theorem cauchy_minorant {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n)
    {m : ℕ} (hm : 3 ≤ m) {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hs1 : s < 1) :
    0 ≤ packetPle2 L n
        - (bankAlias L m r 1 n + bankAlias L m r 2 n
          - (r / s) ^ m * (1 / s + 1 / s ^ 2) * packetEs L s n)
    ∧ packetPle2 L n
        - (bankAlias L m r 1 n + bankAlias L m r 2 n
          - (r / s) ^ m * (1 / s + 1 / s ^ 2) * packetEs L s n)
      ≤ (r / s) ^ m * (1 / s + 1 / s ^ 2) * packetEs L s n := by
  have hs : 0 < s := hr.trans hrs
  have hSs := packetEs_summable hL hn hs.le
  have hS1 := alias_term_summable hL hn hr m 1
  have hS2 := alias_term_summable hL hn hr m 2
  have hSf1 : Summable fun d : ℕ =>
      if d = 1 then mellinB L d n else 0 :=
    summable_of_ne_finset_zero (s := {1})
      (fun d hd => if_neg (by simpa using hd))
  have hSf2 : Summable fun d : ℕ =>
      if d = 2 then mellinB L d n else 0 :=
    summable_of_ne_finset_zero (s := {2})
      (fun d hd => if_neg (by simpa using hd))
  have hSh : Summable fun d : ℕ =>
      (r / s) ^ m * (1 / s + 1 / s ^ 2) * (mellinB L d n * s ^ d) :=
    hSs.mul_left _
  have e1 : packetPle2 L n
      = (∑' d : ℕ, if d = 1 then mellinB L d n else 0)
        + ∑' d : ℕ, if d = 2 then mellinB L d n else 0 := by
    rw [packetPle2, tsum_eq_single 1 (fun d hd => if_neg hd),
      if_pos rfl, tsum_eq_single 2 (fun d hd => if_neg hd), if_pos rfl]
  have e3 : (r / s) ^ m * (1 / s + 1 / s ^ 2) * packetEs L s n
      = ∑' d : ℕ, (r / s) ^ m * (1 / s + 1 / s ^ 2)
          * (mellinB L d n * s ^ d) := by
    rw [packetEs, ← tsum_mul_left]
  have hdiff : packetPle2 L n
      - (bankAlias L m r 1 n + bankAlias L m r 2 n
        - (r / s) ^ m * (1 / s + 1 / s ^ 2) * packetEs L s n)
      = ∑' d : ℕ,
          (((if d = 1 then (1 : ℝ) else 0)
            + (if d = 2 then (1 : ℝ) else 0)
            - ((if (m : ℤ) ∣ ((d : ℤ) - 1) then r ^ d / r ^ 1 else 0)
              + (if (m : ℤ) ∣ ((d : ℤ) - 2) then r ^ d / r ^ 2 else 0)
              - (r / s) ^ m * (1 / s + 1 / s ^ 2) * s ^ d))
            * mellinB L d n) := by
    rw [e1, e3, bankAlias, bankAlias,
      ← hSf1.tsum_add hSf2, ← hS1.tsum_add hS2,
      ← (hS1.add hS2).tsum_sub hSh,
      ← (hSf1.add hSf2).tsum_sub ((hS1.add hS2).sub hSh)]
    refine tsum_congr fun d => ?_
    push_cast
    split_ifs <;> ring
  have hScoef : Summable fun d : ℕ =>
      (((if d = 1 then (1 : ℝ) else 0)
        + (if d = 2 then (1 : ℝ) else 0)
        - ((if (m : ℤ) ∣ ((d : ℤ) - 1) then r ^ d / r ^ 1 else 0)
          + (if (m : ℤ) ∣ ((d : ℤ) - 2) then r ^ d / r ^ 2 else 0)
          - (r / s) ^ m * (1 / s + 1 / s ^ 2) * s ^ d))
        * mellinB L d n) := by
    refine (((hSf1.add hSf2).sub ((hS1.add hS2).sub hSh)).congr
      fun d => ?_)
    push_cast
    split_ifs <;> ring
  constructor
  · rw [hdiff]
    exact tsum_nonneg fun d =>
      mul_nonneg (coef_cases hr hrs hs1 hm d).1 (mellinB_nonneg hL d n)
  · rw [hdiff, e3]
    refine hScoef.tsum_le_tsum (fun d => ?_) hSh
    refine le_trans (mul_le_mul_of_nonneg_right
      (coef_cases hr hrs hs1 hm d).2 (mellinB_nonneg hL d n))
      (le_of_eq (by ring))

/-- `thm:v003-cauchy-minorant` (bank weight): the total absolute
coefficient weight of the `j`-th evaluation bank is `r⁻ʲ`,
independently of `m` — so the display total is
`r⁻¹ + r⁻² + ϑC_s`. -/
theorem bank_weight {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    (∑ v ∈ Finset.range m,
        ‖((m : ℂ) * (r : ℂ) ^ j)⁻¹ * zetaPow m (-(j * v))‖)
      = (r ^ j)⁻¹ := by
  have hterm : ∀ v ∈ Finset.range m,
      ‖((m : ℂ) * (r : ℂ) ^ j)⁻¹ * zetaPow m (-(j * v))‖
        = ((m : ℝ) * r ^ j)⁻¹ := by
    intro v _
    rw [norm_mul, norm_zetaPow, mul_one, norm_inv, norm_mul, norm_pow,
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_inv]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp

end

end NCG
