/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Medium-difficulty exact records, batch 10 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records:

* `thm:GTLOC-local-inverse-square-root` — quasilocal inverse square root on a
  supported word head: if the normalized reflected word Gram `G = I + E`
  satisfies `‖E‖_{μ,Sch} ≤ η < 1` in the `μ`-weighted Schur norm of the word
  support pseudometric, then the (unique positive-semidefinite) inverse square
  root `G^{-1/2}` exists and satisfies
  `‖G^{-1/2}‖_{μ,Sch} ≤ (1-η)^{-1/2}`, so the OS whitening keeps the
  exponential collar.  The proof follows the manuscript: the binomial series
  `(I+E)^{-1/2} = ∑ binom(-1/2,k) Eᵏ` converges in the weighted Schur algebra,
  the absolute values of its coefficients are those of `(1-x)^{-1/2}`, and the
  Chu–Vandermonde convolution `∑_{i+j=k} binom(-1/2,i) binom(-1/2,j) = (-1)ᵏ`
  squares the partial sums into the geometric series.
* `thm:GTLOC-target-local-contact` — target-local contact economy.

The word head is finite (`𝒲 = {W₁,…,W_N}` in the manuscript), so the
weighted Schur algebra `𝔄_μ(𝒲)` is rendered as square real matrices over a
finite index type carrying the support pseudometric; membership in
`𝔄_μ(𝒲)` is the finiteness of the weighted Schur norm, which on the finite
head is witnessed by the quantitative bound `(1-η)^{-1/2}` proved here
(stated via `(Real.sqrt (1 - η))⁻¹`).
-/

open Matrix Finset

namespace NCG

namespace WordHead

/-! ### The binomial coefficients of the inverse square root series -/

/-- The scalar coefficient `binom(-1/2, k)` of the binomial series
`(1+x)^{-1/2} = ∑ₖ binom(-1/2,k) xᵏ`. -/
noncomputable def invSqrtCoeff (k : ℕ) : ℝ := Ring.choose (-(1 / 2) : ℝ) k

/-- The unsigned coefficient `(-1)ᵏ binom(-1/2,k)`, i.e. the `k`-th
coefficient of `(1-x)^{-1/2}`. -/
noncomputable def invSqrtAbsCoeff (k : ℕ) : ℝ := (-1) ^ k * invSqrtCoeff k

/-- The one-step recurrence of the generalized binomial coefficient. -/
theorem ringChoose_succ (a : ℝ) (k : ℕ) :
    Ring.choose a (k + 1) = Ring.choose a k * (a - k) / (k + 1) := by
  have hd : (descPochhammer ℤ (k + 1)).smeval a
      = (descPochhammer ℤ k).smeval a * (a - k) := by
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_natCast]
    push_cast
    ring
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, hd, Nat.factorial_succ]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hkf : ((k.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast k.factorial_ne_zero
  rw [smul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

@[simp] theorem invSqrtCoeff_zero : invSqrtCoeff 0 = 1 := by
  rw [invSqrtCoeff, Ring.choose_zero_right]

@[simp] theorem invSqrtAbsCoeff_zero : invSqrtAbsCoeff 0 = 1 := by
  rw [invSqrtAbsCoeff, invSqrtCoeff_zero, pow_zero, one_mul]

/-- The recurrence of the unsigned coefficients:
`a_{k+1} = a_k · (2k+1)/(2k+2)`. -/
theorem invSqrtAbsCoeff_succ (k : ℕ) :
    invSqrtAbsCoeff (k + 1)
      = invSqrtAbsCoeff k * ((2 * k + 1) / (2 * k + 2)) := by
  have h := ringChoose_succ (-(1 / 2) : ℝ) k
  rw [invSqrtAbsCoeff, invSqrtAbsCoeff, invSqrtCoeff, invSqrtCoeff, h,
    pow_succ]
  have hk : ((2 : ℝ) * k + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The unsigned coefficients are nonnegative. -/
theorem invSqrtAbsCoeff_nonneg (k : ℕ) : 0 ≤ invSqrtAbsCoeff k := by
  induction k with
  | zero => rw [invSqrtAbsCoeff_zero]; norm_num
  | succ k ih =>
      rw [invSqrtAbsCoeff_succ]
      have h : (0 : ℝ) ≤ (2 * k + 1) / (2 * k + 2) := by positivity
      exact mul_nonneg ih h

/-- The unsigned coefficients decrease. -/
theorem invSqrtAbsCoeff_succ_le (k : ℕ) :
    invSqrtAbsCoeff (k + 1) ≤ invSqrtAbsCoeff k := by
  rw [invSqrtAbsCoeff_succ]
  have hfrac : ((2 * k + 1 : ℝ)) / (2 * k + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc invSqrtAbsCoeff k * ((2 * k + 1) / (2 * k + 2))
      ≤ invSqrtAbsCoeff k * 1 :=
        mul_le_mul_of_nonneg_left hfrac (invSqrtAbsCoeff_nonneg k)
    _ = invSqrtAbsCoeff k := mul_one _

/-- The unsigned coefficients are bounded by one. -/
theorem invSqrtAbsCoeff_le_one (k : ℕ) : invSqrtAbsCoeff k ≤ 1 := by
  induction k with
  | zero => rw [invSqrtAbsCoeff_zero]
  | succ k ih => exact (invSqrtAbsCoeff_succ_le k).trans ih

/-- The signed coefficient in terms of the unsigned one. -/
theorem invSqrtCoeff_eq (k : ℕ) :
    invSqrtCoeff k = (-1) ^ k * invSqrtAbsCoeff k := by
  rw [invSqrtAbsCoeff, ← mul_assoc, ← pow_add]
  rw [Even.neg_one_pow ⟨k, by ring⟩, one_mul]

/-- The absolute value of the signed coefficient is the unsigned one. -/
theorem abs_invSqrtCoeff (k : ℕ) : |invSqrtCoeff k| = invSqrtAbsCoeff k := by
  rw [invSqrtCoeff_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (invSqrtAbsCoeff_nonneg k)]

/-- `binom(-1,k) = (-1)ᵏ`. -/
theorem ringChoose_neg_one (k : ℕ) :
    Ring.choose (-1 : ℝ) k = (-1) ^ k := by
  induction k with
  | zero => rw [Ring.choose_zero_right, pow_zero]
  | succ k ih =>
      rw [ringChoose_succ, ih, pow_succ]
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring

/-- **Chu–Vandermonde convolution** of the inverse-square-root coefficients:
`∑_{i+j=k} binom(-1/2,i) binom(-1/2,j) = binom(-1,k) = (-1)ᵏ`. -/
theorem invSqrtCoeff_convolution (k : ℕ) :
    ∑ ij ∈ Finset.antidiagonal k, invSqrtCoeff ij.1 * invSqrtCoeff ij.2
      = (-1) ^ k := by
  have h := Ring.add_choose_eq (r := (-(1 / 2) : ℝ)) (s := (-(1 / 2) : ℝ)) k
    (Commute.all _ _)
  have h2 : (-(1 / 2) : ℝ) + -(1 / 2) = -1 := by norm_num
  rw [h2, ringChoose_neg_one] at h
  exact h.symm

/-- Convolution of the unsigned coefficients: `∑_{i+j=k} aᵢ aⱼ = 1`. -/
theorem invSqrtAbsCoeff_convolution (k : ℕ) :
    ∑ ij ∈ Finset.antidiagonal k, invSqrtAbsCoeff ij.1 * invSqrtAbsCoeff ij.2
      = 1 := by
  have hcong : ∀ ij ∈ Finset.antidiagonal k,
      invSqrtAbsCoeff ij.1 * invSqrtAbsCoeff ij.2
        = (-1 : ℝ) ^ k * (invSqrtCoeff ij.1 * invSqrtCoeff ij.2) := by
    intro ij hij
    have hk : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
    rw [invSqrtAbsCoeff, invSqrtAbsCoeff, ← hk, pow_add]
    ring
  rw [Finset.sum_congr rfl hcong, ← Finset.mul_sum, invSqrtCoeff_convolution,
    ← pow_add, Even.neg_one_pow ⟨k, by ring⟩]

/-- **Partial-sum bound.**  Squaring a partial sum of `∑ aₖ ηᵏ` and applying
the convolution identity dominates it by the geometric series, whence every
partial sum is at most `(1-η)^{-1/2}`. -/
theorem sum_invSqrtAbsCoeff_pow_le {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) (m : ℕ) :
    ∑ k ∈ Finset.range m, invSqrtAbsCoeff k * η ^ k
      ≤ (Real.sqrt (1 - η))⁻¹ := by
  set s := ∑ k ∈ Finset.range m, invSqrtAbsCoeff k * η ^ k with hs
  have hsnn : 0 ≤ s :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (invSqrtAbsCoeff_nonneg k) (pow_nonneg h0 k)
  have hsq : s * s ≤ (1 - η)⁻¹ := by
    have hexp : s * s = ∑ p ∈ Finset.range m ×ˢ Finset.range m,
        invSqrtAbsCoeff p.1 * η ^ p.1 * (invSqrtAbsCoeff p.2 * η ^ p.2) := by
      rw [hs, Finset.sum_mul_sum, Finset.sum_product]
    have hsubset : Finset.range m ×ˢ Finset.range m
        ⊆ (Finset.range (2 * m)).biUnion Finset.antidiagonal := by
      intro p hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      rw [Finset.mem_biUnion]
      exact ⟨p.1 + p.2, Finset.mem_range.mpr (by omega),
        Finset.mem_antidiagonal.mpr rfl⟩
    have hdisj : (↑(Finset.range (2 * m)) : Set ℕ).PairwiseDisjoint
        Finset.antidiagonal := by
      intro a _ b _ hab
      rw [Finset.disjoint_left]
      intro p hpa hpb
      exact hab ((Finset.mem_antidiagonal.mp hpa).symm.trans
        (Finset.mem_antidiagonal.mp hpb))
    have hbound : ∑ p ∈ Finset.range m ×ˢ Finset.range m,
        invSqrtAbsCoeff p.1 * η ^ p.1 * (invSqrtAbsCoeff p.2 * η ^ p.2)
          ≤ ∑ p ∈ (Finset.range (2 * m)).biUnion Finset.antidiagonal,
            invSqrtAbsCoeff p.1 * η ^ p.1 * (invSqrtAbsCoeff p.2 * η ^ p.2) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset fun p _ _ => ?_
      have := invSqrtAbsCoeff_nonneg p.1
      have := invSqrtAbsCoeff_nonneg p.2
      have := pow_nonneg h0 p.1
      have := pow_nonneg h0 p.2
      positivity
    have hgeom : ∑ p ∈ (Finset.range (2 * m)).biUnion Finset.antidiagonal,
        invSqrtAbsCoeff p.1 * η ^ p.1 * (invSqrtAbsCoeff p.2 * η ^ p.2)
          = ∑ k ∈ Finset.range (2 * m), η ^ k := by
      rw [Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hterm : ∀ ij ∈ Finset.antidiagonal k,
          invSqrtAbsCoeff ij.1 * η ^ ij.1 * (invSqrtAbsCoeff ij.2 * η ^ ij.2)
            = invSqrtAbsCoeff ij.1 * invSqrtAbsCoeff ij.2 * η ^ k := by
        intro ij hij
        have hk : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
        rw [← hk, pow_add]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
        invSqrtAbsCoeff_convolution, one_mul]
    have htsum : ∑ k ∈ Finset.range (2 * m), η ^ k ≤ (1 - η)⁻¹ := by
      have hsum := summable_geometric_of_lt_one h0 h1
      calc ∑ k ∈ Finset.range (2 * m), η ^ k
          ≤ ∑' k : ℕ, η ^ k :=
            sum_le_tsum _ (fun k _ => pow_nonneg h0 k) hsum
        _ = (1 - η)⁻¹ := tsum_geometric_of_lt_one h0 h1
    rw [hexp]
    exact hbound.trans (hgeom ▸ htsum)
  have hsqrt : s ≤ Real.sqrt ((1 - η)⁻¹) := by
    have h2 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul_self hsnn] at h2
  rwa [Real.sqrt_inv] at hsqrt

/-! ### The scalar binomial series `(1+x)^{-1/2}` on `[-η, η]` -/

/-- Summability of the coefficient series against a geometric envelope. -/
theorem summable_invSqrtCoeff_mul_pow {x η : ℝ} (hx : |x| ≤ η) (h1 : η < 1) :
    Summable fun k => invSqrtCoeff k * x ^ k := by
  have h0 : 0 ≤ η := (abs_nonneg x).trans hx
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one h0 h1)
  rw [Real.norm_eq_abs, abs_mul, abs_invSqrtCoeff, abs_pow]
  calc invSqrtAbsCoeff k * |x| ^ k
      ≤ 1 * η ^ k := by
        refine mul_le_mul (invSqrtAbsCoeff_le_one k) ?_
          (pow_nonneg (abs_nonneg x) k) zero_le_one
        exact pow_le_pow_left (abs_nonneg x) hx k
    _ = η ^ k := one_mul _

/-- The scalar inverse square root series `g(x) = ∑ₖ binom(-1/2,k) xᵏ`. -/
noncomputable def invSqrtFn (x : ℝ) : ℝ := ∑' k, invSqrtCoeff k * x ^ k

/-- The series squares to `(1+x)⁻¹` (Cauchy product plus the
Chu–Vandermonde convolution). -/
theorem invSqrtFn_mul_self {x η : ℝ} (hx : |x| ≤ η) (h1 : η < 1) :
    invSqrtFn x * invSqrtFn x = (1 + x)⁻¹ := by
  have hxlt : |x| < 1 := lt_of_le_of_lt hx h1
  have h0 : 0 ≤ η := (abs_nonneg x).trans hx
  have hnorm : Summable fun k => ‖invSqrtCoeff k * x ^ k‖ :=
    (summable_invSqrtCoeff_mul_pow hx h1).abs
  rw [invSqrtFn,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hnorm]
  have hterm : ∀ k : ℕ, ∑ ij ∈ Finset.antidiagonal k,
      invSqrtCoeff ij.1 * x ^ ij.1 * (invSqrtCoeff ij.2 * x ^ ij.2)
        = (-x) ^ k := by
    intro k
    have hcong : ∀ ij ∈ Finset.antidiagonal k,
        invSqrtCoeff ij.1 * x ^ ij.1 * (invSqrtCoeff ij.2 * x ^ ij.2)
          = invSqrtCoeff ij.1 * invSqrtCoeff ij.2 * x ^ k := by
      intro ij hij
      have hk : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
      rw [← hk, pow_add]
      ring
    rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul,
      invSqrtCoeff_convolution, neg_pow]
  rw [tsum_congr hterm,
    tsum_geometric_of_norm_lt_one (by rwa [norm_neg, Real.norm_eq_abs]),
    sub_neg_eq_add]

/-- The series is strictly positive on `[-η, η]`: on the negative side all
terms are nonnegative, and on the positive side the alternating pairs are
nonnegative with the leading pair at least `1 - η`. -/
theorem invSqrtFn_pos {x η : ℝ} (hx : |x| ≤ η) (h1 : η < 1) :
    0 < invSqrtFn x := by
  have hsum := summable_invSqrtCoeff_mul_pow hx h1
  rcases le_or_lt x 0 with hx0 | hx0
  · have hterm : ∀ k, 0 ≤ invSqrtCoeff k * x ^ k := by
      intro k
      have hxe : invSqrtCoeff k * x ^ k = invSqrtAbsCoeff k * (-x) ^ k := by
        rw [invSqrtCoeff_eq, neg_pow]
        ring
      rw [hxe]
      exact mul_nonneg (invSqrtAbsCoeff_nonneg k)
        (pow_nonneg (neg_nonneg.mpr hx0) k)
    have h1le : invSqrtCoeff 0 * x ^ 0 ≤ invSqrtFn x :=
      le_tsum hsum 0 fun j _ => hterm j
    rw [invSqrtCoeff_zero, pow_zero, mul_one] at h1le
    linarith
  · have hxle1 : x < 1 := lt_of_le_of_lt ((le_abs_self x).trans hx) h1
    set f := fun k => invSqrtCoeff k * x ^ k with hf
    have heven : Summable fun m => f (2 * m) :=
      hsum.comp_injective (mul_right_injective₀ two_ne_zero)
    have hodd : Summable fun m => f (2 * m + 1) :=
      hsum.comp_injective fun a b h => by omega
    have hpairsum : Summable fun m => f (2 * m) + f (2 * m + 1) :=
      heven.add hodd
    have hpair : invSqrtFn x = ∑' m, (f (2 * m) + f (2 * m + 1)) := by
      rw [invSqrtFn, ← tsum_even_add_odd heven hodd, tsum_add heven hodd]
    have hpair_nonneg : ∀ m, 0 ≤ f (2 * m) + f (2 * m + 1) := by
      intro m
      have he : f (2 * m) = invSqrtAbsCoeff (2 * m) * x ^ (2 * m) := by
        rw [hf, invSqrtCoeff_eq, Even.neg_one_pow ⟨m, by ring⟩, one_mul]
      have ho : f (2 * m + 1)
          = -(invSqrtAbsCoeff (2 * m + 1) * x ^ (2 * m + 1)) := by
        rw [hf, invSqrtCoeff_eq, pow_succ, Even.neg_one_pow ⟨m, by ring⟩]
        ring
      rw [he, ho, pow_succ]
      have hmono := invSqrtAbsCoeff_succ_le (2 * m)
      have hnn1 := invSqrtAbsCoeff_nonneg (2 * m)
      have hnn2 := invSqrtAbsCoeff_nonneg (2 * m + 1)
      have hxp : (0 : ℝ) ≤ x ^ (2 * m) := pow_nonneg hx0.le _
      nlinarith
    have hlead : 1 - x ≤ f 0 + f 1 := by
      have hf0 : f 0 = 1 := by
        rw [hf, invSqrtCoeff_zero, pow_zero, mul_one]
      have hf1 : f 1 = -(invSqrtAbsCoeff 1 * x) := by
        rw [hf, invSqrtCoeff_eq, pow_one, pow_one]
        ring
      have hle := invSqrtAbsCoeff_le_one 1
      have hnn := invSqrtAbsCoeff_nonneg 1
      rw [hf0, hf1]
      nlinarith
    have hge : f 0 + f 1 ≤ invSqrtFn x := by
      rw [hpair]
      have h0pair := le_tsum hpairsum 0 fun j _ => hpair_nonneg j
      simpa using h0pair
    linarith

end WordHead

end NCG
