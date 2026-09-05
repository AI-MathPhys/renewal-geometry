/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.FiniteWeightedSchurNorm
import NCG.Grand.PsdCalculusExact

/-!
# Weighted-local inverse square roots and target-contact economy

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
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, invSqrtCoeff ij.1 * invSqrtCoeff ij.2
      = (-1) ^ k := by
  have h := Ring.add_choose_eq (r := (-(1 / 2) : ℝ)) (s := (-(1 / 2) : ℝ)) k
    (Commute.all _ _)
  have h2 : (-(1 / 2) : ℝ) + -(1 / 2) = -1 := by norm_num
  rw [h2, ringChoose_neg_one] at h
  exact h.symm

/-- Convolution of the unsigned coefficients: `∑_{i+j=k} aᵢ aⱼ = 1`. -/
theorem invSqrtAbsCoeff_convolution (k : ℕ) :
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, invSqrtAbsCoeff ij.1 * invSqrtAbsCoeff ij.2
      = 1 := by
  have hcong : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
      invSqrtAbsCoeff ij.1 * invSqrtAbsCoeff ij.2
        = (-1 : ℝ) ^ k * (invSqrtCoeff ij.1 * invSqrtCoeff ij.2) := by
    intro ij hij
    have hk : ij.1 + ij.2 = k :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hij
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
        ⊆ (Finset.range (2 * m)).biUnion Finset.HasAntidiagonal.antidiagonal := by
      intro p hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      rw [Finset.mem_biUnion]
      exact ⟨p.1 + p.2, Finset.mem_range.mpr (by omega),
        Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
    have hdisj : (↑(Finset.range (2 * m)) : Set ℕ).PairwiseDisjoint
        Finset.HasAntidiagonal.antidiagonal := by
      intro a _ b _ hab
      change Disjoint (Finset.HasAntidiagonal.antidiagonal a)
        (Finset.HasAntidiagonal.antidiagonal b)
      rw [Finset.disjoint_left]
      intro p hpa hpb
      exact hab ((Finset.HasAntidiagonal.mem_antidiagonal.mp hpa).symm.trans
        (Finset.HasAntidiagonal.mem_antidiagonal.mp hpb))
    have hbound : ∑ p ∈ Finset.range m ×ˢ Finset.range m,
        invSqrtAbsCoeff p.1 * η ^ p.1 * (invSqrtAbsCoeff p.2 * η ^ p.2)
          ≤ ∑ p ∈ (Finset.range (2 * m)).biUnion
              Finset.HasAntidiagonal.antidiagonal,
            invSqrtAbsCoeff p.1 * η ^ p.1 * (invSqrtAbsCoeff p.2 * η ^ p.2) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset fun p _ _ => ?_
      have := invSqrtAbsCoeff_nonneg p.1
      have := invSqrtAbsCoeff_nonneg p.2
      have := pow_nonneg h0 p.1
      have := pow_nonneg h0 p.2
      positivity
    have hgeom : ∑ p ∈ (Finset.range (2 * m)).biUnion
        Finset.HasAntidiagonal.antidiagonal,
        invSqrtAbsCoeff p.1 * η ^ p.1 * (invSqrtAbsCoeff p.2 * η ^ p.2)
          = ∑ k ∈ Finset.range (2 * m), η ^ k := by
      rw [Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
          invSqrtAbsCoeff ij.1 * η ^ ij.1 * (invSqrtAbsCoeff ij.2 * η ^ ij.2)
            = invSqrtAbsCoeff ij.1 * invSqrtAbsCoeff ij.2 * η ^ k := by
        intro ij hij
        have hk : ij.1 + ij.2 = k :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        rw [← hk, pow_add]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
        invSqrtAbsCoeff_convolution, one_mul]
    have htsum : ∑ k ∈ Finset.range (2 * m), η ^ k ≤ (1 - η)⁻¹ := by
      have hsum := summable_geometric_of_lt_one h0 h1
      calc ∑ k ∈ Finset.range (2 * m), η ^ k
          ≤ ∑' k : ℕ, η ^ k :=
            hsum.sum_le_tsum _ (fun k _ => pow_nonneg h0 k)
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
        exact pow_le_pow_left₀ (abs_nonneg x) hx k
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
  have hterm : ∀ k : ℕ, ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
      invSqrtCoeff ij.1 * x ^ ij.1 * (invSqrtCoeff ij.2 * x ^ ij.2)
        = (-x) ^ k := by
    intro k
    have hcong : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
        invSqrtCoeff ij.1 * x ^ ij.1 * (invSqrtCoeff ij.2 * x ^ ij.2)
          = invSqrtCoeff ij.1 * invSqrtCoeff ij.2 * x ^ k := by
      intro ij hij
      have hk : ij.1 + ij.2 = k :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [← hk, pow_add]
      ring
    rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul,
      invSqrtCoeff_convolution]
    exact (neg_pow x k).symm
  rw [tsum_congr hterm,
    tsum_geometric_of_norm_lt_one (by rwa [norm_neg, Real.norm_eq_abs]),
    sub_neg_eq_add]

/-- The series is strictly positive on `[-η, η]`: on the negative side all
terms are nonnegative, and on the positive side the alternating pairs are
nonnegative with the leading pair at least `1 - η`. -/
theorem invSqrtFn_pos {x η : ℝ} (hx : |x| ≤ η) (h1 : η < 1) :
    0 < invSqrtFn x := by
  have hsum := summable_invSqrtCoeff_mul_pow hx h1
  rcases le_total x 0 with hx0 | hx0
  · have hterm : ∀ k, 0 ≤ invSqrtCoeff k * x ^ k := by
      intro k
      have hxe : invSqrtCoeff k * x ^ k = invSqrtAbsCoeff k * (-x) ^ k := by
        rw [invSqrtCoeff_eq, neg_pow]
        ring
      rw [hxe]
      exact mul_nonneg (invSqrtAbsCoeff_nonneg k)
        (pow_nonneg (neg_nonneg.mpr hx0) k)
    have h1le : invSqrtCoeff 0 * x ^ 0 ≤ invSqrtFn x := by
      rw [invSqrtFn]
      simpa using hsum.sum_le_tsum ({0} : Finset ℕ)
        (fun j _ => hterm j)
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
      rw [invSqrtFn, ← tsum_even_add_odd heven hodd,
        heven.tsum_add hodd]
    have hpair_nonneg : ∀ m, 0 ≤ f (2 * m) + f (2 * m + 1) := by
      intro m
      have he : f (2 * m) = invSqrtAbsCoeff (2 * m) * x ^ (2 * m) := by
        have hmEven : Even (2 * m) := ⟨m, by omega⟩
        change invSqrtCoeff (2 * m) * x ^ (2 * m) =
          invSqrtAbsCoeff (2 * m) * x ^ (2 * m)
        rw [invSqrtCoeff_eq, Even.neg_one_pow hmEven, one_mul]
      have ho : f (2 * m + 1)
          = -(invSqrtAbsCoeff (2 * m + 1) * x ^ (2 * m + 1)) := by
        have hmEven : Even (2 * m) := ⟨m, by omega⟩
        change invSqrtCoeff (2 * m + 1) * x ^ (2 * m + 1) =
          -(invSqrtAbsCoeff (2 * m + 1) * x ^ (2 * m + 1))
        rw [invSqrtCoeff_eq, pow_succ, Even.neg_one_pow hmEven]
        ring
      rw [he, ho, pow_succ]
      have hmono := invSqrtAbsCoeff_succ_le (2 * m)
      have hnn1 := invSqrtAbsCoeff_nonneg (2 * m)
      have hnn2 := invSqrtAbsCoeff_nonneg (2 * m + 1)
      have hxp : (0 : ℝ) ≤ x ^ (2 * m) := pow_nonneg hx0 _
      have hcoef : invSqrtAbsCoeff (2 * m + 1) * x ≤
          invSqrtAbsCoeff (2 * m) := by
        calc
          invSqrtAbsCoeff (2 * m + 1) * x
              ≤ invSqrtAbsCoeff (2 * m + 1) * 1 :=
            mul_le_mul_of_nonneg_left hxle1.le hnn2
          _ ≤ invSqrtAbsCoeff (2 * m) := by simpa using hmono
      have hp := mul_nonneg hxp (sub_nonneg.mpr hcoef)
      nlinarith
    have hlead : 1 - x ≤ f 0 + f 1 := by
      have hf0 : f 0 = 1 := by
        simp [f]
      have hf1 : f 1 = -(invSqrtAbsCoeff 1 * x) := by
        simp [f, invSqrtCoeff_eq]
      have hle := invSqrtAbsCoeff_le_one 1
      have hnn := invSqrtAbsCoeff_nonneg 1
      rw [hf0, hf1]
      nlinarith
    have hge : f 0 + f 1 ≤ invSqrtFn x := by
      rw [hpair]
      have h0pair := hpairsum.sum_le_tsum ({0} : Finset ℕ)
        (fun j _ => hpair_nonneg j)
      simpa using h0pair
    linarith

/-! ### Matrix-valued inverse-square-root series -/

namespace MatrixSeries

open FiniteWeightedSchurNorm
open QRE
open Unitary
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

/-- Powers in the spectral calculus. -/
theorem matFun_pow_eq (E : Matrix Λ Λ ℂ) (hE : E.IsHermitian) :
    ∀ k : ℕ, matFun hE (fun x => x ^ k) = E ^ k := by
  intro k
  induction k with
  | zero =>
      simpa using Petz.matFun_one hE
  | succ k ih =>
      calc
        matFun hE (fun x => x ^ (k + 1))
            = matFun hE (fun x => x ^ k * id x) :=
          Petz.matFun_congr hE _ _ fun i => by simp [pow_succ]
        _ = matFun hE (fun x => x ^ k) * matFun hE id :=
          (matFun_mul hE _ _).symm
        _ = E ^ k * E := by rw [ih, Petz.matFun_id]
        _ = E ^ (k + 1) := by rw [pow_succ]

/-- Real scalar linearity of the finite spectral calculus. -/
theorem matFun_real_smul_local
    (E : Matrix Λ Λ ℂ) (hE : E.IsHermitian)
    (a : ℝ) (f : ℝ → ℝ) :
    matFun hE (fun x => a * f x) = a • matFun hE f := by
  unfold matFun
  have hdiag : diagonal
      (RCLike.ofReal (K := ℂ) ∘ fun i => a * f (hE.eigenvalues i)) =
      (a : ℂ) • diagonal
        (RCLike.ofReal (K := ℂ) ∘ fun i => f (hE.eigenvalues i)) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply,
        Function.comp_apply, smul_eq_mul]
      push_cast
      rfl
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hdiag, map_smul]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- A scalar multiple of a matrix power is its corresponding spectral
polynomial. -/
theorem coeff_smul_pow_eq_matFun
    (E : Matrix Λ Λ ℂ) (hE : E.IsHermitian) (a : ℝ) (k : ℕ) :
    (a : ℂ) • E ^ k = matFun hE (fun x => a * x ^ k) := by
  calc
    (a : ℂ) • E ^ k = a • E ^ k := by
      ext i j
      simp [Complex.real_smul]
    _ = a • matFun hE (fun x => x ^ k) := by
      rw [matFun_pow_eq E hE k]
    _ = matFun hE (fun x => a * x ^ k) :=
      (matFun_real_smul_local E hE a _).symm

/-- The inverse-square-root binomial series evaluated in the finite matrix
Banach algebra. -/
noncomputable def invSqrtMatrixSeries (E : Matrix Λ Λ ℂ) : Matrix Λ Λ ℂ :=
  ∑' k : ℕ, (invSqrtCoeff k : ℂ) • E ^ k

/-- The matrix binomial series converges whenever the weighted Schur norm of
the perturbation is strictly below one. -/
theorem summable_invSqrtMatrixSeries
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η) :
    Summable fun k : ℕ => (invSqrtCoeff k : ℂ) • E ^ k := by
  have hnormE : ‖E‖ ≤ η :=
    (norm_le_schurNorm μ d hμ hd0 E).trans hE
  have hsigned := summable_invSqrtCoeff_mul_pow
    (x := η) (η := η) (by simpa [abs_of_nonneg hη0]) hη1
  have hmajor : Summable fun k : ℕ => invSqrtAbsCoeff k * η ^ k := by
    have h := hsigned.norm
    simpa [Real.norm_eq_abs, abs_mul, abs_invSqrtCoeff,
      abs_pow, abs_of_nonneg hη0] using h
  refine Summable.of_norm_bounded hmajor fun k => ?_
  calc
    ‖(invSqrtCoeff k : ℂ) • E ^ k‖
        = invSqrtAbsCoeff k * ‖E ^ k‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_invSqrtCoeff]
    _ ≤ invSqrtAbsCoeff k * ‖E‖ ^ k :=
          mul_le_mul_of_nonneg_left (norm_pow_le E k)
            (invSqrtAbsCoeff_nonneg k)
    _ ≤ invSqrtAbsCoeff k * η ^ k :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg E) hnormE k)
            (invSqrtAbsCoeff_nonneg k)

/-- For a Hermitian perturbation, the convergent binomial series is exactly
the spectral functional calculus of the positive scalar branch. -/
theorem invSqrtMatrixSeries_eq_matFun
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η)
    (hHerm : E.IsHermitian) :
    invSqrtMatrixSeries E = matFun hHerm invSqrtFn := by
  let U : Matrix Λ Λ ℂ := hHerm.eigenvectorUnitary
  let D : ℕ → Matrix Λ Λ ℂ := fun k =>
    diagonal (RCLike.ofReal ∘ fun i =>
      invSqrtCoeff k * hHerm.eigenvalues i ^ k)
  let term : ℕ → Matrix Λ Λ ℂ := fun k =>
    (invSqrtCoeff k : ℂ) • E ^ k
  have hsum : Summable term := by
    simpa [term] using summable_invSqrtMatrixSeries
      μ η d hμ hd0 hη0 hη1 E hE
  have ht : ∀ k, term k = U * D k * star U := by
    intro k
    change (invSqrtCoeff k : ℂ) • E ^ k = U * D k * star U
    rw [coeff_smul_pow_eq_matFun E hHerm]
    unfold matFun
    rw [conjStarAlgAut_apply]
  have hUU : star U * U = 1 := by
    dsimp [U]
    exact star_mul_coe hHerm.eigenvectorUnitary
  have hDto : ∀ k, D k = star U * term k * U := by
    intro k
    rw [ht]
    symm
    calc
      star U * (U * D k * star U) * U =
          (star U * U) * D k * (star U * U) := by noncomm_ring
      _ = D k := by rw [hUU]; simp
  have hD : Summable D := by
    have htrans : Summable fun k => star U * term k * U :=
      (hsum.mul_left (star U)).mul_right U
    exact htrans.congr fun k => (hDto k).symm
  let evalEntry (i j : Λ) : Matrix Λ Λ ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hDsum : (∑' k, D k) =
      diagonal (RCLike.ofReal ∘ fun i =>
        invSqrtFn (hHerm.eigenvalues i)) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · have hEntry := hD.hasSum.mapL (evalEntry i i)
      change HasSum (fun k => D k i i) ((∑' k, D k) i i) at hEntry
      rw [← hEntry.tsum_eq]
      simp [D, invSqrtFn, Function.comp_apply, Complex.ofReal_tsum]
    · have hEntry := hD.hasSum.mapL (evalEntry i j)
      change HasSum (fun k => D k i j) ((∑' k, D k) i j) at hEntry
      rw [← hEntry.tsum_eq]
      simp [D, Matrix.diagonal_apply_ne _ hij]
  calc
    invSqrtMatrixSeries E
        = ∑' k, U * D k * star U := by
          rw [invSqrtMatrixSeries]
          exact tsum_congr ht
    _ = (∑' k, U * D k) * star U :=
      (hD.mul_left U).tsum_mul_right (star U)
    _ = U * (∑' k, D k) * star U := by
      rw [hD.tsum_mul_left]
    _ = matFun hHerm invSqrtFn := by
      rw [hDsum]
      unfold matFun
      rw [conjStarAlgAut_apply]

/-- The Cauchy product of the matrix binomial series is the Neumann series
for the inverse of `I + E`. -/
theorem invSqrtMatrixSeries_mul_self_eq_ringInverse
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η) :
    invSqrtMatrixSeries E * invSqrtMatrixSeries E =
      Ring.inverse (1 + E) := by
  have hsum := summable_invSqrtMatrixSeries
    μ η d hμ hd0 hη0 hη1 E hE
  have hnormE : ‖E‖ < 1 :=
    lt_of_le_of_lt ((norm_le_schurNorm μ d hμ hd0 E).trans hE) hη1
  have hconv : ∀ n : ℕ,
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        ((invSqrtCoeff ij.1 : ℂ) • E ^ ij.1) *
          ((invSqrtCoeff ij.2 : ℂ) • E ^ ij.2)
        = ((-1 : ℂ) ^ n) • E ^ n := by
    intro n
    calc
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          ((invSqrtCoeff ij.1 : ℂ) • E ^ ij.1) *
            ((invSqrtCoeff ij.2 : ℂ) • E ^ ij.2)
          = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
              ((invSqrtCoeff ij.1 * invSqrtCoeff ij.2 : ℝ) : ℂ) • E ^ n := by
            apply Finset.sum_congr rfl
            intro ij hij
            have hn : ij.1 + ij.2 = n :=
              Finset.HasAntidiagonal.mem_antidiagonal.mp hij
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, hn]
            norm_cast
      _ = (((∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
              invSqrtCoeff ij.1 * invSqrtCoeff ij.2 : ℝ) : ℂ) • E ^ n) := by
            rw [← Finset.sum_smul]
            norm_cast
      _ = ((-1 : ℂ) ^ n) • E ^ n := by
            rw [invSqrtCoeff_convolution]
            norm_cast
  rw [invSqrtMatrixSeries,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      hsum.norm hsum.norm,
    tsum_congr hconv]
  have hterm : ∀ n : ℕ, ((-1 : ℂ) ^ n) • E ^ n = (-E) ^ n := by
    intro n
    simpa using (smul_pow (-1 : ℂ) E n).symm
  rw [tsum_congr hterm, geom_series_eq_inverse (-E) (by simpa)]
  congr 1
  simp

/-- Algebraic inverse-square-root certificate for the binomial-series
operator. -/
theorem invSqrtMatrixSeries_mul_self_mul
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η) :
    invSqrtMatrixSeries E * invSqrtMatrixSeries E * (1 + E) = 1 := by
  rw [invSqrtMatrixSeries_mul_self_eq_ringInverse
    μ η d hμ hd0 hη0 hη1 E hE]
  have hu : IsUnit (1 + E) := by
    simpa only [sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one
        (x := -E) (by
          simpa using lt_of_le_of_lt
            ((norm_le_schurNorm μ d hμ hd0 E).trans hE) hη1))
  exact Ring.inverse_mul_cancel (1 + E) hu

/-- Every partial matrix sum obeys the scalar inverse-square-root majorant in
the weighted Schur norm. -/
theorem schurNorm_invSqrtMatrixPartialSum_le
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (hdiag : ∀ x, d x x = 0)
    (hη0 : 0 ≤ η) (E : Matrix Λ Λ ℂ)
    (hE : schurNorm μ d E ≤ η) (N : ℕ) :
    schurNorm μ d
        (∑ k ∈ Finset.range N, (invSqrtCoeff k : ℂ) • E ^ k)
      ≤ ∑ k ∈ Finset.range N, invSqrtAbsCoeff k * η ^ k := by
  calc
    schurNorm μ d
        (∑ k ∈ Finset.range N, (invSqrtCoeff k : ℂ) • E ^ k)
        ≤ ∑ k ∈ Finset.range N,
            schurNorm μ d ((invSqrtCoeff k : ℂ) • E ^ k) :=
      schurNorm_sum_le μ d (Finset.range N) _
    _ ≤ ∑ k ∈ Finset.range N, invSqrtAbsCoeff k * η ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        schurNorm μ d ((invSqrtCoeff k : ℂ) • E ^ k)
            ≤ ‖(invSqrtCoeff k : ℂ)‖ * schurNorm μ d (E ^ k) :=
          schurNorm_smul_le μ d _ _
        _ = invSqrtAbsCoeff k * schurNorm μ d (E ^ k) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_invSqrtCoeff]
        _ ≤ invSqrtAbsCoeff k * (schurNorm μ d E) ^ k :=
          mul_le_mul_of_nonneg_left
            (schurNorm_pow_le μ d hμ hd hdiag E k)
            (invSqrtAbsCoeff_nonneg k)
        _ ≤ invSqrtAbsCoeff k * η ^ k :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (schurNorm_nonneg μ d E) hE k)
            (invSqrtAbsCoeff_nonneg k)

/-- **Weighted-local inverse-square-root bound.**  The convergent matrix
binomial series has exactly the manuscript's Schur majorant. -/
theorem schurNorm_invSqrtMatrixSeries_le
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (hdiag : ∀ x, d x x = 0)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η) :
    schurNorm μ d (invSqrtMatrixSeries E) ≤
      (Real.sqrt (1 - η))⁻¹ := by
  have hsum := summable_invSqrtMatrixSeries
    μ η d hμ hd0 hη0 hη1 E hE
  have htMatrix : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N, (invSqrtCoeff k : ℂ) • E ^ k)
      Filter.atTop (nhds (invSqrtMatrixSeries E)) := by
    simpa [invSqrtMatrixSeries] using hsum.hasSum.tendsto_sum_nat
  have htNorm : Filter.Tendsto
      (fun N => schurNorm μ d
        (∑ k ∈ Finset.range N, (invSqrtCoeff k : ℂ) • E ^ k))
      Filter.atTop (nhds (schurNorm μ d (invSqrtMatrixSeries E))) :=
    (continuous_schurNorm μ d).continuousAt.tendsto.comp htMatrix
  apply le_of_tendsto htNorm
  filter_upwards [] with N
  exact (schurNorm_invSqrtMatrixPartialSum_le
    μ η d hμ hd hdiag hη0 E hE N).trans
       (sum_invSqrtAbsCoeff_pow_le hη0 hη1 N)

/-- Every eigenvalue of a finite Hermitian matrix is bounded in modulus by
its Euclidean operator norm.  This generic-index version is useful for word
sets, whose indexing type need not be presented as a `Fin` type. -/
theorem hermitian_eigenvalue_norm_le
    (E : Matrix Λ Λ ℂ) (hE : E.IsHermitian) (i : Λ) :
    ‖((hE.eigenvalues i : ℝ) : ℂ)‖ ≤ ‖E‖ := by
  have hmem : ((hE.eigenvalues i : ℝ) : ℂ) ∈ spectrum ℂ E := by
    rw [hE.spectrum_eq_image_range]
    exact ⟨hE.eigenvalues i, ⟨i, rfl⟩, rfl⟩
  simpa using spectrum.norm_le_norm_mul_of_mem hmem

/-- The binomial-series inverse square root is positive semidefinite. -/
theorem invSqrtMatrixSeries_posSemidef
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η)
    (hHerm : E.IsHermitian) :
    (invSqrtMatrixSeries E).PosSemidef := by
  rw [invSqrtMatrixSeries_eq_matFun
    μ η d hμ hd0 hη0 hη1 E hE hHerm]
  apply matFun_posSemidef hHerm invSqrtFn
  intro i
  apply (invSqrtFn_pos ?_ hη1).le
  have hnormE : ‖E‖ ≤ η :=
    (norm_le_schurNorm μ d hμ hd0 E).trans hE
  have hspec := hermitian_eigenvalue_norm_le E hHerm i
  have habs : |hHerm.eigenvalues i| ≤ ‖E‖ := by
    simpa [Real.norm_eq_abs] using hspec
  exact habs.trans hnormE

/-- Under the strict Schur smallness hypothesis, the series inverse square
root is positive definite. -/
theorem invSqrtMatrixSeries_posDef
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η)
    (hHerm : E.IsHermitian) :
    (invSqrtMatrixSeries E).PosDef := by
  have hpsd := invSqrtMatrixSeries_posSemidef
    μ η d hμ hd0 hη0 hη1 E hE hHerm
  apply hpsd.posDef_iff_isUnit.mpr
  apply IsUnit.of_mul_eq_one
    (invSqrtMatrixSeries E * (1 + E))
  simpa [Matrix.mul_assoc] using
    invSqrtMatrixSeries_mul_self_mul
      μ η d hμ hd0 hη0 hη1 E hE

/-- The series is the unique positive-semidefinite inverse square root
satisfying the algebraic right-inverse certificate. -/
theorem invSqrtMatrixSeries_unique_posSemidef
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E K : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η)
    (hHerm : E.IsHermitian) (hK : K.PosSemidef)
    (hKcert : K * K * (1 + E) = 1) :
    K = invSqrtMatrixSeries E := by
  let H := invSqrtMatrixSeries E
  have hHcert : H * H * (1 + E) = 1 :=
    invSqrtMatrixSeries_mul_self_mul
      μ η d hμ hd0 hη0 hη1 E hE
  have hu : IsUnit (1 + E) := by
    simpa only [sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one
        (x := -E) (by
          simpa using lt_of_le_of_lt
            ((norm_le_schurNorm μ d hμ hd0 E).trans hE) hη1))
  have hsq : K * K = H * H := by
    apply hu.mul_right_cancel
    exact hKcert.trans hHcert.symm
  have hH : H.PosSemidef :=
    invSqrtMatrixSeries_posSemidef
      μ η d hμ hd0 hη0 hη1 E hE hHerm
  have hHH : (H * H).PosSemidef := by
    have hgram := Matrix.posSemidef_conjTranspose_mul_self H
    simpa [hH.isHermitian.eq] using hgram
  have hkroot := posSemidef_sqrt_unique hHH hK hsq
  have hhroot := posSemidef_sqrt_unique hHH hH rfl
  exact hkroot.trans hhroot.symm

/-- **Quasilocal inverse square root on a supported word head.**  The
canonical positive inverse square root supplied by the binomial series has
the exact weighted-Schur bound asserted in the manuscript. -/
theorem localInverseSquareRoot
    (μ η : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (hdiag : ∀ x, d x x = 0)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (E : Matrix Λ Λ ℂ) (hE : schurNorm μ d E ≤ η)
    (hHerm : E.IsHermitian) :
    (invSqrtMatrixSeries E).PosDef ∧
      invSqrtMatrixSeries E * invSqrtMatrixSeries E * (1 + E) = 1 ∧
      schurNorm μ d (invSqrtMatrixSeries E) ≤
        (Real.sqrt (1 - η))⁻¹ := by
  exact ⟨invSqrtMatrixSeries_posDef
      μ η d hμ hd0 hη0 hη1 E hE hHerm,
    invSqrtMatrixSeries_mul_self_mul
      μ η d hμ hd0 hη0 hη1 E hE,
    schurNorm_invSqrtMatrixSeries_le
      μ η d hμ hd0 hd hdiag hη0 hη1 E hE⟩

end MatrixSeries

end WordHead

end NCG
