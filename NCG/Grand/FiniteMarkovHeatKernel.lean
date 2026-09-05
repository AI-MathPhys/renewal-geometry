/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperationalSobolevWeylExact

/-!
# Finite Markov heat kernels

This file develops the finite-dimensional uniformization facts used to turn a
weighted graph Laplacian into a positive, mass-preserving heat semigroup.  The
construction is independent of the manuscript-specific Sobolev constants.
-/

open scoped BigOperators

noncomputable section

namespace NCG

namespace Matrix

/-- Entrywise nonnegativity for a finite real matrix. -/
def EntrywiseNonnegative {ι κ : Type*} (A : Matrix ι κ ℝ) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- A row-stochastic finite real matrix. -/
def RowStochastic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  EntrywiseNonnegative A ∧ ∀ i, ∑ j, A i j = 1

theorem entrywiseNonnegative_zero {ι κ : Type*} :
    EntrywiseNonnegative (0 : Matrix ι κ ℝ) := by
  intro i j
  simp

theorem entrywiseNonnegative_one {ι : Type*} [DecidableEq ι] :
    EntrywiseNonnegative (1 : Matrix ι ι ℝ) := by
  intro i j
  change 0 ≤ if i = j then (1 : ℝ) else 0
  split_ifs <;> norm_num

theorem EntrywiseNonnegative.add
    {ι κ : Type*} {A B : Matrix ι κ ℝ}
    (hA : EntrywiseNonnegative A) (hB : EntrywiseNonnegative B) :
    EntrywiseNonnegative (A + B) := by
  intro i j
  exact add_nonneg (hA i j) (hB i j)

theorem EntrywiseNonnegative.smul
    {ι κ : Type*} {A : Matrix ι κ ℝ}
    (hA : EntrywiseNonnegative A) {a : ℝ} (ha : 0 ≤ a) :
    EntrywiseNonnegative (a • A) := by
  intro i j
  exact mul_nonneg ha (hA i j)

theorem EntrywiseNonnegative.mul
    {ι κ υ : Type*} [Fintype κ]
    {A : Matrix ι κ ℝ} {B : Matrix κ υ ℝ}
    (hA : EntrywiseNonnegative A) (hB : EntrywiseNonnegative B) :
    EntrywiseNonnegative (A * B) := by
  intro i k
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hB j k)

theorem EntrywiseNonnegative.pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : EntrywiseNonnegative A) :
    ∀ n : ℕ, EntrywiseNonnegative (A ^ n)
  | 0 => by simpa using (entrywiseNonnegative_one (ι := ι))
  | n + 1 => by
      rw [pow_succ]
      exact (hA.pow n).mul hA

theorem RowStochastic.one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    RowStochastic (1 : Matrix ι ι ℝ) := by
  refine ⟨entrywiseNonnegative_one, ?_⟩
  intro i
  change ∑ j, (if i = j then (1 : ℝ) else 0) = 1
  simp

theorem RowStochastic.mul
    {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι ℝ} (hA : RowStochastic A) (hB : RowStochastic B) :
    RowStochastic (A * B) := by
  refine ⟨hA.1.mul hB.1, ?_⟩
  intro i
  calc
    (∑ k, (A * B) i k) = ∑ k, ∑ j, A i j * B j k := by rfl
    _ = ∑ j, A i j * (∑ k, B j k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ j, A i j := by simp [hB.2]
    _ = 1 := hA.2 i

theorem RowStochastic.pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : RowStochastic A) :
    ∀ n : ℕ, RowStochastic (A ^ n)
  | 0 => by simpa using (RowStochastic.one (ι := ι))
  | n + 1 => by
      rw [pow_succ]
      exact (hA.pow n).mul hA

/-- Powers preserve an eigenvector, with the corresponding scalar power. -/
theorem pow_mulVec_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (f : ι → ℝ) (q : ℝ)
    (hf : Matrix.mulVec A f = q • f) :
    ∀ n : ℕ, Matrix.mulVec (A ^ n) f = q ^ n • f
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, ← Matrix.mulVec_mulVec, hf, Matrix.mulVec_smul,
        pow_mulVec_eigenvector A f q hf n]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [pow_succ]
      ring

/-- Reversibility with respect to a positive weight. -/
def DetailedBalance {ι : Type*} (μ : ι → ℝ) (A : Matrix ι ι ℝ) : Prop :=
  ∀ i j, μ i * A i j = μ j * A j i

theorem DetailedBalance.one
    {ι : Type*} [DecidableEq ι] (μ : ι → ℝ) :
    DetailedBalance μ (1 : Matrix ι ι ℝ) := by
  intro i j
  change μ i * (if i = j then 1 else 0) =
    μ j * (if j = i then 1 else 0)
  split_ifs with h h' <;> simp_all

theorem DetailedBalance.pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : ι → ℝ} {A : Matrix ι ι ℝ}
    (hA : DetailedBalance μ A) : ∀ n : ℕ, DetailedBalance μ (A ^ n)
  | 0 => by simpa using DetailedBalance.one μ
  | n + 1 => by
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      calc
        μ i * (∑ k, (A ^ n) i k * A k j)
            = ∑ k, (μ i * (A ^ n) i k) * A k j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _
                ring
        _ = ∑ k, (μ k * (A ^ n) k i) * A k j := by
              apply Finset.sum_congr rfl
              intro k _
              rw [hA.pow n i k]
        _ = ∑ k, μ j * (A j k * (A ^ n) k i) := by
              apply Finset.sum_congr rfl
              intro k _
              have hkj := hA k j
              calc
                μ k * (A ^ n) k i * A k j
                    = (μ k * A k j) * (A ^ n) k i := by ring
                _ = (μ j * A j k) * (A ^ n) k i := by rw [hkj]
                _ = μ j * (A j k * (A ^ n) k i) := by ring
        _ = μ j * ∑ k, A j k * (A ^ n) k i := by rw [Finset.mul_sum]
        _ = μ j * (A ^ (n + 1)) j i := by rw [pow_succ', Matrix.mul_apply]

/-- Coordinatewise exponential series of a finite matrix. -/
noncomputable def exponentialEntry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  ∑' n : ℕ, (1 / n.factorial : ℝ) * (A ^ n) i j

theorem exponentialEntry_nonnegative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : EntrywiseNonnegative A) :
    EntrywiseNonnegative (exponentialEntry A) := by
  intro i j
  unfold exponentialEntry
  apply tsum_nonneg
  intro n
  exact mul_nonneg (by positivity) (hA.pow n i j)

theorem exponentialEntry_detailedBalance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : ι → ℝ} {A : Matrix ι ι ℝ}
    (hA : DetailedBalance μ A) :
    DetailedBalance μ (exponentialEntry A) := by
  intro i j
  unfold exponentialEntry
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hn := hA.pow n i j
  calc
    μ i * (1 / n.factorial * (A ^ n) i j)
        = (1 / n.factorial) * (μ i * (A ^ n) i j) := by ring
    _ = (1 / n.factorial) * (μ j * (A ^ n) j i) := by rw [hn]
    _ = μ j * (1 / n.factorial * (A ^ n) j i) := by ring

/-- The exponential of `tK` has row sum `exp t` when `K` is stochastic. -/
theorem exponentialEntry_smul_rowSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : RowStochastic K) (t : ℝ) (i : ι) :
    ∑ j, exponentialEntry (t • K) i j = Real.exp t := by
  unfold exponentialEntry
  have hsummable (j : ι) : Summable (fun n : ℕ =>
      (1 / n.factorial : ℝ) * ((t • K) ^ n) i j) := by
    have hbound (n : ℕ) :
        ‖(1 / n.factorial : ℝ) * ((t • K) ^ n) i j‖ ≤
          |t| ^ n / n.factorial := by
      rw [smul_pow]
      change ‖(1 / n.factorial : ℝ) * (t ^ n * (K ^ n) i j)‖ ≤
        |t| ^ n / n.factorial
      have hentry := (hK.pow n).1 i j
      have hle : (K ^ n) i j ≤ 1 := by
        have hrow := (hK.pow n).2 i
        nlinarith [Finset.single_le_sum (fun k _ => (hK.pow n).1 i k)
          (Finset.mem_univ j)]
      rw [Real.norm_eq_abs]
      have hfac : 0 ≤ (n.factorial : ℝ) := by positivity
      rw [abs_mul, abs_div, abs_one, abs_of_nonneg hfac, abs_mul,
        abs_pow, abs_of_nonneg hentry]
      have hcoef : 0 ≤ |t| ^ n / (n.factorial : ℝ) := by positivity
      calc
        (1 / n.factorial : ℝ) * (|t| ^ n * (K ^ n) i j)
            = (|t| ^ n / n.factorial) * (K ^ n) i j := by ring
        _ ≤ (|t| ^ n / n.factorial) * 1 :=
          mul_le_mul_of_nonneg_left hle hcoef
        _ = |t| ^ n / n.factorial := mul_one _
    exact Summable.of_norm_bounded (Real.summable_pow_div_factorial |t|) hbound
  rw [← Summable.tsum_finsetSum (fun j _ => hsummable j)]
  simp only [smul_pow]
  change (∑' n : ℕ, ∑ j,
    (1 / n.factorial : ℝ) * (t ^ n * (K ^ n) i j)) = Real.exp t
  have hpow (n : ℕ) : ∑ j, (K ^ n) i j = 1 := (hK.pow n).2 i
  simp_rw [← Finset.mul_sum, hpow, mul_one, one_div]
  rw [Real.exp_eq_exp_ℝ, congrFun (NormedSpace.exp_eq_tsum ℝ) t]
  apply tsum_congr
  intro n
  simp only [smul_eq_mul]

/-- The coordinatewise exponential series acts on an eigenvector by the scalar
exponential.  Stochasticity supplies the uniform absolute-convergence bound
needed to exchange the finite vertex sum with the power series. -/
theorem exponentialEntry_smul_mulVec_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : RowStochastic K)
    (f : ι → ℝ) (q s : ℝ) (hs : 0 ≤ s)
    (hf : Matrix.mulVec K f = q • f) :
    Matrix.mulVec (exponentialEntry (s • K)) f = Real.exp (s * q) • f := by
  ext i
  unfold Matrix.mulVec exponentialEntry
  have hsummable (j : ι) : Summable (fun n : ℕ =>
      ((1 / n.factorial : ℝ) * ((s • K) ^ n) i j) * f j) := by
    have hbound (n : ℕ) :
        ‖((1 / n.factorial : ℝ) * ((s • K) ^ n) i j) * f j‖ ≤
        ‖f j‖ * (s ^ n / n.factorial) := by
      rw [smul_pow]
      change ‖((1 / n.factorial : ℝ) * (s ^ n * (K ^ n) i j)) * f j‖ ≤
        ‖f j‖ * (s ^ n / n.factorial)
      have hentry := (hK.pow n).1 i j
      have hle : (K ^ n) i j ≤ 1 := by
        have hrow := (hK.pow n).2 i
        nlinarith [Finset.single_le_sum (fun k _ => (hK.pow n).1 i k)
          (Finset.mem_univ j)]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_div, abs_one, abs_of_nonneg (Nat.cast_nonneg _), abs_mul,
        abs_pow, abs_of_nonneg hs, abs_of_nonneg hentry]
      have hcoef : 0 ≤ s ^ n / (n.factorial : ℝ) := by positivity
      rw [mul_comm]
      have : (1 / (n.factorial : ℝ)) * (s ^ n * (K ^ n) i j) =
          (s ^ n / n.factorial) * (K ^ n) i j := by ring
      rw [this]
      have hinner : (s ^ n / n.factorial) * (K ^ n) i j ≤
          (s ^ n / n.factorial) := by
        simpa using (mul_le_mul_of_nonneg_left hle hcoef :
          (s ^ n / n.factorial) * (K ^ n) i j ≤
            (s ^ n / n.factorial) * 1)
      exact mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    exact Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial s).mul_left ‖f j‖) hbound
  change (∑ j, (∑' n : ℕ,
      (1 / n.factorial : ℝ) * ((s • K) ^ n) i j) * f j) =
        Real.exp (s * q) * f i
  have htsum (j : ι) :
      (∑' n : ℕ, (1 / n.factorial : ℝ) * ((s • K) ^ n) i j) * f j =
        ∑' n : ℕ, ((1 / n.factorial : ℝ) * ((s • K) ^ n) i j) * f j := by
    exact (tsum_mul_right).symm
  simp_rw [htsum]
  have hinterchange :
      (∑ j, ∑' n : ℕ,
          ((1 / n.factorial : ℝ) * ((s • K) ^ n) i j) * f j) =
        ∑' n : ℕ, ∑ j,
          ((1 / n.factorial : ℝ) * ((s • K) ^ n) i j) * f j := by
    exact (Summable.tsum_finsetSum (fun j _ => hsummable j)).symm
  rw [hinterchange]
  have hpow (n : ℕ) :
      Matrix.mulVec ((s • K) ^ n) f = (s * q) ^ n • f := by
    rw [smul_pow, Matrix.smul_mulVec,
      pow_mulVec_eigenvector K f q hf n]
    ext v
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_pow]
    ring
  calc
    (∑' n : ℕ, ∑ j,
        ((1 / n.factorial : ℝ) * ((s • K) ^ n) i j) * f j) =
        ∑' n : ℕ, (1 / n.factorial : ℝ) * (s * q) ^ n * f i := by
          apply tsum_congr
          intro n
          have hn := congrFun (hpow n) i
          simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hn
          calc
            (∑ j, (1 / ↑n.factorial * ((s • K) ^ n) i j) * f j) =
                (1 / ↑n.factorial) * ∑ j, ((s • K) ^ n) i j * f j := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
            _ = (1 / ↑n.factorial) * ((s * q) ^ n * f i) := by
                  have hn' : (∑ j, ((s • K) ^ n) i j * f j) =
                      (s * q) ^ n * f i := hn
                  rw [hn']
            _ = (1 / ↑n.factorial) * (s * q) ^ n * f i := by ring
    _ = (∑' n : ℕ, (1 / n.factorial : ℝ) * (s * q) ^ n) * f i := by
          rw [tsum_mul_right]
    _ = Real.exp (s * q) * f i := by
          rw [Real.exp_eq_exp_ℝ, congrFun (NormedSpace.exp_eq_tsum ℝ) (s * q)]
          congr 1
          apply tsum_congr
          intro n
          simp only [smul_eq_mul, one_div]

/-- Uniformization: `exp(t(K-I))` is row-stochastic for every stochastic
matrix `K` and nonnegative time `t`. -/
theorem exponentialEntry_uniformized_rowStochastic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : RowStochastic K)
    (t : ℝ) (ht : 0 ≤ t) :
    RowStochastic (Real.exp (-t) • exponentialEntry (t • K)) := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact mul_nonneg (Real.exp_nonneg _) ((exponentialEntry_nonnegative
      (hK.1.smul ht)) i j)
  · intro i
    change ∑ j, Real.exp (-t) * exponentialEntry (t • K) i j = 1
    rw [← Finset.mul_sum, exponentialEntry_smul_rowSum K hK t i]
    rw [← Real.exp_add]
    norm_num

theorem exponentialEntry_uniformized_detailedBalance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (K : Matrix ι ι ℝ) (hK : DetailedBalance μ K)
    (t : ℝ) :
    DetailedBalance μ (Real.exp (-t) • exponentialEntry (t • K)) := by
  have hscaled : DetailedBalance μ (t • K) := by
    intro i j
    change μ i * (t * K i j) = μ j * (t * K j i)
    have hij := hK i j
    calc
      μ i * (t * K i j) = t * (μ i * K i j) := by ring
      _ = t * (μ j * K j i) := by rw [hij]
      _ = μ j * (t * K j i) := by ring
  have hseries := exponentialEntry_detailedBalance hscaled
  intro i j
  change μ i * (Real.exp (-t) * exponentialEntry (t • K) i j) =
    μ j * (Real.exp (-t) * exponentialEntry (t • K) j i)
  have hij := hseries i j
  calc
    μ i * (Real.exp (-t) * exponentialEntry (t • K) i j) =
        Real.exp (-t) * (μ i * exponentialEntry (t • K) i j) := by ring
    _ = Real.exp (-t) * (μ j * exponentialEntry (t • K) j i) := by rw [hij]
    _ = μ j * (Real.exp (-t) * exponentialEntry (t • K) j i) := by ring

end Matrix

end NCG
