/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Banach-algebra idempotentization below the quarter threshold

Covers `lem:idempotentization` from `manuscripts/renewal_emergence/renewal_emergence.tex`: if `E`
is an
element of a unital Banach algebra with
`δ := ‖E² − E‖ < 1/4`, there is an idempotent `P` commuting with `E`
such that

`‖P − E‖ ≤ (‖2E − 1‖/2) · ((1 − 4δ)^{-1/2} − 1)`.

Instead of the binomial series, `(1 + 4D)^{-1/2}` is produced by the
quadratically convergent Newton iteration
`Z_{n+1} = Z_n + ½ Z_n (1 − Z_n² W)`, `W := 1 + 4(E² − E)`, run
inside the commutative image of the polynomial functional calculus
`Polynomial ℝ → A` (so all commutation is automatic).  The same
iteration over the scalars with `w := 1 − 4δ` is an exact majorant
whose iterates increase to `(1 − 4δ)^{-1/2}`, which yields the sharp
binomial-series constant `α_B` without any series manipulation.
-/

namespace NCG.Upstream

open Polynomial Filter

/-! ## The scalar majorant iteration -/

/-- The scalar error sequence `e_{n+1} = 3e²/4 + e³/4`, `e₀ = 4δ`. -/
noncomputable def eSeq (δ : ℝ) : ℕ → ℝ
  | 0 => 4 * δ
  | n + 1 => 3 / 4 * eSeq δ n ^ 2 + 1 / 4 * eSeq δ n ^ 3

/-- The scalar Newton iterates `z_{n+1} = z_n(1 + e_n/2)`, `z₀ = 1`. -/
noncomputable def zSeq (δ : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => zSeq δ n * (1 + eSeq δ n / 2)

variable {δ : ℝ}

theorem eSeq_zero (δ : ℝ) : eSeq δ 0 = 4 * δ := rfl

theorem eSeq_succ (δ : ℝ) (n : ℕ) :
    eSeq δ (n + 1) = 3 / 4 * eSeq δ n ^ 2 + 1 / 4 * eSeq δ n ^ 3 :=
  rfl

theorem zSeq_zero (δ : ℝ) : zSeq δ 0 = 1 := rfl

theorem zSeq_succ (δ : ℝ) (n : ℕ) :
    zSeq δ (n + 1) = zSeq δ n * (1 + eSeq δ n / 2) := rfl

theorem eSeq_nonneg (hδ0 : 0 ≤ δ) : ∀ n, 0 ≤ eSeq δ n := by
  intro n
  induction n with
  | zero => rw [eSeq_zero]; linarith
  | succ k ih =>
    rw [eSeq_succ]
    positivity

theorem eSeq_lt_one (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 4) :
    ∀ n, eSeq δ n < 1 := by
  intro n
  induction n with
  | zero => rw [eSeq_zero]; linarith
  | succ k ih =>
    have h0 := eSeq_nonneg hδ0 k
    rw [eSeq_succ]
    nlinarith

theorem eSeq_le_pow (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 4) :
    ∀ n, eSeq δ n ≤ (4 * δ) ^ (n + 1) := by
  intro n
  induction n with
  | zero => rw [eSeq_zero, pow_one]
  | succ k ih =>
    have h0 := eSeq_nonneg hδ0 k
    have h1 := eSeq_lt_one hδ0 hδ k
    have hsq : eSeq δ (k + 1) ≤ eSeq δ k ^ 2 := by
      rw [eSeq_succ]
      nlinarith
    have hpow1 : (0 : ℝ) ≤ (4 * δ) ^ (k + 1) := by positivity
    have h2 : eSeq δ k ^ 2 ≤ ((4 * δ) ^ (k + 1)) ^ 2 := by
      have h5 := mul_le_mul ih ih h0 hpow1
      nlinarith [h5]
    have h3 : ((4 * δ) ^ (k + 1)) ^ 2 ≤ (4 * δ) ^ (k + 2) := by
      rw [← pow_mul]
      refine pow_le_pow_of_le_one (by linarith) (by linarith) ?_
      omega
    linarith

theorem zSeq_pos (hδ0 : 0 ≤ δ) : ∀ n, 0 < zSeq δ n := by
  intro n
  induction n with
  | zero => rw [zSeq_zero]; norm_num
  | succ k ih =>
    have := eSeq_nonneg hδ0 k
    rw [zSeq_succ]
    nlinarith

theorem zSeq_one_le (hδ0 : 0 ≤ δ) : ∀ n, 1 ≤ zSeq δ n := by
  intro n
  induction n with
  | zero => rw [zSeq_zero]
  | succ k ih =>
    have h0 := eSeq_nonneg hδ0 k
    have h1 := zSeq_pos hδ0 k
    rw [zSeq_succ]
    nlinarith

/-- The invariant tying the two scalar sequences to `w = 1 − 4δ`. -/
theorem zSeq_sq (δ : ℝ) :
    ∀ n, zSeq δ n ^ 2 * (1 - 4 * δ) = 1 - eSeq δ n := by
  intro n
  induction n with
  | zero => rw [zSeq_zero, eSeq_zero]; ring
  | succ k ih =>
    rw [zSeq_succ, eSeq_succ]
    linear_combination (1 + eSeq δ k / 2) ^ 2 * ih

theorem zSeq_le (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 4) (n : ℕ) :
    zSeq δ n ≤ (Real.sqrt (1 - 4 * δ))⁻¹ := by
  have hw : (0 : ℝ) < 1 - 4 * δ := by linarith
  have hzsq := zSeq_sq δ n
  have he0 := eSeq_nonneg hδ0 n
  have hz0 := zSeq_pos hδ0 n
  have hsq : zSeq δ n ^ 2 ≤ (1 - 4 * δ)⁻¹ := by
    have h1 : zSeq δ n ^ 2 * (1 - 4 * δ) ≤ 1 := by
      linarith [hzsq, he0]
    calc zSeq δ n ^ 2
        = zSeq δ n ^ 2 * (1 - 4 * δ) * (1 - 4 * δ)⁻¹ := by
          field_simp
      _ ≤ 1 * (1 - 4 * δ)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (1 - 4 * δ)⁻¹ := one_mul _
  have h1 := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hz0.le, Real.sqrt_inv] at h1
  exact h1

/-! ## The polynomial Newton iteration -/

/-- `W` as a polynomial: `1 + 4(X² − X) = (2X − 1)²`. -/
noncomputable def wPoly : Polynomial ℝ :=
  1 + Polynomial.C 4 * (Polynomial.X ^ 2 - Polynomial.X)

/-- The Newton iterates as polynomials in `E`. -/
noncomputable def zPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => zPoly n
      + Polynomial.C (1 / 2) * (zPoly n * (1 - zPoly n ^ 2 * wPoly))

/-- The polynomial error `1 − Z² W`. -/
noncomputable def erPoly (n : ℕ) : Polynomial ℝ :=
  1 - zPoly n ^ 2 * wPoly

theorem zPoly_succ_eq (n : ℕ) :
    zPoly (n + 1) = zPoly n
      + Polynomial.C (1 / 2)
        * (zPoly n * (1 - zPoly n ^ 2 * wPoly)) :=
  rfl

theorem erPoly_succ (n : ℕ) :
    erPoly (n + 1) = Polynomial.C (3 / 4) * erPoly n ^ 2
      + Polynomial.C (1 / 4) * erPoly n ^ 3 := by
  apply Polynomial.funext
  intro x
  simp only [erPoly, zPoly_succ_eq, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_one, Polynomial.eval_C]
  ring

theorem zPoly_succ_sub (n : ℕ) :
    zPoly (n + 1) - zPoly n
      = Polynomial.C (1 / 2) * (zPoly n * erPoly n) := by
  apply Polynomial.funext
  intro x
  simp only [erPoly, zPoly_succ_eq, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_one, Polynomial.eval_C]
  ring

theorem erPoly_zero :
    erPoly 0
      = Polynomial.C (-4) * (Polynomial.X ^ 2 - Polynomial.X) := by
  apply Polynomial.funext
  intro x
  simp only [erPoly, zPoly, wPoly, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem aop_sq :
    (Polynomial.C 2 * Polynomial.X - 1) ^ 2 = wPoly := by
  apply Polynomial.funext
  intro x
  simp only [wPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/-! ## The Banach-algebra iteration -/

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormOneClass A]

variable (E : A)

/-- The operator Newton iterates. -/
noncomputable def newtonZ (n : ℕ) : A := Polynomial.aeval E (zPoly n)

/-- The operator error `1 − Z_n² W`. -/
noncomputable def newtonEr (n : ℕ) : A := Polynomial.aeval E (erPoly n)

omit [CompleteSpace A] [NormOneClass A] in
theorem newtonEr_zero : newtonEr E 0 = (-4 : ℝ) • (E ^ 2 - E) := by
  unfold newtonEr
  rw [erPoly_zero, map_mul, map_sub, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C]
  rw [Algebra.smul_def]

omit [CompleteSpace A] [NormOneClass A] in
theorem newtonEr_succ (n : ℕ) :
    newtonEr E (n + 1) = (3 / 4 : ℝ) • newtonEr E n ^ 2
      + (1 / 4 : ℝ) • newtonEr E n ^ 3 := by
  unfold newtonEr
  rw [erPoly_succ, map_add, map_mul, map_mul, map_pow, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_C]
  rw [Algebra.smul_def, Algebra.smul_def]

omit [CompleteSpace A] [NormOneClass A] in
theorem newtonZ_succ_sub (n : ℕ) :
    newtonZ E (n + 1) - newtonZ E n
      = (1 / 2 : ℝ) • (newtonZ E n * newtonEr E n) := by
  unfold newtonZ newtonEr
  rw [← map_sub, zPoly_succ_sub, map_mul, map_mul,
    Polynomial.aeval_C]
  rw [Algebra.smul_def]

omit [CompleteSpace A] [NormOneClass A] in
theorem newtonZ_zero : newtonZ E 0 = 1 := by
  unfold newtonZ zPoly
  exact map_one _

omit [CompleteSpace A] [NormOneClass A] in
theorem newtonZ_sq_mul (n : ℕ) :
    newtonZ E n ^ 2 * Polynomial.aeval E wPoly
      = 1 - newtonEr E n := by
  have hpoly : zPoly n ^ 2 * wPoly = 1 - erPoly n := by
    unfold erPoly
    ring
  unfold newtonZ newtonEr
  rw [← map_pow, ← map_mul, hpoly, map_sub, map_one]

omit [CompleteSpace A] [NormOneClass A] in
theorem newton_commutes (n : ℕ) (q : Polynomial ℝ) :
    Commute (newtonZ E n) (Polynomial.aeval E q) :=
  (Commute.all (zPoly n) q).map (Polynomial.aeval E)

variable {E}

omit [CompleteSpace A] in
/-- The norm invariants: the scalar pair majorizes the operator
iteration. -/
theorem newton_bounds {δ : ℝ} (hδnorm : ‖E ^ 2 - E‖ ≤ δ)
    (hδ0 : 0 ≤ δ) :
    ∀ n, ‖newtonEr E n‖ ≤ eSeq δ n ∧ ‖newtonZ E n‖ ≤ zSeq δ n
      ∧ ‖newtonZ E n - 1‖ ≤ zSeq δ n - 1 := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [newtonEr_zero, norm_smul, Real.norm_eq_abs, eSeq_zero]
      have habs : |(-4 : ℝ)| = 4 := by norm_num
      rw [habs]
      nlinarith [hδnorm, norm_nonneg (E ^ 2 - E)]
    · rw [newtonZ_zero, norm_one, zSeq_zero]
    · rw [newtonZ_zero, sub_self, norm_zero, zSeq_zero]
      norm_num
  | succ k ih =>
    obtain ⟨ihe, ihz, ihz1⟩ := ih
    have he0 := eSeq_nonneg hδ0 k
    have hz0 := zSeq_pos hδ0 k
    have hstep : ‖newtonZ E (k + 1) - newtonZ E k‖
        ≤ zSeq δ k * eSeq δ k / 2 := by
      rw [newtonZ_succ_sub, norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have h1 : ‖newtonZ E k * newtonEr E k‖
          ≤ zSeq δ k * eSeq δ k := by
        calc ‖newtonZ E k * newtonEr E k‖
            ≤ ‖newtonZ E k‖ * ‖newtonEr E k‖ := norm_mul_le _ _
          _ ≤ zSeq δ k * eSeq δ k := by
              exact mul_le_mul ihz ihe (norm_nonneg _) hz0.le
      linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [newtonEr_succ]
      have h2 : ‖newtonEr E k ^ 2‖ ≤ eSeq δ k ^ 2 := by
        calc ‖newtonEr E k ^ 2‖ = ‖newtonEr E k * newtonEr E k‖ := by
              rw [sq]
          _ ≤ ‖newtonEr E k‖ * ‖newtonEr E k‖ := norm_mul_le _ _
          _ ≤ eSeq δ k * eSeq δ k := by
              exact mul_le_mul ihe ihe (norm_nonneg _) he0
          _ = eSeq δ k ^ 2 := (sq _).symm
      have h3 : ‖newtonEr E k ^ 3‖ ≤ eSeq δ k ^ 3 := by
        have heq3 : newtonEr E k ^ 3
            = newtonEr E k ^ 2 * newtonEr E k := by
          rw [pow_succ]
        calc ‖newtonEr E k ^ 3‖
            = ‖newtonEr E k ^ 2 * newtonEr E k‖ := by rw [heq3]
          _ ≤ ‖newtonEr E k ^ 2‖ * ‖newtonEr E k‖ := norm_mul_le _ _
          _ ≤ eSeq δ k ^ 2 * eSeq δ k := by
              refine mul_le_mul h2 ihe (norm_nonneg _) ?_
              positivity
          _ = eSeq δ k ^ 3 := by ring
      calc ‖(3 / 4 : ℝ) • newtonEr E k ^ 2
            + (1 / 4 : ℝ) • newtonEr E k ^ 3‖
          ≤ ‖(3 / 4 : ℝ) • newtonEr E k ^ 2‖
            + ‖(1 / 4 : ℝ) • newtonEr E k ^ 3‖ := norm_add_le _ _
        _ ≤ 3 / 4 * eSeq δ k ^ 2 + 1 / 4 * eSeq δ k ^ 3 := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs,
              Real.norm_eq_abs,
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4),
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
            nlinarith [h2, h3]
        _ = eSeq δ (k + 1) := by rw [eSeq_succ]
    · have h4 : ‖newtonZ E (k + 1)‖
          ≤ ‖newtonZ E k‖ + ‖newtonZ E (k + 1) - newtonZ E k‖ := by
        have := norm_add_le (newtonZ E k)
          (newtonZ E (k + 1) - newtonZ E k)
        rw [add_sub_cancel] at this
        exact this
      calc ‖newtonZ E (k + 1)‖
          ≤ zSeq δ k + zSeq δ k * eSeq δ k / 2 := by
            linarith [h4, hstep, ihz]
        _ = zSeq δ (k + 1) := by rw [zSeq_succ]; ring
    · have h5 : ‖newtonZ E (k + 1) - 1‖
          ≤ ‖newtonZ E k - 1‖
            + ‖newtonZ E (k + 1) - newtonZ E k‖ := by
        have := norm_add_le (newtonZ E k - 1)
          (newtonZ E (k + 1) - newtonZ E k)
        rw [show newtonZ E k - 1 + (newtonZ E (k + 1) - newtonZ E k)
            = newtonZ E (k + 1) - 1 from by abel] at this
        exact this
      calc ‖newtonZ E (k + 1) - 1‖
          ≤ (zSeq δ k - 1) + zSeq δ k * eSeq δ k / 2 := by
            linarith [h5, hstep, ihz1]
        _ = zSeq δ (k + 1) - 1 := by rw [zSeq_succ]; ring

/-- **Lemma `lem:idempotentization`**: below the quarter threshold
there is an idempotent commuting with `E` at binomial-series
distance. -/
theorem idempotentization {δ : ℝ} (hδnorm : ‖E ^ 2 - E‖ ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 4) :
    ∃ P : A, P * P = P ∧ P * E = E * P
      ∧ ‖P - E‖ ≤ ‖(2 : ℝ) • E - 1‖ / 2
        * ((Real.sqrt (1 - 4 * δ))⁻¹ - 1) := by
  set W : A := Polynomial.aeval E wPoly with hW_def
  set Aop : A := Polynomial.aeval E
    ((Polynomial.C 2 * Polynomial.X - 1 : Polynomial ℝ))
    with hAop_def
  have hAop_eq : Aop = (2 : ℝ) • E - 1 := by
    rw [hAop_def, map_sub, map_mul, Polynomial.aeval_C,
      Polynomial.aeval_X, map_one, Algebra.smul_def]
  have hAop_sq : Aop * Aop = W := by
    rw [hAop_def, hW_def, ← map_mul, ← sq, aop_sq]
  -- Cauchy sequence via the summable scalar increments
  have hbounds := fun n => newton_bounds hδnorm hδ0 (n := n)
  have hdist : ∀ n, dist (newtonZ E n) (newtonZ E (n + 1))
      ≤ zSeq δ (n + 1) - zSeq δ n := by
    intro n
    rw [dist_eq_norm, norm_sub_rev, newtonZ_succ_sub, norm_smul,
      Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have h1 : ‖newtonZ E n * newtonEr E n‖
        ≤ zSeq δ n * eSeq δ n :=
      le_trans (norm_mul_le _ _)
        (mul_le_mul (hbounds n).2.1 (hbounds n).1 (norm_nonneg _)
          (zSeq_pos hδ0 n).le)
    have h2 : zSeq δ (n + 1) - zSeq δ n
        = zSeq δ n * eSeq δ n / 2 := by
      rw [zSeq_succ]
      ring
    linarith
  have hsummable : Summable
      (fun n => zSeq δ (n + 1) - zSeq δ n) := by
    have hd_nonneg : ∀ n, 0 ≤ zSeq δ (n + 1) - zSeq δ n := by
      intro n
      have h1 : zSeq δ (n + 1) - zSeq δ n
          = zSeq δ n * eSeq δ n / 2 := by
        rw [zSeq_succ]
        ring
      rw [h1]
      have h2 := mul_nonneg (zSeq_pos hδ0 n).le (eSeq_nonneg hδ0 n)
      linarith
    refine summable_of_sum_range_le hd_nonneg
      (c := (Real.sqrt (1 - 4 * δ))⁻¹ - 1) ?_
    intro n
    rw [Finset.sum_range_sub (fun k => zSeq δ k)]
    have h3 := zSeq_le hδ0 hδ n
    rw [zSeq_zero]
    linarith
  have hcauchy : CauchySeq (newtonZ E) :=
    cauchySeq_of_dist_le_of_summable _ hdist hsummable
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- limit properties
  have hErLim : Tendsto (fun n => newtonEr E n) atTop (nhds 0) := by
    refine squeeze_zero_norm
      (a := fun n => (4 * δ) ^ (n + 1))
      (fun n => le_trans (hbounds n).1 (eSeq_le_pow hδ0 hδ n)) ?_
    have h4 : Tendsto (fun n : ℕ => (4 * δ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith)
        (by linarith)
    exact h4.comp (tendsto_add_atTop_nat 1)
  have hSW : S * S * W = 1 := by
    have h5 : Tendsto (fun n => newtonZ E n ^ 2 * W) atTop
        (nhds (S * S * W)) := by
      have := (hS.mul hS).mul_const W
      refine this.congr fun n => ?_
      rw [sq]
    have h6 : Tendsto (fun n => newtonZ E n ^ 2 * W) atTop
        (nhds 1) := by
      have h7 : (fun n => newtonZ E n ^ 2 * W)
          = fun n => 1 - newtonEr E n := by
        funext n
        exact newtonZ_sq_mul E n
      rw [h7]
      have := (tendsto_const_nhds (α := ℕ) (x := (1 : A))).sub hErLim
      simpa using this
    exact tendsto_nhds_unique h5 h6
  have hcommS : ∀ q : Polynomial ℝ,
      S * Polynomial.aeval E q = Polynomial.aeval E q * S := by
    intro q
    have h8 : Tendsto (fun n => newtonZ E n * Polynomial.aeval E q)
        atTop (nhds (S * Polynomial.aeval E q)) :=
      hS.mul_const _
    have h9 : Tendsto (fun n => newtonZ E n * Polynomial.aeval E q)
        atTop (nhds (Polynomial.aeval E q * S)) := by
      have h10 : (fun n => newtonZ E n * Polynomial.aeval E q)
          = fun n => Polynomial.aeval E q * newtonZ E n := by
        funext n
        exact (newton_commutes E n q).eq
      rw [h10]
      exact (tendsto_const_nhds).mul hS
    exact tendsto_nhds_unique h8 h9
  have hSE : S * E = E * S := by
    have := hcommS Polynomial.X
    rwa [Polynomial.aeval_X] at this
  have hSA : S * Aop = Aop * S := hcommS _
  have hSWc : S * W = W * S := hcommS _
  have hS1 : ‖S - 1‖ ≤ (Real.sqrt (1 - 4 * δ))⁻¹ - 1 := by
    have h11 : Tendsto (fun n => ‖newtonZ E n - 1‖) atTop
        (nhds ‖S - 1‖) := ((hS.sub tendsto_const_nhds).norm)
    refine le_of_tendsto h11 (Eventually.of_forall fun n => ?_)
    exact le_trans (hbounds n).2.2
      (by linarith [zSeq_le hδ0 hδ n])
  -- the idempotent
  set T : A := Aop * S with hT_def
  have hT_sq : T * T = 1 := by
    rw [hT_def]
    calc Aop * S * (Aop * S) = Aop * (S * Aop) * S := by
          noncomm_ring
      _ = Aop * (Aop * S) * S := by rw [hSA]
      _ = (Aop * Aop) * (S * S) := by noncomm_ring
      _ = W * (S * S) := by rw [hAop_sq]
      _ = S * S * W := by
          calc W * (S * S) = (W * S) * S := by noncomm_ring
            _ = (S * W) * S := by rw [hSWc]
            _ = S * (W * S) := by noncomm_ring
            _ = S * (S * W) := by rw [hSWc]
            _ = S * S * W := by noncomm_ring
      _ = 1 := hSW
  set P : A := (2⁻¹ : ℝ) • (1 + T) with hP_def
  have hP_idem : P * P = P := by
    rw [hP_def]
    rw [smul_mul_smul_comm]
    have h12 : (1 + T) * (1 + T) = (2 : ℝ) • (1 + T) := by
      have h13 : (1 + T) * (1 + T) = 1 + T + T + T * T := by
        noncomm_ring
      rw [h13, hT_sq]
      have h14 : (1 : A) + T + T + 1 = (2 : ℝ) • (1 + T) := by
        rw [two_smul]
        abel
      exact h14
    rw [h12, smul_smul]
    norm_num
  have hTE : T * E = E * T := by
    rw [hT_def]
    calc Aop * S * E = Aop * (S * E) := by noncomm_ring
      _ = Aop * (E * S) := by rw [hSE]
      _ = (Aop * E) * S := by noncomm_ring
      _ = (E * Aop) * S := by
          rw [show Aop * E = E * Aop from by
            rw [hAop_eq]
            noncomm_ring]
      _ = E * (Aop * S) := by noncomm_ring
  have hPE : P * E = E * P := by
    rw [hP_def, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [add_mul, mul_add, one_mul, mul_one, hTE]
  have hPdiff : P - E = (2⁻¹ : ℝ) • (Aop * (S - 1)) := by
    rw [hP_def, hT_def, hAop_eq, mul_sub, mul_one]
    module
  refine ⟨P, hP_idem, hPE, ?_⟩
  rw [hPdiff, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2⁻¹ : ℝ))]
  have h15 : ‖Aop * (S - 1)‖ ≤ ‖Aop‖ * ‖S - 1‖ := norm_mul_le _ _
  have h16 : ‖Aop‖ = ‖(2 : ℝ) • E - 1‖ := by rw [hAop_eq]
  have h17 : (0 : ℝ) ≤ (Real.sqrt (1 - 4 * δ))⁻¹ - 1 := by
    have h18 := zSeq_le hδ0 hδ 0
    rw [zSeq_zero] at h18
    linarith
  calc (2⁻¹ : ℝ) * ‖Aop * (S - 1)‖
      ≤ (2⁻¹ : ℝ) * (‖Aop‖ * ‖S - 1‖) := by linarith
    _ ≤ (2⁻¹ : ℝ) * (‖(2 : ℝ) • E - 1‖
        * ((Real.sqrt (1 - 4 * δ))⁻¹ - 1)) := by
        rw [← h16]
        have := mul_le_mul_of_nonneg_left hS1 (norm_nonneg Aop)
        nlinarith [norm_nonneg Aop]
    _ = ‖(2 : ℝ) • E - 1‖ / 2
        * ((Real.sqrt (1 - 4 * δ))⁻¹ - 1) := by ring

end Banach

end NCG.Upstream
