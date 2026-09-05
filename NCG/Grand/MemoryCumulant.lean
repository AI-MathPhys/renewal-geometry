/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Complete classical–quantum cut-memory short
  (`thm:renewal-memory-cumulant`, Gran-Tensor manuscript)

* `memory_normalization`: `M_cq(0) = 0` — with a faithful
  probability weight the log-partition normalizes exactly,
  `log(Σ_ω exp(log p_ω)) = 0`;
* `classical_variance_nonneg` / `classical_variance_zero_iff`:
  the classical summand of the boxed Hessian is the branch-slope
  variance `Σ p_ω (m_ω - m̄)²` — nonnegative, and zero exactly
  when all branch mean slopes agree;
* `bkm_kernel_nonneg` / `bkm_kernel_zero_iff`: the quantum
  summand in the eigenbasis rendering — the BKM double sum
  `Σ_{ij} λᵢ^s λⱼ^{1-s} |X̃ᵢⱼ|²` is nonnegative, and for a
  faithful branch (`λ > 0`) it vanishes exactly when the
  centered perturbation is zero on the support (scalar
  perturbation).

Rendering disclosed: the trace-exponential second derivative
identity `D²M_cq(0) = variance + ∫₀¹ BKM ds` (the Duhamel
expansion, as in the proved BKM Hessian layer) and the
subtraction clause `A_sh = A_coarse - M_cq` are the manuscript's
operator layer; the normalization, both positivity statements,
and both vanishing characterizations are proved here.
-/

namespace NCG

variable {ι : Type*} [Fintype ι]

/-- `M_cq(0) = 0`: the log-partition of a faithful probability
weight normalizes exactly. -/
theorem memory_normalization (p : ι → ℝ) (hp : ∀ ω, 0 < p ω)
    (hsum : ∑ ω, p ω = 1) :
    Real.log (∑ ω, Real.exp (Real.log (p ω))) = 0 := by
  have hcong : ∑ ω, Real.exp (Real.log (p ω)) = ∑ ω, p ω :=
    Finset.sum_congr rfl fun ω _ => Real.exp_log (hp ω)
  rw [hcong, hsum, Real.log_one]

/-- Classical summand: the branch-slope variance is
nonnegative. -/
theorem classical_variance_nonneg (p m : ι → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (mbar : ℝ) :
    0 ≤ ∑ ω, p ω * (m ω - mbar) ^ 2 :=
  Finset.sum_nonneg fun ω _ =>
    mul_nonneg (hp ω) (sq_nonneg _)

/-- Classical summand vanishing: with strictly positive branch
weights, the variance vanishes exactly when every branch mean
slope agrees with the average. -/
theorem classical_variance_zero_iff (p m : ι → ℝ)
    (hp : ∀ ω, 0 < p ω) (mbar : ℝ) :
    (∑ ω, p ω * (m ω - mbar) ^ 2 = 0) ↔ ∀ ω, m ω = mbar := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun ω _ =>
    mul_nonneg (hp ω).le (sq_nonneg _)]
  constructor
  · intro h ω
    have hω := h ω (Finset.mem_univ ω)
    have h2 : (m ω - mbar) ^ 2 = 0 :=
      (mul_eq_zero.mp hω).resolve_left (hp ω).ne'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith [this]
  · intro h ω _
    rw [h ω]
    ring

/-- Quantum summand (eigenbasis rendering): the BKM double sum
is nonnegative. -/
theorem bkm_kernel_nonneg (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (s : ℝ) (X : ι → ι → ℂ) :
    0 ≤ ∑ i, ∑ j,
      lam i ^ s * lam j ^ (1 - s) * ‖X i j‖ ^ 2 := by
  refine Finset.sum_nonneg fun i _ => ?_
  refine Finset.sum_nonneg fun j _ => ?_
  have h1 : 0 ≤ lam i ^ s := Real.rpow_nonneg (hlam i) s
  have h2 : 0 ≤ lam j ^ (1 - s) :=
    Real.rpow_nonneg (hlam j) (1 - s)
  positivity

/-- Quantum summand vanishing: for a faithful branch (`λ > 0`),
the BKM sum vanishes exactly when the centered perturbation is
zero on the support. -/
theorem bkm_kernel_zero_iff (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (s : ℝ) (X : ι → ι → ℂ) :
    (∑ i, ∑ j,
        lam i ^ s * lam j ^ (1 - s) * ‖X i j‖ ^ 2 = 0)
      ↔ ∀ i j, X i j = 0 := by
  have hnn : ∀ i ∈ Finset.univ, (0 : ℝ)
      ≤ ∑ j, lam i ^ s * lam j ^ (1 - s) * ‖X i j‖ ^ 2 :=
    fun i _ => Finset.sum_nonneg fun j _ => by
      have h1 : 0 ≤ lam i ^ s := Real.rpow_nonneg (hlam i).le s
      have h2 : 0 ≤ lam j ^ (1 - s) :=
        Real.rpow_nonneg (hlam j).le (1 - s)
      positivity
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h i j
    have hi := h i (Finset.mem_univ i)
    have hj : ∀ j ∈ Finset.univ,
        (0 : ℝ) ≤ lam i ^ s * lam j ^ (1 - s) * ‖X i j‖ ^ 2 :=
      fun j _ => by
        have h1 : 0 ≤ lam i ^ s := Real.rpow_nonneg (hlam i).le s
        have h2 : 0 ≤ lam j ^ (1 - s) :=
          Real.rpow_nonneg (hlam j).le (1 - s)
        positivity
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hj).mp hi j
      (Finset.mem_univ j)
    have hk1 : (0 : ℝ) < lam i ^ s :=
      Real.rpow_pos_of_pos (hlam i) s
    have hk2 : (0 : ℝ) < lam j ^ (1 - s) :=
      Real.rpow_pos_of_pos (hlam j) (1 - s)
    have hnorm : ‖X i j‖ ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ‖X i j‖ ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have := mul_pos (mul_pos hk1 hk2) hpos
      linarith [hterm]
    have : ‖X i j‖ = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num)
        |>.mp hnorm
      exact this
    exact norm_eq_zero.mp this
  · intro h i _
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h i j]
    simp

end NCG
