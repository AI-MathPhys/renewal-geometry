/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TwoStateRenewal

/-!
# Exact EASY batch 11: two-state renewal decay
-/

open Matrix

namespace NCG

/-- Total variation of a signed two-state row vector. -/
noncomputable def tvTwo (x : Fin 2 → ℝ) : ℝ :=
  (|x 0| + |x 1|) / 2

theorem tvTwo_smul (c : ℝ) (x : Fin 2 → ℝ) :
    tvTwo (c • x) = |c| * tvTwo x := by
  simp only [tvTwo, Pi.smul_apply, smul_eq_mul, abs_mul]
  ring

/-- Every zero-mass signed row law is the contrast eigenspace. -/
theorem renM0_row_contrast (x : Fin 2 → ℝ)
    (hsum : x 0 + x 1 = 0) :
    x ᵥ* renM0 = (-7 / 15 : ℝ) • x := by
  funext i
  fin_cases i <;>
    simp [renM0, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    linarith

/-- Exact propagation of every signed two-state contrast. -/
theorem renM0_row_contrast_power (x : Fin 2 → ℝ)
    (hsum : x 0 + x 1 = 0) (n : ℕ) :
    x ᵥ* (renM0 ^ n) = (-7 / 15 : ℝ) ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, ih,
        Matrix.smul_vecMul, renM0_row_contrast x hsum,
        smul_smul, pow_succ]

/-- Exact total-variation contraction for arbitrary normalized
two-state laws. -/
theorem renM0_tv_exact (μ ν : Fin 2 → ℝ)
    (hμ : μ 0 + μ 1 = 1) (hν : ν 0 + ν 1 = 1) (n : ℕ) :
    tvTwo (μ ᵥ* (renM0 ^ n) - ν ᵥ* (renM0 ^ n))
      = (7 / 15 : ℝ) ^ n * tvTwo (μ - ν) := by
  have hsum : (μ - ν) 0 + (μ - ν) 1 = 0 := by
    simp only [Pi.sub_apply]
    linarith
  have hdiff : μ ᵥ* (renM0 ^ n) - ν ᵥ* (renM0 ^ n)
      = (μ - ν) ᵥ* (renM0 ^ n) := by
    rw [Matrix.sub_vecMul]
  rw [hdiff, renM0_row_contrast_power (μ - ν) hsum n,
    tvTwo_smul, abs_pow]
  norm_num [abs_of_nonneg]

/-- Every stationary-mean-zero observable is the nontrivial
right eigenspace. -/
theorem renM0_column_contrast (f : Fin 2 → ℝ)
    (hmean : 5 * f 0 + 6 * f 1 = 0) :
    renM0 *ᵥ f = (-7 / 15 : ℝ) • f := by
  funext i
  fin_cases i <;>
    simp [renM0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    linarith

/-- Exact `L²(π)`-sector decay; since the mean-zero sector is
one dimensional, the equality holds for any norm. -/
theorem renM0_column_contrast_power (f : Fin 2 → ℝ)
    (hmean : 5 * f 0 + 6 * f 1 = 0) (n : ℕ) :
    (renM0 ^ n) *ᵥ f = (-7 / 15 : ℝ) ^ n • f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec,
        renM0_column_contrast f hmean, Matrix.mulVec_smul, ih,
        smul_smul, pow_succ]
      match_scalars
      ring

theorem renM0_column_norm_exact (f : Fin 2 → ℝ)
    (hmean : 5 * f 0 + 6 * f 1 = 0) (n : ℕ) :
    ‖(renM0 ^ n) *ᵥ f‖ = (7 / 15 : ℝ) ^ n * ‖f‖ := by
  rw [renM0_column_contrast_power f hmean n, norm_smul,
    Real.norm_eq_abs, abs_pow]
  norm_num [abs_of_nonneg]

/-- The stationary weight conditioning and completed-boundary
flux are the claimed exact scalars. -/
theorem renM0_condition_flux :
    (6 / 11 : ℝ) / (5 / 11) = 6 / 5
      ∧ (5 / 11 : ℝ) * (4 / 5) = 4 / 11
      ∧ (6 / 11 : ℝ) * (2 / 3) = 4 / 11 := by
  norm_num

/-- The two displayed eigenvectors are independent, certifying
that the active predictive carrier has dimension exactly two. -/
theorem renM0_eigenbasis_det :
    (!![1, 6; 1, -5] : Matrix (Fin 2) (Fin 2) ℝ).det = -11 := by
  rw [Matrix.det_fin_two]
  norm_num

/-- `thm:two-state-active-renewal`, combining the original
first-return/stationarity/spectrum calculation with exact decay,
conditioning, flux, and two-dimensionality certificates. -/
theorem two_state_active_renewal_exact :
    (renM0 = renQ0 + Matrix.vecMulVec ![0, 2/3] ![1, 0])
    ∧ (∀ z : ℝ, z ≠ 5 → z ≠ 3 →
        z * (![1, 0] ⬝ᵥ ((1 - z • renQ0)⁻¹ *ᵥ ![0, 2/3]))
          = 8 * z ^ 2 / ((5 - z) * (3 - z)))
    ∧ (![5/11, 6/11] ᵥ* renM0 = ![5/11, 6/11])
    ∧ ((5/11 : ℝ) * renM0 0 1 = (6/11 : ℝ) * renM0 1 0)
    ∧ (renM0 *ᵥ ![1, 1] = ![1, 1])
    ∧ (renM0 *ᵥ ![6, -5] = (-7/15 : ℝ) • ![6, -5])
    ∧ (∀ μ ν : Fin 2 → ℝ,
        μ 0 + μ 1 = 1 → ν 0 + ν 1 = 1 → ∀ n,
        tvTwo (μ ᵥ* (renM0 ^ n) - ν ᵥ* (renM0 ^ n))
          = (7/15 : ℝ)^n * tvTwo (μ - ν))
    ∧ (∀ f : Fin 2 → ℝ, 5 * f 0 + 6 * f 1 = 0 → ∀ n,
        ‖(renM0 ^ n) *ᵥ f‖ = (7/15 : ℝ)^n * ‖f‖)
    ∧ ((6/11 : ℝ) / (5/11) = 6/5)
    ∧ ((5/11 : ℝ) * (4/5) = 4/11)
    ∧ ((!![1, 6; 1, -5] : Matrix (Fin 2) (Fin 2) ℝ).det = -11) := by
  have hbase := two_state_active_renewal
  refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1,
    hbase.2.2.2.2.1, hbase.2.2.2.2.2, ?_, ?_,
    renM0_condition_flux.1, renM0_condition_flux.2.1,
    renM0_eigenbasis_det⟩
  · intro μ ν hμ hν n
    exact renM0_tv_exact μ ν hμ hν n
  · intro f hf n
    exact renM0_column_norm_exact f hf n

end NCG
