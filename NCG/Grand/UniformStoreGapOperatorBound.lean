/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniformStoreGap
import NCG.Grand.ScoreDwellSpectralAssembly

/-!
# Uniform operator gap for exponential Store dwell

This composes the exact score--dwell Hilbert--Schmidt spectral norm identity
with the exponential-dwell multiplier estimate.  It supplies the boxed
operator inequality of `cor:uniform-store-gap`, including the zeroth power.
-/

namespace NCG

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Complex multiplier of an exponential dwell law. -/
noncomputable def exponentialDwellMultiplier (lam omega : ℝ) : ℂ :=
  (lam ^ 2 / (lam ^ 2 + omega ^ 2) : ℝ)

@[simp]
theorem exponentialDwellMultiplier_zero (lam : ℝ) (hlam : lam ≠ 0) :
    exponentialDwellMultiplier lam 0 = 1 := by
  simp [exponentialDwellMultiplier, hlam]

/-- Every transient exponential-dwell multiplier is bounded by the uniform
cutoff factor `1 - gamma₀`. -/
theorem exponentialDwellMultiplier_norm_le_uniform
    (lam lam1 omega d0 : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ lam1) (hd0 : 0 < d0)
    (homega : d0 ≤ |omega|) :
    ‖exponentialDwellMultiplier lam omega‖ ≤
      1 - d0 ^ 2 / (lam1 ^ 2 + d0 ^ 2) := by
  have hscalar := (uniform_store_gap lam lam1 omega d0
    hlam hlam1 hd0 homega).1
  have hnonneg : 0 ≤ lam ^ 2 / (lam ^ 2 + omega ^ 2) := by positivity
  have hnorm :
      ‖((lam ^ 2 / (lam ^ 2 + omega ^ 2) : ℝ) : ℂ)‖ =
        lam ^ 2 / (lam ^ 2 + omega ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [exponentialDwellMultiplier, hnorm]
  calc
    lam ^ 2 / (lam ^ 2 + omega ^ 2)
        ≤ lam1 ^ 2 / (lam1 ^ 2 + d0 ^ 2) := hscalar
    _ = 1 - d0 ^ 2 / (lam1 ^ 2 + d0 ^ 2) :=
      (uniform_store_gap lam lam1 omega d0
        hlam hlam1 hd0 homega).2.1.symm

/-- Exact boxed uniform cutoff gap.  `frequency` lists the spectral
frequencies of all orthogonal score--dwell modes; retained modes have
frequency zero, while every transient mode has magnitude at least `d0`. -/
theorem uniform_store_gap_operator_bound
    {mode : Type*} [Fintype mode] [DecidableEq mode] [Nonempty mode]
    (retained : mode → Bool) (frequency : mode → ℝ)
    (lam lam1 d0 : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ lam1) (hd0 : 0 < d0)
    (hretained : ∀ i, retained i = true → frequency i = 0)
    (htransient : ∀ i, retained i = false → d0 ≤ |frequency i|)
    (n : ℕ) :
    ‖scoreDwellDiagonalEvolution
          (fun i => exponentialDwellMultiplier lam (frequency i)) ^ n -
        scoreDwellRetainedExpectation retained‖ ≤
      (1 - d0 ^ 2 / (lam1 ^ 2 + d0 ^ 2)) ^ n := by
  let q : ℝ := 1 - d0 ^ 2 / (lam1 ^ 2 + d0 ^ 2)
  have hlam1p : 0 < lam1 := lt_of_lt_of_le hlam hlam1
  have hq0 : 0 ≤ q := by
    dsimp [q]
    rw [(uniform_store_gap lam lam1 d0 d0 hlam hlam1 hd0
      (le_abs_self d0)).2.1]
    positivity
  have hone : ∀ i, retained i = true →
      exponentialDwellMultiplier lam (frequency i) = 1 := by
    intro i hi
    rw [hretained i hi]
    exact exponentialDwellMultiplier_zero lam hlam.ne'
  cases n with
  | zero =>
      have hmatrix :
          (scoreDwellDiagonalEvolution
              (fun i => exponentialDwellMultiplier lam (frequency i))) ^ 0 -
              scoreDwellRetainedExpectation retained =
            Matrix.diagonal
              (fun i => if retained i then (0 : ℂ) else 1) := by
        ext i j
        by_cases hij : i = j
        · subst j
          by_cases hi : retained i = true <;>
            simp [scoreDwellRetainedExpectation, hi]
        · simp [scoreDwellRetainedExpectation, Matrix.one_apply, hij,
            Matrix.diagonal_apply_ne _ hij]
      rw [hmatrix, Matrix.l2_opNorm_diagonal]
      have hfun : ‖(fun i => if retained i then (0 : ℂ) else 1)‖ ≤
          (1 : ℝ) := by
        rw [pi_norm_le_iff_of_nonneg (by norm_num)]
        intro i
        by_cases hi : retained i = true <;> simp [hi]
      simpa using hfun
  | succ k =>
      have hexact := scoreDwell_power_distance_exact retained
        (fun i => exponentialDwellMultiplier lam (frequency i))
        hone (k + 1) (Nat.succ_pos k)
      rw [hexact]
      have hrho :
          ‖scoreDwellResidualMultiplier retained
              (fun i => exponentialDwellMultiplier lam (frequency i))‖ ≤ q := by
        rw [pi_norm_le_iff_of_nonneg hq0]
        intro i
        cases hi : retained i
        · simpa [scoreDwellResidualMultiplier, hi, q] using
            exponentialDwellMultiplier_norm_le_uniform
              lam lam1 (frequency i) d0 hlam hlam1 hd0
              (htransient i hi)
        · simp [scoreDwellResidualMultiplier, hi, hq0]
      exact pow_le_pow_left₀ (norm_nonneg _) hrho (k + 1)

end NCG
