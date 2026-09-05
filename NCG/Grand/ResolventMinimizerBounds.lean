/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertResolventObjective

/-!
# Coercive bounds for resolvent minimizers

Comparison with the zero competitor gives a uniform norm bound for minimizers of a nonnegative
quadratic resolvent objective.  This discharges the boundedness obligation in the abstract
varying-space minimizer convergence record whenever the moving sources are uniformly bounded.
-/

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]

/-- A minimizer of a nonnegative resolvent objective has norm at most twice the source norm
divided by the positive quadratic parameter. -/
theorem norm_le_two_mul_div_of_minimizes_resolventObjective
    (q : H → ℝ) (lam : ℝ) (hlam : 0 < lam) (f x : H)
    (hq0 : q 0 = 0) (hqx : 0 ≤ q x)
    (hmin : resolventObjective (K := K) q lam f x ≤
      resolventObjective (K := K) q lam f 0) :
    ‖x‖ ≤ 2 * ‖f‖ / lam := by
  have hre : RCLike.re (inner K x f) ≤ ‖x‖ * ‖f‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm x f)
  have hobjective :
      q x + lam * ‖x‖ ^ 2 - 2 * RCLike.re (inner K x f) ≤ 0 := by
    simpa [resolventObjective, hq0] using hmin
  have hquad : lam * ‖x‖ ^ 2 ≤ 2 * ‖x‖ * ‖f‖ := by
    nlinarith
  by_cases hx0 : ‖x‖ = 0
  · rw [hx0]
    positivity
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
  have hlinear : lam * ‖x‖ ≤ 2 * ‖f‖ := by
    nlinarith
  exact (le_div_iff₀ hlam).2 (by simpa [mul_comm] using hlinear)

/-- Completing the square gives a source-dependent lower bound for every nonnegative resolvent
objective. -/
theorem neg_norm_sq_div_le_resolventObjective
    (q : H → ℝ) (lam : ℝ) (hlam : 0 < lam) (f x : H)
    (hqx : 0 ≤ q x) :
    -(‖f‖ ^ 2) / lam ≤ resolventObjective (K := K) q lam f x := by
  have hre : RCLike.re (inner K x f) ≤ ‖x‖ * ‖f‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm x f)
  have hcomplete :
      -(‖f‖ ^ 2) / lam ≤ lam * ‖x‖ ^ 2 - 2 * ‖x‖ * ‖f‖ := by
    apply (div_le_iff₀ hlam).2
    nlinarith [sq_nonneg (lam * ‖x‖ - ‖f‖)]
  dsimp [resolventObjective]
  nlinarith

/-- A uniform source bound supplies one lower bound for all nonnegative resolvent objectives. -/
theorem uniformlyBoundedBelow_resolventObjectives
    {Hn : ℕ → Type*}
    [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
    (q : (n : ℕ) → Hn n → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (f x : ∀ n, Hn n) (F : ℝ) (hF : 0 ≤ F)
    (hf : ∀ n, ‖f n‖ ≤ F) (hqx : ∀ n, 0 ≤ q n (x n)) :
    ∀ n, -(F ^ 2) / lam ≤
      resolventObjective (K := K) (q n) lam (f n) (x n) := by
  intro n
  calc
    -(F ^ 2) / lam ≤ -(‖f n‖ ^ 2) / lam := by
      apply (div_le_div_iff_of_pos_right hlam).2
      nlinarith [sq_nonneg (F - ‖f n‖), norm_nonneg (f n), hf n]
    _ ≤ resolventObjective (K := K) (q n) lam (f n) (x n) :=
      neg_norm_sq_div_le_resolventObjective (q n) lam hlam (f n) (x n) (hqx n)

/-- A uniformly bounded moving source family gives one uniform bound for all of its resolvent
minimizers. -/
theorem uniformlyBounded_resolventMinimizers
    {Hn : ℕ → Type*}
    [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
    (q : (n : ℕ) → Hn n → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (f x : ∀ n, Hn n) (F : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ F)
    (hq0 : ∀ n, q n 0 = 0) (hqx : ∀ n, 0 ≤ q n (x n))
    (hmin : ∀ n, resolventObjective (K := K) (q n) lam (f n) (x n) ≤
      resolventObjective (K := K) (q n) lam (f n) 0) :
    ∀ n, ‖x n‖ ≤ 2 * F / lam := by
  intro n
  calc
    ‖x n‖ ≤ 2 * ‖f n‖ / lam :=
      norm_le_two_mul_div_of_minimizes_resolventObjective
        (q n) lam hlam (f n) (x n) (hq0 n) (hqx n) (hmin n)
    _ ≤ 2 * F / lam := by
      gcongr
      exact hf n

/-- Comparison with zero bounds the form energy of a resolvent minimizer by its source pairing. -/
theorem formValue_le_two_mul_norms_of_minimizes_resolventObjective
    (q : H → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (f x : H)
    (hq0 : q 0 = 0)
    (hmin : resolventObjective (K := K) q lam f x ≤
      resolventObjective (K := K) q lam f 0) :
    q x ≤ 2 * ‖x‖ * ‖f‖ := by
  have hobjective :
      q x + lam * ‖x‖ ^ 2 - 2 * RCLike.re (inner K x f) ≤ 0 := by
    simpa [resolventObjective, hq0] using hmin
  have hre : RCLike.re (inner K x f) ≤ ‖x‖ * ‖f‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm x f)
  nlinarith [mul_nonneg hlam (sq_nonneg ‖x‖)]

/-- Uniform source and minimizer bounds give a uniform upper bound for their form energies. -/
theorem uniformlyBoundedAbove_resolventMinimizerEnergies
    {Hn : ℕ → Type*}
    [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
    (q : (n : ℕ) → Hn n → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (f x : ∀ n, Hn n) (C F : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ C) (hf : ∀ n, ‖f n‖ ≤ F)
    (hq0 : ∀ n, q n 0 = 0)
    (hmin : ∀ n, resolventObjective (K := K) (q n) lam (f n) (x n) ≤
      resolventObjective (K := K) (q n) lam (f n) 0) :
    ∀ n, q n (x n) ≤ 2 * C * F := by
  intro n
  calc
    q n (x n) ≤ 2 * ‖x n‖ * ‖f n‖ :=
      formValue_le_two_mul_norms_of_minimizes_resolventObjective
        (q n) lam hlam (f n) (x n) (hq0 n) (hmin n)
    _ ≤ 2 * C * F := by
      gcongr
      · exact hx n
      · exact hf n

end NCG.VaryingHilbert
