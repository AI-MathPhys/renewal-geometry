/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.MatrixExpDerivative
import RenewalGeometry.DiscreteAnalysis.ShiftedPlaquetteLogarithmUniformExact

/-!
# The analytic logarithm chart near the identity: quantitative estimates

In a complete normed `ℝ`-algebra `𝔸` with `‖1‖ = 1` the analytic branch of the logarithm near the
identity is `logChart P = log(1 + (P - 1))`, the power series
`Σ_{n ≥ 0} (-1)^n (P - 1)^{n+1}/(n+1)` (`ShiftedPlaquette.logOneAdd`), defined on
`‖P - 1‖ < 1`.  This is the logarithm of `eq:native-plaquettes` and of the logarithmic link
coordinates of the Einstein–SM action-closure manuscript ("the analytic branch near the
identity").  This file proves the quantitative facts used in `eq:native-YM-split`,
`eq:native-YM-envelope` and `thm:finite-Coulomb-normalization`:

* `exp_logChart`: `e^{log P} = P` (`‖P - 1‖ < 1`);
* `norm_logOneAdd_sub_self_le`, `norm_logOneAdd_le`: `‖log(1+z) - z‖ ≤ ‖z‖²`,
  `‖log(1+z)‖ ≤ 2‖z‖` for `‖z‖ ≤ 1/2`;
* `norm_exp_sub_one_sub_le`, `norm_exp_sub_one_le`: `‖e^u - 1 - u‖ ≤ ‖u‖²`, `‖e^u - 1‖ ≤ 2‖u‖`
  for `‖u‖ ≤ 1`;
* `exp_injective_of_norm_le`: `exp` is injective on the ball `‖·‖ ≤ 1/8` (Duhamel's formula);
* `logChart_exp`: `log(e^Y) = Y` for `‖Y‖ ≤ 1/32`, hence `eventually_logChart_exp` (the chart
  hypothesis of `MatrixExpDerivative.hasDerivAt_log_comp`);
* `logChart_conj`: conjugation equivariance `log(u P u⁻¹) = u (log P) u⁻¹` whenever both sides
  are in the chart (a conjugation-invariant chart for norm-preserving conjugations);
* `logChart_star`: `log(P^*) = (log P)^*` in a normed star algebra;
* `norm_logChart_exp4_sub_le` (**the four-exponential estimate**): for `S = Σ ‖a_i‖ ≤ 1/8`,
  `‖log(e^{a₁} e^{a₂} e^{a₃} e^{a₄}) - (a₁ + a₂ + a₃ + a₄)‖ ≤ 21 S²` and
  `‖e^{a₁} e^{a₂} e^{a₃} e^{a₄} - 1‖ ≤ 4 S`;
* `contDiffAt_logChart`: the chart is `C^∞` on `‖P - 1‖ < 1`.
-/

open NormedSpace Filter Topology

namespace RenewalGeometry.SeriesLogChart

open ShiftedPlaquette

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The analytic logarithm chart `log P = log(1 + (P - 1))` near the identity. -/
def logChart (P : 𝔸) : 𝔸 := logOneAdd (P - 1)

theorem exp_logChart {P : 𝔸} (hP : ‖P - 1‖ < 1) : exp (logChart P) = P := by
  rw [logChart, exp_logOneAdd hP, add_sub_cancel]

theorem hasSum_logOneAdd {z : 𝔸} (hz : ‖z‖ < 1) :
    HasSum (fun n => logQuotientCoeff n • z ^ (n + 1)) (logOneAdd z) := by
  have := (hasSum_logQuotient hz).mul_left z
  refine this.congr_fun fun n => ?_
  rw [mul_smul_comm, ← pow_succ']

theorem abs_logQuotientCoeff_succ_le (n : ℕ) : |logQuotientCoeff (n + 1)| ≤ 1 / 2 := by
  have := norm_logQuotientCoeff (n + 1)
  rw [Real.norm_eq_abs] at this
  rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast; linarith

/-- `‖log(1+z) - z‖ ≤ ‖z‖²` for `‖z‖ ≤ 1/2`. -/
theorem norm_logOneAdd_sub_self_le {z : 𝔸} (hz : ‖z‖ ≤ 1 / 2) :
    ‖logOneAdd z - z‖ ≤ ‖z‖ ^ 2 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have h := hasSum_logOneAdd hz1
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one] at h
  have hc0 : logQuotientCoeff 0 = 1 := by simp [logQuotientCoeff]
  rw [hc0, one_smul] at h
  set r := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg z
  have hg : HasSum (fun n : ℕ => (1 / 2 * r ^ 2) * r ^ n) ((1 / 2 * r ^ 2) * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hz1).mul_left _
  have hb := h.norm_le_of_bounded hg fun n => by
    rw [norm_smul, Real.norm_eq_abs]
    calc |logQuotientCoeff (n + 1)| * ‖z ^ (n + 1 + 1)‖ ≤ 1 / 2 * r ^ (n + 1 + 1) :=
          mul_le_mul (abs_logQuotientCoeff_succ_le _) (norm_pow_le _ _) (norm_nonneg _)
            (by norm_num)
      _ = (1 / 2 * r ^ 2) * r ^ n := by ring
  refine hb.trans ?_
  have : (1 - r)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc (1 / 2 * r ^ 2) * (1 - r)⁻¹ ≤ (1 / 2 * r ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = r ^ 2 := by ring

/-- `‖log(1+z)‖ ≤ 2‖z‖` for `‖z‖ ≤ 1/2`. -/
theorem norm_logOneAdd_le {z : 𝔸} (hz : ‖z‖ ≤ 1 / 2) : ‖logOneAdd z‖ ≤ 2 * ‖z‖ := by
  have h1 := norm_logOneAdd_sub_self_le hz
  have h2 : ‖logOneAdd z‖ ≤ ‖logOneAdd z - z‖ + ‖z‖ := by
    have := norm_add_le (logOneAdd z - z) z
    rwa [sub_add_cancel] at this
  nlinarith [norm_nonneg z]

/-! ### Exponential estimates -/

theorem two_pow_le_factorial_add_two (n : ℕ) : 2 ^ (n + 1) ≤ (n + 2).factorial := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

theorem expRemCoeff_le (n : ℕ) : expRemCoeff n ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  unfold expRemCoeff
  rw [one_div_pow, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast two_pow_le_factorial_add_two n)

theorem norm_expRemainder_le {u : 𝔸} (hu : ‖u‖ ≤ 1) : ‖expRemainder u‖ ≤ 1 := by
  have hg : HasSum (fun n : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n) ((1 / 2) * (1 - 1 / 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hb := (hasSum_expRemainder u).norm_le_of_bounded hg fun n => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by unfold expRemCoeff; positivity)]
    calc expRemCoeff n * ‖u ^ n‖ ≤ (1 / 2 : ℝ) ^ (n + 1) * 1 :=
          mul_le_mul (expRemCoeff_le n) ((norm_pow_le u n).trans (pow_le_one₀ (norm_nonneg u) hu))
            (norm_nonneg _) (by positivity)
      _ = (1 / 2) * (1 / 2 : ℝ) ^ n := by ring
  refine hb.trans (le_of_eq ?_)
  norm_num

/-- `‖e^u - 1 - u‖ ≤ ‖u‖²` for `‖u‖ ≤ 1`. -/
theorem norm_exp_sub_one_sub_le {u : 𝔸} (hu : ‖u‖ ≤ 1) : ‖exp u - 1 - u‖ ≤ ‖u‖ ^ 2 := by
  rw [exp_eq_expRemainder, show 1 + u + u ^ 2 * expRemainder u - 1 - u = u ^ 2 * expRemainder u
    by abel]
  calc ‖u ^ 2 * expRemainder u‖ ≤ ‖u ^ 2‖ * ‖expRemainder u‖ := norm_mul_le _ _
    _ ≤ ‖u‖ ^ 2 * 1 := mul_le_mul (norm_pow_le u 2) (norm_expRemainder_le hu) (norm_nonneg _)
        (by positivity)
    _ = _ := mul_one _

/-- `‖e^u - 1‖ ≤ 2‖u‖` for `‖u‖ ≤ 1`. -/
theorem norm_exp_sub_one_le {u : 𝔸} (hu : ‖u‖ ≤ 1) : ‖exp u - 1‖ ≤ 2 * ‖u‖ := by
  have h1 := norm_exp_sub_one_sub_le hu
  have h2 : ‖exp u - 1‖ ≤ ‖exp u - 1 - u‖ + ‖u‖ := by
    have := norm_add_le (exp u - 1 - u) u
    rwa [sub_add_cancel] at this
  nlinarith [norm_nonneg u]

theorem norm_exp_le_one_add {u : 𝔸} (hu : ‖u‖ ≤ 1) : ‖exp u‖ ≤ 1 + 2 * ‖u‖ := by
  have h := norm_exp_sub_one_le hu
  have h2 : ‖exp u‖ ≤ ‖exp u - 1‖ + ‖(1 : 𝔸)‖ := by
    have := norm_add_le (exp u - 1) 1
    rwa [sub_add_cancel] at this
  rw [norm_one] at h2
  linarith

/-! ### Injectivity of `exp` near `0` and `log ∘ exp = id` -/

/-- **`exp` is injective on `‖·‖ ≤ 1/8`** (Duhamel's formula). -/
theorem exp_injective_of_norm_le {W Y : 𝔸} (hW : ‖W‖ ≤ 1 / 8) (hY : ‖Y‖ ≤ 1 / 8)
    (h : exp W = exp Y) : W = Y := by
  set D := W - Y
  have hduh := MatrixExpDerivative.exp_sub_exp_eq_integral W Y
  rw [h, sub_self] at hduh
  have hc : Continuous fun s : ℝ => exp (s • W) * D * exp ((1 - s) • Y) :=
    ((MatrixExpDerivative.continuous_exp'.comp (continuous_id.smul continuous_const)).mul
      continuous_const).mul
      (MatrixExpDerivative.continuous_exp'.comp ((continuous_const.sub continuous_id).smul
        continuous_const))
  have hD : D = ∫ s in (0 : ℝ)..1, (D - exp (s • W) * D * exp ((1 - s) • Y)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
      ← hduh, intervalIntegral.integral_const]
    simp
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
      ‖D - exp (s • W) * D * exp ((1 - s) • Y)‖ ≤ 9 / 16 * ‖D‖ := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2
    have hsW : ‖s • W‖ ≤ 1 / 8 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      nlinarith [norm_nonneg W]
    have hsY : ‖(1 - s) • Y‖ ≤ 1 / 8 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      nlinarith [norm_nonneg Y]
    have e1 := norm_exp_sub_one_le (u := s • W) (by linarith)
    have e2 := norm_exp_sub_one_le (u := (1 - s) • Y) (by linarith)
    have e3 := norm_exp_le_one_add (u := (1 - s) • Y) (by linarith)
    have hsplit : D - exp (s • W) * D * exp ((1 - s) • Y) =
        -((exp (s • W) - 1) * D * exp ((1 - s) • Y)) - D * (exp ((1 - s) • Y) - 1) := by
      noncomm_ring
    rw [hsplit]
    have hD0 := norm_nonneg D
    have a1 : ‖exp (s • W) - 1‖ ≤ 1 / 4 := by linarith
    have a2 : ‖exp ((1 - s) • Y) - 1‖ ≤ 1 / 4 := by linarith
    have a3 : ‖exp ((1 - s) • Y)‖ ≤ 5 / 4 := by linarith
    calc ‖-((exp (s • W) - 1) * D * exp ((1 - s) • Y)) - D * (exp ((1 - s) • Y) - 1)‖
        ≤ ‖(exp (s • W) - 1) * D * exp ((1 - s) • Y)‖ + ‖D * (exp ((1 - s) • Y) - 1)‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
      _ ≤ ‖exp (s • W) - 1‖ * ‖D‖ * ‖exp ((1 - s) • Y)‖ + ‖D‖ * ‖exp ((1 - s) • Y) - 1‖ :=
          add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _))) (norm_mul_le _ _)
      _ ≤ (1 / 4) * ‖D‖ * (5 / 4) + ‖D‖ * (1 / 4) := by gcongr
      _ = 9 / 16 * ‖D‖ := by ring
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [← hD] at hn
  simp only [sub_zero, abs_one, mul_one] at hn
  have : ‖D‖ = 0 := by nlinarith [norm_nonneg D]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **`log(e^Y) = Y`** for `‖Y‖ ≤ 1/32`. -/
theorem logChart_exp {Y : 𝔸} (hY : ‖Y‖ ≤ 1 / 32) : logChart (exp Y) = Y := by
  have hz : ‖exp Y - 1‖ ≤ 1 / 16 := (norm_exp_sub_one_le (by linarith)).trans (by linarith)
  have hW : ‖logChart (exp Y)‖ ≤ 1 / 8 :=
    (norm_logOneAdd_le (by linarith)).trans (by linarith)
  exact exp_injective_of_norm_le hW (by linarith) (exp_logChart (by linarith))

/-- The chart hypothesis of `MatrixExpDerivative.hasDerivAt_log_comp`. -/
theorem eventually_logChart_exp {X : 𝔸} (hX : ‖X‖ < 1 / 32) :
    ∀ᶠ Y in 𝓝 X, logChart (exp Y) = Y := by
  filter_upwards [Metric.ball_mem_nhds X (sub_pos.2 hX)] with Y hY
  refine logChart_exp ?_
  rw [Metric.mem_ball, dist_eq_norm] at hY
  have := norm_le_insert' Y X
  linarith

theorem norm_logChart_le {P : 𝔸} (hP : ‖P - 1‖ ≤ 1 / 2) : ‖logChart P‖ ≤ 2 * ‖P - 1‖ :=
  norm_logOneAdd_le hP

theorem norm_logChart_sub_le {P : 𝔸} (hP : ‖P - 1‖ ≤ 1 / 2) :
    ‖logChart P - (P - 1)‖ ≤ ‖P - 1‖ ^ 2 :=
  norm_logOneAdd_sub_self_le hP

theorem logChart_one : logChart (1 : 𝔸) = 0 := by
  have := logChart_exp (𝔸 := 𝔸) (Y := 0) (by simp)
  rwa [exp_zero] at this

/-! ### Equivariance -/

/-- **Conjugation equivariance of the chart**: `log(1 + u z u⁻¹) = u log(1 + z) u⁻¹` when both
arguments are in the chart. -/
theorem logOneAdd_conj (u : 𝔸ˣ) {z : 𝔸} (hz : ‖z‖ < 1) (hz' : ‖(u : 𝔸) * z * ↑u⁻¹‖ < 1) :
    logOneAdd ((u : 𝔸) * z * ↑u⁻¹) = u * logOneAdd z * ↑u⁻¹ := by
  set C : 𝔸 →L[ℝ] 𝔸 := (ContinuousLinearMap.mul ℝ 𝔸 (u : 𝔸)).comp
    ((ContinuousLinearMap.mul ℝ 𝔸).flip (↑u⁻¹ : 𝔸))
  have hC : ∀ X, C X = u * X * ↑u⁻¹ := fun X => by simp [C, mul_assoc]
  have h1 := (hasSum_logOneAdd hz).mapL C
  have h2 := hasSum_logOneAdd hz'
  rw [hC] at h1
  refine h2.unique (h1.congr_fun fun n => ?_)
  rw [hC, Units.conj_pow, mul_smul_comm, smul_mul_assoc]

theorem logChart_conj (u : 𝔸ˣ) {P : 𝔸} (hP : ‖P - 1‖ < 1)
    (hP' : ‖(u : 𝔸) * (P - 1) * ↑u⁻¹‖ < 1) :
    logChart ((u : 𝔸) * P * ↑u⁻¹) = u * logChart P * ↑u⁻¹ := by
  have e : (u : 𝔸) * P * ↑u⁻¹ - 1 = u * (P - 1) * ↑u⁻¹ := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [logChart, e, logOneAdd_conj u hP hP', logChart]

section Star

variable [StarRing 𝔸] [ContinuousStar 𝔸] [StarModule ℝ 𝔸]

theorem logOneAdd_star {z : 𝔸} (hz : ‖z‖ < 1) (hz' : ‖star z‖ < 1) :
    logOneAdd (star z) = star (logOneAdd z) := by
  have h1 := (hasSum_logOneAdd hz).star
  refine (hasSum_logOneAdd hz').unique (h1.congr_fun fun n => ?_)
  rw [star_smul, star_pow, star_trivial (logQuotientCoeff n)]

theorem logChart_star {P : 𝔸} (hP : ‖P - 1‖ < 1) (hP' : ‖star P - 1‖ < 1) :
    logChart (star P) = star (logChart P) := by
  have e : star P - 1 = star (P - 1) := by rw [star_sub, star_one]
  rw [logChart, e, logOneAdd_star hP (e ▸ hP'), logChart]

end Star

/-! ### Products of near-identity elements -/

/-- `‖xy - 1‖ ≤ (1+s)(1+t) - 1` when `‖x - 1‖ ≤ s`, `‖y - 1‖ ≤ t`. -/
theorem norm_mul_sub_one_le {x y : 𝔸} {s t : ℝ} (hx : ‖x - 1‖ ≤ s) (hy : ‖y - 1‖ ≤ t) :
    ‖x * y - 1‖ ≤ (1 + s) * (1 + t) - 1 := by
  have e : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by noncomm_ring
  rw [e]
  have h0 := (norm_nonneg (x - 1)).trans hx
  have h1 := (norm_nonneg (y - 1)).trans hy
  calc ‖(x - 1) * (y - 1) + (x - 1) + (y - 1)‖
      ≤ ‖(x - 1) * (y - 1)‖ + ‖x - 1‖ + ‖y - 1‖ := norm_add₃_le
    _ ≤ ‖x - 1‖ * ‖y - 1‖ + ‖x - 1‖ + ‖y - 1‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ s * t + s + t := by gcongr
    _ = (1 + s) * (1 + t) - 1 := by ring

/-- The second-order remainder of a four-fold product:
`‖x₁x₂x₃x₄ - 1 - Σ (x_i - 1)‖ ≤ s₁σ₂₃₄ + s₂σ₃₄ + s₃s₄`, `σ` the product bounds. -/
theorem norm_mul4_sub_sum_le {x₁ x₂ x₃ x₄ : 𝔸} {s₁ s₂ s₃ s₄ : ℝ} (h₁ : ‖x₁ - 1‖ ≤ s₁)
    (h₂ : ‖x₂ - 1‖ ≤ s₂) (h₃ : ‖x₃ - 1‖ ≤ s₃) (h₄ : ‖x₄ - 1‖ ≤ s₄) :
    ‖x₁ * x₂ * x₃ * x₄ - 1 - ((x₁ - 1) + (x₂ - 1) + (x₃ - 1) + (x₄ - 1))‖ ≤
      s₁ * ((1 + s₂) * (1 + s₃) * (1 + s₄) - 1) + s₂ * ((1 + s₃) * (1 + s₄) - 1) + s₃ * s₄ := by
  have h34 := norm_mul_sub_one_le h₃ h₄
  have h234 : ‖x₂ * (x₃ * x₄) - 1‖ ≤ (1 + s₂) * (1 + s₃) * (1 + s₄) - 1 := by
    have := norm_mul_sub_one_le h₂ h34
    rwa [show (1 + s₂) * (1 + ((1 + s₃) * (1 + s₄) - 1)) - 1 =
      (1 + s₂) * (1 + s₃) * (1 + s₄) - 1 by ring] at this
  have e : x₁ * x₂ * x₃ * x₄ - 1 - ((x₁ - 1) + (x₂ - 1) + (x₃ - 1) + (x₄ - 1)) =
      (x₁ - 1) * (x₂ * (x₃ * x₄) - 1) + (x₂ - 1) * (x₃ * x₄ - 1) + (x₃ - 1) * (x₄ - 1) := by
    noncomm_ring
  rw [e]
  have n1 := (norm_nonneg _).trans h₁
  have n2 := (norm_nonneg _).trans h₂
  have n3 := (norm_nonneg _).trans h₃
  calc ‖(x₁ - 1) * (x₂ * (x₃ * x₄) - 1) + (x₂ - 1) * (x₃ * x₄ - 1) + (x₃ - 1) * (x₄ - 1)‖
      ≤ ‖(x₁ - 1) * (x₂ * (x₃ * x₄) - 1)‖ + ‖(x₂ - 1) * (x₃ * x₄ - 1)‖ +
          ‖(x₃ - 1) * (x₄ - 1)‖ := norm_add₃_le
    _ ≤ ‖x₁ - 1‖ * ‖x₂ * (x₃ * x₄) - 1‖ + ‖x₂ - 1‖ * ‖x₃ * x₄ - 1‖ +
          ‖x₃ - 1‖ * ‖x₄ - 1‖ := by gcongr <;> exact norm_mul_le _ _
    _ ≤ _ := by gcongr

/-- One step of the product bound: `(1+σ)(1+s) - 1 ≤ 2(T + s)` when `σ ≤ 2T`, `T ≤ 1/2`. -/
theorem prod_step_le {σ T s : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 2 * T) (hT : T ≤ 1 / 2) (hs : 0 ≤ s) :
    (1 + σ) * (1 + s) - 1 ≤ 2 * (T + s) := by
  have h1 : σ * s ≤ 2 * T * s := mul_le_mul_of_nonneg_right hσ hs
  have h2 : 2 * T * s ≤ s := by
    have : 2 * T ≤ 1 := by linarith
    calc 2 * T * s ≤ 1 * s := mul_le_mul_of_nonneg_right this hs
      _ = s := one_mul s
  have e : (1 + σ) * (1 + s) - 1 = σ + s + σ * s := by ring
  rw [e]; linarith

/-- **The four-exponential estimate** (`eq:native-YM-envelope`, pointwise): with
`S = ‖a₁‖ + ‖a₂‖ + ‖a₃‖ + ‖a₄‖ ≤ 1/8`, the product `P = e^{a₁}e^{a₂}e^{a₃}e^{a₄}` satisfies
`‖P - 1‖ ≤ 4S` and `‖log P - (a₁ + a₂ + a₃ + a₄)‖ ≤ 21 S²`. -/
theorem norm_logChart_exp4_sub_le (a₁ a₂ a₃ a₄ : 𝔸)
    (hS : ‖a₁‖ + ‖a₂‖ + ‖a₃‖ + ‖a₄‖ ≤ 1 / 8) :
    ‖exp a₁ * exp a₂ * exp a₃ * exp a₄ - 1‖ ≤ 4 * (‖a₁‖ + ‖a₂‖ + ‖a₃‖ + ‖a₄‖) ∧
      ‖logChart (exp a₁ * exp a₂ * exp a₃ * exp a₄) - (a₁ + a₂ + a₃ + a₄)‖ ≤
        21 * (‖a₁‖ + ‖a₂‖ + ‖a₃‖ + ‖a₄‖) ^ 2 := by
  have n1 := norm_nonneg a₁
  have n2 := norm_nonneg a₂
  have n3 := norm_nonneg a₃
  have n4 := norm_nonneg a₄
  have b1 : ‖a₁‖ ≤ 1 := by linarith
  have b2 : ‖a₂‖ ≤ 1 := by linarith
  have b3 : ‖a₃‖ ≤ 1 := by linarith
  have b4 : ‖a₄‖ ≤ 1 := by linarith
  have e1 := norm_exp_sub_one_le b1
  have e2 := norm_exp_sub_one_le b2
  have e3 := norm_exp_sub_one_le b3
  have e4 := norm_exp_sub_one_le b4
  -- `‖P - 1‖`
  have hP : ‖exp a₁ * exp a₂ * exp a₃ * exp a₄ - 1‖ ≤ 4 * (‖a₁‖ + ‖a₂‖ + ‖a₃‖ + ‖a₄‖) := by
    have h12 := norm_mul_sub_one_le e1 e2
    have h123 := norm_mul_sub_one_le h12 e3
    have h1234 := norm_mul_sub_one_le h123 e4
    refine h1234.trans ?_
    have k1 : (1 + 2 * ‖a₁‖) * (1 + 2 * ‖a₂‖) - 1 ≤ 2 * (‖a₁‖ + 2 * ‖a₂‖) :=
      prod_step_le (by positivity) (by linarith) (by linarith) (by positivity)
    have k2 : (1 + ((1 + 2 * ‖a₁‖) * (1 + 2 * ‖a₂‖) - 1)) * (1 + 2 * ‖a₃‖) - 1 ≤
        2 * (‖a₁‖ + 2 * ‖a₂‖ + 2 * ‖a₃‖) :=
      prod_step_le (by nlinarith) k1 (by linarith) (by positivity)
    have k3 := prod_step_le (s := 2 * ‖a₄‖) (by nlinarith) k2 (by linarith) (by positivity)
    linarith
  refine ⟨hP, ?_⟩
  set S := ‖a₁‖ + ‖a₂‖ + ‖a₃‖ + ‖a₄‖ with hSdef
  set P := exp a₁ * exp a₂ * exp a₃ * exp a₄ with hPdef
  -- second-order remainder of the product
  have hR := norm_mul4_sub_sum_le e1 e2 e3 e4
  have hR' : ‖P - 1 - ((exp a₁ - 1) + (exp a₂ - 1) + (exp a₃ - 1) + (exp a₄ - 1))‖ ≤
      4 * S ^ 2 := by
    refine hR.trans ?_
    set s₁ := 2 * ‖a₁‖ with hs₁
    set s₂ := 2 * ‖a₂‖ with hs₂
    set s₃ := 2 * ‖a₃‖ with hs₃
    set s₄ := 2 * ‖a₄‖ with hs₄
    have p1 : 0 ≤ s₁ := by positivity
    have p2 : 0 ≤ s₂ := by positivity
    have p3 : 0 ≤ s₃ := by positivity
    have p4 : 0 ≤ s₄ := by positivity
    have hS2 : 4 * S ^ 2 = (s₁ + s₂ + s₃ + s₄) ^ 2 := by
      rw [hSdef, hs₁, hs₂, hs₃, hs₄]; ring
    rw [hS2]
    have c34 : (1 + s₃) * (1 + s₄) - 1 ≤ 2 * (s₃ / 2 + s₄) :=
      prod_step_le p3 (by linarith) (by linarith) p4
    have c234 : (1 + s₂) * (1 + s₃) * (1 + s₄) - 1 ≤ 2 * (s₂ / 2 + s₃ + s₄) := by
      have k1 : (1 + s₂) * (1 + s₃) - 1 ≤ 2 * (s₂ / 2 + s₃) :=
        prod_step_le p2 (by linarith) (by linarith) p3
      have k2 := prod_step_le (s := s₄) (by nlinarith) k1 (by linarith) p4
      have e : (1 + s₂) * (1 + s₃) * (1 + s₄) - 1 = (1 + ((1 + s₂) * (1 + s₃) - 1)) * (1 + s₄) - 1 :=
        by ring
      rw [e]; linarith
    have f1 : s₁ * ((1 + s₂) * (1 + s₃) * (1 + s₄) - 1) ≤ s₁ * (2 * (s₂ / 2 + s₃ + s₄)) :=
      mul_le_mul_of_nonneg_left c234 p1
    have f2 : s₂ * ((1 + s₃) * (1 + s₄) - 1) ≤ s₂ * (2 * (s₃ / 2 + s₄)) :=
      mul_le_mul_of_nonneg_left c34 p2
    have e : (s₁ + s₂ + s₃ + s₄) ^ 2 - (s₁ * (2 * (s₂ / 2 + s₃ + s₄)) + s₂ * (2 * (s₃ / 2 + s₄)) +
        s₃ * s₄) = s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2 + s₄ ^ 2 + s₁ * s₂ + s₂ * s₃ + s₃ * s₄ := by ring
    have : 0 ≤ s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2 + s₄ ^ 2 + s₁ * s₂ + s₂ * s₃ + s₃ * s₄ := by positivity
    linarith
  -- linearization of each exponential
  have hlin : ‖((exp a₁ - 1) + (exp a₂ - 1) + (exp a₃ - 1) + (exp a₄ - 1)) -
      (a₁ + a₂ + a₃ + a₄)‖ ≤ S ^ 2 := by
    have f1 := norm_exp_sub_one_sub_le b1
    have f2 := norm_exp_sub_one_sub_le b2
    have f3 := norm_exp_sub_one_sub_le b3
    have f4 := norm_exp_sub_one_sub_le b4
    have e : ((exp a₁ - 1) + (exp a₂ - 1) + (exp a₃ - 1) + (exp a₄ - 1)) - (a₁ + a₂ + a₃ + a₄) =
        (exp a₁ - 1 - a₁) + (exp a₂ - 1 - a₂) + (exp a₃ - 1 - a₃) + (exp a₄ - 1 - a₄) := by abel
    rw [e]
    have hsq : S ^ 2 = ‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 + ‖a₃‖ ^ 2 + ‖a₄‖ ^ 2 + 2 * (‖a₁‖ * ‖a₂‖ +
        ‖a₁‖ * ‖a₃‖ + ‖a₁‖ * ‖a₄‖ + ‖a₂‖ * ‖a₃‖ + ‖a₂‖ * ‖a₄‖ + ‖a₃‖ * ‖a₄‖) := by
      rw [hSdef]; ring
    have hpos : 0 ≤ ‖a₁‖ * ‖a₂‖ + ‖a₁‖ * ‖a₃‖ + ‖a₁‖ * ‖a₄‖ + ‖a₂‖ * ‖a₃‖ + ‖a₂‖ * ‖a₄‖ +
        ‖a₃‖ * ‖a₄‖ := by positivity
    calc _ ≤ ‖exp a₁ - 1 - a₁‖ + ‖exp a₂ - 1 - a₂‖ + ‖exp a₃ - 1 - a₃‖ + ‖exp a₄ - 1 - a₄‖ :=
          norm_add₄_le
      _ ≤ ‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 + ‖a₃‖ ^ 2 + ‖a₄‖ ^ 2 := by gcongr
      _ ≤ S ^ 2 := by rw [hsq]; linarith
  -- the logarithm
  have hP2 : ‖P - 1‖ ≤ 1 / 2 := hP.trans (by linarith)
  have hlog := norm_logChart_sub_le hP2
  have e : logChart P - (a₁ + a₂ + a₃ + a₄) = (logChart P - (P - 1)) +
      (P - 1 - ((exp a₁ - 1) + (exp a₂ - 1) + (exp a₃ - 1) + (exp a₄ - 1))) +
      (((exp a₁ - 1) + (exp a₂ - 1) + (exp a₃ - 1) + (exp a₄ - 1)) - (a₁ + a₂ + a₃ + a₄)) := by
    abel
  rw [e]
  have hS0 : 0 ≤ S := by positivity
  have hP1 : ‖P - 1‖ ^ 2 ≤ 16 * S ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hP 2
    calc ‖P - 1‖ ^ 2 ≤ (4 * S) ^ 2 := this
      _ = 16 * S ^ 2 := by ring
  calc _ ≤ ‖logChart P - (P - 1)‖ +
        ‖P - 1 - ((exp a₁ - 1) + (exp a₂ - 1) + (exp a₃ - 1) + (exp a₄ - 1))‖ +
        ‖((exp a₁ - 1) + (exp a₂ - 1) + (exp a₃ - 1) + (exp a₄ - 1)) - (a₁ + a₂ + a₃ + a₄)‖ :=
        norm_add₃_le
    _ ≤ 16 * S ^ 2 + 4 * S ^ 2 + S ^ 2 := by gcongr; exact hlog.trans hP1
    _ = 21 * S ^ 2 := by ring

/-! ### Smoothness -/

theorem analyticAt_logOneAdd {z : 𝔸} (hz : ‖z‖ < 1) : AnalyticAt ℝ logOneAdd z := by
  have h : AnalyticAt ℝ (fun z : 𝔸 => z * logQuotient z) z :=
    analyticAt_id.mul (analyticAt_logQuotient hz)
  exact h

theorem contDiffAt_logChart {k : WithTop ℕ∞} {P : 𝔸} (hP : ‖P - 1‖ < 1) :
    ContDiffAt ℝ k logChart P := by
  have h1 : ContDiffAt ℝ k logOneAdd (P - 1) := (analyticAt_logOneAdd hP).contDiffAt
  exact h1.comp P (contDiffAt_id.sub contDiffAt_const)

end

end RenewalGeometry.SeriesLogChart
