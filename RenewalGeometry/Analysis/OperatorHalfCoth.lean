/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The operator functions `𝒥(Z) = ∫₀¹ e^{tZ} dt` and `𝒦(Z) = (Z/2) coth(Z/2)` in a Banach algebra
  (`eq:native-JK`, used in `lem:native-log-gauge-differential` and `lem:native-FP-inverse`,
  Einstein–SM action closure)

In a complete normed `ℝ`-algebra `𝔸` with `‖1‖ = 1`:

* `dexpJ Z = Σ_k Z^k/(k+1)!` (the series of `∫₀¹ e^{tZ} dt`), an everywhere-analytic function
  (`analyticAt_dexpJ`, `contDiff_dexpJ`) with `Z · 𝒥(Z) = e^Z - 1` (`mul_dexpJ`);
* `halfCoth Z = 𝒥(Z)⁻¹ · ½(1 + e^Z)`, the paper's `𝒦(Z) = (Z/2)coth(Z/2)` written through the
  identity `½ 𝒥(Z)⁻¹(I + e^Z) = 𝒦(Z)` used in the proof of `lem:native-log-gauge-differential`
  (for real scalars `halfCoth z · (e^z - 1) = (z/2)(e^z + 1)`, `halfCoth_real_mul`);
* on the chart `‖Z‖ ≤ 1/4`: `𝒥(Z)` is a unit with `‖𝒥(Z)⁻¹‖ ≤ 4` and
  `‖𝒦(Z) - 1‖ ≤ 12 ‖Z‖²` (`norm_halfCoth_sub_one_le`); `𝒦(0) = 1`;
* `𝒦` is `C^∞` on the open chart `‖Z‖ < 1/4` (`contDiffAt_halfCoth`).
-/

open Finset Filter NormedSpace FormalMultilinearSeries
open scoped Nat Topology ENNReal

namespace RenewalGeometry.OperatorHalfCoth

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The coefficients `1/(k+1)!` of `𝒥(z) = (e^z - 1)/z`. -/
def jCoeff (k : ℕ) : ℝ := ((k + 1)! : ℝ)⁻¹

variable (𝔸) in
/-- The power series of `𝒥`. -/
def jSeries : FormalMultilinearSeries ℝ 𝔸 𝔸 := ofScalars 𝔸 jCoeff

/-- `𝒥(Z) = Σ_k Z^k/(k+1)! = ∫₀¹ e^{tZ} dt` (`eq:native-JK`). -/
def dexpJ (Z : 𝔸) : 𝔸 := (jSeries 𝔸).sum Z

/-- `𝒦(Z) = (Z/2)coth(Z/2) = ½ 𝒥(Z)⁻¹ (1 + e^Z)` (`eq:native-JK`). -/
def halfCoth (Z : 𝔸) : 𝔸 := Ring.inverse (dexpJ Z) * ((1 / 2 : ℝ) • (1 + exp Z))

theorem jCoeff_nonneg (k : ℕ) : 0 ≤ jCoeff k := by unfold jCoeff; positivity

theorem jCoeff_le (k : ℕ) : jCoeff k ≤ (k ! : ℝ)⁻¹ := by
  unfold jCoeff
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_succ k))

omit [CompleteSpace 𝔸] in
theorem summable_norm_coeff_pow (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ (k ! : ℝ)⁻¹) (Z : 𝔸) :
    Summable fun k => ‖d k • Z ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (Real.summable_pow_div_factorial ‖Z‖)
  calc ‖d k • Z ^ k‖ = |d k| * ‖Z ^ k‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (k ! : ℝ)⁻¹ * ‖Z‖ ^ k := mul_le_mul (hd k) (norm_pow_le Z k) (norm_nonneg _) (by positivity)
    _ = ‖Z‖ ^ k / k ! := by rw [div_eq_mul_inv, mul_comm]

theorem hasSum_dexpJ (Z : 𝔸) : HasSum (fun k => jCoeff k • Z ^ k) (dexpJ Z) := by
  have hs : Summable fun k => jCoeff k • Z ^ k :=
    (summable_norm_coeff_pow jCoeff (fun k => by
      rw [abs_of_nonneg (jCoeff_nonneg k)]; exact jCoeff_le k) Z).of_norm
  have : dexpJ Z = ∑' k, jCoeff k • Z ^ k := ofScalars_sum_eq jCoeff Z
  rw [this]
  exact hs.hasSum

omit [CompleteSpace 𝔸] in
theorem jSeries_radius : (jSeries 𝔸).radius = ⊤ := by
  refine radius_eq_top_of_summable_norm _ fun r => ?_
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _))
    (fun k => ?_) (Real.summable_pow_div_factorial (r : ℝ))
  rw [jSeries, ofScalars_norm, Real.norm_eq_abs, abs_of_nonneg (jCoeff_nonneg k), div_eq_mul_inv,
    mul_comm ((r : ℝ) ^ k)]
  exact mul_le_mul_of_nonneg_right (jCoeff_le k) (pow_nonneg r.2 _)

theorem analyticAt_dexpJ (Z : 𝔸) : AnalyticAt ℝ dexpJ Z := by
  have h := (jSeries 𝔸).hasFPowerSeriesOnBall (by rw [jSeries_radius]; exact ENNReal.zero_lt_top)
  rw [jSeries_radius] at h
  exact h.analyticAt_of_mem (by simp)

theorem contDiff_dexpJ {k : WithTop ℕ∞} : ContDiff ℝ k (dexpJ (𝔸 := 𝔸)) :=
  contDiff_iff_contDiffAt.2 fun Z => (analyticAt_dexpJ Z).contDiffAt

omit [CompleteSpace 𝔸] in
/-- A norm bound for power series with coefficients `|d_k| ≤ 1/k!` vanishing at `k = 0`. -/
theorem norm_tsum_le_one (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ (k ! : ℝ)⁻¹) (hd0 : d 0 = 0) (Z : 𝔸)
    (hZ : ‖Z‖ ≤ 1) : ‖∑' k, d k • Z ^ k‖ ≤ 3 * ‖Z‖ := by
  have hs := summable_norm_coeff_pow d hd Z
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  have hterm : ∀ k, ‖d k • Z ^ k‖ ≤ ‖Z‖ * (1 : ℝ) ^ k / k ! := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hd0]
    · have hp : ‖Z ^ k‖ ≤ ‖Z‖ := (norm_pow_le Z k).trans (by
        calc ‖Z‖ ^ k ≤ ‖Z‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hZ hk
          _ = ‖Z‖ := pow_one _)
      calc ‖d k • Z ^ k‖ = |d k| * ‖Z ^ k‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (k ! : ℝ)⁻¹ * ‖Z‖ := mul_le_mul (hd k) hp (norm_nonneg _) (by positivity)
        _ = ‖Z‖ * (1 : ℝ) ^ k / k ! := by rw [one_pow, mul_one, div_eq_mul_inv, mul_comm]
  have hsum : Summable fun k : ℕ => ‖Z‖ * (1 : ℝ) ^ k / k ! := by
    simp_rw [mul_div_assoc]; exact (Real.summable_pow_div_factorial 1).mul_left _
  refine (hs.tsum_le_tsum hterm hsum).trans ?_
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left]
  have he : ∑' k : ℕ, (1 : ℝ) ^ k / k ! = Real.exp 1 := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [he]
  have := Real.exp_one_lt_d9
  nlinarith [norm_nonneg Z]

omit [CompleteSpace 𝔸] in
/-- A norm bound for power series with coefficients `|d_k| ≤ 1/k!` vanishing at `k = 0, 1`. -/
theorem norm_tsum_le_two (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ (k ! : ℝ)⁻¹) (hd0 : d 0 = 0)
    (hd1 : d 1 = 0) (Z : 𝔸) (hZ : ‖Z‖ ≤ 1) : ‖∑' k, d k • Z ^ k‖ ≤ 3 * ‖Z‖ ^ 2 := by
  have hs := summable_norm_coeff_pow d hd Z
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  have hterm : ∀ k, ‖d k • Z ^ k‖ ≤ ‖Z‖ ^ 2 * (1 : ℝ) ^ k / k ! := by
    intro k
    rcases lt_or_ge k 2 with hk | hk
    · interval_cases k <;> simp [hd0, hd1]
    · have hp : ‖Z ^ k‖ ≤ ‖Z‖ ^ 2 :=
        (norm_pow_le Z k).trans (pow_le_pow_of_le_one (norm_nonneg _) hZ hk)
      calc ‖d k • Z ^ k‖ = |d k| * ‖Z ^ k‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (k ! : ℝ)⁻¹ * ‖Z‖ ^ 2 := mul_le_mul (hd k) hp (norm_nonneg _) (by positivity)
        _ = ‖Z‖ ^ 2 * (1 : ℝ) ^ k / k ! := by rw [one_pow, mul_one, div_eq_mul_inv, mul_comm]
  have hsum : Summable fun k : ℕ => ‖Z‖ ^ 2 * (1 : ℝ) ^ k / k ! := by
    simp_rw [mul_div_assoc]; exact (Real.summable_pow_div_factorial 1).mul_left _
  refine (hs.tsum_le_tsum hterm hsum).trans ?_
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left]
  have he : ∑' k : ℕ, (1 : ℝ) ^ k / k ! = Real.exp 1 := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [he]
  have := Real.exp_one_lt_d9
  nlinarith [sq_nonneg ‖Z‖]

theorem jCoeff_zero : jCoeff 0 = 1 := by simp [jCoeff]

theorem jCoeff_one : jCoeff 1 = 1 / 2 := by simp [jCoeff, Nat.factorial]

/-- `‖𝒥(Z) - 1‖ ≤ 3‖Z‖` for `‖Z‖ ≤ 1`. -/
theorem norm_dexpJ_sub_one_le (Z : 𝔸) (hZ : ‖Z‖ ≤ 1) : ‖dexpJ Z - 1‖ ≤ 3 * ‖Z‖ := by
  set d : ℕ → ℝ := fun k => jCoeff k - if k = 0 then 1 else 0 with hd
  have hsum : HasSum (fun k => d k • Z ^ k) (dexpJ Z - 1) := by
    have h1 : HasSum (fun k : ℕ => if k = 0 then (1 : 𝔸) else 0) 1 := by
      convert hasSum_ite_eq 0 (1 : 𝔸) using 1
    have e : (fun k => d k • Z ^ k) =
        (fun k => jCoeff k • Z ^ k - if k = 0 then (1 : 𝔸) else 0) := by
      funext k
      by_cases hk : k = 0
      · subst hk; simp [hd, sub_smul]
      · simp [hd, hk]
    rw [e]
    exact (hasSum_dexpJ Z).sub h1
  rw [← hsum.tsum_eq]
  refine norm_tsum_le_one d (fun k => ?_) (by simp [hd, jCoeff_zero]) Z hZ
  by_cases hk : k = 0
  · subst hk; simp [hd, jCoeff_zero]
  · simp only [hd, hk, ite_false, sub_zero]
    rw [abs_of_nonneg (jCoeff_nonneg k)]; exact jCoeff_le k

/-- `‖½(1 + e^Z) - 𝒥(Z)‖ ≤ 3‖Z‖²` for `‖Z‖ ≤ 1`. -/
theorem norm_half_one_add_exp_sub_dexpJ_le (Z : 𝔸) (hZ : ‖Z‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • (1 + exp Z) - dexpJ Z‖ ≤ 3 * ‖Z‖ ^ 2 := by
  set d : ℕ → ℝ := fun k => (1 / 2 : ℝ) * (if k = 0 then 1 else 0) + (1 / 2 : ℝ) * (k ! : ℝ)⁻¹ -
    jCoeff k with hd
  have hsum : HasSum (fun k => d k • Z ^ k) ((1 / 2 : ℝ) • (1 + exp Z) - dexpJ Z) := by
    have h1 : HasSum (fun k : ℕ => if k = 0 then (1 : 𝔸) else 0) 1 := by
      convert hasSum_ite_eq 0 (1 : 𝔸) using 1
    have h2 := exp_series_hasSum_exp' (𝕂 := ℝ) Z
    have e : (fun k => d k • Z ^ k) = (fun k => (1 / 2 : ℝ) • ((if k = 0 then (1 : 𝔸) else 0) +
        (k ! : ℝ)⁻¹ • Z ^ k) - jCoeff k • Z ^ k) := by
      funext k
      by_cases hk : k = 0
      · subst hk; simp only [hd, ite_true, pow_zero, smul_add]; module
      · simp only [hd, hk, ite_false, zero_add, mul_zero]
        rw [sub_smul, smul_smul]
    rw [e]
    exact ((h1.add h2).const_smul (1 / 2 : ℝ)).sub (hasSum_dexpJ Z)
  rw [← hsum.tsum_eq]
  refine norm_tsum_le_two d (fun k => ?_) ?_ ?_ Z hZ
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hd, jCoeff_zero]; norm_num
    · have hk0 : k ≠ 0 := hk.ne'
      simp only [hd, hk0, ite_false, mul_zero, zero_add]
      have h1 := jCoeff_le k
      have h2 := jCoeff_nonneg k
      have h3 : (0 : ℝ) ≤ (k ! : ℝ)⁻¹ := by positivity
      have h4 : (k ! : ℝ)⁻¹ ≤ 2 * jCoeff k * (k + 1) := by
        unfold jCoeff
        rw [Nat.factorial_succ]; push_cast
        field_simp
        nlinarith
      rw [abs_le]; constructor <;> nlinarith
  · simp [hd, jCoeff_zero]; norm_num
  · simp [hd, jCoeff_one]

/-- On the chart `‖Z‖ ≤ 1/4`, `𝒥(Z)` is invertible with `‖𝒥(Z)⁻¹‖ ≤ 4`. -/
theorem dexpJ_isUnit_and_norm_inverse_le (Z : 𝔸) (hZ : ‖Z‖ ≤ 1 / 4) :
    IsUnit (dexpJ Z) ∧ ‖Ring.inverse (dexpJ Z)‖ ≤ 4 := by
  set t : 𝔸 := 1 - dexpJ Z with ht
  have hJ : dexpJ Z = 1 - t := by rw [ht]; abel
  have htn : ‖t‖ ≤ 3 / 4 := by
    rw [ht, norm_sub_rev]
    calc ‖dexpJ Z - 1‖ ≤ 3 * ‖Z‖ := norm_dexpJ_sub_one_le Z (by linarith)
      _ ≤ 3 / 4 := by linarith
  have ht1 : ‖t‖ < 1 := by linarith
  refine ⟨hJ ▸ (Units.oneSub t ht1).isUnit, ?_⟩
  rw [hJ, NormedRing.inverse_one_sub t ht1]
  have h := tsum_geometric_le_of_norm_lt_one t ht1
  rw [norm_one] at h
  calc ‖(↑(Units.oneSub t ht1)⁻¹ : 𝔸)‖ = ‖∑' n : ℕ, t ^ n‖ := rfl
    _ ≤ 1 - 1 + (1 - ‖t‖)⁻¹ := h
    _ ≤ 4 := by
        rw [sub_self, zero_add]
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith

/-- **`‖𝒦(Z) - I‖ ≤ 12 ‖Z‖²` on the chart `‖Z‖ ≤ 1/4`.** -/
theorem norm_halfCoth_sub_one_le (Z : 𝔸) (hZ : ‖Z‖ ≤ 1 / 4) :
    ‖halfCoth Z - 1‖ ≤ 12 * ‖Z‖ ^ 2 := by
  obtain ⟨hu, hinv⟩ := dexpJ_isUnit_and_norm_inverse_le Z hZ
  have h1 : halfCoth Z - 1 =
      Ring.inverse (dexpJ Z) * ((1 / 2 : ℝ) • (1 + exp Z) - dexpJ Z) := by
    rw [halfCoth, mul_sub, Ring.inverse_mul_cancel _ hu]
  rw [h1]
  calc ‖Ring.inverse (dexpJ Z) * ((1 / 2 : ℝ) • (1 + exp Z) - dexpJ Z)‖
      ≤ ‖Ring.inverse (dexpJ Z)‖ * ‖(1 / 2 : ℝ) • (1 + exp Z) - dexpJ Z‖ := norm_mul_le _ _
    _ ≤ 4 * (3 * ‖Z‖ ^ 2) := mul_le_mul hinv
        (norm_half_one_add_exp_sub_dexpJ_le Z (by linarith)) (norm_nonneg _) (by norm_num)
    _ = 12 * ‖Z‖ ^ 2 := by ring

theorem dexpJ_zero : dexpJ (0 : 𝔸) = 1 := by
  have h := hasSum_dexpJ (0 : 𝔸)
  have h' : HasSum (fun k : ℕ => jCoeff k • (0 : 𝔸) ^ k) 1 := by
    convert hasSum_ite_eq 0 (1 : 𝔸) using 1
    funext k
    by_cases hk : k = 0
    · subst hk; simp [jCoeff_zero]
    · simp [hk, zero_pow hk]
  exact h.unique h'

/-- `𝒦(0) = I`. -/
theorem halfCoth_zero : halfCoth (0 : 𝔸) = 1 := by
  rw [halfCoth, dexpJ_zero, Ring.inverse_one, one_mul, exp_zero]
  rw [← two_smul ℝ (1 : 𝔸), smul_smul]; norm_num

/-- `Z · 𝒥(Z) = e^Z - 1`. -/
theorem mul_dexpJ (Z : 𝔸) : Z * dexpJ Z = exp Z - 1 := by
  have h1 : HasSum (fun k => Z * (jCoeff k • Z ^ k)) (Z * dexpJ Z) := (hasSum_dexpJ Z).mul_left Z
  have h2 := exp_series_hasSum_exp' (𝕂 := ℝ) Z
  rw [← hasSum_nat_add_iff' 1] at h2
  simp only [range_one, sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul] at h2
  refine h1.unique (h2.congr_fun fun k => ?_)
  rw [mul_smul_comm, ← pow_succ', jCoeff]

/-- For real scalars `𝒦(z)(e^z - 1) = (z/2)(e^z + 1)`, i.e. `𝒦(z) = (z/2)coth(z/2)` for `z ≠ 0`. -/
theorem halfCoth_real_mul (z : ℝ) (hz : ‖z‖ ≤ 1 / 4) :
    halfCoth z * (Real.exp z - 1) = z / 2 * (Real.exp z + 1) := by
  obtain ⟨hu, -⟩ := dexpJ_isUnit_and_norm_inverse_le z hz
  have hJ : dexpJ z ≠ 0 := hu.ne_zero
  have hm := mul_dexpJ z
  rw [← Real.exp_eq_exp_ℝ] at hm
  rw [halfCoth, Ring.inverse_eq_inv', ← hm, Real.exp_eq_exp_ℝ, smul_eq_mul]
  field_simp
  ring

/-- `𝒦` is `C^∞` on the open chart `‖Z‖ < 1/4`. -/
theorem contDiffAt_halfCoth {k : WithTop ℕ∞} (Z : 𝔸) (hZ : ‖Z‖ < 1 / 4) :
    ContDiffAt ℝ k halfCoth Z := by
  obtain ⟨hu, -⟩ := dexpJ_isUnit_and_norm_inverse_le Z hZ.le
  obtain ⟨u, hu'⟩ := hu
  have hinv : ContDiffAt ℝ k (fun Z : 𝔸 => Ring.inverse (dexpJ Z)) Z := by
    have := contDiffAt_ringInverse ℝ (n := k) u
    rw [hu'] at this
    exact this.comp Z contDiff_dexpJ.contDiffAt
  have hexp : ContDiffAt ℝ k (fun Z : 𝔸 => (1 / 2 : ℝ) • (1 + exp Z)) Z :=
    (contDiffAt_const.add (exp_analytic (𝕂 := ℝ) Z).contDiffAt).const_smul _
  exact hinv.mul hexp

end

end RenewalGeometry.OperatorHalfCoth
