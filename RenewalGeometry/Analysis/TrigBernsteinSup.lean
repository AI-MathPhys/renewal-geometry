/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Bernstein's inequality in the sup norm for trigonometric polynomials

Generic infrastructure (no renewal notions) for the "Bernstein estimates" of the
Einstein–Standard-Model action-closure manuscript (proof of `thm:native-source` and of
`lem:native-tail-transfer`: a band-limited field with uniformly bounded values has
`‖∂^α z‖_∞ ≤ (CK)^{|α|} ‖z‖_∞`).

A trigonometric sum of degree `K` on the circle of period `2π` is
`q(t) = Σ_{j ∈ J} d_j e^{i m_j t}` with integer frequencies `|m_j| ≤ K` (the frequencies need not
be distinct).  Its derivative is `q'(t) = Σ_j d_j (i m_j) e^{i m_j t}`.

## Main results

* `integral_cexp_int`: `∫_{-π}^{π} e^{ijs} ds = 2π [j = 0]` for `j ∈ ℤ`.
* `integral_normSq_trigSum`: **finite Parseval**, `∫_{-π}^{π} |Σ_{m ∈ S} c_m e^{ims}|² = 2π Σ |c_m|²`.
* `kernel`: the differentiated de la Vallée-Poussin kernel `g_K(s) = Σ_{|m| ≤ 2K} i m v_K(m) e^{ims}`
  with the trapezoid `v_K = 1` on `[-K, K]`, `0` outside `(-2K, 2K)`, `1/K`-Lipschitz.
* `deriv_eq_convolution`: `q'(t) = (2π)⁻¹ ∫_{-π}^{π} q(t - s) g_K(s) ds` for every trigonometric sum
  of degree `≤ K`.
* `integral_norm_kernel_le`: `∫_{-π}^{π} |g_K| ≤ 120 π K` (weighted Cauchy–Schwarz with the weight
  `1 + K²|e^{is} - 1|²`, finite Parseval and `∫ (1 + a²s²)⁻¹ = π/a`).
* **`norm_trigDeriv_le`** (Bernstein, sup norm): if `|q| ≤ M` on `ℝ` then
  `|q'(t)| ≤ 60 K M` for every `t`.

The constant `60` is not optimal (the sharp constant is `1`); only the linear dependence on `K` is
used downstream.
-/

open MeasureTheory Complex Finset intervalIntegral
open scoped Real BigOperators

namespace RenewalGeometry.TrigBernstein

noncomputable section

/-! ### Orthogonality and finite Parseval -/

/-- `∫_{-π}^{π} e^{ijs} ds = 2π [j = 0]`. -/
theorem integral_cexp_int (j : ℤ) :
    ∫ s in (-π)..π, Complex.exp ((j : ℂ) * (s : ℂ) * I) = if j = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hj
  · subst hj
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const]
    simp only [sub_neg_eq_add, Complex.real_smul, mul_one]
    push_cast; ring
  · have hc : (j : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) I_ne_zero
    have e : (fun s : ℝ => Complex.exp ((j : ℂ) * (s : ℂ) * I)) =
        fun s : ℝ => Complex.exp (((j : ℂ) * I) * (s : ℂ)) := by
      funext s; ring_nf
    rw [e, integral_exp_mul_complex hc]
    have h2 : Complex.exp ((j : ℂ) * I * (π : ℂ)) = Complex.exp ((j : ℂ) * I * ((-π : ℝ) : ℂ)) := by
      have hp : Complex.exp ((j : ℂ) * (2 * (π : ℂ) * I)) = 1 := Complex.exp_int_mul_two_pi_mul_I j
      have : (j : ℂ) * I * (π : ℂ) = (j : ℂ) * I * ((-π : ℝ) : ℂ) + (j : ℂ) * (2 * (π : ℂ) * I) := by
        push_cast; ring
      rw [this, Complex.exp_add, hp, mul_one]
    rw [h2, sub_self, zero_div]

theorem continuous_cexp_mul (m : ℤ) : Continuous fun s : ℝ => Complex.exp ((m : ℂ) * (s : ℂ) * I) :=
  Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)

/-- Integration of a finite exponential sum: `∫_{-π}^{π} Σ_{x ∈ T} a_x e^{i f(x) s} ds
= 2π Σ_{x ∈ T, f(x) = 0} a_x`. -/
theorem integral_sum_cexp {ι : Type*} (T : Finset ι) (a : ι → ℂ) (f : ι → ℤ) :
    ∫ s in (-π)..π, ∑ x ∈ T, a x * Complex.exp ((f x : ℂ) * (s : ℂ) * I) =
      2 * π * ∑ x ∈ T, if f x = 0 then a x else 0 := by
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_cexp_int]
    split_ifs <;> ring
  · intro x _
    exact (continuous_const.mul (continuous_cexp_mul _)).intervalIntegrable _ _

/-- A finite trigonometric sum `Σ_{m ∈ S} c_m e^{ims}`. -/
def trigSum (S : Finset ℤ) (c : ℤ → ℂ) (s : ℝ) : ℂ :=
  ∑ m ∈ S, c m * Complex.exp ((m : ℂ) * (s : ℂ) * I)

theorem continuous_trigSum (S : Finset ℤ) (c : ℤ → ℂ) : Continuous (trigSum S c) :=
  continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_cexp_mul m)

theorem conj_cexp (m : ℤ) (s : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((m : ℂ) * (s : ℂ) * I)) =
      Complex.exp (-((m : ℂ) * (s : ℂ) * I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

/-- **Finite Parseval**: `∫_{-π}^{π} |Σ_{m ∈ S} c_m e^{ims}|² ds = 2π Σ_{m ∈ S} |c_m|²`. -/
theorem integral_normSq_trigSum (S : Finset ℤ) (c : ℤ → ℂ) :
    ∫ s in (-π)..π, ‖trigSum S c s‖ ^ 2 = 2 * π * ∑ m ∈ S, ‖c m‖ ^ 2 := by
  have hpt : ∀ s : ℝ, ((‖trigSum S c s‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ S ×ˢ S, c x.1 * (starRingEnd ℂ) (c x.2) *
        Complex.exp (((x.1 - x.2 : ℤ) : ℂ) * (s : ℂ) * I) := by
    intro s
    rw [Complex.ofReal_pow, ← Complex.mul_conj', trigSum, map_sum, Finset.sum_mul_sum,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    rw [map_mul, conj_cexp]
    have : Complex.exp (((m - m' : ℤ) : ℂ) * (s : ℂ) * I) =
        Complex.exp ((m : ℂ) * (s : ℂ) * I) * Complex.exp (-((m' : ℂ) * (s : ℂ) * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  have hC : (∫ s in (-π)..π, ((‖trigSum S c s‖ ^ 2 : ℝ) : ℂ)) =
      ((2 * π * ∑ m ∈ S, ‖c m‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
    rw [integral_sum_cexp, Finset.sum_product]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_eq_single m]
    · simp only [sub_self, if_true, Complex.mul_conj']
    · intro b _ hb
      have : m - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
      simp [this]
    · intro h; exact absurd hm h
  rw [intervalIntegral.integral_ofReal] at hC
  exact_mod_cast hC

/-! ### The trapezoid and the differentiated kernel -/

/-- The trapezoid `v_K(m) = max 0 (min 1 (2 - |m|/K))`. -/
def vtr (K : ℕ) (m : ℤ) : ℝ := max 0 (min 1 (2 - |(m : ℝ)| / K))

theorem vtr_nonneg (K : ℕ) (m : ℤ) : 0 ≤ vtr K m := le_max_left _ _

theorem vtr_le_one (K : ℕ) (m : ℤ) : vtr K m ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem vtr_eq_one {K : ℕ} {m : ℤ} (hm : |(m : ℝ)| ≤ K) : vtr K m = 1 := by
  unfold vtr
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  · have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have h1 : |(m : ℝ)| / K ≤ 1 := (div_le_one hK').mpr hm
    have : 1 ≤ 2 - |(m : ℝ)| / K := by linarith
    rw [min_eq_left this]; simp

theorem vtr_eq_zero {K : ℕ} (hK : 0 < K) {m : ℤ} (hm : 2 * (K : ℝ) ≤ |(m : ℝ)|) : vtr K m = 0 := by
  unfold vtr
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have : 2 - |(m : ℝ)| / K ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hK']; linarith
  exact max_eq_left ((min_le_right _ _).trans this)

theorem abs_vtr_sub_le {K : ℕ} (hK : 0 < K) (m m' : ℤ) :
    |vtr K m - vtr K m'| ≤ |(m : ℝ) - m'| / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  unfold vtr
  calc |max 0 (min 1 (2 - |(m : ℝ)| / K)) - max 0 (min 1 (2 - |(m' : ℝ)| / K))|
      = |max (min 1 (2 - |(m : ℝ)| / K)) 0 - max (min 1 (2 - |(m' : ℝ)| / K)) 0| := by
        rw [max_comm 0, max_comm 0]
    _ ≤ |min 1 (2 - |(m : ℝ)| / K) - min 1 (2 - |(m' : ℝ)| / K)| := abs_max_sub_max_le_abs _ _ _
    _ ≤ max |(1 : ℝ) - 1| |(2 - |(m : ℝ)| / K) - (2 - |(m' : ℝ)| / K)| :=
        abs_min_sub_min_le_max _ _ _ _
    _ ≤ |(m : ℝ) - m'| / K := by
        refine max_le (by simp; positivity) ?_
        have e : (2 - |(m : ℝ)| / K) - (2 - |(m' : ℝ)| / K) = -((|(m : ℝ)| - |(m' : ℝ)|) / K) := by
          ring
        rw [e, abs_neg, abs_div, abs_of_pos hK']
        exact div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub _ _) hK'.le

/-- The kernel coefficients `γ_m = i m v_K(m)`. -/
def gam (K : ℕ) (m : ℤ) : ℂ := ((m : ℝ) * vtr K m : ℝ) * I

/-- The differentiated de la Vallée-Poussin kernel `g_K(s) = Σ_{|m| ≤ 2K} i m v_K(m) e^{ims}`. -/
def kernel (K : ℕ) (s : ℝ) : ℂ := trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K)) (gam K) s

theorem continuous_kernel (K : ℕ) : Continuous (kernel K) := continuous_trigSum _ _

theorem gam_eq_zero {K : ℕ} (hK : 0 < K) {m : ℤ} (hm : m ∉ Finset.Icc (-(2 * K : ℤ)) (2 * K)) :
    gam K m = 0 := by
  have : 2 * (K : ℝ) ≤ |(m : ℝ)| := by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hm
    rcases hm with hm | hm
    · have : (m : ℝ) < -(2 * K) := by exact_mod_cast hm
      rw [abs_of_neg (by linarith)]; linarith
    · have : (2 * K : ℝ) < m := by exact_mod_cast hm
      have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
      rw [abs_of_pos (by linarith)]; linarith
  simp [gam, vtr_eq_zero hK this]

theorem norm_gam_le {K : ℕ} (hK : 0 < K) (m : ℤ) : ‖gam K m‖ ≤ 2 * K := by
  unfold gam
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (vtr_nonneg K m)]
  by_cases h : |(m : ℝ)| ≤ 2 * K
  · calc |(m : ℝ)| * vtr K m ≤ (2 * K) * 1 :=
          mul_le_mul h (vtr_le_one K m) (vtr_nonneg K m) (by positivity)
      _ = 2 * K := mul_one _
  · rw [vtr_eq_zero hK (le_of_lt (not_le.mp h)), mul_zero]; positivity

theorem norm_gam_sub_le {K : ℕ} (hK : 0 < K) {m : ℤ}
    (hm : m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K + 1)) : ‖gam K (m - 1) - gam K m‖ ≤ 4 := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have e : gam K (m - 1) - gam K m =
      ((((m - 1 : ℤ) : ℝ) * (vtr K (m - 1) - vtr K m) - vtr K m : ℝ) : ℂ) * I := by
    unfold gam; push_cast; ring
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.mem_Icc] at hm
  have hm1 : |((m - 1 : ℤ) : ℝ)| ≤ 2 * K + 1 := by
    rw [abs_le]; constructor
    · have : (-(2 * K : ℤ) : ℝ) ≤ m := by exact_mod_cast hm.1
      push_cast at this ⊢; linarith
    · have : (m : ℝ) ≤ 2 * K + 1 := by exact_mod_cast hm.2
      push_cast; linarith
  have hv := abs_vtr_sub_le hK (m - 1) m
  have hd : |(((m - 1 : ℤ) : ℝ)) - m| = 1 := by push_cast; simp
  rw [hd] at hv
  calc |((m - 1 : ℤ) : ℝ) * (vtr K (m - 1) - vtr K m) - vtr K m|
      ≤ |((m - 1 : ℤ) : ℝ)| * |vtr K (m - 1) - vtr K m| + |vtr K m| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ (2 * K + 1) * (1 / K) + 1 := by
        gcongr
        rw [abs_of_nonneg (vtr_nonneg K m)]; exact vtr_le_one K m
    _ ≤ 4 := by
        rw [mul_one_div, add_div, mul_div_assoc, div_self (by positivity)]
        have : 1 / (K : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hK'
        linarith

/-! ### The kernel identity -/

/-- `(2π)⁻¹ ∫_{-π}^{π} e^{ij(t-s)} g_K(s) ds = i j e^{ijt}` for `|j| ≤ K`. -/
theorem integral_cexp_mul_kernel {K : ℕ} {j : ℤ} (hj : |(j : ℝ)| ≤ K) (t : ℝ) :
    ∫ s in (-π)..π, Complex.exp ((j : ℂ) * ((t - s : ℝ) : ℂ) * I) * kernel K s =
      2 * π * ((j : ℂ) * I * Complex.exp ((j : ℂ) * (t : ℂ) * I)) := by
  have hpt : ∀ s : ℝ, Complex.exp ((j : ℂ) * ((t - s : ℝ) : ℂ) * I) * kernel K s =
      ∑ m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K), (Complex.exp ((j : ℂ) * (t : ℂ) * I) * gam K m) *
        Complex.exp (((m - j : ℤ) : ℂ) * (s : ℂ) * I) := by
    intro s
    rw [kernel, trigSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : Complex.exp ((j : ℂ) * ((t - s : ℝ) : ℂ) * I) * Complex.exp ((m : ℂ) * (s : ℂ) * I) =
        Complex.exp ((j : ℂ) * (t : ℂ) * I) * Complex.exp (((m - j : ℤ) : ℂ) * (s : ℂ) * I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    calc Complex.exp ((j : ℂ) * ((t - s : ℝ) : ℂ) * I) * (gam K m * Complex.exp ((m : ℂ) * (s : ℂ) * I))
        = gam K m * (Complex.exp ((j : ℂ) * ((t - s : ℝ) : ℂ) * I) *
            Complex.exp ((m : ℂ) * (s : ℂ) * I)) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [hpt]
  rw [integral_sum_cexp]
  have hjmem : j ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K) := by
    rw [Finset.mem_Icc]
    rw [abs_le] at hj
    constructor
    · have : (-(2 * K : ℤ) : ℝ) ≤ j := by push_cast; linarith [hj.1, (Nat.cast_nonneg K : (0:ℝ) ≤ K)]
      exact_mod_cast this
    · have : (j : ℝ) ≤ (2 * K : ℤ) := by push_cast; linarith [hj.2, (Nat.cast_nonneg K : (0:ℝ) ≤ K)]
      exact_mod_cast this
  rw [Finset.sum_eq_single j]
  · simp only [sub_self, if_true, gam, vtr_eq_one hj, mul_one]
    push_cast; ring
  · intro b _ hb
    have : b - j ≠ 0 := sub_ne_zero.mpr hb
    simp [this]
  · intro h; exact absurd hjmem h

/-- A trigonometric sum with integer frequencies (not necessarily distinct):
`q(t) = Σ_{x ∈ J} d_x e^{i m_x t}`. -/
def tsum' {J : Type*} [Fintype J] (d : J → ℂ) (m : J → ℤ) (t : ℝ) : ℂ :=
  ∑ x, d x * Complex.exp ((m x : ℂ) * (t : ℂ) * I)

/-- Its derivative `q'(t) = Σ_x d_x (i m_x) e^{i m_x t}`. -/
def tsumDeriv {J : Type*} [Fintype J] (d : J → ℂ) (m : J → ℤ) (t : ℝ) : ℂ :=
  ∑ x, d x * ((m x : ℂ) * I) * Complex.exp ((m x : ℂ) * (t : ℂ) * I)

theorem continuous_tsum' {J : Type*} [Fintype J] (d : J → ℂ) (m : J → ℤ) :
    Continuous (tsum' d m) :=
  continuous_finsetSum _ fun x _ => continuous_const.mul (continuous_cexp_mul _)

theorem hasDerivAt_tsum' {J : Type*} [Fintype J] (d : J → ℂ) (m : J → ℤ) (t : ℝ) :
    HasDerivAt (tsum' d m) (tsumDeriv d m t) t := by
  unfold tsum' tsumDeriv
  refine HasDerivAt.fun_sum fun x _ => ?_
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id (t : ℂ)).comp_ofReal
  have h1 : HasDerivAt (fun s : ℝ => (m x : ℂ) * (s : ℂ) * I) ((m x : ℂ) * 1 * I) t :=
    (h0.const_mul (m x : ℂ)).mul_const I
  have h2 := h1.cexp.const_mul (d x)
  exact h2.congr_deriv (by ring)

/-- **The convolution identity**: `q'(t) = (2π)⁻¹ ∫_{-π}^{π} q(t - s) g_K(s) ds` for every
trigonometric sum of degree `≤ K`. -/
theorem deriv_eq_convolution {J : Type*} [Fintype J] {K : ℕ} (d : J → ℂ) (m : J → ℤ)
    (hm : ∀ x, |(m x : ℝ)| ≤ K) (t : ℝ) :
    tsumDeriv d m t = (2 * π : ℂ)⁻¹ * ∫ s in (-π)..π, tsum' d m (t - s) * kernel K s := by
  have hpt : ∀ s : ℝ, tsum' d m (t - s) * kernel K s =
      ∑ x, d x * (Complex.exp ((m x : ℂ) * ((t - s : ℝ) : ℂ) * I) * kernel K s) := by
    intro s; rw [tsum', Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum (fun x _ => ?_)]
  · simp_rw [intervalIntegral.integral_const_mul, integral_cexp_mul_kernel (hm _) t]
    rw [Finset.mul_sum, tsumDeriv]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    field_simp
  · refine (continuous_const.mul ((Complex.continuous_exp.comp ?_).mul
      (continuous_kernel K))).intervalIntegrable _ _
    exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.sub continuous_id))).mul continuous_const

/-! ### The `L¹` bound of the kernel -/

/-- `|e^{is} - 1|² = 2 - 2 cos s ≥ 4 s²/π²` for `|s| ≤ π` (Jordan's inequality). -/
theorem sq_div_le_two_sub_two_cos {s : ℝ} (hs : |s| ≤ π) : 4 * s ^ 2 / π ^ 2 ≤ 2 - 2 * Real.cos s := by
  have hc : 2 - 2 * Real.cos s = 4 * Real.sin (|s| / 2) ^ 2 := by
    have h1 : Real.cos s = Real.cos |s| := (Real.cos_abs s).symm
    have h2 : Real.cos |s| = 1 - 2 * Real.sin (|s| / 2) ^ 2 := by
      have e : Real.cos |s| = Real.cos (2 * (|s| / 2)) := by congr 1; ring
      rw [e, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (|s| / 2)]
    rw [h1, h2]; ring
  rw [hc]
  have h0 : 0 ≤ |s| / 2 := by positivity
  have h1 : |s| / 2 ≤ π / 2 := by linarith
  have hj := Real.mul_le_sin h0 h1
  have hpos : 0 ≤ 2 / π * (|s| / 2) := by positivity
  have : (|s| / π) ^ 2 ≤ Real.sin (|s| / 2) ^ 2 := by
    have e : |s| / π = 2 / π * (|s| / 2) := by field_simp
    rw [e]; exact pow_le_pow_left₀ hpos hj 2
  have hs2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  rw [hs2, div_pow] at *
  have : 4 * |s| ^ 2 / π ^ 2 = 4 * (|s| ^ 2 / π ^ 2) := by ring
  rw [this]; nlinarith

theorem norm_cexp_sub_one_sq (s : ℝ) :
    ‖Complex.exp ((1 : ℤ) * (s : ℂ) * I) - 1‖ ^ 2 = 2 - 2 * Real.cos s := by
  have : Complex.exp ((1 : ℤ) * (s : ℂ) * I) = (Real.cos s : ℂ) + (Real.sin s : ℂ) * I := by
    push_cast; rw [one_mul, Complex.exp_mul_I]
  rw [this, ← Complex.normSq_eq_norm_sq]
  have e : (Real.cos s : ℂ) + (Real.sin s : ℂ) * I - 1 = ((Real.cos s - 1 : ℝ) : ℂ) +
      (Real.sin s : ℂ) * I := by push_cast; ring
  rw [e, Complex.normSq_add_mul_I]
  nlinarith [Real.sin_sq_add_cos_sq s]

/-- `∫_{-π}^{π} (1 + a² s²)⁻¹ ds ≤ π/a`. -/
theorem integral_inv_one_add_sq_le {a : ℝ} (ha : 0 < a) :
    ∫ s in (-π)..π, (1 + (a * s) ^ 2)⁻¹ ≤ π / a := by
  have hint : Integrable (fun s : ℝ => (1 + (a * s) ^ 2)⁻¹) := by
    have := (integrable_inv_one_add_sq).comp_mul_left' ha.ne'
    simpa using this
  have hall : ∫ s, (1 + (a * s) ^ 2)⁻¹ = π / a := by
    have := Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) a
    rw [this, integral_univ_inv_one_add_sq, abs_inv, abs_of_pos ha, smul_eq_mul]
    ring
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← hall]
  refine setIntegral_le_integral hint (Filter.Eventually.of_forall fun s => ?_)
  positivity

/-- **The `L¹` bound of the kernel**: `∫_{-π}^{π} |g_K| ≤ 120 π K` for `K ≥ 1`. -/
theorem integral_norm_kernel_le {K : ℕ} (hK : 0 < K) :
    ∫ s in (-π)..π, ‖kernel K s‖ ≤ 120 * π * K := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  set w : ℝ → ℝ := fun s => 1 + (K : ℝ) ^ 2 * (2 - 2 * Real.cos s) with hw
  have hw0 : ∀ s, 1 ≤ w s := fun s => by
    have : 0 ≤ 2 - 2 * Real.cos s := by linarith [Real.cos_le_one s]
    simp only [hw]; nlinarith
  set ε : ℝ := 1 / (K : ℝ) ^ 2 with hε
  have hε0 : 0 < ε := by positivity
  -- pointwise AM–GM
  have hpt : ∀ s, ‖kernel K s‖ ≤
      (ε * (‖kernel K s‖ ^ 2 + (K : ℝ) ^ 2 * ‖trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K + 1))
          (fun m => gam K (m - 1) - gam K m) s‖ ^ 2) + 1 / (ε * w s)) / 2 := by
    intro s
    have hshift : trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K + 1)) (fun m => gam K (m - 1) - gam K m) s =
        (Complex.exp ((1 : ℤ) * (s : ℂ) * I) - 1) * kernel K s := by
      simp only [trigSum, kernel]
      rw [sub_mul, one_mul, Finset.mul_sum]
      simp only [sub_mul, Finset.sum_sub_distrib]
      have hz : ∀ m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K + 1),
          m ∉ Finset.Icc (-(2 * K : ℤ) + 1) (2 * K + 1) →
            gam K (m - 1) * Complex.exp ((m : ℂ) * (s : ℂ) * I) = 0 := by
        intro m hm hm'
        rw [Finset.mem_Icc] at hm hm'
        have : m = -(2 * K : ℤ) := by omega
        subst this
        rw [gam_eq_zero hK (by rw [Finset.mem_Icc]; omega), zero_mul]
      have h1 : ∑ m ∈ Finset.Icc (-(2 * K : ℤ) + 1) (2 * K + 1),
          gam K (m - 1) * Complex.exp ((m : ℂ) * (s : ℂ) * I) =
          ∑ m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K + 1),
            gam K (m - 1) * Complex.exp ((m : ℂ) * (s : ℂ) * I) :=
        Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl) hz
      have hz' : ∀ m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K + 1), m ∉ Finset.Icc (-(2 * K : ℤ)) (2 * K) →
          gam K m * Complex.exp ((m : ℂ) * (s : ℂ) * I) = 0 := by
        intro m _ hm'; rw [gam_eq_zero hK hm', zero_mul]
      have h2 : ∑ m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K),
          gam K m * Complex.exp ((m : ℂ) * (s : ℂ) * I) =
          ∑ m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K + 1),
            gam K m * Complex.exp ((m : ℂ) * (s : ℂ) * I) :=
        Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) hz'
      rw [← h1, ← h2, ← Finset.map_add_right_Icc _ _ (1 : ℤ), Finset.sum_map]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [addRightEmbedding_apply, add_sub_cancel_right]
      rw [show Complex.exp ((1 : ℤ) * (s : ℂ) * I) * (gam K m * Complex.exp ((m : ℂ) * (s : ℂ) * I)) =
        gam K m * (Complex.exp ((m : ℂ) * (s : ℂ) * I) * Complex.exp ((1 : ℤ) * (s : ℂ) * I)) by ring,
        ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hshift, norm_mul, mul_pow, norm_cexp_sub_one_sq]
    set x := ‖kernel K s‖
    have hx : 0 ≤ x := norm_nonneg _
    have hws : w s = 1 + (K : ℝ) ^ 2 * (2 - 2 * Real.cos s) := rfl
    have hwpos : 0 < w s := lt_of_lt_of_le one_pos (hw0 s)
    have key : x ≤ (ε * x ^ 2 * w s + 1 / (ε * w s)) / 2 := by
      have h : 0 ≤ (ε * x * w s - 1) ^ 2 / (2 * ε * w s) := by positivity
      have e : (ε * x ^ 2 * w s + 1 / (ε * w s)) / 2 - x = (ε * x * w s - 1) ^ 2 / (2 * ε * w s) := by
        field_simp; ring
      linarith
    calc x ≤ (ε * x ^ 2 * w s + 1 / (ε * w s)) / 2 := key
      _ = _ := by rw [hws]; ring
  -- integrate
  have hc1 : Continuous fun s => ‖kernel K s‖ := (continuous_kernel K).norm
  have hcw : Continuous w := continuous_const.add (continuous_const.mul
    (continuous_const.sub (continuous_const.mul Real.continuous_cos)))
  have hc2 : Continuous fun s => (ε * (‖kernel K s‖ ^ 2 + (K : ℝ) ^ 2 *
      ‖trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K + 1)) (fun m => gam K (m - 1) - gam K m) s‖ ^ 2) +
        1 / (ε * w s)) / 2 := by
    refine ((continuous_const.mul ((hc1.pow 2).add (continuous_const.mul
      ((continuous_trigSum _ _).norm.pow 2)))).add ?_).div_const _
    exact continuous_const.div (continuous_const.mul hcw) fun s =>
      (mul_pos hε0 (lt_of_lt_of_le one_pos (hw0 s))).ne'
  have hπ0 : -π ≤ π := by linarith [Real.pi_pos]
  refine (intervalIntegral.integral_mono_on hπ0 (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _) (fun s _ => hpt s)).trans ?_
  -- evaluate the right side
  have hP1 : ∫ s in (-π)..π, ‖kernel K s‖ ^ 2 ≤ 2 * π * ((4 * K + 1) * (2 * K) ^ 2) := by
    rw [show (fun s => ‖kernel K s‖ ^ 2) = fun s =>
      ‖trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K)) (gam K) s‖ ^ 2 from rfl,
      integral_normSq_trigSum]
    gcongr
    calc ∑ m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K), ‖gam K m‖ ^ 2
        ≤ ∑ _m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K), (2 * (K : ℝ)) ^ 2 :=
          Finset.sum_le_sum fun m _ => pow_le_pow_left₀ (norm_nonneg _) (norm_gam_le hK m) 2
      _ = (4 * K + 1) * (2 * K) ^ 2 := by
          rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
          congr 1
          have : (2 * (K : ℤ) + 1 - -(2 * K)) = ((4 * K + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [this, Int.toNat_natCast]; push_cast; ring
  have hP2 : ∫ s in (-π)..π, ‖trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K + 1))
      (fun m => gam K (m - 1) - gam K m) s‖ ^ 2 ≤ 2 * π * ((4 * K + 2) * 16) := by
    rw [integral_normSq_trigSum]
    gcongr
    calc ∑ m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K + 1), ‖gam K (m - 1) - gam K m‖ ^ 2
        ≤ ∑ _m ∈ Finset.Icc (-(2 * K : ℤ)) (2 * K + 1), (4 : ℝ) ^ 2 :=
          Finset.sum_le_sum fun m hm => pow_le_pow_left₀ (norm_nonneg _) (norm_gam_sub_le hK hm) 2
      _ = (4 * K + 2) * 16 := by
          rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
          have : (2 * (K : ℤ) + 1 + 1 - -(2 * K)) = ((4 * K + 2 : ℕ) : ℤ) := by push_cast; ring
          rw [this, Int.toNat_natCast]; push_cast; ring
  have hP3 : ∫ s in (-π)..π, 1 / (ε * w s) ≤ (1 / ε) * (π / (2 * K / π)) := by
    have hle : ∀ s ∈ Set.Icc (-π) π, 1 / (ε * w s) ≤ (1 / ε) * (1 + (2 * K / π * s) ^ 2)⁻¹ := by
      intro s hs
      have habs : |s| ≤ π := abs_le.mpr ⟨hs.1, hs.2⟩
      have hj := sq_div_le_two_sub_two_cos habs
      have hpos : 0 < 1 + (2 * K / π * s) ^ 2 := by positivity
      have hwle : 1 + (2 * K / π * s) ^ 2 ≤ w s := by
        simp only [hw]
        have : (2 * K / π * s) ^ 2 = (K : ℝ) ^ 2 * (4 * s ^ 2 / π ^ 2) := by
          field_simp; ring
        rw [this]; gcongr
      calc 1 / (ε * w s) = (1 / ε) * (w s)⁻¹ := by
            have := lt_of_lt_of_le one_pos (hw0 s); field_simp
        _ ≤ (1 / ε) * (1 + (2 * K / π * s) ^ 2)⁻¹ := by gcongr
    have hcA : Continuous fun s : ℝ => 1 / (ε * w s) :=
      continuous_const.div (continuous_const.mul hcw) fun s =>
        (mul_pos hε0 (lt_of_lt_of_le one_pos (hw0 s))).ne'
    have hcB : Continuous fun s : ℝ => (1 / ε) * (1 + (2 * K / π * s) ^ 2)⁻¹ :=
      continuous_const.mul ((continuous_const.add ((continuous_const.mul
        continuous_id).pow 2)).inv₀ fun s => (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')
    have hint : ∫ s in (-π)..π, 1 / (ε * w s) ≤
        ∫ s in (-π)..π, (1 / ε) * (1 + (2 * K / π * s) ^ 2)⁻¹ :=
      intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
        (hcA.intervalIntegrable _ _) (hcB.intervalIntegrable _ _) hle
    refine hint.trans ?_
    rw [intervalIntegral.integral_const_mul]
    gcongr
    exact integral_inv_one_add_sq_le (by positivity)
  have hcomb : ∫ s in (-π)..π, (ε * (‖kernel K s‖ ^ 2 + (K : ℝ) ^ 2 *
      ‖trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K + 1)) (fun m => gam K (m - 1) - gam K m) s‖ ^ 2) +
        1 / (ε * w s)) / 2 =
      (ε * ((∫ s in (-π)..π, ‖kernel K s‖ ^ 2) + (K : ℝ) ^ 2 * ∫ s in (-π)..π,
        ‖trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K + 1)) (fun m => gam K (m - 1) - gam K m) s‖ ^ 2) +
        ∫ s in (-π)..π, 1 / (ε * w s)) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
    · exact (hc1.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul ((continuous_trigSum _ _).norm.pow 2)).intervalIntegrable _ _
    · exact (continuous_const.mul ((hc1.pow 2).add (continuous_const.mul
        ((continuous_trigSum _ _).norm.pow 2)))).intervalIntegrable _ _
    · exact (continuous_const.div (continuous_const.mul hcw) fun s =>
        (mul_pos hε0 (lt_of_lt_of_le one_pos (hw0 s))).ne').intervalIntegrable _ _
  rw [hcomb]
  have hπ : 0 < π := Real.pi_pos
  have hA : ε * ((∫ s in (-π)..π, ‖kernel K s‖ ^ 2) + (K : ℝ) ^ 2 * ∫ s in (-π)..π,
      ‖trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K + 1)) (fun m => gam K (m - 1) - gam K m) s‖ ^ 2) ≤
      ε * (2 * π * ((4 * K + 1) * (2 * K) ^ 2) + (K : ℝ) ^ 2 * (2 * π * ((4 * K + 2) * 16))) := by
    gcongr
  have hB : (1 / ε) * (π / (2 * K / π)) = π ^ 2 * K / 2 := by
    simp only [hε]; field_simp
  have hA' : ε * (2 * π * ((4 * K + 1) * (2 * K) ^ 2) + (K : ℝ) ^ 2 * (2 * π * ((4 * K + 2) * 16))) =
      2 * π * (16 * K + 4 + 64 * K + 32) := by
    simp only [hε]; field_simp; ring
  have hπ4 : π < 4 := Real.pi_lt_four
  have : (ε * ((∫ s in (-π)..π, ‖kernel K s‖ ^ 2) + (K : ℝ) ^ 2 * ∫ s in (-π)..π,
      ‖trigSum (Finset.Icc (-(2 * K : ℤ)) (2 * K + 1)) (fun m => gam K (m - 1) - gam K m) s‖ ^ 2) +
        ∫ s in (-π)..π, 1 / (ε * w s)) / 2 ≤
      (2 * π * (16 * K + 4 + 64 * K + 32) + π ^ 2 * K / 2) / 2 := by
    rw [← hA', ← hB]; gcongr
  refine this.trans ?_
  nlinarith [mul_pos hπ hK0]

/-! ### Bernstein's inequality -/

/-- **Bernstein's inequality in the sup norm** (crude constant): a trigonometric sum
`q(t) = Σ_x d_x e^{i m_x t}` of degree `≤ K` (`|m_x| ≤ K`) with `|q| ≤ M` on `ℝ` has
`|q'(t)| ≤ 60 K M` for every `t`. -/
theorem norm_trigDeriv_le {J : Type*} [Fintype J] {K : ℕ} (d : J → ℂ) (m : J → ℤ)
    (hm : ∀ x, |(m x : ℝ)| ≤ K) {M : ℝ} (hM : ∀ s, ‖tsum' d m s‖ ≤ M) (t : ℝ) :
    ‖tsumDeriv d m t‖ ≤ 60 * K * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have : tsumDeriv d m t = 0 := by
      unfold tsumDeriv
      refine Finset.sum_eq_zero fun x _ => ?_
      have : (m x : ℝ) = 0 := by have := hm x; simp at this; exact_mod_cast this
      have h' : (m x : ℂ) = 0 := by exact_mod_cast this
      simp [h']
    rw [this, norm_zero]; simp
  rw [deriv_eq_convolution d m hm t, norm_mul]
  have hπ : 0 < π := Real.pi_pos
  have hc : Continuous fun s : ℝ => tsum' d m (t - s) * kernel K s :=
    ((continuous_tsum' d m).comp (continuous_const.sub continuous_id)).mul (continuous_kernel K)
  have h1 : ‖∫ s in (-π)..π, tsum' d m (t - s) * kernel K s‖ ≤ ∫ s in (-π)..π, M * ‖kernel K s‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans ?_
    refine intervalIntegral.integral_mono_on (by linarith) (hc.norm.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_kernel K).norm).intervalIntegrable _ _) fun s _ => ?_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  rw [intervalIntegral.integral_const_mul] at h1
  have h2 := integral_norm_kernel_le hK
  have hn : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv]; congr 1; rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn]
  calc (2 * π)⁻¹ * ‖∫ s in (-π)..π, tsum' d m (t - s) * kernel K s‖
      ≤ (2 * π)⁻¹ * (M * (120 * π * K)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hM0)
    _ = 60 * K * M := by field_simp; ring

end

end RenewalGeometry.TrigBernstein
