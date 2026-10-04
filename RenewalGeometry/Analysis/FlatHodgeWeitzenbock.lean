/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevTorusBridge
import RenewalGeometry.Analysis.SobolevLocalRellich

/-!
# The flat Weitzenböck (Hodge) identity for compactly supported `W^{1,2}` one-forms

Generic infrastructure (no renewal notions) for `lem:critical-Coulomb-Hodge` of the
Einstein–Standard-Model action-closure manuscript.

A (complex) one-form on `ℝ^ι` is a family `w ν : ℝ^ι → ℂ`; its weak gradient is
`g ν μ = ∂_μ w_ν` (`MemW12 univ (w ν) (g ν)`).  Its exterior derivative and codifferential (flat
metric) are `(dw)_{μν} = ∂_μ w_ν - ∂_ν w_μ = g ν μ - g μ ν` and `-d^*w = Σ_μ ∂_μ w_μ`.

* `lagrange_identity` (fibre algebra): for `a ∈ ℝ^ι`, `W ∈ ℂ^ι`,
  `|a|² |W|² = ½ Σ_{μν} |a_μ W_ν - a_ν W_μ|² + |Σ_μ a_μ W_μ|²`;
* `mFourierCoeff_sub`, `mFourierCoeff_finset_sum`: linearity of torus Fourier coefficients;
* `weitzenbock_flat` (**flat Weitzenböck / Plancherel identity**): if `w ∈ W^{1,2}(ℝ^ι)` and its
  gradient vanish off a ball, then
  `Σ_{μν} ‖∂_μ w_ν‖²_{L²} = ½ Σ_{μν} ‖(dw)_{μν}‖²_{L²} + ‖d^*w‖²_{L²}`.
  Proof: periodise to the flat torus (`SobolevTorusBridge.lean`), use the Fourier rule
  `(∂_μ w_ν)^(n) = (2πi n_μ/L) ŵ_ν(n)` and Parseval, and apply the Lagrange identity to every
  Fourier mode;
* `eLpNorm_grad_le_d_dstar` (**Hodge estimate for compactly supported forms**): every partial
  derivative is bounded by the exterior derivative and the codifferential:
  `‖∂_μ w_ν‖_{L²} ≤ Σ_{μ'ν'} ‖(dw)_{μ'ν'}‖_{L²} + ‖d^*w‖_{L²}`.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal ContDiff Real ComplexConjugate

noncomputable section

namespace RenewalGeometry.SobolevOpen

open TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Fibre algebra -/

theorem sq_norm_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

/-- **Lagrange identity** for a real covector and a complex vector:
`|a|²|W|² = ½ Σ_{μν} |a_μ W_ν - a_ν W_μ|² + |Σ_μ a_μ W_μ|²`. -/
theorem lagrange_identity (a : ι → ℝ) (W : ι → ℂ) :
    ∑ μ, ∑ ν, a μ ^ 2 * ‖W ν‖ ^ 2 =
      (1 / 2) * ∑ μ, ∑ ν, ‖(a μ : ℂ) * W ν - (a ν : ℂ) * W μ‖ ^ 2 +
        ‖∑ μ, (a μ : ℂ) * W μ‖ ^ 2 := by
  have h1 : ∀ μ ν, ‖(a μ : ℂ) * W ν - (a ν : ℂ) * W μ‖ ^ 2 =
      a μ ^ 2 * ‖W ν‖ ^ 2 + a ν ^ 2 * ‖W μ‖ ^ 2 - 2 * (a μ * a ν * (W ν * conj (W μ)).re) := by
    intro μ ν
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have h2 : ‖∑ μ, (a μ : ℂ) * W μ‖ ^ 2 = ∑ μ, ∑ ν, a μ * a ν * (W ν * conj (W μ)).re := by
    rw [sq_norm_eq_re_mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  have h3 : ∑ μ, ∑ ν, a ν ^ 2 * ‖W μ‖ ^ 2 = ∑ μ, ∑ ν, a μ ^ 2 * ‖W ν‖ ^ 2 := Finset.sum_comm
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h3, h2]
  ring

/-! ### Linearity of torus Fourier coefficients -/

theorem integrable_mFourier_smul {f : UnitAddTorus ι → ℂ} (hf : Integrable f) (n : ι → ℤ) :
    Integrable (fun t => mFourier (-n) t • f t) := by
  refine hf.norm.mono' ((mFourier (-n)).continuous.aestronglyMeasurable.smul hf.1)
    (Eventually.of_forall fun t => ?_)
  rw [norm_smul]
  have : ‖mFourier (-n) t‖ ≤ 1 :=
    ((mFourier (-n)).norm_coe_le_norm t).trans (le_of_eq mFourier_norm)
  simpa using mul_le_mul_of_nonneg_right this (norm_nonneg (f t))

theorem mFourierCoeff_sub {f h : UnitAddTorus ι → ℂ} (hf : Integrable f) (hh : Integrable h)
    (n : ι → ℤ) :
    mFourierCoeff (fun t => f t - h t) n = mFourierCoeff f n - mFourierCoeff h n := by
  unfold mFourierCoeff
  simp only [smul_sub]
  exact integral_sub (integrable_mFourier_smul hf n) (integrable_mFourier_smul hh n)

theorem mFourierCoeff_finset_sum {κ : Type*} (s : Finset κ) {f : κ → UnitAddTorus ι → ℂ}
    (hf : ∀ k, Integrable (f k)) (n : ι → ℤ) :
    mFourierCoeff (fun t => ∑ k ∈ s, f k t) n = ∑ k ∈ s, mFourierCoeff (f k) n := by
  unfold mFourierCoeff
  simp only [Finset.smul_sum]
  exact integral_finset_sum s fun k _ => integrable_mFourier_smul (hf k) n

/-! ### The Weitzenböck identity -/

/-- Parseval for a periodisation, in whole-space units:
`Σ_n |(periodize f)^(n)|² = L^{-d} ‖f‖²_{L²}`. -/
theorem hasSum_sq_coeff_periodize {R : ℝ} (hR : 0 ≤ R) {f : (ι → ℝ) → ℂ}
    (hf : MemLp f 2 volume) (hf0 : ∀ x, R < ‖x‖ → f x = 0) :
    HasSum (fun n => ‖mFourierCoeff (periodize R f) n‖ ^ 2)
      ((cubeSide R ^ Fintype.card ι)⁻¹ * ∫ x, ‖f x‖ ^ 2) := by
  rw [← integral_sq_periodize hR hf0]
  exact hasSum_sq_mFourierCoeff_of_memLp (memLp_periodize hR hf)

theorem integrable_periodize {R : ℝ} (hR : 0 ≤ R) {f : (ι → ℝ) → ℂ} (hf : MemLp f 2 volume) :
    Integrable (periodize R f) :=
  (memLp_periodize hR hf).integrable one_le_two

/-- **Flat Weitzenböck identity.**  Let `w = (w_ν)` be a one-form on `ℝ^ι` with components in
`W^{1,2}(ℝ^ι)` (weak gradients `g ν μ = ∂_μ w_ν`), all vanishing off the ball of radius `R`.
Then `Σ_{μν} ‖∂_μ w_ν‖²_{L²} = ½ Σ_{μν} ‖∂_μ w_ν - ∂_ν w_μ‖²_{L²} + ‖Σ_μ ∂_μ w_μ‖²_{L²}`, i.e.
`‖∇w‖² = ‖dw‖² + ‖d^*w‖²` (each unordered pair `μ < ν` counted once in `‖dw‖²`). -/
theorem weitzenbock_flat {R : ℝ} (hR : 0 ≤ R) {w : ι → (ι → ℝ) → ℂ}
    {g : ι → ι → (ι → ℝ) → ℂ} (hW : ∀ ν, MemW12 univ (w ν) (g ν))
    (hw0 : ∀ ν x, R < ‖x‖ → w ν x = 0) (hg0 : ∀ ν μ x, R < ‖x‖ → g ν μ x = 0) :
    ∑ μ, ∑ ν, (∫ x, ‖g ν μ x‖ ^ 2) =
      (1 / 2) * ∑ μ, ∑ ν, (∫ x, ‖g ν μ x - g μ ν x‖ ^ 2) + ∫ x, ‖∑ μ, g μ μ x‖ ^ 2 := by
  set L := cubeSide R
  set κ : ℝ := (L ^ Fintype.card ι)⁻¹
  have hκ : κ ≠ 0 := inv_ne_zero (pow_ne_zero _ (cubeSide_pos hR).ne')
  have hw2 : ∀ ν, MemLp (w ν) 2 volume := fun ν => by simpa using (hW ν).memLp
  have hg2 : ∀ ν μ, MemLp (g ν μ) 2 volume := fun ν μ => by simpa using (hW ν).memLp_grad μ
  have hloc : ∀ ν, LocallyIntegrable (w ν) volume := fun ν =>
    (hw2 ν).locallyIntegrable (by norm_num)
  have hlocg : ∀ ν μ, LocallyIntegrable (g ν μ) volume := fun ν μ =>
    (hg2 ν μ).locallyIntegrable (by norm_num)
  set Wc : ι → (ι → ℤ) → ℂ := fun ν n => mFourierCoeff (periodize R (w ν)) n
  set a : (ι → ℤ) → ι → ℝ := fun n μ => 2 * π * (n μ : ℝ) / L
  have hrule : ∀ ν μ n, mFourierCoeff (periodize R (g ν μ)) n =
      Complex.I * ((a n μ : ℝ) : ℂ) * Wc ν n := by
    intro ν μ n
    rw [mFourierCoeff_periodize_weak hR ((hW ν).weak μ) (hloc ν) (hlocg ν μ) (hw0 ν) (hg0 ν μ) n]
    simp only [a, Wc]
    push_cast
    ring
  have hint : ∀ ν μ, Integrable (periodize R (g ν μ)) := fun ν μ =>
    integrable_periodize hR (hg2 ν μ)
  have hcurl : ∀ μ ν n, mFourierCoeff (periodize R (fun x => g ν μ x - g μ ν x)) n =
      Complex.I * ((a n μ : ℂ) * Wc ν n - (a n ν : ℂ) * Wc μ n) := by
    intro μ ν n
    show mFourierCoeff (fun t => periodize R (g ν μ) t - periodize R (g μ ν) t) n = _
    rw [mFourierCoeff_sub (hint ν μ) (hint μ ν), hrule, hrule]
    ring
  have hdiv : ∀ n, mFourierCoeff (periodize R (fun x => ∑ μ, g μ μ x)) n =
      Complex.I * ∑ μ, (a n μ : ℂ) * Wc μ n := by
    intro n
    show mFourierCoeff (fun t => ∑ μ, periodize R (g μ μ) t) n = _
    rw [mFourierCoeff_finset_sum _ (fun μ => hint μ μ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hrule]; ring
  -- the two `HasSum`s
  have hA : HasSum (fun n => ∑ μ, ∑ ν, ‖mFourierCoeff (periodize R (g ν μ)) n‖ ^ 2)
      (∑ μ, ∑ ν, κ * ∫ x, ‖g ν μ x‖ ^ 2) :=
    hasSum_sum fun μ _ => hasSum_sum fun ν _ =>
      hasSum_sq_coeff_periodize hR (hg2 ν μ) (hg0 ν μ)
  have hc2 : ∀ ν μ, MemLp (fun x => g ν μ x - g μ ν x) 2 volume := fun ν μ =>
    (hg2 ν μ).sub (hg2 μ ν)
  have hd2 : MemLp (fun x => ∑ μ, g μ μ x) 2 volume :=
    memLp_finset_sum _ fun μ _ => hg2 μ μ
  have hB1 : ∀ μ ν, HasSum
      (fun n => ‖mFourierCoeff (periodize R (fun x => g ν μ x - g μ ν x)) n‖ ^ 2)
      (κ * ∫ x, ‖g ν μ x - g μ ν x‖ ^ 2) := fun μ ν =>
    hasSum_sq_coeff_periodize hR (hc2 ν μ) fun x hx => by simp [hg0 ν μ x hx, hg0 μ ν x hx]
  have hB2 : HasSum (fun n => ‖mFourierCoeff (periodize R (fun x => ∑ μ, g μ μ x)) n‖ ^ 2)
      (κ * ∫ x, ‖∑ μ, g μ μ x‖ ^ 2) :=
    hasSum_sq_coeff_periodize hR hd2 fun x hx => by simp [hg0 _ _ x hx]
  have hB : HasSum (fun n => (1 / 2) * ∑ μ, ∑ ν,
        ‖mFourierCoeff (periodize R (fun x => g ν μ x - g μ ν x)) n‖ ^ 2 +
        ‖mFourierCoeff (periodize R (fun x => ∑ μ, g μ μ x)) n‖ ^ 2)
      ((1 / 2) * ∑ μ, ∑ ν, κ * (∫ x, ‖g ν μ x - g μ ν x‖ ^ 2) +
        κ * ∫ x, ‖∑ μ, g μ μ x‖ ^ 2) :=
    ((hasSum_sum (s := Finset.univ) fun μ _ => hasSum_sum (s := Finset.univ) fun ν _ =>
      hB1 μ ν).mul_left (1 / 2)).add hB2
  have hAB : (fun n => ∑ μ, ∑ ν, ‖mFourierCoeff (periodize R (g ν μ)) n‖ ^ 2) =
      fun n => (1 / 2) * ∑ μ, ∑ ν,
        ‖mFourierCoeff (periodize R (fun x => g ν μ x - g μ ν x)) n‖ ^ 2 +
        ‖mFourierCoeff (periodize R (fun x => ∑ μ, g μ μ x)) n‖ ^ 2 := by
    funext n
    simp only [hrule, hcurl, hdiv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    exact lagrange_identity (a n) (fun ν => Wc ν n)
  rw [hAB] at hA
  have E := hA.unique hB
  simp only [← Finset.mul_sum] at E
  apply mul_left_cancel₀ hκ
  linear_combination E

/-! ### The Hodge estimate -/

theorem eLpNorm_two_eq_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hf : MemLp f 2 μ) : eLpNorm f 2 μ = ENNReal.ofReal (√(∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]

/-- **Hodge estimate for compactly supported one-forms.**  Under the hypotheses of
`weitzenbock_flat`, every partial derivative is controlled by `dw` and `d^*w`:
`‖∂_μ w_ν‖_{L²} ≤ Σ_{μ'ν'} ‖∂_{μ'} w_{ν'} - ∂_{ν'} w_{μ'}‖_{L²} + ‖Σ_{μ'} ∂_{μ'} w_{μ'}‖_{L²}`. -/
theorem eLpNorm_grad_le_d_dstar {R : ℝ} (hR : 0 ≤ R) {w : ι → (ι → ℝ) → ℂ}
    {g : ι → ι → (ι → ℝ) → ℂ} (hW : ∀ ν, MemW12 univ (w ν) (g ν))
    (hw0 : ∀ ν x, R < ‖x‖ → w ν x = 0) (hg0 : ∀ ν μ x, R < ‖x‖ → g ν μ x = 0) (ν μ : ι) :
    eLpNorm (g ν μ) 2 volume ≤
      ∑ μ', ∑ ν', eLpNorm (fun x => g ν' μ' x - g μ' ν' x) 2 volume +
        eLpNorm (fun x => ∑ μ', g μ' μ' x) 2 volume := by
  have hg2 : ∀ ν μ, MemLp (g ν μ) 2 volume := fun ν μ => by simpa using (hW ν).memLp_grad μ
  have hc2 : ∀ μ' ν', MemLp (fun x => g ν' μ' x - g μ' ν' x) 2 volume := fun μ' ν' =>
    (hg2 ν' μ').sub (hg2 μ' ν')
  have hd2 : MemLp (fun x => ∑ μ', g μ' μ' x) 2 volume := memLp_finset_sum _ fun μ _ => hg2 μ μ
  have hW' := weitzenbock_flat hR hW hw0 hg0
  set X : ι → ι → ℝ := fun ν μ => ∫ x, ‖g ν μ x‖ ^ 2 with hXd
  set Y : ι → ι → ℝ := fun μ' ν' => ∫ x, ‖g ν' μ' x - g μ' ν' x‖ ^ 2 with hYd
  set Z : ℝ := ∫ x, ‖∑ μ', g μ' μ' x‖ ^ 2 with hZd
  have hX : ∀ ν μ, 0 ≤ X ν μ := fun _ _ => integral_nonneg fun _ => by positivity
  have hY : ∀ μ' ν', 0 ≤ Y μ' ν' := fun _ _ => integral_nonneg fun _ => by positivity
  have hZ : 0 ≤ Z := integral_nonneg fun _ => by positivity
  -- `X ν μ ≤ Σ Σ Y + Z ≤ (Σ Σ √Y + √Z)²`
  have h1 : X ν μ ≤ ∑ μ', ∑ ν', X ν' μ' :=
    (Finset.single_le_sum (f := fun ν' => X ν' μ) (fun _ _ => hX _ _) (Finset.mem_univ ν)).trans
      (Finset.single_le_sum (f := fun μ' => ∑ ν', X ν' μ') (fun _ _ =>
        Finset.sum_nonneg fun _ _ => hX _ _) (Finset.mem_univ μ))
  have hSY : 0 ≤ ∑ μ', ∑ ν', Y μ' ν' := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
    fun _ _ => hY _ _
  have h2 : ∑ μ', ∑ ν', X ν' μ' ≤ ∑ μ', ∑ ν', Y μ' ν' + Z := by
    have : ∑ μ', ∑ ν', X ν' μ' = (1 / 2) * ∑ μ', ∑ ν', Y μ' ν' + Z := by
      simp only [hXd, hYd]; exact hW'
    rw [this]; linarith
  set S : ℝ := ∑ μ', ∑ ν', √(Y μ' ν') with hSd
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have h3 : ∑ μ', ∑ ν', Y μ' ν' ≤ S ^ 2 := by
    calc ∑ μ', ∑ ν', Y μ' ν' = ∑ μ', ∑ ν', √(Y μ' ν') ^ 2 := by
          simp only [Real.sq_sqrt (hY _ _)]
      _ ≤ ∑ μ', (∑ ν', √(Y μ' ν')) ^ 2 := Finset.sum_le_sum fun μ' _ =>
          Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => Real.sqrt_nonneg _
      _ ≤ S ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have h4 : √(X ν μ) ≤ S + √Z := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt hZ
    nlinarith [Real.sqrt_nonneg Z]
  have e : ENNReal.ofReal (S + √Z) =
      ∑ μ', ∑ ν', ENNReal.ofReal (√(Y μ' ν')) + ENNReal.ofReal (√Z) := by
    rw [ENNReal.ofReal_add hS (Real.sqrt_nonneg _), hSd, ENNReal.ofReal_sum_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)]
    congr 1
    refine Finset.sum_congr rfl fun μ' _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
  rw [eLpNorm_two_eq_sqrt (hg2 ν μ), eLpNorm_two_eq_sqrt hd2]
  simp only [eLpNorm_two_eq_sqrt (hc2 _ _)]
  exact (ENNReal.ofReal_le_ofReal h4).trans (le_of_eq e)

end RenewalGeometry.SobolevOpen
