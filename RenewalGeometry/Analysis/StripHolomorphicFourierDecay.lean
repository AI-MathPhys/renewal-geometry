/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevBoxCrEmbedding

/-!
# Exponential decay of Fourier coefficients of strip-holomorphic periodic functions

Generic infrastructure (no renewal notions) for the complex-analytic step of
`lem:log-source-upgrade` of the Einstein–Standard-Model action-closure manuscript
("spatial contour shifting gives `|f̂(t,ℓ)| ≤ A e^{-a|ℓ|/K}`").

## One variable

`strip b = {z ∈ ℂ : |Im z| < b}`.  Let `g : ℂ → E` be holomorphic on `strip b`, `1`-periodic on
the real line and bounded by `A` on the strip.

* `periodic_on_strip`: periodicity propagates from `ℝ` to the whole strip (identity theorem).
* `integral_eq_integral_shift`: **contour shift** — for `|y| < b`,
  `∫₀¹ φ(x) dx = ∫₀¹ φ(x + iy) dx` for every strip-holomorphic `1`-periodic `φ` (Cauchy's theorem
  on the rectangle `[0,1] × [0,y]`; the vertical sides cancel by periodicity).
* `norm_fourierIntegral_le_of_strip`: `‖∫₀¹ e^{-2πinx} g(x) dx‖ ≤ A e^{-2πb|n|}` for every
  `n ∈ ℤ` (shift by `∓ i b'`, `b' < b`, then let `b' → b`).

## The torus `𝕋^d`

* `norm_mFourierCoeff_le_of_strip_line`: if a continuous `F : 𝕋^d → ℂ` extends, along every
  coordinate line `s ↦ F(x + s eᵢ)` through every real point, holomorphically to `strip b` with
  bound `A`, then `|F̂(n)| ≤ A e^{-2πb|nᵢ|}` for every `i` (translation invariance of the Haar
  measure + Fubini reduce to the one-variable estimate on each line).
* `norm_mFourierCoeff_le_of_strip`: hence `|F̂(n)| ≤ A e^{-2πb|n|_∞}`.

Normalisation: Mathlib's torus has period `1` and characters `e^{2πi n·x}`.  On the manuscript's
box of period `2π` with characters `e^{iℓ·x}`, a strip of width `a/K` corresponds to
`b = a/(2πK)` here, and the bound reads `|f̂(ℓ)| ≤ A e^{-a|ℓ|_∞/K}`.  The hypothesis is the
holomorphic extension of each coordinate restriction (implied by the manuscript's extension
"in the three spatial variables to width `a/K`").
-/

open Complex MeasureTheory Filter Topology Set UnitAddTorus
open scoped Real BigOperators Interval

namespace RenewalGeometry.StripFourier

set_option linter.unusedSectionVars false

noncomputable section

/-! ### One variable -/

/-- The horizontal strip `{z : |Im z| < b}`. -/
def strip (b : ℝ) : Set ℂ := {z : ℂ | |z.im| < b}

theorem mem_strip {b : ℝ} {z : ℂ} : z ∈ strip b ↔ |z.im| < b := Iff.rfl

theorem isOpen_strip (b : ℝ) : IsOpen (strip b) :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

theorem strip_eq_preimage (b : ℝ) : strip b = Complex.im ⁻¹' Ioo (-b) b := by
  ext z; simp [strip, abs_lt]

theorem convex_strip (b : ℝ) : Convex ℝ (strip b) := by
  rw [strip_eq_preimage]
  exact (convex_Ioo _ _).linear_preimage Complex.imLm

theorem ofReal_mem_strip {b : ℝ} (hb : 0 < b) (x : ℝ) : (x : ℂ) ∈ strip b := by
  simp [strip, hb]

theorem add_real_mem_strip {b : ℝ} {z : ℂ} (hz : z ∈ strip b) (x : ℝ) : z + x ∈ strip b := by
  simpa [strip] using hz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Periodicity propagates to the strip** (identity theorem): a function holomorphic on
`strip b` and `1`-periodic on the real line is `1`-periodic on the strip. -/
theorem periodic_on_strip [CompleteSpace E] {g : ℂ → E} {b : ℝ} (hb : 0 < b)
    (hg : DifferentiableOn ℂ g (strip b)) (hper : ∀ x : ℝ, g (x + 1) = g x) :
    ∀ z ∈ strip b, g (z + 1) = g z := by
  set h : ℂ → E := fun z => g (z + 1) - g z
  have hshift : MapsTo (fun z : ℂ => z + 1) (strip b) (strip b) := fun z hz => by
    simpa using add_real_mem_strip hz 1
  have hd : DifferentiableOn ℂ h (strip b) :=
    (hg.comp (differentiableOn_id.add_const 1) hshift).sub hg
  have han := hd.analyticOnNhd (isOpen_strip b)
  have h0 : (0 : ℂ) ∈ strip b := by simpa using ofReal_mem_strip hb 0
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), h z = 0 := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (Complex.continuous_ofReal.tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
        simpa using this
      · exact eventually_nhdsWithin_of_forall fun x hx => by simpa using hx
    exact ht.frequently (Frequently.of_forall fun x => by simp [h, hper])
  intro z hz
  have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_strip b).isPreconnected
    h0 hfreq hz
  simpa [h, sub_eq_zero] using this

/-- **Contour shift** on the strip: for a strip-holomorphic `1`-periodic `φ` and `|y| < b`,
`∫₀¹ φ(x) dx = ∫₀¹ φ(x + iy) dx` (Cauchy on the rectangle `[0,1] × [0,y]`, vertical sides cancel). -/
theorem integral_eq_integral_shift [CompleteSpace E] {φ : ℂ → E} {b y : ℝ}
    (hφ : DifferentiableOn ℂ φ (strip b)) (hper : ∀ z ∈ strip b, φ (z + 1) = φ z)
    (hy : |y| < b) :
    ∫ x : ℝ in (0 : ℝ)..1, φ x = ∫ x : ℝ in (0 : ℝ)..1, φ (x + y * I) := by
  have himy : ∀ t ∈ [[(0 : ℝ), y]], |t| < b := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg h1]; exact lt_of_le_of_lt (h2.trans (le_abs_self y)) hy
    · rw [abs_of_nonpos h2]; exact lt_of_le_of_lt (by linarith [neg_abs_le y]) hy
  have hrect : [[(0 : ℂ).re, (1 + y * I).re]] ×ℂ [[(0 : ℂ).im, (1 + y * I).im]] ⊆ strip b := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    have : z.im ∈ [[(0 : ℝ), y]] := by simpa using hz.2
    exact himy _ this
  have H := integral_boundary_rect_eq_zero_of_differentiableOn φ 0 (1 + y * I) (hφ.mono hrect)
  have hv : (∫ t : ℝ in (0 : ℂ).im..(1 + y * I).im, φ (((1 + y * I).re : ℝ) + t * I)) =
      ∫ t : ℝ in (0 : ℂ).im..(1 + y * I).im, φ (((0 : ℂ).re : ℝ) + t * I) := by
    simp only [Complex.zero_im, Complex.zero_re, Complex.add_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.add_im, Complex.one_im, Complex.mul_im, mul_zero, sub_zero, mul_one, zero_add,
      add_zero, Complex.ofReal_zero, Complex.ofReal_one]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have hmem : (t : ℂ) * I ∈ strip b := by
      simpa [strip] using himy t ht
    rw [add_comm]
    exact hper _ hmem
  rw [hv] at H
  simp only [Complex.zero_im, Complex.zero_re, Complex.add_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    Complex.add_im, Complex.one_im, Complex.mul_im, mul_zero, sub_zero, mul_one, zero_add,
    add_zero, Complex.ofReal_zero, zero_mul] at H
  have := H
  rw [add_sub_cancel_right, sub_eq_zero] at this
  exact this

/-- `exp(-2πin)` is `1` for integer `n`. -/
theorem exp_neg_two_pi_I_int (n : ℤ) : Complex.exp (-(2 * π * I * n)) = 1 := by
  have := Complex.exp_int_mul_two_pi_mul_I (-n)
  rw [← this]
  congr 1
  push_cast
  ring

/-- `‖exp(-2πin(x+iy))‖ = exp(2πny)`. -/
theorem norm_exp_fourier_shift (n : ℤ) (x y : ℝ) :
    ‖Complex.exp (-(2 * π * I * n * ((x : ℂ) + y * I)))‖ = Real.exp (2 * π * n * y) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The shifted bound for one `b' < b`. -/
theorem norm_fourierIntegral_le_of_strip_aux [CompleteSpace E] {g : ℂ → E} {b A b' : ℝ}
    (hb : 0 < b) (hg : DifferentiableOn ℂ g (strip b)) (hper : ∀ x : ℝ, g (x + 1) = g x)
    (hA : ∀ z ∈ strip b, ‖g z‖ ≤ A) (n : ℤ) (hb0 : 0 ≤ b') (hbb : b' < b) :
    ‖∫ x : ℝ in (0 : ℝ)..1, Complex.exp (-(2 * π * I * n * x)) • g x‖ ≤
      A * Real.exp (-(2 * π * b' * |(n : ℝ)|)) := by
  set φ : ℂ → E := fun z => Complex.exp (-(2 * π * I * n * z)) • g z
  have hφd : DifferentiableOn ℂ φ (strip b) := by
    refine DifferentiableOn.smul ?_ hg
    exact (differentiable_exp.comp ((differentiable_id.const_mul _).neg)).differentiableOn
  have hgper := periodic_on_strip hb hg hper
  have hφper : ∀ z ∈ strip b, φ (z + 1) = φ z := by
    intro z hz
    simp only [φ]
    rw [hgper z hz]
    congr 1
    rw [show -(2 * π * I * n * (z + 1)) = -(2 * π * I * n * z) + -(2 * π * I * n) by ring,
      Complex.exp_add, exp_neg_two_pi_I_int, mul_one]
  set y : ℝ := if 0 ≤ n then -b' else b'
  have hy : |y| < b := by
    simp only [y]; split_ifs <;> simp [abs_of_nonneg hb0, hbb]
  have hny : 2 * π * n * y = -(2 * π * b' * |(n : ℝ)|) := by
    simp only [y]
    split_ifs with h
    · rw [abs_of_nonneg (by exact_mod_cast h)]; ring
    · rw [abs_of_neg (by exact_mod_cast (not_le.mp h))]; ring
  have hshift := integral_eq_integral_shift hφd hφper hy
  change ‖∫ x : ℝ in (0 : ℝ)..1, φ x‖ ≤ _
  rw [hshift]
  have hbound : ∀ x ∈ Ι (0 : ℝ) 1, ‖φ (x + y * I)‖ ≤
      A * Real.exp (-(2 * π * b' * |(n : ℝ)|)) := by
    intro x _
    simp only [φ]
    rw [norm_smul, norm_exp_fourier_shift, hny, mul_comm]
    refine mul_le_mul_of_nonneg_right (hA _ ?_) (Real.exp_pos _).le
    simpa [strip] using hy
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa using this

/-- **Fourier coefficients of a strip-holomorphic periodic function decay exponentially**:
`‖∫₀¹ e^{-2πinx} g(x) dx‖ ≤ A e^{-2πb|n|}` when `g` is holomorphic on `|Im z| < b`, `1`-periodic on
`ℝ` and bounded by `A` on the strip. -/
theorem norm_fourierIntegral_le_of_strip [CompleteSpace E] {g : ℂ → E} {b A : ℝ}
    (hb : 0 < b) (hg : DifferentiableOn ℂ g (strip b)) (hper : ∀ x : ℝ, g (x + 1) = g x)
    (hA : ∀ z ∈ strip b, ‖g z‖ ≤ A) (n : ℤ) :
    ‖∫ x : ℝ in (0 : ℝ)..1, Complex.exp (-(2 * π * I * n * x)) • g x‖ ≤
      A * Real.exp (-(2 * π * b * |(n : ℝ)|)) := by
  have ht : Tendsto (fun b' : ℝ => A * Real.exp (-(2 * π * b' * |(n : ℝ)|))) (𝓝[<] b)
      (𝓝 (A * Real.exp (-(2 * π * b * |(n : ℝ)|)))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact ((continuous_const.mul (Real.continuous_exp.comp
      (((continuous_const.mul continuous_id).mul continuous_const).neg))).tendsto b)
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hb] with b' hb'
  exact norm_fourierIntegral_le_of_strip_aux hb hg hper hA n hb'.1.le hb'.2

/-! ### The torus `𝕋^d` -/

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d] [DecidableEq d]

open TorusSobolev

theorem continuous_lineShift (i : d) : Continuous (lineShift (d := d) i) := by
  unfold lineShift
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h
    simp only [Pi.single_eq_same]
    exact AddCircle.continuous_mk' 1
  · simp only [Pi.single_eq_of_ne h]
    exact continuous_const

theorem lineShift_one (i : d) : lineShift (d := d) i 1 = 0 := by
  unfold lineShift
  have : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period (p := (1 : ℝ))
  rw [this, Pi.single_zero]

/-- **Fourier decay on `𝕋^d` from strip holomorphy along coordinate lines**: if the continuous
`F` extends, along every coordinate line `s ↦ F(x + s eᵢ)` through every point, holomorphically
to `strip b` with bound `A`, then `|F̂(n)| ≤ A e^{-2πb|nᵢ|}` for every direction `i`.
Proof: `F̂(n) = ∫_x ∫₀¹ e_{-n}(x + s eᵢ) F(x + s eᵢ) ds dx` (translation invariance and Fubini),
and the inner integral is `e_{-n}(x)` times a one-variable Fourier coefficient of the extension. -/
theorem norm_mFourierCoeff_le_of_strip_line (F : C(UnitAddTorus d, ℂ)) {b A : ℝ} (hb : 0 < b)
    (hext : ∀ (x : UnitAddTorus d) (i : d), ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (strip b) ∧
      (∀ s : ℝ, G s = F (x + lineShift i s)) ∧ ∀ z ∈ strip b, ‖G z‖ ≤ A)
    (n : d → ℤ) (i : d) :
    ‖mFourierCoeff F n‖ ≤ A * Real.exp (-(2 * π * b * |(n i : ℝ)|)) := by
  set Φ : UnitAddTorus d → ℂ := fun x => mFourier (-n) x • F x with hΦdef
  have hΦc : Continuous Φ := (mFourier (-n)).continuous.smul F.continuous
  have hinv : ∀ s : ℝ, ∫ x, Φ (x + lineShift i s) = ∫ x, Φ x := fun s =>
    integral_add_right_eq_self (μ := volume) Φ (lineShift i s)
  have havg : ∫ x, Φ x = ∫ s in (0 : ℝ)..1, ∫ x, Φ (x + lineShift i s) := by
    simp_rw [hinv]; simp
  have hcont2 : Continuous (Function.uncurry fun (s : ℝ) (x : UnitAddTorus d) =>
      Φ (x + lineShift i s)) :=
    hΦc.comp (continuous_snd.add ((continuous_lineShift i).comp continuous_fst))
  have hint : Integrable (Function.uncurry fun (s : ℝ) (x : UnitAddTorus d) =>
      Φ (x + lineShift i s)) ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    refine Integrable.of_bound hcont2.aestronglyMeasurable ‖F‖ (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, Φ, smul_eq_mul, norm_mul, norm_mFourier_apply, one_mul]
    exact F.norm_coe_le_norm _
  have hswap : (∫ s in (0 : ℝ)..1, ∫ x, Φ (x + lineShift i s)) =
      ∫ x, ∫ s in (0 : ℝ)..1, Φ (x + lineShift i s) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
    exact integral_integral_swap hint
  have hline : ∀ x, ‖∫ s in (0 : ℝ)..1, Φ (x + lineShift i s)‖ ≤
      A * Real.exp (-(2 * π * b * |(n i : ℝ)|)) := by
    intro x
    obtain ⟨G, hGd, hGeq, hGA⟩ := hext x i
    have hper : ∀ s : ℝ, G (s + 1) = G s := by
      intro s
      have h1 := hGeq (s + 1)
      push_cast at h1
      rw [h1, hGeq, SobolevBoxCr.lineShift_add, lineShift_one, add_zero]
    have hΦline : ∀ s : ℝ, Φ (x + lineShift i s) =
        mFourier (-n) x * (Complex.exp (-(2 * π * I * (n i : ℤ) * (s : ℂ))) • G s) := by
      intro s
      simp only [Φ, smul_eq_mul, mFourier_add_apply, mFourier_lineShift, hGeq]
      have : Complex.exp (2 * π * I * (((-n) i : ℤ) : ℂ) * s) =
          Complex.exp (-(2 * π * I * (n i : ℤ) * (s : ℂ))) := by
        congr 1; simp only [Pi.neg_apply, Int.cast_neg]; ring
      rw [this]; ring
    rw [intervalIntegral.integral_congr (fun s _ => hΦline s),
      intervalIntegral.integral_const_mul, norm_mul, norm_mFourier_apply, one_mul]
    exact norm_fourierIntegral_le_of_strip hb hGd hper hGA (n i)
  have hcoeff : mFourierCoeff F n = ∫ x, Φ x := rfl
  rw [hcoeff, havg, hswap]
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ hline)).trans ?_
  simp

/-- The sup norm `|n|_∞ = maxᵢ |nᵢ|` of a lattice vector. -/
def linfNorm (n : d → ℤ) : ℕ := Finset.univ.sup fun i => (n i).natAbs

theorem natAbs_le_linfNorm (n : d → ℤ) (i : d) : (n i).natAbs ≤ linfNorm n :=
  Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ i)

theorem exists_eq_linfNorm [Nonempty d] (n : d → ℤ) : ∃ i, ((n i).natAbs : ℝ) = linfNorm n := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset d) Finset.univ_nonempty
    (fun i => (n i).natAbs)
  exact ⟨i, by unfold linfNorm; rw [hi]⟩

/-- **Fourier decay on `𝕋^d` in the sup norm**: under the strip hypothesis,
`|F̂(n)| ≤ A e^{-2πb|n|_∞}` (shift in the direction of the largest frequency component). -/
theorem norm_mFourierCoeff_le_of_strip [Nonempty d] (F : C(UnitAddTorus d, ℂ)) {b A : ℝ}
    (hb : 0 < b)
    (hext : ∀ (x : UnitAddTorus d) (i : d), ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (strip b) ∧
      (∀ s : ℝ, G s = F (x + lineShift i s)) ∧ ∀ z ∈ strip b, ‖G z‖ ≤ A)
    (n : d → ℤ) :
    ‖mFourierCoeff F n‖ ≤ A * Real.exp (-(2 * π * b * (linfNorm n : ℝ))) := by
  obtain ⟨i, hi⟩ := exists_eq_linfNorm n
  have h := norm_mFourierCoeff_le_of_strip_line F hb hext n i
  rw [← hi, Nat.cast_natAbs, Int.cast_abs]
  exact h

/-! ### Non-vacuity -/

/-- The strip hypothesis is satisfied by every Fourier monomial `e_m` (a nonconstant example):
along each coordinate line `e_m(x + s eᵢ) = e_m(x) e^{2πi mᵢ s}` extends to an entire function,
bounded on `strip b` by `e^{2πb|m|₁}`. -/
theorem strip_extension_mFourier (m : d → ℤ) {b : ℝ} (x : UnitAddTorus d) (i : d) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (strip b) ∧
      (∀ s : ℝ, G s = mFourier m (x + lineShift i s)) ∧
      ∀ z ∈ strip b, ‖G z‖ ≤ Real.exp (2 * π * b * ∑ j, |((m j : ℤ) : ℝ)|) := by
  refine ⟨fun z => mFourier m x * Complex.exp (2 * π * I * m i * z), ?_, ?_, ?_⟩
  · exact (differentiable_const _ |>.mul
      (differentiable_exp.comp (differentiable_id.const_mul _))).differentiableOn
  · intro s
    rw [mFourier_add_apply, mFourier_lineShift]
  · intro z hz
    rw [norm_mul, norm_mFourier_apply, one_mul, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hre : (2 * π * I * (m i : ℂ) * z).re = -(2 * π * (m i : ℝ) * z.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have h1 : -(2 * π * (m i : ℝ) * z.im) ≤ 2 * π * |((m i : ℤ) : ℝ)| * |z.im| := by
      have := neg_abs_le (2 * π * (m i : ℝ) * z.im)
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
      linarith
    have h2 : |z.im| ≤ b := (mem_strip.mp hz).le
    have h3 : |((m i : ℤ) : ℝ)| ≤ ∑ j, |((m j : ℤ) : ℝ)| :=
      Finset.single_le_sum (f := fun j => |((m j : ℤ) : ℝ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hb : 0 ≤ b := (abs_nonneg _).trans h2
    calc -(2 * π * (m i : ℝ) * z.im) ≤ 2 * π * |((m i : ℤ) : ℝ)| * |z.im| := h1
      _ ≤ 2 * π * (∑ j, |((m j : ℤ) : ℝ)|) * b := by gcongr
      _ = 2 * π * b * ∑ j, |((m j : ℤ) : ℝ)| := by ring

/-- Non-vacuity: for a monomial `e_m` on `𝕋³` and every strip width `b > 0`, the decay theorem
applies and gives `|ê_m(n)| ≤ e^{2πb|m|₁} e^{-2πb|n|_∞}`. -/
example (m n : Fin 3 → ℤ) {b : ℝ} (hb : 0 < b) :
    ‖mFourierCoeff (mFourier m) n‖ ≤
      Real.exp (2 * π * b * ∑ j, |((m j : ℤ) : ℝ)|) * Real.exp (-(2 * π * b * (linfNorm n : ℝ))) :=
  norm_mFourierCoeff_le_of_strip (mFourier m) hb (fun x i => strip_extension_mFourier m x i) n

end

end RenewalGeometry.StripFourier
