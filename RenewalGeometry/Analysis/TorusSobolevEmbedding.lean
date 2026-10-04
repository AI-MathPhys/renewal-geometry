/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.FourierCoefficientRellich

/-!
# Sobolev spaces on the flat torus `𝕋^d` in Fourier form: interpolation, embedding, Rellich

Generic infrastructure (no renewal notions) for the continuum Sobolev steps of the
Einstein–Standard-Model action-closure manuscript (`prop:shadow-residual-upgrade`,
`prop:sobolev-bosonic`, `cor:stress-topology`, `prop:orlicz`).  The torus is
`𝕋^d = UnitAddTorus d` for an arbitrary finite index type `d` (the manuscript needs `d = 3` for
Cauchy slabs and `d = 4` for periodic space-time boxes), with Mathlib's Haar probability measure
and Fourier monomials `mFourier n`, `n ∈ ℤ^d`.

The Sobolev weight is `⟨n⟩² = sobWeight n = 1 + 4π²|n|²` (the symbol of `1 - Δ`), and for a real
exponent `s` the squared `H^s` norm of a coefficient family `c : ℤ^d → ℂ` is
`coeffSobSq s c = Σ_n ⟨n⟩^{2s} |c n|²` (written `sobWeight n ^ s`); for a function it is applied to
the Fourier coefficients `mFourierCoeff f`.

* `coeffSobSq_mono`, `CoeffMemH.mono`: `H^s ⊂ H^t` for `t ≤ s`, with `‖·‖_{H^t} ≤ ‖·‖_{H^s}`.
* `sobSq_zero_eq_norm_sq`: `H^0 = L²` isometrically (Parseval).
* `coeffSobSq_interpolation`, `sobNorm_interpolation`, `sobNorm_interpolation_L2`:
  the **interpolation inequality** `‖u‖_{H^k} ≤ ‖u‖_{L²}^{1-k/s} ‖u‖_{H^s}^{k/s}`, `0 ≤ k ≤ s`
  (Hölder on the coefficient sum); `lintegral_sobSq_interpolation` is the space-time
  (`L²_t H^k_x`) version for families `u(t)` over any measure space of times (Hölder in `t`).
* `summable_sobWeight_rpow_neg`: `Σ_{n ∈ ℤ^d} ⟨n⟩^{-2s} < ∞` for `s > d/2`.
* `summable_norm_of_coeffMemH`: Cauchy–Schwarz, `Σ |c n| ≤ C_{s,d} ‖c‖_{H^s}` for `s > d/2`.
* `fourierSum`, `mFourierCoeff_fourierSum`: the uniformly convergent Fourier series of an
  absolutely summable family is a continuous function with the prescribed coefficients.
* `exists_continuous_of_memH` (**Sobolev embedding `H^s(𝕋^d) ⊂ C⁰`, `s > d/2`**): every
  `f ∈ L²` with finite `H^s` norm has a continuous representative `g` (`g = f` in `L²`, hence
  a.e.), its Fourier series converges uniformly to `g`, and `‖g‖_∞ ≤ C_{s,d} ‖f‖_{H^s}`;
  `norm_le_of_memH` is the continuous-function form.
* `rellich_coeff`, `rellich_L2` (**Rellich–Kondrachov on `𝕋^d`**): bounded sequences in `H^s`
  have subsequences converging in `H^t` for every `t < s` (real exponents).
* `rellich_C0`, `rellich_C0_Lp`: bounded sequences of continuous functions in `H^s`, `s > d/2`,
  have subsequences converging uniformly, hence in every `L^p`, `p ≤ ∞`;
  `precompact_of_bounded_memH` packages `H^s ⋐ H^t ∩ C⁰ ∩ L^p` for `L²` sequences.
* `mFourierCoeff_mFourier`, `memH_mFourier`, `sobSq_mFourier`: monomials (non-vacuity).
-/

open Finset Filter Topology MeasureTheory UnitAddTorus
open scoped BigOperators Real ENNReal InnerProductSpace

namespace RenewalGeometry.TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

variable {d : Type*} [Fintype d]

/-! ### The Sobolev weight -/

/-- The Sobolev weight `⟨n⟩² = 1 + 4π²|n|²` on `ℤ^d` (the Fourier symbol of `1 - Δ` on `𝕋^d`). -/
def sobWeight (n : d → ℤ) : ℝ := 1 + 4 * π ^ 2 * ∑ i, ((n i : ℝ)) ^ 2

theorem sq_le_sum_sq (n : d → ℤ) (i : d) : ((n i : ℝ)) ^ 2 ≤ ∑ j, ((n j : ℝ)) ^ 2 :=
  single_le_sum (f := fun j => ((n j : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)

theorem sum_sq_nonneg (n : d → ℤ) : 0 ≤ ∑ j, ((n j : ℝ)) ^ 2 :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem one_le_sobWeight (n : d → ℤ) : 1 ≤ sobWeight n := by
  unfold sobWeight
  have := sum_sq_nonneg n
  have : 0 ≤ 4 * π ^ 2 * ∑ j, ((n j : ℝ)) ^ 2 := by positivity
  linarith

theorem sobWeight_pos (n : d → ℤ) : 0 < sobWeight n :=
  lt_of_lt_of_le one_pos (one_le_sobWeight n)

theorem four_pi_sq_ge_one : 1 ≤ 4 * π ^ 2 := by nlinarith [Real.pi_gt_three]

/-- Each coordinate is controlled: `1 + n_i² ≤ ⟨n⟩²`. -/
theorem one_add_sq_le_sobWeight (n : d → ℤ) (i : d) : 1 + ((n i : ℝ)) ^ 2 ≤ sobWeight n := by
  unfold sobWeight
  have h1 := sq_le_sum_sq n i
  have h0 := sq_nonneg ((n i : ℝ))
  have hπ := four_pi_sq_ge_one
  nlinarith

/-- The derivative symbol is controlled: `(2π n_i)² ≤ ⟨n⟩²`. -/
theorem sq_symbol_le_sobWeight (n : d → ℤ) (i : d) : (2 * π * n i) ^ 2 ≤ sobWeight n := by
  unfold sobWeight
  have h1 := sq_le_sum_sq n i
  have : (2 * π * n i) ^ 2 = 4 * π ^ 2 * ((n i : ℝ)) ^ 2 := by ring
  rw [this]
  have : 4 * π ^ 2 * ((n i : ℝ)) ^ 2 ≤ 4 * π ^ 2 * ∑ j, ((n j : ℝ)) ^ 2 := by gcongr
  linarith

theorem sobWeight_rpow_nonneg (n : d → ℤ) (s : ℝ) : 0 ≤ sobWeight n ^ s :=
  Real.rpow_nonneg (sobWeight_pos n).le s

theorem sobWeight_rpow_pos (n : d → ℤ) (s : ℝ) : 0 < sobWeight n ^ s :=
  Real.rpow_pos_of_pos (sobWeight_pos n) s

theorem sobWeight_rpow_mono (n : d → ℤ) {t s : ℝ} (h : t ≤ s) :
    sobWeight n ^ t ≤ sobWeight n ^ s :=
  Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) h

theorem one_le_sobWeight_rpow (n : d → ℤ) {s : ℝ} (hs : 0 ≤ s) : 1 ≤ sobWeight n ^ s :=
  Real.one_le_rpow (one_le_sobWeight n) hs

/-! ### Sobolev norms of coefficient families and of functions -/

/-- The squared `H^s` norm of a coefficient family: `Σ_n ⟨n⟩^{2s} |c n|²`. -/
def coeffSobSq (s : ℝ) (c : (d → ℤ) → ℂ) : ℝ := ∑' n, sobWeight n ^ s * ‖c n‖ ^ 2

/-- Membership in `H^s`: the weighted squared coefficients are summable. -/
def CoeffMemH (s : ℝ) (c : (d → ℤ) → ℂ) : Prop :=
  Summable fun n => sobWeight n ^ s * ‖c n‖ ^ 2

/-- The squared `H^s(𝕋^d)` norm of a function, through its Fourier coefficients. -/
def sobSq (s : ℝ) (f : UnitAddTorus d → ℂ) : ℝ := coeffSobSq s (mFourierCoeff f)

/-- `f ∈ H^s(𝕋^d)`. -/
def MemH (s : ℝ) (f : UnitAddTorus d → ℂ) : Prop := CoeffMemH s (mFourierCoeff f)

/-- The `H^s(𝕋^d)` norm `‖f‖_{H^s} = (Σ_n ⟨n⟩^{2s} |f̂(n)|²)^{1/2}`. -/
def sobNorm (s : ℝ) (f : UnitAddTorus d → ℂ) : ℝ := Real.sqrt (sobSq s f)

theorem coeffSobSq_term_nonneg (s : ℝ) (c : (d → ℤ) → ℂ) (n : d → ℤ) :
    0 ≤ sobWeight n ^ s * ‖c n‖ ^ 2 :=
  mul_nonneg (sobWeight_rpow_nonneg n s) (sq_nonneg _)

theorem coeffSobSq_nonneg (s : ℝ) (c : (d → ℤ) → ℂ) : 0 ≤ coeffSobSq s c :=
  tsum_nonneg (coeffSobSq_term_nonneg s c)

theorem sobSq_nonneg (s : ℝ) (f : UnitAddTorus d → ℂ) : 0 ≤ sobSq s f :=
  coeffSobSq_nonneg s _

theorem sobNorm_sq (s : ℝ) (f : UnitAddTorus d → ℂ) : sobNorm s f ^ 2 = sobSq s f :=
  Real.sq_sqrt (sobSq_nonneg s f)

/-- **`H^s ⊂ H^t` for `t ≤ s`.** -/
theorem CoeffMemH.mono {t s : ℝ} (h : t ≤ s) {c : (d → ℤ) → ℂ} (hc : CoeffMemH s c) :
    CoeffMemH t c :=
  Summable.of_nonneg_of_le (coeffSobSq_term_nonneg t c)
    (fun n => mul_le_mul_of_nonneg_right (sobWeight_rpow_mono n h) (sq_nonneg _)) hc

/-- **Monotonicity of the Sobolev scale**: `‖c‖_{H^t} ≤ ‖c‖_{H^s}` for `t ≤ s`. -/
theorem coeffSobSq_mono {t s : ℝ} (h : t ≤ s) {c : (d → ℤ) → ℂ} (hc : CoeffMemH s c) :
    coeffSobSq t c ≤ coeffSobSq s c :=
  Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (sobWeight_rpow_mono n h) (sq_nonneg _))
    (hc.mono h) hc

theorem MemH.mono {t s : ℝ} (h : t ≤ s) {f : UnitAddTorus d → ℂ} (hf : MemH s f) : MemH t f :=
  CoeffMemH.mono h hf

theorem sobNorm_mono {t s : ℝ} (h : t ≤ s) {f : UnitAddTorus d → ℂ} (hf : MemH s f) :
    sobNorm t f ≤ sobNorm s f :=
  Real.sqrt_le_sqrt (coeffSobSq_mono h hf)

theorem coeffMemH_zero_iff (c : (d → ℤ) → ℂ) :
    CoeffMemH 0 c ↔ Summable fun n => ‖c n‖ ^ 2 := by
  simp [CoeffMemH, Real.rpow_zero]

theorem coeffSobSq_zero (c : (d → ℤ) → ℂ) : coeffSobSq 0 c = ∑' n, ‖c n‖ ^ 2 := by
  simp [coeffSobSq, Real.rpow_zero]

/-! ### Interpolation -/

/-- **Interpolation inequality in coefficient form** (`prop:shadow-residual-upgrade`):
for `0 ≤ k ≤ s`, `s > 0`, `‖c‖²_{H^k} ≤ (‖c‖²_{H^0})^{1-k/s} (‖c‖²_{H^s})^{k/s}`.
Proof: Hölder with exponents `1/(1-θ)`, `1/θ`, `θ = k/s`, applied to
`⟨n⟩^{2k}|c|² = (|c|²)^{1-θ} (⟨n⟩^{2s}|c|²)^θ`. -/
theorem coeffSobSq_interpolation {k s : ℝ} (hk : 0 ≤ k) (hks : k ≤ s) (hs : 0 < s)
    {c : (d → ℤ) → ℂ} (h0 : CoeffMemH 0 c) (hS : CoeffMemH s c) :
    CoeffMemH k c ∧
      coeffSobSq k c ≤ coeffSobSq 0 c ^ (1 - k / s) * coeffSobSq s c ^ (k / s) := by
  refine ⟨hS.mono hks, ?_⟩
  set θ := k / s with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hk hs.le
  have hθ1 : θ ≤ 1 := (div_le_one hs).mpr hks
  rcases hθ0.eq_or_lt with h | h
  · have hk0 : k = 0 := by
      have : k = θ * s := by rw [hθ]; field_simp
      rw [this, ← h, zero_mul]
    rw [← h, hk0, sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
  rcases hθ1.eq_or_lt with h' | h'
  · have hks' : k = s := by
      have : k = θ * s := by rw [hθ]; field_simp
      rw [this, h', one_mul]
    rw [h', sub_self, Real.rpow_zero, Real.rpow_one, one_mul, hks']
  -- the genuine Hölder case `0 < θ < 1`
  have hpq := Real.holderConjugate_one_div (a := 1 - θ) (b := θ) (by linarith) h (by ring)
  set f : (d → ℤ) → ℝ := fun n => (‖c n‖ ^ 2) ^ (1 - θ)
  set g : (d → ℤ) → ℝ := fun n => (sobWeight n ^ s * ‖c n‖ ^ 2) ^ θ
  have hf : ∀ n, 0 ≤ f n := fun n => Real.rpow_nonneg (sq_nonneg _) _
  have hg : ∀ n, 0 ≤ g n := fun n => Real.rpow_nonneg (coeffSobSq_term_nonneg s c n) _
  have hfp : ∀ n, f n ^ (1 / (1 - θ)) = ‖c n‖ ^ 2 := by
    intro n
    simp only [f]
    rw [← Real.rpow_mul (sq_nonneg _), mul_one_div_cancel (by linarith), Real.rpow_one]
  have hgq : ∀ n, g n ^ (1 / θ) = sobWeight n ^ s * ‖c n‖ ^ 2 := by
    intro n
    simp only [g]
    rw [← Real.rpow_mul (coeffSobSq_term_nonneg s c n), mul_one_div_cancel h.ne', Real.rpow_one]
  have hfg : ∀ n, f n * g n = sobWeight n ^ k * ‖c n‖ ^ 2 := by
    intro n
    simp only [f, g]
    rw [Real.mul_rpow (sobWeight_rpow_nonneg n s) (sq_nonneg _),
      ← Real.rpow_mul (sobWeight_pos n).le]
    have hsθ : s * θ = k := by rw [hθ]; field_simp
    rw [hsθ]
    have : (‖c n‖ ^ 2) ^ (1 - θ) * (‖c n‖ ^ 2) ^ θ = ‖c n‖ ^ 2 := by
      rw [← Real.rpow_add' (sq_nonneg _) (by norm_num), sub_add_cancel, Real.rpow_one]
    calc (‖c n‖ ^ 2) ^ (1 - θ) * (sobWeight n ^ k * (‖c n‖ ^ 2) ^ θ)
        = sobWeight n ^ k * ((‖c n‖ ^ 2) ^ (1 - θ) * (‖c n‖ ^ 2) ^ θ) := by ring
      _ = _ := by rw [this]
  have hf_sum : Summable fun n => f n ^ (1 / (1 - θ)) := by
    simp_rw [hfp]; exact (coeffMemH_zero_iff c).mp h0
  have hg_sum : Summable fun n => g n ^ (1 / θ) := by simp_rw [hgq]; exact hS
  have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum
  simp_rw [hfg, hfp, hgq] at hH
  rw [one_div_one_div, one_div_one_div] at hH
  rw [coeffSobSq_zero]
  exact hH

/-- **Interpolation of Sobolev norms** (`prop:shadow-residual-upgrade`):
`‖f‖_{H^k} ≤ ‖f‖_{H^0}^{1-k/s} ‖f‖_{H^s}^{k/s}` for `0 ≤ k ≤ s`, `s > 0`. -/
theorem sobNorm_interpolation {k s : ℝ} (hk : 0 ≤ k) (hks : k ≤ s) (hs : 0 < s)
    {f : UnitAddTorus d → ℂ} (h0 : MemH 0 f) (hS : MemH s f) :
    MemH k f ∧ sobNorm k f ≤ sobNorm 0 f ^ (1 - k / s) * sobNorm s f ^ (k / s) := by
  obtain ⟨hk', hle⟩ := coeffSobSq_interpolation hk hks hs h0 hS
  refine ⟨hk', ?_⟩
  unfold sobNorm
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (sobSq_nonneg _ _), ← Real.rpow_mul (sobSq_nonneg _ _), mul_comm (1 / 2),
    mul_comm (1 / 2), Real.rpow_mul (sobSq_nonneg _ _), Real.rpow_mul (sobSq_nonneg _ _),
    ← Real.mul_rpow (Real.rpow_nonneg (sobSq_nonneg _ _) _)
      (Real.rpow_nonneg (sobSq_nonneg _ _) _)]
  exact Real.rpow_le_rpow (sobSq_nonneg _ _) hle (by norm_num)

/-! ### `H^0 = L²` (Parseval) -/

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

theorem mFourierCoeff_Lp_sub (f g : L²(UnitAddTorus d)) (n : d → ℤ) :
    mFourierCoeff (⇑(f - g)) n = mFourierCoeff f n - mFourierCoeff g n := by
  simp only [← mFourierBasis_repr, map_sub]
  rfl

theorem mFourierCoeff_Lp_add (f g : L²(UnitAddTorus d)) (n : d → ℤ) :
    mFourierCoeff (⇑(f + g)) n = mFourierCoeff f n + mFourierCoeff g n := by
  simp only [← mFourierBasis_repr, map_add]
  rfl

theorem mFourierCoeff_Lp_smul (a : ℂ) (f : L²(UnitAddTorus d)) (n : d → ℤ) :
    mFourierCoeff (⇑(a • f)) n = a * mFourierCoeff f n := by
  simp only [← mFourierBasis_repr, map_smul]
  rfl

/-- Every `L²` function lies in `H^0`. -/
theorem memH_zero_of_L2 (f : L²(UnitAddTorus d)) : MemH 0 f :=
  (coeffMemH_zero_iff _).mpr (hasSum_sq_mFourierCoeff f).summable

/-- **`H^0 = L²` isometrically**: `‖f‖²_{H^0} = ∫ |f|²`. -/
theorem sobSq_zero_eq_integral (f : L²(UnitAddTorus d)) : sobSq 0 f = ∫ t, ‖f t‖ ^ 2 := by
  unfold sobSq
  rw [coeffSobSq_zero]
  exact (hasSum_sq_mFourierCoeff f).tsum_eq

/-- **`H^0 = L²` isometrically**: `‖f‖_{H^0} = ‖f‖_{L²}`. -/
theorem sobNorm_zero_eq_norm (f : L²(UnitAddTorus d)) : sobNorm 0 f = ‖f‖ := by
  have h1 : ‖f‖ = ‖mFourierBasis.repr f‖ := (mFourierBasis.repr.norm_map f).symm
  have h2 := lp.norm_eq_tsum_rpow (p := 2) (by norm_num) (mFourierBasis.repr f)
  rw [h1, h2]
  unfold sobNorm sobSq
  rw [coeffSobSq_zero, Real.sqrt_eq_rpow]
  congr 1
  · refine tsum_congr fun n => ?_
    rw [← mFourierBasis_repr]
    norm_num

/-- **Interpolation between `L²` and `H^s`** (`prop:shadow-residual-upgrade`, analytic core):
for `f ∈ L²(𝕋^d) ∩ H^s` and `0 ≤ k ≤ s`, `s > 0`,
`‖f‖_{H^k} ≤ ‖f‖_{L²}^{1-k/s} ‖f‖_{H^s}^{k/s}`. -/
theorem sobNorm_interpolation_L2 {k s : ℝ} (hk : 0 ≤ k) (hks : k ≤ s) (hs : 0 < s)
    (f : L²(UnitAddTorus d)) (hS : MemH s f) :
    MemH k f ∧ sobNorm k f ≤ ‖f‖ ^ (1 - k / s) * sobNorm s f ^ (k / s) := by
  rw [← sobNorm_zero_eq_norm]
  exact sobNorm_interpolation hk hks hs (memH_zero_of_L2 f) hS

/-! ### Summability of `⟨n⟩^{-2s}` on `ℤ^d` for `s > d/2` -/

/-- One-dimensional summability: `Σ_{m ∈ ℤ} (1 + m²)^{-a} < ∞` for `a > 1/2`. -/
theorem summable_one_add_sq_rpow_neg {a : ℝ} (ha : 1 / 2 < a) :
    Summable fun m : ℤ => (1 + (m : ℝ) ^ 2) ^ (-a) := by
  have h1 := Real.summable_abs_int_rpow (b := 2 * a) (by linarith)
  have h2 : Summable fun m : ℤ => if m = 0 then (1 : ℝ) else 0 := (hasSum_ite_eq 0 1).summable
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (h1.add h2)
  by_cases hm : m = 0
  · subst hm
    have : (0 : ℝ) ^ (-(2 * a)) = 0 := Real.zero_rpow (by linarith)
    simp [this]
  · rw [if_neg hm, add_zero]
    have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hpos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    calc (1 + (m : ℝ) ^ 2) ^ (-a) ≤ ((m : ℝ) ^ 2) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
      _ = |(m : ℝ)| ^ (-(2 * a)) := by
          rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
          congr 1; push_cast; ring

/-- Products of summable nonnegative one-dimensional families are summable on `ℤ^ι`, with
`Σ_{n} Π_i g_i(n_i) ≤ Π_i Σ_m g_i(m)`. -/
theorem summable_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℤ → ℝ)
    (hg : ∀ i m, 0 ≤ g i m) (hs : ∀ i, Summable (g i)) :
    Summable (fun n : ι → ℤ => ∏ i, g i (n i)) ∧
      ∑' n : ι → ℤ, ∏ i, g i (n i) ≤ ∏ i, ∑' m, g i m := by
  have key : ∀ S : Finset (ι → ℤ), ∑ n ∈ S, ∏ i, g i (n i) ≤ ∏ i, ∑' m, g i m := by
    intro S
    set T : ι → Finset ℤ := fun i => S.image (fun n => n i)
    have hsub : S ⊆ Fintype.piFinset T := by
      intro n hn
      rw [Fintype.mem_piFinset]
      intro i
      exact mem_image_of_mem _ hn
    calc ∑ n ∈ S, ∏ i, g i (n i) ≤ ∑ n ∈ Fintype.piFinset T, ∏ i, g i (n i) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => prod_nonneg fun _ _ => hg _ _)
      _ = ∏ i, ∑ t ∈ T i, g i t := (Finset.prod_univ_sum T (fun i t => g i t)).symm
      _ ≤ ∏ i, ∑' m, g i m := prod_le_prod (fun _ _ => sum_nonneg fun _ _ => hg _ _)
          (fun i _ => (hs i).sum_le_tsum _ (fun _ _ => hg i _))
  exact ⟨summable_of_sum_le (fun _ => prod_nonneg fun _ _ => hg _ _) key,
    tsum_le_of_sum_le' (prod_nonneg fun i _ => tsum_nonneg (hg i)) key⟩

/-- **`Σ_{n ∈ ℤ^d} ⟨n⟩^{-2s} < ∞` for `s > d/2`** (the sharp lattice-sum threshold behind the
Sobolev embedding).  Proof: `⟨n⟩^{-2s} ≤ Π_i (1 + n_i²)^{-s/d}` and the one-dimensional sums
converge since `2s/d > 1`. -/
theorem summable_sobWeight_rpow_neg {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 < s) :
    Summable fun n : d → ℤ => sobWeight n ^ (-s) := by
  classical
  rcases isEmpty_or_nonempty d with hd | hd
  · exact Summable.of_finite
  have hD : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  set D : ℝ := (Fintype.card d : ℝ)
  set a : ℝ := s / D
  have ha : 1 / 2 < a := by
    rw [lt_div_iff₀ hD]; linarith
  have hs0 : 0 < s := by linarith
  have ha0 : 0 < a := by positivity
  refine Summable.of_nonneg_of_le (fun n => sobWeight_rpow_nonneg n _) (fun n => ?_)
    (summable_pi_prod (fun _ m => (1 + (m : ℝ) ^ 2) ^ (-a)) (fun _ _ => by positivity)
      (fun _ => summable_one_add_sq_rpow_neg ha)).1
  have e : sobWeight n ^ (-s) = ∏ _i : d, sobWeight n ^ (-a) := by
    rw [prod_const, card_univ, ← Real.rpow_natCast, ← Real.rpow_mul (sobWeight_pos n).le]
    congr 1
    simp only [a, D]
    field_simp
  rw [e]
  exact prod_le_prod (fun _ _ => sobWeight_rpow_nonneg n _)
    (fun i _ => Real.rpow_le_rpow_of_nonpos (by positivity) (one_add_sq_le_sobWeight n i)
      (by linarith))

/-- The embedding constant `C_{s,d} = (Σ_{n ∈ ℤ^d} ⟨n⟩^{-2s})^{1/2}`. -/
def embConst (d : Type*) [Fintype d] (s : ℝ) : ℝ :=
  Real.sqrt (∑' n : d → ℤ, sobWeight n ^ (-s))

theorem embConst_nonneg (s : ℝ) : 0 ≤ embConst d s := Real.sqrt_nonneg _

/-- **Cauchy–Schwarz on the Fourier side**: for `s > d/2`, an `H^s` coefficient family is
absolutely summable and `Σ_n |c n| ≤ C_{s,d} ‖c‖_{H^s}`. -/
theorem summable_norm_of_coeffMemH {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 < s)
    {c : (d → ℤ) → ℂ} (hc : CoeffMemH s c) :
    Summable (fun n => ‖c n‖) ∧ ∑' n, ‖c n‖ ≤ embConst d s * Real.sqrt (coeffSobSq s c) := by
  set f : (d → ℤ) → ℝ := fun n => sobWeight n ^ (-s / 2)
  set g : (d → ℤ) → ℝ := fun n => sobWeight n ^ (s / 2) * ‖c n‖
  have hf : ∀ n, 0 ≤ f n := fun n => sobWeight_rpow_nonneg n _
  have hg : ∀ n, 0 ≤ g n := fun n => mul_nonneg (sobWeight_rpow_nonneg n _) (norm_nonneg _)
  have hf2 : ∀ n, f n ^ (2 : ℝ) = sobWeight n ^ (-s) := by
    intro n
    simp only [f]
    rw [← Real.rpow_mul (sobWeight_pos n).le]
    congr 1; ring
  have hg2 : ∀ n, g n ^ (2 : ℝ) = sobWeight n ^ s * ‖c n‖ ^ 2 := by
    intro n
    simp only [g]
    rw [Real.rpow_two, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (sobWeight_pos n).le]
    congr 2; push_cast; ring
  have hfg : ∀ n, f n * g n = ‖c n‖ := by
    intro n
    simp only [f, g]
    rw [← mul_assoc, ← Real.rpow_add (sobWeight_pos n)]
    have : -s / 2 + s / 2 = 0 := by ring
    rw [this, Real.rpow_zero, one_mul]
  have hfs : Summable fun n => f n ^ (2 : ℝ) := by
    simp_rw [hf2]; exact summable_sobWeight_rpow_neg hs
  have hgs : Summable fun n => g n ^ (2 : ℝ) := by simp_rw [hg2]; exact hc
  have hH := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hf
    hg hfs hgs
  simp_rw [hfg, hf2, hg2] at hH
  refine ⟨hH.1, ?_⟩
  rw [embConst, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hH.2

/-! ### Uniformly convergent Fourier series -/

/-- The uniformly convergent Fourier series `Σ_n c_n e_n` as a continuous function
(the value is `0` if the family is not summable in `C(𝕋^d, ℂ)`). -/
def fourierSum (c : (d → ℤ) → ℂ) : C(UnitAddTorus d, ℂ) := ∑' n, c n • mFourier n

theorem summable_fourierSeries {c : (d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) :
    Summable fun n => c n • mFourier n :=
  Summable.of_norm (by simpa only [norm_smul, mFourier_norm, mul_one] using hc)

theorem hasSum_fourierSum {c : (d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) :
    HasSum (fun n => c n • mFourier n) (fourierSum c) :=
  (summable_fourierSeries hc).hasSum

theorem norm_fourierSum_le {c : (d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) :
    ‖fourierSum c‖ ≤ ∑' n, ‖c n‖ := by
  have hn : Summable fun n => ‖c n • mFourier n‖ := by
    simpa only [norm_smul, mFourier_norm, mul_one] using hc
  refine (norm_tsum_le_tsum_norm hn).trans (le_of_eq ?_)
  simp only [norm_smul, mFourier_norm, mul_one]

theorem fourierSum_apply {c : (d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖)
    (x : UnitAddTorus d) : HasSum (fun n => c n * mFourier n x) (fourierSum c x) := by
  have := (ContinuousMap.evalCLM ℂ x).hasSum (hasSum_fourierSum hc)
  simpa [ContinuousMap.evalCLM_apply] using this

/-- Fourier coefficients of a continuous function as `L²` inner products with the monomials. -/
theorem mFourierCoeff_eq_inner (g : C(UnitAddTorus d, ℂ)) (m : d → ℤ) :
    mFourierCoeff g m = ⟪mFourierLp 2 m, g.toLp 2 volume ℂ⟫_ℂ := by
  rw [← mFourierCoeff_toLp, ← mFourierBasis_repr, mFourierBasis.repr_apply_apply,
    coe_mFourierBasis]

/-- **The Fourier coefficients of `Σ_n c_n e_n` are `c`** (absolutely summable `c`). -/
theorem mFourierCoeff_fourierSum {c : (d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖)
    (m : d → ℤ) : mFourierCoeff (fourierSum c) m = c m := by
  classical
  rw [mFourierCoeff_eq_inner]
  have h := (hasSum_fourierSum hc).mapL
    ((innerSL ℂ (mFourierLp (d := d) 2 m)).comp (ContinuousMap.toLp 2 volume ℂ))
  have e : ∀ n, ((innerSL ℂ (mFourierLp (d := d) 2 m)).comp (ContinuousMap.toLp 2 volume ℂ))
      (c n • mFourier n) = if n = m then c m else 0 := by
    intro n
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, map_smul, innerSL_apply_apply]
    have ho := orthonormal_iff_ite.mp (orthonormal_mFourier (d := d)) m n
    rw [ho]
    by_cases hnm : n = m
    · subst hnm; simp
    · rw [if_neg (Ne.symm hnm), if_neg hnm, smul_zero]
  simp only [e] at h
  exact h.unique (hasSum_ite_eq m (c m))

/-! ### The Sobolev embedding `H^s(𝕋^d) ⊂ C⁰(𝕋^d)` for `s > d/2` -/

/-- A continuous `H^s` function, `s > d/2`, is the sum of its uniformly convergent Fourier
series. -/
theorem eq_fourierSum_of_memH {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 < s)
    (F : C(UnitAddTorus d, ℂ)) (hF : MemH s F) : F = fourierSum (mFourierCoeff F) := by
  have h1 := (summable_norm_of_coeffMemH hs hF).1
  exact (hasSum_mFourier_series_of_summable h1.of_norm).unique (hasSum_fourierSum h1)

/-- **Sobolev embedding, continuous form** (`s > d/2`): `‖F‖_∞ ≤ C_{s,d} ‖F‖_{H^s}`. -/
theorem norm_le_of_memH {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 < s)
    (F : C(UnitAddTorus d, ℂ)) (hF : MemH s F) : ‖F‖ ≤ embConst d s * sobNorm s F := by
  obtain ⟨h1, h2⟩ := summable_norm_of_coeffMemH hs hF
  calc ‖F‖ = ‖fourierSum (mFourierCoeff F)‖ := by rw [← eq_fourierSum_of_memH hs F hF]
    _ ≤ ∑' n, ‖mFourierCoeff F n‖ := norm_fourierSum_le h1
    _ ≤ _ := h2

theorem norm_apply_le_of_memH {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 < s)
    (F : C(UnitAddTorus d, ℂ)) (hF : MemH s F) (x : UnitAddTorus d) :
    ‖F x‖ ≤ embConst d s * sobNorm s F :=
  (F.norm_coe_le_norm x).trans (norm_le_of_memH hs F hF)

/-- **Sobolev embedding `H^s(𝕋^d) ⊂ C⁰(𝕋^d)` for `s > d/2`** (`prop:sobolev-bosonic`,
`cor:stress-topology`): every `f ∈ L²(𝕋^d)` with finite `H^s` norm has a continuous
representative `g` — `g = f` in `L²`, hence a.e. — whose Fourier series converges uniformly,
with the same Fourier coefficients and `‖g‖_∞ ≤ C_{s,d} ‖f‖_{H^s}`. -/
theorem exists_continuous_of_memH {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 < s)
    (f : L²(UnitAddTorus d)) (hf : MemH s f) :
    ∃ g : C(UnitAddTorus d, ℂ), g.toLp 2 volume ℂ = f ∧ (⇑f =ᵐ[volume] ⇑g) ∧
      (∀ n, mFourierCoeff g n = mFourierCoeff f n) ∧
      HasSum (fun n => mFourierCoeff f n • mFourier n) g ∧
      ‖g‖ ≤ embConst d s * sobNorm s f := by
  obtain ⟨h1, h2⟩ := summable_norm_of_coeffMemH hs hf
  set g := fourierSum (mFourierCoeff ⇑f)
  have hcoef : ∀ n, mFourierCoeff g n = mFourierCoeff f n := mFourierCoeff_fourierSum h1
  have heq : g.toLp 2 volume ℂ = f := by
    apply mFourierBasis.repr.injective
    ext n
    rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_toLp, hcoef]
  refine ⟨g, heq, ?_, hcoef, hasSum_fourierSum h1, (norm_fourierSum_le h1).trans h2⟩
  have := ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) g
  rw [heq] at this
  exact this

/-! ### Rellich–Kondrachov on `𝕋^d` -/

theorem finite_sobWeight_lt (R : ℝ) : {n : d → ℤ | sobWeight n < R}.Finite := by
  obtain ⟨M, hM⟩ := exists_nat_gt R
  refine (Set.Finite.pi (t := fun _ : d => Set.Icc (-(M : ℤ)) M)
    fun _ => Set.finite_Icc _ _).subset ?_
  intro n hn
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro i
  have h1 := one_add_sq_le_sobWeight n i
  have hn' : sobWeight n < R := hn
  have hsq : ((n i : ℝ)) ^ 2 < (M : ℝ) := by linarith
  have hsqZ : (n i) ^ 2 < (M : ℤ) := by exact_mod_cast hsq
  have habs : |n i| ≤ (M : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact (Int.natAbs_le_self_sq _).trans hsqZ.le
  exact abs_le.mp habs

/-- **Rellich–Kondrachov on `𝕋^d`, coefficient form** (`prop:sobolev-bosonic`, `prop:orlicz`):
for real `t < s`, a sequence bounded in `H^s` has a subsequence converging coefficientwise to some
`cl ∈ H^s` (with the same bound) and **strongly in `H^t`**. -/
theorem rellich_coeff {t s : ℝ} (hts : t < s) {B : ℝ} (c : ℕ → (d → ℤ) → ℂ)
    (hc : ∀ k, CoeffMemH s (c k)) (hB : ∀ k, coeffSobSq s (c k) ≤ B) :
    ∃ (φ : ℕ → ℕ) (cl : (d → ℤ) → ℂ), StrictMono φ ∧
      (∀ n, Tendsto (fun k => c (φ k) n) atTop (𝓝 (cl n))) ∧
      CoeffMemH s cl ∧ coeffSobSq s cl ≤ B ∧
      (∀ k, CoeffMemH t (c (φ k) - cl)) ∧
      Tendsto (fun k => coeffSobSq t (c (φ k) - cl)) atTop (𝓝 0) := by
  have hfin : ∀ R : ℝ, {n : d → ℤ | sobWeight n ^ s < R * sobWeight n ^ t}.Finite := by
    intro R
    refine (finite_sobWeight_lt (R ^ (s - t)⁻¹)).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    have hwt := sobWeight_rpow_pos n t
    have h1 : sobWeight n ^ (s - t) < R := by
      rw [Real.rpow_sub (sobWeight_pos n), div_lt_iff₀ hwt]; exact hn
    have hst : 0 < (s - t)⁻¹ := inv_pos.mpr (by linarith)
    have := Real.rpow_lt_rpow (sobWeight_rpow_nonneg n _) h1 hst
    rwa [← Real.rpow_mul (sobWeight_pos n).le, mul_inv_cancel₀ (by linarith),
      Real.rpow_one] at this
  obtain ⟨φ, cl, hφ, h1, h2, h3, h4, h5⟩ := FourierRellich.rellich_coefficients
    (fun n => sobWeight n ^ s) (fun n => sobWeight n ^ t) (fun n => sobWeight_rpow_pos n s)
    (fun n => sobWeight_rpow_nonneg n t) hfin c hc hB
  exact ⟨φ, cl, hφ, h1, h2, h3, h4, h5⟩

/-- **Rellich–Kondrachov on `𝕋^d`, `L²` form** (`prop:sobolev-bosonic`, `prop:orlicz`): for
`0 ≤ s` and `t < s`, a sequence of `L²(𝕋^d)` functions bounded in `H^s` has a subsequence
converging in `H^t` to some `g ∈ H^s` with `‖g‖²_{H^s} ≤ B`. -/
theorem rellich_L2 {t s : ℝ} (hts : t < s) (hs0 : 0 ≤ s) {B : ℝ}
    (f : ℕ → L²(UnitAddTorus d)) (hf : ∀ k, MemH s (f k)) (hB : ∀ k, sobSq s (f k) ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : L²(UnitAddTorus d)), StrictMono φ ∧ MemH s g ∧ sobSq s g ≤ B ∧
      (∀ k, MemH t ⇑(f (φ k) - g)) ∧
      Tendsto (fun k => sobSq t ⇑(f (φ k) - g)) atTop (𝓝 0) := by
  obtain ⟨φ, cl, hφ, -, h2, h3, h4, h5⟩ :=
    rellich_coeff hts (fun k => mFourierCoeff ⇑(f k)) hf hB
  have hsq : Summable fun n => ‖cl n‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => le_mul_of_one_le_left (sq_nonneg _) (one_le_sobWeight_rpow n hs0)) h2
  have hmem : Memℓp cl 2 := by
    refine memℓp_gen ?_
    simpa using hsq
  set g : L²(UnitAddTorus d) := mFourierBasis.repr.symm ⟨cl, hmem⟩
  have hg : ∀ n, mFourierCoeff g n = cl n := by
    intro n
    rw [← mFourierBasis_repr]
    simp [g]
  have hsub : ∀ k, mFourierCoeff ⇑(f (φ k) - g) = mFourierCoeff ⇑(f (φ k)) - cl := by
    intro k; funext n; rw [mFourierCoeff_Lp_sub, hg]; rfl
  refine ⟨φ, g, hφ, ?_, ?_, ?_, ?_⟩
  · show CoeffMemH s (mFourierCoeff g); rw [funext hg]; exact h2
  · unfold sobSq; rw [funext hg]; exact h3
  · intro k; show CoeffMemH t _; rw [hsub]; exact h4 k
  · simp only [sobSq, hsub]; exact h5

theorem mFourierCoeff_continuous_sub (F G : C(UnitAddTorus d, ℂ)) (n : d → ℤ) :
    mFourierCoeff ⇑(F - G) n = mFourierCoeff F n - mFourierCoeff G n := by
  rw [← mFourierCoeff_toLp (F - G), map_sub, mFourierCoeff_Lp_sub, mFourierCoeff_toLp,
    mFourierCoeff_toLp]

/-- **Compactness of `H^s ⊂ C⁰` for `s > d/2`** (`prop:sobolev-bosonic`): a sequence of continuous
functions bounded in `H^s(𝕋^d)` has a uniformly convergent subsequence, whose limit lies in `H^s`
with the same bound.  Proof: Rellich into `H^t`, `d/2 < t < s`, then the embedding
`H^t ⊂ C⁰`. -/
theorem rellich_C0 {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 < s) {B : ℝ}
    (F : ℕ → C(UnitAddTorus d, ℂ)) (hF : ∀ k, MemH s (F k)) (hB : ∀ k, sobSq s (F k) ≤ B) :
    ∃ (φ : ℕ → ℕ) (G : C(UnitAddTorus d, ℂ)), StrictMono φ ∧ MemH s G ∧ sobSq s G ≤ B ∧
      Tendsto (fun k => ‖F (φ k) - G‖) atTop (𝓝 0) := by
  set t := ((Fintype.card d : ℝ) / 2 + s) / 2 with ht_def
  have ht : (Fintype.card d : ℝ) / 2 < t := by rw [ht_def]; linarith
  have hts : t < s := by rw [ht_def]; linarith
  obtain ⟨φ, cl, hφ, -, h2, h3, h4, h5⟩ :=
    rellich_coeff hts (fun k => mFourierCoeff ⇑(F k)) hF hB
  have hcl := (summable_norm_of_coeffMemH hs h2).1
  set G := fourierSum cl
  have hG : ∀ n, mFourierCoeff G n = cl n := mFourierCoeff_fourierSum hcl
  have hsub : ∀ k, mFourierCoeff ⇑(F (φ k) - G) = mFourierCoeff ⇑(F (φ k)) - cl := by
    intro k; funext n; rw [mFourierCoeff_continuous_sub, hG]; rfl
  refine ⟨φ, G, hφ, ?_, ?_, ?_⟩
  · show CoeffMemH s (mFourierCoeff G); rw [funext hG]; exact h2
  · unfold sobSq; rw [funext hG]; exact h3
  · have hbound : ∀ k, ‖F (φ k) - G‖ ≤
        embConst d t * Real.sqrt (coeffSobSq t (mFourierCoeff ⇑(F (φ k)) - cl)) := by
      intro k
      have hm : MemH t ⇑(F (φ k) - G) := by show CoeffMemH t _; rw [hsub]; exact h4 k
      have := norm_le_of_memH ht _ hm
      unfold sobNorm sobSq at this
      rwa [hsub] at this
    have hlim : Tendsto (fun k => embConst d t *
        Real.sqrt (coeffSobSq t (mFourierCoeff ⇑(F (φ k)) - cl))) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp h5).const_mul (embConst d t)
      simpa [Function.comp_def] using this
    exact squeeze_zero (fun k => norm_nonneg _) hbound hlim

/-- On the probability space `𝕋^d`, every `L^p` norm of a continuous function is at most its
sup norm. -/
theorem eLpNorm_le_norm (F : C(UnitAddTorus d, ℂ)) (p : ℝ≥0∞) :
    eLpNorm F p volume ≤ ENNReal.ofReal ‖F‖ := by
  refine (eLpNorm_le_of_ae_bound (Eventually.of_forall fun x => F.norm_coe_le_norm x)).trans ?_
  simp [measure_univ]

/-- Uniform convergence on `𝕋^d` implies convergence in every `L^p`, `p ≤ ∞`. -/
theorem tendsto_eLpNorm_of_tendsto_norm {G : ℕ → C(UnitAddTorus d, ℂ)}
    (hG : Tendsto (fun k => ‖G k‖) atTop (𝓝 0)) (p : ℝ≥0∞) :
    Tendsto (fun k => eLpNorm (G k) p volume) atTop (𝓝 0) := by
  have h := ENNReal.tendsto_ofReal hG
  rw [ENNReal.ofReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    (fun k => eLpNorm_le_norm _ p)

/-- **Bounded sets of `H^s(𝕋^d)`, `s > d/2`, are precompact in `H^t` (`t < s`), in `C⁰` and in
every `L^p`** (`prop:sobolev-bosonic`, torus rendering; for `d = 4`, `s = 2 + σ`, `t = 1`: the
`H^{2+σ} ⋐ H¹ ∩ C⁰ ∩ L^p` step).  For a sequence `f_k ∈ L²(𝕋^d)` with `‖f_k‖²_{H^s} ≤ B`
there are a subsequence, a limit `g ∈ H^s`, continuous representatives `G_k = f_k`,
`G = g` (a.e.), with `‖f_{φ k} - g‖_{H^t} → 0`, `‖G_{φ k} - G‖_∞ → 0` and
`‖f_{φ k} - g‖_{L^p} → 0` for every `p`. -/
theorem precompact_of_bounded_memH {t s : ℝ} (hs : (Fintype.card d : ℝ) / 2 < s) (hts : t < s)
    {B : ℝ} (f : ℕ → L²(UnitAddTorus d)) (hf : ∀ k, MemH s (f k))
    (hB : ∀ k, sobSq s (f k) ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : L²(UnitAddTorus d)) (Gs : ℕ → C(UnitAddTorus d, ℂ))
      (G : C(UnitAddTorus d, ℂ)), StrictMono φ ∧ MemH s g ∧ sobSq s g ≤ B ∧
      (∀ k, ⇑(f k) =ᵐ[volume] ⇑(Gs k)) ∧ (⇑g =ᵐ[volume] ⇑G) ∧
      (∀ k, MemH t ⇑(f (φ k) - g)) ∧
      Tendsto (fun k => sobSq t ⇑(f (φ k) - g)) atTop (𝓝 0) ∧
      Tendsto (fun k => ‖Gs (φ k) - G‖) atTop (𝓝 0) ∧
      ∀ p : ℝ≥0∞, Tendsto (fun k => eLpNorm (⇑(f (φ k)) - ⇑g) p volume) atTop (𝓝 0) := by
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ (Fintype.card d : ℝ) / 2 := by positivity
    linarith
  -- a common subsequence for the `H^t` and the uniform convergence: use `max t t'`
  set t' := max t (((Fintype.card d : ℝ) / 2 + s) / 2) with ht'_def
  have ht' : (Fintype.card d : ℝ) / 2 < t' :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hts' : t' < s := max_lt hts (by linarith)
  obtain ⟨φ, g, hφ, hgs, hgB, hm, hlim⟩ := rellich_L2 hts' hs0 f hf hB
  choose Gs hGs using fun k => exists_continuous_of_memH hs (f k) (hf k)
  obtain ⟨G, hGL, hGae, hGc, -, -⟩ := exists_continuous_of_memH hs g hgs
  have hdiff : ∀ k, mFourierCoeff ⇑(Gs (φ k) - G) = mFourierCoeff ⇑(f (φ k) - g) := by
    intro k; funext n
    rw [mFourierCoeff_continuous_sub, mFourierCoeff_Lp_sub, (hGs (φ k)).2.2.1 n, hGc n]
  have hunif : Tendsto (fun k => ‖Gs (φ k) - G‖) atTop (𝓝 0) := by
    have hbound : ∀ k, ‖Gs (φ k) - G‖ ≤ embConst d t' * Real.sqrt (sobSq t' ⇑(f (φ k) - g)) := by
      intro k
      have hmk : MemH t' ⇑(Gs (φ k) - G) := by
        show CoeffMemH t' _; rw [hdiff]; exact hm k
      have := norm_le_of_memH ht' _ hmk
      unfold sobNorm sobSq at this
      rw [hdiff] at this
      exact this
    have hl : Tendsto (fun k => embConst d t' * Real.sqrt (sobSq t' ⇑(f (φ k) - g))) atTop
        (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp hlim).const_mul (embConst d t')
      simpa [Function.comp_def] using this
    exact squeeze_zero (fun k => norm_nonneg _) hbound hl
  refine ⟨φ, g, Gs, G, hφ, hgs, hgB, fun k => (hGs k).2.1, hGae, fun k => (hm k).mono
    (le_max_left _ _), ?_, hunif, fun p => ?_⟩
  · refine squeeze_zero (fun k => sobSq_nonneg _ _) (fun k => ?_) hlim
    exact coeffSobSq_mono (le_max_left _ _) (hm k)
  · have hLp := tendsto_eLpNorm_of_tendsto_norm hunif p
    refine hLp.congr fun k => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hGs (φ k)).2.1, hGae] with x h1 h2
    simp [h1, h2]

/-! ### Monomials and non-vacuity -/

/-- Monomials have modulus one pointwise. -/
theorem norm_mFourier_apply (n : d → ℤ) (x : UnitAddTorus d) : ‖mFourier n x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod]
  exact Finset.prod_eq_one fun i _ => by
    rw [fourier_apply]; exact Circle.norm_coe _

/-- The Fourier coefficients of a monomial: `ê_m(n) = δ_{nm}`. -/
theorem mFourierCoeff_mFourier (m n : d → ℤ) :
    mFourierCoeff (⇑(mFourier m)) n = if n = m then 1 else 0 := by
  rw [mFourierCoeff_eq_inner]
  exact orthonormal_iff_ite.mp (orthonormal_mFourier (d := d)) n m

/-- Every monomial lies in every `H^s`. -/
theorem memH_mFourier (s : ℝ) (m : d → ℤ) : MemH s (⇑(mFourier m)) := by
  unfold MemH CoeffMemH
  simp_rw [mFourierCoeff_mFourier]
  refine summable_of_ne_finset_zero (s := {m}) fun n hn => ?_
  rw [Finset.mem_singleton] at hn
  simp [hn]

/-- `‖e_m‖²_{H^s} = ⟨m⟩^{2s}`. -/
theorem sobSq_mFourier (s : ℝ) (m : d → ℤ) : sobSq s (⇑(mFourier m)) = sobWeight m ^ s := by
  unfold sobSq coeffSobSq
  simp_rw [mFourierCoeff_mFourier]
  rw [tsum_eq_single m fun n hn => by simp [hn]]
  simp

/-- Non-vacuity of the embedding: a monomial on `𝕋⁴` in `H³` (`3 > 4/2`). -/
example (m : Fin 4 → ℤ) :
    ‖mFourier m‖ ≤ embConst (Fin 4) 3 * sobNorm 3 (⇑(mFourier m)) :=
  norm_le_of_memH (by norm_num) _ (memH_mFourier 3 m)

/-- Non-vacuity of interpolation: `‖e_m‖_{H^1} ≤ ‖e_m‖_{H^0}^{1/2} ‖e_m‖_{H^2}^{1/2}` on `𝕋³`. -/
example (m : Fin 3 → ℤ) :
    sobNorm 1 (⇑(mFourier m)) ≤
      sobNorm 0 (⇑(mFourier m)) ^ (1 - 1 / 2 : ℝ) * sobNorm 2 (⇑(mFourier m)) ^ (1 / 2 : ℝ) :=
  (sobNorm_interpolation (by norm_num) (by norm_num) (by norm_num) (memH_mFourier 0 m)
    (memH_mFourier 2 m)).2

/-- Non-vacuity of the `C⁰` compactness statement: the hypotheses hold for the sequence of
monomials `k ↦ e_{(k mod 2) v}`, bounded in `H^{5/2}(𝕋⁴)`. -/
example (v : Fin 4 → ℤ) :
    ∃ (φ : ℕ → ℕ) (G : C(UnitAddTorus (Fin 4), ℂ)), StrictMono φ ∧
      MemH (5 / 2) ⇑G ∧ sobSq (5 / 2) ⇑G ≤ sobWeight v ^ (5 / 2 : ℝ) ∧
      Tendsto (fun k => ‖mFourier ((φ k % 2 : ℕ) • v) - G‖) atTop (𝓝 0) := by
  refine rellich_C0 (s := 5 / 2) (by norm_num) (fun k => mFourier ((k % 2 : ℕ) • v))
    (fun k => memH_mFourier _ _) (fun k => ?_)
  rw [sobSq_mFourier]
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [h, zero_smul, show sobWeight (0 : Fin 4 → ℤ) = 1 by simp [sobWeight], Real.one_rpow]
    exact Real.one_le_rpow (one_le_sobWeight v) (by norm_num)
  · rw [h, one_smul]

/-! ### Space-time interpolation: `L²_t H^k_x` between `L²_t L²_x` and `L²_t H^s_x` -/

/-- **Interpolation in `L²_t H^k_x`** (`prop:shadow-residual-upgrade`, cylinder form with a
non-periodic time interval, or any measure space of times): for a family `u(t) ∈ L²(𝕋^d) ∩ H^s`
and `0 ≤ k ≤ s`, `s > 0`,
`∫ ‖u(t)‖²_{H^k} dt ≤ (∫ ‖u(t)‖²_{L²} dt)^{1-k/s} (∫ ‖u(t)‖²_{H^s} dt)^{k/s}`
(pointwise interpolation, then Hölder in `t` with exponents `1/(1-k/s)`, `s/k`; lower
integrals, so no integrability assumption is needed). -/
theorem lintegral_sobSq_interpolation {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {k s : ℝ} (hk : 0 ≤ k) (hks : k ≤ s) (hs : 0 < s) (u : α → L²(UnitAddTorus d))
    (hu : ∀ t, MemH s (u t))
    (h0 : AEMeasurable (fun t => ENNReal.ofReal (sobSq 0 (u t))) μ)
    (hS : AEMeasurable (fun t => ENNReal.ofReal (sobSq s (u t))) μ) :
    ∫⁻ t, ENNReal.ofReal (sobSq k (u t)) ∂μ ≤
      (∫⁻ t, ENNReal.ofReal (sobSq 0 (u t)) ∂μ) ^ (1 - k / s) *
        (∫⁻ t, ENNReal.ofReal (sobSq s (u t)) ∂μ) ^ (k / s) := by
  set θ := k / s with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hk hs.le
  have hθ1 : θ ≤ 1 := (div_le_one hs).mpr hks
  -- pointwise interpolation
  have hpt : ∀ t, ENNReal.ofReal (sobSq k (u t)) ≤
      ENNReal.ofReal (sobSq 0 (u t)) ^ (1 - θ) * ENNReal.ofReal (sobSq s (u t)) ^ θ := by
    intro t
    have h := (coeffSobSq_interpolation hk hks hs (memH_zero_of_L2 (u t)) (hu t)).2
    rw [ENNReal.ofReal_rpow_of_nonneg (sobSq_nonneg _ _) (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (sobSq_nonneg _ _) hθ0, ← ENNReal.ofReal_mul
        (Real.rpow_nonneg (sobSq_nonneg _ _) _)]
    exact ENNReal.ofReal_le_ofReal h
  refine (lintegral_mono hpt).trans ?_
  rcases hθ0.eq_or_lt with h | h
  · simp [← h]
  rcases hθ1.eq_or_lt with h' | h'
  · simp [h']
  have hpq := Real.holderConjugate_one_div (a := 1 - θ) (b := θ) (by linarith) h (by ring)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (h0.pow_const (1 - θ)) (hS.pow_const θ)
  have e1 : ∀ t, (ENNReal.ofReal (sobSq 0 (u t)) ^ (1 - θ)) ^ (1 / (1 - θ)) =
      ENNReal.ofReal (sobSq 0 (u t)) := by
    intro t
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (by linarith), ENNReal.rpow_one]
  have e2 : ∀ t, (ENNReal.ofReal (sobSq s (u t)) ^ θ) ^ (1 / θ) =
      ENNReal.ofReal (sobSq s (u t)) := by
    intro t
    rw [← ENNReal.rpow_mul, mul_one_div_cancel h.ne', ENNReal.rpow_one]
  simp only [Pi.mul_apply, e1, e2, one_div_one_div] at hH
  exact hH

end

end RenewalGeometry.TorusSobolev
