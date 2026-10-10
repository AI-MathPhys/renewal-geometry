/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.FlatHodgeWeitzenbock
import RenewalGeometry.Continuum.NativeCoulombFourier

/-!
# Hodge, Poincaré, integration by parts and critical Sobolev estimates on the flat torus
  (step (a) of Uhlenbeck's small-energy Coulomb gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (K. Uhlenbeck, *Connections with `L^p` bounds on
curvature*, Comm. Math. Phys. 83 (1982), Thm 1.3, case `p = n/2 = 2`), in the **periodic
rendering**: functions on the flat unit torus `𝕋^d = UnitAddTorus d` (Haar probability measure),
derivatives through the Fourier rule.

* `IsTPartial μ f g` : `g` is the (weak) partial derivative `∂_μ f` on `𝕋^d`, i.e.
  `ĝ(n) = 2πi n_μ f̂(n)` for every `n ∈ ℤ^d` (the torus definition of the weak derivative);
  linearity (`IsTPartial.sub`, `.const_mul`, `.sub_const`).
* `weitzenbock_torus` (**flat Weitzenböck identity on `𝕋^d`**): for a one-form `w` with `L²`
  partials `g ν μ = ∂_μ w_ν`,
  `Σ_{μν} ‖∂_μ w_ν‖²_{L²} = ½ Σ_{μν} ‖(dw)_{μν}‖²_{L²} + ‖d^*w‖²_{L²}`
  (Parseval and the Lagrange identity mode by mode; no boundary terms, no compact support).
* `eLpNorm_partial_le_curl_div` (**Hodge estimate**): every partial derivative is bounded by
  the exterior derivative and the codifferential,
  `‖∂_μ w_ν‖_{L²} ≤ Σ_{μ'ν'} ‖(dw)_{μ'ν'}‖_{L²} + ‖d^*w‖_{L²}`.
* `integral_sq_le_of_mean_zero`, `eLpNorm_le_of_mean_zero` (**Poincaré inequality**): for
  `f̂(0) = 0`, `‖f‖²_{L²} ≤ Σ_μ ‖∂_μ f‖²_{L²}` (spectral gap `4π² ≥ 1`).
* `integral_conj_partial_mul` (**integration by parts**): `⟨∂_μ u, v⟩ = -⟨u, ∂_μ v⟩` for
  `u, v, ∂_μ u, ∂_μ v ∈ L²` (Parseval for inner products).
* `eLpNorm_four_le_torus` (**critical Sobolev inequality `H¹(𝕋⁴) ⊂ L⁴`, derivative form**):
  `‖f‖_{L⁴} ≤ 3 Σ_μ ‖∂_μ f‖_{L²} + 4 ‖f‖_{L²}`, and for mean-zero `f`,
  `‖f‖_{L⁴} ≤ 7 Σ_μ ‖∂_μ f‖_{L²}` (`eLpNorm_four_le_of_mean_zero`).
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace RenewalGeometry.UhlenbeckTorus

open SobolevOpen TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Torus partial derivatives through the Fourier rule -/

/-- The Fourier symbol `2πi n_μ` of `∂_μ` on `𝕋^d`. -/
def sym (μ : d) (n : d → ℤ) : ℂ := 2 * π * Complex.I * (n μ : ℂ)

theorem sym_eq (μ : d) (n : d → ℤ) : sym μ n = Complex.I * ((2 * π * (n μ : ℝ) : ℝ) : ℂ) := by
  unfold sym; push_cast; ring

theorem norm_sym_sq (μ : d) (n : d → ℤ) : ‖sym μ n‖ ^ 2 = (2 * π * (n μ : ℝ)) ^ 2 := by
  rw [sym_eq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem conj_sym (μ : d) (n : d → ℤ) : conj (sym μ n) = -sym μ n := by
  rw [sym_eq, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring

theorem sym_zero (μ : d) : sym μ (0 : d → ℤ) = 0 := by simp [sym]

/-- `g = ∂_μ f` on the torus `𝕋^d`: `ĝ(n) = 2πi n_μ f̂(n)` for every frequency `n`. -/
def IsTPartial (μ : d) (f g : UnitAddTorus d → ℂ) : Prop :=
  ∀ n, mFourierCoeff g n = sym μ n * mFourierCoeff f n

theorem integrable_of_memLp_two {f : UnitAddTorus d → ℂ} (hf : MemLp f 2 volume) :
    Integrable f volume := hf.integrable one_le_two

theorem mFourierCoeff_const_mul (c : ℂ) (f : UnitAddTorus d → ℂ) (n : d → ℤ) :
    mFourierCoeff (fun x => c * f x) n = c * mFourierCoeff f n := by
  unfold mFourierCoeff
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext t; ring

/-- Fourier coefficients of a constant function. -/
theorem mFourierCoeff_const (c : ℂ) (n : d → ℤ) :
    mFourierCoeff (fun _ : UnitAddTorus d => c) n = if n = 0 then c else 0 := by
  have e : (fun _ : UnitAddTorus d => c) = ⇑(trigPoly ({0} : Finset (d → ℤ)) fun _ => c) := by
    funext x
    simp [trigPoly, mFourier_zero]
  rw [e, mFourierCoeff_trigPoly]
  simp

theorem IsTPartial.sub {μ : d} {f₁ f₂ g₁ g₂ : UnitAddTorus d → ℂ} (h₁ : IsTPartial μ f₁ g₁)
    (h₂ : IsTPartial μ f₂ g₂) (hf₁ : Integrable f₁ volume) (hf₂ : Integrable f₂ volume)
    (hg₁ : Integrable g₁ volume) (hg₂ : Integrable g₂ volume) :
    IsTPartial μ (fun x => f₁ x - f₂ x) (fun x => g₁ x - g₂ x) := by
  intro n
  rw [mFourierCoeff_sub hg₁ hg₂, mFourierCoeff_sub hf₁ hf₂, h₁ n, h₂ n]; ring

theorem IsTPartial.const_mul {μ : d} {f g : UnitAddTorus d → ℂ} (h : IsTPartial μ f g) (c : ℂ) :
    IsTPartial μ (fun x => c * f x) (fun x => c * g x) := by
  intro n
  rw [mFourierCoeff_const_mul, mFourierCoeff_const_mul, h n]; ring

/-- Subtracting a constant does not change the derivative. -/
theorem IsTPartial.sub_const {μ : d} {f g : UnitAddTorus d → ℂ} (h : IsTPartial μ f g)
    (hf : Integrable f volume) (c : ℂ) : IsTPartial μ (fun x => f x - c) g := by
  intro n
  rw [mFourierCoeff_sub hf (integrable_const c), mFourierCoeff_const, h n]
  by_cases hn : n = 0
  · subst hn; simp [sym_zero]
  · simp [hn]

theorem IsTPartial.finset_sum {μ : d} {κ : Type*} (s : Finset κ) {f g : κ → UnitAddTorus d → ℂ}
    (h : ∀ k, IsTPartial μ (f k) (g k)) (hf : ∀ k, Integrable (f k) volume)
    (hg : ∀ k, Integrable (g k) volume) :
    IsTPartial μ (fun x => ∑ k ∈ s, f k x) (fun x => ∑ k ∈ s, g k x) := by
  intro n
  rw [mFourierCoeff_finset_sum s hg, mFourierCoeff_finset_sum s hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => h k n

/-- The mean of `f` is its zeroth Fourier coefficient; `f - f̂(0)` has mean zero. -/
theorem mFourierCoeff_sub_mean {f : UnitAddTorus d → ℂ} (hf : Integrable f volume) :
    mFourierCoeff (fun x => f x - mFourierCoeff f 0) 0 = 0 := by
  rw [mFourierCoeff_sub hf (integrable_const _), mFourierCoeff_const]; simp

/-! ### The Weitzenböck identity and the Hodge estimate on `𝕋^d` -/

/-- **Flat Weitzenböck identity on the torus.**  For a one-form `w = (w_ν)` on `𝕋^d` whose
partial derivatives `g ν μ = ∂_μ w_ν` lie in `L²`,
`Σ_{μν} ‖∂_μ w_ν‖² = ½ Σ_{μν} ‖∂_μ w_ν - ∂_ν w_μ‖² + ‖Σ_μ ∂_μ w_μ‖²`, i.e.
`‖∇w‖² = ‖dw‖² + ‖d^*w‖²` (each unordered pair counted once in `‖dw‖²`). -/
theorem weitzenbock_torus {w : d → UnitAddTorus d → ℂ} {g : d → d → UnitAddTorus d → ℂ}
    (hg : ∀ ν μ, MemLp (g ν μ) 2 volume) (hd : ∀ ν μ, IsTPartial μ (w ν) (g ν μ)) :
    ∑ μ, ∑ ν, (∫ x, ‖g ν μ x‖ ^ 2) =
      (1 / 2) * ∑ μ, ∑ ν, (∫ x, ‖g ν μ x - g μ ν x‖ ^ 2) + ∫ x, ‖∑ μ, g μ μ x‖ ^ 2 := by
  set Wc : d → (d → ℤ) → ℂ := fun ν n => mFourierCoeff (w ν) n
  set a : (d → ℤ) → d → ℝ := fun n μ => 2 * π * (n μ : ℝ)
  have hrule : ∀ ν μ n, mFourierCoeff (g ν μ) n = Complex.I * ((a n μ : ℝ) : ℂ) * Wc ν n := by
    intro ν μ n
    rw [hd ν μ n, sym_eq]
  have hint : ∀ ν μ, Integrable (g ν μ) volume := fun ν μ => integrable_of_memLp_two (hg ν μ)
  have hcurl : ∀ μ ν n, mFourierCoeff (fun x => g ν μ x - g μ ν x) n =
      Complex.I * ((a n μ : ℂ) * Wc ν n - (a n ν : ℂ) * Wc μ n) := by
    intro μ ν n
    rw [mFourierCoeff_sub (hint ν μ) (hint μ ν), hrule, hrule]
    ring
  have hdiv : ∀ n, mFourierCoeff (fun x => ∑ μ, g μ μ x) n =
      Complex.I * ∑ μ, (a n μ : ℂ) * Wc μ n := by
    intro n
    rw [mFourierCoeff_finset_sum _ (fun μ => hint μ μ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hrule]; ring
  have hA : HasSum (fun n => ∑ μ, ∑ ν, ‖mFourierCoeff (g ν μ) n‖ ^ 2)
      (∑ μ, ∑ ν, ∫ x, ‖g ν μ x‖ ^ 2) :=
    hasSum_sum fun μ _ => hasSum_sum fun ν _ => hasSum_sq_mFourierCoeff_of_memLp (hg ν μ)
  have hB1 : ∀ μ ν, HasSum (fun n => ‖mFourierCoeff (fun x => g ν μ x - g μ ν x) n‖ ^ 2)
      (∫ x, ‖g ν μ x - g μ ν x‖ ^ 2) := fun μ ν =>
    hasSum_sq_mFourierCoeff_of_memLp ((hg ν μ).sub (hg μ ν))
  have hB2 : HasSum (fun n => ‖mFourierCoeff (fun x => ∑ μ, g μ μ x) n‖ ^ 2)
      (∫ x, ‖∑ μ, g μ μ x‖ ^ 2) :=
    hasSum_sq_mFourierCoeff_of_memLp (memLp_finsetSum _ fun μ _ => hg μ μ)
  have hB : HasSum (fun n => (1 / 2) * ∑ μ, ∑ ν,
        ‖mFourierCoeff (fun x => g ν μ x - g μ ν x) n‖ ^ 2 +
        ‖mFourierCoeff (fun x => ∑ μ, g μ μ x) n‖ ^ 2)
      ((1 / 2) * ∑ μ, ∑ ν, (∫ x, ‖g ν μ x - g μ ν x‖ ^ 2) + ∫ x, ‖∑ μ, g μ μ x‖ ^ 2) :=
    ((hasSum_sum (s := Finset.univ) fun μ _ => hasSum_sum (s := Finset.univ) fun ν _ =>
      hB1 μ ν).mul_left (1 / 2)).add hB2
  have hAB : (fun n => ∑ μ, ∑ ν, ‖mFourierCoeff (g ν μ) n‖ ^ 2) =
      fun n => (1 / 2) * ∑ μ, ∑ ν, ‖mFourierCoeff (fun x => g ν μ x - g μ ν x) n‖ ^ 2 +
        ‖mFourierCoeff (fun x => ∑ μ, g μ μ x) n‖ ^ 2 := by
    funext n
    simp only [hrule, hcurl, hdiv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    exact lagrange_identity (a n) (fun ν => Wc ν n)
  rw [hAB] at hA
  exact hA.unique hB

/-- From an identity `Σ_{μν} X_{νμ} = ½ Σ Y + Z` (nonnegative reals) to the square-root bound
`√X_{νμ} ≤ Σ √Y + √Z`. -/
theorem sqrt_le_of_weitzenbock {ι : Type*} [Fintype ι] {X Y : ι → ι → ℝ} {Z : ℝ}
    (hX : ∀ ν μ, 0 ≤ X ν μ) (hY : ∀ μ ν, 0 ≤ Y μ ν) (hZ : 0 ≤ Z)
    (hW : ∑ μ, ∑ ν, X ν μ = (1 / 2) * ∑ μ, ∑ ν, Y μ ν + Z) (ν μ : ι) :
    √(X ν μ) ≤ ∑ μ', ∑ ν', √(Y μ' ν') + √Z := by
  have h1 : X ν μ ≤ ∑ μ', ∑ ν', X ν' μ' :=
    (Finset.single_le_sum (f := fun ν' => X ν' μ) (fun _ _ => hX _ _) (Finset.mem_univ ν)).trans
      (Finset.single_le_sum (f := fun μ' => ∑ ν', X ν' μ') (fun _ _ =>
        Finset.sum_nonneg fun _ _ => hX _ _) (Finset.mem_univ μ))
  have hSY : 0 ≤ ∑ μ', ∑ ν', Y μ' ν' :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hY _ _
  have h2 : ∑ μ', ∑ ν', X ν' μ' ≤ ∑ μ', ∑ ν', Y μ' ν' + Z := by rw [hW]; linarith
  set S : ℝ := ∑ μ', ∑ ν', √(Y μ' ν') with hSd
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have h3 : ∑ μ', ∑ ν', Y μ' ν' ≤ S ^ 2 := by
    calc ∑ μ', ∑ ν', Y μ' ν' = ∑ μ', ∑ ν', √(Y μ' ν') ^ 2 := by
          simp only [Real.sq_sqrt (hY _ _)]
      _ ≤ ∑ μ', (∑ ν', √(Y μ' ν')) ^ 2 := Finset.sum_le_sum fun μ' _ =>
          Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => Real.sqrt_nonneg _
      _ ≤ S ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt hZ
  nlinarith [Real.sqrt_nonneg Z]

/-- **Hodge estimate on `𝕋^d`.**  Every partial derivative of a one-form is controlled by its
exterior derivative and codifferential:
`‖∂_μ w_ν‖_{L²} ≤ Σ_{μ'ν'} ‖∂_{μ'} w_{ν'} - ∂_{ν'} w_{μ'}‖_{L²} + ‖Σ_{μ'} ∂_{μ'} w_{μ'}‖_{L²}`. -/
theorem eLpNorm_partial_le_curl_div {w : d → UnitAddTorus d → ℂ}
    {g : d → d → UnitAddTorus d → ℂ} (hg : ∀ ν μ, MemLp (g ν μ) 2 volume)
    (hd : ∀ ν μ, IsTPartial μ (w ν) (g ν μ)) (ν μ : d) :
    eLpNorm (g ν μ) 2 volume ≤
      ∑ μ', ∑ ν', eLpNorm (fun x => g ν' μ' x - g μ' ν' x) 2 volume +
        eLpNorm (fun x => ∑ μ', g μ' μ' x) 2 volume := by
  have hc2 : ∀ μ' ν', MemLp (fun x => g ν' μ' x - g μ' ν' x) 2 volume := fun μ' ν' =>
    (hg ν' μ').sub (hg μ' ν')
  have hd2 : MemLp (fun x => ∑ μ', g μ' μ' x) 2 volume := memLp_finsetSum _ fun μ _ => hg μ μ
  have h4 := sqrt_le_of_weitzenbock (X := fun ν μ => ∫ x, ‖g ν μ x‖ ^ 2)
    (Y := fun μ' ν' => ∫ x, ‖g ν' μ' x - g μ' ν' x‖ ^ 2) (Z := ∫ x, ‖∑ μ', g μ' μ' x‖ ^ 2)
    (fun _ _ => integral_nonneg fun _ => by positivity)
    (fun _ _ => integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity) (weitzenbock_torus hg hd) ν μ
  have e : ENNReal.ofReal (∑ μ', ∑ ν', √(∫ x, ‖g ν' μ' x - g μ' ν' x‖ ^ 2) +
      √(∫ x, ‖∑ μ', g μ' μ' x‖ ^ 2)) =
      ∑ μ', ∑ ν', ENNReal.ofReal (√(∫ x, ‖g ν' μ' x - g μ' ν' x‖ ^ 2)) +
        ENNReal.ofReal (√(∫ x, ‖∑ μ', g μ' μ' x‖ ^ 2)) := by
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ENNReal.ofReal_sum_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)]
    congr 1
    refine Finset.sum_congr rfl fun μ' _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
  rw [eLpNorm_two_eq_sqrt (hg ν μ), eLpNorm_two_eq_sqrt hd2]
  simp only [eLpNorm_two_eq_sqrt (hc2 _ _)]
  exact (ENNReal.ofReal_le_ofReal h4).trans (le_of_eq e)

/-- **Hodge estimate for co-closed forms**: if `d^*w = 0` a.e., then
`‖∂_μ w_ν‖_{L²} ≤ Σ_{μ'ν'} ‖(dw)_{μ'ν'}‖_{L²}`. -/
theorem eLpNorm_partial_le_curl_of_coclosed {w : d → UnitAddTorus d → ℂ}
    {g : d → d → UnitAddTorus d → ℂ} (hg : ∀ ν μ, MemLp (g ν μ) 2 volume)
    (hd : ∀ ν μ, IsTPartial μ (w ν) (g ν μ)) (hdiv : ∀ᵐ x ∂volume, ∑ μ, g μ μ x = 0)
    (ν μ : d) :
    eLpNorm (g ν μ) 2 volume ≤ ∑ μ', ∑ ν', eLpNorm (fun x => g ν' μ' x - g μ' ν' x) 2 volume := by
  have h := eLpNorm_partial_le_curl_div hg hd ν μ
  have h0 : eLpNorm (fun x => ∑ μ', g μ' μ' x) 2 volume = 0 := by
    rw [eLpNorm_congr_ae (g := fun _ => (0 : ℂ)) hdiv]; simp
  rwa [h0, add_zero] at h

/-! ### Poincaré inequality -/

/-- **Poincaré inequality on `𝕋^d`**: for `f ∈ L²` with mean zero (`f̂(0) = 0`) and `L²`
partials, `‖f‖²_{L²} ≤ Σ_μ ‖∂_μ f‖²_{L²}` (the spectral gap of `-Δ` is `4π² ≥ 1`). -/
theorem integral_sq_le_of_mean_zero {f : UnitAddTorus d → ℂ} {g : d → UnitAddTorus d → ℂ}
    (hf : MemLp f 2 volume) (hg : ∀ μ, MemLp (g μ) 2 volume) (hd : ∀ μ, IsTPartial μ f (g μ))
    (h0 : mFourierCoeff f 0 = 0) :
    ∫ x, ‖f x‖ ^ 2 ≤ ∑ μ, ∫ x, ‖g μ x‖ ^ 2 := by
  refine hasSum_le (fun n => ?_) (hasSum_sq_mFourierCoeff_of_memLp hf)
    (hasSum_sum fun μ _ => hasSum_sq_mFourierCoeff_of_memLp (hg μ))
  have e : ∀ μ, ‖mFourierCoeff (g μ) n‖ ^ 2 = (2 * π * (n μ : ℝ)) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
    fun μ => by rw [hd μ n, norm_mul, mul_pow, norm_sym_sq]
  simp only [e]
  by_cases hn : n = 0
  · subst hn; rw [h0]; simp
  · obtain ⟨μ, hμ⟩ : ∃ μ, n μ ≠ 0 := by
      by_contra h; exact hn (funext fun μ => by simpa using not_exists.mp h μ)
    have h1 : (1 : ℝ) ≤ (n μ : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ (n μ) ^ 2 := by
        rcases lt_or_gt_of_ne hμ with h | h <;> nlinarith
      exact_mod_cast this
    have h2 : 1 ≤ (2 * π * (n μ : ℝ)) ^ 2 := by
      have := four_pi_sq_ge_one
      calc (1 : ℝ) ≤ 4 * π ^ 2 * 1 := by linarith
        _ ≤ 4 * π ^ 2 * (n μ : ℝ) ^ 2 := by gcongr
        _ = (2 * π * (n μ : ℝ)) ^ 2 := by ring
    calc ‖mFourierCoeff f n‖ ^ 2 ≤ (2 * π * (n μ : ℝ)) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
          le_mul_of_one_le_left (by positivity) h2
      _ ≤ ∑ μ', (2 * π * (n μ' : ℝ)) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
          Finset.single_le_sum (f := fun μ' => (2 * π * (n μ' : ℝ)) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ μ)

/-- `√(Σ x_i) ≤ Σ √x_i` for nonnegative reals. -/
theorem sqrt_sum_le_sum_sqrt {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    √(∑ i ∈ s, x i) ≤ ∑ i ∈ s, √(x i) := by
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)]
  calc ∑ i ∈ s, x i = ∑ i ∈ s, √(x i) ^ 2 := by simp only [Real.sq_sqrt (hx _)]
    _ ≤ (∑ i ∈ s, √(x i)) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => Real.sqrt_nonneg _

/-- **Poincaré inequality, norm form**: `‖f‖_{L²} ≤ Σ_μ ‖∂_μ f‖_{L²}` for mean-zero `f`. -/
theorem eLpNorm_le_of_mean_zero {f : UnitAddTorus d → ℂ} {g : d → UnitAddTorus d → ℂ}
    (hf : MemLp f 2 volume) (hg : ∀ μ, MemLp (g μ) 2 volume) (hd : ∀ μ, IsTPartial μ f (g μ))
    (h0 : mFourierCoeff f 0 = 0) :
    eLpNorm f 2 volume ≤ ∑ μ, eLpNorm (g μ) 2 volume := by
  rw [eLpNorm_two_eq_sqrt hf]
  simp only [eLpNorm_two_eq_sqrt (hg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (Real.sqrt_le_sqrt (integral_sq_le_of_mean_zero hf hg hd h0)).trans ?_
  exact sqrt_sum_le_sum_sqrt _ _ fun _ => integral_nonneg fun _ => by positivity

/-! ### Integration by parts -/

/-- `mFourierCoeff` of an `L²` function agrees with that of its `L²` class. -/
theorem mFourierCoeff_toLp {f : UnitAddTorus d → ℂ} (hf : MemLp f 2 volume) :
    mFourierCoeff ⇑(hf.toLp f) = mFourierCoeff f := by
  funext n
  unfold mFourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]

/-- **Integration by parts on `𝕋^d`**: `∫ conj(∂_μ u) v = -∫ conj(u) ∂_μ v` for
`u, v, ∂_μ u, ∂_μ v ∈ L²` (Parseval for inner products and `conj(2πi n_μ) = -2πi n_μ`). -/
theorem integral_conj_partial_mul {μ : d} {u v gu gv : UnitAddTorus d → ℂ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (hgu : MemLp gu 2 volume)
    (hgv : MemLp gv 2 volume) (hdu : IsTPartial μ u gu) (hdv : IsTPartial μ v gv) :
    ∫ x, conj (gu x) * v x = -∫ x, conj (u x) * gv x := by
  have h1 := hasSum_prod_mFourierCoeff (hgu.toLp gu) (hv.toLp v)
  have h2 := hasSum_prod_mFourierCoeff (hu.toLp u) (hgv.toLp gv)
  rw [mFourierCoeff_toLp hgu, mFourierCoeff_toLp hv] at h1
  rw [mFourierCoeff_toLp hu, mFourierCoeff_toLp hgv] at h2
  have e1 : ∫ t, conj ((hgu.toLp gu) t) * (hv.toLp v) t = ∫ x, conj (gu x) * v x := by
    refine integral_congr_ae ?_
    filter_upwards [hgu.coeFn_toLp, hv.coeFn_toLp] with t h₁ h₂
    rw [h₁, h₂]
  have e2 : ∫ t, conj ((hu.toLp u) t) * (hgv.toLp gv) t = ∫ x, conj (u x) * gv x := by
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp, hgv.coeFn_toLp] with t h₁ h₂
    rw [h₁, h₂]
  rw [e1] at h1
  rw [e2] at h2
  have hf : (fun i => conj (mFourierCoeff gu i) * mFourierCoeff v i) =
      fun i => -(conj (mFourierCoeff u i) * mFourierCoeff gv i) := by
    funext i
    rw [hdu i, hdv i, map_mul, conj_sym]; ring
  rw [hf] at h1
  exact h1.unique h2.neg

/-! ### The critical Sobolev inequality on `𝕋⁴` in derivative form -/

open NativeCoulomb in
/-- **Critical Sobolev inequality `H¹(𝕋⁴) ⊂ L⁴`** (derivative form): for `f ∈ L²(𝕋⁴)` with
`L²` partial derivatives `g μ = ∂_μ f`,
`‖f‖_{L⁴} ≤ 3 Σ_μ ‖∂_μ f‖_{L²} + 4 ‖f‖_{L²}`.
Proof: the inequality for the Fourier truncations (`NativeCoulomb.eLpNorm_four_trigPoly_le`, with
Bessel's inequality for the truncated coefficient sums) and their `L⁴` convergence
(`NativeCoulomb.tendsto_eLpNorm_four_trunc`). -/
theorem eLpNorm_four_le_torus {f : UnitAddTorus (Fin 4) → ℂ} {g : Fin 4 → UnitAddTorus (Fin 4) → ℂ}
    (hf : MemLp f 2 volume) (hg : ∀ μ, MemLp (g μ) 2 volume) (hd : ∀ μ, IsTPartial μ f (g μ)) :
    eLpNorm f 4 volume ≤ 3 * ∑ μ, eLpNorm (g μ) 2 volume + 4 * eLpNorm f 2 volume := by
  set F := hf.toLp f
  have hFc : mFourierCoeff ⇑F = mFourierCoeff f := mFourierCoeff_toLp hf
  have hPf := hasSum_sq_mFourierCoeff_of_memLp hf
  have hPg := fun μ => hasSum_sq_mFourierCoeff_of_memLp (hg μ)
  -- `F ∈ H¹`
  have hF1 : MemH 1 ⇑F := by
    unfold MemH CoeffMemH
    rw [hFc]
    have hs : Summable fun n => ‖mFourierCoeff f n‖ ^ 2 + ∑ μ, ‖mFourierCoeff (g μ) n‖ ^ 2 :=
      hPf.summable.add (summable_sum fun μ _ => (hPg μ).summable)
    refine hs.congr fun n => ?_
    have e : ∀ μ, ‖mFourierCoeff (g μ) n‖ ^ 2 =
        (2 * π * (n μ : ℝ)) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
      fun μ => by rw [hd μ n, norm_mul, mul_pow, norm_sym_sq]
    simp only [Real.rpow_one, e, sobWeight]
    rw [add_mul, one_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
  obtain ⟨-, hT⟩ := tendsto_eLpNorm_four_trunc hF1
  -- the bound for the truncations
  set B : ℝ≥0∞ := 3 * ∑ μ, eLpNorm (g μ) 2 volume + 4 * eLpNorm f 2 volume
  have hbessel : ∀ (S : Finset (Fin 4 → ℤ)) (c : (Fin 4 → ℤ) → ℂ) (h : UnitAddTorus (Fin 4) → ℂ),
      MemLp h 2 volume → (∀ n, c n = mFourierCoeff h n) →
      ENNReal.ofReal ‖ContinuousMap.toLp 2 volume ℂ (trigPoly S c)‖ ≤ eLpNorm h 2 volume := by
    intro S c h hh hc
    rw [eLpNorm_two_eq_sqrt hh]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.sqrt_sq (norm_nonneg _), norm_toLp_trigPoly_sq]
    refine Real.sqrt_le_sqrt ?_
    simp only [hc]
    exact sum_le_hasSum S (fun _ _ => by positivity) (hasSum_sq_mFourierCoeff_of_memLp hh)
  have hR : ∀ R : ℕ, eLpNorm (⇑(trigPoly (TorusSobolev.box R) (mFourierCoeff ⇑F))) 4 volume ≤ B := by
    intro R
    refine (NativeCoulomb.eLpNorm_four_trigPoly_le _ _).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    simp only [ENNReal.ofReal_ofNat]
    show _ ≤ 3 * ∑ μ, eLpNorm (g μ) 2 volume + 4 * eLpNorm f 2 volume
    gcongr with μ
    · refine hbessel _ _ (g μ) (hg μ) fun n => ?_
      rw [hd μ n, hFc]; rfl
    · exact hbessel _ _ f hf fun n => by rw [hFc]
  -- pass to the limit
  have hle : ∀ R : ℕ, eLpNorm (⇑F) 4 volume ≤ B + eLpNorm (fun y =>
      trigPoly (TorusSobolev.box R) (mFourierCoeff ⇑F) y - F y) 4 volume := by
    intro R
    set P := trigPoly (TorusSobolev.box R) (mFourierCoeff ⇑F)
    have e : (⇑F) = fun y => P y - (P y - F y) := by funext y; ring
    calc eLpNorm (⇑F) 4 volume = eLpNorm (fun y => P y - (P y - F y)) 4 volume := by rw [← e]
      _ ≤ eLpNorm (⇑P) 4 volume + eLpNorm (fun y => P y - F y) 4 volume :=
          eLpNorm_sub_le P.continuous.aestronglyMeasurable
            (P.continuous.aestronglyMeasurable.sub (Lp.aestronglyMeasurable F)) (by norm_num)
      _ ≤ B + eLpNorm (fun y => P y - F y) 4 volume := add_le_add (hR R) le_rfl
  have hlim : Tendsto (fun R : ℕ => B + eLpNorm (fun y =>
      trigPoly (TorusSobolev.box R) (mFourierCoeff ⇑F) y - F y) 4 volume) atTop (𝓝 (B + 0)) :=
    tendsto_const_nhds.add hT
  rw [add_zero] at hlim
  have hF4 : eLpNorm (⇑F) 4 volume ≤ B := ge_of_tendsto' hlim hle
  rwa [eLpNorm_congr_ae hf.coeFn_toLp] at hF4

/-- **Critical Sobolev–Poincaré inequality on `𝕋⁴`**: for mean-zero `f`,
`‖f‖_{L⁴} ≤ 7 Σ_μ ‖∂_μ f‖_{L²}`. -/
theorem eLpNorm_four_le_of_mean_zero {f : UnitAddTorus (Fin 4) → ℂ}
    {g : Fin 4 → UnitAddTorus (Fin 4) → ℂ} (hf : MemLp f 2 volume)
    (hg : ∀ μ, MemLp (g μ) 2 volume) (hd : ∀ μ, IsTPartial μ f (g μ))
    (h0 : mFourierCoeff f 0 = 0) :
    eLpNorm f 4 volume ≤ 7 * ∑ μ, eLpNorm (g μ) 2 volume := by
  refine (eLpNorm_four_le_torus hf hg hd).trans ?_
  have hP := eLpNorm_le_of_mean_zero hf hg hd h0
  calc 3 * ∑ μ, eLpNorm (g μ) 2 volume + 4 * eLpNorm f 2 volume
      ≤ 3 * ∑ μ, eLpNorm (g μ) 2 volume + 4 * ∑ μ, eLpNorm (g μ) 2 volume := by gcongr
    _ = 7 * ∑ μ, eLpNorm (g μ) 2 volume := by rw [← add_mul]; norm_num

end RenewalGeometry.UhlenbeckTorus
