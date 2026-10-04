/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TotallyBoundedApproximation

/-!
# The Kolmogorov–Riesz (Fréchet–Kolmogorov) theorem on the torus `𝕋^d`

Mathlib has no Kolmogorov–Riesz compactness criterion.  This file proves it on the unit torus
`𝕋^d = UnitAddTorus d` (any finite index type `d`, Mathlib's Haar probability measure of
`Mathlib.Analysis.Fourier.AddCircleMulti`), for scalar and for finite-dimensional vector values.
It is the compactness step of `lem:native-discrete-KR`, `thm:native-Wilson-compactness` and
`prop:Wilson-screen-compactness` of the Einstein–SM action-closure manuscript (whose native
comparison grid is a periodic box).

* `transl y f = f(· + y)`: translation on `L²(𝕋^d; E)` (an isometry).
* `mFourierCoeff_transl`: `(τ_y f)^(n) = e_n(y) f̂(n)`.
* `hasSum_norm_sq_transl_sub`: `‖τ_y f - f‖² = Σ_n |e_n(y) - 1|² |f̂(n)|²` (Parseval).
* `sum_sq_mFourierCoeff_le_of_modulus`: averaging the coordinate translation `s e_μ` over
  `s ∈ [0, δ]`: if `‖τ_{s e_μ} f - f‖ ≤ ω` for `0 ≤ s ≤ δ`, then
  `Σ_{n ∈ F} |f̂(n)|² ≤ ω²` for every finite set `F` of frequencies with `π δ |n_μ| ≥ 1`.
* `kolmogorovRiesz_torus`: **Kolmogorov–Riesz.**  A family bounded in `L²(𝕋^d)` whose
  coordinate translation moduli `sup_f ‖τ_{s e_μ} f - f‖` (`0 ≤ s ≤ δ`, all directions `μ`) tend
  to zero as `δ → 0` is totally bounded in `L²(𝕋^d)`.
* `kolmogorovRiesz_torus_real_cofinite`: real scalar values (isometric complexification).
* `kolmogorovRiesz_torus_vector`: the same for `L²(𝕋^d; E)`, `E` a finite-dimensional real
  normed space (in particular any finite-dimensional complex one), component by component in a
  basis.
* `kolmogorovRiesz_torus_cofinite`, `kolmogorovRiesz_torus_vector_cofinite`: the moduli need only
  be small outside a finite set of indices (for sequences: eventually), as in `limsup_{h ↓ 0}`
  formulations.
-/

open MeasureTheory Set Filter Topology Metric UnitAddTorus ComplexConjugate
open scoped ENNReal Real

namespace RenewalGeometry.KolmogorovRieszTorus

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

instance isAddRightInvariant_volume_torus :
    (volume : Measure (UnitAddTorus d)).IsAddRightInvariant := by
  unfold UnitAddTorus; infer_instance

instance isProbabilityMeasure_volume_torus :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus d)) := by
  unfold UnitAddTorus; infer_instance

/-! ### Translations -/

variable {E : Type*} [NormedAddCommGroup E]

/-- Translation `τ_y f = f(· + y)` on `L²(𝕋^d; E)`. -/
def transl (y : UnitAddTorus d) (f : Lp E 2 (volume : Measure (UnitAddTorus d))) :
    Lp E 2 (volume : Measure (UnitAddTorus d)) :=
  Lp.compMeasurePreserving (fun x => x + y) (measurePreserving_add_right volume y) f

theorem coeFn_transl (y : UnitAddTorus d) (f : Lp E 2 (volume : Measure (UnitAddTorus d))) :
    transl y f =ᵐ[volume] fun x => f (x + y) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem norm_transl (y : UnitAddTorus d) (f : Lp E 2 (volume : Measure (UnitAddTorus d))) :
    ‖transl y f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

/-! ### Fourier coefficients of translates -/

theorem mFourier_add_apply (n : d → ℤ) (x y : UnitAddTorus d) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp [mFourier, fourier_apply, smul_add, AddCircle.toCircle_add, Finset.prod_mul_distrib]

theorem mFourier_neg_neg (n : d → ℤ) (y : UnitAddTorus d) : mFourier (-n) (-y) = mFourier n y := by
  simp [mFourier, fourier_apply]

/-- `(τ_y f)^(n) = e_n(y) f̂(n)`. -/
theorem mFourierCoeff_transl (y : UnitAddTorus d) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (n : d → ℤ) : mFourierCoeff (transl y f) n = mFourier n y * mFourierCoeff f n := by
  have h1 : mFourierCoeff (⇑(transl y f)) n = ∫ t, mFourier (-n) t • f (t + y) :=
    integral_congr_ae (by filter_upwards [coeFn_transl y f] with t ht; rw [ht])
  rw [h1]
  have h2 := integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus d)))
    (fun s => mFourier (-n) (s - y) • f s) y
  simp only [add_sub_cancel_right] at h2
  rw [h2, mFourierCoeff, ← integral_const_mul]
  congr 1
  funext s
  rw [sub_eq_add_neg, mFourier_add_apply, mFourier_neg_neg, smul_eq_mul, smul_eq_mul]
  ring

/-- Parseval on `𝕋^d`: `‖f‖² = Σ_n |f̂(n)|²`. -/
theorem hasSum_norm_sq_mFourierCoeff (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    HasSum (fun n => ‖mFourierCoeff f n‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (mFourierBasis.repr f)
  simp only [LinearIsometryEquiv.norm_map, mFourierBasis_repr] at h
  norm_num at h
  exact h

/-- `‖τ_y f - f‖² = Σ_n |e_n(y) - 1|² |f̂(n)|²`. -/
theorem hasSum_norm_sq_transl_sub (y : UnitAddTorus d)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    HasSum (fun n => ‖mFourier n y - 1‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2) (‖transl y f - f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (mFourierBasis.repr (transl y f - f))
  rw [LinearIsometryEquiv.norm_map] at h
  simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, mFourierBasis_repr, mFourierCoeff_transl] at h
  norm_num at h
  convert h using 1
  funext n
  rw [← mul_pow, ← norm_mul, sub_mul, one_mul]

/-! ### Coordinate translations -/

/-- The torus point `s e_μ`. -/
def coordPt [DecidableEq d] (μ : d) (s : ℝ) : UnitAddTorus d := Pi.single μ (s : UnitAddCircle)

theorem mFourier_coordPt [DecidableEq d] (n : d → ℤ) (μ : d) (s : ℝ) :
    mFourier n (coordPt μ s) = Complex.exp (((2 * π * (n μ : ℝ) * s : ℝ) : ℂ) * Complex.I) := by
  have : mFourier n (coordPt μ s) = fourier (n μ) (s : UnitAddCircle) := by
    simp only [mFourier, coordPt, ContinuousMap.coe_mk]
    rw [Finset.prod_eq_single μ]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, fourier_eval_zero]
    · simp
  rw [this, fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem norm_exp_sub_one_sq (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `∫_0^δ (2 - 2 cos(c s)) ds ≥ δ` when `|c| δ ≥ 2`. -/
theorem le_integral_two_sub_two_cos {c δ : ℝ} (hδ : 0 < δ) (hc : 2 ≤ |c| * δ) :
    δ ≤ ∫ s in (0)..δ, (2 - 2 * Real.cos (c * s)) := by
  have hc0 : c ≠ 0 := by
    rintro rfl; simp at hc; linarith
  have hcos : ∫ s in (0)..δ, Real.cos (c * s) = c⁻¹ * Real.sin (c * δ) := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc0, integral_cos]
    simp
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun s => 2 * Real.cos (c * s)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, hcos]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hb : |c⁻¹ * Real.sin (c * δ)| ≤ δ / 2 := by
    rw [abs_mul, abs_inv]
    have hs := Real.abs_sin_le_one (c * δ)
    have hcpos : 0 < |c| := abs_pos.mpr hc0
    calc |c|⁻¹ * |Real.sin (c * δ)| ≤ |c|⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hcpos.le)
      _ ≤ δ / 2 := by
          rw [mul_one, inv_le_iff_one_le_mul₀ hcpos]
          nlinarith
  have := le_abs_self (c⁻¹ * Real.sin (c * δ))
  linarith

/-- **Tail bound from a coordinate translation modulus.**  If `‖τ_{s e_μ} f - f‖ ≤ ω` for all
`0 ≤ s ≤ δ`, then `Σ_{n ∈ F} |f̂(n)|² ≤ ω²` for every finite set `F` of frequencies with
`π δ |n_μ| ≥ 1`. -/
theorem sum_sq_mFourierCoeff_le_of_modulus [DecidableEq d]
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (μ : d) {δ ω : ℝ} (hδ : 0 < δ)
    (hmod : ∀ s ∈ Icc (0 : ℝ) δ, ‖transl (coordPt μ s) f - f‖ ≤ ω) (F : Finset (d → ℤ))
    (hF : ∀ n ∈ F, 1 ≤ π * δ * |(n μ : ℝ)|) :
    ∑ n ∈ F, ‖mFourierCoeff f n‖ ^ 2 ≤ ω ^ 2 := by
  have hω : 0 ≤ ω := (norm_nonneg _).trans (hmod 0 ⟨le_rfl, hδ.le⟩)
  set φ : (d → ℤ) → ℝ → ℝ := fun n s => 2 - 2 * Real.cos (2 * π * (n μ : ℝ) * s) with hφ
  have hpt : ∀ s ∈ Icc (0 : ℝ) δ, ∑ n ∈ F, φ n s * ‖mFourierCoeff f n‖ ^ 2 ≤ ω ^ 2 := by
    intro s hs
    have hsum := hasSum_norm_sq_transl_sub (coordPt μ s) f
    have hle := sum_le_hasSum F (fun n _ => by positivity) hsum
    have hsq : ‖transl (coordPt μ s) f - f‖ ^ 2 ≤ ω ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hmod s hs) 2
    refine le_trans (le_of_eq ?_) (hle.trans hsq)
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mFourier_coordPt, norm_exp_sub_one_sq]
  have hint : ∀ n, IntervalIntegrable (φ n) volume 0 δ := fun n => by
    simp only [hφ]; exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hcont : Continuous fun s => ∑ n ∈ F, φ n s * ‖mFourierCoeff f n‖ ^ 2 := by
    simp only [hφ]; fun_prop
  have h1 : ∫ s in (0)..δ, ∑ n ∈ F, φ n s * ‖mFourierCoeff f n‖ ^ 2 ≤ ∫ s in (0)..δ, ω ^ 2 :=
    intervalIntegral.integral_mono_on hδ.le (hcont.intervalIntegrable _ _)
      intervalIntegrable_const hpt
  rw [intervalIntegral.integral_finsetSum fun n _ => (hint n).mul_const _,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
  have h2 : δ * ∑ n ∈ F, ‖mFourierCoeff f n‖ ^ 2 ≤
      ∑ n ∈ F, (∫ s in (0)..δ, φ n s * ‖mFourierCoeff f n‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [intervalIntegral.integral_mul_const]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := hF n hn
    refine le_integral_two_sub_two_cos hδ ?_
    rw [abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
    nlinarith
  have := h2.trans h1
  nlinarith


/-! ### Low-frequency projections and the Kolmogorov–Riesz theorem -/

/-- The low-frequency projection `P_B f = Σ_{n ∈ B} f̂(n) e_n`. -/
def lowProj (B : Finset (d → ℤ)) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
  ∑ n ∈ B, mFourierBasis.repr f n • mFourierBasis n

/-- `‖f - P_B f‖² = Σ_{n ∉ B} |f̂(n)|²`. -/
theorem hasSum_norm_sq_sub_lowProj [DecidableEq d] (B : Finset (d → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    HasSum (fun n => if n ∈ B then 0 else ‖mFourierCoeff f n‖ ^ 2) (‖f - lowProj B f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (mFourierBasis.repr (f - lowProj B f))
  rw [LinearIsometryEquiv.norm_map] at h
  norm_num at h
  convert h using 1
  funext n
  simp only [lowProj, map_sub, map_sum, map_smul, HilbertBasis.repr_self, lp.coeFn_sub,
    Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, mFourierBasis_repr]
  by_cases hn : n ∈ B
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m _ hm; simp [Pi.single_eq_of_ne' hm]
    · intro h'; exact absurd hn h'
  · rw [if_neg hn, Finset.sum_eq_zero]
    · simp
    · intro m hm
      have : n ≠ m := fun h' => hn (h' ▸ hm)
      simp [Pi.single_eq_of_ne this]

/-- **Kolmogorov–Riesz on `𝕋^d` (cofinite form).**  A family bounded in `L²(𝕋^d)` such that for
every `ε > 0` there are `δ > 0` and a finite exceptional set of indices outside of which the
coordinate translation moduli `max_μ sup_{0 ≤ s ≤ δ} ‖τ_{s e_μ} f - f‖` are at most `ε`, is
totally bounded in `L²(𝕋^d)`. -/
theorem kolmogorovRiesz_torus_cofinite [DecidableEq d] {ι : Type*}
    (F : ι → Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (hbdd : ∃ M, ∀ i, ‖F i‖ ≤ M)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∃ S : Set ι, S.Finite ∧ ∀ i ∉ S, ∀ μ, ∀ s ∈ Icc (0 : ℝ) δ,
      ‖transl (coordPt μ s) (F i) - F i‖ ≤ ε) :
    TotallyBounded (range F) := by
  obtain ⟨M, hM⟩ := hbdd
  apply totallyBounded_of_forall_approx
  intro ε hε
  set D : ℝ := (Fintype.card d : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  set ω : ℝ := ε / (D + 1) with hω
  have hω0 : 0 < ω := by positivity
  obtain ⟨δ, hδ, S, hS, hδm⟩ := hmod ω hω0
  set K : ℕ := ⌈1 / (π * δ)⌉₊ with hK
  set B : Finset (d → ℤ) := Fintype.piFinset fun _ => Finset.Ioo (-(K : ℤ)) K with hB
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (mFourierBasis '' (B : Set (d → ℤ)))) :=
    FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet B).image _)
  refine ⟨((Submodule.span ℂ (mFourierBasis '' (B : Set (d → ℤ))) : Set _) ∩
      closedBall 0 (M + ε)) ∪ F '' S,
    (totallyBounded_inter_closedBall_of_finiteDimensional _ _).union (hS.image F).totallyBounded,
    ?_⟩
  rintro x ⟨i, rfl⟩
  by_cases hiS : i ∈ S
  · exact ⟨F i, Or.inr ⟨i, hiS, rfl⟩, by simpa using hε⟩
  -- frequencies outside `B` have a large coordinate
  have hout : ∀ n, n ∉ B → ∃ μ, 1 ≤ π * δ * |(n μ : ℝ)| := by
    intro n hn
    simp only [hB, Fintype.mem_piFinset, Finset.mem_Ioo, not_forall] at hn
    obtain ⟨μ, hμ⟩ := hn
    refine ⟨μ, ?_⟩
    have hKn : (K : ℤ) ≤ |n μ| := by
      rcases le_or_gt (K : ℤ) (n μ) with h | h
      · exact h.trans (le_abs_self _)
      · have : n μ ≤ -(K : ℤ) := by
          by_contra h'; exact hμ ⟨lt_of_not_ge h', h⟩
        rw [abs_of_neg (by omega)]; omega
    have hKR : ((K : ℤ) : ℝ) ≤ |(n μ : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hKn
    have h1 : 1 / (π * δ) ≤ (K : ℝ) := Nat.le_ceil _
    have hpd : 0 < π * δ := by positivity
    rw [div_le_iff₀ hpd] at h1
    push_cast at hKR
    nlinarith
  have htail : ‖F i - lowProj B (F i)‖ ^ 2 ≤ D * ω ^ 2 := by
    have h := hasSum_norm_sq_sub_lowProj B (F i)
    rw [← h.tsum_eq]
    refine h.summable.tsum_le_of_sum_le fun G => ?_
    classical
    set a : (d → ℤ) → ℝ := fun n => ‖mFourierCoeff (F i) n‖ ^ 2 with ha
    have h1 : ∑ n ∈ G, (if n ∈ B then 0 else a n) ≤
        ∑ μ : d, ∑ n ∈ G, (if 1 ≤ π * δ * |(n μ : ℝ)| then a n else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun n _ => ?_
      by_cases hn : n ∈ B
      · rw [if_pos hn]
        exact Finset.sum_nonneg fun μ _ => by split_ifs <;> positivity
      · rw [if_neg hn]
        obtain ⟨μ, hμ⟩ := hout n hn
        have := Finset.single_le_sum (f := fun μ => if 1 ≤ π * δ * |(n μ : ℝ)| then a n else 0)
          (fun μ _ => by split_ifs <;> positivity) (Finset.mem_univ μ)
        simpa [hμ] using this
    refine h1.trans ?_
    have h2 : ∀ μ : d, ∑ n ∈ G, (if 1 ≤ π * δ * |(n μ : ℝ)| then a n else 0) ≤ ω ^ 2 := by
      intro μ
      rw [← Finset.sum_filter]
      exact sum_sq_mFourierCoeff_le_of_modulus (F i) μ hδ (hδm i hiS μ) _
        fun n hn => (Finset.mem_filter.mp hn).2
    refine (Finset.sum_le_sum fun μ _ => h2 μ).trans (le_of_eq ?_)
    simp [hD]
  have hlt : ‖F i - lowProj B (F i)‖ < ε := by
    have hDω : D * ω ^ 2 < ε ^ 2 := by
      rw [hω, div_pow]
      have hpos : 0 < (D + 1) ^ 2 := by positivity
      rw [mul_div_assoc', div_lt_iff₀ hpos]
      have h1 : D < (D + 1) ^ 2 := by nlinarith
      have h2 := mul_lt_mul_of_pos_left h1 (pow_pos hε 2)
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le (htail.trans_lt hDω)
  refine ⟨lowProj B (F i), Or.inl ⟨?_, ?_⟩, by rw [dist_eq_norm]; exact hlt⟩
  · refine Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hn)
  · rw [mem_closedBall, dist_zero_right]
    have := norm_le_norm_add_norm_sub' (lowProj B (F i)) (F i)
    rw [norm_sub_rev] at this
    linarith [hM i]


/-- **Kolmogorov–Riesz on `𝕋^d`.**  A family bounded in `L²(𝕋^d)` whose coordinate
translation moduli `sup_f max_μ sup_{0 ≤ s ≤ δ} ‖τ_{s e_μ} f - f‖` tend to zero as `δ → 0` is
totally bounded in `L²(𝕋^d)`. -/
theorem kolmogorovRiesz_torus [DecidableEq d] {ι : Type*}
    (F : ι → Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (hbdd : ∃ M, ∀ i, ‖F i‖ ≤ M)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ i μ, ∀ s ∈ Icc (0 : ℝ) δ,
      ‖transl (coordPt μ s) (F i) - F i‖ ≤ ε) :
    TotallyBounded (range F) :=
  kolmogorovRiesz_torus_cofinite F hbdd fun ε hε => by
    obtain ⟨δ, hδ, h⟩ := hmod ε hε
    exact ⟨δ, hδ, ∅, Set.finite_empty, fun i _ => h i⟩

/-! ### Vector values -/

section Vector

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Translations commute with pointwise bounded linear maps. -/
theorem transl_compLp {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    (y : UnitAddTorus d) (f : Lp V 2 (volume : Measure (UnitAddTorus d))) :
    transl y (L.compLp f) = L.compLp (transl y f) := by
  refine Lp.ext ?_
  have hqmp := (measurePreserving_add_right (volume : Measure (UnitAddTorus d)) y).quasiMeasurePreserving
  have h1 : (fun x => (L.compLp f) (x + y)) =ᵐ[volume] fun x => L (f (x + y)) :=
    hqmp.ae_eq_comp (L.coeFn_compLp' f)
  filter_upwards [coeFn_transl y (L.compLp f), h1, L.coeFn_compLp' (transl y f),
    coeFn_transl y f] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, hx4]

/-- **Kolmogorov–Riesz on `𝕋^d`, real scalar values (cofinite form)**, deduced from the complex
case through the isometric embedding `L²(𝕋^d; ℝ) → L²(𝕋^d; ℂ)`. -/
theorem kolmogorovRiesz_torus_real_cofinite [DecidableEq d] {ι : Type*}
    (F : ι → Lp ℝ 2 (volume : Measure (UnitAddTorus d))) (hbdd : ∃ M, ∀ i, ‖F i‖ ≤ M)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∃ S : Set ι, S.Finite ∧ ∀ i ∉ S, ∀ μ, ∀ s ∈ Icc (0 : ℝ) δ,
      ‖transl (coordPt μ s) (F i) - F i‖ ≤ ε) :
    TotallyBounded (range F) := by
  obtain ⟨M, hM⟩ := hbdd
  set J : Lp ℝ 2 (volume : Measure (UnitAddTorus d)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
    ContinuousLinearMap.compLpL 2 volume Complex.ofRealCLM with hJ
  have hJapp : ∀ f, J f = Complex.ofRealCLM.compLp f := fun _ => rfl
  have hnorm : ∀ f, ‖J f‖ = ‖f‖ := by
    intro f
    rw [hJapp, Lp.norm_def, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_norm_ae ?_
    filter_upwards [(Complex.ofRealCLM).coeFn_compLp' f] with y hy
    rw [hy, Complex.ofRealCLM_apply, Complex.norm_real]
  have hiso : Isometry J :=
    AddMonoidHomClass.isometry_of_norm J.toLinearMap.toAddMonoidHom hnorm
  have hKR : TotallyBounded (range fun i => J (F i)) := by
    refine kolmogorovRiesz_torus_cofinite _ ⟨M, fun i => (hnorm _).trans_le (hM i)⟩
      fun ε hε => ?_
    obtain ⟨δ, hδ, S, hS, h⟩ := hmod ε hε
    refine ⟨δ, hδ, S, hS, fun i hi μ s hs => ?_⟩
    rw [hJapp, transl_compLp, ← hJapp, ← hJapp, ← map_sub, hnorm]
    exact h i hi μ s hs
  refine (totallyBounded_preimage hiso.isUniformInducing hKR).subset ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨i, rfl⟩

/-- **Kolmogorov–Riesz on `𝕋^d`, finite-dimensional vector values (cofinite form).**  A family
bounded in `L²(𝕋^d; V)` (`V` a finite-dimensional real normed space) whose coordinate
translation moduli are, for every `ε`, at most `ε` for `0 ≤ s ≤ δ` outside a finite set of
indices, is totally bounded in `L²(𝕋^d; V)`. -/
theorem kolmogorovRiesz_torus_vector_cofinite [DecidableEq d] [FiniteDimensional ℝ V]
    {ι : Type*} (F : ι → Lp V 2 (volume : Measure (UnitAddTorus d)))
    (hbdd : ∃ M, ∀ i, ‖F i‖ ≤ M)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∃ S : Set ι, S.Finite ∧ ∀ i ∉ S, ∀ μ, ∀ s ∈ Icc (0 : ℝ) δ,
      ‖transl (coordPt μ s) (F i) - F i‖ ≤ ε) :
    TotallyBounded (range F) := by
  obtain ⟨M, hM⟩ := hbdd
  set b := Module.finBasis ℝ V with hb
  let c : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let e : Fin (Module.finrank ℝ V) → ℝ →L[ℝ] V := fun j => (ContinuousLinearMap.id ℝ ℝ).smulRight (b j)
  let Lc : Fin (Module.finrank ℝ V) →
      (Lp ℝ 2 (volume : Measure (UnitAddTorus d)) →L[ℝ] Lp V 2 (volume : Measure (UnitAddTorus d))) :=
    fun j => ContinuousLinearMap.compLpL 2 volume (e j)
  refine totallyBounded_of_components (Z := fun _ => Lp ℝ 2 (volume : Measure (UnitAddTorus d)))
    (fun j f => (c j).compLp f) (fun j => (Lc j).toLinearMap.toAddMonoidHom)
    (K := ∑ j, ‖Lc j‖) (Finset.sum_nonneg fun j _ => norm_nonneg _) ?_ ?_ ?_
  · intro j z
    refine ((Lc j).le_opNorm z).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact Finset.single_le_sum (f := fun j => ‖Lc j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ j)
  · rintro x -
    refine Lp.ext ?_
    have h2 : ∀ᵐ t ∂(volume : Measure (UnitAddTorus d)),
        ∀ j, ((e j).compLp ((c j).compLp x)) t = e j (((c j).compLp x) t) :=
      ae_all_iff.2 fun j => (e j).coeFn_compLp' _
    have h3 : ∀ᵐ t ∂(volume : Measure (UnitAddTorus d)), ∀ j, ((c j).compLp x) t = c j (x t) :=
      ae_all_iff.2 fun j => (c j).coeFn_compLp' _
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun j => (e j).compLp ((c j).compLp x)), h2, h3] with t h1 h2 h3
    have hLc : ∀ j z, Lc j z = (e j).compLp z := fun _ _ => rfl
    simp only [LinearMap.toAddMonoidHom_coe, ContinuousLinearMap.coe_coe, hLc]
    rw [h1]
    simp only [h2, h3, e, c, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    exact (b.sum_repr (x t)).symm
  · intro j
    rw [← Set.range_comp]
    refine kolmogorovRiesz_torus_real_cofinite _ ⟨‖c j‖ * M, fun i => ?_⟩ ?_
    · exact ((c j).norm_compLp_le _).trans (mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _))
    · intro ε hε
      obtain ⟨δ, hδ, S, hS, hδm⟩ := hmod (ε / (‖c j‖ + 1)) (by positivity)
      refine ⟨δ, hδ, S, hS, fun i hiS μ s hs => ?_⟩
      simp only [Function.comp_apply]
      have hsub : (c j).compLp (transl (coordPt μ s) (F i)) - (c j).compLp (F i) =
          (c j).compLp (transl (coordPt μ s) (F i) - F i) := by
        change ContinuousLinearMap.compLpL 2 volume (c j) _ -
          ContinuousLinearMap.compLpL 2 volume (c j) _ =
          ContinuousLinearMap.compLpL 2 volume (c j) _
        rw [map_sub]
      rw [transl_compLp, hsub]
      refine ((c j).norm_compLp_le _).trans ?_
      refine (mul_le_mul_of_nonneg_left (hδm i hiS μ s hs) (norm_nonneg _)).trans ?_
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg (c j)]

/-- **Kolmogorov–Riesz on `𝕋^d`, finite-dimensional vector values.**  A family bounded in
`L²(𝕋^d; V)` whose coordinate translation moduli tend to zero uniformly is totally bounded. -/
theorem kolmogorovRiesz_torus_vector [DecidableEq d] [FiniteDimensional ℝ V] {ι : Type*}
    (F : ι → Lp V 2 (volume : Measure (UnitAddTorus d))) (hbdd : ∃ M, ∀ i, ‖F i‖ ≤ M)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ i μ, ∀ s ∈ Icc (0 : ℝ) δ,
      ‖transl (coordPt μ s) (F i) - F i‖ ≤ ε) :
    TotallyBounded (range F) :=
  kolmogorovRiesz_torus_vector_cofinite F hbdd fun ε hε => by
    obtain ⟨δ, hδ, h⟩ := hmod ε hε
    exact ⟨δ, hδ, ∅, Set.finite_empty, fun i _ => h i⟩

end Vector

end

end RenewalGeometry.KolmogorovRieszTorus
