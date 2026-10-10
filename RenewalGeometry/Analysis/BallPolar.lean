/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Polar coordinates on `ℝⁿ = Fin n → ℝ` and a radial approximate identity
  (stage C0 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.  The library's Sobolev theory lives on the
coordinate space `Fin n → ℝ` (product Lebesgue measure, sup norm), whose metric balls are cubes;
Euclidean balls are the sets `{x | Σ (x i - c i)² < r²}`.  This file provides:

* `sphereMeasure n`: the surface measure `σ` of the unit Euclidean sphere `S^{n-1}`, the image in
  `Fin n → ℝ` of Mathlib's `volume.toSphere` on `EuclideanSpace ℝ (Fin n)`; it is finite, carried
  by the sphere (`ae_sphereMeasure`: `σ`-a.e. `Σ ω_i² = 1`), of total mass `n |Bⁿ|`
  (`sphereMeasure_univ`);
* `integral_polar` (**polar coordinates centred at `c`**): for integrable `f`,
  `∫ f = ∫_{S^{n-1}} ∫_0^∞ ρ^{n-1} f(c + ρ ω) dρ dσ(ω)`, from
  `measurePreserving_homeomorphUnitSphereProd` and `PiLp.volume_preserving_ofLp`;
* the **radial cutoff kernel** `cutK r k = -(d/dρ) θ((k+1)(1 - ρ²/r²))` (`θ = smoothTransition`):
  nonnegative, of unit mass on `[0, r]` (`integral_cutK`), supported in `(r - r/(k+1), r)`
  (`cutK_ne_zero`), hence an approximate identity at `ρ = r` (`tendsto_integral_cutK`,
  `abs_integral_cutK_le`).  It is the radial part of the smooth cutoffs used to prove the
  divergence theorem on balls (`BallDivergence.lean`).
-/

open MeasureTheory Set Metric WithLp Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.BallAnalysis

/-! ### The surface measure and polar coordinates -/

/-- The unit Euclidean sphere of `ℝⁿ`, embedded in the coordinate space `Fin n → ℝ`. -/
def sphereEmb (n : ℕ) : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → (Fin n → ℝ) :=
  fun ω => ofLp (ω : EuclideanSpace ℝ (Fin n))

theorem measurableEmbedding_sphereEmb (n : ℕ) : MeasurableEmbedding (sphereEmb n) := by
  have h1 : Topology.IsClosedEmbedding (fun ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      (ω : EuclideanSpace ℝ (Fin n))) := isClosed_sphere.isClosedEmbedding_subtypeVal
  have h2 : Topology.IsClosedEmbedding (ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) :=
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isClosedEmbedding
  exact (h2.comp h1).measurableEmbedding

theorem sum_sq_sphereEmb {n : ℕ} (ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∑ i, sphereEmb n ω i ^ 2 = 1 := by
  have h := ω.2
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  simpa [sphereEmb, Real.norm_eq_abs, sq_abs] using h

/-- The surface measure `σ` of the unit Euclidean sphere `S^{n-1}`, transported to `Fin n → ℝ`:
the image of Mathlib's `volume.toSphere` (with `σ(S^{n-1}) = n · |B^n|`, and polar coordinates
`dx = ρ^{n-1} dρ dσ`, `integral_polar`). -/
def sphereMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.map (sphereEmb n) (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

instance (n : ℕ) : IsFiniteMeasure (sphereMeasure n) := by
  unfold sphereMeasure; infer_instance

/-- `σ`-almost every point is on the unit sphere. -/
theorem ae_sphereMeasure (n : ℕ) : ∀ᵐ ω ∂(sphereMeasure n), ∑ i, ω i ^ 2 = 1 := by
  unfold sphereMeasure
  rw [(measurableEmbedding_sphereEmb n).ae_map_iff]
  exact Eventually.of_forall fun ω => sum_sq_sphereEmb ω

/-- Integrals against `σ` are integrals over the sphere. -/
theorem integral_sphereMeasure {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : (Fin n → ℝ) → F) :
    ∫ ω, g ω ∂(sphereMeasure n) =
      ∫ ω, g (sphereEmb n ω) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere :=
  (measurableEmbedding_sphereEmb n).integral_map g

theorem sphereMeasure_univ (n : ℕ) :
    sphereMeasure n univ = n * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [sphereMeasure, Measure.map_apply (measurableEmbedding_sphereEmb n).measurable
    MeasurableSet.univ, preimage_univ, Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Polar coordinates on `EuclideanSpace ℝ (Fin n)` (from Mathlib's
`measurePreserving_homeomorphUnitSphereProd`), with the integrability of the radial integrals
over the sphere. -/
theorem polar_euclid {n : ℕ} [NeZero n] (g : EuclideanSpace ℝ (Fin n) → F)
    (hg : Integrable g) :
    (∫ y, g y = ∫ ω, (∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) • g (ρ • (ω : EuclideanSpace ℝ (Fin n))))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) ∧
    Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) • g (ρ • (ω : EuclideanSpace ℝ (Fin n))))
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  set μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  set h : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Ioi (0 : ℝ) → F :=
    fun p => g (p.2.1 • (p.1 : _))
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hcomp : ∀ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
      h (homeomorphUnitSphereProd _ x) = g x := by
    intro x
    have hx : (x : EuclideanSpace ℝ (Fin n)) ≠ 0 := x.2
    simp only [h, homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe,
      smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have h1 : ∫ y, g y ∂μ = ∫ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))), g x ∂(μ.comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl,
      MeasureTheory.restrict_compl_singleton]
  have h2 : ∫ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))), g x ∂(μ.comap (↑)) =
      ∫ p, h p ∂(μ.toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
    rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _) h]
    simp only [hcomp]
  have hint : Integrable h (μ.toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have : Integrable (fun x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) => g x) (μ.comap (↑)) :=
      (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hg.integrableOn
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, hcomp]
  have hinner : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∫ ρ, h (ω, ρ) ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) =
        ∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) • g (ρ • (ω : EuclideanSpace ℝ (Fin n))) := by
    intro ω
    rw [hdim]
    simp only [h, Measure.volumeIoiPow, ENNReal.ofReal]
    rw [integral_withDensity_eq_integral_smul, integral_subtype_comap measurableSet_Ioi
      (fun a => Real.toNNReal (a ^ (n - 1)) • g (a • (ω : EuclideanSpace ℝ (Fin n))))]
    · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hx) _)]
    · exact (measurable_subtype_coe.pow_const _).real_toNNReal
  refine ⟨?_, ?_⟩
  · rw [h1, h2, integral_prod _ hint]
    exact integral_congr_ae (Eventually.of_forall hinner)
  · exact hint.integral_prod_left.congr (Eventually.of_forall hinner)

/-- Polar coordinates on `EuclideanSpace ℝ (Fin n)`. -/
theorem integral_polar_euclid {n : ℕ} [NeZero n] (g : EuclideanSpace ℝ (Fin n) → F)
    (hg : Integrable g) :
    ∫ y, g y = ∫ ω, (∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) • g (ρ • (ω : EuclideanSpace ℝ (Fin n))))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere :=
  (polar_euclid g hg).1

/-- **Polar coordinates** on `Fin n → ℝ` centred at `c`:
`∫ f = ∫_{S^{n-1}} ∫_0^∞ ρ^{n-1} f(c + ρω) dρ dσ(ω)` for integrable `f`. -/
theorem integral_polar {n : ℕ} [NeZero n] (c : Fin n → ℝ) (f : (Fin n → ℝ) → F)
    (hf : Integrable f) :
    ∫ x, f x = ∫ ω, (∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) • f (c + ρ • ω)) ∂(sphereMeasure n) := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  have e1 : ∫ x, f x = ∫ y : EuclideanSpace ℝ (Fin n), f (c + ofLp y) := by
    rw [← integral_add_left_eq_self f c]
    exact (hmp.integral_comp' (fun x => f (c + x))).symm
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin n) => f (c + ofLp y)) := by
    have h0 : Integrable (fun x => f (c + x)) := hf.comp_add_left c
    exact hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr h0
  rw [e1, integral_polar_euclid _ hint, integral_sphereMeasure]
  rfl

/-- The radial integrals of an integrable function are integrable over the sphere. -/
theorem integrable_polar {n : ℕ} [NeZero n] (c : Fin n → ℝ) (f : (Fin n → ℝ) → F)
    (hf : Integrable f) :
    Integrable (fun ω => ∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) • f (c + ρ • ω)) (sphereMeasure n) := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin n) => f (c + ofLp y)) := by
    have h0 : Integrable (fun x => f (c + x)) := hf.comp_add_left c
    exact hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr h0
  unfold sphereMeasure
  rw [(measurableEmbedding_sphereEmb n).integrable_map_iff]
  exact (polar_euclid _ hint).2


/-! ### The radial cutoff kernel -/

/-- `deriv smoothTransition` vanishes off `(0,1)`. -/
theorem deriv_smoothTransition_eq_zero {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hcl : IsClosed {t : ℝ | deriv Real.smoothTransition t = 0} := isClosed_eq hc continuous_const
  rcases ht with ht | ht
  · have hsub : Iio (0 : ℝ) ⊆ {t : ℝ | deriv Real.smoothTransition t = 0} := by
      intro s hs
      have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hs] with u hu
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hu)
      simp [this.deriv_eq]
    have := hcl.closure_subset_iff.mpr hsub
    rw [closure_Iio] at this
    exact this ht
  · have hsub : Ioi (1 : ℝ) ⊆ {t : ℝ | deriv Real.smoothTransition t = 0} := by
      intro s hs
      have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds hs] with u hu
        exact Real.smoothTransition.one_of_one_le (le_of_lt hu)
      simp [this.deriv_eq]
    have := hcl.closure_subset_iff.mpr hsub
    rw [closure_Ioi] at this
    exact this ht

theorem deriv_smoothTransition_nonneg (t : ℝ) : 0 ≤ deriv Real.smoothTransition t :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

/-- The radial cutoff profile `ψ_k(ρ) = θ((k+1)(1 - ρ²/r²))`. -/
def radCut (r : ℝ) (k : ℕ) (ρ : ℝ) : ℝ := Real.smoothTransition (((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2))

/-- The kernel `K_k = -ψ_k'`. -/
def cutK (r : ℝ) (k : ℕ) (ρ : ℝ) : ℝ :=
  2 * ρ / r ^ 2 * ((k : ℝ) + 1) * deriv Real.smoothTransition (((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2))

theorem hasDerivAt_radCut (r : ℝ) (k : ℕ) (ρ : ℝ) :
    HasDerivAt (radCut r k) (-cutK r k ρ) ρ := by
  have h1 : HasDerivAt (fun ρ : ℝ => ((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2))
      (((k : ℝ) + 1) * (-(2 * ρ / r ^ 2))) ρ := by
    have := ((hasDerivAt_pow 2 ρ).div_const (r ^ 2)).const_sub 1 |>.const_mul ((k : ℝ) + 1)
    exact this.congr_deriv (by norm_num)
  have h2 := (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num))
    (((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2))).hasDerivAt.comp ρ h1
  have e : -cutK r k ρ = deriv Real.smoothTransition (((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2)) *
      (((k : ℝ) + 1) * (-(2 * ρ / r ^ 2))) := by unfold cutK; ring
  rw [e]; exact h2

theorem continuous_cutK (r : ℝ) (k : ℕ) : Continuous (cutK r k) := by
  unfold cutK
  exact (by fun_prop : Continuous fun ρ : ℝ => 2 * ρ / r ^ 2 * ((k : ℝ) + 1)).mul
    (continuous_deriv_smoothTransition.comp (by fun_prop))

theorem cutK_nonneg {r : ℝ} (k : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ cutK r k ρ := by
  unfold cutK
  have := deriv_smoothTransition_nonneg (((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2))
  positivity

theorem cutK_eq_zero_of_le {r : ℝ} (hr : 0 < r) (k : ℕ) {ρ : ℝ} (hρ : r ≤ ρ) : cutK r k ρ = 0 := by
  unfold cutK
  rw [deriv_smoothTransition_eq_zero (Or.inl ?_), mul_zero]
  have : 1 ≤ ρ ^ 2 / r ^ 2 := by
    rw [one_le_div (by positivity)]; nlinarith
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  nlinarith

/-- Where the kernel is nonzero, `r - r/(k+1) < ρ < r`. -/
theorem cutK_ne_zero {r : ℝ} (hr : 0 < r) (k : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (h : cutK r k ρ ≠ 0) :
    r - r / ((k : ℝ) + 1) < ρ ∧ ρ < r := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hd : deriv Real.smoothTransition (((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2)) ≠ 0 := by
    intro h0; apply h; simp [cutK, h0]
  have h01 : 0 < ((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2) ∧
      ((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2) < 1 := by
    by_contra hc
    rw [not_and_or, not_lt, not_lt] at hc
    exact hd (deriv_smoothTransition_eq_zero hc)
  have hr2 : 0 < r ^ 2 := by positivity
  have hlt : ρ < r := by
    have h0 : 0 < 1 - ρ ^ 2 / r ^ 2 := by
      by_contra hc; push_neg at hc; nlinarith [h01.1]
    have : ρ ^ 2 < r ^ 2 := by
      rw [sub_pos, div_lt_one hr2] at h0; exact h0
    nlinarith
  refine ⟨?_, hlt⟩
  have h3 : ((k : ℝ) + 1) * (r ^ 2 - ρ ^ 2) < r ^ 2 := by
    have := h01.2
    have e2 : ((k : ℝ) + 1) * (1 - ρ ^ 2 / r ^ 2) = ((k : ℝ) + 1) * (r ^ 2 - ρ ^ 2) / r ^ 2 := by
      field_simp
    rw [e2, div_lt_one hr2] at this; exact this
  have h4 : ((k : ℝ) + 1) * (r - ρ) * r ≤ ((k : ℝ) + 1) * (r ^ 2 - ρ ^ 2) := by
    have : (r - ρ) * r ≤ r ^ 2 - ρ ^ 2 := by nlinarith
    nlinarith
  have h5 : ((k : ℝ) + 1) * (r - ρ) < r := by
    by_contra hc; push_neg at hc; nlinarith
  rw [sub_lt_comm, lt_div_iff₀ hk]; linarith

theorem integral_cutK {r : ℝ} (hr : 0 < r) (k : ℕ) : ∫ ρ in (0 : ℝ)..r, cutK r k ρ = 1 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := r)
    (fun ρ _ => hasDerivAt_radCut r k ρ) ((continuous_cutK r k).neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at h
  have h0 : radCut r k 0 = 1 := by
    unfold radCut; apply Real.smoothTransition.one_of_one_le; simp
  have hr' : radCut r k r = 0 := by
    unfold radCut; apply Real.smoothTransition.zero_of_nonpos
    rw [div_self (by positivity)]; simp
  linarith

/-- The integral over `(0,∞)` of the kernel against `φ` is the integral over `(0, r]`. -/
theorem setIntegral_Ioi_cutK {r : ℝ} (hr : 0 < r) (k : ℕ) (φ : ℝ → ℝ) :
    ∫ ρ in Ioi (0 : ℝ), cutK r k ρ * φ ρ = ∫ ρ in (0 : ℝ)..r, cutK r k ρ * φ ρ := by
  rw [intervalIntegral.integral_of_le hr.le]
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self ?_
  intro ρ hρ
  have : r ≤ ρ := by
    by_contra h; push_neg at h; exact hρ.2 ⟨hρ.1, h.le⟩
  rw [cutK_eq_zero_of_le hr k this, zero_mul]

/-- Bound: `|∫ K_k φ| ≤ M` if `|φ| ≤ M` on `[0, r]`. -/
theorem abs_integral_cutK_le {r : ℝ} (hr : 0 < r) (k : ℕ) {φ : ℝ → ℝ}
    {M : ℝ} (hM : ∀ ρ ∈ Icc 0 r, |φ ρ| ≤ M) :
    |∫ ρ in Ioi (0 : ℝ), cutK r k ρ * φ ρ| ≤ M := by
  rw [setIntegral_Ioi_cutK hr, intervalIntegral.integral_of_le hr.le]
  have hint : IntegrableOn (fun ρ => cutK r k ρ * M) (Ioc 0 r) :=
    ((continuous_cutK r k).mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  calc |∫ ρ in Ioc 0 r, cutK r k ρ * φ ρ| ≤ ∫ ρ in Ioc 0 r, cutK r k ρ * M := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc
          fun ρ hρ => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutK_nonneg k hρ.1.le)]
        exact mul_le_mul_of_nonneg_left (hM ρ (Ioc_subset_Icc_self hρ)) (cutK_nonneg k hρ.1.le)
    _ = M := by
        rw [integral_mul_const, ← intervalIntegral.integral_of_le hr.le, integral_cutK hr, one_mul]

/-- **Concentration of the kernel at `ρ = r`.** -/
theorem tendsto_integral_cutK {r : ℝ} (hr : 0 < r) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 r)) :
    Tendsto (fun k : ℕ => ∫ ρ in Ioi (0 : ℝ), cutK r k ρ * φ ρ) atTop (𝓝 (φ r)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcr : ContinuousWithinAt φ (Icc 0 r) r := hφ r ⟨hr.le, le_rfl⟩
  rw [Metric.continuousWithinAt_iff] at hcr
  obtain ⟨δ, hδ, hδφ⟩ := hcr (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (r / δ)
  refine ⟨N, fun k hk => ?_⟩
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hrk : r / ((k : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ hk1]
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_lt_iff₀ hδ] at hN; nlinarith
  rw [setIntegral_Ioi_cutK hr, intervalIntegral.integral_of_le hr.le, Real.dist_eq]
  have hint1 : IntegrableOn (fun ρ => cutK r k ρ * φ ρ) (Ioc 0 r) :=
    (((continuous_cutK r k).continuousOn.mul hφ).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun ρ => cutK r k ρ * φ r) (Ioc 0 r) :=
    ((continuous_cutK r k).mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint3 : IntegrableOn (fun ρ => cutK r k ρ * (ε / 2)) (Ioc 0 r) :=
    ((continuous_cutK r k).mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h1 : ∫ ρ in Ioc 0 r, cutK r k ρ * φ r = φ r := by
    rw [integral_mul_const, ← intervalIntegral.integral_of_le hr.le, integral_cutK hr, one_mul]
  have h2 : ∫ ρ in Ioc 0 r, cutK r k ρ * (ε / 2) = ε / 2 := by
    rw [integral_mul_const, ← intervalIntegral.integral_of_le hr.le, integral_cutK hr, one_mul]
  have key : |∫ ρ in Ioc 0 r, (cutK r k ρ * φ ρ - cutK r k ρ * φ r)| ≤ ε / 2 := by
    rw [← h2, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hint3 (ae_restrict_of_forall_mem measurableSet_Ioc
      fun ρ hρ => ?_)
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (cutK_nonneg k hρ.1.le)]
    by_cases h0 : cutK r k ρ = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (cutK_nonneg k hρ.1.le)
      obtain ⟨hlo, hhi⟩ := cutK_ne_zero hr k hρ.1.le h0
      have hd : dist ρ r < δ := by
        rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith
      have := hδφ (Ioc_subset_Icc_self hρ) hd
      rw [Real.dist_eq] at this; exact this.le
  rw [integral_sub hint1 hint2, h1] at key
  linarith

end RenewalGeometry.BallAnalysis
