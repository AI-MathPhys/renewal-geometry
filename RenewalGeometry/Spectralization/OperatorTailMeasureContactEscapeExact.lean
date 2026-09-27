/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.OperatorMeasureWeakCompactness
import RenewalGeometry.Spectralization.OperatorTailMeasureDynamicJetsExact
import RenewalGeometry.Spectralization.OperatorTailMeasureDeterminacyExact
/-!
# High-energy memory escape and instantaneous contact terms

Paper `predictive_spectral_geometry`, label `thm:supp-contact-escape`
(`eq:supp-contact-selfenergy`, `eq:supp-contact-kernel`).

Let `μ n` be positive operator-valued tail measures supported in `[m, ∞)` (`m > 0`), with
`ν n = λ⁻¹ dμ n` and `Q n = ν n([m,∞)) = Σ_n(0)`.  If `sup_n Tr Q_n < ∞`, a subsequence of the
`ν n` converges weakly on the one-point compactification `[m, ∞]` to a positive operator-valued
measure `ν_∞ = ν_fin + Q_esc δ_∞`, and

* `Σ_{φ n}(z) → Q_esc + ∫ λ/(λ - z) dν_fin(λ)` locally uniformly off `[m, ∞)`
  (`eq:supp-contact-selfenergy`);
* `K_{φ n}(t) dt → Q_esc δ_0 + K_fin(t) dt` against bounded continuous test functions on `[0,∞)`,
  where `K_fin(t) = ∫ λ e^{-λ t} dν_fin(λ)` (`eq:supp-contact-kernel`).

The one-point compactification of `[m, ∞)` is realised as the compact interval
`X = [0, 1/m]` through `y = 1/λ`, the point `∞` being `y = 0`.  The measures `ν n` are pushed
forward to `X` (`escapeMeasure`), the weak-* compactness theorem
`OperatorMeasureL2.exists_subseq_tendsto_posOperatorMeasure` is applied there, and the limit
`νlim` on `X` is split into its atom at `0` (`Q_esc`) and its restriction to `(0, 1/m]`, which is
pulled back to `[m, ∞)` (`finitePart`).

Main statement: `OperatorTailMeasure.contact_escape`.
-/

open MeasureTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal ComplexOrder InnerProductSpace

namespace RenewalGeometry

/-! ## Positive operator-valued measures on a general measurable space: scalarisation bridge -/

namespace OperatorMeasureL2

open OperatorTailMeasure

variable {X : Type*} [MeasurableSpace X] {H : Type*} [Fintype H] [DecidableEq H]

namespace PosOperatorMeasure

variable (ν : PosOperatorMeasure X H)

/-- The trace measure `E ↦ Tr ν(E) = ∑ᵢ ⟨eᵢ, ν(E) eᵢ⟩`. -/
noncomputable def traceMeasure : Measure X := ∑ i, ν.formMeasure (Pi.single i 1)

instance : IsFiniteMeasure ν.traceMeasure where
  measure_univ_lt_top := by
    rw [traceMeasure, Measure.coe_finsetSum, Finset.sum_apply]
    exact ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top _ _

theorem traceMeasure_apply {s : Set X} (hs : MeasurableSet s) :
    ν.traceMeasure s = ENNReal.ofReal (Matrix.of (ν.toVectorMeasure s)).trace.re := by
  rw [traceMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [formMeasure_apply ν _ hs, quadFormCLM_single]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Complex.re_sum]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun i _ => posSemidef_re_apply_self_nonneg (ν.posSemidef_apply s) i)]
  rfl

/-- The variation of a positive operator-valued measure is dominated by its trace measure. -/
theorem variation_le_traceMeasure : ν.toVectorMeasure.variation ≤ ν.traceMeasure := by
  refine VectorMeasure.variation_le_of_forall_enorm_le fun s hs => ?_
  rw [traceMeasure_apply ν hs]
  calc ‖ν.toVectorMeasure s‖ₑ = ENNReal.ofReal ‖ν.toVectorMeasure s‖ := (ofReal_norm _).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (posSemidef_norm_le_re_trace (ν.posSemidef_apply s))

instance : IsFiniteMeasure ν.toVectorMeasure.variation :=
  isFiniteMeasure_of_le _ ν.variation_le_traceMeasure

/-- The scalarised measure is dominated by a multiple of the variation. -/
theorem formMeasure_le_smul_variation (ξ : H → ℂ) :
    ν.formMeasure ξ ≤ ‖quadFormCLM ξ‖₊ • ν.toVectorMeasure.variation := by
  have h := variation_mapRange_le' ν.toVectorMeasure (quadFormCLM ξ)
  change (ν.signedForm ξ).variation ≤ _ at h
  rw [← toSignedMeasure_formMeasure, Measure.variation_toSignedMeasure] at h
  exact h

theorem integrable_formMeasure_of_variation (ξ : H → ℂ) {f : X → ℝ}
    (hf : Integrable f ν.toVectorMeasure.variation) : Integrable f (ν.formMeasure ξ) :=
  hf.of_measure_le_smul ENNReal.coe_ne_top (ν.formMeasure_le_smul_variation ξ)

/-- **Bridge**: `Re ⟨ξ, (∫ f dν) ξ⟩ = ∫ f d(formMeasure ν ξ)` for a real integrable `f`. -/
theorem quadFormCLM_integral (ξ : H → ℂ) {f : X → ℝ}
    (hf : Integrable f ν.toVectorMeasure.variation) :
    quadFormCLM ξ (VectorMeasure.integral ν.toVectorMeasure f (ContinuousLinearMap.lsmul ℝ ℝ)) =
      ∫ x, f x ∂(ν.formMeasure ξ) := by
  rw [← integral_mapRange_lsmul _ _ hf]
  change VectorMeasure.integral (reForm ν.toVectorMeasure ξ) f _ = _
  rw [reForm_posOperatorMeasure, ← PosOperatorMeasure.toSignedMeasure_formMeasure,
    integral_toSignedMeasure_lsmul]

/-- The imaginary quadratic form of a real operator integral vanishes. -/
theorem quadFormImCLM_integral (ξ : H → ℂ) {f : X → ℝ}
    (hf : Integrable f ν.toVectorMeasure.variation) :
    quadFormImCLM ξ (VectorMeasure.integral ν.toVectorMeasure f (ContinuousLinearMap.lsmul ℝ ℝ)) =
      0 := by
  rw [← integral_mapRange_lsmul _ _ hf]
  change VectorMeasure.integral (imForm ν.toVectorMeasure ξ) f _ = _
  rw [imForm_posOperatorMeasure, VectorMeasure.integral_zero_vectorMeasure]

/-- **Quadratic form of a real operator integral**: `⟨ξ, (∫ f dν) ξ⟩ = ∫ f d⟨ξ, ν ξ⟩`. -/
theorem quadForm_integral (ξ : H → ℂ) {f : X → ℝ}
    (hf : Integrable f ν.toVectorMeasure.variation) :
    quadForm ξ (Matrix.of (VectorMeasure.integral ν.toVectorMeasure f
      (ContinuousLinearMap.lsmul ℝ ℝ))) = ((∫ x, f x ∂(ν.formMeasure ξ) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    rw [← ν.quadFormCLM_integral ξ hf, quadFormCLM_apply]
  · simp only [Complex.ofReal_im]
    rw [← ν.quadFormImCLM_integral ξ hf, quadFormImCLM_apply]

end PosOperatorMeasure

/-! ## Complex integrands against matrix-valued vector measures -/

section ComplexSplit

variable (V : VectorMeasure X (H → H → ℂ))

omit [DecidableEq H] in
/-- Real integrands: the complex-scalar pairing reduces to the real-scalar pairing. -/
theorem integral_ofReal_lsmul_vectorMeasure {f : X → ℝ} (hf : Integrable f V.variation) :
    VectorMeasure.integral V (fun x => (f x : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ) =
      VectorMeasure.integral V f (ContinuousLinearMap.lsmul ℝ ℝ) := by
  have h := VectorMeasure.integral_continuousLinearMap_comp (μ := V)
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (C := Complex.ofRealCLM) hf
  simp only [Complex.ofRealCLM_apply] at h
  rw [h]
  congr 1

omit [DecidableEq H] in
/-- Complex constants come out of the operator integral. -/
theorem integral_const_mul_vectorMeasure (c : ℂ) {f : X → ℂ} (hf : Integrable f V.variation) :
    VectorMeasure.integral V (fun x => c * f x) (ContinuousLinearMap.lsmul ℝ ℂ) =
      c • VectorMeasure.integral V f (ContinuousLinearMap.lsmul ℝ ℂ) := by
  have h1 : (fun x => c * f x) = fun x => (ContinuousLinearMap.lsmul ℝ ℂ c : ℂ →L[ℝ] ℂ) (f x) := by
    funext x
    simp
  rw [h1, VectorMeasure.integral_continuousLinearMap_comp hf]
  have h2 := VectorMeasure.continuousLinearMap_apply_integral (μ := V)
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))
    (C := (ContinuousLinearMap.lsmul ℝ ℂ c : (H → H → ℂ) →L[ℝ] (H → H → ℂ))) hf
  rw [ContinuousLinearMap.lsmul_apply] at h2
  rw [h2]
  congr 1
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun M => ?_
  simp [smul_smul]

omit [DecidableEq H] in
/-- A complex integrand splits into real and imaginary parts. -/
theorem integral_eq_re_add_im {g : X → ℂ} (hg : Integrable g V.variation) :
    VectorMeasure.integral V g (ContinuousLinearMap.lsmul ℝ ℂ) =
      VectorMeasure.integral V (fun x => (g x).re) (ContinuousLinearMap.lsmul ℝ ℝ) +
        Complex.I • VectorMeasure.integral V (fun x => (g x).im)
          (ContinuousLinearMap.lsmul ℝ ℝ) := by
  have hre : Integrable (fun x => (g x).re) V.variation := hg.re
  have him : Integrable (fun x => (g x).im) V.variation := hg.im
  have hsplit : g = fun x => (((g x).re : ℝ) : ℂ) + Complex.I * (((g x).im : ℝ) : ℂ) := by
    funext x
    rw [mul_comm]
    exact (Complex.re_add_im (g x)).symm
  have h3 : VectorMeasure.integral V (fun x => Complex.I * (((g x).im : ℝ) : ℂ))
      (ContinuousLinearMap.lsmul ℝ ℂ) =
      Complex.I • VectorMeasure.integral V (fun x => (((g x).im : ℝ) : ℂ))
        (ContinuousLinearMap.lsmul ℝ ℂ) :=
    integral_const_mul_vectorMeasure V Complex.I him.ofReal
  conv_lhs => rw [hsplit]
  rw [VectorMeasure.integral_fun_add hre.ofReal ((him.ofReal).const_mul _), h3,
    integral_ofReal_lsmul_vectorMeasure V hre, integral_ofReal_lsmul_vectorMeasure V him]

end ComplexSplit

/-! ## Uniform convergence of Lipschitz families on compact sets -/

/-- A pointwise convergent sequence of uniformly Lipschitz maps converges uniformly on compact
sets (ε/3 argument through a finite net). -/
theorem tendstoUniformlyOn_of_lipschitzOnWith {α β : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] {F : ℕ → α → β} {f : α → β} {K : Set α} (hK : IsCompact K) {L : ℝ≥0}
    (hF : ∀ n, LipschitzOnWith L (F n) K)
    (hlim : ∀ z ∈ K, Tendsto (fun n => F n z) atTop (𝓝 (f z))) :
    TendstoUniformlyOn F f atTop K := by
  have hf : LipschitzOnWith L f K := by
    intro z hz z' hz'
    rw [edist_dist, edist_dist]
    have h1 := ((hlim z hz).dist (hlim z' hz'))
    have h2 : ∀ n, dist (F n z) (F n z') ≤ L * dist z z' := fun n => (hF n).dist_le_mul z hz z' hz'
    have h3 : dist (f z) (f z') ≤ L * dist z z' := le_of_tendsto' h1 h2
    calc ENNReal.ofReal (dist (f z) (f z')) ≤ ENNReal.ofReal (L * dist z z') :=
          ENNReal.ofReal_le_ofReal h3
      _ = (L : ℝ≥0∞) * ENNReal.ofReal (dist z z') := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := ε / (3 * ((L : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact hK hδpos
  have hev : ∀ᶠ n in atTop, ∀ x ∈ t, dist (f x) (F n x) < ε / 3 := by
    rw [eventually_all_finite htfin]
    intro x hx
    have := (hlim x (htK hx))
    exact (Metric.tendsto_nhds.mp this (ε / 3) (by positivity)).mono fun n hn => by
      rw [dist_comm]; exact hn
  filter_upwards [hev] with n hn
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  rw [Metric.mem_ball] at hxy
  have hLδ : (L : ℝ) * δ ≤ ε / 3 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hε, L.coe_nonneg]
  have h1 : dist (f x) (f y) ≤ L * δ :=
    (hf.dist_le_mul x hx y (htK hy)).trans (by gcongr)
  have h2 : dist (F n y) (F n x) ≤ L * δ :=
    (hF n).dist_le_mul y (htK hy) x hx |>.trans (by rw [dist_comm]; gcongr)
  have h3 := hn y hy
  calc dist (f x) (F n x) ≤ dist (f x) (f y) + dist (f y) (F n y) + dist (F n y) (F n x) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

end OperatorMeasureL2

/-! ## The escape space `[0, 1/m]` and the push-forward of `λ⁻¹ dμ` -/

namespace OperatorTailMeasure

open OperatorMeasureL2

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The one-point compactification `[m, ∞]` of `[m, ∞)`, realised as `[0, 1/m]` through `y = 1/λ`
(the point at infinity is `y = 0`). -/
abbrev EscapeSpace (m : ℝ) : Type := Icc (0 : ℝ) m⁻¹

/-- The coordinate `λ ↦ 1/λ` from `ℝ` to the escape space (clamped outside `[m, ∞)`). -/
noncomputable def escapeCoord {m : ℝ} (hm : 0 < m) (lam : ℝ) : EscapeSpace m :=
  projIcc 0 m⁻¹ (inv_nonneg.mpr hm.le) lam⁻¹

theorem measurable_escapeCoord {m : ℝ} (hm : 0 < m) : Measurable (escapeCoord hm) :=
  (continuous_projIcc.measurable).comp measurable_inv

theorem escapeCoord_apply_of_le {m : ℝ} (hm : 0 < m) {lam : ℝ} (hlam : m ≤ lam) :
    (escapeCoord hm lam : ℝ) = lam⁻¹ := by
  unfold escapeCoord
  rw [projIcc_of_mem]
  exact ⟨inv_nonneg.mpr (hm.trans_le hlam).le, inv_anti₀ hm hlam⟩

/-- The point at infinity, `y = 0`. -/
def escapeInfty (m : ℝ) (hm : 0 < m) : EscapeSpace m := ⟨0, le_rfl, inv_nonneg.mpr hm.le⟩

namespace PositiveTailMeasure

variable (μ : PositiveTailMeasure H)

/-- `μ` is supported in `[m, ∞)`: it vanishes on Borel subsets of `(-∞, m)`. -/
def IsSupportedAbove (m : ℝ) : Prop :=
  ∀ s : Set ℝ, MeasurableSet s → s ⊆ Iio m → μ.toVectorMeasure s = 0

theorem variation_Iio_eq_zero {m : ℝ} (hμ : μ.IsSupportedAbove m) :
    μ.toVectorMeasure.variation (Iio m) = 0 :=
  (VectorMeasure.variation_apply_eq_zero measurableSet_Iio).2 fun t hts ht => hμ t ht hts

theorem ae_le_variation {m : ℝ} (hμ : μ.IsSupportedAbove m) :
    ∀ᵐ lam ∂μ.toVectorMeasure.variation, m ≤ lam := by
  rw [ae_iff]
  refine measure_mono_null (fun x (hx : ¬ m ≤ x) => not_le.mp hx) (μ.variation_Iio_eq_zero hμ)

theorem formMeasure_Iio_eq_zero {m : ℝ} (hμ : μ.IsSupportedAbove m) (ξ : H → ℂ) :
    μ.formMeasure ξ (Iio m) = 0 := by
  rw [μ.formMeasure_apply ξ measurableSet_Iio, hμ _ measurableSet_Iio subset_rfl, map_zero,
    ENNReal.ofReal_zero]

theorem ae_le_formMeasure {m : ℝ} (hμ : μ.IsSupportedAbove m) (ξ : H → ℂ) :
    ∀ᵐ lam ∂μ.formMeasure ξ, m ≤ lam := by
  rw [ae_iff]
  refine measure_mono_null (fun x (hx : ¬ m ≤ x) => not_le.mp hx) (μ.formMeasure_Iio_eq_zero hμ ξ)

/-- Bounded measurable functions are integrable against the variation. -/
theorem integrable_variation_of_bound {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ᵐ lam ∂μ.toVectorMeasure.variation, ‖f lam‖ ≤ C) :
    Integrable f μ.toVectorMeasure.variation :=
  Integrable.of_bound hf.aestronglyMeasurable C hC

theorem integrable_inv_variation {m : ℝ} (hm : 0 < m) (hμ : μ.IsSupportedAbove m) :
    Integrable (fun lam : ℝ => lam⁻¹) μ.toVectorMeasure.variation := by
  refine μ.integrable_variation_of_bound measurable_inv (C := m⁻¹) ?_
  filter_upwards [μ.ae_le_variation hμ] with lam hlam
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hm.trans_le hlam).le)]
  exact inv_anti₀ hm hlam

/-- A real operator integral of a nonnegative function is positive semidefinite (real pairing). -/
theorem posSemidef_integral_lsmul_of_nonneg {f : ℝ → ℝ}
    (hf : Integrable f μ.toVectorMeasure.variation) (hf0 : 0 ≤ᵐ[μ.toVectorMeasure.variation] f) :
    (Matrix.of (VectorMeasure.integral μ.toVectorMeasure f
      (ContinuousLinearMap.lsmul ℝ ℝ))).PosSemidef := by
  rw [← μ.integral_ofReal_lsmul hf]
  exact μ.posSemidef_integral_ofReal_of_nonneg hf hf0

/-- The measure `ν = λ⁻¹ dμ` (as a vector measure on `ℝ`). -/
noncomputable def invDensity : VectorMeasure ℝ (H → H → ℂ) :=
  μ.toVectorMeasure.withDensity (fun lam : ℝ => lam⁻¹) (ContinuousLinearMap.lsmul ℝ ℝ)

theorem invDensity_apply {m : ℝ} (hm : 0 < m) (hμ : μ.IsSupportedAbove m) {s : Set ℝ}
    (hs : MeasurableSet s) :
    μ.invDensity s = VectorMeasure.integral μ.toVectorMeasure
      (s.indicator fun lam : ℝ => lam⁻¹) (ContinuousLinearMap.lsmul ℝ ℝ) := by
  rw [invDensity, VectorMeasure.withDensity_apply (μ.integrable_inv_variation hm hμ),
    VectorMeasure.integral_indicator hs]

/-- **The escape measure**: the push-forward of `ν = λ⁻¹ dμ` to the escape space `[0, 1/m]`. -/
noncomputable def escapeMeasure {m : ℝ} (hm : 0 < m) (hμ : μ.IsSupportedAbove m) :
    PosOperatorMeasure (EscapeSpace m) H where
  toVectorMeasure := μ.invDensity.map (escapeCoord hm)
  posSemidef s hs := by
    rw [VectorMeasure.map_apply _ (measurable_escapeCoord hm) hs,
      μ.invDensity_apply hm hμ ((measurable_escapeCoord hm) hs)]
    refine μ.posSemidef_integral_lsmul_of_nonneg
      ((μ.integrable_inv_variation hm hμ).indicator ((measurable_escapeCoord hm) hs)) ?_
    filter_upwards [μ.ae_le_variation hμ] with lam hlam
    exact Set.indicator_nonneg (fun x _ => inv_nonneg.mpr (hm.trans_le hlam).le) lam

theorem escapeMeasure_apply {m : ℝ} (hm : 0 < m) (hμ : μ.IsSupportedAbove m)
    {s : Set (EscapeSpace m)} (hs : MeasurableSet s) :
    (μ.escapeMeasure hm hμ).toVectorMeasure s = VectorMeasure.integral μ.toVectorMeasure
      ((escapeCoord hm ⁻¹' s).indicator fun lam : ℝ => lam⁻¹) (ContinuousLinearMap.lsmul ℝ ℝ) := by
  change (μ.invDensity.map (escapeCoord hm)) s = _
  rw [VectorMeasure.map_apply _ (measurable_escapeCoord hm) hs,
    μ.invDensity_apply hm hμ ((measurable_escapeCoord hm) hs)]

/-- `Σ_μ(0) = ∫ λ⁻¹ dμ` with the real pairing. -/
theorem stieltjesSelfEnergy_zero_eq {m : ℝ} (hm : 0 < m) (hμ : μ.IsSupportedAbove m) :
    μ.stieltjesSelfEnergy 0 = Matrix.of (VectorMeasure.integral μ.toVectorMeasure
      (fun lam : ℝ => lam⁻¹) (ContinuousLinearMap.lsmul ℝ ℝ)) := by
  rw [stieltjesSelfEnergy, ← μ.integral_ofReal_lsmul (μ.integrable_inv_variation hm hμ)]
  congr 2
  funext lam
  simp

/-- The total mass of the escape measure is `Σ_μ(0) = ν([m, ∞))`. -/
theorem escapeMeasure_univ {m : ℝ} (hm : 0 < m) (hμ : μ.IsSupportedAbove m) :
    Matrix.of ((μ.escapeMeasure hm hμ).toVectorMeasure univ) = μ.stieltjesSelfEnergy 0 := by
  rw [μ.escapeMeasure_apply hm hμ MeasurableSet.univ, Set.preimage_univ, Set.indicator_univ,
    μ.stieltjesSelfEnergy_zero_eq hm hμ]

/-- The scalarisation of the escape measure is the push-forward of `λ⁻¹ d⟨ξ, μ ξ⟩`. -/
theorem formMeasure_escapeMeasure {m : ℝ} (hm : 0 < m) (hμ : μ.IsSupportedAbove m) (ξ : H → ℂ) :
    (μ.escapeMeasure hm hμ).formMeasure ξ =
      Measure.map (escapeCoord hm)
        ((μ.formMeasure ξ).withDensity fun lam : ℝ => ENNReal.ofReal lam⁻¹) := by
  refine Measure.ext fun s hs => ?_
  have hpre : MeasurableSet (escapeCoord hm ⁻¹' s) := (measurable_escapeCoord hm) hs
  rw [PosOperatorMeasure.formMeasure_apply _ ξ hs, μ.escapeMeasure_apply hm hμ hs,
    μ.quadFormCLM_integral ξ ((μ.integrable_inv_variation hm hμ).indicator hpre),
    Measure.map_apply (measurable_escapeCoord hm) hs, withDensity_apply _ hpre,
    ← lintegral_indicator hpre]
  have hnn : 0 ≤ᵐ[μ.formMeasure ξ] (escapeCoord hm ⁻¹' s).indicator fun lam : ℝ => lam⁻¹ := by
    filter_upwards [μ.ae_le_formMeasure hμ ξ] with lam hlam
    exact Set.indicator_nonneg (fun x _ => inv_nonneg.mpr (hm.trans_le hlam).le) lam
  rw [ofReal_integral_eq_lintegral_ofReal
    (((μ.integrable_inv_variation hm hμ).indicator hpre).of_measure_le_smul ENNReal.coe_ne_top
      (μ.formMeasure_le_smul_variation ξ)) hnn]
  congr 1
  funext lam
  rw [← Function.comp_apply (f := ENNReal.ofReal), ← Set.indicator_comp_of_zero ENNReal.ofReal_zero]
  rfl

theorem escapeMeasure_formMeasure_apply_univ {m : ℝ} (hm : 0 < m) (hμ : μ.IsSupportedAbove m)
    (ξ : H → ℂ) : ((μ.escapeMeasure hm hμ).formMeasure ξ) univ =
      ENNReal.ofReal (quadForm ξ (μ.stieltjesSelfEnergy 0)).re := by
  rw [PosOperatorMeasure.formMeasure_apply _ ξ MeasurableSet.univ, quadFormCLM_apply,
    μ.escapeMeasure_univ hm hμ]

/-- **Change of variables**: the operator integral of a bounded measurable real `g` against the
escape measure is the integral of `g(1/λ) λ⁻¹` against `μ`. -/
theorem integral_escapeMeasure {m : ℝ} (hm : 0 < m) (hμ : μ.IsSupportedAbove m)
    {g : EscapeSpace m → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ y, ‖g y‖ ≤ C) :
    VectorMeasure.integral (μ.escapeMeasure hm hμ).toVectorMeasure g
        (ContinuousLinearMap.lsmul ℝ ℝ) =
      VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => g (escapeCoord hm lam) * lam⁻¹)
        (ContinuousLinearMap.lsmul ℝ ℝ) := by
  have hg1 : Integrable g (μ.escapeMeasure hm hμ).toVectorMeasure.variation :=
    Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hgC)
  have hg2 : Integrable (fun lam : ℝ => g (escapeCoord hm lam) * lam⁻¹)
      μ.toVectorMeasure.variation := by
    refine μ.integrable_variation_of_bound ((hg.comp (measurable_escapeCoord hm)).mul measurable_inv)
      (C := C * m⁻¹) ?_
    filter_upwards [μ.ae_le_variation hμ] with lam hlam
    rw [norm_mul, Real.norm_eq_abs (lam⁻¹), abs_of_nonneg (inv_nonneg.mpr (hm.trans_le hlam).le)]
    exact mul_le_mul (hgC _) (inv_anti₀ hm hlam) (inv_nonneg.mpr (hm.trans_le hlam).le)
      ((norm_nonneg _).trans (hgC (escapeCoord hm lam)))
  have hq : ∀ ξ : H → ℂ, quadForm ξ (Matrix.of (VectorMeasure.integral
      (μ.escapeMeasure hm hμ).toVectorMeasure g (ContinuousLinearMap.lsmul ℝ ℝ))) =
      quadForm ξ (Matrix.of (VectorMeasure.integral μ.toVectorMeasure
        (fun lam : ℝ => g (escapeCoord hm lam) * lam⁻¹) (ContinuousLinearMap.lsmul ℝ ℝ))) := by
    intro ξ
    rw [PosOperatorMeasure.quadForm_integral _ ξ hg1, ← μ.integral_ofReal_lsmul hg2,
      μ.quadForm_integral_ofReal ξ hg2, μ.formMeasure_escapeMeasure hm hμ ξ]
    congr 1
    rw [integral_map (measurable_escapeCoord hm).aemeasurable hg.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [μ.ae_le_formMeasure hμ ξ] with lam hlam
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (hm.trans_le hlam).le), smul_eq_mul, mul_comm]
  have hzero : ∀ ξ : H → ℂ, quadForm ξ (Matrix.of (VectorMeasure.integral
      (μ.escapeMeasure hm hμ).toVectorMeasure g (ContinuousLinearMap.lsmul ℝ ℝ)) -
      Matrix.of (VectorMeasure.integral μ.toVectorMeasure
        (fun lam : ℝ => g (escapeCoord hm lam) * lam⁻¹) (ContinuousLinearMap.lsmul ℝ ℝ))) = 0 :=
    fun ξ => by rw [quadForm_sub, hq ξ, sub_self]
  have := sub_eq_zero.mp (matrix_eq_zero_of_forall_quadForm_eq_zero hzero)
  exact congrArg Matrix.of.symm this

end PositiveTailMeasure


/-! ## The limit measure: atom at infinity and finite part -/

section LimitMeasure

variable {m : ℝ} (hm : 0 < m)

/-- The coordinate `y ↦ 1/y` back from the escape space to `ℝ`. -/
noncomputable def escapeInv (m : ℝ) (y : EscapeSpace m) : ℝ := (y : ℝ)⁻¹

theorem measurable_escapeInv (m : ℝ) : Measurable (escapeInv m) :=
  measurable_inv.comp measurable_subtype_coe

theorem escapeInv_pos {y : EscapeSpace m} (hy : y ≠ escapeInfty m hm) : 0 < escapeInv m y := by
  have h0 : (y : ℝ) ≠ 0 := fun h => hy (Subtype.ext h)
  exact inv_pos.mpr (lt_of_le_of_ne y.2.1 (Ne.symm h0))

theorem le_escapeInv {y : EscapeSpace m} (hy : y ≠ escapeInfty m hm) : m ≤ escapeInv m y := by
  have h0 : (y : ℝ) ≠ 0 := fun h => hy (Subtype.ext h)
  have hpos : 0 < (y : ℝ) := lt_of_le_of_ne y.2.1 (Ne.symm h0)
  have := inv_anti₀ hpos y.2.2
  rwa [inv_inv] at this

/-- **The finite part** `ν_fin` of a positive operator-valued measure on the escape space: its
restriction to `(0, 1/m]` pulled back to `[m, ∞)` through `λ = 1/y`. -/
noncomputable def finitePart (ν : PosOperatorMeasure (EscapeSpace m) H) :
    PositiveTailMeasure H where
  toVectorMeasure := (ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ).map (escapeInv m)
  posSemidef s hs := by
    rw [VectorMeasure.map_apply _ (measurable_escapeInv m) hs,
      VectorMeasure.restrict_apply _ (measurableSet_singleton _).compl ((measurable_escapeInv m) hs)]
    exact ν.posSemidef _ (((measurable_escapeInv m) hs).inter (measurableSet_singleton _).compl)
  eq_zero_of_subset_Iic s hs hsub := by
    rw [VectorMeasure.map_apply _ (measurable_escapeInv m) hs,
      VectorMeasure.restrict_apply _ (measurableSet_singleton _).compl ((measurable_escapeInv m) hs)]
    have : escapeInv m ⁻¹' s ∩ {escapeInfty m hm}ᶜ = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff, mem_empty_iff_false,
        iff_false, not_and]
      intro hys hy
      have := hsub hys
      rw [mem_Iic] at this
      exact absurd this (not_le.mpr (escapeInv_pos hm hy))
    rw [this, VectorMeasure.empty]

theorem finitePart_apply (ν : PosOperatorMeasure (EscapeSpace m) H) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (finitePart hm ν).toVectorMeasure s =
      ν.toVectorMeasure (escapeInv m ⁻¹' s ∩ {escapeInfty m hm}ᶜ) := by
  change ((ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ).map (escapeInv m)) s = _
  rw [VectorMeasure.map_apply _ (measurable_escapeInv m) hs,
    VectorMeasure.restrict_apply _ (measurableSet_singleton _).compl ((measurable_escapeInv m) hs)]

/-- The finite part is supported in `[m, ∞)`. -/
theorem finitePart_isSupportedAbove (ν : PosOperatorMeasure (EscapeSpace m) H) :
    (finitePart hm ν).IsSupportedAbove m := by
  intro s hs hsub
  rw [finitePart_apply hm ν hs]
  have : escapeInv m ⁻¹' s ∩ {escapeInfty m hm}ᶜ = ∅ := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff, mem_empty_iff_false,
      iff_false, not_and]
    intro hys hy
    have := hsub hys
    rw [mem_Iio] at this
    exact absurd this (not_lt.mpr (le_escapeInv hm hy))
  rw [this, VectorMeasure.empty]

/-- Integrals against the finite part are set integrals over `(0, 1/m]` on the escape space. -/
theorem integral_finitePart (ν : PosOperatorMeasure (EscapeSpace m) H) {h : ℝ → ℂ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ y : EscapeSpace m, ‖h (escapeInv m y)‖ ≤ C) :
    VectorMeasure.integral (finitePart hm ν).toVectorMeasure h (ContinuousLinearMap.lsmul ℝ ℂ) =
      VectorMeasure.integral (ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ)
        (fun y => h (escapeInv m y)) (ContinuousLinearMap.lsmul ℝ ℂ) := by
  change VectorMeasure.integral ((ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ).map (escapeInv m))
    h _ = _
  refine VectorMeasure.integral_map (measurable_escapeInv m) hh.aestronglyMeasurable ?_
  exact Integrable.of_bound (hh.comp (measurable_escapeInv m)).aestronglyMeasurable C
    (ae_of_all _ hC)

/-- Splitting an integral on the escape space into the atom at infinity and the rest. -/
theorem integral_split (ν : PosOperatorMeasure (EscapeSpace m) H) {g : EscapeSpace m → ℂ}
    (hg : Integrable g ν.toVectorMeasure.variation) :
    VectorMeasure.integral ν.toVectorMeasure g (ContinuousLinearMap.lsmul ℝ ℂ) =
      g (escapeInfty m hm) • ν.toVectorMeasure {escapeInfty m hm} +
        VectorMeasure.integral (ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ) g
          (ContinuousLinearMap.lsmul ℝ ℂ) := by
  rw [← VectorMeasure.setIntegral_add_compl (measurableSet_singleton (escapeInfty m hm)) hg,
    VectorMeasure.integral_singleton]
  rfl

end LimitMeasure

/-! ## The self-energy on the escape space -/

/-- The domain `ℂ ∖ [m, ∞)`. -/
def escapeDomain (m : ℝ) : Set ℂ := {z | ¬ (z.im = 0 ∧ m ≤ z.re)}

theorem isOpen_escapeDomain (m : ℝ) : IsOpen (escapeDomain m) := by
  have hclosed : IsClosed {z : ℂ | z.im = 0 ∧ m ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  exact hclosed.isOpen_compl

/-- The transfer function `g_z(y) = (1 - z y)⁻¹` on the escape space (`= λ/(λ - z)` at
`y = 1/λ`, `= 1` at infinity). -/
noncomputable def escapeTransfer (m : ℝ) (z : ℂ) (y : EscapeSpace m) : ℂ :=
  (1 - z * ((y : ℝ) : ℂ))⁻¹

section Transfer

variable {m : ℝ} (hm : 0 < m)

theorem one_sub_mul_ne_zero {z : ℂ} (hz : z ∈ escapeDomain m) (y : EscapeSpace m) :
    1 - z * ((y : ℝ) : ℂ) ≠ 0 := by
  intro h
  have hzy : z * ((y : ℝ) : ℂ) = 1 := (sub_eq_zero.mp h).symm
  have hy0 : ((y : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hzy
    exact zero_ne_one hzy
  have hy0' : (y : ℝ) ≠ 0 := fun h0 => hy0 (by rw [h0, Complex.ofReal_zero])
  have hzeq : z = (((y : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv]
    exact eq_inv_of_mul_eq_one_left hzy
  have hypos : 0 < (y : ℝ) := lt_of_le_of_ne y.2.1 (Ne.symm hy0')
  have hle : m ≤ (y : ℝ)⁻¹ := by
    have := inv_anti₀ hypos y.2.2
    rwa [inv_inv] at this
  exact hz ⟨by rw [hzeq, Complex.ofReal_im], by rw [hzeq, Complex.ofReal_re]; exact hle⟩

theorem continuous_escapeTransfer {z : ℂ} (hz : z ∈ escapeDomain m) :
    Continuous (escapeTransfer m z) :=
  (continuous_const.sub (continuous_const.mul
    (Complex.continuous_ofReal.comp continuous_subtype_val))).inv₀ (one_sub_mul_ne_zero hz)

theorem escapeTransfer_infty (z : ℂ) : escapeTransfer m z (escapeInfty m hm) = 1 := by
  simp [escapeTransfer, escapeInfty]

/-- `g_z(1/λ) λ⁻¹ = (λ - z)⁻¹` for `λ ≥ m`. -/
theorem escapeTransfer_escapeCoord_mul_inv (z : ℂ) {lam : ℝ} (hlam : m ≤ lam) :
    escapeTransfer m z (escapeCoord hm lam) * ((lam⁻¹ : ℝ) : ℂ) = ((lam : ℂ) - z)⁻¹ := by
  have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hm.trans_le hlam).ne'
  rw [escapeTransfer, escapeCoord_apply_of_le hm hlam, Complex.ofReal_inv]
  have : (1 : ℂ) - z * (lam : ℂ)⁻¹ = ((lam : ℂ) - z) * (lam : ℂ)⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hl]
  rw [this, mul_inv, inv_inv, mul_assoc, mul_inv_cancel₀ hl, mul_one]

/-- `g_z(y) = λ/(λ - z)` at `λ = 1/y` for `y ≠ 0`. -/
theorem escapeTransfer_eq_of_ne {z : ℂ} {y : EscapeSpace m} (hy : y ≠ escapeInfty m hm) :
    escapeTransfer m z y = ((escapeInv m y : ℝ) : ℂ) / (((escapeInv m y : ℝ) : ℂ) - z) := by
  have hy0 : ((y : ℝ) : ℂ) ≠ 0 := by
    intro h
    exact hy (Subtype.ext (Complex.ofReal_eq_zero.mp h))
  rw [escapeTransfer, escapeInv, Complex.ofReal_inv, div_eq_mul_inv]
  have : ((y : ℝ) : ℂ)⁻¹ - z = (1 - z * ((y : ℝ) : ℂ)) * ((y : ℝ) : ℂ)⁻¹ := by
    rw [sub_mul, one_mul, mul_assoc, mul_inv_cancel₀ hy0, mul_one]
  rw [this, mul_inv, inv_inv, mul_left_comm, inv_mul_cancel₀ hy0, mul_one]

end Transfer

namespace PositiveTailMeasure

variable {m : ℝ} (hm : 0 < m) (μ : PositiveTailMeasure H)

/-- **The self-energy as an integral over the escape space**:
`Σ_μ(z) = ∫_{[0,1/m]} (1 - z y)⁻¹ dν̃(y)` where `ν̃` is the escape measure. -/
theorem stieltjesSelfEnergy_eq_integral_escapeMeasure (hμ : μ.IsSupportedAbove m) {z : ℂ}
    (hz : z ∈ escapeDomain m) :
    μ.stieltjesSelfEnergy z = Matrix.of (VectorMeasure.integral
      (μ.escapeMeasure hm hμ).toVectorMeasure (escapeTransfer m z)
      (ContinuousLinearMap.lsmul ℝ ℂ)) := by
  set G : EscapeSpace m →ᵇ ℂ := mkOfCompact ⟨escapeTransfer m z, continuous_escapeTransfer hz⟩
    with hG
  have hGapply : ∀ y, G y = escapeTransfer m z y := fun y => rfl
  have hbound : ∀ y, ‖escapeTransfer m z y‖ ≤ ‖G‖ := fun y => by
    rw [← hGapply]; exact G.norm_coe_le_norm y
  have hre_bound : ∀ y, ‖(escapeTransfer m z y).re‖ ≤ ‖G‖ := fun y =>
    (Complex.abs_re_le_norm _).trans (hbound y)
  have him_bound : ∀ y, ‖(escapeTransfer m z y).im‖ ≤ ‖G‖ := fun y =>
    (Complex.abs_im_le_norm _).trans (hbound y)
  have hmeas : Measurable (escapeTransfer m z) := (continuous_escapeTransfer hz).measurable
  have hint1 : Integrable (escapeTransfer m z) (μ.escapeMeasure hm hμ).toVectorMeasure.variation :=
    Integrable.of_bound hmeas.aestronglyMeasurable ‖G‖ (ae_of_all _ hbound)
  have hint2 : Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ.toVectorMeasure.variation := by
    refine Integrable.of_bound (by fun_prop) (‖G‖ * m⁻¹) ?_
    filter_upwards [μ.ae_le_variation hμ] with lam hlam
    rw [← escapeTransfer_escapeCoord_mul_inv hm z hlam, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hm.trans_le hlam).le)]
    exact mul_le_mul (hbound _) (inv_anti₀ hm hlam) (inv_nonneg.mpr (hm.trans_le hlam).le)
      ((norm_nonneg _).trans (hbound (escapeCoord hm lam)))
  have hmeas_re : Measurable fun y => (escapeTransfer m z y).re := Complex.measurable_re.comp hmeas
  have hmeas_im : Measurable fun y => (escapeTransfer m z y).im := Complex.measurable_im.comp hmeas
  rw [stieltjesSelfEnergy, integral_eq_re_add_im _ hint1, integral_eq_re_add_im _ hint2,
    μ.integral_escapeMeasure hm hμ hmeas_re hre_bound,
    μ.integral_escapeMeasure hm hμ hmeas_im him_bound]
  have hre : VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => (((lam : ℂ) - z)⁻¹).re)
      (ContinuousLinearMap.lsmul ℝ ℝ) = VectorMeasure.integral μ.toVectorMeasure
        (fun lam : ℝ => (escapeTransfer m z (escapeCoord hm lam)).re * lam⁻¹)
        (ContinuousLinearMap.lsmul ℝ ℝ) := by
    refine VectorMeasure.integral_congr_ae ?_
    filter_upwards [μ.ae_le_variation hμ] with lam hlam
    rw [← escapeTransfer_escapeCoord_mul_inv hm z hlam, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have him : VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => (((lam : ℂ) - z)⁻¹).im)
      (ContinuousLinearMap.lsmul ℝ ℝ) = VectorMeasure.integral μ.toVectorMeasure
        (fun lam : ℝ => (escapeTransfer m z (escapeCoord hm lam)).im * lam⁻¹)
        (ContinuousLinearMap.lsmul ℝ ℝ) := by
    refine VectorMeasure.integral_congr_ae ?_
    filter_upwards [μ.ae_le_variation hμ] with lam hlam
    rw [← escapeTransfer_escapeCoord_mul_inv hm z hlam, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
  rw [hre, him]

end PositiveTailMeasure

/-! ## The limit of the self-energies -/

section SelfEnergyLimit

variable {m : ℝ} (hm : 0 < m)

/-- The limiting self-energy `Q_esc + ∫ λ/(λ - z) dν_fin(λ)` (`eq:supp-contact-selfenergy`). -/
noncomputable def escapeLimitSelfEnergy (ν : PosOperatorMeasure (EscapeSpace m) H) (z : ℂ) :
    Matrix H H ℂ :=
  Matrix.of (ν.toVectorMeasure {escapeInfty m hm}) +
    Matrix.of (VectorMeasure.integral (finitePart hm ν).toVectorMeasure
      (fun lam : ℝ => (lam : ℂ) / ((lam : ℂ) - z)) (ContinuousLinearMap.lsmul ℝ ℂ))

/-- The limiting self-energy is the integral of `g_z` against the limit measure. -/
theorem escapeLimitSelfEnergy_eq_integral (ν : PosOperatorMeasure (EscapeSpace m) H) {z : ℂ}
    (hz : z ∈ escapeDomain m) :
    escapeLimitSelfEnergy hm ν z = Matrix.of (VectorMeasure.integral ν.toVectorMeasure
      (escapeTransfer m z) (ContinuousLinearMap.lsmul ℝ ℂ)) := by
  set G : EscapeSpace m →ᵇ ℂ := mkOfCompact ⟨escapeTransfer m z, continuous_escapeTransfer hz⟩
  have hbound : ∀ y, ‖escapeTransfer m z y‖ ≤ ‖G‖ := fun y => G.norm_coe_le_norm y
  have hmeas : Measurable (escapeTransfer m z) := (continuous_escapeTransfer hz).measurable
  have hint : Integrable (escapeTransfer m z) ν.toVectorMeasure.variation :=
    Integrable.of_bound hmeas.aestronglyMeasurable ‖G‖ (ae_of_all _ hbound)
  have hh : Measurable fun lam : ℝ => (lam : ℂ) / ((lam : ℂ) - z) := by fun_prop
  have hhC : ∀ y : EscapeSpace m, ‖((escapeInv m y : ℝ) : ℂ) / (((escapeInv m y : ℝ) : ℂ) - z)‖ ≤
      ‖G‖ := by
    intro y
    by_cases hy : y = escapeInfty m hm
    · subst hy
      simp [escapeInv, escapeInfty]
    · rw [← escapeTransfer_eq_of_ne hm hy]
      exact hbound y
  have hset : VectorMeasure.integral (ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ)
      (escapeTransfer m z) (ContinuousLinearMap.lsmul ℝ ℂ) =
      VectorMeasure.integral (ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ)
        (fun y => ((escapeInv m y : ℝ) : ℂ) / (((escapeInv m y : ℝ) : ℂ) - z))
        (ContinuousLinearMap.lsmul ℝ ℂ) :=
    VectorMeasure.setIntegral_congr_fun fun y hy => escapeTransfer_eq_of_ne hm hy
  rw [integral_split hm ν hint, escapeTransfer_infty hm z, one_smul, hset, escapeLimitSelfEnergy,
    integral_finitePart hm ν hh hhC]
  rfl

/-- **Pointwise convergence** of the self-energies along the extracted subsequence. -/
theorem tendsto_stieltjesSelfEnergy_escape (μ : ℕ → PositiveTailMeasure H)
    (hμ : ∀ n, (μ n).IsSupportedAbove m) (ν : PosOperatorMeasure (EscapeSpace m) H)
    (hconv : ∀ g : EscapeSpace m →ᵇ ℝ, Tendsto (fun n => VectorMeasure.integral
      (((μ n).escapeMeasure hm (hμ n)).toVectorMeasure) g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) atTop
      (𝓝 (VectorMeasure.integral ν.toVectorMeasure g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))))
    {z : ℂ} (hz : z ∈ escapeDomain m) :
    Tendsto (fun n => (μ n).stieltjesSelfEnergy z) atTop (𝓝 (escapeLimitSelfEnergy hm ν z)) := by
  simp_rw [fun n => (μ n).stieltjesSelfEnergy_eq_integral_escapeMeasure hm (hμ n) hz]
  rw [escapeLimitSelfEnergy_eq_integral hm ν hz]
  set G : EscapeSpace m →ᵇ ℂ := mkOfCompact ⟨escapeTransfer m z, continuous_escapeTransfer hz⟩
  have hbound : ∀ y, ‖escapeTransfer m z y‖ ≤ ‖G‖ := fun y => G.norm_coe_le_norm y
  have hmeas : Measurable (escapeTransfer m z) := (continuous_escapeTransfer hz).measurable
  have hint : ∀ V : VectorMeasure (EscapeSpace m) (H → H → ℂ), IsFiniteMeasure V.variation →
      Integrable (escapeTransfer m z) V.variation := fun V _ =>
    Integrable.of_bound hmeas.aestronglyMeasurable ‖G‖ (ae_of_all _ hbound)
  simp_rw [fun n => integral_eq_re_add_im _ (hint _ inferInstance)]
  set gre : EscapeSpace m →ᵇ ℝ :=
    mkOfCompact ⟨fun y => (escapeTransfer m z y).re,
      Complex.continuous_re.comp (continuous_escapeTransfer hz)⟩
  set gim : EscapeSpace m →ᵇ ℝ :=
    mkOfCompact ⟨fun y => (escapeTransfer m z y).im,
      Complex.continuous_im.comp (continuous_escapeTransfer hz)⟩
  have h1 := hconv gre
  have h2 := hconv gim
  exact h1.add (h2.const_smul Complex.I)

include hm in
/-- The self-energies are uniformly Lipschitz on compact subsets of `ℂ ∖ [m, ∞)`, with a
constant controlled by the trace mass. -/
theorem lipschitzOnWith_integral_escapeTransfer {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ escapeDomain m) {C : ℝ} (hC0 : 0 ≤ C) :
    ∃ L : ℝ≥0, ∀ ν : PosOperatorMeasure (EscapeSpace m) H,
      (ν.toVectorMeasure.variation.real univ ≤ C) →
      LipschitzOnWith L (fun z => VectorMeasure.integral ν.toVectorMeasure
        (escapeTransfer m z) (ContinuousLinearMap.lsmul ℝ ℂ)) K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, fun ν _ => by rw [hKe]; exact fun x hx => absurd hx (by simp)⟩
  -- a uniform lower bound on `|1 - z y|`
  have hXne : Nonempty (EscapeSpace m) := ⟨escapeInfty m hm⟩
  set Φ : ℂ × EscapeSpace m → ℝ := fun p => ‖1 - p.1 * ((p.2 : ℝ) : ℂ)‖
  have hΦ : Continuous Φ := (continuous_const.sub (continuous_fst.mul
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)))).norm
  obtain ⟨p, hpK, hpmin⟩ := (hK.prod isCompact_univ).exists_isMinOn
    (hKne.prod univ_nonempty) hΦ.continuousOn
  set c : ℝ := Φ p with hc
  have hcpos : 0 < c := norm_pos_iff.mpr (one_sub_mul_ne_zero (hKΩ hpK.1) p.2)
  have hlow : ∀ z ∈ K, ∀ y : EscapeSpace m, c ≤ ‖1 - z * ((y : ℝ) : ℂ)‖ := fun z hz y =>
    hpmin (mk_mem_prod hz (mem_univ y))
  refine ⟨⟨m⁻¹ * C / (c * c), by positivity⟩, fun ν hν => ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
  have hint : ∀ w ∈ K, Integrable (escapeTransfer m w) ν.toVectorMeasure.variation := by
    intro w hw
    refine Integrable.of_bound (continuous_escapeTransfer (hKΩ hw)).measurable.aestronglyMeasurable
      c⁻¹ (ae_of_all _ fun y => ?_)
    rw [escapeTransfer, norm_inv]
    exact inv_anti₀ hcpos (hlow w hw y)
  rw [dist_eq_norm, ← VectorMeasure.integral_fun_sub (hint z hz) (hint z' hz')]
  have hpt : ∀ y : EscapeSpace m, ‖escapeTransfer m z y - escapeTransfer m z' y‖ ≤
      m⁻¹ / (c * c) * dist z z' := by
    intro y
    have h1 := one_sub_mul_ne_zero (hKΩ hz) y
    have h2 := one_sub_mul_ne_zero (hKΩ hz') y
    have h1' : 1 - ((y : ℝ) : ℂ) * z ≠ 0 := by rwa [mul_comm]
    have h2' : 1 - ((y : ℝ) : ℂ) * z' ≠ 0 := by rwa [mul_comm]
    have hid : escapeTransfer m z y - escapeTransfer m z' y =
        ((y : ℝ) : ℂ) * (z - z') / ((1 - z * ((y : ℝ) : ℂ)) * (1 - z' * ((y : ℝ) : ℂ))) := by
      rw [escapeTransfer, escapeTransfer]
      field_simp
      ring
    rw [hid, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg y.2.1, dist_eq_norm]
    have hy : (y : ℝ) ≤ m⁻¹ := y.2.2
    have hden : c * c ≤ ‖1 - z * ((y : ℝ) : ℂ)‖ * ‖1 - z' * ((y : ℝ) : ℂ)‖ :=
      mul_le_mul (hlow z hz y) (hlow z' hz' y) hcpos.le (norm_nonneg _)
    calc (y : ℝ) * ‖z - z'‖ / (‖1 - z * ((y : ℝ) : ℂ)‖ * ‖1 - z' * ((y : ℝ) : ℂ)‖)
        ≤ m⁻¹ * ‖z - z'‖ / (c * c) := by
          gcongr
    _ = m⁻¹ / (c * c) * ‖z - z'‖ := by ring
  have hB : ‖(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  calc ‖VectorMeasure.integral ν.toVectorMeasure
        (fun y => escapeTransfer m z y - escapeTransfer m z' y) (ContinuousLinearMap.lsmul ℝ ℂ)‖
      ≤ (m⁻¹ / (c * c) * dist z z') *
          ‖(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))‖ *
          ν.toVectorMeasure.variation.real univ :=
        VectorMeasure.norm_integral_le_of_norm_le_const (ae_of_all _ hpt)
    _ ≤ (m⁻¹ / (c * c) * dist z z') * 1 * C := by
        gcongr
    _ = ((⟨m⁻¹ * C / (c * c), by positivity⟩ : ℝ≥0) : ℝ) * dist z z' := by
        simp only
        ring

/-- The total variation of the escape measure is bounded by the trace of `Σ_μ(0)`. -/
theorem variation_real_escapeMeasure_le (μ : PositiveTailMeasure H) (hμ : μ.IsSupportedAbove m) :
    (μ.escapeMeasure hm hμ).toVectorMeasure.variation.real univ ≤
      (μ.stieltjesSelfEnergy 0).trace.re := by
  have h1 := (μ.escapeMeasure hm hμ).variation_le_traceMeasure univ
  rw [PosOperatorMeasure.traceMeasure_apply _ MeasurableSet.univ, μ.escapeMeasure_univ hm hμ] at h1
  rw [measureReal_def]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans ?_
  have hpsd : (μ.stieltjesSelfEnergy 0).PosSemidef := by
    rw [μ.stieltjesSelfEnergy_zero_eq hm hμ]
    refine μ.posSemidef_integral_lsmul_of_nonneg (μ.integrable_inv_variation hm hμ) ?_
    filter_upwards [μ.ae_le_variation hμ] with lam hlam
    exact inv_nonneg.mpr (hm.trans_le hlam).le
  rw [ENNReal.toReal_ofReal (posSemidef_re_trace_nonneg hpsd)]

end SelfEnergyLimit


/-! ## Fubini for Euclidean-time kernels -/

namespace PositiveTailMeasure

variable (ρ : PositiveTailMeasure H)

theorem quadForm_integral_lsmul (ξ : H → ℂ) {f : ℝ → ℝ}
    (hf : Integrable f ρ.toVectorMeasure.variation) :
    quadForm ξ (Matrix.of (VectorMeasure.integral ρ.toVectorMeasure f
      (ContinuousLinearMap.lsmul ℝ ℝ))) = ((∫ x, f x ∂(ρ.formMeasure ξ) : ℝ) : ℂ) := by
  rw [← ρ.integral_ofReal_lsmul hf]
  exact ρ.quadForm_integral_ofReal ξ hf

theorem re_trace_integral_lsmul {f : ℝ → ℝ} (hf : Integrable f ρ.toVectorMeasure.variation) :
    (Matrix.of (VectorMeasure.integral ρ.toVectorMeasure f
      (ContinuousLinearMap.lsmul ℝ ℝ))).trace.re = ∫ x, f x ∂ρ.traceMeasure := by
  rw [← ρ.integral_ofReal_lsmul hf]
  exact ρ.re_trace_integral_ofReal hf

theorem traceMeasure_Iio_eq_zero {m : ℝ} (hρ : ρ.IsSupportedAbove m) :
    ρ.traceMeasure (Iio m) = 0 := by
  rw [traceMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i _ => ρ.formMeasure_Iio_eq_zero hρ _

theorem ae_le_traceMeasure {m : ℝ} (hρ : ρ.IsSupportedAbove m) :
    ∀ᵐ lam ∂ρ.traceMeasure, m ≤ lam := by
  rw [ae_iff]
  exact measure_mono_null (t := Iio m) (fun x (hx : ¬ m ≤ x) => not_le.mp hx)
    (ρ.traceMeasure_Iio_eq_zero hρ)

section Fubini

variable {m : ℝ} (hm : 0 < m) (hρ : ρ.IsSupportedAbove m)
  (φ : ℝ → ℝ) (hφ : Continuous φ) {M : ℝ} (hM : ∀ t, |φ t| ≤ M)
  (w : ℝ → ℝ → ℝ) (hw : Continuous (Function.uncurry w))
  (hw0 : ∀ t lam, 0 < t → m ≤ lam → 0 ≤ w t lam)
  (hwint : ∀ lam, m ≤ lam → IntegrableOn (fun t => w t lam) (Ioi 0))
  {B : ℝ} (hw1 : ∀ lam, m ≤ lam → ∫ t in Ioi 0, w t lam ≤ B)
  (hwloc : ∀ a, 0 < a → ∃ C, ∀ t, a ≤ t → ∀ lam, m ≤ lam → w t lam ≤ C)

include hφ hM hw0 hwint hw1 in
/-- The Euclidean-time integral `∫_0^∞ φ(t) w(t, λ) dt` is bounded by `M B` for `λ ≥ m`. -/
theorem abs_integral_mul_kernel_le {lam : ℝ} (hlam : m ≤ lam) :
    |∫ t in Ioi 0, φ t * w t lam| ≤ M * B := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hint := (hwint lam hlam).bdd_mul hφ.aestronglyMeasurable (ae_of_all _ fun t => hM t)
  have hb : ∀ t ∈ Ioi (0 : ℝ), |φ t * w t lam| ≤ M * w t lam := fun t ht => by
    rw [abs_mul, abs_of_nonneg (hw0 t lam ht hlam)]
    exact mul_le_mul_of_nonneg_right (hM t) (hw0 t lam ht hlam)
  have hMB : M * ∫ t in Ioi 0, w t lam ≤ M * B := mul_le_mul_of_nonneg_left (hw1 lam hlam) hM0
  rw [abs_le]
  constructor
  · calc -(M * B) ≤ -(M * ∫ t in Ioi 0, w t lam) := neg_le_neg hMB
      _ = ∫ t in Ioi 0, -(M * w t lam) := by
          rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
      _ ≤ ∫ t in Ioi 0, φ t * w t lam := by
          exact integral_mono_ae (((hwint lam hlam).const_mul M).neg) hint
            ((ae_restrict_iff' measurableSet_Ioi).mpr
              (ae_of_all _ fun t ht => neg_le_of_abs_le (hb t ht)))
  · calc ∫ t in Ioi 0, φ t * w t lam ≤ ∫ t in Ioi 0, M * w t lam := by
          exact integral_mono_ae hint ((hwint lam hlam).const_mul M)
            ((ae_restrict_iff' measurableSet_Ioi).mpr
              (ae_of_all _ fun t ht => (le_abs_self _).trans (hb t ht)))
      _ = M * ∫ t in Ioi 0, w t lam := MeasureTheory.integral_const_mul _ _
      _ ≤ M * B := hMB

include hφ hM hw hw0 hwint hw1 in
/-- Product integrability of `φ(t) w(t, λ)` against `dt ⊗ σ` for a finite `σ` supported in
`[m, ∞)`. -/
theorem integrable_prod_kernel (σ : Measure ℝ) [IsFiniteMeasure σ] (hσ : ∀ᵐ lam ∂σ, m ≤ lam) :
    Integrable (Function.uncurry fun t lam => φ t * w t lam)
      (((volume : Measure ℝ).restrict (Ioi 0)).prod σ) := by
  have hcont : Continuous (Function.uncurry fun t lam => φ t * w t lam) :=
    (hφ.comp continuous_fst).mul hw
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  constructor
  · filter_upwards [hσ] with lam hlam
    exact (hwint lam hlam).bdd_mul hφ.aestronglyMeasurable (ae_of_all _ fun t => hM t)
  · refine Integrable.of_bound ?_ (M * B) ?_
    · exact (hcont.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
    · filter_upwards [hσ] with lam hlam
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      calc ∫ t in Ioi 0, ‖Function.uncurry (fun t lam => φ t * w t lam) (t, lam)‖
          ≤ ∫ t in Ioi 0, M * w t lam := by
            refine integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _)
              ((hwint lam hlam).const_mul M) ((ae_restrict_iff' measurableSet_Ioi).mpr
                (ae_of_all _ fun t ht => ?_))
            simp only [Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs]
            rw [abs_of_nonneg (hw0 t lam ht hlam)]
            exact mul_le_mul_of_nonneg_right (hM t) (hw0 t lam ht hlam)
        _ = M * ∫ t in Ioi 0, w t lam := MeasureTheory.integral_const_mul _ _
        _ ≤ M * B := mul_le_mul_of_nonneg_left (hw1 lam hlam) hM0

include hρ hw hw0 hwloc in
/-- The operator kernel `t ↦ ∫ w(t, λ) dρ(λ)` is continuous on `(0, ∞)`. -/
theorem continuousOn_integral_kernel :
    ContinuousOn (fun t => VectorMeasure.integral ρ.toVectorMeasure (fun lam => w t lam)
      (ContinuousLinearMap.lsmul ℝ ℝ)) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  obtain ⟨C, hC⟩ := hwloc (t₀ / 2) (by positivity)
  refine ContinuousAt.continuousWithinAt ?_
  have hev : ∀ᶠ t in 𝓝 t₀, t₀ / 2 ≤ t := eventually_ge_nhds (by linarith)
  refine VectorMeasure.continuousAt_of_dominated (bound := fun _ => max C 0) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun t =>
      (hw.comp (Continuous.prodMk continuous_const continuous_id)).measurable.aestronglyMeasurable
  · filter_upwards [hev] with t ht
    filter_upwards [ρ.ae_le_variation hρ] with lam hlam
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, (hC t ht lam hlam).trans (le_max_left _ _)⟩
    have : (0 : ℝ) < t := by linarith
    have h0 := hw0 t lam this hlam
    linarith [le_max_right C 0]
  · exact ae_of_all _ fun lam => (hw.comp (Continuous.prodMk continuous_id continuous_const)).continuousAt

include hρ hφ hM hw hw0 hwint hw1 hwloc in
/-- **Fubini for Euclidean kernels**: `∫_0^∞ φ(t) (∫ w(t,λ) dρ(λ)) dt = ∫ (∫_0^∞ φ(t) w(t,λ) dt) dρ(λ)`
for a bounded continuous `φ` and a nonnegative continuous kernel `w` with `∫_0^∞ w(t, λ) dt ≤ 1`. -/
theorem integral_smul_integral_kernel :
    ∫ t in Ioi 0, φ t • VectorMeasure.integral ρ.toVectorMeasure (fun lam => w t lam)
        (ContinuousLinearMap.lsmul ℝ ℝ) =
      VectorMeasure.integral ρ.toVectorMeasure (fun lam => ∫ t in Ioi 0, φ t * w t lam)
        (ContinuousLinearMap.lsmul ℝ ℝ) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set I : ℝ → H → H → ℂ := fun t => VectorMeasure.integral ρ.toVectorMeasure (fun lam => w t lam)
    (ContinuousLinearMap.lsmul ℝ ℝ) with hI
  -- integrability of `w(t, ·)` for `t > 0`
  have hwt : ∀ t, 0 < t → Integrable (fun lam => w t lam) ρ.toVectorMeasure.variation := by
    intro t ht
    obtain ⟨C, hC⟩ := hwloc t ht
    refine ρ.integrable_variation_of_bound
      (hw.comp (Continuous.prodMk continuous_const continuous_id)).measurable (C := max C 0) ?_
    filter_upwards [ρ.ae_le_variation hρ] with lam hlam
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hw0 t lam ht hlam, le_max_right C 0], (hC t le_rfl lam hlam).trans
      (le_max_left _ _)⟩
  -- the inner Bochner integral is integrable on `(0, ∞)`
  have hτ : Integrable (Function.uncurry fun t lam => (1 : ℝ) * w t lam)
      (((volume : Measure ℝ).restrict (Ioi 0)).prod ρ.traceMeasure) :=
    integrable_prod_kernel (fun _ => (1 : ℝ)) continuous_const (M := 1)
      (fun _ => by simp) w hw hw0 hwint (B := B) hw1 ρ.traceMeasure (ρ.ae_le_traceMeasure hρ)
  have hτ' : Integrable (fun t => ∫ lam, w t lam ∂ρ.traceMeasure)
      ((volume : Measure ℝ).restrict (Ioi 0)) := by
    have := hτ.integral_prod_left
    simpa only [Function.uncurry_apply_pair, one_mul] using this
  have hIcont := ρ.continuousOn_integral_kernel hρ w hw hw0 hwloc
  have hIint : Integrable (fun t => φ t • I t) ((volume : Measure ℝ).restrict (Ioi 0)) := by
    refine Integrable.mono' (hτ'.const_mul M) (hφ.aestronglyMeasurable.smul
      (hIcont.aestronglyMeasurable measurableSet_Ioi)) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    rw [norm_smul, Real.norm_eq_abs]
    have hpsd : (Matrix.of (I t)).PosSemidef := by
      refine ρ.posSemidef_integral_lsmul_of_nonneg (hwt t ht') ?_
      filter_upwards [ρ.ae_le_variation hρ] with lam hlam
      exact hw0 t lam ht' hlam
    have h1 : ‖I t‖ ≤ ∫ lam, w t lam ∂ρ.traceMeasure := by
      refine (posSemidef_norm_le_re_trace hpsd).trans ?_
      rw [ρ.re_trace_integral_lsmul (hwt t ht')]
    exact mul_le_mul (hM t) h1 (norm_nonneg _) hM0
  -- compare the quadratic forms
  have hq : ∀ ξ : H → ℂ, quadForm ξ (Matrix.of (∫ t in Ioi 0, φ t • I t)) =
      quadForm ξ (Matrix.of (VectorMeasure.integral ρ.toVectorMeasure
        (fun lam => ∫ t in Ioi 0, φ t * w t lam) (ContinuousLinearMap.lsmul ℝ ℝ))) := by
    intro ξ
    have hσ := ρ.ae_le_formMeasure hρ ξ
    have hprod := integrable_prod_kernel φ hφ hM w hw hw0 hwint hw1 (ρ.formMeasure ξ) hσ
    -- right-hand side
    have hfint : Integrable (fun lam => ∫ t in Ioi 0, φ t * w t lam) ρ.toVectorMeasure.variation := by
      refine ρ.integrable_variation_of_bound
        ((((hφ.comp continuous_fst).mul hw).stronglyMeasurable.integral_prod_left').measurable)
        (C := M * B) ?_
      filter_upwards [ρ.ae_le_variation hρ] with lam hlam
      rw [Real.norm_eq_abs]
      exact abs_integral_mul_kernel_le φ hφ hM w hw0 hwint hw1 hlam
    rw [ρ.quadForm_integral_lsmul ξ hfint]
    -- left-hand side through the sesquilinear functional
    change sesqCLM ξ ξ (∫ t in Ioi 0, φ t • I t) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ hIint]
    have hpt : ∀ t ∈ Ioi (0 : ℝ), sesqCLM ξ ξ (φ t • I t) =
        ((φ t * ∫ lam, w t lam ∂(ρ.formMeasure ξ) : ℝ) : ℂ) := by
      intro t ht
      rw [map_smul, sesqCLM_apply, sesqForm_self, hI]
      change φ t • quadForm ξ (Matrix.of (VectorMeasure.integral ρ.toVectorMeasure
        (fun lam => w t lam) (ContinuousLinearMap.lsmul ℝ ℝ))) = _
      rw [ρ.quadForm_integral_lsmul ξ (hwt t ht), Complex.real_smul, Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal]
    congr 1
    have hswap := integral_integral_swap hprod
    rw [← hswap]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [MeasureTheory.integral_const_mul]
  have hzero : ∀ ξ : H → ℂ, quadForm ξ (Matrix.of (∫ t in Ioi 0, φ t • I t) -
      Matrix.of (VectorMeasure.integral ρ.toVectorMeasure
        (fun lam => ∫ t in Ioi 0, φ t * w t lam) (ContinuousLinearMap.lsmul ℝ ℝ))) = 0 :=
    fun ξ => by rw [quadForm_sub, hq ξ, sub_self]
  have := sub_eq_zero.mp (matrix_eq_zero_of_forall_quadForm_eq_zero hzero)
  exact congrArg Matrix.of.symm this

end Fubini

end PositiveTailMeasure


/-! ## Locally uniform convergence of the self-energies -/

section Uniform

variable {m : ℝ} (hm : 0 < m)

include hm in
/-- **`eq:supp-contact-selfenergy`, locally uniform form.**  Along a subsequence whose escape
measures converge weakly to `ν`, the self-energies converge locally uniformly on `ℂ ∖ [m, ∞)`
to `Q_esc + ∫ λ/(λ - z) dν_fin(λ)`. -/
theorem tendstoLocallyUniformlyOn_stieltjesSelfEnergy (μ : ℕ → PositiveTailMeasure H)
    (hμ : ∀ n, (μ n).IsSupportedAbove m) {C : ℝ}
    (hC : ∀ n, ((μ n).stieltjesSelfEnergy 0).trace.re ≤ C)
    (ν : PosOperatorMeasure (EscapeSpace m) H)
    (hconv : ∀ g : EscapeSpace m →ᵇ ℝ, Tendsto (fun n => VectorMeasure.integral
      (((μ n).escapeMeasure hm (hμ n)).toVectorMeasure) g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) atTop
      (𝓝 (VectorMeasure.integral ν.toVectorMeasure g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))))) :
    TendstoLocallyUniformlyOn (fun n z => (μ n).stieltjesSelfEnergy z)
      (escapeLimitSelfEnergy hm ν) atTop (escapeDomain m) := by
  have hC0 : 0 ≤ C := by
    refine le_trans ?_ (hC 0)
    have h := variation_real_escapeMeasure_le hm (μ 0) (hμ 0)
    exact measureReal_nonneg.trans h
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_escapeDomain m)]
  intro K hKΩ hK
  obtain ⟨L, hL⟩ := lipschitzOnWith_integral_escapeTransfer hm (H := H) hK hKΩ hC0
  have key : TendstoUniformlyOn
      (fun n z => VectorMeasure.integral ((μ n).escapeMeasure hm (hμ n)).toVectorMeasure
        (escapeTransfer m z) (ContinuousLinearMap.lsmul ℝ ℂ))
      (fun z => VectorMeasure.integral ν.toVectorMeasure (escapeTransfer m z)
        (ContinuousLinearMap.lsmul ℝ ℂ)) atTop K := by
    refine tendstoUniformlyOn_of_lipschitzOnWith hK (L := L) (fun n => hL _ ?_) fun z hz => ?_
    · exact (variation_real_escapeMeasure_le hm (μ n) (hμ n)).trans (hC n)
    · have h := tendsto_stieltjesSelfEnergy_escape hm μ hμ ν hconv (hKΩ hz)
      rw [escapeLimitSelfEnergy_eq_integral hm ν (hKΩ hz)] at h
      simp_rw [fun n => (μ n).stieltjesSelfEnergy_eq_integral_escapeMeasure hm (hμ n) (hKΩ hz)] at h
      exact h
  refine (key.congr (Eventually.of_forall fun n z hz => ?_)).congr_right fun z hz => ?_
  · exact ((μ n).stieltjesSelfEnergy_eq_integral_escapeMeasure hm (hμ n) (hKΩ hz)).symm
  · exact (escapeLimitSelfEnergy_eq_integral hm ν (hKΩ hz)).symm

end Uniform

/-! ## The Euclidean memory kernels (`eq:supp-contact-kernel`) -/

section Kernel

variable {m : ℝ} (hm : 0 < m)

/-- Real version of `integral_finitePart`. -/
theorem integral_finitePart_real (ν : PosOperatorMeasure (EscapeSpace m) H) {h : ℝ → ℝ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ y : EscapeSpace m, ‖h (escapeInv m y)‖ ≤ C) :
    VectorMeasure.integral (finitePart hm ν).toVectorMeasure h (ContinuousLinearMap.lsmul ℝ ℝ) =
      VectorMeasure.integral (ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ)
        (fun y => h (escapeInv m y)) (ContinuousLinearMap.lsmul ℝ ℝ) := by
  change VectorMeasure.integral ((ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ).map (escapeInv m))
    h _ = _
  refine VectorMeasure.integral_map (measurable_escapeInv m) hh.aestronglyMeasurable ?_
  exact Integrable.of_bound (hh.comp (measurable_escapeInv m)).aestronglyMeasurable C
    (ae_of_all _ hC)

/-- Real version of `integral_split`. -/
theorem integral_split_real (ν : PosOperatorMeasure (EscapeSpace m) H) {g : EscapeSpace m → ℝ}
    (hg : Integrable g ν.toVectorMeasure.variation) :
    VectorMeasure.integral ν.toVectorMeasure g (ContinuousLinearMap.lsmul ℝ ℝ) =
      g (escapeInfty m hm) • ν.toVectorMeasure {escapeInfty m hm} +
        VectorMeasure.integral (ν.toVectorMeasure.restrict {escapeInfty m hm}ᶜ) g
          (ContinuousLinearMap.lsmul ℝ ℝ) := by
  rw [← VectorMeasure.setIntegral_add_compl (measurableSet_singleton (escapeInfty m hm)) hg,
    VectorMeasure.integral_singleton]
  rfl

/-- The test function `h_φ(y) = ∫_0^∞ φ(s y) e^{-s} ds` on the escape space: `h_φ(1/λ) =
∫_0^∞ φ(t) λ e^{-λ t} dt` and `h_φ(∞) = φ(0)`. -/
noncomputable def escapeTest (m : ℝ) (φ : ℝ → ℝ) (y : EscapeSpace m) : ℝ :=
  ∫ s in Ioi 0, φ (s * (y : ℝ)) * Real.exp (-s)

variable (φ : ℝ → ℝ) (hφ : Continuous φ) {M : ℝ} (hM : ∀ t, |φ t| ≤ M)

include hφ hM in
theorem continuous_escapeTest : Continuous (escapeTest m φ) := by
  refine continuous_of_dominated (F := fun (y : EscapeSpace m) (s : ℝ) =>
    φ (s * (y : ℝ)) * Real.exp (-s)) (bound := fun s => M * Real.exp (-s)) ?_ ?_ ?_ ?_
  · intro y
    exact ((hφ.comp (continuous_id.mul continuous_const)).mul
      (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable
  · intro y
    refine ae_of_all _ fun s => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hM _) (Real.exp_pos _).le
  · exact (integrableOn_exp_neg_Ioi 0).const_mul M
  · refine ae_of_all _ fun s => ?_
    exact (hφ.comp (continuous_const.mul continuous_subtype_val)).mul continuous_const

theorem escapeTest_infty : escapeTest m φ (escapeInfty m hm) = φ 0 := by
  have : ∀ s : ℝ, φ (s * ((escapeInfty m hm : EscapeSpace m) : ℝ)) = φ 0 := fun s => by
    simp [escapeInfty]
  simp only [escapeTest, this]
  rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

include hM in
theorem abs_escapeTest_le (y : EscapeSpace m) : |escapeTest m φ y| ≤ M := by
  rw [← Real.norm_eq_abs, escapeTest]
  calc ‖∫ s in Ioi 0, φ (s * (y : ℝ)) * Real.exp (-s)‖ ≤ ∫ s in Ioi 0, M * Real.exp (-s) := by
        refine norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 0).const_mul M)
          (ae_of_all _ fun s => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hM _) (Real.exp_pos _).le
    _ = M := by rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

theorem escapeTest_escapeCoord {lam : ℝ} (hlam : m ≤ lam) :
    escapeTest m φ (escapeCoord hm lam) = ∫ t in Ioi 0, φ t * (lam * Real.exp (-lam * t)) := by
  rw [escapeTest, escapeCoord_apply_of_le hm hlam, integral_mul_exp_eq φ (hm.trans_le hlam)]
  simp_rw [div_eq_mul_inv]

theorem escapeTest_eq_of_ne {y : EscapeSpace m} (hy : y ≠ escapeInfty m hm) :
    escapeTest m φ y =
      ∫ t in Ioi 0, φ t * (escapeInv m y * Real.exp (-(escapeInv m y) * t)) := by
  rw [integral_mul_exp_eq φ (escapeInv_pos hm hy), escapeTest]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [escapeInv, div_inv_eq_mul]

/-! ### The two Euclidean kernels `e^{-tλ}` and `λ e^{-λ t}` -/

include hm in
theorem integrableOn_exp_kernel {lam : ℝ} (hlam : m ≤ lam) :
    IntegrableOn (fun t : ℝ => Real.exp (-t * lam)) (Ioi 0) := by
  have : (fun t : ℝ => Real.exp (-t * lam)) = fun t => Real.exp (-lam * t) := by
    funext t; ring_nf
  rw [this]
  exact StieltjesLaplace.integrable_exp_neg_mul_restrict_Ioi (hm.trans_le hlam)

include hm in
theorem integral_exp_kernel_le {lam : ℝ} (hlam : m ≤ lam) :
    ∫ t in Ioi 0, Real.exp (-t * lam) ≤ m⁻¹ := by
  have : (fun t : ℝ => Real.exp (-t * lam)) = fun t => Real.exp (-lam * t) := by
    funext t; ring_nf
  rw [this, StieltjesLaplace.integral_exp_neg_mul_Ioi_zero (hm.trans_le hlam)]
  exact inv_anti₀ hm hlam

include hm in
theorem exp_kernel_le_one {t lam : ℝ} (ht : 0 ≤ t) (hlam : m ≤ lam) :
    Real.exp (-t * lam) ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith [hm.trans_le hlam])

include hm in
theorem integrableOn_weighted_kernel {lam : ℝ} (hlam : m ≤ lam) :
    IntegrableOn (fun t : ℝ => lam * Real.exp (-lam * t)) (Ioi 0) :=
  (StieltjesLaplace.integrable_exp_neg_mul_restrict_Ioi (hm.trans_le hlam)).const_mul lam

include hm in
theorem integral_weighted_kernel_le {lam : ℝ} (hlam : m ≤ lam) :
    ∫ t in Ioi 0, lam * Real.exp (-lam * t) ≤ 1 := by
  rw [MeasureTheory.integral_const_mul,
    StieltjesLaplace.integral_exp_neg_mul_Ioi_zero (hm.trans_le hlam),
    mul_inv_cancel₀ (hm.trans_le hlam).ne']

include hm in
theorem weighted_kernel_le {a t lam : ℝ} (ha : 0 < a) (hat : a ≤ t) (hlam : m ≤ lam) :
    lam * Real.exp (-lam * t) ≤ a⁻¹ := by
  have hl : 0 < lam := hm.trans_le hlam
  have h1 : Real.exp (-lam * t) ≤ Real.exp (-lam * a) := Real.exp_le_exp.2 (by nlinarith)
  have h2 : lam * a ≤ Real.exp (lam * a) := by linarith [Real.add_one_le_exp (lam * a)]
  calc lam * Real.exp (-lam * t) ≤ lam * Real.exp (-lam * a) :=
        mul_le_mul_of_nonneg_left h1 hl.le
    _ ≤ a⁻¹ := by
        rw [neg_mul, Real.exp_neg, ← one_div, ← one_div, mul_one_div,
          div_le_div_iff₀ (Real.exp_pos _) ha]
        linarith

include hm hφ hM in
/-- `∫_0^∞ φ(t) K_ρ(t) dt = ∫ (∫_0^∞ φ(t) e^{-tλ} dt) dρ(λ)`. -/
theorem integral_smul_euclideanMemoryKernel (ρ : PositiveTailMeasure H)
    (hρ : ρ.IsSupportedAbove m) :
    ∫ t in Ioi 0, φ t • Matrix.of.symm (ρ.euclideanMemoryKernel t) =
      VectorMeasure.integral ρ.toVectorMeasure
        (fun lam => ∫ t in Ioi 0, φ t * Real.exp (-t * lam)) (ContinuousLinearMap.lsmul ℝ ℝ) := by
  have h1 : ∀ t ∈ Ioi (0 : ℝ), φ t • Matrix.of.symm (ρ.euclideanMemoryKernel t) =
      φ t • VectorMeasure.integral ρ.toVectorMeasure (fun lam => Real.exp (-t * lam))
        (ContinuousLinearMap.lsmul ℝ ℝ) := by
    intro t ht
    rw [PositiveTailMeasure.euclideanMemoryKernel, Equiv.symm_apply_apply,
      ρ.integral_ofReal_lsmul (ρ.integrable_exp_neg_mul_variation (le_of_lt ht))]
  rw [setIntegral_congr_fun measurableSet_Ioi h1]
  refine ρ.integral_smul_integral_kernel hρ φ hφ hM (fun t lam => Real.exp (-t * lam))
    (by fun_prop) (fun t lam _ _ => (Real.exp_pos _).le) (fun lam hlam => integrableOn_exp_kernel hm hlam)
    (B := m⁻¹) (fun lam hlam => integral_exp_kernel_le hm hlam) fun a ha => ⟨1, fun t hat lam hlam =>
      exp_kernel_le_one hm (ha.le.trans hat) hlam⟩

include hm hφ hM in
/-- `∫_0^∞ φ(t) K_fin(t) dt = ∫ (∫_0^∞ φ(t) λ e^{-λt} dt) dν_fin(λ)`. -/
theorem integral_smul_weightedKernel (ρ : PositiveTailMeasure H) (hρ : ρ.IsSupportedAbove m) :
    ∫ t in Ioi 0, φ t • VectorMeasure.integral ρ.toVectorMeasure
        (fun lam => lam * Real.exp (-lam * t)) (ContinuousLinearMap.lsmul ℝ ℝ) =
      VectorMeasure.integral ρ.toVectorMeasure
        (fun lam => ∫ t in Ioi 0, φ t * (lam * Real.exp (-lam * t)))
        (ContinuousLinearMap.lsmul ℝ ℝ) :=
  ρ.integral_smul_integral_kernel hρ φ hφ hM (fun t lam => lam * Real.exp (-lam * t))
    (by fun_prop) (fun t lam _ hlam => mul_nonneg (hm.trans_le hlam).le (Real.exp_pos _).le)
    (fun lam hlam => integrableOn_weighted_kernel hm hlam) (B := 1)
    (fun lam hlam => integral_weighted_kernel_le hm hlam)
    fun a ha => ⟨a⁻¹, fun t hat lam hlam => weighted_kernel_le hm ha hat hlam⟩

include hm hφ hM in
/-- **`eq:supp-contact-kernel`**: along a subsequence whose escape measures converge weakly to `ν`,
`∫_0^∞ φ(t) K_n(t) dt → φ(0) Q_esc + ∫_0^∞ φ(t) K_fin(t) dt` with
`K_fin(t) = ∫ λ e^{-λt} dν_fin(λ)`, i.e. `K_n(t) dt → Q_esc δ_0 + K_fin(t) dt`. -/
theorem tendsto_integral_smul_euclideanMemoryKernel (μ : ℕ → PositiveTailMeasure H)
    (hμ : ∀ n, (μ n).IsSupportedAbove m) (ν : PosOperatorMeasure (EscapeSpace m) H)
    (hconv : ∀ g : EscapeSpace m →ᵇ ℝ, Tendsto (fun n => VectorMeasure.integral
      (((μ n).escapeMeasure hm (hμ n)).toVectorMeasure) g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) atTop
      (𝓝 (VectorMeasure.integral ν.toVectorMeasure g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))))) :
    Tendsto (fun n => ∫ t in Ioi 0, φ t • Matrix.of.symm ((μ n).euclideanMemoryKernel t)) atTop
      (𝓝 (φ 0 • ν.toVectorMeasure {escapeInfty m hm} +
        ∫ t in Ioi 0, φ t • VectorMeasure.integral (finitePart hm ν).toVectorMeasure
          (fun lam => lam * Real.exp (-lam * t)) (ContinuousLinearMap.lsmul ℝ ℝ))) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set G : EscapeSpace m →ᵇ ℝ := mkOfCompact ⟨escapeTest m φ, continuous_escapeTest φ hφ hM⟩
    with hG
  have hGapply : ∀ y, G y = escapeTest m φ y := fun y => rfl
  have hGmeas : Measurable (escapeTest m φ) := (continuous_escapeTest φ hφ hM).measurable
  have hGbound : ∀ y, ‖escapeTest m φ y‖ ≤ M := fun y => by
    rw [Real.norm_eq_abs]; exact abs_escapeTest_le φ hM y
  -- the `n`-th term
  have hA : ∀ n, ∫ t in Ioi 0, φ t • Matrix.of.symm ((μ n).euclideanMemoryKernel t) =
      VectorMeasure.integral ((μ n).escapeMeasure hm (hμ n)).toVectorMeasure G
        (ContinuousLinearMap.lsmul ℝ ℝ) := by
    intro n
    rw [integral_smul_euclideanMemoryKernel hm φ hφ hM (μ n) (hμ n)]
    change _ = VectorMeasure.integral ((μ n).escapeMeasure hm (hμ n)).toVectorMeasure
      (escapeTest m φ) (ContinuousLinearMap.lsmul ℝ ℝ)
    rw [(μ n).integral_escapeMeasure hm (hμ n) hGmeas hGbound]
    refine VectorMeasure.integral_congr_ae ?_
    filter_upwards [(μ n).ae_le_variation (hμ n)] with lam hlam
    have hl : lam ≠ 0 := (hm.trans_le hlam).ne'
    rw [escapeTest_escapeCoord hm φ hlam, ← MeasureTheory.integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have : -t * lam = -lam * t := by ring
    rw [this]
    field_simp
  -- the limit
  have hh : Measurable fun lam : ℝ => ∫ t in Ioi 0, φ t * (lam * Real.exp (-lam * t)) :=
    (((hφ.comp continuous_fst).mul ((continuous_snd).mul (Real.continuous_exp.comp
      ((continuous_snd.neg).mul continuous_fst)))).stronglyMeasurable.integral_prod_left').measurable
  have hhC : ∀ y : EscapeSpace m,
      ‖∫ t in Ioi 0, φ t * (escapeInv m y * Real.exp (-(escapeInv m y) * t))‖ ≤ M * 1 := by
    intro y
    by_cases hy : y = escapeInfty m hm
    · subst hy
      simp [escapeInv, escapeInfty, hM0]
    · rw [Real.norm_eq_abs]
      exact PositiveTailMeasure.abs_integral_mul_kernel_le (m := m) φ hφ hM (fun t lam => lam * Real.exp (-lam * t))
        (fun t lam _ hlam => mul_nonneg (hm.trans_le hlam).le (Real.exp_pos _).le)
        (fun lam hlam => integrableOn_weighted_kernel hm hlam) (B := 1)
        (fun lam hlam => integral_weighted_kernel_le hm hlam) (le_escapeInv hm hy)
  have hint : Integrable G ν.toVectorMeasure.variation :=
    Integrable.of_bound hGmeas.aestronglyMeasurable M (ae_of_all _ hGbound)
  have hD : VectorMeasure.integral ν.toVectorMeasure G (ContinuousLinearMap.lsmul ℝ ℝ) =
      φ 0 • ν.toVectorMeasure {escapeInfty m hm} +
        ∫ t in Ioi 0, φ t • VectorMeasure.integral (finitePart hm ν).toVectorMeasure
          (fun lam => lam * Real.exp (-lam * t)) (ContinuousLinearMap.lsmul ℝ ℝ) := by
    rw [integral_split_real hm ν hint, hGapply, escapeTest_infty hm φ,
      integral_smul_weightedKernel hm φ hφ hM (finitePart hm ν) (finitePart_isSupportedAbove hm ν),
      integral_finitePart_real hm ν hh hhC]
    congr 1
    exact VectorMeasure.setIntegral_congr_fun fun y hy => escapeTest_eq_of_ne hm φ hy
  rw [← hD]
  simp_rw [hA]
  exact hconv G

end Kernel

/-! ## The main theorem -/

/-- **`thm:supp-contact-escape` (High-energy memory escape and instantaneous contact terms).**
Let `μ n` be positive operator-valued tail measures supported in `[m, ∞)`, `m > 0`, with
`ν n = λ⁻¹ dμ n` and `Q n = ν n([m,∞)) = Σ_n(0)`, and suppose `sup_n Tr Q_n ≤ C`.  Then there are
a subsequence `φ` and a positive operator-valued measure `ν_∞` on the one-point compactification
`[m, ∞] ≅ [0, 1/m]` (`y = 1/λ`, `∞ ↦ 0`) such that

* `ν_{φ n} → ν_∞` weakly (against bounded continuous functions on the compactification);
* `ν_∞ = ν_fin + Q_esc δ_∞` with `Q_esc = ν_∞({∞}) ⪰ 0` and `ν_fin` (`finitePart`) the restriction
  of `ν_∞` to `[m, ∞)`, a positive tail measure supported in `[m, ∞)`;
* `Σ_{φ n}(z) → Q_esc + ∫_{[m,∞)} λ/(λ - z) dν_fin(λ)` locally uniformly on `ℂ ∖ [m, ∞)`
  (`eq:supp-contact-selfenergy`);
* for every bounded continuous test function `ψ` on `[0, ∞)`,
  `∫_0^∞ ψ(t) K_{φ n}(t) dt → ψ(0) Q_esc + ∫_0^∞ ψ(t) K_fin(t) dt` with
  `K_fin(t) = ∫ λ e^{-λt} dν_fin(λ)`, i.e. `K_n(t) dt → Q_esc δ_0 + K_fin(t) dt`
  (`eq:supp-contact-kernel`). -/
theorem contact_escape {m : ℝ} (hm : 0 < m) (μ : ℕ → PositiveTailMeasure H)
    (hμ : ∀ n, (μ n).IsSupportedAbove m) {C : ℝ}
    (hC : ∀ n, ((μ n).stieltjesSelfEnergy 0).trace.re ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νlim : PosOperatorMeasure (EscapeSpace m) H,
      (∀ g : EscapeSpace m →ᵇ ℝ, Tendsto (fun n => VectorMeasure.integral
        (((μ (φ n)).escapeMeasure hm (hμ (φ n))).toVectorMeasure) g
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) atTop
        (𝓝 (VectorMeasure.integral νlim.toVectorMeasure g
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))))) ∧
      (Matrix.of (νlim.toVectorMeasure {escapeInfty m hm})).PosSemidef ∧
      (finitePart hm νlim).IsSupportedAbove m ∧
      (∀ s : Set ℝ, MeasurableSet s → (finitePart hm νlim).toVectorMeasure s =
        νlim.toVectorMeasure (escapeInv m ⁻¹' s ∩ {escapeInfty m hm}ᶜ)) ∧
      TendstoLocallyUniformlyOn (fun n z => (μ (φ n)).stieltjesSelfEnergy z)
        (fun z => Matrix.of (νlim.toVectorMeasure {escapeInfty m hm}) +
          Matrix.of (VectorMeasure.integral (finitePart hm νlim).toVectorMeasure
            (fun lam : ℝ => (lam : ℂ) / ((lam : ℂ) - z)) (ContinuousLinearMap.lsmul ℝ ℂ)))
        atTop (escapeDomain m) ∧
      ∀ (ψ : ℝ → ℝ), Continuous ψ → ∀ M : ℝ, (∀ t, |ψ t| ≤ M) →
        Tendsto (fun n => ∫ t in Ioi 0, ψ t • Matrix.of.symm ((μ (φ n)).euclideanMemoryKernel t))
          atTop (𝓝 (ψ 0 • νlim.toVectorMeasure {escapeInfty m hm} +
            ∫ t in Ioi 0, ψ t • VectorMeasure.integral (finitePart hm νlim).toVectorMeasure
              (fun lam => lam * Real.exp (-lam * t)) (ContinuousLinearMap.lsmul ℝ ℝ))) := by
  have : Nonempty (EscapeSpace m) := ⟨escapeInfty m hm⟩
  have hC' : ∀ n, (Matrix.of (((μ n).escapeMeasure hm (hμ n)).toVectorMeasure univ)).trace.re ≤
      C := fun n => by rw [(μ n).escapeMeasure_univ hm (hμ n)]; exact hC n
  obtain ⟨φ, hφ, νlim, -, hint⟩ := exists_subseq_tendsto_posOperatorMeasure
    (fun n => (μ n).escapeMeasure hm (hμ n)) hC'
  refine ⟨φ, hφ, νlim, hint, νlim.posSemidef _ (measurableSet_singleton _),
    finitePart_isSupportedAbove hm νlim, fun s hs => finitePart_apply hm νlim hs, ?_, ?_⟩
  · exact tendstoLocallyUniformlyOn_stieltjesSelfEnergy hm (fun n => μ (φ n)) (fun n => hμ (φ n))
      (fun n => hC (φ n)) νlim hint
  · intro ψ hψ M hM
    exact tendsto_integral_smul_euclideanMemoryKernel hm ψ hψ hM (fun n => μ (φ n))
      (fun n => hμ (φ n)) νlim hint

end OperatorTailMeasure

end RenewalGeometry
