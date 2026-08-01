/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.MassPrefix

/-!
# Mass–flux inequality (`thm:mass-flux`, `thm:multiport-prefix`)

Stage A: the `L¹ ∩ L²` compatibility bridge for the vector-valued
`L²` Fourier transform (`MeasureTheory.Lp.fourierTransformₗᵢ`):
for `f` integrable and square-integrable whose pointwise Fourier
integral is square-integrable, the `L²` transform of `f` is the
pointwise transform.  Proved by testing against the dense Schwartz
range through the multiplication formula.
-/

open MeasureTheory FourierTransform SchwartzMap Complex Filter
  ComplexConjugate
open scoped ComplexInnerProductSpace InnerProductSpace

namespace NCG

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The multiplication formula: for integrable `f` and Schwartz `φ`,
`∫ ⟪f, 𝓕⁻φ⟫ = ∫ ⟪𝓕f, φ⟫`. -/
theorem integral_inner_fourierInv {f : ℝ → H} (hf1 : Integrable f)
    (φ : 𝓢(ℝ, H)) :
    (∫ s : ℝ, ⟪f s, (𝓕⁻ (⇑φ) : ℝ → H) s⟫)
      = ∫ ξ : ℝ, ⟪(𝓕 f) ξ, φ ξ⟫ := by
  -- expand the inverse transform inside the inner product
  have hIntφ : ∀ s : ℝ, Integrable fun ξ : ℝ =>
      (𝐞 (⟪ξ, s⟫_ℝ) : Circle) • (φ : ℝ → H) ξ := by
    intro s
    have h1 := (Real.fourierIntegral_convergent_iff (E := H)
      (f := (φ : ℝ → H)) (μ := volume) (-s)).mpr φ.integrable
    simpa [inner_neg_right] using h1
  have hexp : ∀ s : ℝ, ⟪f s, (𝓕⁻ (⇑φ) : ℝ → H) s⟫
      = ∫ ξ : ℝ, ⟪f s, (𝐞 (⟪ξ, s⟫_ℝ) : Circle) • (φ : ℝ → H) ξ⟫ := by
    intro s
    rw [Real.fourierInv_eq]
    exact ((innerSL ℂ (f s)).integral_comp_comm (hIntφ s)).symm
  simp only [hexp]
  -- swap the two integrals
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun s ξ : ℝ =>
        ⟪f s, (𝐞 (⟪ξ, s⟫_ℝ) : Circle) • (φ : ℝ → H) ξ⟫)
      (volume.prod volume) := by
    refine AEStronglyMeasurable.inner ?_ ?_
    · exact hf1.1.comp_quasiMeasurePreserving
        MeasureTheory.Measure.quasiMeasurePreserving_fst
    · refine Continuous.aestronglyMeasurable ?_
      refine Continuous.smul ?_ (φ.continuous.comp continuous_snd)
      exact continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp
          (continuous_inner.comp (continuous_snd.prodMk continuous_fst)))
  have hbound : Integrable
      (fun p : ℝ × ℝ => ‖f p.1‖ * ‖(φ : ℝ → H) p.2‖)
      (volume.prod volume) :=
    hf1.norm.mul_prod φ.integrable.norm
  have huncurry : Integrable
      (Function.uncurry fun s ξ : ℝ =>
        ⟪f s, (𝐞 (⟪ξ, s⟫_ℝ) : Circle) • (φ : ℝ → H) ξ⟫)
      (volume.prod volume) := by
    refine hbound.mono' hmeas ?_
    refine Eventually.of_forall fun p => ?_
    calc ‖⟪f p.1, (𝐞 (⟪p.2, p.1⟫_ℝ) : Circle) • (φ : ℝ → H) p.2⟫‖
        ≤ ‖f p.1‖ * ‖(𝐞 (⟪p.2, p.1⟫_ℝ) : Circle) • (φ : ℝ → H) p.2‖ :=
          norm_inner_le_norm _ _
      _ = ‖f p.1‖ * ‖(φ : ℝ → H) p.2‖ := by
          rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
  rw [MeasureTheory.integral_integral_swap huncurry]
  -- reassemble the forward transform per frequency
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only []
  have hIntf : Integrable fun v : ℝ =>
      (𝐞 (-⟪v, ξ⟫_ℝ) : Circle) • f v :=
    (Real.fourierIntegral_convergent_iff (E := H) (f := f)
      (μ := volume) ξ).mpr hf1
  have hswap2 : ⟪(φ : ℝ → H) ξ,
      ∫ v : ℝ, (𝐞 (-⟪v, ξ⟫_ℝ) : Circle) • f v⟫
        = ∫ v : ℝ, ⟪(φ : ℝ → H) ξ,
            (𝐞 (-⟪v, ξ⟫_ℝ) : Circle) • f v⟫ :=
    ((innerSL ℂ ((φ : ℝ → H) ξ)).integral_comp_comm hIntf).symm
  rw [Real.fourier_eq,
    show ⟪∫ v : ℝ, (𝐞 (-⟪v, ξ⟫_ℝ) : Circle) • f v, (φ : ℝ → H) ξ⟫
        = conj ⟪(φ : ℝ → H) ξ,
            ∫ v : ℝ, (𝐞 (-⟪v, ξ⟫_ℝ) : Circle) • f v⟫ from
      (inner_conj_symm _ _).symm,
    hswap2, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only []
  rw [inner_conj_symm, Circle.smul_def, Circle.smul_def,
    inner_smul_left, inner_smul_right]
  congr 1
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj,
    Complex.conj_conj, real_inner_comm]

set_option maxHeartbeats 1000000 in
-- defeq checks through the `L²` Fourier isometry extension are slow
/-- Stage-A bridge: the `L²` Fourier transform of an integrable,
square-integrable function whose pointwise transform is
square-integrable is that pointwise transform. -/
theorem fourier_toLp_eq {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume) (hg2 : MemLp (𝓕 f) 2 volume) :
    𝓕 (hf2.toLp f) = hg2.toLp (𝓕 f) := by
  -- test against the dense Schwartz range
  have htest : ∀ φ : 𝓢(ℝ, H),
      ⟪𝓕 (hf2.toLp f) - hg2.toLp (𝓕 f), φ.toLp 2 volume⟫ = (0 : ℂ) := by
    intro φ
    rw [inner_sub_left, sub_eq_zero]
    have h1 : φ.toLp 2 volume = 𝓕 ((𝓕⁻ φ).toLp 2 volume) := by
      rw [SchwartzMap.toLp_fourier_eq,
        FourierTransform.fourier_fourierInv_eq]
    calc ⟪𝓕 (hf2.toLp f), φ.toLp 2 volume⟫
        = ⟪𝓕 (hf2.toLp f), 𝓕 ((𝓕⁻ φ).toLp 2 volume)⟫ := by
          rw [← h1]
      _ = ⟪hf2.toLp f, (𝓕⁻ φ).toLp 2 volume⟫ :=
          MeasureTheory.Lp.inner_fourier_eq _ _
      _ = ∫ s : ℝ, ⟪f s, (𝓕⁻ (⇑φ) : ℝ → H) s⟫ := by
          rw [MeasureTheory.L2.inner_def]
          refine integral_congr_ae ?_
          filter_upwards [hf2.coeFn_toLp,
            SchwartzMap.coeFn_toLp (𝓕⁻ φ) 2 volume] with s h1' h2'
          rw [h1', h2', SchwartzMap.fourierInv_coe]
      _ = ∫ ξ : ℝ, ⟪(𝓕 f) ξ, (φ : ℝ → H) ξ⟫ :=
          integral_inner_fourierInv hf1 φ
      _ = ⟪hg2.toLp (𝓕 f), φ.toLp 2 volume⟫ := by
          rw [MeasureTheory.L2.inner_def]
          refine integral_congr_ae ?_
          filter_upwards [hg2.coeFn_toLp,
            SchwartzMap.coeFn_toLp φ 2 volume] with ξ h1' h2'
          rw [h1', h2']
  -- density: the difference is orthogonal to a dense range
  have hdense := SchwartzMap.denseRange_toLpCLM
    (F := H) (E := ℝ) (p := 2) (μ := volume) ENNReal.ofNat_ne_top
  set w : Lp (α := ℝ) H 2 := 𝓕 (hf2.toLp f) - hg2.toLp (𝓕 f) with hw
  have hzero : ∀ y : Lp (α := ℝ) H 2, ⟪w, y⟫ = (0 : ℂ) := by
    intro y
    have hcont1 : Continuous fun y : Lp (α := ℝ) H 2 => ⟪w, y⟫ :=
      continuous_const.inner continuous_id
    have heq : Set.EqOn (fun y : Lp (α := ℝ) H 2 => ⟪w, y⟫)
        (fun _ => (0 : ℂ))
        (Set.range (SchwartzMap.toLpCLM ℝ (E := ℝ) H 2 volume)) := by
      rintro _ ⟨φ, rfl⟩
      exact htest φ
    have := hcont1.ext_on hdense continuous_const heq
    exact congrFun this y
  have hwzero : w = 0 := by
    have := hzero w
    rwa [inner_self_eq_zero] at this
  have := sub_eq_zero.mp (hw ▸ hwzero)
  exact this

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- `L²` membership from a bounded, `1/|ξ|`-decaying majorant. -/
theorem memLp_two_of_le_min {g : ℝ → H}
    (hm : AEStronglyMeasurable g volume) {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hb : ∀ ξ : ℝ, ξ ≠ 0 → ‖g ξ‖ ≤ min C₁ (C₂ / |ξ|)) :
    MemLp g 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm hm]
  have hD : Integrable fun ξ : ℝ => (C₁ ^ 2 + C₂ ^ 2) * (1 + ξ ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq).const_mul _
  refine hD.mono' ?_ ?_
  · exact (hm.norm.pow 2)
  · have hae : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
      exact measure_singleton 0
    filter_upwards [hae] with ξ hξ
    have h1 : ‖g ξ‖ ≤ C₁ := (hb ξ hξ).trans (min_le_left _ _)
    have h2 : ‖g ξ‖ ≤ C₂ / |ξ| := (hb ξ hξ).trans (min_le_right _ _)
    have hξ0 : 0 < |ξ| := abs_pos.mpr hξ
    have h3 : ‖g ξ‖ * |ξ| ≤ C₂ := by
      rw [div_eq_mul_inv] at h2
      calc ‖g ξ‖ * |ξ| ≤ C₂ * |ξ|⁻¹ * |ξ| :=
            mul_le_mul_of_nonneg_right h2 hξ0.le
        _ = C₂ := by field_simp
    rw [Real.norm_of_nonneg (by positivity),
      le_mul_inv_iff₀ (by positivity)]
    have h4 : ‖g ξ‖ ^ 2 * ξ ^ 2 ≤ C₂ ^ 2 := by
      have h5 : (‖g ξ‖ * |ξ|) ^ 2 ≤ C₂ ^ 2 := by
        have h0 : (0 : ℝ) ≤ ‖g ξ‖ * |ξ| := by positivity
        nlinarith
      calc ‖g ξ‖ ^ 2 * ξ ^ 2 = (‖g ξ‖ * |ξ|) ^ 2 := by
            rw [mul_pow, sq_abs]
        _ ≤ C₂ ^ 2 := h5
    have h6 : ‖g ξ‖ ^ 2 ≤ C₁ ^ 2 := by
      nlinarith [norm_nonneg (g ξ)]
    nlinarith

omit [CompleteSpace H] in
/-- The `L²` norm of `toLp` as an integral of squared norms. -/
theorem norm_toLp_sq {g : ℝ → H} (hg : MemLp g 2 volume) :
    ‖hg.toLp g‖ ^ 2 = ∫ ξ : ℝ, ‖g ξ‖ ^ 2 := by
  have h1 : RCLike.re ⟪hg.toLp g, hg.toLp g⟫ = ‖hg.toLp g‖ ^ 2 :=
    inner_self_eq_norm_sq _
  rw [← h1, MeasureTheory.L2.inner_def]
  have hInt : Integrable
      (fun ξ : ℝ => ⟪(hg.toLp g : ℝ → H) ξ, (hg.toLp g : ℝ → H) ξ⟫)
      volume := MeasureTheory.L2.integrable_inner _ _
  rw [← integral_re hInt]
  have hcongr : ∀ᵐ ξ : ℝ ∂volume,
      RCLike.re ⟪(hg.toLp g : ℝ → H) ξ, (hg.toLp g : ℝ → H) ξ⟫
        = ‖g ξ‖ ^ 2 := by
    filter_upwards [hg.coeFn_toLp] with ξ hξ
    rw [hξ]
    exact inner_self_eq_norm_sq _
  exact integral_congr_ae hcongr

section MassFlux

variable (d : ℕ → H) (sc : ℕ → ℝ) (N : ℕ) (F : ℝ → ℂ)

/-- The port synthesis `𝒞_F(d)(u) = Σ_c F(u + s_c) d_c` — the
tensor packet `Σ_c d_c ⊗ T_{s_c}F` realized in `L²(ℝ, H)`. -/
noncomputable def portSynthesis (u : ℝ) : H :=
  ∑ c ∈ Finset.range (N + 1), F (u + sc c) • d c

/-- The frequency packet `G(ξ) = Σ_c e^{2πiξs_c} d_c`. -/
noncomputable def freqPacket (ξ : ℝ) : H :=
  ∑ c ∈ Finset.range (N + 1),
    Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (sc c : ℂ)
      * Complex.I) • d c

/-- Fourier transform of a translated, vector-scaled port. -/
theorem fourier_translate_smul (_hF1 : Integrable F) (a : ℝ) (v : H)
    (ξ : ℝ) :
    𝓕 (fun u : ℝ => F (u + a) • v) ξ
      = (Complex.exp ((2 * Real.pi * ξ * a : ℝ) * Complex.I)
          * 𝓕 F ξ) • v := by
  rw [Real.fourier_eq']
  have hpt : ∀ u : ℝ,
      Complex.exp ((-2 * Real.pi * ⟪u, ξ⟫_ℝ : ℝ) * Complex.I)
          • (F (u + a) • v)
        = (Complex.exp ((-2 * Real.pi * (u * ξ) : ℝ) * Complex.I)
            * F (u + a)) • v := by
    intro u
    rw [smul_smul, show ⟪u, ξ⟫_ℝ = u * ξ from by
      rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring]
  simp only [hpt]
  rw [integral_smul_const]
  congr 1
  -- shift the integration variable
  have hshift : (∫ u : ℝ,
      Complex.exp ((-2 * Real.pi * (u * ξ) : ℝ) * Complex.I)
        * F (u + a))
      = ∫ v' : ℝ,
        Complex.exp ((-2 * Real.pi * ((v' - a) * ξ) : ℝ) * Complex.I)
          * F v' := by
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun v' : ℝ =>
        Complex.exp ((-2 * Real.pi * ((v' - a) * ξ) : ℝ) * Complex.I)
          * F v') a]
    simp only [add_sub_cancel_right]
  rw [hshift, Real.fourier_eq']
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v' => ?_)
  simp only []
  rw [smul_eq_mul,
    show ⟪v', ξ⟫_ℝ = v' * ξ from by
      rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring,
    show Complex.exp (((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)
          * (Complex.exp (((-2 * Real.pi * (v' * ξ) : ℝ) : ℂ)
              * Complex.I) * F v')
        = Complex.exp (((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I
            + ((-2 * Real.pi * (v' * ξ) : ℝ) : ℂ) * Complex.I)
            * F v' from by
      rw [Complex.exp_add]
      ring]
  congr 1
  congr 1
  push_cast
  ring

variable {d sc N F}

omit [CompleteSpace H] in
/-- Translates of an integrable port are integrable. -/
theorem integrable_translate_smul (hF1 : Integrable F) (a : ℝ)
    (v : H) : Integrable fun u : ℝ => F (u + a) • v := by
  have h1 : Integrable (F ∘ (· + a)) volume :=
    ((measurePreserving_add_right volume a).integrable_comp
      hF1.1).mpr hF1
  exact h1.smul_const v

omit [CompleteSpace H] in
/-- The port synthesis is integrable. -/
theorem integrable_portSynthesis (hF1 : Integrable F) :
    Integrable (portSynthesis d sc N F) volume := by
  refine integrable_finsetSum _ fun c _ => ?_
  exact integrable_translate_smul hF1 (sc c) (d c)

omit [CompleteSpace H] in
/-- The port synthesis is square-integrable. -/
theorem memLp_portSynthesis (hF2 : MemLp F 2 volume) :
    MemLp (portSynthesis d sc N F) 2 volume := by
  refine memLp_finsetSum _ fun c _ => ?_
  have h1 : MemLp (F ∘ (· + sc c)) 2 volume :=
    hF2.comp_measurePreserving (measurePreserving_add_right volume _)
  have h2 : MemLp (fun u : ℝ => ‖d c‖ * ‖F (u + sc c)‖) 2 volume :=
    h1.norm.const_mul _
  refine MemLp.of_le h2 (h1.1.smul aestronglyMeasurable_const) ?_
  refine Eventually.of_forall fun u => ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_comm]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The step prefix field is integrable. -/
theorem integrable_stepPrefix :
    Integrable (stepPrefix d sc N) volume := by
  refine integrable_finsetSum _ fun c _ => ?_
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Ico
  exact (continuous_const.integrableOn_Icc).mono_set
    Set.Ico_subset_Icc_self

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The step prefix field is square-integrable. -/
theorem memLp_stepPrefix : MemLp (stepPrefix d sc N) 2 volume := by
  refine memLp_finsetSum _ fun c _ => ?_
  exact memLp_indicator_const 2 measurableSet_Ico _
    (Or.inr measure_Ico_lt_top.ne)

/-- The Fourier transform of the port synthesis factors through the
frequency packet. -/
theorem fourier_portSynthesis (hF1 : Integrable F) (ξ : ℝ) :
    𝓕 (portSynthesis d sc N F) ξ = 𝓕 F ξ • freqPacket d sc N ξ := by
  have hsum : 𝓕 (portSynthesis d sc N F) ξ
      = ∑ c ∈ Finset.range (N + 1),
          𝓕 (fun u : ℝ => F (u + sc c) • d c) ξ := by
    simp only [Real.fourier_eq, portSynthesis, Finset.smul_sum]
    exact MeasureTheory.integral_finsetSum _ fun c _ =>
      (Real.fourierIntegral_convergent_iff (μ := volume) ξ).mpr
        (integrable_translate_smul hF1 (sc c) (d c))
  rw [hsum,
    Finset.sum_congr rfl fun c _ =>
      fourier_translate_smul F hF1 (sc c) (d c) ξ,
    freqPacket, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_smul]
  congr 1
  rw [mul_comm]
  congr 1
  push_cast
  ring

omit [CompleteSpace H] in
/-- The pointwise Fourier transform of the step prefix in
boundary-compatible form. -/
theorem fourier_stepPrefix_eq (ξ : ℝ) :
    (∫ u : ℝ, Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (u : ℂ)
        * Complex.I) • stepPrefix d sc N u)
      = 𝓕 (stepPrefix d sc N) (-ξ) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only []
  congr 1
  congr 1
  rw [show ⟪u, -ξ⟫_ℝ = u * -ξ from by
    rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring]
  push_cast
  ring

/-- Norm bound: the transform of the step prefix decays like
`1/|ξ|` through the boundary identity. -/
theorem norm_fourier_stepPrefix_le (hs : Monotone sc) (ξ : ℝ)
    (hξ : ξ ≠ 0) :
    ‖𝓕 (stepPrefix d sc N) (-ξ)‖
      ≤ (‖totalMass d N‖
          + ∑ c ∈ Finset.range (N + 1), ‖d c‖) / (2 * Real.pi * |ξ|) := by
  have hfb := fourier_boundary d sc N hs (2 * Real.pi * ξ)
  rw [fourier_stepPrefix_eq] at hfb
  -- isolate the transform term
  have hkey : (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ))
      • 𝓕 (stepPrefix d sc N) (-ξ)
      = Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (sc N : ℂ)
          * Complex.I) • totalMass d N
        - ∑ c ∈ Finset.range (N + 1),
            Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (sc c : ℂ)
              * Complex.I) • d c := by
    rw [eq_sub_iff_add_eq] at hfb
    refine eq_sub_of_add_eq ?_
    rw [add_comm]
    exact hfb
  have hnorm1 : ‖(Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ))
      • 𝓕 (stepPrefix d sc N) (-ξ)‖
      = (2 * Real.pi * |ξ|) * ‖𝓕 (stepPrefix d sc N) (-ξ)‖ := by
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real]
    congr 1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity :
      (0 : ℝ) < 2 * Real.pi)]
  have hnorm2 : ‖Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ)
        * (sc N : ℂ) * Complex.I) • totalMass d N
      - ∑ c ∈ Finset.range (N + 1),
          Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (sc c : ℂ)
            * Complex.I) • d c‖
      ≤ ‖totalMass d N‖ + ∑ c ∈ Finset.range (N + 1), ‖d c‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ)
        * (sc N : ℂ) * Complex.I) • totalMass d N‖
        = ‖totalMass d N‖ := by
      rw [norm_smul, Complex.norm_exp]
      simp
    have h2 : ‖∑ c ∈ Finset.range (N + 1),
        Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (sc c : ℂ)
          * Complex.I) • d c‖
        ≤ ∑ c ∈ Finset.range (N + 1), ‖d c‖ := by
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun c _ => ?_
      rw [norm_smul, Complex.norm_exp]
      simp
    linarith
  have hpos : (0 : ℝ) < 2 * Real.pi * |ξ| := by
    have := abs_pos.mpr hξ
    positivity
  rw [le_div_iff₀ hpos, mul_comm]
  calc (2 * Real.pi * |ξ|) * ‖𝓕 (stepPrefix d sc N) (-ξ)‖
      = ‖(Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ))
          • 𝓕 (stepPrefix d sc N) (-ξ)‖ := hnorm1.symm
    _ ≤ ‖totalMass d N‖ + ∑ c ∈ Finset.range (N + 1), ‖d c‖ := by
        rw [hkey]
        exact hnorm2

/-- The transform is bounded by the `L¹` norm. -/
theorem norm_fourier_le_integral_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (g : ℝ → E) (ξ : ℝ) :
    ‖𝓕 g ξ‖ ≤ ∫ u : ℝ, ‖g u‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only []
  rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

set_option maxHeartbeats 1000000 in
-- elaboration through the `L²` Fourier isometry is slow
/-- `thm:mass-flux` (part 1): if `Λ = sup (2πξ)²|𝓕F(ξ)|² < ∞`, then
`‖𝒞_F(d)‖ ≤ ‖F‖·‖M(d)‖ + √Λ·‖J_d‖`, all norms in `L²`.  (In the
manuscript's unitary convention `√Λ = √(2πΛ_F)`.) -/
theorem mass_flux (hs : Monotone sc) (hF1 : Integrable F)
    (hF2 : MemLp F 2 volume) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖𝓕 F ξ‖ ^ 2 ≤ Λ) :
    ‖(memLp_portSynthesis (d := d) (sc := sc) (N := N)
        hF2).toLp (portSynthesis d sc N F)‖
      ≤ ‖hF2.toLp F‖ * ‖totalMass d N‖
        + Real.sqrt Λ
          * ‖(memLp_stepPrefix (d := d) (sc := sc)
              (N := N)).toLp (stepPrefix d sc N)‖ := by
  classical
  -- the pointwise `√Λ` bound on the weighted transform
  have hsqrt : ∀ ξ : ℝ, (2 * Real.pi * |ξ|) * ‖𝓕 F ξ‖
      ≤ Real.sqrt Λ := by
    intro ξ
    have h2 : ((2 * Real.pi * |ξ|) * ‖𝓕 F ξ‖) ^ 2 ≤ Λ := by
      calc ((2 * Real.pi * |ξ|) * ‖𝓕 F ξ‖) ^ 2
          = (2 * Real.pi * |ξ|) ^ 2 * ‖𝓕 F ξ‖ ^ 2 := mul_pow _ _ _
        _ = (2 * Real.pi * ξ) ^ 2 * ‖𝓕 F ξ‖ ^ 2 := by
            congr 1
            rw [mul_pow, sq_abs, ← mul_pow]
        _ ≤ Λ := hΛ ξ
    have h3 : (0 : ℝ) ≤ (2 * Real.pi * |ξ|) * ‖𝓕 F ξ‖ := by positivity
    exact (Real.le_sqrt h3 hΛ0).mpr h2
  -- continuity and `L¹`-bounds for the transforms
  have hcontF : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hF1
  have hJ1 : Integrable (stepPrefix d sc N) volume :=
    integrable_stepPrefix
  have hcontJ : Continuous (𝓕 (stepPrefix d sc N)) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hJ1
  have h𝒞1 : Integrable (portSynthesis d sc N F) volume :=
    integrable_portSynthesis hF1
  have hcont𝒞 : Continuous (𝓕 (portSynthesis d sc N F)) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) h𝒞1
  -- `L²` membership of `𝓕F`
  have h𝓕F2 : MemLp (𝓕 F) 2 volume := by
    refine memLp_two_of_le_min hcontF.aestronglyMeasurable
      (C₁ := ∫ u : ℝ, ‖F u‖) (C₂ := Real.sqrt Λ / (2 * Real.pi))
      (integral_nonneg fun u => norm_nonneg _) (by positivity) ?_
    intro ξ hξ
    refine le_min (norm_fourier_le_integral_norm F ξ) ?_
    have habs : 0 < |ξ| := abs_pos.mpr hξ
    rw [div_div, le_div_iff₀ (by positivity)]
    rw [mul_comm]
    exact hsqrt ξ
  -- `L²` membership of `𝓕J` through the boundary decay
  have hD0 : (0 : ℝ) ≤ ‖totalMass d N‖
      + ∑ c ∈ Finset.range (N + 1), ‖d c‖ := by
    have := Finset.sum_nonneg
      (fun c (_ : c ∈ Finset.range (N + 1)) => norm_nonneg (d c))
    positivity
  have h𝓕J2 : MemLp (𝓕 (stepPrefix d sc N)) 2 volume := by
    refine memLp_two_of_le_min hcontJ.aestronglyMeasurable
      (C₁ := ∫ u : ℝ, ‖stepPrefix d sc N u‖)
      (C₂ := (‖totalMass d N‖
        + ∑ c ∈ Finset.range (N + 1), ‖d c‖) / (2 * Real.pi))
      (integral_nonneg fun u => norm_nonneg _) (by positivity) ?_
    intro ξ hξ
    refine le_min (norm_fourier_le_integral_norm _ ξ) ?_
    have h1 := norm_fourier_stepPrefix_le (d := d) (N := N) hs (-ξ)
      (neg_ne_zero.mpr hξ)
    rw [neg_neg, abs_neg] at h1
    rwa [div_div]
  -- `L²` membership of `𝓕𝒞`
  have hGle : ∀ ξ : ℝ, ‖freqPacket d sc N ξ‖
      ≤ ∑ c ∈ Finset.range (N + 1), ‖d c‖ := by
    intro ξ
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun c _ => ?_
    rw [norm_smul, Complex.norm_exp]
    simp
  have h𝓕𝒞2 : MemLp (𝓕 (portSynthesis d sc N F)) 2 volume := by
    have h2 : MemLp (fun ξ : ℝ =>
        (∑ c ∈ Finset.range (N + 1), ‖d c‖) * ‖𝓕 F ξ‖) 2 volume :=
      h𝓕F2.norm.const_mul _
    refine MemLp.of_le h2 hcont𝒞.aestronglyMeasurable ?_
    refine Eventually.of_forall fun ξ => ?_
    rw [fourier_portSynthesis hF1, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    calc ‖𝓕 F ξ‖ * ‖freqPacket d sc N ξ‖
        ≤ ‖𝓕 F ξ‖ * ∑ c ∈ Finset.range (N + 1), ‖d c‖ :=
          mul_le_mul_of_nonneg_left (hGle ξ) (norm_nonneg _)
      _ = (∑ c ∈ Finset.range (N + 1), ‖d c‖) * ‖𝓕 F ξ‖ :=
          mul_comm _ _
  -- the boundary split `𝓕𝒞 = A + B`
  set A : ℝ → H := fun ξ =>
    (𝓕 F ξ * Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (sc N : ℂ)
      * Complex.I)) • totalMass d N with hAdef
  set B : ℝ → H := fun ξ =>
    -(((Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * 𝓕 F ξ)
      • 𝓕 (stepPrefix d sc N) (-ξ)) with hBdef
  have hsplit : ∀ ξ : ℝ,
      𝓕 (portSynthesis d sc N F) ξ = A ξ + B ξ := by
    intro ξ
    rw [fourier_portSynthesis hF1]
    have hfb := fourier_boundary d sc N hs (2 * Real.pi * ξ)
    rw [fourier_stepPrefix_eq] at hfb
    have hG : freqPacket d sc N ξ
        = Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (sc N : ℂ)
            * Complex.I) • totalMass d N
          - (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ))
            • 𝓕 (stepPrefix d sc N) (-ξ) := hfb
    rw [hG]
    simp only [hAdef, hBdef]
    module
  -- membership of the two pieces
  have hphase : ∀ ξ : ℝ,
      ‖Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (sc N : ℂ)
        * Complex.I)‖ = 1 := by
    intro ξ
    rw [Complex.norm_exp]
    simp
  have hA2 : MemLp A 2 volume := by
    have h2 : MemLp (fun ξ : ℝ => ‖totalMass d N‖ * ‖𝓕 F ξ‖)
        2 volume := h𝓕F2.norm.const_mul _
    refine MemLp.of_le h2 ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine Continuous.smul (hcontF.mul ?_) continuous_const
      fun_prop
    · refine Eventually.of_forall fun ξ => ?_
      rw [hAdef]
      simp only []
      rw [norm_smul, norm_mul, hphase ξ, mul_one,
        Real.norm_of_nonneg (by positivity), mul_comm]
  have hBneg2 : MemLp (fun ξ : ℝ => 𝓕 (stepPrefix d sc N) (-ξ))
      2 volume :=
    h𝓕J2.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hB2 : MemLp B 2 volume := by
    have h2 : MemLp (fun ξ : ℝ =>
        Real.sqrt Λ * ‖𝓕 (stepPrefix d sc N) (-ξ)‖) 2 volume :=
      hBneg2.norm.const_mul _
    refine MemLp.of_le h2 ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine Continuous.neg ?_
      refine Continuous.smul ?_ (hcontJ.comp continuous_neg)
      fun_prop
    · refine Eventually.of_forall fun ξ => ?_
      rw [hBdef]
      simp only []
      rw [norm_neg, norm_smul, norm_mul, norm_mul, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact hsqrt ξ
  -- Plancherel + split at the `Lp` level
  have hkey1 : ‖(memLp_portSynthesis (d := d) (sc := sc) (N := N)
      hF2).toLp (portSynthesis d sc N F)‖
      = ‖h𝓕𝒞2.toLp (𝓕 (portSynthesis d sc N F))‖ := by
    rw [← fourier_toLp_eq h𝒞1 (memLp_portSynthesis hF2) h𝓕𝒞2,
      MeasureTheory.Lp.norm_fourier_eq]
  have hkey2 : h𝓕𝒞2.toLp (𝓕 (portSynthesis d sc N F))
      = hA2.toLp A + hB2.toLp B := by
    rw [← MeasureTheory.MemLp.toLp_add hA2 hB2]
    exact MeasureTheory.MemLp.toLp_congr _ _
      (Eventually.of_forall hsplit)
  -- the exact `A`-norm
  have hPF : ‖h𝓕F2.toLp (𝓕 F)‖ = ‖hF2.toLp F‖ := by
    rw [← fourier_toLp_eq hF1 hF2 h𝓕F2,
      MeasureTheory.Lp.norm_fourier_eq]
  have hnormA : ‖hA2.toLp A‖ = ‖hF2.toLp F‖ * ‖totalMass d N‖ := by
    have h1 : ‖hA2.toLp A‖ ^ 2
        = ‖hF2.toLp F‖ ^ 2 * ‖totalMass d N‖ ^ 2 := by
      rw [norm_toLp_sq]
      have hpt : ∀ ξ : ℝ, ‖A ξ‖ ^ 2
          = ‖totalMass d N‖ ^ 2 * ‖𝓕 F ξ‖ ^ 2 := by
        intro ξ
        rw [hAdef]
        simp only []
        rw [norm_smul, norm_mul, hphase ξ, mul_one, mul_pow]
        ring
      rw [integral_congr_ae (Eventually.of_forall hpt),
        MeasureTheory.integral_const_mul, ← norm_toLp_sq h𝓕F2, hPF]
      ring
    have h2 : (0 : ℝ) ≤ ‖hF2.toLp F‖ * ‖totalMass d N‖ := by
      positivity
    calc ‖hA2.toLp A‖
        = Real.sqrt (‖hA2.toLp A‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt ((‖hF2.toLp F‖ * ‖totalMass d N‖) ^ 2) := by
          rw [h1, mul_pow]
      _ = ‖hF2.toLp F‖ * ‖totalMass d N‖ := Real.sqrt_sq h2
  -- the `B`-norm bound
  have hPJ : (∫ ξ : ℝ, ‖𝓕 (stepPrefix d sc N) ξ‖ ^ 2)
      = ∫ u : ℝ, ‖stepPrefix d sc N u‖ ^ 2 := by
    rw [← norm_toLp_sq h𝓕J2,
      ← norm_toLp_sq (memLp_stepPrefix (d := d) (sc := sc) (N := N)),
      ← fourier_toLp_eq hJ1 memLp_stepPrefix h𝓕J2,
      MeasureTheory.Lp.norm_fourier_eq]
  have hnormB : ‖hB2.toLp B‖
      ≤ Real.sqrt Λ
        * ‖(memLp_stepPrefix (d := d) (sc := sc)
            (N := N)).toLp (stepPrefix d sc N)‖ := by
    have h1 : ‖hB2.toLp B‖ ^ 2
        ≤ Λ * ‖(memLp_stepPrefix (d := d) (sc := sc)
            (N := N)).toLp (stepPrefix d sc N)‖ ^ 2 := by
      rw [norm_toLp_sq, norm_toLp_sq]
      have hrefl : (∫ ξ : ℝ, ‖𝓕 (stepPrefix d sc N) (-ξ)‖ ^ 2)
          = ∫ ξ : ℝ, ‖𝓕 (stepPrefix d sc N) ξ‖ ^ 2 :=
        integral_neg_eq_self
          (fun ξ => ‖𝓕 (stepPrefix d sc N) ξ‖ ^ 2) volume
      calc (∫ ξ : ℝ, ‖B ξ‖ ^ 2)
          ≤ ∫ ξ : ℝ, Λ * ‖𝓕 (stepPrefix d sc N) (-ξ)‖ ^ 2 := by
            refine integral_mono_ae
              ((memLp_two_iff_integrable_sq_norm hB2.1).mp hB2)
              (((memLp_two_iff_integrable_sq_norm
                hBneg2.1).mp hBneg2).const_mul Λ) ?_
            refine Eventually.of_forall fun ξ => ?_
            rw [hBdef]
            simp only []
            rw [norm_neg, norm_smul, norm_mul, norm_mul,
              Complex.norm_I, one_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_mul,
              abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
              mul_pow]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have h3 := hsqrt ξ
            have h4 : ((2 * Real.pi * |ξ|) * ‖𝓕 F ξ‖) ^ 2
                ≤ Real.sqrt Λ ^ 2 := by
              refine pow_le_pow_left₀ (by positivity) h3 2
            rwa [Real.sq_sqrt hΛ0] at h4
          _ = Λ * ∫ ξ : ℝ, ‖𝓕 (stepPrefix d sc N) (-ξ)‖ ^ 2 :=
            MeasureTheory.integral_const_mul _ _
          _ = Λ * ∫ u : ℝ, ‖stepPrefix d sc N u‖ ^ 2 := by
            rw [hrefl, hPJ]
    have h2 : (0 : ℝ) ≤ Real.sqrt Λ
        * ‖(memLp_stepPrefix (d := d) (sc := sc)
            (N := N)).toLp (stepPrefix d sc N)‖ := by positivity
    calc ‖hB2.toLp B‖
        = Real.sqrt (‖hB2.toLp B‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (Λ * ‖(memLp_stepPrefix (d := d) (sc := sc)
            (N := N)).toLp (stepPrefix d sc N)‖ ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt Λ
          * ‖(memLp_stepPrefix (d := d) (sc := sc)
              (N := N)).toLp (stepPrefix d sc N)‖ := by
          rw [Real.sqrt_mul hΛ0, Real.sqrt_sq (norm_nonneg _)]
  calc ‖(memLp_portSynthesis (d := d) (sc := sc) (N := N)
      hF2).toLp (portSynthesis d sc N F)‖
      = ‖hA2.toLp A + hB2.toLp B‖ := by rw [hkey1, hkey2]
    _ ≤ ‖hA2.toLp A‖ + ‖hB2.toLp B‖ := norm_add_le _ _
    _ ≤ ‖hF2.toLp F‖ * ‖totalMass d N‖
        + Real.sqrt Λ
          * ‖(memLp_stepPrefix (d := d) (sc := sc)
              (N := N)).toLp (stepPrefix d sc N)‖ :=
        add_le_add (le_of_eq hnormA) hnormB

set_option maxHeartbeats 1000000 in
-- elaboration through the `L²` Fourier isometry is slow
/-- `thm:mass-flux` (part 2): when the total mass vanishes, the
port energy is exactly the flux integral
`‖𝒞_F(d)‖² = ∫ (2πξ)²|𝓕F(ξ)|²‖𝓕J(−ξ)‖² dξ`. -/
theorem mass_flux_zero (hs : Monotone sc) (hF1 : Integrable F)
    (hF2 : MemLp F 2 volume) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖𝓕 F ξ‖ ^ 2 ≤ Λ)
    (hM : totalMass d N = 0) :
    ‖(memLp_portSynthesis (d := d) (sc := sc) (N := N)
        hF2).toLp (portSynthesis d sc N F)‖ ^ 2
      = ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖𝓕 F ξ‖ ^ 2
          * ‖𝓕 (stepPrefix d sc N) (-ξ)‖ ^ 2 := by
  classical
  have hsqrt : ∀ ξ : ℝ, (2 * Real.pi * |ξ|) * ‖𝓕 F ξ‖
      ≤ Real.sqrt Λ := by
    intro ξ
    have h2 : ((2 * Real.pi * |ξ|) * ‖𝓕 F ξ‖) ^ 2 ≤ Λ := by
      calc ((2 * Real.pi * |ξ|) * ‖𝓕 F ξ‖) ^ 2
          = (2 * Real.pi * |ξ|) ^ 2 * ‖𝓕 F ξ‖ ^ 2 := mul_pow _ _ _
        _ = (2 * Real.pi * ξ) ^ 2 * ‖𝓕 F ξ‖ ^ 2 := by
            congr 1
            rw [mul_pow, sq_abs, ← mul_pow]
        _ ≤ Λ := hΛ ξ
    have h3 : (0 : ℝ) ≤ (2 * Real.pi * |ξ|) * ‖𝓕 F ξ‖ := by positivity
    exact (Real.le_sqrt h3 hΛ0).mpr h2
  have hcontF : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hF1
  have hJ1 : Integrable (stepPrefix d sc N) volume :=
    integrable_stepPrefix
  have hcontJ : Continuous (𝓕 (stepPrefix d sc N)) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hJ1
  have h𝒞1 : Integrable (portSynthesis d sc N F) volume :=
    integrable_portSynthesis hF1
  have hcont𝒞 : Continuous (𝓕 (portSynthesis d sc N F)) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) h𝒞1
  have h𝓕F2 : MemLp (𝓕 F) 2 volume := by
    refine memLp_two_of_le_min hcontF.aestronglyMeasurable
      (C₁ := ∫ u : ℝ, ‖F u‖) (C₂ := Real.sqrt Λ / (2 * Real.pi))
      (integral_nonneg fun u => norm_nonneg _) (by positivity) ?_
    intro ξ hξ
    refine le_min (norm_fourier_le_integral_norm F ξ) ?_
    have habs : 0 < |ξ| := abs_pos.mpr hξ
    rw [div_div, le_div_iff₀ (by positivity)]
    rw [mul_comm]
    exact hsqrt ξ
  have hGle : ∀ ξ : ℝ, ‖freqPacket d sc N ξ‖
      ≤ ∑ c ∈ Finset.range (N + 1), ‖d c‖ := by
    intro ξ
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun c _ => ?_
    rw [norm_smul, Complex.norm_exp]
    simp
  have h𝓕𝒞2 : MemLp (𝓕 (portSynthesis d sc N F)) 2 volume := by
    have h2 : MemLp (fun ξ : ℝ =>
        (∑ c ∈ Finset.range (N + 1), ‖d c‖) * ‖𝓕 F ξ‖) 2 volume :=
      h𝓕F2.norm.const_mul _
    refine MemLp.of_le h2 hcont𝒞.aestronglyMeasurable ?_
    refine Eventually.of_forall fun ξ => ?_
    rw [fourier_portSynthesis hF1, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    calc ‖𝓕 F ξ‖ * ‖freqPacket d sc N ξ‖
        ≤ ‖𝓕 F ξ‖ * ∑ c ∈ Finset.range (N + 1), ‖d c‖ :=
          mul_le_mul_of_nonneg_left (hGle ξ) (norm_nonneg _)
      _ = (∑ c ∈ Finset.range (N + 1), ‖d c‖) * ‖𝓕 F ξ‖ :=
          mul_comm _ _
  -- with vanishing mass the transform is pure flux
  have hsplit : ∀ ξ : ℝ, 𝓕 (portSynthesis d sc N F) ξ
      = -(((Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * 𝓕 F ξ)
          • 𝓕 (stepPrefix d sc N) (-ξ)) := by
    intro ξ
    rw [fourier_portSynthesis hF1]
    have hfb := fourier_boundary d sc N hs (2 * Real.pi * ξ)
    rw [fourier_stepPrefix_eq, hM] at hfb
    have hG : freqPacket d sc N ξ
        = -((Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ))
            • 𝓕 (stepPrefix d sc N) (-ξ)) := by
      rw [show freqPacket d sc N ξ
          = Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (sc N : ℂ)
              * Complex.I) • (0 : H)
            - (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ))
              • 𝓕 (stepPrefix d sc N) (-ξ) from hfb]
      rw [smul_zero, zero_sub]
    rw [hG, smul_neg, smul_smul]
    congr 2
    ring
  have hkey1 : ‖(memLp_portSynthesis (d := d) (sc := sc) (N := N)
      hF2).toLp (portSynthesis d sc N F)‖
      = ‖h𝓕𝒞2.toLp (𝓕 (portSynthesis d sc N F))‖ := by
    rw [← fourier_toLp_eq h𝒞1 (memLp_portSynthesis hF2) h𝓕𝒞2,
      MeasureTheory.Lp.norm_fourier_eq]
  rw [hkey1, norm_toLp_sq]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only []
  rw [hsplit ξ, norm_neg, norm_smul, norm_mul, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs]

/-- `thm:multiport-prefix`: the weighted Minkowski assembly — if
each port obeys `x_r ≤ a_r + b_r` (the per-port mass–flux bound,
with `a_r = ‖F_r‖·‖M‖` and `b_r = √Λ_r·‖J‖`), then
`√(Σ λ_r x_r²) ≤ √(Σ λ_r a_r²) + √(Σ λ_r b_r²)` — the
manuscript's direct-sum argument. -/
theorem multiport_prefix {R : ℕ} (lam x a b : Fin R → ℝ)
    (hlam : ∀ r, 0 ≤ lam r) (ha : ∀ r, 0 ≤ a r) (hb : ∀ r, 0 ≤ b r)
    (hx0 : ∀ r, 0 ≤ x r) (hx : ∀ r, x r ≤ a r + b r) :
    Real.sqrt (∑ r, lam r * x r ^ 2)
      ≤ Real.sqrt (∑ r, lam r * a r ^ 2)
        + Real.sqrt (∑ r, lam r * b r ^ 2) := by
  classical
  set SA : ℝ := ∑ r, lam r * a r ^ 2 with hSA
  set SB : ℝ := ∑ r, lam r * b r ^ 2 with hSB
  have hSA0 : 0 ≤ SA :=
    Finset.sum_nonneg fun r _ => mul_nonneg (hlam r) (sq_nonneg _)
  have hSB0 : 0 ≤ SB :=
    Finset.sum_nonneg fun r _ => mul_nonneg (hlam r) (sq_nonneg _)
  have hCS : (∑ r, lam r * (a r * b r))
      ≤ Real.sqrt SA * Real.sqrt SB := by
    have h1 : (∑ r, (Real.sqrt (lam r) * a r)
        * (Real.sqrt (lam r) * b r)) ^ 2
        ≤ (∑ r, (Real.sqrt (lam r) * a r) ^ 2)
          * ∑ r, (Real.sqrt (lam r) * b r) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h2 : ∀ r : Fin R, (Real.sqrt (lam r) * a r)
        * (Real.sqrt (lam r) * b r) = lam r * (a r * b r) := by
      intro r
      rw [show (Real.sqrt (lam r) * a r) * (Real.sqrt (lam r) * b r)
          = (Real.sqrt (lam r) * Real.sqrt (lam r)) * (a r * b r)
        from by ring, Real.mul_self_sqrt (hlam r)]
    have h3 : ∀ r : Fin R, (Real.sqrt (lam r) * a r) ^ 2
        = lam r * a r ^ 2 := by
      intro r
      rw [mul_pow, Real.sq_sqrt (hlam r)]
    have h4 : ∀ r : Fin R, (Real.sqrt (lam r) * b r) ^ 2
        = lam r * b r ^ 2 := by
      intro r
      rw [mul_pow, Real.sq_sqrt (hlam r)]
    rw [Finset.sum_congr rfl fun r _ => h2 r,
      Finset.sum_congr rfl fun r _ => h3 r,
      Finset.sum_congr rfl fun r _ => h4 r] at h1
    have h5 : (0 : ℝ) ≤ ∑ r, lam r * (a r * b r) :=
      Finset.sum_nonneg fun r _ =>
        mul_nonneg (hlam r) (mul_nonneg (ha r) (hb r))
    have h6 := (Real.le_sqrt h5 (by positivity)).mpr h1
    rwa [Real.sqrt_mul hSA0] at h6
  have hmain : (∑ r, lam r * x r ^ 2)
      ≤ (Real.sqrt SA + Real.sqrt SB) ^ 2 := by
    have h1 : (∑ r, lam r * x r ^ 2)
        ≤ ∑ r, lam r * (a r + b r) ^ 2 := by
      refine Finset.sum_le_sum fun r _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (hlam r)
      exact pow_le_pow_left₀ (hx0 r) (hx r) 2
    have h2 : (∑ r, lam r * (a r + b r) ^ 2)
        = SA + 2 * (∑ r, lam r * (a r * b r)) + SB := by
      rw [hSA, hSB, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    have h3 : (Real.sqrt SA + Real.sqrt SB) ^ 2
        = SA + 2 * (Real.sqrt SA * Real.sqrt SB) + SB := by
      rw [add_sq, Real.sq_sqrt hSA0, Real.sq_sqrt hSB0]
      ring
    rw [h3]
    calc (∑ r, lam r * x r ^ 2)
        ≤ ∑ r, lam r * (a r + b r) ^ 2 := h1
      _ = SA + 2 * (∑ r, lam r * (a r * b r)) + SB := h2
      _ ≤ SA + 2 * (Real.sqrt SA * Real.sqrt SB) + SB := by
          linarith [hCS]
  calc Real.sqrt (∑ r, lam r * x r ^ 2)
      ≤ Real.sqrt ((Real.sqrt SA + Real.sqrt SB) ^ 2) :=
        Real.sqrt_le_sqrt hmain
    _ = Real.sqrt SA + Real.sqrt SB :=
        Real.sqrt_sq (by positivity)

end MassFlux


end NCG
