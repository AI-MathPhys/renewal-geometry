/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Gravity.VolterraML
import NCG.Gravity.MLContinuity

/-!
# The driven fractional threshold equation
  (`thm:irreversible-crossing-threshold`, exact solution layer)

The driven Caputo relaxation `D^α y = -λy + s₀f` in integrated
(Volterra) form, with the exact Mittag-Leffler solution
`y = Δ₀E_α(-λtᵅ) + s₀(R ⋆ f)` where
`R(v) = v^{α-1}E_{α,α}(-λvᵅ)` is the resolvent kernel.

This file builds the measure-theoretic infrastructure: the kernel
`mlK`, its measurability, the envelope bound
`|R(v)| ≤ v^{α-1}·E_{α,α}(|λ|tᵅ)` on `(0,t]`, and the section
integrabilities feeding the triangle Fubini exchange.
-/

namespace NCG

open Real MeasureTheory intervalIntegral

/-- The resolvent kernel `R(v) = v^{α-1}E_{α,α}(-λvᵅ)`. -/
noncomputable def mlK (al lam : ℝ) (v : ℝ) : ℝ :=
  v ^ (al - 1) * mittagLeffler al al (-(lam * v ^ al))

/-- Measurability of a fixed real power. -/
theorem measurable_rpow_const (c : ℝ) :
    Measurable fun v : ℝ => v ^ c := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  intro x hx
  exact (Real.continuousAt_rpow_const x c
    (Or.inl (Set.mem_compl_singleton_iff.mp hx))).continuousWithinAt

/-- The kernel is measurable. -/
theorem mlK_measurable {al lam : ℝ} (hal : 0 < al) :
    Measurable (mlK al lam) := by
  unfold mlK
  apply Measurable.mul (measurable_rpow_const (al - 1))
  exact (ml_continuous hal hal).measurable.comp
    (((measurable_rpow_const al).const_mul lam).neg)

/-- The envelope bound: `|R(v)| ≤ v^{α-1}·E_{α,α}(|λ|Tᵅ)` for
`v ∈ (0, T]`. -/
theorem mlK_bound {al lam T : ℝ} (hal : 0 < al) (_hT : 0 < T)
    {v : ℝ} (hv : v ∈ Set.Ioc 0 T) :
    |mlK al lam v| ≤ v ^ (al - 1) *
      mittagLeffler al al (|lam| * T ^ al) := by
  obtain ⟨hv0, hvT⟩ := hv
  unfold mlK
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hv0.le _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hv0.le _)
  calc |mittagLeffler al al (-(lam * v ^ al))|
      ≤ mittagLeffler al al |(-(lam * v ^ al))| :=
        ml_abs_le hal hal _
  _ ≤ mittagLeffler al al (|lam| * T ^ al) := by
        apply ml_mono_nonneg hal hal (abs_nonneg _)
        rw [abs_neg, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hv0.le al)]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg lam)
        exact Real.rpow_le_rpow hv0.le hvT hal.le

/-- The kernel slice `u ↦ mlK(s-u)·f(u)` is interval integrable. -/
theorem mlK_conv_intervalIntegrable {al lam : ℝ} (hal : 0 < al)
    {f : ℝ → ℝ} (hf : Continuous f) (s : ℝ) :
    IntervalIntegrable (fun u => mlK al lam (s - u) * f u)
      MeasureTheory.volume 0 s := by
  have h1 : IntervalIntegrable (fun u : ℝ => (s - u) ^ (al - 1))
      MeasureTheory.volume 0 s := by
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ (al - 1))
        MeasureTheory.volume 0 s :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h := h0.comp_sub_left s
    simpa using h.symm
  have hcongr : (fun u => mlK al lam (s - u) * f u)
      = fun u => (s - u) ^ (al - 1) *
          (mittagLeffler al al (-(lam * (s - u) ^ al)) * f u) := by
    funext u
    unfold mlK
    ring
  rw [hcongr]
  apply h1.mul_continuousOn
  apply ContinuousOn.mul _ hf.continuousOn
  apply Continuous.continuousOn
  exact (ml_continuous hal hal).comp
    (((Real.continuous_rpow_const hal.le).comp
      (continuous_const.sub continuous_id)).const_mul lam).neg

/-- The set identity for the lower triangle sections. -/
theorem Ioc_inter_Iio_eq {T s : ℝ} (hsT : s ≤ T) :
    Set.Ioc (0 : ℝ) T ∩ Set.Iio s = Set.Ioo 0 s := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, by linarith⟩, h2⟩

/-- The set identity for the upper triangle sections. -/
theorem Ioc_inter_Ioi_eq {T u : ℝ} (hu : 0 < u) :
    Set.Ioc (0 : ℝ) T ∩ Set.Ioi u = Set.Ioc u T := by
  ext s
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith, h2⟩, h1⟩

/-- Nonnegativity of the Mittag-Leffler function at nonnegative
arguments. -/
theorem ml_nonneg {al be x : ℝ} (hal : 0 < al) (hbe : 0 < be)
    (hx : 0 ≤ x) : 0 ≤ mittagLeffler al be x := by
  unfold mittagLeffler
  apply tsum_nonneg
  intro n
  exact div_nonneg (pow_nonneg hx n)
    (Real.Gamma_pos_of_pos (by positivity)).le

/-- The reflected power `s ↦ (T-s)^{α-1}` is interval integrable. -/
theorem reflected_rpow_intervalIntegrable {al T : ℝ} (hal : 0 < al) :
    IntervalIntegrable (fun s : ℝ => (T - s) ^ (al - 1))
      MeasureTheory.volume 0 T := by
  have h0 : IntervalIntegrable (fun x : ℝ => x ^ (al - 1))
      MeasureTheory.volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h := h0.comp_sub_left T
  simpa using h.symm

/-- Triangle Fubini for the driven convolution: the double
convolution reorders onto the resolvent factor. -/
theorem conv_swap {al lam T : ℝ} (hal : 0 < al) (hT : 0 < T)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ s in (0 : ℝ)..T, (T - s) ^ (al - 1) *
        ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u
      = ∫ u in (0 : ℝ)..T, f u *
          ∫ v in (0 : ℝ)..(T - u),
            (T - u - v) ^ (al - 1) * mlK al lam v := by
  classical
  set μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc 0 T) with hμ
  set F : ℝ → ℝ → ℝ := fun s u =>
    if u < s then (T - s) ^ (al - 1) * (mlK al lam (s - u) * f u)
    else 0 with hF
  obtain ⟨Mf, hMf⟩ := (isCompact_Icc (a := (0 : ℝ))
    (b := T)).exists_bound_of_continuousOn hf.norm.continuousOn
  simp only [norm_norm] at hMf
  set CE : ℝ := mittagLeffler al al (|lam| * T ^ al) with hCE
  have hCE0 : 0 ≤ CE :=
    ml_nonneg hal hal (by positivity)
  have hMf0 : 0 ≤ Mf :=
    le_trans (norm_nonneg (f 0)) (hMf 0 ⟨le_refl 0, hT.le⟩)
  -- measurability
  have hFmeas : Measurable (Function.uncurry F) := by
    apply Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    · apply Measurable.mul
      · exact (measurable_rpow_const (al - 1)).comp
          (measurable_const.sub measurable_fst)
      · exact ((mlK_measurable hal).comp
          (measurable_fst.sub measurable_snd)).mul
          (hf.measurable.comp measurable_snd)
    · exact measurable_const
  have hFaesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry F) (μ.prod μ) := hFmeas.aestronglyMeasurable
  -- indicator form of the sections
  have hind : ∀ s, F s = (Set.Iio s).indicator
      (fun u => (T - s) ^ (al - 1) * (mlK al lam (s - u) * f u)) := by
    intro s
    funext u
    by_cases h : u < s
    · simp [hF, Set.indicator_of_mem, h, Set.mem_Iio]
    · simp [hF, Set.indicator_of_notMem, h, Set.mem_Iio]
  -- sections are integrable
  have hsec : ∀ s ∈ Set.Ioc (0 : ℝ) T,
      MeasureTheory.Integrable (F s) μ := by
    intro s hs
    rw [hind s, hμ,
      MeasureTheory.integrable_indicator_iff measurableSet_Iio,
      MeasureTheory.IntegrableOn,
      MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
      Set.inter_comm, Ioc_inter_Iio_eq hs.2]
    apply MeasureTheory.Integrable.const_mul
    exact ((mlK_conv_intervalIntegrable hal hf s).1).mono_set
      Set.Ioo_subset_Ioc_self
  have hcond1 : ∀ᵐ s ∂μ, MeasureTheory.Integrable (F s) μ := by
    rw [hμ]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hsec
  -- the norm-section bound
  have hnormbound : ∀ s ∈ Set.Ioc (0 : ℝ) T,
      (∫ u, ‖F s u‖ ∂μ)
        ≤ (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al)) := by
    intro s hs
    have hdom_int : MeasureTheory.Integrable
        ((Set.Iio s).indicator
          (fun u => (T - s) ^ (al - 1) * ((s - u) ^ (al - 1) * (CE * Mf)))) μ := by
      rw [hμ, MeasureTheory.integrable_indicator_iff measurableSet_Iio,
        MeasureTheory.IntegrableOn,
        MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
        Set.inter_comm, Ioc_inter_Iio_eq hs.2]
      apply MeasureTheory.Integrable.const_mul
      apply MeasureTheory.Integrable.mul_const
      have h1 : IntervalIntegrable (fun u : ℝ => (s - u) ^ (al - 1))
          MeasureTheory.volume 0 s := by
        have h0 : IntervalIntegrable (fun x : ℝ => x ^ (al - 1))
            MeasureTheory.volume 0 s :=
          intervalIntegral.intervalIntegrable_rpow' (by linarith)
        have h := h0.comp_sub_left s
        simpa using h.symm
      exact (h1.1).mono_set Set.Ioo_subset_Ioc_self
    have hmono : (∫ u, ‖F s u‖ ∂μ)
        ≤ ∫ u, (Set.Iio s).indicator
            (fun u => (T - s) ^ (al - 1) *
              ((s - u) ^ (al - 1) * (CE * Mf))) u ∂μ := by
      apply MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun u => norm_nonneg _) hdom_int
      rw [hμ]
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      intro u hu
      simp only [hind s]
      by_cases h : u < s
      · rw [Set.indicator_of_mem (Set.mem_Iio.mpr h),
          Set.indicator_of_mem (Set.mem_Iio.mpr h)]
        rw [norm_mul, norm_mul]
        have hTs : (0 : ℝ) ≤ T - s := by linarith [hs.2]
        rw [Real.norm_eq_abs ((T - s) ^ (al - 1)),
          abs_of_nonneg (Real.rpow_nonneg hTs _)]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hTs _)
        have hbnd := mlK_bound (lam := lam) hal hT
          (v := s - u) ⟨by linarith, by linarith [hu.1, hs.2]⟩
        calc ‖mlK al lam (s - u)‖ * ‖f u‖
            ≤ ((s - u) ^ (al - 1) * CE) * Mf := by
              apply mul_le_mul _ _ (norm_nonneg _) _
              · rw [Real.norm_eq_abs]
                exact hbnd
              · exact hMf u ⟨hu.1.le, hu.2⟩
              · positivity
        _ = (s - u) ^ (al - 1) * (CE * Mf) := by ring
      · rw [Set.indicator_of_notMem (by simpa [Set.mem_Iio] using h),
          Set.indicator_of_notMem (by simpa [Set.mem_Iio] using h)]
        simp
    have heval : (∫ u, (Set.Iio s).indicator
        (fun u => (T - s) ^ (al - 1) *
          ((s - u) ^ (al - 1) * (CE * Mf))) u ∂μ)
        = (T - s) ^ (al - 1) * (CE * Mf) *
            ∫ u in Set.Ioo (0 : ℝ) s, (s - u) ^ (al - 1) := by
      rw [hμ, MeasureTheory.integral_indicator measurableSet_Iio,
        MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
        Set.inter_comm, Ioc_inter_Iio_eq hs.2,
        ← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro u _
      ring
    have hrpow_eval : (∫ u in Set.Ioo (0 : ℝ) s, (s - u) ^ (al - 1))
        = s ^ al / al := by
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hs.1.le]
      rw [show (fun u : ℝ => (s - u) ^ (al - 1))
        = fun u : ℝ => (fun x : ℝ => x ^ (al - 1)) (s - u) from rfl]
      rw [intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => x ^ (al - 1)) s]
      rw [sub_zero, sub_self]
      rw [integral_rpow (Or.inl (by linarith))]
      rw [show al - 1 + 1 = al by ring, Real.zero_rpow hal.ne']
      ring
    have hfin : (T - s) ^ (al - 1) * (CE * Mf) * (s ^ al / al)
        ≤ (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al)) := by
      have hs_pow : s ^ al ≤ T ^ al :=
        Real.rpow_le_rpow hs.1.le hs.2 hal.le
      have hTs : (0 : ℝ) ≤ T - s := by linarith [hs.2]
      have h1 : (0 : ℝ) ≤ (T - s) ^ (al - 1) := Real.rpow_nonneg hTs _
      have h2 : (0 : ℝ) ≤ CE * Mf := mul_nonneg hCE0 hMf0
      rw [show (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al))
        = (T - s) ^ (al - 1) * (CE * Mf) * (T ^ al / al) by ring]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg h1 h2)
      gcongr
    calc (∫ u, ‖F s u‖ ∂μ)
        ≤ ∫ u, (Set.Iio s).indicator
            (fun u => (T - s) ^ (al - 1) *
              ((s - u) ^ (al - 1) * (CE * Mf))) u ∂μ := hmono
    _ = (T - s) ^ (al - 1) * (CE * Mf) * (s ^ al / al) := by
          rw [heval, hrpow_eval]
    _ ≤ (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al)) := hfin
  -- cond2: the norm-section integral function is integrable
  have hcond2 : MeasureTheory.Integrable
      (fun s => ∫ u, ‖F s u‖ ∂μ) μ := by
    apply MeasureTheory.Integrable.mono'
      (g := fun s => (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al)))
    · rw [hμ]
      exact ((reflected_rpow_intervalIntegrable
        (T := T) hal).1).mul_const _
    · exact hFaesm.norm.integral_prod_right'
    · rw [hμ]
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      intro s hs
      rw [Real.norm_eq_abs, abs_of_nonneg
        (MeasureTheory.integral_nonneg fun u => norm_nonneg _)]
      exact hnormbound s hs
  have hInt : MeasureTheory.Integrable (Function.uncurry F)
      (μ.prod μ) :=
    (MeasureTheory.integrable_prod_iff hFaesm).mpr ⟨hcond1, hcond2⟩
  have hswap := MeasureTheory.integral_integral_swap hInt
  -- identify the left side
  have hL : (∫ s in (0 : ℝ)..T, (T - s) ^ (al - 1) *
      ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u)
      = ∫ s, ∫ u, F s u ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hT.le, hμ]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp only []
    rw [hind s, MeasureTheory.integral_indicator measurableSet_Iio,
      MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
      Set.inter_comm, Ioc_inter_Iio_eq hs.2,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hs.1.le,
      ← intervalIntegral.integral_const_mul]
  -- identify the right side
  have hR : (∫ u, ∫ s, F s u ∂μ ∂μ)
      = ∫ u in (0 : ℝ)..T, f u *
          ∫ v in (0 : ℝ)..(T - u),
            (T - u - v) ^ (al - 1) * mlK al lam v := by
    rw [intervalIntegral.integral_of_le hT.le, hμ]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    simp only []
    have hind2 : (fun s => F s u) = (Set.Ioi u).indicator
        (fun s => (T - s) ^ (al - 1) * (mlK al lam (s - u) * f u)) := by
      funext s
      by_cases h : u < s
      · simp [hF, Set.indicator_of_mem, h, Set.mem_Ioi]
      · simp [hF, Set.indicator_of_notMem, h, Set.mem_Ioi]
    rw [hind2, MeasureTheory.integral_indicator measurableSet_Ioi,
      MeasureTheory.Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_comm, Ioc_inter_Ioi_eq hu.1,
      ← intervalIntegral.integral_of_le hu.2]
    rw [show (fun s => (T - s) ^ (al - 1) * (mlK al lam (s - u) * f u))
      = fun s => (fun v => (T - u - v) ^ (al - 1) *
          (mlK al lam v * f u)) (s - u) from by
        funext s
        simp only []
        rw [show T - u - (s - u) = T - s by ring]]
    rw [intervalIntegral.integral_comp_sub_right
      (fun v => (T - u - v) ^ (al - 1) * (mlK al lam v * f u)) u,
      sub_self, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    ring
  rw [hL, hswap, hR]

/-- Integrability of the reflected-kernel convolution
`s ↦ (T-s)^{α-1}·(R⋆f)(s)` on `(0,T]`. -/
theorem reflected_conv_integrableOn {al lam T : ℝ} (hal : 0 < al)
    (hT : 0 < T) {f : ℝ → ℝ} (hf : Continuous f) :
    MeasureTheory.IntegrableOn
      (fun s => (T - s) ^ (al - 1) *
        ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u)
      (Set.Ioc 0 T) := by
  classical
  set μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc 0 T) with hμ
  set F : ℝ → ℝ → ℝ := fun s u =>
    if u < s then (T - s) ^ (al - 1) * (mlK al lam (s - u) * f u)
    else 0 with hF
  obtain ⟨Mf, hMf⟩ := (isCompact_Icc (a := (0 : ℝ))
    (b := T)).exists_bound_of_continuousOn hf.norm.continuousOn
  simp only [norm_norm] at hMf
  set CE : ℝ := mittagLeffler al al (|lam| * T ^ al) with hCE
  have hCE0 : 0 ≤ CE :=
    ml_nonneg hal hal (by positivity)
  have hMf0 : 0 ≤ Mf :=
    le_trans (norm_nonneg (f 0)) (hMf 0 ⟨le_refl 0, hT.le⟩)
  -- measurability
  have hFmeas : Measurable (Function.uncurry F) := by
    apply Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    · apply Measurable.mul
      · exact (measurable_rpow_const (al - 1)).comp
          (measurable_const.sub measurable_fst)
      · exact ((mlK_measurable hal).comp
          (measurable_fst.sub measurable_snd)).mul
          (hf.measurable.comp measurable_snd)
    · exact measurable_const
  have hFaesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry F) (μ.prod μ) := hFmeas.aestronglyMeasurable
  -- indicator form of the sections
  have hind : ∀ s, F s = (Set.Iio s).indicator
      (fun u => (T - s) ^ (al - 1) * (mlK al lam (s - u) * f u)) := by
    intro s
    funext u
    by_cases h : u < s
    · simp [hF, Set.indicator_of_mem, h, Set.mem_Iio]
    · simp [hF, Set.indicator_of_notMem, h, Set.mem_Iio]
  -- sections are integrable
  have hsec : ∀ s ∈ Set.Ioc (0 : ℝ) T,
      MeasureTheory.Integrable (F s) μ := by
    intro s hs
    rw [hind s, hμ,
      MeasureTheory.integrable_indicator_iff measurableSet_Iio,
      MeasureTheory.IntegrableOn,
      MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
      Set.inter_comm, Ioc_inter_Iio_eq hs.2]
    apply MeasureTheory.Integrable.const_mul
    exact ((mlK_conv_intervalIntegrable hal hf s).1).mono_set
      Set.Ioo_subset_Ioc_self
  have hcond1 : ∀ᵐ s ∂μ, MeasureTheory.Integrable (F s) μ := by
    rw [hμ]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hsec
  -- the norm-section bound
  have hnormbound : ∀ s ∈ Set.Ioc (0 : ℝ) T,
      (∫ u, ‖F s u‖ ∂μ)
        ≤ (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al)) := by
    intro s hs
    have hdom_int : MeasureTheory.Integrable
        ((Set.Iio s).indicator
          (fun u => (T - s) ^ (al - 1) * ((s - u) ^ (al - 1) * (CE * Mf)))) μ := by
      rw [hμ, MeasureTheory.integrable_indicator_iff measurableSet_Iio,
        MeasureTheory.IntegrableOn,
        MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
        Set.inter_comm, Ioc_inter_Iio_eq hs.2]
      apply MeasureTheory.Integrable.const_mul
      apply MeasureTheory.Integrable.mul_const
      have h1 : IntervalIntegrable (fun u : ℝ => (s - u) ^ (al - 1))
          MeasureTheory.volume 0 s := by
        have h0 : IntervalIntegrable (fun x : ℝ => x ^ (al - 1))
            MeasureTheory.volume 0 s :=
          intervalIntegral.intervalIntegrable_rpow' (by linarith)
        have h := h0.comp_sub_left s
        simpa using h.symm
      exact (h1.1).mono_set Set.Ioo_subset_Ioc_self
    have hmono : (∫ u, ‖F s u‖ ∂μ)
        ≤ ∫ u, (Set.Iio s).indicator
            (fun u => (T - s) ^ (al - 1) *
              ((s - u) ^ (al - 1) * (CE * Mf))) u ∂μ := by
      apply MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun u => norm_nonneg _) hdom_int
      rw [hμ]
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      intro u hu
      simp only [hind s]
      by_cases h : u < s
      · rw [Set.indicator_of_mem (Set.mem_Iio.mpr h),
          Set.indicator_of_mem (Set.mem_Iio.mpr h)]
        rw [norm_mul, norm_mul]
        have hTs : (0 : ℝ) ≤ T - s := by linarith [hs.2]
        rw [Real.norm_eq_abs ((T - s) ^ (al - 1)),
          abs_of_nonneg (Real.rpow_nonneg hTs _)]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hTs _)
        have hbnd := mlK_bound (lam := lam) hal hT
          (v := s - u) ⟨by linarith, by linarith [hu.1, hs.2]⟩
        calc ‖mlK al lam (s - u)‖ * ‖f u‖
            ≤ ((s - u) ^ (al - 1) * CE) * Mf := by
              apply mul_le_mul _ _ (norm_nonneg _) _
              · rw [Real.norm_eq_abs]
                exact hbnd
              · exact hMf u ⟨hu.1.le, hu.2⟩
              · positivity
        _ = (s - u) ^ (al - 1) * (CE * Mf) := by ring
      · rw [Set.indicator_of_notMem (by simpa [Set.mem_Iio] using h),
          Set.indicator_of_notMem (by simpa [Set.mem_Iio] using h)]
        simp
    have heval : (∫ u, (Set.Iio s).indicator
        (fun u => (T - s) ^ (al - 1) *
          ((s - u) ^ (al - 1) * (CE * Mf))) u ∂μ)
        = (T - s) ^ (al - 1) * (CE * Mf) *
            ∫ u in Set.Ioo (0 : ℝ) s, (s - u) ^ (al - 1) := by
      rw [hμ, MeasureTheory.integral_indicator measurableSet_Iio,
        MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
        Set.inter_comm, Ioc_inter_Iio_eq hs.2,
        ← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro u _
      ring
    have hrpow_eval : (∫ u in Set.Ioo (0 : ℝ) s, (s - u) ^ (al - 1))
        = s ^ al / al := by
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hs.1.le]
      rw [show (fun u : ℝ => (s - u) ^ (al - 1))
        = fun u : ℝ => (fun x : ℝ => x ^ (al - 1)) (s - u) from rfl]
      rw [intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => x ^ (al - 1)) s]
      rw [sub_zero, sub_self]
      rw [integral_rpow (Or.inl (by linarith))]
      rw [show al - 1 + 1 = al by ring, Real.zero_rpow hal.ne']
      ring
    have hfin : (T - s) ^ (al - 1) * (CE * Mf) * (s ^ al / al)
        ≤ (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al)) := by
      have hs_pow : s ^ al ≤ T ^ al :=
        Real.rpow_le_rpow hs.1.le hs.2 hal.le
      have hTs : (0 : ℝ) ≤ T - s := by linarith [hs.2]
      have h1 : (0 : ℝ) ≤ (T - s) ^ (al - 1) := Real.rpow_nonneg hTs _
      have h2 : (0 : ℝ) ≤ CE * Mf := mul_nonneg hCE0 hMf0
      rw [show (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al))
        = (T - s) ^ (al - 1) * (CE * Mf) * (T ^ al / al) by ring]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg h1 h2)
      gcongr
    calc (∫ u, ‖F s u‖ ∂μ)
        ≤ ∫ u, (Set.Iio s).indicator
            (fun u => (T - s) ^ (al - 1) *
              ((s - u) ^ (al - 1) * (CE * Mf))) u ∂μ := hmono
    _ = (T - s) ^ (al - 1) * (CE * Mf) * (s ^ al / al) := by
          rw [heval, hrpow_eval]
    _ ≤ (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al)) := hfin
  -- cond2: the norm-section integral function is integrable
  have hcond2 : MeasureTheory.Integrable
      (fun s => ∫ u, ‖F s u‖ ∂μ) μ := by
    apply MeasureTheory.Integrable.mono'
      (g := fun s => (T - s) ^ (al - 1) * (CE * Mf * (T ^ al / al)))
    · rw [hμ]
      exact ((reflected_rpow_intervalIntegrable
        (T := T) hal).1).mul_const _
    · exact hFaesm.norm.integral_prod_right'
    · rw [hμ]
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      intro s hs
      rw [Real.norm_eq_abs, abs_of_nonneg
        (MeasureTheory.integral_nonneg fun u => norm_nonneg _)]
      exact hnormbound s hs
  have hInt : MeasureTheory.Integrable (Function.uncurry F)
      (μ.prod μ) :=
    (MeasureTheory.integrable_prod_iff hFaesm).mpr ⟨hcond1, hcond2⟩
  have hker : MeasureTheory.Integrable
      (fun s => ∫ u, F s u ∂μ) μ := hInt.integral_prod_left
  rw [MeasureTheory.IntegrableOn, ← hμ]
  apply hker.congr
  rw [hμ]
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
  intro s hs
  simp only []
  rw [hind s, MeasureTheory.integral_indicator measurableSet_Iio,
    MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
    Set.inter_comm, Ioc_inter_Iio_eq hs.2,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hs.1.le,
    ← intervalIntegral.integral_const_mul]

/-- `thm:irreversible-crossing-threshold` (driven exact solution):
`y(t) = y₀·E_α(-λtᵅ) + (R⋆f)(t)` with the resolvent kernel
`R(v) = v^{α-1}E_{α,α}(-λvᵅ)` solves the driven linear Volterra
equation `y = y₀ - (λ/Γ(α))·(k⋆y) + (1/Γ(α))·(k⋆f)`,
`k(v) = v^{α-1}` — the integrated form of the driven Caputo
relaxation equation `D^α y = -λy + f`. -/
theorem driven_ml_volterra {al lam t y0 : ℝ} (hal : 0 < al)
    (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) :
    y0 * mittagLeffler al 1 (-(lam * t ^ al))
        + ∫ u in (0 : ℝ)..t, mlK al lam (t - u) * f u
      = y0
        - lam / Real.Gamma al *
            (∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) *
              (y0 * mittagLeffler al 1 (-(lam * s ^ al))
                + ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u))
        + 1 / Real.Gamma al *
            ∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) * f s := by
  have hGal : Real.Gamma al ≠ 0 := (Real.Gamma_pos_of_pos hal).ne'
  -- the mixed-kernel identity: λ·(k⋆(R⋆f)) = k⋆f − Γ(α)·(R⋆f)
  have hstep : lam * (∫ u in (0 : ℝ)..t, f u *
        ∫ v in (0 : ℝ)..(t - u), (t - u - v) ^ (al - 1) * mlK al lam v)
      = (∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) * f s)
        - Real.Gamma al * ∫ u in (0 : ℝ)..t, mlK al lam (t - u) * f u := by
    have hfr : IntervalIntegrable
        (fun u => f u * (t - u) ^ (al - 1))
        MeasureTheory.volume 0 t :=
      (reflected_rpow_intervalIntegrable (T := t) hal).continuousOn_mul
        hf.continuousOn
    have hmlf : IntervalIntegrable
        (fun u => Real.Gamma al * (mlK al lam (t - u) * f u))
        MeasureTheory.volume 0 t :=
      (mlK_conv_intervalIntegrable hal hf t).const_mul _
    have hcongr2 : (∫ u in (0 : ℝ)..t, lam * (f u *
          ∫ v in (0 : ℝ)..(t - u),
            (t - u - v) ^ (al - 1) * mlK al lam v))
        = ∫ u in (0 : ℝ)..t,
            (f u * (t - u) ^ (al - 1)
              - Real.Gamma al * (mlK al lam (t - u) * f u)) := by
      rw [intervalIntegral.integral_of_le ht.le,
        intervalIntegral.integral_of_le ht.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      simp only []
      have ht' : (0 : ℝ) < t - u := by linarith [hu.2]
      have h := mlKernel_volterra (lam := lam) hal ht'
      unfold mlK
      linear_combination f u * h
    rw [← intervalIntegral.integral_const_mul, hcongr2,
      intervalIntegral.integral_sub hfr hmlf,
      intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    simp only []
    ring
  -- swap the double convolution
  have hswap := conv_swap (lam := lam) hal ht hf
  -- multiplied resolvent identity: Γ(α)·(R⋆f) = k⋆f − λ·(k⋆(R⋆f))
  have hPmul : Real.Gamma al *
        (∫ u in (0 : ℝ)..t, mlK al lam (t - u) * f u)
      = (∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) * f s)
        - lam * ∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) *
            ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u := by
    linear_combination hstep + lam * hswap
  have hPdiv : (∫ u in (0 : ℝ)..t, mlK al lam (t - u) * f u)
      = 1 / Real.Gamma al *
          (∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) * f s)
        - lam / Real.Gamma al *
            ∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) *
              ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u := by
    field_simp
    linear_combination hPmul
  -- split the driving integral
  have hHcont : Continuous
      (fun s : ℝ => mittagLeffler al 1 (-(lam * s ^ al))) :=
    (ml_continuous hal one_pos).comp
      (((Real.continuous_rpow_const hal.le).const_mul lam).neg)
  have hIH_int : IntervalIntegrable
      (fun s => (t - s) ^ (al - 1) *
        mittagLeffler al 1 (-(lam * s ^ al)))
      MeasureTheory.volume 0 t :=
    (reflected_rpow_intervalIntegrable (T := t) hal).mul_continuousOn
      hHcont.continuousOn
  have hIP_int : IntervalIntegrable
      (fun s => (t - s) ^ (al - 1) *
        ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u)
      MeasureTheory.volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr
      (reflected_conv_integrableOn hal ht hf)
  have hsplit : (∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) *
        (y0 * mittagLeffler al 1 (-(lam * s ^ al))
          + ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u))
      = y0 * (∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) *
            mittagLeffler al 1 (-(lam * s ^ al)))
        + ∫ s in (0 : ℝ)..t, (t - s) ^ (al - 1) *
            ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u := by
    rw [show (fun s => (t - s) ^ (al - 1) *
          (y0 * mittagLeffler al 1 (-(lam * s ^ al))
            + ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u))
        = fun s => y0 * ((t - s) ^ (al - 1) *
              mittagLeffler al 1 (-(lam * s ^ al)))
            + (t - s) ^ (al - 1) *
              ∫ u in (0 : ℝ)..s, mlK al lam (s - u) * f u from by
        funext s
        ring]
    rw [intervalIntegral.integral_add (hIH_int.const_mul y0) hIP_int,
      intervalIntegral.integral_const_mul]
  rw [hsplit]
  have hH := ml_volterra (lam := lam) hal ht
  linear_combination y0 * hH + hPdiv

end NCG
