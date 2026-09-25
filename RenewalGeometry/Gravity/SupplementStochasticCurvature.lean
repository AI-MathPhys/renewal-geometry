/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.CurvatureEnergyPropagationExact
import RenewalGeometry.Action.ActionCurrentCertificateExact

/-!
# Expected curvature energy and a sufficient pathwise upgrade
  (`cor:supp-stochastic-curvature`, `eq:supp-expected-curvature`,
  `eq:supp-pathwise-source-budget`; emergent-spacetime manuscript, supplement)

Expectations are Lebesgue integrals `∫⁻ ω, ENNReal.ofReal (·) ∂μ` of the
nonnegative energies, so no integrability in `ω` is assumed (only
measurability of the processes entering Tonelli's theorem); the time
integrals of the source norms are the Bochner integrals of the manuscript
under its finite `L²` budgets.

* `pathwise_sup_sq_le`: from the pathwise propagation estimate
  `sup_t z(t) ≤ e^{A_*}(z(0) + ∫₀^{T_*} ‖f‖)` one gets
  `sup_t z(t)² ≤ 2 e^{2A_*}(z(0)² + (∫₀^{T_*} ‖f‖)²)`.
* `sq_setIntegral_gramNorm_le`: Cauchy–Schwarz in time,
  `(∫₀^{T_*} ‖f‖_H)² ≤ T_* ∫₀^{T_*} ‖f‖²_H`.
* `lintegral_gramNormSq_source_le`: the pathwise source budget
  `∫₀^{T_*} ‖f‖²_H ≤ 2 ∫₀^{T_*} Γ̄ ‖𝔞‖²_{G⁻¹} + 2 ∫₀^{T_*} ‖r^{src}‖²_H`
  from `eq:supp-curvature-source-budget` with a deterministic bound
  `Γ_X(t) ≤ Γ̄(t)`.
* `expected_curvature_energy_bound` (`eq:supp-expected-curvature`): with the
  incidence `f = 𝖳 𝔞 + r^{src}` (target norm already the curvature-energy
  norm), deterministic supported bounds `Γ_X(ω, t) ≤ Γ̄(t)` and the
  action-gradient bound in expectation `𝔼 ‖𝔞(t)‖²_{G⁻¹} ≤ C(t) Δ(t)`,
  `𝔼 sup_{t ≤ T_*} z(t)² ≤ 2 e^{2A_*}[𝔼 z(0)² + 2 T_* ∫₀^{T_*} Γ̄ C Δ
    + 2 T_* 𝔼 ∫₀^{T_*} ‖r^{src}‖²_H]`
  (Tonelli for the `ω × t` product; `lintegral_lintegral_swap`).
* `expected_curvature_energy_bound_of_writer`: the same conclusion with the
  pathwise propagation estimate *derived* from the finite propagation
  equation `eq:main-curvature-propagation-writer` holding pathwise, via the
  proved `curvature_energy_uniform_bound` (`thm:main-curvature-propagation`).
* `pathwise_curvature_upgrade` (`eq:supp-pathwise-source-budget`): for a
  countable cofinal sequence with `sup_X z_X(0) < ∞` almost surely,
  `Σ_X 𝔼 ∫₀^{T_*} ‖f_X‖²_{H_X} < ∞` and a pathwise uniform growth budget,
  Tonelli (`lintegral_tsum`, `ae_lt_top'`) makes the realized integrated
  source energies uniformly bounded almost surely, and the deterministic
  propagation estimate gives `sup_X sup_t z_X(t) < ∞` almost surely.
* `pathwise_l2_curvature_upgrade`: with pathwise interpolation, lapse and
  boundary budgets (as in `derived_l2_curvature_bound`) this yields
  `sup_X ‖R_X‖_{L²(K)} < ∞` almost surely.

Scoped hypotheses disclosed: the Gram square roots are supplied as data
(`GramSqrt`); for each path the `H`-norm of the source is square integrable on
`[0, T_*]`; the weighted dual-norm process `Γ̄(t) ‖𝔞(ω,t)‖²_{G⁻¹}` is
a.e.-measurable on the product `Ω × [0, T_*]` (and in `t` for each `ω`), the
initial energy is a.e.-measurable, and `μ` is s-finite (any probability
measure).  The uniform-in-cutoff expected `L²` curvature norm of the middle
sentence is the same interpolation abstraction as in
`derived_l2_curvature_bound` and is not restated in expectation.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory Filter

namespace RenewalGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Squaring the pathwise propagation estimate:
`sup_{t ∈ [0,T]} z(t)² ≤ 2 e^{2A}(z(0)² + I²)` when
`z(t) ≤ e^{A}(z(0) + I)` on `[0, T]` and `z ≥ 0`. -/
theorem pathwise_sup_sq_le {z : ℝ → ℝ} {T A I : ℝ} (hz0 : ∀ t, 0 ≤ z t)
    (hpath : ∀ t ∈ Set.Icc 0 T, z t ≤ Real.exp A * (z 0 + I)) :
    ⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z t ^ 2) ≤
      ENNReal.ofReal (2 * Real.exp (2 * A) * (z 0 ^ 2 + I ^ 2)) := by
  refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
  have h := hpath t ht
  have h0 := hz0 t
  have hsq : z t ^ 2 ≤ (Real.exp A * (z 0 + I)) ^ 2 := pow_le_pow_left₀ h0 h 2
  have hexp : Real.exp A ^ 2 = Real.exp (2 * A) := by rw [sq, ← Real.exp_add, two_mul]
  calc z t ^ 2 ≤ (Real.exp A * (z 0 + I)) ^ 2 := hsq
    _ = Real.exp (2 * A) * (z 0 + I) ^ 2 := by rw [mul_pow, hexp]
    _ ≤ Real.exp (2 * A) * (2 * (z 0 ^ 2 + I ^ 2)) := by
        gcongr
        nlinarith [sq_nonneg (z 0 - I)]
    _ = _ := by ring

/-- Cauchy–Schwarz in time for the Gram norm of a source on `[0, T]`:
`(∫₀ᵀ ‖f‖_H)² ≤ T ∫₀ᵀ ‖f‖²_H`. -/
theorem sq_setIntegral_gramNorm_le {T : ℝ} (hT : 0 ≤ T) (H : ℝ → F →L[ℝ] F)
    (S : ∀ t, GramSqrt (H t)) (f : ℝ → F)
    (hfL2 : MemLp (fun t => gramNorm (H t) (f t)) 2 (volume.restrict (Set.Icc 0 T))) :
    (∫ t in Set.Icc 0 T, gramNorm (H t) (f t)) ^ 2 ≤
      T * ∫ t in Set.Icc 0 T, gramNormSq (H t) (f t) := by
  set μ := volume.restrict (Set.Icc 0 T) with hμ
  have hfin : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hμuniv : μ.real Set.univ = T := by
    rw [hμ, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), sub_zero]
  have hg : Integrable (fun t => gramNorm (H t) (f t)) μ := hfL2.integrable (by norm_num)
  have hg2 : Integrable (fun t => gramNorm (H t) (f t) ^ 2) μ := by
    rw [memLp_two_iff_integrable_sq hfL2.1] at hfL2
    exact hfL2
  have hsq_eq : (fun t => gramNorm (H t) (f t) ^ 2) = fun t => gramNormSq (H t) (f t) := by
    funext t
    exact Real.sq_sqrt (gramNormSq_nonneg (S t) _)
  have hcs := sq_integral_le_measure_mul_integral_sq μ hg hg2
  rw [hμuniv, hsq_eq] at hcs
  exact hcs

/-- The Bochner time integral of the squared Gram norm as a Lebesgue integral. -/
theorem ofReal_setIntegral_gramNormSq {T : ℝ} (H : ℝ → F →L[ℝ] F)
    (S : ∀ t, GramSqrt (H t)) (f : ℝ → F)
    (hfL2 : MemLp (fun t => gramNorm (H t) (f t)) 2 (volume.restrict (Set.Icc 0 T))) :
    ENNReal.ofReal (∫ t in Set.Icc 0 T, gramNormSq (H t) (f t)) =
      ∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H t) (f t)) := by
  have hg2 : Integrable (fun t => gramNorm (H t) (f t) ^ 2) (volume.restrict (Set.Icc 0 T)) := by
    rw [memLp_two_iff_integrable_sq hfL2.1] at hfL2
    exact hfL2
  have hsq_eq : (fun t => gramNorm (H t) (f t) ^ 2) = fun t => gramNormSq (H t) (f t) := by
    funext t
    exact Real.sq_sqrt (gramNormSq_nonneg (S t) _)
  rw [hsq_eq] at hg2
  exact ofReal_integral_eq_lintegral_ofReal hg2
    (Eventually.of_forall fun t => gramNormSq_nonneg (S t) _)

/-- Pathwise source-energy budget in Lebesgue form: for the incidence
`f = 𝖳 𝔞 + r` with `Γ(t) ≤ Γ̄(t)`,
`∫⁻₀ᵀ ‖f‖²_H ≤ 2 ∫⁻₀ᵀ Γ̄ ‖𝔞‖²_{G⁻¹} + 2 ∫⁻₀ᵀ ‖r‖²_H`. -/
theorem lintegral_gramNormSq_source_le {T : ℝ} (G : ℝ → E →L[ℝ] E) (H : ℝ → F →L[ℝ] F)
    (R : ∀ t, GramSqrt (G t)) (S : ∀ t, GramSqrt (H t)) (Tr : ℝ → E →L[ℝ] F)
    (𝔞 : ℝ → E) (r f : ℝ → F) (Γbar : ℝ → ℝ)
    (hinc : ∀ t, f t = Tr t (𝔞 t) + r t) (hΓ0 : ∀ t, 0 ≤ Γbar t)
    (hΓ : ∀ t, amplification (R t) (S t) (Tr t) ≤ Γbar t)
    (hmeas : AEMeasurable (fun t => Γbar t * dualNormSq (R t) (𝔞 t))
      (volume.restrict (Set.Icc 0 T))) :
    (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H t) (f t))) ≤
      ENNReal.ofReal 2 *
          (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (Γbar t * dualNormSq (R t) (𝔞 t)))
        + ENNReal.ofReal 2 * (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H t) (r t))) := by
  have hd0 : ∀ t, 0 ≤ dualNormSq (R t) (𝔞 t) := fun t => by rw [dualNormSq_eq]; positivity
  have hpt : ∀ t, gramNormSq (H t) (f t) ≤
      2 * (Γbar t * dualNormSq (R t) (𝔞 t)) + 2 * gramNormSq (H t) (r t) := by
    intro t
    have h := source_gramNormSq_le (R t) (S t) (Tr t) (hinc t)
      (le_of_eq (mul_one (dualNormSq (R t) (𝔞 t))).symm)
    have := mul_le_mul_of_nonneg_right (hΓ t) (hd0 t)
    linarith
  have hm1 : AEMeasurable (fun t => ENNReal.ofReal (2 * (Γbar t * dualNormSq (R t) (𝔞 t))))
      (volume.restrict (Set.Icc 0 T)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_const.mul hmeas)
  have e1 : ∀ t, ENNReal.ofReal (2 * (Γbar t * dualNormSq (R t) (𝔞 t))) =
      ENNReal.ofReal 2 * ENNReal.ofReal (Γbar t * dualNormSq (R t) (𝔞 t)) := fun t =>
    ENNReal.ofReal_mul zero_le_two
  have e2 : ∀ t, ENNReal.ofReal (2 * gramNormSq (H t) (r t)) =
      ENNReal.ofReal 2 * ENNReal.ofReal (gramNormSq (H t) (r t)) := fun t =>
    ENNReal.ofReal_mul zero_le_two
  calc (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H t) (f t)))
      ≤ ∫⁻ t in Set.Icc 0 T, (ENNReal.ofReal (2 * (Γbar t * dualNormSq (R t) (𝔞 t)))
          + ENNReal.ofReal (2 * gramNormSq (H t) (r t))) := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_add (by have := hΓ0 t; have := hd0 t; positivity)
          (by have := gramNormSq_nonneg (S t) (r t); positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt t)
    _ = (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (2 * (Γbar t * dualNormSq (R t) (𝔞 t))))
          + (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (2 * gramNormSq (H t) (r t))) :=
        lintegral_add_left' hm1 _
    _ = (∫⁻ t in Set.Icc 0 T,
            ENNReal.ofReal 2 * ENNReal.ofReal (Γbar t * dualNormSq (R t) (𝔞 t)))
          + (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal 2 * ENNReal.ofReal (gramNormSq (H t) (r t))) := by
        simp_rw [e1, e2]
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- `cor:supp-stochastic-curvature`, `eq:supp-expected-curvature`: if the
pathwise propagation estimate `z(t) ≤ e^{A_*}(z(0) + ∫₀^{T_*} ‖f‖_H)` holds
on `[0, T_*]`, the forcing has the incidence `f = 𝖳 𝔞 + r^{src}` with the
target norm already the curvature-energy norm, `Γ_X(ω, t) ≤ Γ̄(t)`
deterministically and `𝔼 ‖𝔞(t)‖²_{G⁻¹} ≤ C(t) Δ(t)`, then
`𝔼 sup_{t ≤ T_*} z(t)² ≤ 2 e^{2A_*}[𝔼 z(0)² + 2 T_* ∫₀^{T_*} Γ̄ C Δ
  + 2 T_* 𝔼 ∫₀^{T_*} ‖r^{src}‖²_H]`. -/
theorem expected_curvature_energy_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [SFinite μ] {T A : ℝ} (hT : 0 ≤ T)
    (z : Ω → ℝ → ℝ) (G : Ω → ℝ → E →L[ℝ] E) (H : Ω → ℝ → F →L[ℝ] F)
    (R : ∀ ω t, GramSqrt (G ω t)) (S : ∀ ω t, GramSqrt (H ω t))
    (Tr : Ω → ℝ → E →L[ℝ] F) (𝔞 : Ω → ℝ → E) (r f : Ω → ℝ → F) (Γbar C Δ : ℝ → ℝ)
    (hz : ∀ ω t, 0 ≤ z ω t)
    (hpath : ∀ ω, ∀ t ∈ Set.Icc 0 T, z ω t ≤
      Real.exp A * (z ω 0 + ∫ s in Set.Icc 0 T, gramNorm (H ω s) (f ω s)))
    (hfL2 : ∀ ω, MemLp (fun s => gramNorm (H ω s) (f ω s)) 2 (volume.restrict (Set.Icc 0 T)))
    (hinc : ∀ ω t, f ω t = Tr ω t (𝔞 ω t) + r ω t)
    (hΓ0 : ∀ t, 0 ≤ Γbar t) (hΓ : ∀ ω t, amplification (R ω t) (S ω t) (Tr ω t) ≤ Γbar t)
    (hcert : ∀ t ∈ Set.Icc 0 T,
      (∫⁻ ω, ENNReal.ofReal (dualNormSq (R ω t) (𝔞 ω t)) ∂μ) ≤ ENNReal.ofReal (C t * Δ t))
    (hz0meas : AEMeasurable (fun ω => z ω 0) μ)
    (hmeas_t : ∀ ω, AEMeasurable (fun t => Γbar t * dualNormSq (R ω t) (𝔞 ω t))
      (volume.restrict (Set.Icc 0 T)))
    (hmeas : AEMeasurable (fun p : Ω × ℝ => Γbar p.2 * dualNormSq (R p.1 p.2) (𝔞 p.1 p.2))
      (μ.prod (volume.restrict (Set.Icc 0 T)))) :
    (∫⁻ ω, ⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z ω t ^ 2) ∂μ) ≤
      ENNReal.ofReal (2 * Real.exp (2 * A)) *
        ((∫⁻ ω, ENNReal.ofReal (z ω 0 ^ 2) ∂μ)
          + ENNReal.ofReal (2 * T) *
              (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (Γbar t * (C t * Δ t)))
          + ENNReal.ofReal (2 * T) *
              (∫⁻ ω, (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H ω t) (r ω t))) ∂μ)) := by
  set ν := volume.restrict (Set.Icc 0 T) with hν
  -- the two source processes
  set g₁ : Ω → ℝ≥0∞ := fun ω => ∫⁻ t, ENNReal.ofReal (Γbar t * dualNormSq (R ω t) (𝔞 ω t)) ∂ν
    with hg₁
  set g₂ : Ω → ℝ≥0∞ := fun ω => ∫⁻ t, ENNReal.ofReal (gramNormSq (H ω t) (r ω t)) ∂ν with hg₂
  -- Step 1: pathwise bound
  have hpw : ∀ ω, (⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z ω t ^ 2)) ≤
      ENNReal.ofReal (2 * Real.exp (2 * A)) *
        (ENNReal.ofReal (z ω 0 ^ 2) + ENNReal.ofReal (2 * T) * g₁ ω
          + ENNReal.ofReal (2 * T) * g₂ ω) := by
    intro ω
    set I := ∫ s in Set.Icc 0 T, gramNorm (H ω s) (f ω s) with hI
    have h1 := pathwise_sup_sq_le (hz ω) (hpath ω)
    have hcs := sq_setIntegral_gramNorm_le hT (H ω) (S ω) (f ω) (hfL2 ω)
    have hL := ofReal_setIntegral_gramNormSq (H ω) (S ω) (f ω) (hfL2 ω)
    have hL2 := lintegral_gramNormSq_source_le (T := T) (G ω) (H ω) (R ω) (S ω) (Tr ω) (𝔞 ω)
      (r ω) (f ω) Γbar (hinc ω) hΓ0 (hΓ ω) (hmeas_t ω)
    have hI2 : ENNReal.ofReal (I ^ 2) ≤
        ENNReal.ofReal (2 * T) * g₁ ω + ENNReal.ofReal (2 * T) * g₂ ω := by
      calc ENNReal.ofReal (I ^ 2)
          ≤ ENNReal.ofReal (T * ∫ t in Set.Icc 0 T, gramNormSq (H ω t) (f ω t)) :=
            ENNReal.ofReal_le_ofReal hcs
        _ = ENNReal.ofReal T *
              (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H ω t) (f ω t))) := by
            rw [ENNReal.ofReal_mul hT, hL]
        _ ≤ ENNReal.ofReal T * (ENNReal.ofReal 2 * g₁ ω + ENNReal.ofReal 2 * g₂ ω) := by
            gcongr
        _ = _ := by
            rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hT, mul_comm T 2]
    calc (⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z ω t ^ 2))
        ≤ ENNReal.ofReal (2 * Real.exp (2 * A) * (z ω 0 ^ 2 + I ^ 2)) := h1
      _ = ENNReal.ofReal (2 * Real.exp (2 * A)) *
            (ENNReal.ofReal (z ω 0 ^ 2) + ENNReal.ofReal (I ^ 2)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      _ ≤ ENNReal.ofReal (2 * Real.exp (2 * A)) *
            (ENNReal.ofReal (z ω 0 ^ 2) +
              (ENNReal.ofReal (2 * T) * g₁ ω + ENNReal.ofReal (2 * T) * g₂ ω)) := by
          gcongr
      _ = _ := by rw [add_assoc]
  -- measurability of the summands
  have hm0 : AEMeasurable (fun ω => ENNReal.ofReal (z ω 0 ^ 2)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hz0meas.pow_const 2)
  have hmg₁ : AEMeasurable g₁ μ :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hmeas).lintegral_prod_right'
  -- Step 2: Tonelli on the weighted dual-norm process
  have hΓsum : (∫⁻ ω, g₁ ω ∂μ) ≤
      ∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (Γbar t * (C t * Δ t)) := by
    have hswap := lintegral_lintegral_swap (μ := μ) (ν := ν)
      (f := fun ω t => ENNReal.ofReal (Γbar t * dualNormSq (R ω t) (𝔞 ω t)))
      (ENNReal.measurable_ofReal.comp_aemeasurable hmeas)
    simp only [hg₁]
    rw [hswap]
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).mpr
      (Eventually.of_forall fun t ht => ?_))
    calc (∫⁻ ω, ENNReal.ofReal (Γbar t * dualNormSq (R ω t) (𝔞 ω t)) ∂μ)
        = ENNReal.ofReal (Γbar t) * ∫⁻ ω, ENNReal.ofReal (dualNormSq (R ω t) (𝔞 ω t)) ∂μ := by
          simp_rw [ENNReal.ofReal_mul (hΓ0 t)]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Γbar t) * ENNReal.ofReal (C t * Δ t) := by
          gcongr
          exact hcert t ht
      _ = ENNReal.ofReal (Γbar t * (C t * Δ t)) := (ENNReal.ofReal_mul (hΓ0 t)).symm
  -- Step 3: integrate the pathwise bound over `ω`
  calc (∫⁻ ω, ⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z ω t ^ 2) ∂μ)
      ≤ ∫⁻ ω, ENNReal.ofReal (2 * Real.exp (2 * A)) *
          (ENNReal.ofReal (z ω 0 ^ 2) + ENNReal.ofReal (2 * T) * g₁ ω
            + ENNReal.ofReal (2 * T) * g₂ ω) ∂μ := lintegral_mono hpw
    _ = ENNReal.ofReal (2 * Real.exp (2 * A)) *
          ∫⁻ ω, (ENNReal.ofReal (z ω 0 ^ 2) + ENNReal.ofReal (2 * T) * g₁ ω
            + ENNReal.ofReal (2 * T) * g₂ ω) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 * Real.exp (2 * A)) *
          ((∫⁻ ω, ENNReal.ofReal (z ω 0 ^ 2) ∂μ)
            + ENNReal.ofReal (2 * T) * (∫⁻ ω, g₁ ω ∂μ)
            + ENNReal.ofReal (2 * T) * (∫⁻ ω, g₂ ω ∂μ)) := by
        have hm01 : AEMeasurable
            (fun ω => ENNReal.ofReal (z ω 0 ^ 2) + ENNReal.ofReal (2 * T) * g₁ ω) μ :=
          hm0.add (aemeasurable_const.mul hmg₁)
        rw [lintegral_add_left' hm01, lintegral_add_left' hm0,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by gcongr

/-- `cor:supp-stochastic-curvature` with the pathwise propagation estimate
derived from the finite propagation equation
`eq:main-curvature-propagation-writer` holding pathwise on `[0, T_*]`
(`curvature_energy_uniform_bound`, `thm:main-curvature-propagation`), with
`∫₀^{T_*} a ≤ A_*` deterministically; here `z(t) = √⟪y, M y⟫` and the target
Gram of the source is the curvature Gram `M`. -/
theorem expected_curvature_energy_bound_of_writer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {T A : ℝ} (hT : 0 ≤ T)
    (M M' K L : Ω → ℝ → F →L[ℝ] F) (y y' f : Ω → ℝ → F) (a : Ω → ℝ → ℝ)
    (hM : ∀ ω t, HasDerivAt (M ω) (M' ω t) t) (hy : ∀ ω t, HasDerivAt (y ω) (y' ω t) t)
    (hf : ∀ ω, Continuous (f ω)) (ha : ∀ ω, Continuous (a ω)) (ha0 : ∀ ω t, 0 ≤ a ω t)
    (hsymm : ∀ ω t x w, ⟪M ω t x, w⟫_ℝ = ⟪x, M ω t w⟫_ℝ)
    (hpos : ∀ ω t x, 0 ≤ ⟪x, M ω t x⟫_ℝ)
    (hwriter : ∀ ω t, y' ω t = (K ω t + L ω t) (y ω t) + f ω t)
    (hskew : ∀ ω t x, ⟪M ω t x, K ω t x⟫_ℝ = 0)
    (hgrowth : ∀ ω t x, ⟪x, M' ω t x⟫_ℝ + 2 * ⟪M ω t x, L ω t x⟫_ℝ ≤
      2 * a ω t * ⟪x, M ω t x⟫_ℝ)
    (hA : ∀ ω, ∫ s in (0:ℝ)..T, a ω s ≤ A)
    (G : Ω → ℝ → E →L[ℝ] E) (R : ∀ ω t, GramSqrt (G ω t)) (S : ∀ ω t, GramSqrt (M ω t))
    (Tr : Ω → ℝ → E →L[ℝ] F) (𝔞 : Ω → ℝ → E) (r : Ω → ℝ → F) (Γbar C Δ : ℝ → ℝ)
    (hfL2 : ∀ ω, MemLp (fun s => gramNorm (M ω s) (f ω s)) 2 (volume.restrict (Set.Icc 0 T)))
    (hinc : ∀ ω t, f ω t = Tr ω t (𝔞 ω t) + r ω t)
    (hΓ0 : ∀ t, 0 ≤ Γbar t) (hΓ : ∀ ω t, amplification (R ω t) (S ω t) (Tr ω t) ≤ Γbar t)
    (hcert : ∀ t ∈ Set.Icc 0 T,
      (∫⁻ ω, ENNReal.ofReal (dualNormSq (R ω t) (𝔞 ω t)) ∂μ) ≤ ENNReal.ofReal (C t * Δ t))
    (hz0meas : AEMeasurable (fun ω => gramEnergy (M ω) (y ω) 0) μ)
    (hmeas_t : ∀ ω, AEMeasurable (fun t => Γbar t * dualNormSq (R ω t) (𝔞 ω t))
      (volume.restrict (Set.Icc 0 T)))
    (hmeas : AEMeasurable (fun p : Ω × ℝ => Γbar p.2 * dualNormSq (R p.1 p.2) (𝔞 p.1 p.2))
      (μ.prod (volume.restrict (Set.Icc 0 T)))) :
    (∫⁻ ω, ⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (gramEnergy (M ω) (y ω) t ^ 2) ∂μ) ≤
      ENNReal.ofReal (2 * Real.exp (2 * A)) *
        ((∫⁻ ω, ENNReal.ofReal (gramEnergy (M ω) (y ω) 0 ^ 2) ∂μ)
          + ENNReal.ofReal (2 * T) *
              (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (Γbar t * (C t * Δ t)))
          + ENNReal.ofReal (2 * T) *
              (∫⁻ ω, (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (M ω t) (r ω t))) ∂μ)) := by
  refine expected_curvature_energy_bound μ hT (fun ω t => gramEnergy (M ω) (y ω) t) G M R S Tr 𝔞
    r f Γbar C Δ (fun ω t => Real.sqrt_nonneg _) ?_ hfL2 hinc hΓ0 hΓ hcert hz0meas hmeas_t hmeas
  intro ω t ht
  have hbound := curvature_energy_uniform_bound (M ω) (M' ω) (K ω) (L ω) (y ω) (y' ω) (f ω)
    (a ω) (hM ω) (hy ω) (hf ω) (ha ω) (ha0 ω) (hsymm ω) (hpos ω) (hwriter ω) (hskew ω)
    (hgrowth ω) hT (le_refl _) (hA ω) (le_refl (∫ s in (0:ℝ)..T, gramEnergy (M ω) (f ω) s))
    t ht
  have hint : ∫ s in (0:ℝ)..T, gramEnergy (M ω) (f ω) s =
      ∫ s in Set.Icc 0 T, gramNorm (M ω s) (f ω s) := by
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
    rfl
  rw [hint] at hbound
  exact hbound

/-- `eq:supp-pathwise-source-budget`: for a countable cofinal sequence of
cutoffs with almost surely bounded initial energies and summable expected
integrated source energies, Tonelli makes the realized integrated source
energies uniformly bounded almost surely, and the pathwise propagation
estimate (uniform growth budget `A_*`) gives `sup_X sup_{t ≤ T_*} z_X(t) < ∞`
almost surely. -/
theorem pathwise_curvature_upgrade {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T A : ℝ} (hT : 0 ≤ T)
    (z : ℕ → Ω → ℝ → ℝ) (H : ℕ → Ω → ℝ → F →L[ℝ] F)
    (S : ∀ n ω t, GramSqrt (H n ω t)) (f : ℕ → Ω → ℝ → F)
    (hpath : ∀ n ω, ∀ t ∈ Set.Icc 0 T, z n ω t ≤
      Real.exp A * (z n ω 0 + ∫ s in Set.Icc 0 T, gramNorm (H n ω s) (f n ω s)))
    (hfL2 : ∀ n ω,
      MemLp (fun s => gramNorm (H n ω s) (f n ω s)) 2 (volume.restrict (Set.Icc 0 T)))
    (hz0 : ∀ᵐ ω ∂μ, ∃ Z, ∀ n, z n ω 0 ≤ Z)
    (hmeas : ∀ n, AEMeasurable
      (fun ω => ∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H n ω t) (f n ω t))) μ)
    (hsum : (∑' n, ∫⁻ ω, (∫⁻ t in Set.Icc 0 T,
      ENNReal.ofReal (gramNormSq (H n ω t) (f n ω t))) ∂μ) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ B, ∀ n, ∀ t ∈ Set.Icc 0 T, z n ω t ≤ B := by
  set g : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H n ω t) (f n ω t)) with hg
  -- Tonelli: the sum of the integrated source energies is finite a.s.
  have htsum : (∫⁻ ω, ∑' n, g n ω ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hmeas]
    exact hsum
  have hae : ∀ᵐ ω ∂μ, (∑' n, g n ω) < ∞ :=
    ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) htsum
  filter_upwards [hae, hz0] with ω hω hZ
  obtain ⟨Z, hZ⟩ := hZ
  set Ssum : ℝ := (∑' n, g n ω).toReal with hS
  refine ⟨Real.exp A * (Z + Real.sqrt (T * Ssum)), fun n t ht => ?_⟩
  -- each integrated source energy is at most the sum
  have hgn : g n ω ≤ ∑' n, g n ω := ENNReal.le_tsum n
  have hcs := sq_setIntegral_gramNorm_le hT (H n ω) (S n ω) (f n ω) (hfL2 n ω)
  have hL := ofReal_setIntegral_gramNormSq (H n ω) (S n ω) (f n ω) (hfL2 n ω)
  have hint_le : ∫ t in Set.Icc 0 T, gramNormSq (H n ω t) (f n ω t) ≤ Ssum := by
    rw [hS, ← ENNReal.ofReal_le_iff_le_toReal hω.ne, hL]
    exact hgn
  have hI0 : 0 ≤ ∫ s in Set.Icc 0 T, gramNorm (H n ω s) (f n ω s) :=
    integral_nonneg fun s => Real.sqrt_nonneg _
  have hI : ∫ s in Set.Icc 0 T, gramNorm (H n ω s) (f n ω s) ≤ Real.sqrt (T * Ssum) := by
    rw [← Real.sqrt_sq hI0]
    exact Real.sqrt_le_sqrt (hcs.trans (mul_le_mul_of_nonneg_left hint_le hT))
  calc z n ω t ≤ Real.exp A * (z n ω 0 + ∫ s in Set.Icc 0 T, gramNorm (H n ω s) (f n ω s)) :=
        hpath n ω t ht
    _ ≤ Real.exp A * (Z + Real.sqrt (T * Ssum)) := by gcongr; exact hZ n

/-- Last assertion of `cor:supp-stochastic-curvature`: under
`eq:supp-pathwise-source-budget` and pathwise uniform interpolation, lapse
and boundary budgets (the abstraction of `derived_l2_curvature_bound`),
`sup_X ‖R_X‖_{L²(K)} < ∞` almost surely. -/
theorem pathwise_l2_curvature_upgrade {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T A : ℝ} (hT : 0 ≤ T)
    (z : ℕ → Ω → ℝ → ℝ) (H : ℕ → Ω → ℝ → F →L[ℝ] F)
    (S : ∀ n ω t, GramSqrt (H n ω t)) (f : ℕ → Ω → ℝ → F)
    (hz : ∀ n ω t, 0 ≤ z n ω t)
    (hpath : ∀ n ω, ∀ t ∈ Set.Icc 0 T, z n ω t ≤
      Real.exp A * (z n ω 0 + ∫ s in Set.Icc 0 T, gramNorm (H n ω s) (f n ω s)))
    (hfL2 : ∀ n ω,
      MemLp (fun s => gramNorm (H n ω s) (f n ω s)) 2 (volume.restrict (Set.Icc 0 T)))
    (hz0 : ∀ᵐ ω ∂μ, ∃ Z, ∀ n, z n ω 0 ≤ Z)
    (hmeas : ∀ n, AEMeasurable
      (fun ω => ∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H n ω t) (f n ω t))) μ)
    (hsum : (∑' n, ∫⁻ ω, (∫⁻ t in Set.Icc 0 T,
      ENNReal.ofReal (gramNormSq (H n ω t) (f n ω t))) ∂μ) ≠ ∞)
    -- pathwise interpolation, lapse and boundary budgets
    (ρ N : ℕ → Ω → ℝ → ℝ) (RL2 : ℕ → Ω → ℝ) {Nstar CI Cζ : ℝ} (hCI : 0 ≤ CI)
    (hρ : ∀ n ω, ∀ t ∈ Set.Icc 0 T, 0 ≤ ρ n ω t ∧ ρ n ω t ≤ CI * z n ω t)
    (hN : ∀ n ω, ∀ t ∈ Set.Icc 0 T, 0 ≤ N n ω t ∧ N n ω t ≤ Nstar)
    (hint : ∀ n ω, IntervalIntegrable (fun t => N n ω t * ρ n ω t ^ 2) volume 0 T)
    (hR : ∀ n ω, RL2 n ω ≤ Real.sqrt (∫ t in (0:ℝ)..T, N n ω t * ρ n ω t ^ 2) + Cζ) :
    ∀ᵐ ω ∂μ, ∃ B, ∀ n, RL2 n ω ≤ B := by
  filter_upwards [pathwise_curvature_upgrade μ hT z H S f hpath hfL2 hz0 hmeas hsum]
    with ω hB
  obtain ⟨B, hB⟩ := hB
  refine ⟨CI * Real.sqrt (Nstar * T) * max B 0 + Cζ, fun n => ?_⟩
  exact derived_l2_curvature_bound (z n ω) (ρ n ω) (N n ω) hT hCI (le_max_right _ _)
    (fun t ht => (hB n t ht).trans (le_max_left _ _)) (fun t _ => hz n ω t) (hρ n ω) (hN n ω)
    (hint n ω) (hR n ω)

end RenewalGeometry
