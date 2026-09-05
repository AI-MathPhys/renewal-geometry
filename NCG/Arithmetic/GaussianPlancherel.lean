/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.MassFlux

/-!
# Exact Gaussian Plancherel identity
  (`thm:plancherel`, arithmetic monograph)

Stage 1: the Gaussian window `G_A` and its complex-shift transform
`∫ e^{zr} G_A(u−r) dr = e^{zu} e^{Az²}`, with the integrability and
uniform-majorant estimates used downstream.
-/

open MeasureTheory FourierTransform Complex Filter
open scoped InnerProductSpace

namespace NCG

/-- The Gaussian window `G_A(v) = (4πA)^{-1/2} e^{−v²/(4A)}`. -/
noncomputable def gaussKer (A v : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * A))⁻¹ * Real.exp (-v ^ 2 / (4 * A))

lemma gaussKer_nonneg {A : ℝ} (v : ℝ) : 0 ≤ gaussKer A v := by
  rw [gaussKer]
  positivity

/-- The quadratic-form decomposition of the shifted Gaussian
integrand. -/
lemma gaussKer_cexp_eq {A : ℝ} (_hA : 0 < A) (z : ℂ) (u r : ℝ) :
    Complex.exp (z * r) * (gaussKer A (u - r) : ℂ)
      = ((Real.sqrt (4 * Real.pi * A) : ℝ) : ℂ)⁻¹
        * Complex.exp ((-(1 / (4 * A)) : ℂ) * r ^ 2
            + (z + (u / (2 * A) : ℝ)) * r
            + (-(u ^ 2 / (4 * A)) : ℝ)) := by
  rw [gaussKer]
  push_cast
  rw [show ((-(1 / (4 * A)) : ℂ) * (r : ℂ) ^ 2
      + (z + (u : ℂ) / (2 * A)) * (r : ℂ)
      + -((u : ℂ) ^ 2 / (4 * A)))
    = z * (r : ℂ) + (-((u : ℂ) - r) ^ 2 / (4 * A)) from by ring,
    Complex.exp_add]
  ring

/-- Complex-shift Gaussian transform:
`∫ e^{zr} G_A(u−r) dr = e^{zu} e^{Az²}`. -/
theorem gaussian_shift {A : ℝ} (hA : 0 < A) (z : ℂ) (u : ℝ) :
    (∫ r : ℝ, Complex.exp (z * r) * (gaussKer A (u - r) : ℂ))
      = Complex.exp (z * u) * Complex.exp (A * z ^ 2) := by
  have hb : ((-(1 / (4 * A)) : ℂ)).re < 0 := by
    rw [show (-(1 / (4 * A)) : ℂ) = ((-(1 / (4 * A)) : ℝ) : ℂ) from by
        push_cast
        ring,
      Complex.ofReal_re]
    have h0 : (0 : ℝ) < 1 / (4 * A) := by positivity
    linarith
  simp only [gaussKer_cexp_eq hA z]
  rw [MeasureTheory.integral_const_mul,
    integral_cexp_quadratic hb _ _]
  -- normalize the prefactor and the exponent
  have hpre : ((Real.sqrt (4 * Real.pi * A) : ℝ) : ℂ)⁻¹
      * ((Real.pi : ℂ) / -(-(1 / (4 * A)) : ℂ)) ^ (1 / 2 : ℂ) = 1 := by
    have h1 : ((Real.pi : ℂ) / -(-(1 / (4 * A)) : ℂ))
        = ((4 * Real.pi * A : ℝ) : ℂ) := by
      push_cast
      rw [neg_neg]
      field_simp
    rw [h1]
    have h2 : ((4 * Real.pi * A : ℝ) : ℂ) ^ (1 / 2 : ℂ)
        = ((Real.sqrt (4 * Real.pi * A) : ℝ) : ℂ) := by
      rw [show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) from by norm_num,
        ← Complex.ofReal_cpow (by positivity), Real.sqrt_eq_rpow]
    rw [h2, inv_mul_cancel₀ (by
      refine Complex.ofReal_ne_zero.mpr ?_
      positivity)]
  have hexp : ((-(u ^ 2 / (4 * A)) : ℝ) : ℂ)
      - (z + ((u / (2 * A) : ℝ) : ℂ)) ^ 2
          / (4 * (-(1 / (4 * A)) : ℂ))
      = z * u + A * z ^ 2 := by
    have hA' : ((A : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hA.ne'
    push_cast
    field_simp
    ring
  calc ((Real.sqrt (4 * Real.pi * A) : ℝ) : ℂ)⁻¹
      * (((Real.pi : ℂ) / -(-(1 / (4 * A)) : ℂ)) ^ (1 / 2 : ℂ)
        * Complex.exp (((-(u ^ 2 / (4 * A)) : ℝ) : ℂ)
          - (z + ((u / (2 * A) : ℝ) : ℂ)) ^ 2
              / (4 * (-(1 / (4 * A)) : ℂ))))
      = (((Real.sqrt (4 * Real.pi * A) : ℝ) : ℂ)⁻¹
          * ((Real.pi : ℂ) / -(-(1 / (4 * A)) : ℂ)) ^ (1 / 2 : ℂ))
        * Complex.exp (((-(u ^ 2 / (4 * A)) : ℝ) : ℂ)
          - (z + ((u / (2 * A) : ℝ) : ℂ)) ^ 2
              / (4 * (-(1 / (4 * A)) : ℂ))) := by ring
    _ = Complex.exp (z * u) * Complex.exp ((A : ℂ) * z ^ 2) := by
        rw [hpre, one_mul, hexp, Complex.exp_add]

/-- Integrability of the shifted Gaussian integrand. -/
theorem gaussian_shift_integrable {A : ℝ} (hA : 0 < A) (z : ℂ)
    (u : ℝ) :
    Integrable fun r : ℝ =>
      Complex.exp (z * r) * (gaussKer A (u - r) : ℂ) := by
  have hb : ((-(1 / (4 * A)) : ℂ)).re < 0 := by
    rw [show (-(1 / (4 * A)) : ℂ) = ((-(1 / (4 * A)) : ℝ) : ℂ) from by
        push_cast
        ring,
      Complex.ofReal_re]
    have h0 : (0 : ℝ) < 1 / (4 * A) := by positivity
    linarith
  simp only [gaussKer_cexp_eq hA z]
  exact (integrable_cexp_quadratic' hb _ _).const_mul _

/-- The uniform Gaussian majorant: for `u` in a window `[0, L]`,
`G_A(u−r) ≤ (4πA)^{-1/2} e^{L²/(4A)} e^{−r²/(8A)}`. -/
theorem gaussKer_le_majorant {A L : ℝ} (hA : 0 < A) {u : ℝ}
    (hu0 : 0 ≤ u) (huL : u ≤ L) (r : ℝ) :
    gaussKer A (u - r)
      ≤ (Real.sqrt (4 * Real.pi * A))⁻¹
        * Real.exp (L ^ 2 / (4 * A)) * Real.exp (-r ^ 2 / (8 * A)) := by
  rw [gaussKer]
  have hmerge : (Real.sqrt (4 * Real.pi * A))⁻¹
        * Real.exp (L ^ 2 / (4 * A)) * Real.exp (-r ^ 2 / (8 * A))
      = (Real.sqrt (4 * Real.pi * A))⁻¹
        * Real.exp (L ^ 2 / (4 * A) + -r ^ 2 / (8 * A)) := by
    rw [Real.exp_add]
    ring
  rw [hmerge]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_exp.mpr ?_
  have h1 : r ^ 2 / 2 - u ^ 2 ≤ (u - r) ^ 2 := by
    nlinarith [sq_nonneg (2 * u - r)]
  have h2 : u ^ 2 ≤ L ^ 2 := by nlinarith
  rw [div_add_div _ _ (by positivity : (4 * A : ℝ) ≠ 0)
    (by positivity : (8 * A : ℝ) ≠ 0)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hA2 : (0 : ℝ) < A ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hA2.le,
    mul_le_mul_of_nonneg_left h2 hA2.le]

/-- Gaussians beat linear exponents. -/
theorem integrable_gauss_lin {A : ℝ} (hA : 0 < A) (c : ℝ) :
    Integrable fun r : ℝ => Real.exp (c * r - r ^ 2 / (8 * A)) := by
  have hb : (0 : ℝ) < ((1 / (8 * A) : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  have h1 := (integrable_cexp_quadratic (b := ((1 / (8 * A) : ℝ) : ℂ))
    hb ((c : ℝ) : ℂ) 0).norm
  refine h1.congr ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only []
  rw [Complex.norm_exp]
  congr 1
  rw [show (-((1 / (8 * A) : ℝ) : ℂ) * (r : ℂ) ^ 2
      + ((c : ℝ) : ℂ) * r + 0)
    = ((c * r - r ^ 2 / (8 * A) : ℝ) : ℂ) from by push_cast; ring,
    Complex.ofReal_re]

section Port

variable {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) (A τ : ℝ)

open ArithmeticFunction in
open scoped Classical in
/-- The cutoff-matched transform
`𝔏^△(s) = Σ_{n≤X} χ(n)Λ(n)e^{−s·log n} − δ_χ ∫₀^{log X} e^{(1−s)u} du`. -/
noncomputable def cutoffL (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (X + 1),
    χ n * (vonMangoldt n : ℂ) * Complex.exp (-s * Real.log n))
  - (if χ = 1 then 1 else 0)
    * ∫ u in Set.Ioc (0 : ℝ) (Real.log X), Complex.exp ((1 - s) * u)

open ArithmeticFunction in
open scoped Classical in
/-- The cutoff-matched Gaussian travelling port `𝒢^△(r)`. -/
noncomputable def gaussPort (r : ℝ) : ℂ :=
  Complex.exp ((τ : ℂ) * r * Complex.I)
    * ((∑ n ∈ Finset.range (X + 1),
        χ n * (vonMangoldt n : ℂ)
          * Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
          * gaussKer A (Real.log n - r))
      - (if χ = 1 then 1 else 0)
        * ∫ u in Set.Ioc (0 : ℝ) (Real.log X),
            Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
              * Real.exp u * gaussKer A (u - r))

end Port

section ContinuousPart

variable {A L : ℝ}

/-- Uncurried integrability of the windowed continuous-part
integrand. -/
theorem cont_uncurry_integrable (hA : 0 < A) (g : ℝ → ℂ)
    (hg : Continuous g) (z : ℂ) :
    Integrable
      (Function.uncurry fun r u : ℝ =>
        Complex.exp (z * r) * (g u * (gaussKer A (u - r) : ℂ)))
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) L))) := by
  classical
  set μL : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) L) with hμL
  haveI : IsFiniteMeasure μL := by
    refine ⟨?_⟩
    rw [hμL, Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  obtain ⟨Cg, hCg⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn
      hg.continuousOn
  -- uncurried integrability
  have hk : Integrable fun r : ℝ =>
      Real.exp (z.re * r - r ^ 2 / (8 * A)) :=
    integrable_gauss_lin hA z.re
  have hprod : Integrable
      (fun p : ℝ × ℝ => Real.exp (z.re * p.1 - p.1 ^ 2 / (8 * A))
        * (1 : ℝ)) (volume.prod μL) :=
    hk.mul_prod (integrable_const 1)
  have huncurry : Integrable
      (Function.uncurry fun r u : ℝ =>
        Complex.exp (z * r) * (g u * (gaussKer A (u - r) : ℂ)))
      (volume.prod μL) := by
    refine ((hprod.const_mul
      ((max Cg 0) * ((Real.sqrt (4 * Real.pi * A))⁻¹
        * Real.exp (L ^ 2 / (4 * A))))).mono' ?_ ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine Continuous.mul ?_ (Continuous.mul (hg.comp continuous_snd) ?_)
      · exact Complex.continuous_exp.comp
          (continuous_const.mul
            (Complex.continuous_ofReal.comp continuous_fst))
      · refine Complex.continuous_ofReal.comp ?_
        refine Continuous.mul continuous_const ?_
        exact Real.continuous_exp.comp (by fun_prop)
    · have h2 : ∀ᵐ u ∂μL, u ∈ Set.Ioc (0 : ℝ) L := by
        rw [hμL]
        exact ae_restrict_mem measurableSet_Ioc
      filter_upwards [(MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := volume) (ν := μL)).ae h2] with p hp
      obtain ⟨hp0, hpL⟩ := hp
      have hzre : ‖Complex.exp (z * (p.1 : ℂ))‖
          = Real.exp (z.re * p.1) := by
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re]
      have hgb : ‖g p.2‖ ≤ max Cg 0 :=
        le_max_of_le_left (hCg p.2 ⟨hp0.le, hpL⟩)
      have hker : ‖((gaussKer A (p.2 - p.1) : ℝ) : ℂ)‖
          ≤ (Real.sqrt (4 * Real.pi * A))⁻¹
            * Real.exp (L ^ 2 / (4 * A))
            * Real.exp (-p.1 ^ 2 / (8 * A)) := by
        rw [Complex.norm_real,
          Real.norm_of_nonneg (gaussKer_nonneg _)]
        exact gaussKer_le_majorant hA hp0.le hpL p.1
      calc ‖Function.uncurry (fun r u : ℝ => Complex.exp (z * r)
            * (g u * (gaussKer A (u - r) : ℂ))) p‖
          = ‖Complex.exp (z * (p.1 : ℂ))‖ * (‖g p.2‖
              * ‖((gaussKer A (p.2 - p.1) : ℝ) : ℂ)‖) := by
            rw [Function.uncurry]
            simp only [norm_mul]
        _ ≤ Real.exp (z.re * p.1) * ((max Cg 0)
              * ((Real.sqrt (4 * Real.pi * A))⁻¹
                * Real.exp (L ^ 2 / (4 * A))
                * Real.exp (-p.1 ^ 2 / (8 * A)))) := by
            rw [hzre]
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
            exact mul_le_mul hgb hker (norm_nonneg _)
              (le_max_right _ _)
        _ = (max Cg 0) * ((Real.sqrt (4 * Real.pi * A))⁻¹
              * Real.exp (L ^ 2 / (4 * A)))
            * (Real.exp (z.re * p.1 - p.1 ^ 2 / (8 * A)) * 1) := by
            rw [mul_one,
              show z.re * p.1 - p.1 ^ 2 / (8 * A)
                = z.re * p.1 + -p.1 ^ 2 / (8 * A) from by ring,
              Real.exp_add]
            ring
  exact huncurry

/-- Fubini–shift for the windowed continuous part: the `z`-transform
of `r ↦ ∫₀^L g(u)G_A(u−r) du` factors through the window. -/
theorem cont_swap (hA : 0 < A) (g : ℝ → ℂ)
    (hg : Continuous g) (z : ℂ) :
    (∫ r : ℝ, Complex.exp (z * r)
        * ∫ u in Set.Ioc (0 : ℝ) L, g u * (gaussKer A (u - r) : ℂ))
      = (∫ u in Set.Ioc (0 : ℝ) L,
          g u * Complex.exp (z * u)) * Complex.exp (A * z ^ 2) := by
  classical
  have huncurry := cont_uncurry_integrable (L := L) hA g hg z
  -- pull the exponential inside and swap
  have hswap : (∫ r : ℝ, Complex.exp (z * r)
      * ∫ u in Set.Ioc (0 : ℝ) L, g u * (gaussKer A (u - r) : ℂ))
      = ∫ u in Set.Ioc (0 : ℝ) L, ∫ r : ℝ,
          Complex.exp (z * r) * (g u * (gaussKer A (u - r) : ℂ)) := by
    simp_rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_integral_swap huncurry
  rw [hswap]
  have hinner : ∀ u : ℝ, (∫ r : ℝ,
      Complex.exp (z * r) * (g u * (gaussKer A (u - r) : ℂ)))
      = g u * Complex.exp (z * u) * Complex.exp (A * z ^ 2) := by
    intro u
    have h1 : ∀ r : ℝ, Complex.exp (z * r)
        * (g u * (gaussKer A (u - r) : ℂ))
        = g u * (Complex.exp (z * r) * (gaussKer A (u - r) : ℂ)) := by
      intro r
      ring
    simp_rw [h1]
    rw [MeasureTheory.integral_const_mul, gaussian_shift hA z u]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    (fun u _ => hinner u), MeasureTheory.integral_mul_const]

/-- Integrability of the transformed continuous part. -/
theorem cont_integrable (hA : 0 < A) (g : ℝ → ℂ)
    (hg : Continuous g) (z : ℂ) :
    Integrable fun r : ℝ => Complex.exp (z * r)
      * ∫ u in Set.Ioc (0 : ℝ) L, g u * (gaussKer A (u - r) : ℂ) := by
  have h1 := (cont_uncurry_integrable (L := L) hA g hg z).integral_prod_left
  refine h1.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.uncurry]
  rw [MeasureTheory.integral_const_mul]

end ContinuousPart

section Transform

open ArithmeticFunction

variable {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) {A : ℝ}
  (τ σ : ℝ)

set_option maxHeartbeats 1000000 in
-- long elaboration through the phase-merging rewrites
open scoped Classical in
/-- Pointwise transform of the weighted port: for every real `t`,
`∫ e^{−itr} e^{−σr} 𝒢^△(r) dr = e^{A z_t²} 𝔏^△(1/2+σ+it)` with
`z_t = −σ + (τ−t)i`. -/
theorem port_transform (hA : 0 < A) (t : ℝ) :
    (∫ r : ℝ, Complex.exp (-(t : ℂ) * r * Complex.I)
        * (Complex.exp (-(σ : ℂ) * r) * gaussPort χ X A τ r))
      = Complex.exp ((A : ℂ)
          * (-(σ : ℂ) + ((τ : ℂ) - t) * Complex.I) ^ 2)
        * cutoffL χ X (1 / 2 + (σ : ℂ) + (t : ℂ) * Complex.I) := by
  classical
  set L : ℝ := Real.log X with hLdef
  set zt : ℂ := -(σ : ℂ) + ((τ : ℂ) - t) * Complex.I with hzt
  set st : ℂ := 1 / 2 + (σ : ℂ) + (t : ℂ) * Complex.I with hst
  set g : ℝ → ℂ := fun u =>
    Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
      * ((Real.exp u : ℝ) : ℂ) with hg
  have hgc : Continuous g := by
    rw [hg]
    have h1 : Continuous fun u : ℝ =>
        Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u) :=
      Complex.continuous_exp.comp
        (continuous_const.mul
          (Complex.continuous_ofReal))
    exact h1.mul (Complex.continuous_ofReal.comp Real.continuous_exp)
  -- merge the three phases pointwise
  have hpt : ∀ r : ℝ,
      Complex.exp (-(t : ℂ) * r * Complex.I)
          * (Complex.exp (-(σ : ℂ) * r) * gaussPort χ X A τ r)
        = (∑ n ∈ Finset.range (X + 1),
            χ n * (vonMangoldt n : ℂ)
              * Complex.exp
                  (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
              * (Complex.exp (zt * r)
                * (gaussKer A (Real.log n - r) : ℂ)))
          - (if χ = 1 then 1 else 0)
            * (Complex.exp (zt * r)
              * ∫ u in Set.Ioc (0 : ℝ) L,
                  g u * (gaussKer A (u - r) : ℂ)) := by
    intro r
    rw [gaussPort]
    have hz : Complex.exp (-(t : ℂ) * r * Complex.I)
        * (Complex.exp (-(σ : ℂ) * r)
          * Complex.exp ((τ : ℂ) * r * Complex.I))
        = Complex.exp (zt * r) := by
      rw [← Complex.exp_add, ← Complex.exp_add, hzt]
      congr 1
      ring
    rw [show Complex.exp (-(t : ℂ) * r * Complex.I)
        * (Complex.exp (-(σ : ℂ) * r)
          * (Complex.exp ((τ : ℂ) * r * Complex.I)
            * ((∑ n ∈ Finset.range (X + 1),
                χ n * (vonMangoldt n : ℂ)
                  * Complex.exp
                      (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
                  * gaussKer A (Real.log n - r))
              - (if χ = 1 then 1 else 0)
                * ∫ u in Set.Ioc (0 : ℝ) L,
                    Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
                      * Real.exp u * gaussKer A (u - r))))
      = (Complex.exp (-(t : ℂ) * r * Complex.I)
          * (Complex.exp (-(σ : ℂ) * r)
            * Complex.exp ((τ : ℂ) * r * Complex.I)))
        * ((∑ n ∈ Finset.range (X + 1),
            χ n * (vonMangoldt n : ℂ)
              * Complex.exp
                  (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
              * gaussKer A (Real.log n - r))
          - (if χ = 1 then 1 else 0)
            * ∫ u in Set.Ioc (0 : ℝ) L,
                Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
                  * Real.exp u * gaussKer A (u - r)) from by ring,
      hz, mul_sub, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      ring
    · rw [show Complex.exp (zt * r)
          * ((if χ = 1 then 1 else 0)
            * ∫ u in Set.Ioc (0 : ℝ) L,
                Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
                  * Real.exp u * gaussKer A (u - r))
        = (if χ = 1 then 1 else 0)
          * (Complex.exp (zt * r)
            * ∫ u in Set.Ioc (0 : ℝ) L,
                Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
                  * Real.exp u * gaussKer A (u - r)) from by ring]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  -- split and evaluate
  have hint_atomic : ∀ n ∈ Finset.range (X + 1),
      Integrable fun r : ℝ =>
        χ n * (vonMangoldt n : ℂ)
          * Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
          * (Complex.exp (zt * r)
            * (gaussKer A (Real.log n - r) : ℂ)) := fun n _ =>
    (gaussian_shift_integrable hA zt (Real.log n)).const_mul _
  have hint_sum : Integrable fun r : ℝ =>
      ∑ n ∈ Finset.range (X + 1),
        χ n * (vonMangoldt n : ℂ)
          * Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
          * (Complex.exp (zt * r)
            * (gaussKer A (Real.log n - r) : ℂ)) :=
    integrable_finsetSum _ hint_atomic
  have hint_cont : Integrable fun r : ℝ =>
      (if χ = 1 then (1 : ℂ) else 0)
        * (Complex.exp (zt * r)
          * ∫ u in Set.Ioc (0 : ℝ) L, g u * (gaussKer A (u - r) : ℂ)) :=
    (cont_integrable (L := L) hA g hgc zt).const_mul _
  rw [MeasureTheory.integral_sub hint_sum hint_cont,
    MeasureTheory.integral_finsetSum _ hint_atomic,
    MeasureTheory.integral_const_mul]
  have hatom : ∀ n ∈ Finset.range (X + 1),
      (∫ r : ℝ, χ n * (vonMangoldt n : ℂ)
          * Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
          * (Complex.exp (zt * r)
            * (gaussKer A (Real.log n - r) : ℂ)))
        = χ n * (vonMangoldt n : ℂ)
            * Complex.exp (-st * Real.log n)
            * Complex.exp ((A : ℂ) * zt ^ 2) := by
    intro n _
    rw [MeasureTheory.integral_const_mul,
      gaussian_shift hA zt (Real.log n),
      show χ n * (vonMangoldt n : ℂ)
          * Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
          * (Complex.exp (zt * Real.log n)
            * Complex.exp ((A : ℂ) * zt ^ 2))
        = χ n * (vonMangoldt n : ℂ)
          * (Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
            * Complex.exp (zt * Real.log n))
          * Complex.exp ((A : ℂ) * zt ^ 2) from by ring,
      ← Complex.exp_add,
      show -(1 / 2 + (τ : ℂ) * Complex.I) * (Real.log n : ℂ)
          + zt * (Real.log n : ℂ)
        = -st * (Real.log n : ℂ) from by
        rw [hzt, hst]
        ring]
  rw [Finset.sum_congr rfl hatom, cont_swap hA g hgc zt]
  have hgu : ∀ u ∈ Set.Ioc (0 : ℝ) L,
      g u * Complex.exp (zt * u)
        = Complex.exp ((1 - st) * u) := by
    intro u _
    rw [hg]
    simp only []
    rw [show ((Real.exp u : ℝ) : ℂ) = Complex.exp (u : ℂ) from
        Complex.ofReal_exp u,
      show Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
            * Complex.exp (u : ℂ) * Complex.exp (zt * u)
          = Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u
              + (u : ℂ) + zt * u) from by
        rw [Complex.exp_add, Complex.exp_add],
      show -(1 / 2 + (τ : ℂ) * Complex.I) * (u : ℂ) + (u : ℂ)
            + zt * (u : ℂ)
          = (1 - st) * (u : ℂ) from by
        rw [hzt, hst]
        ring]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hgu,
    cutoffL, ← Finset.sum_mul]
  ring

end Transform

section Bounds

open ArithmeticFunction

variable {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) {A : ℝ}
  (τ : ℝ)

/-- Window bounds for the logarithmic centres. -/
lemma log_mem_window (X : ℕ) :
    ∀ n ∈ Finset.range (X + 1),
      0 ≤ Real.log n ∧ Real.log n ≤ Real.log X := by
  intro n hn
  refine ⟨Real.log_natCast_nonneg n, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · simpa using Real.log_natCast_nonneg X
  · refine Real.log_le_log (by exact_mod_cast hn1) ?_
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)

open scoped Classical in
/-- The port is dominated by a fixed Gaussian. -/
theorem port_bound (hA : 0 < A) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ r : ℝ, ‖gaussPort χ X A τ r‖
      ≤ C * Real.exp (-r ^ 2 / (8 * A)) := by
  classical
  set L : ℝ := Real.log X with hLdef
  set K : ℝ := (Real.sqrt (4 * Real.pi * A))⁻¹
    * Real.exp (L ^ 2 / (4 * A)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set S : ℝ := ∑ n ∈ Finset.range (X + 1),
    ‖χ n * (vonMangoldt n : ℂ)
      * Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)‖
    with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => norm_nonneg _
  set V : ℝ := (volume.real (Set.Ioc (0 : ℝ) L)) * Real.exp (L / 2)
    with hV
  have hV0 : 0 ≤ V := by
    rw [hV]
    exact mul_nonneg measureReal_nonneg (Real.exp_nonneg _)
  refine ⟨(S + V) * K, by positivity, ?_⟩
  intro r
  rw [gaussPort, norm_mul, Complex.norm_exp,
    show (((τ : ℂ) * (r : ℝ)) * Complex.I).re = 0 from by
      simp [Complex.mul_re],
    Real.exp_zero, one_mul]
  refine (norm_sub_le _ _).trans ?_
  have hatomic : ‖∑ n ∈ Finset.range (X + 1),
      χ n * (vonMangoldt n : ℂ)
        * Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
        * gaussKer A (Real.log n - r)‖
      ≤ S * (K * Real.exp (-r ^ 2 / (8 * A))) := by
    refine (norm_sum_le _ _).trans ?_
    rw [hS, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨h0, hL'⟩ := log_mem_window X n hn
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (gaussKer_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hmaj := gaussKer_le_majorant (L := L) hA h0 hL' r
    calc gaussKer A (Real.log n - r)
        ≤ (Real.sqrt (4 * Real.pi * A))⁻¹
          * Real.exp (L ^ 2 / (4 * A))
          * Real.exp (-r ^ 2 / (8 * A)) := hmaj
      _ = K * Real.exp (-r ^ 2 / (8 * A)) := by rw [hK]
  have hcont : ‖(if χ = 1 then (1 : ℂ) else 0)
      * ∫ u in Set.Ioc (0 : ℝ) L,
          Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
            * Real.exp u * gaussKer A (u - r)‖
      ≤ V * (K * Real.exp (-r ^ 2 / (8 * A))) := by
    rw [norm_mul]
    have hδ : ‖(if χ = 1 then (1 : ℂ) else 0)‖ ≤ 1 := by
      split_ifs <;> simp
    have hI : ‖∫ u in Set.Ioc (0 : ℝ) L,
        Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
          * Real.exp u * gaussKer A (u - r)‖
        ≤ Real.exp (L / 2) * (K * Real.exp (-r ^ 2 / (8 * A)))
          * volume.real (Set.Ioc (0 : ℝ) L) := by
      refine MeasureTheory.norm_setIntegral_le_of_norm_le_const
        measure_Ioc_lt_top ?_
      intro u hu
      obtain ⟨hu0, huL⟩ := hu
      rw [norm_mul, norm_mul, Complex.norm_exp,
        show ((-(1 / 2 + (τ : ℂ) * Complex.I)) * ((u : ℝ) : ℂ)).re
            = -(u / 2) from by
          simp [Complex.mul_re, Complex.add_re, Complex.add_im]
          ring,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
        Complex.norm_real, Real.norm_of_nonneg (gaussKer_nonneg _)]
      have h1 : Real.exp (-(u / 2)) * Real.exp u
          = Real.exp (u / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h1]
      have h2 : Real.exp (u / 2) ≤ Real.exp (L / 2) := by
        refine Real.exp_le_exp.mpr ?_
        linarith
      have h3 := gaussKer_le_majorant (L := L) hA hu0.le huL r
      calc Real.exp (u / 2) * gaussKer A (u - r)
          ≤ Real.exp (L / 2)
            * ((Real.sqrt (4 * Real.pi * A))⁻¹
              * Real.exp (L ^ 2 / (4 * A))
              * Real.exp (-r ^ 2 / (8 * A))) :=
            mul_le_mul h2 h3 (gaussKer_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp (L / 2) * (K * Real.exp (-r ^ 2 / (8 * A))) := by
            rw [hK]
    calc ‖(if χ = 1 then (1 : ℂ) else 0)‖
        * ‖∫ u in Set.Ioc (0 : ℝ) L,
            Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
              * Real.exp u * gaussKer A (u - r)‖
        ≤ 1 * (Real.exp (L / 2) * (K * Real.exp (-r ^ 2 / (8 * A)))
            * volume.real (Set.Ioc (0 : ℝ) L)) := by
          refine mul_le_mul hδ hI (norm_nonneg _) (by norm_num)
      _ = V * (K * Real.exp (-r ^ 2 / (8 * A))) := by
          rw [hV]
          ring
  calc ‖∑ n ∈ Finset.range (X + 1),
      χ n * (vonMangoldt n : ℂ)
        * Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * Real.log n)
        * gaussKer A (Real.log n - r)‖
      + ‖(if χ = 1 then (1 : ℂ) else 0)
        * ∫ u in Set.Ioc (0 : ℝ) L,
            Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
              * Real.exp u * gaussKer A (u - r)‖
      ≤ S * (K * Real.exp (-r ^ 2 / (8 * A)))
        + V * (K * Real.exp (-r ^ 2 / (8 * A))) :=
        add_le_add hatomic hcont
    _ = (S + V) * K * Real.exp (-r ^ 2 / (8 * A)) := by ring

open scoped Classical in
/-- The cutoff transform is uniformly bounded on a vertical line. -/
theorem cutoff_bound (σ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : ℝ, ‖cutoffL χ X (1 / 2 + (σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C := by
  classical
  set L : ℝ := Real.log X with hLdef
  set M : ℝ := max 1 (Real.exp ((1 / 2 - σ) * L)) with hM
  have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  refine ⟨(∑ n ∈ Finset.range (X + 1),
      ‖χ n‖ * vonMangoldt n
        * Real.exp (-(1 / 2 + σ) * Real.log n))
    + M * volume.real (Set.Ioc (0 : ℝ) L), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (X + 1),
        ‖χ n‖ * vonMangoldt n
          * Real.exp (-(1 / 2 + σ) * Real.log n) :=
      Finset.sum_nonneg fun n _ => by
        have hvm := vonMangoldt_nonneg (n := n)
        positivity
    have h2 : (0 : ℝ) ≤ M * volume.real (Set.Ioc (0 : ℝ) L) :=
      mul_nonneg hM0 measureReal_nonneg
    linarith
  · intro t
    rw [cutoffL]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun n _ => ?_
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg vonMangoldt_nonneg, Complex.norm_exp]
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_)
        (by positivity)
      congr 1
      simp only [Complex.neg_re, Complex.mul_re, Complex.add_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      rw [show ((1 : ℂ) / 2).re = 1 / 2 from by norm_num]
      ring
    · rw [norm_mul]
      have hδ : ‖(if χ = 1 then (1 : ℂ) else 0)‖ ≤ 1 := by
        split_ifs <;> simp
      have hI : ‖∫ u in Set.Ioc (0 : ℝ) L,
          Complex.exp ((1 - (1 / 2 + (σ : ℂ) + (t : ℂ) * Complex.I))
            * u)‖ ≤ M * volume.real (Set.Ioc (0 : ℝ) L) := by
        refine MeasureTheory.norm_setIntegral_le_of_norm_le_const
          measure_Ioc_lt_top ?_
        intro u hu
        obtain ⟨hu0, huL⟩ := hu
        rw [Complex.norm_exp,
          show ((1 - (1 / 2 + (σ : ℂ) + (t : ℂ) * Complex.I))
              * ((u : ℝ) : ℂ)).re = (1 / 2 - σ) * u from by
            simp only [Complex.mul_re, Complex.sub_re,
              Complex.add_re, Complex.sub_im, Complex.add_im,
              Complex.one_re, Complex.one_im, Complex.ofReal_re,
              Complex.ofReal_im, Complex.mul_im, Complex.I_re,
              Complex.I_im]
            rw [show ((1 : ℂ) / 2).re = 1 / 2 from by norm_num]
            ring]
        rw [hM]
        rcases le_or_gt (1 / 2 - σ) 0 with hc | hc
        · refine le_max_of_le_left ?_
          refine Real.exp_le_one_iff.mpr ?_
          exact mul_nonpos_of_nonpos_of_nonneg hc hu0.le
        · refine le_max_of_le_right ?_
          refine Real.exp_le_exp.mpr ?_
          exact mul_le_mul_of_nonneg_left huL hc.le
      calc ‖(if χ = 1 then (1 : ℂ) else 0)‖
          * ‖∫ u in Set.Ioc (0 : ℝ) L,
              Complex.exp ((1 - (1 / 2 + (σ : ℂ)
                + (t : ℂ) * Complex.I)) * u)‖
          ≤ 1 * (M * volume.real (Set.Ioc (0 : ℝ) L)) :=
            mul_le_mul hδ hI (norm_nonneg _) (by norm_num)
        _ = M * volume.real (Set.Ioc (0 : ℝ) L) := one_mul _

end Bounds

section Main

open ArithmeticFunction

variable {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) {A : ℝ}
  (τ σ : ℝ)

open scoped Classical in
/-- Continuity of the Gaussian travelling port. -/
theorem gaussPort_continuous (hA : 0 < A) :
    Continuous (gaussPort χ X A τ) := by
  classical
  set L : ℝ := Real.log X with hLdef
  have hker : Continuous fun p : ℝ × ℝ => gaussKer A (p.1 - p.2) := by
    rw [show (fun p : ℝ × ℝ => gaussKer A (p.1 - p.2))
        = fun p : ℝ × ℝ => (Real.sqrt (4 * Real.pi * A))⁻¹
          * Real.exp (-(p.1 - p.2) ^ 2 / (4 * A)) from by
      funext p
      rw [gaussKer]]
    fun_prop
  have hcont_int : Continuous fun r : ℝ =>
      ∫ u in Set.Ioc (0 : ℝ) L,
        Complex.exp (-(1 / 2 + (τ : ℂ) * Complex.I) * u)
          * Real.exp u * gaussKer A (u - r) := by
    refine MeasureTheory.continuous_of_dominated
      (bound := fun u : ℝ => Real.exp (-(u / 2)) * Real.exp u
        * (Real.sqrt (4 * Real.pi * A))⁻¹) ?_ ?_ ?_ ?_
    · intro r
      refine Continuous.aestronglyMeasurable ?_
      refine Continuous.mul (Continuous.mul ?_ ?_) ?_
      · exact Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)
      · exact Complex.continuous_ofReal.comp Real.continuous_exp
      · exact Complex.continuous_ofReal.comp
          (hker.comp (Continuous.prodMk continuous_id continuous_const))
    · intro r
      refine Filter.Eventually.of_forall fun u => ?_
      rw [norm_mul, norm_mul, Complex.norm_exp,
        show ((-(1 / 2 + (τ : ℂ) * Complex.I)) * ((u : ℝ) : ℂ)).re
            = -(u / 2) from by
          simp [Complex.mul_re, Complex.add_re, Complex.add_im]
          ring,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
        Complex.norm_real, Real.norm_of_nonneg (gaussKer_nonneg _)]
      calc Real.exp (-(u / 2)) * Real.exp u * gaussKer A (u - r)
          ≤ Real.exp (-(u / 2)) * Real.exp u
            * (Real.sqrt (4 * Real.pi * A))⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [gaussKer]
            refine mul_le_of_le_one_right (by positivity) ?_
            rw [← Real.exp_zero]
            refine Real.exp_le_exp.mpr ?_
            exact div_nonpos_of_nonpos_of_nonneg
              (neg_nonpos_of_nonneg (sq_nonneg _)) (by positivity)
        _ = Real.exp (-(u / 2)) * Real.exp u
            * (Real.sqrt (4 * Real.pi * A))⁻¹ := rfl
    · refine Continuous.integrableOn_Icc ?_ |>.mono_set
        Set.Ioc_subset_Icc_self
      exact ((Real.continuous_exp.comp (by fun_prop)).mul
        Real.continuous_exp).mul_const _
    · refine Filter.Eventually.of_forall fun u => ?_
      refine Continuous.mul continuous_const ?_
      exact Complex.continuous_ofReal.comp
        (hker.comp (Continuous.prodMk continuous_const continuous_id))
  unfold gaussPort
  refine Continuous.mul ?_ (Continuous.sub ?_ ?_)
  · exact Complex.continuous_exp.comp (by fun_prop)
  · refine continuous_finsetSum _ fun n _ => ?_
    refine Continuous.mul continuous_const ?_
    exact Complex.continuous_ofReal.comp
      (hker.comp (Continuous.prodMk continuous_const continuous_id))
  · exact continuous_const.mul hcont_int


set_option maxHeartbeats 2000000 in
-- long: assembles the transform, memberships, Plancherel, and scaling
open scoped Classical in
/-- `thm:plancherel` (exact Gaussian Plancherel identity): for every
real `σ`,
`∫ e^{−2σr}|𝒢^△(r)|² dr
  = (e^{2Aσ²}/2π) ∫ e^{−2A(t−τ)²} |𝔏^△(1/2+σ+it)|² dt`. -/
theorem gaussian_plancherel (hA : 0 < A) :
    (∫ r : ℝ, Real.exp (-2 * σ * r) * ‖gaussPort χ X A τ r‖ ^ 2)
      = Real.exp (2 * A * σ ^ 2) / (2 * Real.pi)
        * ∫ t : ℝ, Real.exp (-2 * A * (t - τ) ^ 2)
            * ‖cutoffL χ X (1 / 2 + (σ : ℂ)
                + (t : ℂ) * Complex.I)‖ ^ 2 := by
  classical
  obtain ⟨CP, hCP0, hCPb⟩ := port_bound χ X τ hA
  obtain ⟨CL, hCL0, hCLb⟩ := cutoff_bound χ X σ
  set h : ℝ → ℂ := fun r =>
    Complex.exp (-(σ : ℂ) * r) * gaussPort χ X A τ r with hh
  have hnorm : ∀ r : ℝ,
      ‖h r‖ = Real.exp (-σ * r) * ‖gaussPort χ X A τ r‖ := by
    intro r
    rw [hh]
    simp only []
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  have hcont_h : Continuous h := by
    rw [hh]
    exact (Complex.continuous_exp.comp (by fun_prop)).mul
      (gaussPort_continuous χ X τ hA)
  -- `L¹` and `L²` membership of the weighted port
  have hInt_h : Integrable h := by
    refine ((integrable_gauss_lin hA (-σ)).const_mul CP).mono'
      hcont_h.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun r => ?_
    rw [hnorm r,
      show -σ * r - r ^ 2 / (8 * A)
        = -σ * r + -r ^ 2 / (8 * A) from by ring, Real.exp_add]
    calc Real.exp (-σ * r) * ‖gaussPort χ X A τ r‖
        ≤ Real.exp (-σ * r) * (CP * Real.exp (-r ^ 2 / (8 * A))) :=
          mul_le_mul_of_nonneg_left (hCPb r) (Real.exp_nonneg _)
      _ = CP * (Real.exp (-σ * r) * Real.exp (-r ^ 2 / (8 * A))) := by
          ring
  have hA2 : (0 : ℝ) < A / 2 := by positivity
  have hMem2_h : MemLp h 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hcont_h.aestronglyMeasurable]
    refine ((integrable_gauss_lin hA2 (-2 * σ)).const_mul
      (CP ^ 2)).mono' (hcont_h.norm.pow 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun r => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : ‖h r‖ ≤ CP * Real.exp (-σ * r + -r ^ 2 / (8 * A)) := by
      rw [hnorm r, Real.exp_add]
      calc Real.exp (-σ * r) * ‖gaussPort χ X A τ r‖
          ≤ Real.exp (-σ * r) * (CP * Real.exp (-r ^ 2 / (8 * A))) :=
            mul_le_mul_of_nonneg_left (hCPb r) (Real.exp_nonneg _)
        _ = CP * (Real.exp (-σ * r) * Real.exp (-r ^ 2 / (8 * A))) := by
            ring
    calc ‖h r‖ ^ 2
        ≤ (CP * Real.exp (-σ * r + -r ^ 2 / (8 * A))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = CP ^ 2 * Real.exp (-2 * σ * r - r ^ 2 / (8 * (A / 2))) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
  -- transform identification
  have hFh : ∀ ξ : ℝ, 𝓕 h ξ
      = Complex.exp ((A : ℂ) * (-(σ : ℂ)
          + ((τ : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) ^ 2)
        * cutoffL χ X (1 / 2 + (σ : ℂ)
            + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
    intro ξ
    rw [Real.fourier_eq']
    have hcongr : ∀ v : ℝ,
        Complex.exp (((-2 * Real.pi * ⟪v, ξ⟫_ℝ : ℝ) : ℂ)
            * Complex.I) • h v
          = Complex.exp (-((2 * Real.pi * ξ : ℝ) : ℂ) * v * Complex.I)
            * (Complex.exp (-(σ : ℂ) * v) * gaussPort χ X A τ v) := by
      intro v
      rw [smul_eq_mul, hh]
      simp only []
      congr 2
      rw [show ⟪v, ξ⟫_ℝ = v * ξ from by
        rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
        ring]
      push_cast
      ring
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hcongr)]
    exact port_transform χ X τ σ hA (2 * Real.pi * ξ)
  -- norm of the transform
  have hFnorm : ∀ ξ : ℝ, ‖𝓕 h ξ‖
      = Real.exp (A * (σ ^ 2 - (τ - 2 * Real.pi * ξ) ^ 2))
        * ‖cutoffL χ X (1 / 2 + (σ : ℂ)
            + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ := by
    intro ξ
    rw [hFh ξ, norm_mul, Complex.norm_exp]
    congr 2
    have hz : ((A : ℂ) * (-(σ : ℂ)
        + ((τ : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) ^ 2)
        = ((A * (σ ^ 2 - (τ - 2 * Real.pi * ξ) ^ 2) : ℝ) : ℂ)
          + ((-2 * A * σ * (τ - 2 * Real.pi * ξ) : ℝ) : ℂ)
            * Complex.I := by
      push_cast
      linear_combination ((A : ℂ)
        * (((τ : ℂ) - 2 * Real.pi * ξ) ^ 2)) * Complex.I_sq
    rw [hz, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  -- `L²` membership of the transform
  have hcont_Fh : Continuous (𝓕 h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hInt_h
  set A' : ℝ := 1 / (64 * Real.pi ^ 2 * A) with hA'
  have hA'0 : 0 < A' := by
    rw [hA']
    positivity
  have hMem2_Fh : MemLp (𝓕 h) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hcont_Fh.aestronglyMeasurable]
    refine ((integrable_gauss_lin hA'0
      (8 * Real.pi * A * τ)).const_mul
      (CL ^ 2 * Real.exp (2 * A * σ ^ 2)
        * Real.exp (-2 * A * τ ^ 2))).mono'
      ((hcont_Fh.norm.pow 2).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_of_nonneg (by positivity), hFnorm ξ]
    have h1 : ‖cutoffL χ X (1 / 2 + (σ : ℂ)
        + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ ≤ CL :=
      hCLb (2 * Real.pi * ξ)
    calc (Real.exp (A * (σ ^ 2 - (τ - 2 * Real.pi * ξ) ^ 2))
          * ‖cutoffL χ X (1 / 2 + (σ : ℂ)
            + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖) ^ 2
        ≤ (Real.exp (A * (σ ^ 2 - (τ - 2 * Real.pi * ξ) ^ 2))
            * CL) ^ 2 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          exact mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
      _ = CL ^ 2 * Real.exp (2 * A * σ ^ 2)
          * Real.exp (-2 * A * τ ^ 2)
          * Real.exp (8 * Real.pi * A * τ * ξ - ξ ^ 2 / (8 * A')) := by
          rw [mul_pow, ← Real.exp_nat_mul,
            show CL ^ 2 * Real.exp (2 * A * σ ^ 2)
                * Real.exp (-2 * A * τ ^ 2)
                * Real.exp (8 * Real.pi * A * τ * ξ - ξ ^ 2 / (8 * A'))
              = CL ^ 2 * Real.exp ((2 * A * σ ^ 2)
                + (-2 * A * τ ^ 2)
                + (8 * Real.pi * A * τ * ξ - ξ ^ 2 / (8 * A')))
              from by
                rw [Real.exp_add, Real.exp_add]
                ring,
            hA', mul_comm]
          congr 2
          push_cast
          have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
          field_simp
          ring
  -- Plancherel through the bridge
  have hPl : (∫ r : ℝ, ‖h r‖ ^ 2) = ∫ ξ : ℝ, ‖𝓕 h ξ‖ ^ 2 := by
    rw [← norm_toLp_sq hMem2_h, ← norm_toLp_sq hMem2_Fh,
      ← fourier_toLp_eq hInt_h hMem2_h hMem2_Fh,
      MeasureTheory.Lp.norm_fourier_eq]
  -- scaling substitution to the manuscript frequency
  set W : ℝ → ℝ := fun t =>
    Real.exp (2 * A * (σ ^ 2 - (τ - t) ^ 2))
      * ‖cutoffL χ X (1 / 2 + (σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
    with hW
  have hWval : ∀ ξ : ℝ, ‖𝓕 h ξ‖ ^ 2 = W (2 * Real.pi * ξ) := by
    intro ξ
    rw [hFnorm ξ, hW]
    simp only []
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hsub : (∫ ξ : ℝ, ‖𝓕 h ξ‖ ^ 2)
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ, W t := by
    calc (∫ ξ : ℝ, ‖𝓕 h ξ‖ ^ 2)
        = ∫ ξ : ℝ, W (2 * Real.pi * ξ) :=
          MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall hWval)
      _ = |(2 * Real.pi)⁻¹| • ∫ t : ℝ, W t :=
          MeasureTheory.Measure.integral_comp_mul_left W (2 * Real.pi)
      _ = (2 * Real.pi)⁻¹ * ∫ t : ℝ, W t := by
          rw [abs_of_pos (by positivity), smul_eq_mul]
  have hLHS : (∫ r : ℝ, Real.exp (-2 * σ * r)
      * ‖gaussPort χ X A τ r‖ ^ 2) = ∫ r : ℝ, ‖h r‖ ^ 2 := by
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun r => ?_)
    simp only []
    rw [hnorm r, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [hLHS, hPl, hsub]
  have hWsplit : ∀ t : ℝ, W t
      = Real.exp (2 * A * σ ^ 2)
        * (Real.exp (-2 * A * (t - τ) ^ 2)
          * ‖cutoffL χ X (1 / 2 + (σ : ℂ)
              + (t : ℂ) * Complex.I)‖ ^ 2) := by
    intro t
    rw [hW]
    simp only []
    rw [show 2 * A * (σ ^ 2 - (τ - t) ^ 2)
        = 2 * A * σ ^ 2 + -2 * A * (t - τ) ^ 2 from by ring,
      Real.exp_add]
    ring
  rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hWsplit),
    MeasureTheory.integral_const_mul]
  ring

end Main

end NCG
