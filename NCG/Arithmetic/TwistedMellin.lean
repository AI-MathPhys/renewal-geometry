/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact twisted Mellin transform
  (`thm:v002-twisted-mellin`, arithmetic manuscript)

For a continuous compactly supported window `C` and `Re s > 1/2`:

* the single-frequency substitution `u = log(a/X)` gives
  `∫₀^∞ C(log(a/X)) X^{-s} dX/X = a^{-s} H_C(s)`
  (`mellin_log_dilate`);
* the prime side sums to the twisted von Mangoldt L-series
  (`twisted_mellin_prime_side`, by Fubini);
* the centered channel integrates to `H_C(s)/(s - 1/2)`
  (`twisted_mellin_center_side`);
* subtracting yields the boxed identity
  `∫₀^∞ ℰ_{C,χ}(X) X^{-s} dX/X
   = H_C(s)[-L'/L(s + 1/2, χ) - δ_χ/(s - 1/2)]`
  (`twisted_mellin`, with `-L'/L` the logarithmic derivative of
  the Dirichlet L-series, per Mathlib's
  `LSeries_twist_vonMangoldt_eq`; the δ-channel enters through
  the explicit centered term).

Absolute convergence in the half-plane is established en route
(the summability and integrability side conditions of the Fubini
steps).
-/

open MeasureTheory Real Set Filter ArithmeticFunction

namespace NCG

/-- The bilateral Laplace symbol `H_C(s) = ∫ C(u) e^{su} du`. -/
noncomputable def packetH (C : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, (C u : ℂ) * Complex.exp (s * u)

/-- Exponential substitution for integrals over `(0,∞)`. -/
lemma integral_Ioi_eq_integral_exp (f : ℝ → ℂ) :
    ∫ X in Ioi (0 : ℝ), f X
      = ∫ t : ℝ, Real.exp t • f (Real.exp t) := by
  have h1 : ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have h2 : Set.InjOn Real.exp Set.univ :=
    Real.exp_injective.injOn
  have h3 := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ h1 h2 f
  rw [Set.image_univ, Real.range_exp] at h3
  rw [h3, setIntegral_univ]
  refine integral_congr_ae (.of_forall fun t => ?_)
  simp only [abs_of_pos (Real.exp_pos t)]

/-- The boxed single-frequency identity: the substitution
`u = log(a/X)` evaluates the Mellin integral of a dilated window
to `a^{-s} H_C(s)`. -/
lemma mellin_log_dilate (C : ℝ → ℝ) {a : ℝ} (ha : 0 < a)
    (s : ℂ) :
    ∫ X in Ioi (0 : ℝ),
        (C (Real.log (a / X)) : ℂ) * (X : ℂ) ^ (-s) / X
      = (a : ℂ) ^ (-s) * packetH C s := by
  rw [integral_Ioi_eq_integral_exp]
  have hpt : ∀ t : ℝ, Real.exp t •
      ((C (Real.log (a / Real.exp t)) : ℂ)
        * ((Real.exp t : ℝ) : ℂ) ^ (-s) / (Real.exp t : ℝ))
      = (C (Real.log a - t) : ℂ) * Complex.exp (-s * t) := by
    intro t
    rw [Real.log_div ha.ne' (Real.exp_ne_zero t), Real.log_exp,
      show ((Real.exp t : ℝ) : ℂ) ^ (-s)
          = Complex.exp (-s * t) from by
        rw [Complex.ofReal_exp,
          Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
          Complex.log_exp (by simpa using Real.pi_pos)
            (by simpa using Real.pi_pos.le), mul_comm],
      Complex.real_smul, mul_comm,
      div_mul_cancel₀ _
        (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t))]
  rw [integral_congr_ae (.of_forall hpt)]
  have hshift : ∫ t : ℝ,
      (C (Real.log a - t) : ℂ) * Complex.exp (-s * t)
      = ∫ u : ℝ, (C u : ℂ)
          * Complex.exp (-s * (Real.log a - u)) := by
    rw [← integral_sub_left_eq_self
      (fun u => (C u : ℂ) * Complex.exp (-s * (Real.log a - u)))
      volume (Real.log a)]
    refine integral_congr_ae (.of_forall fun t => ?_)
    push_cast
    ring
  rw [hshift]
  have hsplit : ∀ u : ℝ,
      (C u : ℂ) * Complex.exp (-s * (Real.log a - u))
      = Complex.exp (-s * Real.log a)
          * ((C u : ℂ) * Complex.exp (s * u)) := by
    intro u
    rw [show (-s * ((Real.log a : ℝ) - (u : ℝ)) : ℂ)
        = -s * Real.log a + s * u from by ring,
      Complex.exp_add]
    ring
  rw [integral_congr_ae (.of_forall hsplit), integral_const_mul,
    packetH]
  congr 1
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr ha.ne'),
    ← Complex.ofReal_log ha.le, mul_comm]

/-- The tail power integral `∫₁^∞ y^w dy = -1/(w+1)` for
`Re w < -1`. -/
lemma integral_Ioi_one_cpow {w : ℂ} (hw : w.re < -1) :
    ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ w = -1 / (w + 1) := by
  have hw1 : w + 1 ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re,
      Complex.zero_re] at h2
    linarith
  have hderiv : ∀ y ∈ Ioi (1 : ℝ),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (w + 1) / (w + 1))
        ((y : ℂ) ^ w) y := by
    intro y hy
    have hy0 : y ≠ 0 := by
      have : (1 : ℝ) < y := hy
      linarith
    have h1 := hasDerivAt_ofReal_cpow_const' hy0
      (show w ≠ -1 from fun hcon => by
        rw [hcon] at hw
        simp at hw)
    exact h1
  have hcont : ContinuousWithinAt
      (fun y : ℝ => (y : ℂ) ^ (w + 1) / (w + 1))
      (Ici (1 : ℝ)) 1 := by
    have h1 := hasDerivAt_ofReal_cpow_const'
      (one_ne_zero (α := ℝ))
      (show w ≠ -1 from fun hcon => by
        rw [hcon] at hw
        simp at hw)
    exact h1.continuousAt.continuousWithinAt
  have hint : IntegrableOn (fun y : ℝ => (y : ℂ) ^ w)
      (Ioi (1 : ℝ)) := by
    have := integrableOn_Ioi_cpow_of_lt hw one_pos
    exact this
  have htend : Tendsto
      (fun y : ℝ => (y : ℂ) ^ (w + 1) / (w + 1)) atTop
      (nhds 0) := by
    have h0 : (0 : ℂ) = 0 / (w + 1) := by simp
    rw [h0]
    refine Tendsto.div_const ?_ _
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hEE : ∀ᶠ y : ℝ in atTop,
        ‖(y : ℂ) ^ (w + 1)‖ = y ^ (w.re + 1) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simp
    rw [tendsto_congr' hEE]
    simpa using tendsto_rpow_neg_atTop
      (y := -(w.re + 1)) (by linarith)
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    hderiv hint htend
  rw [hres, Complex.ofReal_one, Complex.one_cpow, zero_sub,
    neg_div]

/-- Norm evaluation of the dilated Mellin integrand. -/
lemma mellin_log_dilate_norm (C : ℝ → ℝ) {a : ℝ} (ha : 0 < a)
    (σ : ℝ) :
    ∫ X in Ioi (0 : ℝ),
        |C (Real.log (a / X))| * X ^ (-σ) / X
      = a ^ (-σ) * ∫ u : ℝ, |C u| * Real.exp (σ * u) := by
  have h1 := mellin_log_dilate (fun u => |C u|) ha (σ : ℂ)
  have h2 : ∫ X in Ioi (0 : ℝ),
      ((|C (Real.log (a / X))| : ℝ) : ℂ)
        * (X : ℂ) ^ (-(σ : ℂ)) / X
      = ((∫ X in Ioi (0 : ℝ),
          |C (Real.log (a / X))| * X ^ (-σ) / X : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi
      fun X hX => ?_
    have hX0 : (0 : ℝ) < X := hX
    rw [Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_cpow hX0.le]
    push_cast
    ring
  have h3 : packetH (fun u => |C u|) (σ : ℂ)
      = ((∫ u : ℝ, |C u| * Real.exp (σ * u) : ℝ) : ℂ) := by
    rw [packetH, ← integral_complex_ofReal]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  have h4 : ((a : ℝ) : ℂ) ^ (-(σ : ℂ))
      = ((a ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ha.le]
    push_cast
    ring
  rw [h2, h3, h4] at h1
  exact_mod_cast h1

/-- Pointwise norm of the dilated Mellin integrand. -/
lemma mellin_integrand_norm (C : ℝ → ℝ) {a : ℝ} (s : ℂ)
    {X : ℝ} (hX : 0 < X) :
    ‖(C (Real.log (a / X)) : ℂ) * (X : ℂ) ^ (-s) / X‖
      = |C (Real.log (a / X))| * X ^ (-s.re) / X := by
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_cpow_eq_rpow_re_of_pos hX, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hX, Complex.neg_re]

/-- Off the window `[a e^{-R}, a e^{R}]` the dilated integrand
vanishes. -/
lemma mellin_integrand_eq_zero (C : ℝ → ℝ) {R : ℝ}
    (hR : tsupport C ⊆ Metric.closedBall 0 R)
    {a : ℝ} (ha : 0 < a) (s : ℂ) {X : ℝ} (hX0 : 0 < X)
    (hXK : X ∉ Icc (a / Real.exp R) (a * Real.exp R)) :
    (C (Real.log (a / X)) : ℂ) * (X : ℂ) ^ (-s) / X = 0 := by
  have hCz : C (Real.log (a / X)) = 0 := by
    by_contra hne
    have hmem : Real.log (a / X) ∈ tsupport C :=
      subset_tsupport C hne
    have habs : |Real.log (a / X)| ≤ R := by
      have h6 := hR hmem
      rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h6
    rw [Real.log_div ha.ne' hX0.ne', abs_le] at habs
    refine hXK ⟨?_, ?_⟩
    · have h5 : Real.log a - R ≤ Real.log X := by
        linarith [habs.2]
      have h6 := Real.exp_le_exp.mpr h5
      rwa [Real.exp_sub, Real.exp_log ha,
        Real.exp_log hX0] at h6
    · have h5 : Real.log X ≤ Real.log a + R := by
        linarith [habs.1]
      have h6 := Real.exp_le_exp.mpr h5
      rwa [Real.exp_add, Real.exp_log ha,
        Real.exp_log hX0] at h6
  rw [hCz]
  simp

/-- The dilated Mellin integrand is integrable on `(0,∞)` for a
compactly supported continuous window. -/
lemma mellin_integrand_integrableOn (C : ℝ → ℝ)
    (hC : Continuous C) (hsupp : HasCompactSupport C)
    {a : ℝ} (ha : 0 < a) (s : ℂ) :
    IntegrableOn
      (fun X : ℝ =>
        (C (Real.log (a / X)) : ℂ) * (X : ℂ) ^ (-s) / X)
      (Ioi (0 : ℝ)) := by
  obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall 0
  set K : Set ℝ := Icc (a / Real.exp R) (a * Real.exp R)
    with hK
  have hKlo : 0 < a / Real.exp R := by positivity
  have hKint : IntegrableOn
      (fun X : ℝ =>
        (C (Real.log (a / X)) : ℂ) * (X : ℂ) ^ (-s) / X) K := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    intro X hX
    have hX0 : (0 : ℝ) < X := lt_of_lt_of_le hKlo hX.1
    have c1 : ContinuousAt
        (fun X : ℝ => (C (Real.log (a / X)) : ℂ)) X := by
      refine Complex.continuous_ofReal.continuousAt.comp ?_
      refine hC.continuousAt.comp ?_
      refine (Real.continuousAt_log ?_).comp ?_
      · positivity
      · exact continuousAt_const.div continuousAt_id hX0.ne'
    have c2 : ContinuousAt (fun X : ℝ => (X : ℂ) ^ (-s)) X :=
      Complex.continuousAt_ofReal_cpow_const X (-s)
        (Or.inr hX0.ne')
    have c3 : ContinuousAt (fun X : ℝ => (X : ℂ)) X :=
      Complex.continuous_ofReal.continuousAt
    exact ((c1.mul c2).div c3
      (Complex.ofReal_ne_zero.mpr hX0.ne')).continuousWithinAt
  have hdiff : IntegrableOn
      (fun X : ℝ =>
        (C (Real.log (a / X)) : ℂ) * (X : ℂ) ^ (-s) / X)
      (Ioi (0 : ℝ) \ K) := by
    rw [integrableOn_congr_fun
      (g := fun _ => (0 : ℂ))
      (fun X hX => mellin_integrand_eq_zero C hR ha s hX.1
        hX.2)
      (measurableSet_Ioi.diff measurableSet_Icc)]
    exact integrableOn_zero
  refine (hdiff.union hKint).mono_set fun X hX => ?_
  by_cases hXK : X ∈ K
  · exact Or.inr hXK
  · exact Or.inl ⟨hX, hXK⟩

/-- Integrability of a pointwise sum from summable norm
integrals (the integrable companion of `integral_tsum`). -/
lemma integrable_tsum_of_summable' {F : ℕ → ℝ → ℂ}
    {μ : Measure ℝ} (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i => ∫ a, ‖F i a‖ ∂μ)
    (hae : ∀ᵐ a ∂μ, Summable fun i => ‖F i a‖) :
    Integrable (fun a => ∑' i, F i a) μ := by
  have hmeas : AEStronglyMeasurable (fun a => ∑' i, F i a) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n a => ∑ i ∈ Finset.range n, F i a)
      (fun n => ?_) ?_
    · exact (Finset.aestronglyMeasurable_sum
        (Finset.range n) fun i _ => (hF_int i).1).congr
        (.of_forall fun a => by simp)
    · filter_upwards [hae] with a hsa
      exact ((Summable.of_norm hsa).hasSum).tendsto_sum_nat
  have hbound : Integrable (fun a => ∑' i, ‖F i a‖) μ := by
    refine ⟨?_, ?_⟩
    · refine aestronglyMeasurable_of_tendsto_ae atTop
        (f := fun n a => ∑ i ∈ Finset.range n, ‖F i a‖)
        (fun n => ?_) ?_
      · exact (Finset.aestronglyMeasurable_sum
          (Finset.range n) fun i _ => (hF_int i).norm.1).congr
          (.of_forall fun a => by simp)
      · filter_upwards [hae] with a hsa
        exact hsa.hasSum.tendsto_sum_nat
    · rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ a, ‖∑' i, ‖F i a‖‖ₑ ∂μ
          ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae] with a hsa
            calc ‖∑' i, ‖F i a‖‖ₑ
                ≤ ∑' i, ‖(‖F i a‖ : ℝ)‖ₑ :=
                  enorm_tsum_le_tsum_enorm
              _ = ∑' i, ‖F i a‖ₑ :=
                  tsum_congr fun i => enorm_norm _
        _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ :=
            lintegral_tsum fun i => (hF_int i).1.enorm
        _ < ⊤ := by
            have h1 : ∀ i, ∫⁻ a, ‖F i a‖ₑ ∂μ
                = ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := by
              intro i
              rw [← ofReal_integral_norm_eq_lintegral_enorm
                (hF_int i)]
            rw [funext h1, ← ENNReal.ofReal_tsum_of_nonneg
              (fun i => integral_nonneg fun a => norm_nonneg _)
              hF_sum]
            exact ENNReal.ofReal_lt_top
  refine hbound.mono' hmeas ?_
  filter_upwards [hae] with a hsa
  simpa using norm_tsum_le_tsum_norm hsa

/-- `thm:v002-twisted-mellin`, prime side: absolute convergence,
and Fubini with the single-frequency identity produce the twisted
von Mangoldt L-series. -/
theorem twisted_mellin_prime_side {N : ℕ}
    (χ : DirichletCharacter ℂ N) (C : ℝ → ℝ)
    (hC : Continuous C) (hsupp : HasCompactSupport C)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn
      (fun X : ℝ =>
        (∑' n : ℕ, (Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)
          * (C (Real.log (n / X)) : ℂ)) * (X : ℂ) ^ (-s) / X)
      (Ioi (0 : ℝ))
    ∧ ∫ X in Ioi (0 : ℝ),
        (∑' n : ℕ, (Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)
          * (C (Real.log (n / X)) : ℂ)) * (X : ℂ) ^ (-s) / X
      = packetH C s
          * LSeries (fun n => χ n * (Λ n : ℂ)) (s + 1 / 2) := by
  obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall 0
  set σ : ℝ := s.re with hσ
  set B : ℝ := ∫ u : ℝ, |C u| * Real.exp (σ * u) with hB
  set F : ℕ → ℝ → ℂ := fun n X =>
    (Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)
      * ((C (Real.log (n / X)) : ℂ) * (X : ℂ) ^ (-s) / X)
    with hF
  have hpt : ∀ X : ℝ,
      (∑' n : ℕ, (Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)
        * (C (Real.log (n / X)) : ℂ)) * (X : ℂ) ^ (-s) / X
      = ∑' n, F n X := by
    intro X
    rw [div_eq_mul_inv, ← tsum_mul_right, ← tsum_mul_right]
    exact tsum_congr fun n => by rw [hF]; ring
  have hFzero : F 0 = fun _ => 0 := by
    funext X
    rw [hF]
    simp
  have hFint : ∀ n : ℕ,
      Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hFzero]
      exact integrable_zero _ _ _
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact (mellin_integrand_integrableOn C hC hsupp hn0
        s).const_mul _
  have hnormval : ∀ n : ℕ, 0 < n →
      ∫ X in Ioi (0 : ℝ), ‖F n X‖
      = ‖(Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)‖
          * ((n : ℝ) ^ (-σ) * B) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : ∀ X ∈ Ioi (0 : ℝ), ‖F n X‖
        = ‖(Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)‖
          * (|C (Real.log (n / X))| * X ^ (-σ) / X) := by
      intro X hX
      rw [hF]
      rw [norm_mul, mellin_integrand_norm C s hX]
    rw [setIntegral_congr_fun measurableSet_Ioi h1,
      integral_const_mul, mellin_log_dilate_norm C hn0 σ]
  have hre : 1 < (s + 1 / 2).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  have hΛsum : Summable fun n =>
      ‖LSeries.term (fun k => (Λ k : ℂ)) (s + 1 / 2) n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hre).norm
  have hB0 : 0 ≤ B :=
    integral_nonneg fun u => by positivity
  have hterm : ∀ n : ℕ, 0 < n →
      ‖LSeries.term (fun k => (Λ k : ℂ)) (s + 1 / 2) n‖
      = Λ n * (n : ℝ) ^ (-(σ + 1 / 2)) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne', norm_div,
      Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      show ((n : ℕ) : ℂ) = (((n : ℝ) : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0,
      show (s + 1 / 2).re = σ + 1 / 2 from by
        rw [Complex.add_re, hσ]; norm_num,
      Real.rpow_neg hn0.le, div_eq_mul_inv]
  have hFsum : Summable fun n =>
      ∫ X in Ioi (0 : ℝ), ‖F n X‖ := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun X => norm_nonneg _)
      (fun n => ?_) (hΛsum.mul_right B)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hFzero]
      simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [hnormval n hn, hterm n hn]
      calc ‖(Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)‖
            * ((n : ℝ) ^ (-σ) * B)
          ≤ Λ n * (n : ℝ) ^ (-(1 : ℝ) / 2)
              * ((n : ℝ) ^ (-σ) * B) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [norm_div, norm_mul, Complex.norm_real,
              Real.norm_of_nonneg
                ArithmeticFunction.vonMangoldt_nonneg,
              show ((n : ℕ) : ℂ) = (((n : ℝ) : ℝ) : ℂ) by
                norm_cast,
              Complex.norm_cpow_eq_rpow_re_of_pos hn0,
              show ((1 : ℂ) / 2).re = (1 : ℝ) / 2 from by
                norm_num,
              show (-(1 : ℝ) / 2 : ℝ) = -(1 / 2 : ℝ) from by
                ring,
              Real.rpow_neg hn0.le, div_eq_mul_inv]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_of_le_one_right
              ArithmeticFunction.vonMangoldt_nonneg
              (χ.norm_le_one _)
      _ = Λ n * (n : ℝ) ^ (-(σ + 1 / 2)) * B := by
            rw [show (-(σ + 1 / 2) : ℝ) = -σ + -(1 / 2) from by
              ring, Real.rpow_add hn0,
              show (-(1 : ℝ)) / 2 = -(1 / 2 : ℝ) from by ring]
            ring
  have hae : ∀ᵐ X ∂volume.restrict (Ioi (0 : ℝ)),
      Summable fun n => ‖F n X‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with X hX
    refine summable_of_ne_finset_zero
      (s := Finset.range (⌈X * Real.exp R⌉₊ + 1))
      fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    have hnn : ⌈X * Real.exp R⌉₊ < n := Nat.lt_of_succ_le hn
    have hbig : X * Real.exp R < (n : ℝ) := by
      calc X * Real.exp R ≤ (⌈X * Real.exp R⌉₊ : ℝ) :=
            Nat.le_ceil _
        _ < (n : ℝ) := by exact_mod_cast hnn
    have hX0 : (0 : ℝ) < X := hX
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      calc (0 : ℝ) < X * Real.exp R := by positivity
        _ < n := hbig
    have hnot : X ∉ Icc ((n : ℝ) / Real.exp R)
        ((n : ℝ) * Real.exp R) := by
      intro hmem
      have h2 : (n : ℝ) / Real.exp R ≤ X := hmem.1
      rw [div_le_iff₀ (Real.exp_pos R)] at h2
      linarith
    simp only [hF]
    rw [mellin_integrand_eq_zero C hR hn0 s hX0 hnot]
    simp
  have hint : IntegrableOn
      (fun X : ℝ =>
        (∑' n : ℕ, (Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)
          * (C (Real.log (n / X)) : ℂ)) * (X : ℂ) ^ (-s) / X)
      (Ioi (0 : ℝ)) := by
    refine (integrable_tsum_of_summable' hFint hFsum
      hae).congr ?_
    exact .of_forall fun X => (hpt X).symm
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae (.of_forall hpt),
    ← integral_tsum_of_summable_integral_norm hFint hFsum]
  have hval : ∀ n : ℕ, (∫ X in Ioi (0 : ℝ), F n X)
      = LSeries.term (fun k => χ k * (Λ k : ℂ)) (s + 1 / 2) n
        * packetH C s := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hFzero, LSeries.term_zero]
      simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hne : ((n : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast hn0.ne'
      have h12 : (n : ℂ) ^ ((1 : ℂ) / 2) ≠ 0 := by
        simp [Complex.cpow_eq_zero_iff, hne]
      have hsne : (n : ℂ) ^ s ≠ 0 := by
        simp [Complex.cpow_eq_zero_iff, hne]
      rw [hF]
      rw [integral_const_mul, mellin_log_dilate C hn0 s,
        LSeries.term_of_ne_zero hn.ne',
        Complex.cpow_add _ _ hne, Complex.cpow_neg]
      push_cast
      field_simp
  rw [tsum_congr hval, tsum_mul_right, mul_comm]
  rfl

/-- `thm:v002-twisted-mellin`, centered channel:
`∫₀^∞ 𝒞_C(X) X^{-s} dX/X = H_C(s)/(s - 1/2)`. -/
theorem twisted_mellin_center_side (C : ℝ → ℝ)
    (hC : Continuous C) (hsupp : HasCompactSupport C)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn
      (fun X : ℝ =>
        ((∫ y in Ioi (1 : ℝ),
          y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ) : ℂ)
          * (X : ℂ) ^ (-s) / X)
      (Ioi (0 : ℝ))
    ∧ ∫ X in Ioi (0 : ℝ),
        ((∫ y in Ioi (1 : ℝ),
          y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ) : ℂ)
          * (X : ℂ) ^ (-s) / X
      = packetH C s / (s - 1 / 2) := by
  set σ : ℝ := s.re with hσ
  set B : ℝ := ∫ u : ℝ, |C u| * Real.exp (σ * u) with hB
  set G : ℝ → ℝ → ℂ := fun X y =>
    ((y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ) : ℂ)
      * (X : ℂ) ^ (-s) / X with hG
  have hpt : ∀ X : ℝ,
      ((∫ y in Ioi (1 : ℝ),
        y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ) : ℂ)
        * (X : ℂ) ^ (-s) / X
      = ∫ y in Ioi (1 : ℝ), G X y := by
    intro X
    calc ((∫ y in Ioi (1 : ℝ),
          y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ) : ℂ)
          * (X : ℂ) ^ (-s) / X
        = ((X : ℂ) ^ (-s) / X)
            * ((∫ y in Ioi (1 : ℝ),
              y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ)
                : ℂ) := by ring
      _ = ((X : ℂ) ^ (-s) / X)
            * ∫ y in Ioi (1 : ℝ),
              ((y ^ (-(1 : ℝ) / 2)
                * C (Real.log (y / X)) : ℝ) : ℂ) := by
            rw [integral_complex_ofReal]
      _ = ∫ y in Ioi (1 : ℝ), ((X : ℂ) ^ (-s) / X)
            * ((y ^ (-(1 : ℝ) / 2)
              * C (Real.log (y / X)) : ℝ) : ℂ) :=
            (integral_const_mul _ _).symm
      _ = ∫ y in Ioi (1 : ℝ), G X y := by
            refine integral_congr_ae (.of_forall fun y => ?_)
            rw [hG]
            ring
  have hmeasG : AEStronglyMeasurable
      (fun p : ℝ × ℝ => G p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (1 : ℝ)))) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.aestronglyMeasurable ?_
      (measurableSet_Ioi.prod measurableSet_Ioi)
    intro p hp
    have hX0 : (0 : ℝ) < p.1 := hp.1
    have hy0 : (0 : ℝ) < p.2 := lt_trans one_pos hp.2
    have a1 : ContinuousAt
        (fun p : ℝ × ℝ => p.2 ^ (-(1 : ℝ) / 2)) p :=
      (Real.continuousAt_rpow_const p.2 _
        (Or.inl hy0.ne')).comp continuousAt_snd
    have a2 : ContinuousAt
        (fun p : ℝ × ℝ => C (Real.log (p.2 / p.1))) p := by
      refine hC.continuousAt.comp ?_
      refine (Real.continuousAt_log ?_).comp ?_
      · positivity
      · exact continuousAt_snd.div continuousAt_fst hX0.ne'
    have a3 : ContinuousAt
        (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) ^ (-s)) p :=
      (Complex.continuousAt_ofReal_cpow_const p.1 (-s)
        (Or.inr hX0.ne')).comp continuousAt_fst
    have a4 : ContinuousAt
        (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        continuousAt_fst
    refine ContinuousAt.continuousWithinAt ?_
    exact ((Complex.continuous_ofReal.continuousAt.comp
      (a1.mul a2)).mul a3).div a4
      (Complex.ofReal_ne_zero.mpr hX0.ne')
  have hslice : ∀ᵐ y ∂volume.restrict (Ioi (1 : ℝ)),
      Integrable (fun X => G X y)
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with y hy
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    refine ((mellin_integrand_integrableOn C hC hsupp hy0
      s).const_mul
      (((y ^ (-(1 : ℝ) / 2) : ℝ) : ℂ))).congr ?_
    refine .of_forall fun X => ?_
    rw [hG]
    push_cast
    ring
  have hnorm : ∀ y ∈ Ioi (1 : ℝ),
      (∫ X in Ioi (0 : ℝ), ‖G X y‖)
      = y ^ (-(1 : ℝ) / 2) * (y ^ (-σ) * B) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    have h1 : ∀ X ∈ Ioi (0 : ℝ), ‖G X y‖
        = y ^ (-(1 : ℝ) / 2)
          * (|C (Real.log (y / X))| * X ^ (-σ) / X) := by
      intro X hX
      have hX0 : (0 : ℝ) < X := hX
      simp only [hG]
      rw [show ((y ^ (-(1 : ℝ) / 2)
          * C (Real.log (y / X)) : ℝ) : ℂ)
            * (X : ℂ) ^ (-s) / X
          = ((y ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
            * ((C (Real.log (y / X)) : ℂ)
              * (X : ℂ) ^ (-s) / X) from by push_cast; ring,
        norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _),
        mellin_integrand_norm C s hX0]
    rw [setIntegral_congr_fun measurableSet_Ioi h1,
      integral_const_mul, mellin_log_dilate_norm C hy0 σ]
  have hmarg : Integrable
      (fun y => ∫ X in Ioi (0 : ℝ), ‖G X y‖)
      (volume.restrict (Ioi (1 : ℝ))) := by
    have h2 : IntegrableOn
        (fun y : ℝ => y ^ (-(1 : ℝ) / 2 + -σ) * B)
        (Ioi (1 : ℝ)) := by
      refine Integrable.mul_const ?_ _
      refine integrableOn_Ioi_rpow_of_lt ?_ one_pos
      linarith
    refine h2.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with y hy
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    rw [hnorm y hy, Real.rpow_add hy0]
    ring
  have hprod : Integrable (fun p : ℝ × ℝ => G p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (1 : ℝ)))) := by
    rw [integrable_prod_iff' hmeasG]
    exact ⟨hslice, hmarg⟩
  have hint : IntegrableOn
      (fun X : ℝ =>
        ((∫ y in Ioi (1 : ℝ),
          y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ) : ℂ)
          * (X : ℂ) ^ (-s) / X)
      (Ioi (0 : ℝ)) := by
    refine (hprod.integral_prod_left).congr ?_
    exact .of_forall fun X => (hpt X).symm
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae (.of_forall hpt),
    integral_integral_swap hprod]
  have hyne : ∀ y ∈ Ioi (1 : ℝ), ((y : ℝ) : ℂ) ≠ 0 :=
    fun y hy => Complex.ofReal_ne_zero.mpr
      (lt_trans one_pos hy).ne'
  have hinner : ∀ y ∈ Ioi (1 : ℝ),
      (∫ X in Ioi (0 : ℝ), G X y)
      = packetH C s * (y : ℂ) ^ (-s - 1 / 2) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    have h3 : (fun X : ℝ => G X y)
        = fun X => ((y ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
          * ((C (Real.log (y / X)) : ℂ)
            * (X : ℂ) ^ (-s) / X) := by
      funext X
      rw [hG]
      push_cast
      ring
    rw [h3, integral_const_mul, mellin_log_dilate C hy0 s,
      Complex.ofReal_cpow hy0.le,
      show (((-(1 : ℝ) / 2 : ℝ)) : ℂ) = -(1 / 2 : ℂ) from by
        norm_num,
      ← mul_assoc, ← Complex.cpow_add _ _
        (Complex.ofReal_ne_zero.mpr hy0.ne'),
      show (-(1 / 2 : ℂ)) + -s = -s - 1 / 2 from by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner,
    integral_const_mul,
    integral_Ioi_one_cpow (by
      rw [Complex.sub_re, Complex.neg_re]
      norm_num
      linarith)]
  rw [show (-s - 1 / 2 + 1 : ℂ) = -(s - 1 / 2) from by ring,
    div_neg, neg_div, neg_neg, mul_one_div]

/-- `thm:v002-twisted-mellin`, boxed identity: the Mellin
transform of the centered packet equals
`H_C(s)[-L'/L(s + 1/2, χ) - δ/(s - 1/2)]` on `Re s > 1/2`. -/
theorem twisted_mellin {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (C : ℝ → ℝ)
    (hC : Continuous C) (hsupp : HasCompactSupport C)
    (δ : ℂ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ X in Ioi (0 : ℝ),
        ((∑' n : ℕ, (Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)
            * (C (Real.log (n / X)) : ℂ))
          - δ * ((∫ y in Ioi (1 : ℝ),
              y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ)
                : ℂ))
          * (X : ℂ) ^ (-s) / X
      = packetH C s
          * (-deriv (LSeries fun n => (χ n : ℂ)) (s + 1 / 2)
                / LSeries (fun n => (χ n : ℂ)) (s + 1 / 2)
              - δ / (s - 1 / 2)) := by
  obtain ⟨hPint, hPval⟩ :=
    twisted_mellin_prime_side χ C hC hsupp hs
  obtain ⟨hCint, hCval⟩ :=
    twisted_mellin_center_side C hC hsupp hs
  have hsplit : ∀ X : ℝ,
      ((∑' n : ℕ, (Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)
          * (C (Real.log (n / X)) : ℂ))
        - δ * ((∫ y in Ioi (1 : ℝ),
            y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ)
              : ℂ))
        * (X : ℂ) ^ (-s) / X
      = (∑' n : ℕ, (Λ n : ℂ) * χ n / (n : ℂ) ^ ((1 : ℂ) / 2)
          * (C (Real.log (n / X)) : ℂ)) * (X : ℂ) ^ (-s) / X
        - δ * (((∫ y in Ioi (1 : ℝ),
            y ^ (-(1 : ℝ) / 2) * C (Real.log (y / X)) : ℝ)
              : ℂ) * (X : ℂ) ^ (-s) / X) := by
    intro X
    ring
  rw [integral_congr_ae (.of_forall hsplit),
    integral_sub hPint (hCint.const_mul δ), integral_const_mul,
    hPval, hCval]
  have hre : 1 < (s + 1 / 2).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  have hLs : LSeries (fun n => χ n * (Λ n : ℂ)) (s + 1 / 2)
      = -deriv (LSeries fun n => (χ n : ℂ)) (s + 1 / 2)
        / LSeries (fun n => (χ n : ℂ)) (s + 1 / 2) := by
    rw [← DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre]
    exact LSeries_congr (fun _ => rfl) _
  rw [hLs]
  ring

end NCG
