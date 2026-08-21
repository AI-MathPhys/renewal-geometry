/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independent exponential completion stages

This file supplies the probability layer of
`thm:renewal-continuous-completion` from the Gran-Tensor manuscript.  The
canonical sample space is the product of the two exponential laws.  Its
coordinate maps have the prescribed marginal laws, are independent, and their
sum is the two-stage completion time.
-/

open MeasureTheory ProbabilityTheory Real

namespace NCG

noncomputable section

/-- The canonical probability space carrying independent exponential stages
with rates `firstRate` and `secondRate`. -/
def independentExponentialStageMeasure (firstRate secondRate : ℝ) : Measure (ℝ × ℝ) :=
  (expMeasure firstRate).prod (expMeasure secondRate)

/-- The completion-time random variable on the canonical two-stage space. -/
def exponentialCompletionTime : ℝ × ℝ → ℝ := fun ω ↦ ω.1 + ω.2

/-- The probability law of the sum of two independent exponential stages. -/
def independentExponentialCompletionLaw (firstRate secondRate : ℝ) : Measure ℝ :=
  (independentExponentialStageMeasure firstRate secondRate).map exponentialCompletionTime

theorem isProbabilityMeasure_independentExponentialStageMeasure
    {firstRate secondRate : ℝ} (hFirst : 0 < firstRate) (hSecond : 0 < secondRate) :
    IsProbabilityMeasure (independentExponentialStageMeasure firstRate secondRate) := by
  letI : IsProbabilityMeasure (expMeasure firstRate) :=
    isProbabilityMeasure_expMeasure hFirst
  letI : IsProbabilityMeasure (expMeasure secondRate) :=
    isProbabilityMeasure_expMeasure hSecond
  change IsProbabilityMeasure ((expMeasure firstRate).prod (expMeasure secondRate))
  infer_instance

/-- The two coordinate stages on the canonical space are independent. -/
theorem independent_exponentialStages
    {firstRate secondRate : ℝ} (hFirst : 0 < firstRate) (hSecond : 0 < secondRate) :
    Prod.fst ⟂ᵢ[independentExponentialStageMeasure firstRate secondRate] Prod.snd := by
  letI : IsProbabilityMeasure (expMeasure firstRate) :=
    isProbabilityMeasure_expMeasure hFirst
  letI : IsProbabilityMeasure (expMeasure secondRate) :=
    isProbabilityMeasure_expMeasure hSecond
  simpa [independentExponentialStageMeasure] using
    (indepFun_prod (μ := expMeasure firstRate) (ν := expMeasure secondRate)
      (X := id) (Y := id) measurable_id measurable_id)

/-- The first coordinate has the first exponential law. -/
theorem map_fst_independentExponentialStageMeasure
    {firstRate secondRate : ℝ} (_hFirst : 0 < firstRate) (hSecond : 0 < secondRate) :
    Measure.map Prod.fst (independentExponentialStageMeasure firstRate secondRate) =
      expMeasure firstRate := by
  letI : IsProbabilityMeasure (expMeasure secondRate) :=
    isProbabilityMeasure_expMeasure hSecond
  change Measure.map Prod.fst ((expMeasure firstRate).prod (expMeasure secondRate)) = _
  exact (measurePreserving_fst (μ := expMeasure firstRate) (ν := expMeasure secondRate)).map_eq

/-- The second coordinate has the second exponential law. -/
theorem map_snd_independentExponentialStageMeasure
    {firstRate secondRate : ℝ} (hFirst : 0 < firstRate) (hSecond : 0 < secondRate) :
    Measure.map Prod.snd (independentExponentialStageMeasure firstRate secondRate) =
      expMeasure secondRate := by
  letI : IsProbabilityMeasure (expMeasure firstRate) :=
    isProbabilityMeasure_expMeasure hFirst
  letI : IsProbabilityMeasure (expMeasure secondRate) :=
    isProbabilityMeasure_expMeasure hSecond
  change Measure.map Prod.snd ((expMeasure firstRate).prod (expMeasure secondRate)) = _
  exact (measurePreserving_snd (μ := expMeasure firstRate) (ν := expMeasure secondRate)).map_eq

/-- Exact distributional realization of the independent two-stage sum. -/
theorem independentExponentialCompletion_realization
    {firstRate secondRate : ℝ} (hFirst : 0 < firstRate) (hSecond : 0 < secondRate) :
    Prod.fst ⟂ᵢ[independentExponentialStageMeasure firstRate secondRate] Prod.snd ∧
      Measure.map Prod.fst (independentExponentialStageMeasure firstRate secondRate) =
        expMeasure firstRate ∧
      Measure.map Prod.snd (independentExponentialStageMeasure firstRate secondRate) =
        expMeasure secondRate ∧
      independentExponentialCompletionLaw firstRate secondRate =
        Measure.map (fun ω : ℝ × ℝ ↦ ω.1 + ω.2)
          (independentExponentialStageMeasure firstRate secondRate) := by
  exact ⟨independent_exponentialStages hFirst hSecond,
    map_fst_independentExponentialStageMeasure hFirst hSecond,
    map_snd_independentExponentialStageMeasure hFirst hSecond, rfl⟩

end
/-- Laplace transform of one exponential law, proved from mathlib's literal
exponential density rather than assumed as a scalar interface. -/
theorem integral_exp_neg_mul_expMeasure (rate s : ℝ) (hRate : 0 < rate) (hs : 0 ≤ s) :
    ∫ x : ℝ, Real.exp (-(s * x)) ∂expMeasure rate = rate / (rate + s) := by
  have hRateS : 0 < rate + s := by linarith
  rw [expMeasure, gammaMeasure]
  change (∫ x : ℝ, Real.exp (-(s * x))
      ∂volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal 1 rate x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal 1 rate).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg zero_lt_one hRate _), smul_eq_mul]
  have hfun :
      (fun x : ℝ ↦ gammaPDFReal 1 rate x * Real.exp (-(s * x))) =
        Set.indicator (Set.Ici 0)
          (fun x : ℝ ↦ rate * Real.exp (-((rate + s) * x))) := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [gammaPDFReal, if_pos hx]
      norm_num
      simp only [Set.indicator, Set.mem_Ici, if_pos hx]
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    · simp [gammaPDFReal, hx, Set.indicator]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul]
  have hGamma := integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 : ℝ)) (r := rate + s) zero_lt_one hRateS
  norm_num at hGamma
  calc
    rate * ∫ x : ℝ in Set.Ioi 0, Real.exp (-((rate + s) * x)) =
        rate * (rate + s)⁻¹ := by rw [hGamma]
    _ = rate / (rate + s) := by rw [div_eq_mul_inv]


/-- The first moment of an exponential law is the reciprocal of its rate. -/
theorem integral_id_expMeasure (rate : ℝ) (hRate : 0 < rate) :
    ∫ x : ℝ, x ∂expMeasure rate = rate⁻¹ := by
  rw [expMeasure, gammaMeasure]
  change (∫ x : ℝ, x
      ∂volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal 1 rate x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal 1 rate).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg zero_lt_one hRate _), smul_eq_mul]
  have hfun :
      (fun x : ℝ ↦ gammaPDFReal 1 rate x * x) =
        Set.indicator (Set.Ici 0)
          (fun x : ℝ ↦ rate * (x * Real.exp (-(rate * x)))) := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [gammaPDFReal, if_pos hx]
      norm_num
      simp only [Set.indicator, Set.mem_Ici, if_pos hx]
      ring
    · simp [gammaPDFReal, hx, Set.indicator]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul]
  have hGamma := integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := rate) (by norm_num) hRate
  norm_num at hGamma
  calc
    rate * ∫ x : ℝ in Set.Ioi 0, x * Real.exp (-(rate * x)) =
        rate * (rate ^ 2)⁻¹ := by rw [hGamma]
    _ = rate⁻¹ := by field_simp

/-- The identity random variable is integrable under every positive-rate
exponential law. -/
theorem integrable_id_expMeasure (rate : ℝ) (hRate : 0 < rate) :
    Integrable (fun x : ℝ ↦ x) (expMeasure rate) := by
  rw [expMeasure, gammaMeasure]
  change Integrable (fun x : ℝ ↦ x)
    (volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal 1 rate x)))
  rw [integrable_withDensity_iff
    (measurable_gammaPDFReal 1 rate).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg zero_lt_one hRate _)]
  have hfun :
      (fun x : ℝ ↦ x * gammaPDFReal 1 rate x) =
        Set.indicator (Set.Ici 0)
          (fun x : ℝ ↦ rate * (x * Real.exp (-(rate * x)))) := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [gammaPDFReal, if_pos hx]
      norm_num
      simp only [Set.indicator, Set.mem_Ici, if_pos hx]
      ring
    · simp [gammaPDFReal, hx, Set.indicator]
  rw [hfun]
  have hGamma := integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := rate) (by norm_num) hRate
  norm_num at hGamma
  have hBase : IntegrableOn
      (fun x : ℝ ↦ x * Real.exp (-(rate * x))) (Set.Ioi 0) := by
    by_contra hNot
    rw [integral_undef hNot] at hGamma
    have hPositive : 0 < (rate ^ 2)⁻¹ := by positivity
    linarith
  have hScaled : IntegrableOn
      (fun x : ℝ ↦ rate * (x * Real.exp (-(rate * x)))) (Set.Ioi 0) := by
    exact hBase.const_mul rate
  have hScaledClosed : IntegrableOn
      (fun x : ℝ ↦ rate * (x * Real.exp (-(rate * x)))) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun x : ℝ ↦ rate * (x * Real.exp (-(rate * x))))
      (b := 0)).mpr hScaled
  exact hScaledClosed.integrable_indicator measurableSet_Ici


/-- The survival function of a positive-rate exponential law.  This is the
holding-time characterization used by continuous-time jump chains. -/
theorem expMeasure_real_Ioi (rate t : ℝ) (hRate : 0 < rate) (ht : 0 ≤ t) :
    (expMeasure rate).real (Set.Ioi t) = Real.exp (-(rate * t)) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hRate
  rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
    ← cdf_eq_real, cdf_expMeasure_eq hRate, if_pos ht]
  ring

/-- The right derivative at zero of exponential survival is minus the holding
rate.  Thus the rate is recovered intrinsically from the holding-time law. -/
theorem expMeasure_survival_hasDerivWithinAt_zero (rate : ℝ) (hRate : 0 < rate) :
    HasDerivWithinAt (fun t : ℝ ↦ (expMeasure rate).real (Set.Ioi t))
      (-rate) (Set.Ici 0) 0 := by
  have hExp : HasDerivWithinAt (fun t : ℝ ↦ Real.exp (-(rate * t)))
      (-rate) (Set.Ici 0) 0 := by
    have hAt := (hasDerivAt_neg_exp_mul_exp (r := rate) (x := (0 : ℝ))).neg
    have hWithin : HasDerivWithinAt (fun t : ℝ ↦ Real.exp (-(rate * t)))
        (-(rate * Real.exp (-(rate * (0 : ℝ))))) (Set.Ici 0) 0 := by
      refine (hAt.hasDerivWithinAt (s := Set.Ici 0)).congr_of_mem ?_ (by simp)
      intro t _
      simp
    simpa using hWithin
  refine hExp.congr_of_mem ?_ (by simp)
  intro t ht
  exact expMeasure_real_Ioi rate t hRate ht

/-- At the manuscript rates, the two holding-time survival derivatives are
exactly the two diagonal exit rates of `L₀`. -/
theorem renewal_exponentialStage_survival_derivatives (lam : ℝ) (hLam : 0 < lam) :
    HasDerivWithinAt (fun t : ℝ ↦ (expMeasure (4 * lam / 5)).real (Set.Ioi t))
        (-(4 * lam / 5)) (Set.Ici 0) 0 ∧
      HasDerivWithinAt (fun t : ℝ ↦ (expMeasure (2 * lam / 3)).real (Set.Ioi t))
        (-(2 * lam / 3)) (Set.Ici 0) 0 := by
  exact ⟨expMeasure_survival_hasDerivWithinAt_zero _ (by positivity),
    expMeasure_survival_hasDerivWithinAt_zero _ (by positivity)⟩
/-- The Laplace transform of the independent two-stage completion time is the
product of the two exponential transforms. -/
theorem integral_exp_neg_mul_exponentialCompletionTime
    (firstRate secondRate s : ℝ) (hFirst : 0 < firstRate)
    (hSecond : 0 < secondRate) (hs : 0 ≤ s) :
    ∫ ω : ℝ × ℝ, Real.exp (-(s * exponentialCompletionTime ω))
        ∂independentExponentialStageMeasure firstRate secondRate =
      firstRate / (firstRate + s) * (secondRate / (secondRate + s)) := by
  letI : IsProbabilityMeasure (expMeasure firstRate) :=
    isProbabilityMeasure_expMeasure hFirst
  letI : IsProbabilityMeasure (expMeasure secondRate) :=
    isProbabilityMeasure_expMeasure hSecond
  change (∫ ω : ℝ × ℝ, Real.exp (-(s * (ω.1 + ω.2)))
      ∂(expMeasure firstRate).prod (expMeasure secondRate)) = _
  have hfactor :
      (fun ω : ℝ × ℝ ↦ Real.exp (-(s * (ω.1 + ω.2)))) =
        fun ω ↦ Real.exp (-(s * ω.1)) * Real.exp (-(s * ω.2)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfactor]
  calc
    ∫ ω : ℝ × ℝ, Real.exp (-(s * ω.1)) * Real.exp (-(s * ω.2))
        ∂(expMeasure firstRate).prod (expMeasure secondRate) =
      (∫ x : ℝ, Real.exp (-(s * x)) ∂expMeasure firstRate) *
        ∫ y : ℝ, Real.exp (-(s * y)) ∂expMeasure secondRate :=
          integral_prod_mul (μ := expMeasure firstRate) (ν := expMeasure secondRate)
            (fun x : ℝ ↦ Real.exp (-(s * x))) (fun y : ℝ ↦ Real.exp (-(s * y)))
    _ = _ := by rw [integral_exp_neg_mul_expMeasure firstRate s hFirst hs,
      integral_exp_neg_mul_expMeasure secondRate s hSecond hs]

/-- The mean of the independent two-stage completion time is the sum of the
reciprocal rates. -/
theorem integral_exponentialCompletionTime
    (firstRate secondRate : ℝ) (hFirst : 0 < firstRate)
    (hSecond : 0 < secondRate) :
    ∫ ω : ℝ × ℝ, exponentialCompletionTime ω
        ∂independentExponentialStageMeasure firstRate secondRate =
      firstRate⁻¹ + secondRate⁻¹ := by
  letI : IsProbabilityMeasure (expMeasure firstRate) :=
    isProbabilityMeasure_expMeasure hFirst
  letI : IsProbabilityMeasure (expMeasure secondRate) :=
    isProbabilityMeasure_expMeasure hSecond
  have hFst : Integrable (fun ω : ℝ × ℝ ↦ ω.1)
      ((expMeasure firstRate).prod (expMeasure secondRate)) :=
    (integrable_id_expMeasure firstRate hFirst).comp_fst (expMeasure secondRate)
  have hSnd : Integrable (fun ω : ℝ × ℝ ↦ ω.2)
      ((expMeasure firstRate).prod (expMeasure secondRate)) :=
    (integrable_id_expMeasure secondRate hSecond).comp_snd (expMeasure firstRate)
  change (∫ ω : ℝ × ℝ, ω.1 + ω.2
      ∂(expMeasure firstRate).prod (expMeasure secondRate)) = _
  rw [integral_add hFst hSnd]
  calc
    (∫ a : ℝ × ℝ, a.1 ∂(expMeasure firstRate).prod (expMeasure secondRate)) +
        ∫ a : ℝ × ℝ, a.2 ∂(expMeasure firstRate).prod (expMeasure secondRate) =
      (expMeasure secondRate).real Set.univ • (∫ x : ℝ, x ∂expMeasure firstRate) +
        (expMeasure firstRate).real Set.univ • (∫ y : ℝ, y ∂expMeasure secondRate) := by
          congr 1
          · exact integral_fun_fst (μ := expMeasure firstRate)
              (ν := expMeasure secondRate) (fun x : ℝ ↦ x)
          · exact integral_fun_snd (μ := expMeasure firstRate)
              (ν := expMeasure secondRate) (fun y : ℝ ↦ y)
    _ = firstRate⁻¹ + secondRate⁻¹ := by
      rw [integral_id_expMeasure firstRate hFirst, integral_id_expMeasure secondRate hSecond]
      simp
/-- Generic handoff from any concrete stochastic construction to the canonical
two-stage completion law.  Once a model supplies two measurable independent
holding times with exponential marginal laws, their sum has exactly
`independentExponentialCompletionLaw`. -/
theorem map_add_eq_independentExponentialCompletionLaw_of_independent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (firstHolding secondHolding : Ω → ℝ) (firstRate secondRate : ℝ)
    (mFirst : Measurable firstHolding) (mSecond : Measurable secondHolding)
    (hFirstLaw : Measure.map firstHolding μ = expMeasure firstRate)
    (hSecondLaw : Measure.map secondHolding μ = expMeasure secondRate)
    (hIndep : firstHolding ⟂ᵢ[μ] secondHolding) :
    Measure.map (fun ω ↦ firstHolding ω + secondHolding ω) μ =
      independentExponentialCompletionLaw firstRate secondRate := by
  have mPair : Measurable (fun ω ↦ (firstHolding ω, secondHolding ω)) :=
    mFirst.prodMk mSecond
  have mSum : Measurable exponentialCompletionTime := by
    exact measurable_fst.add measurable_snd
  have hJoint :
      Measure.map (fun ω ↦ (firstHolding ω, secondHolding ω)) μ =
        (expMeasure firstRate).prod (expMeasure secondRate) := by
    rw [hIndep.map_prod_eq_prod_map_map mFirst.aemeasurable mSecond.aemeasurable,
      hFirstLaw, hSecondLaw]
  rw [independentExponentialCompletionLaw, independentExponentialStageMeasure]
  calc
    Measure.map (fun ω ↦ firstHolding ω + secondHolding ω) μ =
        Measure.map exponentialCompletionTime
          (Measure.map (fun ω ↦ (firstHolding ω, secondHolding ω)) μ) := by
      rw [Measure.map_map mSum mPair]
      rfl
    _ = Measure.map exponentialCompletionTime
        ((expMeasure firstRate).prod (expMeasure secondRate)) := by rw [hJoint]


/-- The manuscript's completion stages, with rates `4λ/5` and `2λ/3`, are
realized as independent coordinate random variables with exactly those laws. -/
theorem renewalCompletionTime_independent_exponential_realization
    (lam : ℝ) (hLam : 0 < lam) :
    Prod.fst ⟂ᵢ[independentExponentialStageMeasure (4 * lam / 5) (2 * lam / 3)]
        Prod.snd ∧
      Measure.map Prod.fst
          (independentExponentialStageMeasure (4 * lam / 5) (2 * lam / 3)) =
        expMeasure (4 * lam / 5) ∧
      Measure.map Prod.snd
          (independentExponentialStageMeasure (4 * lam / 5) (2 * lam / 3)) =
        expMeasure (2 * lam / 3) ∧
      independentExponentialCompletionLaw (4 * lam / 5) (2 * lam / 3) =
        Measure.map (fun ω : ℝ × ℝ ↦ ω.1 + ω.2)
          (independentExponentialStageMeasure (4 * lam / 5) (2 * lam / 3)) := by
  exact independentExponentialCompletion_realization (by positivity) (by positivity)

/-- Boxed manuscript Laplace transform for the genuine completion-time random
variable on the independent product probability space. -/
theorem renewalCompletionTime_laplace (lam s : ℝ) (hLam : 0 < lam) (hs : 0 ≤ s) :
    ∫ ω : ℝ × ℝ, Real.exp (-(s * exponentialCompletionTime ω))
        ∂independentExponentialStageMeasure (4 * lam / 5) (2 * lam / 3) =
      8 * lam ^ 2 / ((4 * lam + 5 * s) * (2 * lam + 3 * s)) := by
  rw [integral_exp_neg_mul_exponentialCompletionTime
    (4 * lam / 5) (2 * lam / 3) s (by positivity) (by positivity) hs]
  have h1 : 4 * lam / 5 + s ≠ 0 := by positivity
  have h2 : 2 * lam / 3 + s ≠ 0 := by positivity
  have h3 : 4 * lam + 5 * s ≠ 0 := by positivity
  have h4 : 2 * lam + 3 * s ≠ 0 := by positivity
  field_simp
  ring

/-- Boxed manuscript mean and physical event intensity, now evaluated from
the actual independent two-stage probability model. -/
theorem renewalCompletionTime_mean_and_intensity (lam : ℝ) (hLam : 0 < lam) :
    (∫ ω : ℝ × ℝ, exponentialCompletionTime ω
        ∂independentExponentialStageMeasure (4 * lam / 5) (2 * lam / 3)) =
        11 / (4 * lam) ∧
      (∫ ω : ℝ × ℝ, exponentialCompletionTime ω
        ∂independentExponentialStageMeasure (4 * lam / 5) (2 * lam / 3))⁻¹ =
        4 * lam / 11 := by
  rw [integral_exponentialCompletionTime
    (4 * lam / 5) (2 * lam / 3) (by positivity) (by positivity)]
  constructor
  · field_simp
    ring
  · field_simp
    ring


end NCG
