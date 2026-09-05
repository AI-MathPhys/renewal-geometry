/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.AcceptedResponseLaw
import NCG.Grand.RenewalProfiles
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Topology.MetricSpace.Algebra

/-!
# Analytic pressure of the accepted-response renewal

This module constructs the pressure branch from the actual accepted-response
PMF.  A rationalized quadratic root removes the apparent singularity when the
quadratic coefficient vanishes.  The resulting branch is analytic at the
origin and has the exact response-rate derivative.
-/

noncomputable section

open Matrix Topology Filter

namespace NCG

/-- Quadratic coefficient in the accepted-response pressure equation. -/
def acceptedPressureCoefficient (θ q : ℝ) : ℝ :=
  7 + 8 * θ * (Real.exp (-q) - 1)

/-- Discriminant of the accepted-response pressure quadratic. -/
def acceptedPressureDiscriminant (θ q : ℝ) : ℝ :=
  64 + 60 * acceptedPressureCoefficient θ q

/-- Analytic positive square-root germ on the positive real axis. -/
def analyticPositiveSqrt (x : ℝ) : ℝ :=
  Real.exp (Real.log x / 2)

theorem analyticPositiveSqrt_eq_sqrt {x : ℝ} (hx : 0 < x) :
    analyticPositiveSqrt x = Real.sqrt x := by
  rw [analyticPositiveSqrt, Real.exp_half, Real.exp_log hx]

/-- Rationalized positive root.  Unlike the usual quadratic formula, this
expression already has the continuous value at `A = 0`. -/
def acceptedPressureRoot (θ q : ℝ) : ℝ :=
  30 * (8 + analyticPositiveSqrt
    (acceptedPressureDiscriminant θ q))⁻¹

/-- Accepted-response pressure, normalized by one protected tick of duration
`h`. -/
def acceptedResponsePressure (θ h q : ℝ) : ℝ :=
  -Real.log (acceptedPressureRoot θ q) / h

/-- Operator-valued tilted first-return effect of the actual PMF. -/
def acceptedTiltedFirstReturnEffect {ι : Type*} [Fintype ι]
    [DecidableEq ι] (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (h q r : ℝ) : Matrix ι ι ℝ :=
  (Real.exp (-q) * pmfPgf (acceptedResponseWaitingPMF θ hθ hθ1)
    (Real.exp (-h * r))) • (1 : Matrix ι ι ℝ)

theorem acceptedTiltedFirstReturnEffect_formula {ι : Type*} [Fintype ι]
    [DecidableEq ι] (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (h q r : ℝ) :
    acceptedTiltedFirstReturnEffect (ι := ι) θ hθ hθ1 h q r =
      (Real.exp (-q) * pmfPgf (acceptedResponseWaitingPMF θ hθ hθ1)
        (Real.exp (-h * r))) • (1 : Matrix ι ι ℝ) := rfl

@[simp] theorem acceptedPressureCoefficient_zero (θ : ℝ) :
    acceptedPressureCoefficient θ 0 = 7 := by
  simp [acceptedPressureCoefficient]

@[simp] theorem acceptedPressureDiscriminant_zero (θ : ℝ) :
    acceptedPressureDiscriminant θ 0 = 484 := by
  norm_num [acceptedPressureDiscriminant]

@[simp] theorem analyticPositiveSqrt_484 :
    analyticPositiveSqrt 484 = 22 := by
  rw [analyticPositiveSqrt_eq_sqrt (by norm_num)]
  norm_num

@[simp] theorem acceptedPressureRoot_zero (θ : ℝ) :
    acceptedPressureRoot θ 0 = 1 := by
  norm_num [acceptedPressureRoot]

@[simp] theorem acceptedResponsePressure_zero (θ h : ℝ) :
    acceptedResponsePressure θ h 0 = 0 := by
  simp [acceptedResponsePressure]

theorem acceptedPressureRoot_pos {θ q : ℝ}
    (hdisc : 0 < acceptedPressureDiscriminant θ q) :
    0 < acceptedPressureRoot θ q := by
  have hsqrt : 0 < analyticPositiveSqrt
      (acceptedPressureDiscriminant θ q) := by
    rw [analyticPositiveSqrt_eq_sqrt hdisc]
    exact Real.sqrt_pos.2 hdisc
  unfold acceptedPressureRoot
  exact mul_pos (by norm_num) (inv_pos.2 (by linarith))

/-- The rationalized root satisfies the pressure quadratic wherever the
discriminant is positive, including the removable case `A = 0`. -/
theorem acceptedPressureRoot_quadratic {θ q : ℝ}
    (hdisc : 0 < acceptedPressureDiscriminant θ q) :
    acceptedPressureCoefficient θ q * acceptedPressureRoot θ q ^ 2 +
      8 * acceptedPressureRoot θ q - 15 = 0 := by
  have hsqrt := analyticPositiveSqrt_eq_sqrt hdisc
  have hsquare : analyticPositiveSqrt
      (acceptedPressureDiscriminant θ q) ^ 2 =
      acceptedPressureDiscriminant θ q := by
    rw [hsqrt, Real.sq_sqrt hdisc.le]
  have hden : 8 + analyticPositiveSqrt
      (acceptedPressureDiscriminant θ q) ≠ 0 := by
    have hspos : 0 < analyticPositiveSqrt
        (acceptedPressureDiscriminant θ q) := by
      rw [hsqrt]
      exact Real.sqrt_pos.2 hdisc
    linarith
  unfold acceptedPressureRoot
  field_simp [hden]
  unfold acceptedPressureDiscriminant at hsquare ⊢
  ring_nf at hsquare ⊢
  nlinarith

/-- Agreement with the displayed quadratic formula away from its removable
zero. -/
theorem acceptedPressureRoot_eq_displayed {θ q : ℝ}
    (hdisc : 0 < acceptedPressureDiscriminant θ q)
    (hA : acceptedPressureCoefficient θ q ≠ 0) :
    acceptedPressureRoot θ q =
      (-8 + Real.sqrt (64 + 60 * acceptedPressureCoefficient θ q)) /
        (2 * acceptedPressureCoefficient θ q) := by
  have hsqrt := analyticPositiveSqrt_eq_sqrt hdisc
  have hsquare : analyticPositiveSqrt
      (acceptedPressureDiscriminant θ q) ^ 2 =
      acceptedPressureDiscriminant θ q := by
    rw [hsqrt, Real.sq_sqrt hdisc.le]
  have hden : 8 + analyticPositiveSqrt
      (acceptedPressureDiscriminant θ q) ≠ 0 := by
    have hspos : 0 < analyticPositiveSqrt
        (acceptedPressureDiscriminant θ q) := by
      rw [hsqrt]
      exact Real.sqrt_pos.2 hdisc
    linarith
  rw [show Real.sqrt (64 + 60 * acceptedPressureCoefficient θ q) =
      analyticPositiveSqrt (acceptedPressureDiscriminant θ q) by
        simpa [acceptedPressureDiscriminant] using hsqrt.symm]
  unfold acceptedPressureRoot
  field_simp [hA, hden]
  unfold acceptedPressureDiscriminant at hsquare ⊢
  ring_nf at hsquare ⊢
  nlinarith

/-- The explicit pressure branch is real analytic at the origin. -/
theorem acceptedResponsePressure_analyticAt (θ h : ℝ) :
    AnalyticAt ℝ (acceptedResponsePressure θ h) 0 := by
  unfold acceptedResponsePressure acceptedPressureRoot
    analyticPositiveSqrt acceptedPressureDiscriminant
    acceptedPressureCoefficient
  let D : ℝ → ℝ := fun q =>
    64 + 60 * (7 + 8 * θ * (Real.exp (-q) - 1))
  have hD : AnalyticAt ℝ D 0 := by
    dsimp [D]
    fun_prop
  have hDpos : 0 < D 0 := by norm_num [D]
  have hlogD : AnalyticAt ℝ (fun q => Real.log (D q)) 0 := hD.log hDpos
  have hs : AnalyticAt ℝ
      (fun q => Real.exp (Real.log (D q) / 2)) 0 := by
    fun_prop
  have hden : AnalyticAt ℝ
      (fun q => 8 + Real.exp (Real.log (D q) / 2)) 0 := by
    fun_prop
  have hroot : AnalyticAt ℝ
      (fun q => 30 * (8 + Real.exp (Real.log (D q) / 2))⁻¹) 0 := by
    exact analyticAt_const.mul (hden.inv (by positivity))
  have hrootpos : 0 < 30 *
      (8 + Real.exp (Real.log (D 0) / 2))⁻¹ := by
    positivity
  exact (hroot.log hrootpos).neg.div_const (c := h)

/-- Exact derivative of the pressure at the partition anchor. -/
theorem acceptedResponsePressure_hasDerivAt (θ h : ℝ) (hh : 0 < h) :
    HasDerivAt (acceptedResponsePressure θ h)
      (-4 * θ / (11 * h)) 0 := by
  have he : HasDerivAt (fun q : ℝ => Real.exp (-q)) (-1) 0 := by
    have hid : HasDerivAt (fun q : ℝ => q) 1 0 :=
      hasDerivAt_id' (x := 0)
    convert hid.neg.exp using 1 <;> norm_num
  have hA : HasDerivAt
      (fun q : ℝ => 7 + 8 * θ * (Real.exp (-q) - 1)) (-8 * θ) 0 := by
    exact (((he.sub_const 1).const_mul (8 * θ)).const_add 7).congr_deriv
      (by ring)
  have hD : HasDerivAt
      (fun q : ℝ => 64 + 60 * (7 + 8 * θ * (Real.exp (-q) - 1)))
      (-480 * θ) 0 := by
    exact ((hA.const_mul 60).const_add 64).congr_deriv (by ring)
  have hlogD := hD.log (by norm_num)
  have hhalf := hlogD.div_const 2
  have hs := hhalf.exp
  have hden := hs.const_add 8
  have hden0 : 8 + Real.exp
      (Real.log (64 + 60 * (7 + 8 * θ * (Real.exp (-0) - 1))) / 2) ≠ 0 := by
    positivity
  have hinv := hden.inv hden0
  have hroot := hinv.const_mul 30
  have hroot0 : 30 / (8 + Real.exp
      (Real.log (64 + 60 * (7 + 8 * θ * (Real.exp (-0) - 1))) / 2)) ≠ 0 := by
    positivity
  have hlogroot := hroot.log hroot0
  have hp := hlogroot.neg.div_const h
  apply hp.congr_deriv
  simp only [neg_zero, Real.exp_zero, sub_self, mul_zero, add_zero]
  norm_num only
  simp only [Pi.inv_apply]
  simp only [neg_zero, Real.exp_zero, sub_self, mul_zero, add_zero]
  norm_num only
  rw [show Real.exp (Real.log (484 : ℝ) / 2) = 22 by
    rw [Real.exp_half, Real.exp_log (by norm_num)]
    norm_num]
  field_simp [ne_of_gt hh]
  ring

theorem acceptedResponsePressure_deriv (θ h : ℝ) (hh : 0 < h) :
    deriv (acceptedResponsePressure θ h) 0 = -4 * θ / (11 * h) :=
  (acceptedResponsePressure_hasDerivAt θ h hh).deriv

/-- Exact mean/pressure anchor identity. -/
theorem acceptedResponsePressure_mean_anchor (θ h : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hh : 0 < h) :
    -h * pmfFirstMoment (acceptedResponseWaitingPMF θ hθ hθ1) *
      deriv (acceptedResponsePressure θ h) 0 = 1 := by
  rw [acceptedResponseWaitingPMF_firstMoment θ hθ hθ1,
    acceptedResponsePressure_deriv θ h hh]
  field_simp [ne_of_gt hθ, ne_of_gt hh]

/-- Exponentiating the pressure recovers the positive quadratic root. -/
theorem exp_neg_mul_acceptedResponsePressure {θ h q : ℝ}
    (hh : h ≠ 0) (hdisc : 0 < acceptedPressureDiscriminant θ q) :
    Real.exp (-h * acceptedResponsePressure θ h q) =
      acceptedPressureRoot θ q := by
  rw [acceptedResponsePressure]
  have hroot := acceptedPressureRoot_pos hdisc
  rw [show -h * (-Real.log (acceptedPressureRoot θ q) / h) =
      Real.log (acceptedPressureRoot θ q) by field_simp]
  exact Real.exp_log hroot

/-- Pointwise normalization of the actual PMF-valued first-return effect. -/
theorem acceptedResponsePressure_normalizes {ι : Type*} [Fintype ι]
    [DecidableEq ι] {θ h q : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hh : h ≠ 0) (hdisc : 0 < acceptedPressureDiscriminant θ q)
    (hz3 : acceptedPressureRoot θ q < 3)
    (hcontract : |(1 - θ) *
      (8 * acceptedPressureRoot θ q ^ 2 /
        ((5 - acceptedPressureRoot θ q) *
          (3 - acceptedPressureRoot θ q)))| < 1) :
    acceptedTiltedFirstReturnEffect (ι := ι) θ hθ hθ1 h q
        (acceptedResponsePressure θ h q) = 1 := by
  have hzpos := acceptedPressureRoot_pos hdisc
  rw [acceptedTiltedFirstReturnEffect,
    exp_neg_mul_acceptedResponsePressure hh hdisc,
    acceptedResponseWaitingPMF_pgf_of_lt_three θ hθ hθ1
      hzpos.le hz3 hcontract]
  have hquad := acceptedPressureRoot_quadratic hdisc
  have hθne : θ ≠ 0 := ne_of_gt hθ
  have hz_ne : acceptedPressureRoot θ q ≠ 0 := ne_of_gt hzpos
  have he_ne : Real.exp (-q) ≠ 0 := Real.exp_ne_zero _
  have hden : 15 - 8 * acceptedPressureRoot θ q +
      (8 * θ - 7) * acceptedPressureRoot θ q ^ 2 =
        8 * θ * Real.exp (-q) * acceptedPressureRoot θ q ^ 2 := by
    unfold acceptedPressureCoefficient at hquad
    nlinarith
  have hscalar : Real.exp (-q) *
      (8 * θ * acceptedPressureRoot θ q ^ 2 /
        (15 - 8 * acceptedPressureRoot θ q +
          (8 * θ - 7) * acceptedPressureRoot θ q ^ 2)) = 1 := by
    rw [hden]
    field_simp [hθne, hz_ne, he_ne]
  rw [hscalar]
  simp

/-- The explicit positive root is the unique positive root whenever the
quadratic coefficient is positive. -/
theorem acceptedPressureRoot_unique_positive {θ q x : ℝ}
    (hdisc : 0 < acceptedPressureDiscriminant θ q)
    (hA : 0 < acceptedPressureCoefficient θ q) (hx : 0 < x)
    (hquad : acceptedPressureCoefficient θ q * x ^ 2 + 8 * x - 15 = 0) :
    x = acceptedPressureRoot θ q := by
  have hy := acceptedPressureRoot_pos hdisc
  have hyquad := acceptedPressureRoot_quadratic hdisc
  have hsum : 0 < acceptedPressureCoefficient θ q *
      (x + acceptedPressureRoot θ q) + 8 := by positivity
  have hfactor : (x - acceptedPressureRoot θ q) *
      (acceptedPressureCoefficient θ q *
        (x + acceptedPressureRoot θ q) + 8) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hxy | hzero
  · exact sub_eq_zero.mp hxy
  · exact (ne_of_gt hsum hzero).elim

/-- Uniqueness of the analytic pressure germ: any analytic branch through
zero satisfying the same pressure quadratic agrees near the origin. -/
theorem acceptedResponsePressure_unique_analytic_germ {θ h : ℝ}
    (hh : h ≠ 0) (P : ℝ → ℝ) (_hP : AnalyticAt ℝ P 0) (_hP0 : P 0 = 0)
    (hquad : ∀ᶠ q in 𝓝 0,
      acceptedPressureCoefficient θ q * Real.exp (-h * P q) ^ 2 +
        8 * Real.exp (-h * P q) - 15 = 0) :
    P =ᶠ[𝓝 0] acceptedResponsePressure θ h := by
  have hDcont : ContinuousAt (acceptedPressureDiscriminant θ) 0 := by
    unfold acceptedPressureDiscriminant acceptedPressureCoefficient
    fun_prop
  have hDisc : ∀ᶠ q in 𝓝 0, 0 < acceptedPressureDiscriminant θ q :=
    continuousAt_const.eventually_lt hDcont (by norm_num)
  have hAcont : ContinuousAt (acceptedPressureCoefficient θ) 0 := by
    unfold acceptedPressureCoefficient
    fun_prop
  have hAPos : ∀ᶠ q in 𝓝 0, 0 < acceptedPressureCoefficient θ q :=
    continuousAt_const.eventually_lt hAcont (by norm_num)
  filter_upwards [hquad, hDisc, hAPos] with q hq hdisc hA
  have hrootEq := acceptedPressureRoot_unique_positive hdisc hA
    (Real.exp_pos _) hq
  have hexpPressure := exp_neg_mul_acceptedResponsePressure hh hdisc
  have : -h * P q = -h * acceptedResponsePressure θ h q := by
    exact Real.exp_injective (hrootEq.trans hexpPressure.symm)
  exact (mul_left_cancel₀ (neg_ne_zero.mpr hh) this)

/-- The rationalized positive root is analytic at the source anchor. -/
theorem acceptedPressureRoot_analyticAt (θ : ℝ) :
    AnalyticAt ℝ (acceptedPressureRoot θ) 0 := by
  unfold acceptedPressureRoot analyticPositiveSqrt
    acceptedPressureDiscriminant acceptedPressureCoefficient
  let D : ℝ → ℝ := fun q =>
    64 + 60 * (7 + 8 * θ * (Real.exp (-q) - 1))
  have hD : AnalyticAt ℝ D 0 := by
    dsimp [D]
    fun_prop
  have hDpos : 0 < D 0 := by norm_num [D]
  have hlogD : AnalyticAt ℝ (fun q => Real.log (D q)) 0 := hD.log hDpos
  have hs : AnalyticAt ℝ
      (fun q => Real.exp (Real.log (D q) / 2)) 0 := by
    fun_prop
  have hden : AnalyticAt ℝ
      (fun q => 8 + Real.exp (Real.log (D q) / 2)) 0 := by
    fun_prop
  exact analyticAt_const.mul (hden.inv (by positivity))

/-- On a whole neighborhood of the source anchor, the explicit pressure
normalizes the operator-valued first-return effect of the actual law. -/
theorem acceptedResponsePressure_eventually_normalizes {ι : Type*}
    [Fintype ι] [DecidableEq ι] {θ h : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hh : h ≠ 0) :
    ∀ᶠ q in 𝓝 0,
      acceptedTiltedFirstReturnEffect (ι := ι) θ hθ hθ1 h q
        (acceptedResponsePressure θ h q) = 1 := by
  have hDcont : ContinuousAt (acceptedPressureDiscriminant θ) 0 := by
    unfold acceptedPressureDiscriminant acceptedPressureCoefficient
    fun_prop
  have hDisc : ∀ᶠ q in 𝓝 0, 0 < acceptedPressureDiscriminant θ q :=
    continuousAt_const.eventually_lt hDcont (by norm_num)
  have hrootCont : ContinuousAt (acceptedPressureRoot θ) 0 :=
    (acceptedPressureRoot_analyticAt θ).continuousAt
  have hz3 : ∀ᶠ q in 𝓝 0, acceptedPressureRoot θ q < 3 :=
    hrootCont.eventually_lt continuousAt_const (by norm_num)
  let C : ℝ → ℝ := fun q => |(1 - θ) *
    (8 * acceptedPressureRoot θ q ^ 2 /
      ((5 - acceptedPressureRoot θ q) *
        (3 - acceptedPressureRoot θ q)))|
  have hCcont : ContinuousAt C 0 := by
    dsimp [C]
    have hden0 : (5 - acceptedPressureRoot θ 0) *
        (3 - acceptedPressureRoot θ 0) ≠ 0 := by norm_num
    fun_prop
  have hC0 : C 0 < 1 := by
    dsimp [C]
    simp only [acceptedPressureRoot_zero, one_pow]
    norm_num
    rw [abs_of_nonneg (sub_nonneg.mpr hθ1)]
    linarith
  have hContract : ∀ᶠ q in 𝓝 0, C q < 1 :=
    hCcont.eventually_lt continuousAt_const hC0
  filter_upwards [hDisc, hz3, hContract] with q hdisc hroot3 hcontract
  exact acceptedResponsePressure_normalizes hθ hθ1 hh hdisc hroot3 hcontract

/-- Exact source-independent partition anchor. -/
theorem acceptedResponsePressure_partition_anchor {ι : Type*}
    [Fintype ι] [DecidableEq ι] {θ h : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    acceptedTiltedFirstReturnEffect (ι := ι) θ hθ hθ1 h 0
        (acceptedResponsePressure θ h 0) = 1 := by
  simp [acceptedTiltedFirstReturnEffect, pmfPgf_one]

/-! ## Poisson scaling -/

/-- The rationalized velocity in the acceptance parameter. -/
def acceptedPressureVelocity (θ q : ℝ) : ℝ :=
  16 * (Real.exp (-q) - 1) /
    (analyticPositiveSqrt (acceptedPressureDiscriminant θ q) + 22)

/-- Continuous extension of the quotient
`-log (acceptedPressureRoot θ q) / θ` through `θ = 0`. -/
def acceptedPressurePoissonKernel (θ q : ℝ) : ℝ :=
  acceptedPressureVelocity θ q *
    dslope Real.log 1 (1 + θ * acceptedPressureVelocity θ q)

@[simp] theorem acceptedPressureVelocity_zero (q : ℝ) :
    acceptedPressureVelocity 0 q =
      (4 / 11 : ℝ) * (Real.exp (-q) - 1) := by
  norm_num [acceptedPressureVelocity, acceptedPressureDiscriminant,
    acceptedPressureCoefficient]
  ring

@[simp] theorem acceptedPressurePoissonKernel_zero (q : ℝ) :
    acceptedPressurePoissonKernel 0 q =
      (4 / 11 : ℝ) * (Real.exp (-q) - 1) := by
  simp [acceptedPressurePoissonKernel, dslope_same, Real.deriv_log]

/-- Joint continuity of the extended pressure quotient along the entire
`θ = 0` axis.  This is the uniformity input for the Poisson limit. -/
theorem acceptedPressurePoissonKernel_continuousAt_zero (q₀ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ =>
      acceptedPressurePoissonKernel p.1 p.2) (0, q₀) := by
  have hdisc0 : acceptedPressureDiscriminant (0 : ℝ) q₀ = 484 := by
    norm_num [acceptedPressureDiscriminant, acceptedPressureCoefficient]
  have hdisc_ne : acceptedPressureDiscriminant (0 : ℝ) q₀ ≠ 0 := by
    rw [hdisc0]
    norm_num
  have hs : ContinuousAt (fun p : ℝ × ℝ =>
      analyticPositiveSqrt (acceptedPressureDiscriminant p.1 p.2))
      (0, q₀) := by
    have hdiscCont : ContinuousAt (fun p : ℝ × ℝ =>
        acceptedPressureDiscriminant p.1 p.2) (0, q₀) := by
      unfold acceptedPressureDiscriminant acceptedPressureCoefficient
      fun_prop
    unfold analyticPositiveSqrt
    exact Real.continuous_exp.continuousAt.comp
      ((hdiscCont.log hdisc_ne).div_const 2)
  have hden : analyticPositiveSqrt
      (acceptedPressureDiscriminant (0 : ℝ) q₀) + 22 ≠ 0 := by
    rw [hdisc0, analyticPositiveSqrt_484]
    norm_num
  have hv : ContinuousAt (fun p : ℝ × ℝ =>
      acceptedPressureVelocity p.1 p.2) (0, q₀) := by
    unfold acceptedPressureVelocity
    fun_prop
  have hinter : ContinuousAt (fun p : ℝ × ℝ =>
      1 + p.1 * acceptedPressureVelocity p.1 p.2) (0, q₀) := by
    fun_prop
  have hinter0 : 1 + (0 : ℝ) * acceptedPressureVelocity 0 q₀ = 1 := by
    ring
  have hlogSlope : ContinuousAt (dslope Real.log 1) 1 :=
    continuousAt_dslope_same.2
      (Real.hasDerivAt_log (by norm_num)).differentiableAt
  have hcomp : ContinuousAt (fun p : ℝ × ℝ =>
      dslope Real.log 1
        (1 + p.1 * acceptedPressureVelocity p.1 p.2)) (0, q₀) := by
    simpa [Function.comp_def] using hlogSlope.comp_of_eq hinter hinter0
  exact hv.mul hcomp

/-- The extended pressure quotient converges locally uniformly in the source
variable. -/
theorem acceptedPressurePoissonKernel_tendstoLocallyUniformly :
    TendstoLocallyUniformly
      (fun θ q => acceptedPressurePoissonKernel θ q)
      (fun q => (4 / 11 : ℝ) * (Real.exp (-q) - 1)) (𝓝 0) := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro q₀
  apply tendsto_uniformity_iff_dist_tendsto_zero.2
  have hkernel : Tendsto (fun p : ℝ × ℝ =>
      acceptedPressurePoissonKernel p.1 p.2)
      (𝓝 0 ×ˢ 𝓝 q₀)
      (𝓝 (acceptedPressurePoissonKernel 0 q₀)) := by
    have hk := (acceptedPressurePoissonKernel_continuousAt_zero q₀).tendsto
    rwa [nhds_prod_eq] at hk
  have hlimit : Tendsto (fun p : ℝ × ℝ =>
      (4 / 11 : ℝ) * (Real.exp (-p.2) - 1))
      (𝓝 0 ×ˢ 𝓝 q₀)
      (𝓝 ((4 / 11 : ℝ) * (Real.exp (-q₀) - 1))) := by
    have hc : ContinuousAt (fun p : ℝ × ℝ =>
        (4 / 11 : ℝ) * (Real.exp (-p.2) - 1)) (0, q₀) := by
      fun_prop
    have ht := hc.tendsto
    rwa [nhds_prod_eq] at ht
  simpa using hlimit.dist hkernel

/-- Rationalization identity behind the removable quotient. -/
theorem one_add_mul_acceptedPressureVelocity {θ q : ℝ}
    (hdisc : 0 < acceptedPressureDiscriminant θ q) :
    1 + θ * acceptedPressureVelocity θ q =
      (acceptedPressureRoot θ q)⁻¹ := by
  have hsqrt := analyticPositiveSqrt_eq_sqrt hdisc
  have hspos : 0 < analyticPositiveSqrt
      (acceptedPressureDiscriminant θ q) := by
    rw [hsqrt]
    exact Real.sqrt_pos.2 hdisc
  have hsquare : analyticPositiveSqrt
      (acceptedPressureDiscriminant θ q) ^ 2 =
      acceptedPressureDiscriminant θ q := by
    rw [hsqrt, Real.sq_sqrt hdisc.le]
  have hden : analyticPositiveSqrt
      (acceptedPressureDiscriminant θ q) + 22 ≠ 0 := by linarith
  have hrootden : 8 + analyticPositiveSqrt
      (acceptedPressureDiscriminant θ q) ≠ 0 := by linarith
  unfold acceptedPressureVelocity acceptedPressureRoot
  field_simp [hden, hrootden]
  unfold acceptedPressureDiscriminant acceptedPressureCoefficient at hsquare ⊢
  ring_nf at hsquare ⊢
  nlinarith

/-- Away from `θ = 0`, the continuous kernel is exactly the logarithmic
pressure quotient. -/
theorem acceptedPressurePoissonKernel_eq {θ q : ℝ} (hθ : θ ≠ 0)
    (hdisc : 0 < acceptedPressureDiscriminant θ q) :
    acceptedPressurePoissonKernel θ q =
      -Real.log (acceptedPressureRoot θ q) / θ := by
  have hfactor := one_add_mul_acceptedPressureVelocity hdisc
  have hroot := acceptedPressureRoot_pos hdisc
  by_cases hv : acceptedPressureVelocity θ q = 0
  · have hrinv : (acceptedPressureRoot θ q)⁻¹ = 1 := by
      simpa [hv] using hfactor.symm
    have hr : acceptedPressureRoot θ q = 1 := by
      simpa using congrArg Inv.inv hrinv
    simp [acceptedPressurePoissonKernel, hv, hr]
  · have hinner : 1 + θ * acceptedPressureVelocity θ q ≠ 1 := by
      intro heq
      apply hv
      apply mul_left_cancel₀ hθ
      linarith
    have hdiff : (acceptedPressureRoot θ q)⁻¹ - 1 =
        θ * acceptedPressureVelocity θ q := by linarith
    rw [acceptedPressurePoissonKernel, dslope_of_ne Real.log hinner,
      slope_fun_def_field, hfactor]
    simp only
    rw [Real.log_inv, Real.log_one, hdiff]
    field_simp [hθ, hv]
    ring

/-- Exact factorization of pressure into the scale ratio and the continuous
Poisson kernel. -/
theorem acceptedResponsePressure_eq_ratio_mul_kernel {θ h q : ℝ}
    (hθ : θ ≠ 0) (hh : h ≠ 0)
    (hdisc : 0 < acceptedPressureDiscriminant θ q) :
    acceptedResponsePressure θ h q =
      (θ / h) * acceptedPressurePoissonKernel θ q := by
  rw [acceptedResponsePressure, acceptedPressurePoissonKernel_eq hθ hdisc]
  field_simp [hθ, hh]

/-- **Poisson pressure limit.** If protected time vanishes and the acceptance
probability satisfies `θᵢ / hᵢ → a`, then the exact accepted-response pressure
converges locally uniformly in the source to the Poisson pressure
`(4a/11)(e⁻ᑫ - 1)`. -/
theorem acceptedResponsePressure_poisson_limit
    {κ : Type*} {l : Filter κ} {θ h : κ → ℝ} {a : ℝ}
    (hθ0 : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun i => θ i / h i) l (𝓝 a))
    (hrange : ∀ᶠ i in l, 0 < θ i ∧ θ i ≤ 1 ∧ 0 < h i) :
    TendstoLocallyUniformly
      (fun i q => acceptedResponsePressure (θ i) (h i) q)
      (fun q => (4 * a / 11) * (Real.exp (-q) - 1)) l := by
  have hkernel : TendstoLocallyUniformly
      (fun i q => acceptedPressurePoissonKernel (θ i) q)
      (fun q => (4 / 11 : ℝ) * (Real.exp (-q) - 1)) l := by
    intro u hu q₀
    obtain ⟨t, ht, hevent⟩ :=
      acceptedPressurePoissonKernel_tendstoLocallyUniformly u hu q₀
    exact ⟨t, ht, hθ0.eventually hevent⟩
  have hratioUniform : TendstoUniformly
      (fun i (_q : ℝ) => θ i / h i) (fun _q : ℝ => a) l := by
    intro u hu
    have hevent := hratio.eventually (mem_nhds_left a hu)
    filter_upwards [hevent] with i hi
    intro q
    exact hi
  have hratioLocal := hratioUniform.tendstoLocallyUniformly
  have hproduct := hratioLocal.mul₀ hkernel (by fun_prop) (by fun_prop)
  have hsurrogate : TendstoLocallyUniformly
      (fun i q => (θ i / h i) * acceptedPressurePoissonKernel (θ i) q)
      (fun q => a * ((4 / 11 : ℝ) * (Real.exp (-q) - 1))) l := by
    exact (hproduct.congr (by intro i q; rfl)).congr_right (by intro q; rfl)
  have hpressure := hsurrogate.congr_inseparable (by
    filter_upwards [hrange] with i hi
    intro q
    apply Inseparable.of_eq
    symm
    apply acceptedResponsePressure_eq_ratio_mul_kernel
    · exact ne_of_gt hi.1
    · exact ne_of_gt hi.2.2
    · unfold acceptedPressureDiscriminant acceptedPressureCoefficient
      have hprod : 0 < θ i * Real.exp (-q) :=
        mul_pos hi.1 (Real.exp_pos _)
      nlinarith)
  exact hpressure.congr_right (fun q => by ring)

end NCG
