/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeLocalActionFrechet
import RenewalGeometry.GaugeTheory.NativeActionGaugeInvariance
import RenewalGeometry.Algebra.MatrixExpDerivative

/-!
# The physical link-tangent covector norm of the native action
  (`eq:link-tangent-mass`, `thm:finite-Wilson-zero-defect (F5)`,
  `prop:equivariant-native-budgets`, Einstein–SM action closure)

The complete covector of the finite local action in the physical link tangent
`α_μ = h⁻¹ U̇_μ U_μ⁻¹` is `NativeGauge.linkCov` (the derivative of the link-level action along
the curves `U_t = e^{thα} U`).  The manuscript measures it in "the positive physical link/matter
mass metric" `eq:link-tangent-mass`,
`‖V‖²_{0,h,link} = h⁴ Σ_x (|ė|² + |α|² + |η_H|² + |η_Ψ|² + |η_Ψ̄|²)` "with the fixed positive
coefficient metrics", and `σ_h^{link}` (`σ_h^{phys}` in `(F5)`) is the dual norm.

* `MassMetric`: the fixed positive coefficient metrics `|α|² = g_m(α, α)`, `|η|² = h_m(η, η)`
  (coercive continuous bilinear forms); `massSqP` (`eq:link-tangent-mass`); `covNormP`, the dual
  norm `sup {|DS[τ]| : ‖τ‖_{link} ≤ 1}`.
* `linkCov_eq_fderiv` (**log-to-link-tangent chain rule**): on the chart (nondegenerate coframes,
  Cartan and gauge plaquettes in the logarithm chart, `‖hA‖ < 1/32`) the covector at a link
  tangent `τ` is the Fréchet derivative of `S_h^{loc}` applied to the logarithmic-coordinate
  variation `logTan τ`, whose gauge component is `𝒥(h ad_A)⁻¹ α`
  (`lem:native-log-gauge-differential`); conversely (`tanOf`, `logTan_tanOf`) every logarithmic
  variation `v` is realized by the link tangent `α = 𝒥(h ad_A) a`, so
  `nativeVar_eq_linkCov`: `D S_h^{loc}(y)[v] = DS^{link}[tanOf v]`.
* `abs_linkCov_le` (**Cauchy–Schwarz for the dual norm**): on the chart the covector is bounded,
  so `|DS^{link}[τ]| ≤ σ_h^{link} ‖τ‖_{link}` for every tangent.
* `covNormP_gauge`, `covNormP_record_gauge`: `σ_h^{link}` is exactly invariant under finite site
  gauges when the fixed metrics are invariant (`Ad` and `ρ_H`).
* `massSqP_tanOf_le`, `nodalL2Sq_logTan_le` (**uniform equivalence of the logarithmic-coordinate
  and physical link-tangent norms on the scaled chart**, `‖𝒥(h ad_A)‖ ≤ 2`,
  `‖𝒥(h ad_A)⁻¹‖ ≤ 4`), and `abs_deriv_localAction_le` (the stationarity budget
  `|D S_h^{loc}(y)[v]| ≤ σ_h^{link} √K ‖v‖_{0,h}`).
-/

open NormedSpace Finset Filter Topology
open scoped ContDiff

namespace RenewalGeometry.NativeLinkCov

open ShiftedJetAction (Grid unitVec)
open NativeScaling (Mat)
open NativeDensity NativeGauge MatrixExpDerivative OperatorHalfCoth SeriesLogChart

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [Nontrivial 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable {n : ℕ} [NeZero n]

/-! ### Tangents as nodal records -/

/-- A link tangent read as a nodal record `(ė, α, η, ψ, ψ̄)`. -/
def toV (τ : Tangent n 𝔄 𝓗 𝓢) : Grid n → Field 𝔄 𝓗 𝓢 :=
  fun x => (τ.ε x, fun μ => τ.α μ x, τ.η x, τ.ψ x, τ.ψb x)

/-- A nodal record read as a link tangent. -/
def ofV (w : Grid n → Field 𝔄 𝓗 𝓢) : Tangent n 𝔄 𝓗 𝓢 :=
  ⟨coframe w, fun μ x => NativeDensity.gauge w μ x, higgs w, psi w, psiBar w⟩

theorem toV_ofV (w : Grid n → Field 𝔄 𝓗 𝓢) : toV (ofV w) = w := by
  funext x; rfl

/-- The Jacobian `𝒥(h ad_{A_μ(x)})` of the scaled exponential chart. -/
def jac (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (μ : Fin 4) (x : Grid n) : 𝔄 →L[ℝ] 𝔄 :=
  dexpJ (adOp (h • NativeDensity.gauge y μ x))

/-- The pointwise inverse Jacobian acting on the gauge components of a nodal record. -/
def jinvL (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) :
    (Grid n → Field 𝔄 𝓗 𝓢) →L[ℝ] (Grid n → Field 𝔄 𝓗 𝓢) :=
  ContinuousLinearMap.pi fun x =>
    ((ContinuousLinearMap.id ℝ Mat).prodMap
      ((ContinuousLinearMap.pi fun μ =>
          (Ring.inverse (jac h y μ x)).comp (ContinuousLinearMap.proj μ)).prodMap
        (ContinuousLinearMap.id ℝ (𝓗 × 𝓢 × CoSpinor 𝓢)))).comp
      (ContinuousLinearMap.proj x)

@[simp] theorem jinvL_apply (h : ℝ) (y w : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    jinvL h y w x = ((w x).1, fun μ => Ring.inverse (jac h y μ x) ((w x).2.1 μ), (w x).2.2) :=
  rfl

/-- **The logarithmic-coordinate variation of a link tangent**: gauge component
`𝒥(h ad_A)⁻¹ α`, the other components unchanged. -/
def logTan (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (τ : Tangent n 𝔄 𝓗 𝓢) : Grid n → Field 𝔄 𝓗 𝓢 :=
  jinvL h y (toV τ)

/-- **The link tangent of a logarithmic variation**: `α = 𝒥(h ad_A) a`. -/
def tanOf (h : ℝ) (y v : Grid n → Field 𝔄 𝓗 𝓢) : Tangent n 𝔄 𝓗 𝓢 :=
  ⟨coframe v, fun μ x => jac h y μ x (NativeDensity.gauge v μ x), higgs v, psi v, psiBar v⟩

theorem isUnit_jac {h : ℝ} {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32) (μ : Fin 4) (x : Grid n) :
    IsUnit (jac h y μ x) :=
  isUnit_dexpJ_adOp_of_norm_le _ ((hs μ x).le.trans (by norm_num))

theorem logTan_tanOf {h : ℝ} {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32) (v : Grid n → Field 𝔄 𝓗 𝓢) :
    logTan h y (tanOf h y v) = v := by
  funext x
  simp only [logTan, jinvL_apply]
  have e : (fun μ => Ring.inverse (jac h y μ x) ((toV (tanOf h y v) x).2.1 μ)) = (v x).2.1 := by
    funext μ
    change (Ring.inverse (jac h y μ x) * jac h y μ x) (NativeDensity.gauge v μ x) = _
    rw [Ring.inverse_mul_cancel _ (isUnit_jac hs μ x)]
    rfl
  rw [e]
  rfl

/-! ### The record curve realizing a link tangent -/

/-- The record curve whose links are `e^{thα} e^{hA}`:
`A_t = h⁻¹ Log(e^{thα} e^{hA})`, the other components affine. -/
def recCurve (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (τ : Tangent n 𝔄 𝓗 𝓢) (t : ℝ) :
    Grid n → Field 𝔄 𝓗 𝓢 := fun x =>
  (coframe y x + t • τ.ε x,
    fun μ => h⁻¹ • logChart (exp ((t * h) • τ.α μ x) * exp (h • NativeDensity.gauge y μ x)),
    higgs y x + t • τ.η x, psi y x + t • τ.ψ x, psiBar y x + t • τ.ψb x)

theorem recCurve_zero {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32) (τ : Tangent n 𝔄 𝓗 𝓢) :
    recCurve h y τ 0 = y := by
  funext x
  have e : (fun μ => h⁻¹ • logChart (exp (((0 : ℝ) * h) • τ.α μ x) *
      exp (h • NativeDensity.gauge y μ x))) = (y x).2.1 := by
    funext μ
    rw [zero_mul, zero_smul, exp_zero, one_mul, logChart_exp (hs μ x).le, smul_smul,
      inv_mul_cancel₀ hh, one_smul]
    rfl
  refine Prod.ext ?_ (Prod.ext e (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · change coframe y x + (0 : ℝ) • τ.ε x = _
    rw [zero_smul, add_zero]; rfl
  · change higgs y x + (0 : ℝ) • τ.η x = _
    rw [zero_smul, add_zero]; rfl
  · change psi y x + (0 : ℝ) • τ.ψ x = _
    rw [zero_smul, add_zero]; rfl
  · change psiBar y x + (0 : ℝ) • τ.ψb x = _
    have : (0 : ℝ) • τ.ψb x = 0 := by ext v; simp
    rw [this, add_zero]; rfl

theorem hasDerivAt_affine {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a b : V) :
    HasDerivAt (fun t : ℝ => a + t • b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a

theorem hasDerivAt_recCurve {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32) (τ : Tangent n 𝔄 𝓗 𝓢) :
    HasDerivAt (recCurve h y τ) (logTan h y τ) 0 := by
  refine hasDerivAt_pi.2 fun x => ?_
  have hg : ∀ μ, HasDerivAt (fun t : ℝ =>
      h⁻¹ • logChart (exp ((t * h) • τ.α μ x) * exp (h • NativeDensity.gauge y μ x)))
      (Ring.inverse (jac h y μ x) (τ.α μ x)) 0 := by
    intro μ
    set X := h • NativeDensity.gauge y μ x
    have hγ : HasDerivAt (fun t : ℝ => exp ((t * h) • τ.α μ x) * exp X)
        ((h • τ.α μ x) * exp X) 0 := by
      have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (h • τ.α μ x) 0
      simp only [zero_smul, exp_zero, one_mul] at h1
      have h2 := h1.mul_const (exp X)
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      simp only [mul_smul]
    have hL := hasDerivAt_log_comp X (isUnit_jac hs μ x)
      (eventually_logChart_exp (hs μ x)) hγ (by simp)
    have := hL.const_smul h⁻¹
    refine this.congr_deriv ?_
    rw [mul_assoc, MatrixExpDerivative.exp_mul_exp_neg, mul_one, map_smul, smul_smul, inv_mul_cancel₀ hh, one_smul]
    rfl
  have hA : HasDerivAt (fun t : ℝ => fun μ =>
      h⁻¹ • logChart (exp ((t * h) • τ.α μ x) * exp (h • NativeDensity.gauge y μ x)))
      (fun μ => Ring.inverse (jac h y μ x) (τ.α μ x)) 0 := hasDerivAt_pi.2 hg
  have H := (hasDerivAt_affine (coframe y x) (τ.ε x)).prodMk (hA.prodMk
    ((hasDerivAt_affine (higgs y x) (τ.η x)).prodMk ((hasDerivAt_affine (psi y x) (τ.ψ x)).prodMk
      (hasDerivAt_affine (psiBar y x) (τ.ψb x)))))
  exact H

theorem norm_exp_sub_one_lt {X : 𝔄} (hX : ‖X‖ < 1 / 32) : ‖exp X - 1‖ < 1 :=
  (norm_exp_sub_one_le (by linarith)).trans_lt (by linarith)

/-- Near `t = 0` the links of the record curve are those of the link curve. -/
theorem eventually_toLinks_recCurve {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32) (τ : Tangent n 𝔄 𝓗 𝓢) :
    ∀ᶠ t in 𝓝 (0 : ℝ), toLinks h (recCurve h y τ t) = curve h (toLinks h y) τ t := by
  have hev : ∀ μ x, ∀ᶠ t in 𝓝 (0 : ℝ),
      ‖exp ((t * h) • τ.α μ x) * exp (h • NativeDensity.gauge y μ x) - 1‖ < 1 := by
    intro μ x
    have hc : Continuous fun t : ℝ =>
        ‖exp ((t * h) • τ.α μ x) * exp (h • NativeDensity.gauge y μ x) - 1‖ := by
      have := continuous_exp' (𝔸 := 𝔄)
      fun_prop
    have h0 : ‖exp (((0 : ℝ) * h) • τ.α μ x) * exp (h • NativeDensity.gauge y μ x) - 1‖ < 1 := by
      simp only [zero_mul, zero_smul, exp_zero, one_mul]
      exact norm_exp_sub_one_lt (hs μ x)
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ μ x,
      ‖exp ((t * h) • τ.α μ x) * exp (h • NativeDensity.gauge y μ x) - 1‖ < 1 := by
    simp only [Filter.eventually_all]
    exact hev
  filter_upwards [hall] with t ht
  ext1
  · rfl
  · funext μ x
    change exp (h • (h⁻¹ • logChart (exp ((t * h) • τ.α μ x) *
      exp (h • NativeDensity.gauge y μ x)))) = _
    rw [smul_smul, mul_inv_cancel₀ hh, one_smul, exp_logChart (ht μ x)]
    rfl
  · rfl
  · rfl
  · rfl

variable (C : CovData 𝔄 𝓗 𝓢)

/-- **The log-to-link-tangent chain rule**: on the chart, the covector at the link tangent `τ`
is the Fréchet derivative of the native local action at the logarithmic variation `logTan τ`. -/
theorem linkCov_eq_fderiv {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32)
    (hd : DifferentiableAt ℝ (localAction C.toData h) y) (τ : Tangent n 𝔄 𝓗 𝓢) :
    linkCov C h (toLinks h y) τ = fderiv ℝ (localAction C.toData h) y (logTan h y τ) := by
  have hcomp : HasDerivAt (fun t => localAction C.toData h (recCurve h y τ t))
      (fderiv ℝ (localAction C.toData h) y (logTan h y τ)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_recCurve hh hs τ)
      (recCurve_zero hh hs τ).symm
  unfold linkCov
  rw [← hcomp.deriv]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_toLinks_recCurve hh hs τ] with t ht
  rw [localAction_eq_linkAction, ht]

/-- **The logarithmic first variation is the link covector at the realizing tangent**:
`D S_h^{loc}(y)[v] = DS^{link}[tanOf v]`, `α = 𝒥(h ad_A) a` (`lem:native-log-gauge-differential`). -/
theorem nativeVar_eq_linkCov {N : ℕ} [NeZero N] {y : Grid N → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖(N : ℝ)⁻¹ • NativeDensity.gauge y μ x‖ < 1 / 32)
    (hd : DifferentiableAt ℝ (localAction C.toData (N : ℝ)⁻¹) y) (v : Grid N → Field 𝔄 𝓗 𝓢) :
    deriv (fun s : ℝ => localAction C.toData (N : ℝ)⁻¹ (y + s • v)) 0 =
      linkCov C (N : ℝ)⁻¹ (toLinks (N : ℝ)⁻¹ y) (tanOf (N : ℝ)⁻¹ y v) := by
  have hN : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N))
  rw [linkCov_eq_fderiv C hN hs hd, logTan_tanOf hs]
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    exact hasDerivAt_affine y v
  have h0 : y = y + (0 : ℝ) • v := by
    funext x
    exact Prod.ext (by simp) (Prod.ext (by funext μ; simp) (Prod.ext (by simp)
      (Prod.ext (by simp) (by ext w; simp))))
  exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0).deriv

/-! ### The positive physical mass metric and the dual covector norm -/

/-- **The fixed positive coefficient metrics** of `eq:link-tangent-mass`: a coercive form `g_m`
on the gauge algebra (`|α|²`) and a coercive form `h_m` on the Higgs space (`|η_H|²`). -/
structure MassMetric (𝔄 𝓗 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [NormedAddCommGroup 𝓗]
    [NormedSpace ℝ 𝓗] where
  gm : 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ
  hm : 𝓗 →L[ℝ] 𝓗 →L[ℝ] ℝ
  c : ℝ
  c_pos : 0 < c
  gm_coer : ∀ X, c * ‖X‖ ^ 2 ≤ gm X X
  hm_coer : ∀ v, c * ‖v‖ ^ 2 ≤ hm v v

variable (M : MassMetric 𝔄 𝓗)

/-- The mass metric on nodal records. -/
def massQ (h : ℝ) (w : Grid n → Field 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, (‖(w x).1‖ ^ 2 + ∑ μ, M.gm ((w x).2.1 μ) ((w x).2.1 μ) +
    M.hm (w x).2.2.1 (w x).2.2.1 + ‖(w x).2.2.2.1‖ ^ 2 + ‖(w x).2.2.2.2‖ ^ 2)

/-- **The positive physical link/matter mass metric** `eq:link-tangent-mass`:
`‖τ‖²_{0,h,link} = h⁴ Σ_x (|ė|² + Σ_μ |α_μ|² + |η_H|² + |ψ|² + |ψ̄|²)`. -/
def massSqP (h : ℝ) (τ : Tangent n 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, (‖τ.ε x‖ ^ 2 + ∑ μ, M.gm (τ.α μ x) (τ.α μ x) + M.hm (τ.η x) (τ.η x) +
    ‖τ.ψ x‖ ^ 2 + ‖τ.ψb x‖ ^ 2)

theorem massSqP_eq (h : ℝ) (τ : Tangent n 𝔄 𝓗 𝓢) : massSqP M h τ = massQ M h (toV τ) := rfl

/-- **`σ_h^{link}`**: the dual norm of the complete action covector in the positive physical
link/matter mass metric. -/
def covNormP (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) : ℝ :=
  sSup ((fun τ => |linkCov C h c τ|) '' {τ | massSqP M h τ ≤ 1})

theorem massQ_smul (h s : ℝ) (w : Grid n → Field 𝔄 𝓗 𝓢) :
    massQ M h (s • w) = s ^ 2 * massQ M h w := by
  unfold massQ
  have e : ∀ x, (‖((s • w) x).1‖ ^ 2 + ∑ μ, M.gm (((s • w) x).2.1 μ) (((s • w) x).2.1 μ) +
      M.hm ((s • w) x).2.2.1 ((s • w) x).2.2.1 + ‖((s • w) x).2.2.2.1‖ ^ 2 +
      ‖((s • w) x).2.2.2.2‖ ^ 2) = s ^ 2 * (‖(w x).1‖ ^ 2 +
      ∑ μ, M.gm ((w x).2.1 μ) ((w x).2.1 μ) + M.hm (w x).2.2.1 (w x).2.2.1 +
      ‖(w x).2.2.2.1‖ ^ 2 + ‖(w x).2.2.2.2‖ ^ 2) := by
    intro x
    change ‖s • (w x).1‖ ^ 2 + ∑ μ, M.gm (s • (w x).2.1 μ) (s • (w x).2.1 μ) +
        M.hm (s • (w x).2.2.1) (s • (w x).2.2.1) + ‖s • (w x).2.2.2.1‖ ^ 2 +
        ‖s • (w x).2.2.2.2‖ ^ 2 = _
    simp only [norm_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_pow,
      Real.norm_eq_abs, sq_abs]
    have hsum : ∑ μ, s * (s * M.gm ((w x).2.1 μ) ((w x).2.1 μ)) =
        s ^ 2 * ∑ μ, M.gm ((w x).2.1 μ) ((w x).2.1 μ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun μ _ => by ring
    rw [hsum]
    ring
  rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.mul_sum]
  ring

theorem sq_max_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : max a b ^ 2 ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

theorem norm_pi_sq_le {V : Type*} [NormedAddCommGroup V] (b : Fin 4 → V) :
    ‖b‖ ^ 2 ≤ ∑ μ, ‖b μ‖ ^ 2 := by
  have hS : 0 ≤ ∑ μ, ‖b μ‖ ^ 2 := by positivity
  have h1 : ‖b‖ ≤ Real.sqrt (∑ μ, ‖b μ‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun μ => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun μ => ‖b μ‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ μ)
  calc ‖b‖ ^ 2 ≤ Real.sqrt (∑ μ, ‖b μ‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := Real.sq_sqrt hS

/-- The norm of a nodal field value is controlled by its components. -/
theorem norm_field_sq_le (p : Field 𝔄 𝓗 𝓢) :
    ‖p‖ ^ 2 ≤ ‖p.1‖ ^ 2 + ∑ μ, ‖p.2.1 μ‖ ^ 2 + ‖p.2.2.1‖ ^ 2 + ‖p.2.2.2.1‖ ^ 2 +
      ‖p.2.2.2.2‖ ^ 2 := by
  have e1 := sq_max_le _ _ (norm_nonneg p.1) (norm_nonneg p.2)
  have e2 := sq_max_le _ _ (norm_nonneg p.2.1) (norm_nonneg p.2.2)
  have e3 := sq_max_le _ _ (norm_nonneg p.2.2.1) (norm_nonneg p.2.2.2)
  have e4 := sq_max_le _ _ (norm_nonneg p.2.2.2.1) (norm_nonneg p.2.2.2.2)
  have e5 := norm_pi_sq_le p.2.1
  rw [← Prod.norm_def] at e1 e2 e3 e4
  linarith

theorem massQ_nonneg {h : ℝ} (w : Grid n → Field 𝔄 𝓗 𝓢) : 0 ≤ massQ M h w := by
  unfold massQ
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => ?_)
  have h1 : ∀ μ, 0 ≤ M.gm ((w x).2.1 μ) ((w x).2.1 μ) := fun μ =>
    (mul_nonneg M.c_pos.le (by positivity)).trans (M.gm_coer _)
  have h2 : 0 ≤ M.hm (w x).2.2.1 (w x).2.2.1 :=
    (mul_nonneg M.c_pos.le (by positivity)).trans (M.hm_coer _)
  have h3 := Finset.sum_nonneg fun μ (_ : μ ∈ Finset.univ) => h1 μ
  positivity

/-- **Coercivity of the mass metric**: `h⁴ min(1, c) ‖w‖² ≤ ‖w‖²_{link}`. -/
theorem massQ_coer {h : ℝ} (w : Grid n → Field 𝔄 𝓗 𝓢) :
    h ^ 4 * min 1 M.c * ‖w‖ ^ 2 ≤ massQ M h w := by
  set c₁ := min 1 M.c
  have hc₁ : 0 < c₁ := lt_min one_pos M.c_pos
  set S : Grid n → ℝ := fun x => ‖(w x).1‖ ^ 2 + ∑ μ, M.gm ((w x).2.1 μ) ((w x).2.1 μ) +
    M.hm (w x).2.2.1 (w x).2.2.1 + ‖(w x).2.2.2.1‖ ^ 2 + ‖(w x).2.2.2.2‖ ^ 2 with hS
  have hpt : ∀ x, c₁ * ‖w x‖ ^ 2 ≤ S x := by
    intro x
    have hf := norm_field_sq_le (w x)
    have hg : ∀ μ, c₁ * ‖(w x).2.1 μ‖ ^ 2 ≤ M.gm ((w x).2.1 μ) ((w x).2.1 μ) := fun μ =>
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans (M.gm_coer _)
    have hh' : c₁ * ‖(w x).2.2.1‖ ^ 2 ≤ M.hm (w x).2.2.1 (w x).2.2.1 :=
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans (M.hm_coer _)
    have hsum : c₁ * ∑ μ, ‖(w x).2.1 μ‖ ^ 2 ≤ ∑ μ, M.gm ((w x).2.1 μ) ((w x).2.1 μ) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun μ _ => hg μ
    have h1 : c₁ ≤ 1 := min_le_left _ _
    have a1 : c₁ * ‖(w x).1‖ ^ 2 ≤ ‖(w x).1‖ ^ 2 :=
      mul_le_of_le_one_left (by positivity) h1
    have a4 : c₁ * ‖(w x).2.2.2.1‖ ^ 2 ≤ ‖(w x).2.2.2.1‖ ^ 2 :=
      mul_le_of_le_one_left (by positivity) h1
    have a5 : c₁ * ‖(w x).2.2.2.2‖ ^ 2 ≤ ‖(w x).2.2.2.2‖ ^ 2 :=
      mul_le_of_le_one_left (by positivity) h1
    have := mul_le_mul_of_nonneg_left hf hc₁.le
    simp only [hS]
    nlinarith
  have hS0 : ∀ x, 0 ≤ S x := fun x => (by positivity : (0 : ℝ) ≤ c₁ * ‖w x‖ ^ 2).trans (hpt x)
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_max_image Finset.univ (fun x => ‖w x‖) Finset.univ_nonempty
  have hw : ‖w‖ = ‖w x₀‖ := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun x =>
      hx₀ x (Finset.mem_univ x)) (norm_le_pi_norm w x₀)
  have hsum : S x₀ ≤ ∑ x, S x :=
    Finset.single_le_sum (f := S) (fun x _ => hS0 x) (Finset.mem_univ x₀)
  unfold massQ
  rw [hw]
  calc h ^ 4 * c₁ * ‖w x₀‖ ^ 2 = h ^ 4 * (c₁ * ‖w x₀‖ ^ 2) := by ring
    _ ≤ h ^ 4 * ∑ x, S x :=
        mul_le_mul_of_nonneg_left ((hpt x₀).trans hsum) (by positivity)

/-- The link covector is linear in the realized record of the tangent. -/
theorem linkCov_ofV {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32)
    (hd : DifferentiableAt ℝ (localAction C.toData h) y) (w : Grid n → Field 𝔄 𝓗 𝓢) :
    linkCov C h (toLinks h y) (ofV w) =
      ((fderiv ℝ (localAction C.toData h) y).comp (jinvL h y)) w := by
  rw [linkCov_eq_fderiv C hh hs hd, logTan, toV_ofV]
  rfl

theorem linkCov_eq_toV {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32)
    (hd : DifferentiableAt ℝ (localAction C.toData h) y) (τ : Tangent n 𝔄 𝓗 𝓢) :
    linkCov C h (toLinks h y) τ =
      ((fderiv ℝ (localAction C.toData h) y).comp (jinvL h y)) (toV τ) := by
  rw [linkCov_eq_fderiv C hh hs hd, logTan]
  rfl

/-- The covector is bounded on the unit ball of the mass metric. -/
theorem abs_linkCov_le_K {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32)
    (hd : DifferentiableAt ℝ (localAction C.toData h) y) :
    ∃ K, 0 ≤ K ∧ ∀ τ : Tangent n 𝔄 𝓗 𝓢,
      |linkCov C h (toLinks h y) τ| ≤ K * Real.sqrt (massSqP M h τ) := by
  set L := (fderiv ℝ (localAction C.toData h) y).comp (jinvL h y)
  set c₁ := min 1 M.c
  have hc₁ : 0 < c₁ := lt_min one_pos M.c_pos
  have hh4 : 0 < h ^ 4 := by positivity
  obtain ⟨KL, hKL, hLb⟩ := L.bound
  refine ⟨KL / Real.sqrt (h ^ 4 * c₁), by positivity, fun τ => ?_⟩
  rw [linkCov_eq_toV C hh hs hd, massSqP_eq, ← Real.norm_eq_abs]
  have h1 := hLb (toV τ)
  have h2 : Real.sqrt (h ^ 4 * c₁) * ‖toV τ‖ ≤ Real.sqrt (massQ M h (toV τ)) := by
    rw [← Real.sqrt_sq (norm_nonneg (toV τ)), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have := massQ_coer M (h := h) (toV τ)
    linarith
  have hsq : 0 < Real.sqrt (h ^ 4 * c₁) := Real.sqrt_pos.2 (by positivity)
  calc ‖L (toV τ)‖ ≤ KL * ‖toV τ‖ := h1
    _ = KL / Real.sqrt (h ^ 4 * c₁) * (Real.sqrt (h ^ 4 * c₁) * ‖toV τ‖) := by
        field_simp
    _ ≤ KL / Real.sqrt (h ^ 4 * c₁) * Real.sqrt (massQ M h (toV τ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Cauchy–Schwarz for the dual norm**: on the chart, `|DS^{link}[τ]| ≤ σ_h^{link} ‖τ‖_{link}`
for every physical tangent `τ` (the covector is bounded, so its dual norm is finite). -/
theorem abs_linkCov_le {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32)
    (hd : DifferentiableAt ℝ (localAction C.toData h) y) (τ : Tangent n 𝔄 𝓗 𝓢) :
    |linkCov C h (toLinks h y) τ| ≤
      covNormP C M h (toLinks h y) * Real.sqrt (massSqP M h τ) := by
  obtain ⟨K, hK0, hK⟩ := abs_linkCov_le_K C M hh hs hd
  have hbdd : BddAbove ((fun τ => |linkCov C h (toLinks h y) τ|) ''
      {τ | massSqP M h τ ≤ 1}) := by
    refine ⟨K, ?_⟩
    rintro _ ⟨τ', hτ', rfl⟩
    refine (hK τ').trans ?_
    have : Real.sqrt (massSqP M h τ') ≤ 1 := Real.sqrt_le_one.mpr hτ'
    nlinarith
  have hm0 : 0 ≤ massSqP M h τ := by rw [massSqP_eq]; exact massQ_nonneg M _
  rcases hm0.eq_or_lt with hm | hm
  · have h1 := hK τ
    rw [← hm, Real.sqrt_zero, mul_zero] at h1 ⊢
    exact h1
  · have hsq : 0 < Real.sqrt (massSqP M h τ) := Real.sqrt_pos.2 hm
    have hτ' : massSqP M h (ofV ((Real.sqrt (massSqP M h τ))⁻¹ • toV τ)) ≤ 1 := by
      rw [massSqP_eq, toV_ofV, massQ_smul, ← massSqP_eq, inv_pow, Real.sq_sqrt hm.le,
        inv_mul_cancel₀ hm.ne']
    have hle : |linkCov C h (toLinks h y) (ofV ((Real.sqrt (massSqP M h τ))⁻¹ • toV τ))| ≤
        covNormP C M h (toLinks h y) :=
      le_csSup hbdd ⟨_, hτ', rfl⟩
    have e : linkCov C h (toLinks h y) (ofV ((Real.sqrt (massSqP M h τ))⁻¹ • toV τ)) =
        (Real.sqrt (massSqP M h τ))⁻¹ * linkCov C h (toLinks h y) τ := by
      rw [linkCov_ofV C hh hs hd, map_smul, smul_eq_mul, ← linkCov_eq_toV C hh hs hd]
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hsq), inv_mul_le_iff₀ hsq] at hle
    linarith [hle]

/-! ### Exact site-gauge invariance of `σ_h^{link}` -/

/-- Invariance of the fixed metrics under the gauge group. -/
structure MassMetric.Invariant (C : CovData 𝔄 𝓗 𝓢) (M : MassMetric 𝔄 𝓗) : Prop where
  gm_conj : ∀ g ∈ C.G, ∀ X : 𝔄, M.gm ((g : 𝔄) * X * ↑g⁻¹) ((g : 𝔄) * X * ↑g⁻¹) = M.gm X X
  hm_inv : ∀ g ∈ C.G, ∀ v : 𝓗, M.hm (C.ρH g v) (C.ρH g v) = M.hm v v

theorem massSqP_tangentAct (hM : M.Invariant C) {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G)
    (h : ℝ) (τ : Tangent n 𝔄 𝓗 𝓢) : massSqP M h (tangentAct C g τ) = massSqP M h τ := by
  simp only [massSqP, tangentAct]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hM.hm_inv _ (hg x), C.ρS_isom _ (hg x), norm_comp_ρS_inv C (hg x)]
  simp only [hM.gm_conj _ (hg x)]

/-- **`σ_h^{link}` is exactly invariant under finite site gauges** (on the plaquette chart). -/
theorem covNormP_gauge (hM : M.Invariant C) {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    {c : LinkConfig n 𝔄 𝓗 𝓢} (hu : ∀ μ x, IsUnit (c.U μ x)) (hc : Chart c) :
    covNormP C M h (gaugeAct C g c) = covNormP C M h c := by
  have hset : (fun τ => |linkCov C h (gaugeAct C g c) τ|) '' {τ | massSqP M h τ ≤ 1} =
      (fun τ => |linkCov C h c τ|) '' {τ | massSqP M h τ ≤ 1} := by
    ext r
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨τ', hτ', rfl⟩
      refine ⟨tangentAct C (fun x => (g x)⁻¹) τ', ?_, ?_⟩
      · rwa [← massSqP_tangentAct C M hM hg h, tangentAct_inv]
      · rw [← linkCov_gauge C hg h hu hc, tangentAct_inv]
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨tangentAct C g τ, by rwa [massSqP_tangentAct C M hM hg h], by
        rw [linkCov_gauge C hg h hu hc τ]⟩
  unfold covNormP
  rw [hset]

/-- **`σ_h^{link}` of native records is gauge invariant.** -/
theorem covNormP_record_gauge (hM : M.Invariant C) {h : ℝ} {g : Grid n → 𝔄ˣ}
    {y y' : Grid n → Field 𝔄 𝓗 𝓢} (hy : IsGaugeTransform C h g y y')
    (hc : Chart (toLinks h y)) :
    covNormP C M h (toLinks h y') = covNormP C M h (toLinks h y) := by
  rw [hy.2]
  exact covNormP_gauge C M hM hy.1 h (isUnit_toLinks h y) hc

/-! ### Uniform equivalence of logarithmic and link-tangent norms, and the stationarity budget -/

/-- The logarithmic-coordinate nodal mass norm `‖v‖²_{0,h} = h⁴ Σ_x |v(x)|²` (`eq:prefix-mass`),
with the component norms. -/
def nodalL2Sq (h : ℝ) (v : Grid n → Field 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, (‖(v x).1‖ ^ 2 + ∑ μ, ‖(v x).2.1 μ‖ ^ 2 + ‖(v x).2.2.1‖ ^ 2 +
    ‖(v x).2.2.2.1‖ ^ 2 + ‖(v x).2.2.2.2‖ ^ 2)

theorem nodalL2Sq_nonneg (h : ℝ) (v : Grid n → Field 𝔄 𝓗 𝓢) : 0 ≤ nodalL2Sq h v := by
  unfold nodalL2Sq; positivity

/-- On the scaled logarithm chart the Jacobian `𝒥(h ad_A)` has norm at most `2`. -/
theorem norm_jac_le {h : ℝ} {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32) (μ : Fin 4) (x : Grid n) :
    ‖jac h y μ x‖ ≤ 2 := by
  have h1 : ‖adOp (h • NativeDensity.gauge y μ x)‖ ≤ 1 / 16 :=
    (norm_adOp_le _).trans (by linarith [hs μ x])
  have h2 := norm_dexpJ_sub_one_le _ (h1.trans (by norm_num))
  have h3 : ‖(1 : 𝔄 →L[ℝ] 𝔄)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc ‖jac h y μ x‖ = ‖(jac h y μ x - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖jac h y μ x - 1‖ + ‖(1 : 𝔄 →L[ℝ] 𝔄)‖ := norm_add_le _ _
    _ ≤ 3 * (1 / 16) + 1 := by unfold jac; linarith
    _ ≤ 2 := by norm_num

/-- On the scaled logarithm chart the inverse Jacobian `𝒥(h ad_A)⁻¹` has norm at most `4`. -/
theorem norm_jac_inv_le {h : ℝ} {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32) (μ : Fin 4) (x : Grid n) :
    ‖Ring.inverse (jac h y μ x)‖ ≤ 4 :=
  (dexpJ_isUnit_and_norm_inverse_le _ ((norm_adOp_le _).trans (by linarith [hs μ x]))).2

theorem gm_le (X : 𝔄) : M.gm X X ≤ ‖M.gm‖ * ‖X‖ ^ 2 := by
  calc M.gm X X ≤ ‖M.gm X X‖ := le_abs_self _
    _ ≤ ‖M.gm‖ * ‖X‖ * ‖X‖ := M.gm.le_opNorm₂ X X
    _ = ‖M.gm‖ * ‖X‖ ^ 2 := by ring

theorem hm_le (v : 𝓗) : M.hm v v ≤ ‖M.hm‖ * ‖v‖ ^ 2 := by
  calc M.hm v v ≤ ‖M.hm v v‖ := le_abs_self _
    _ ≤ ‖M.hm‖ * ‖v‖ * ‖v‖ := M.hm.le_opNorm₂ v v
    _ = ‖M.hm‖ * ‖v‖ ^ 2 := by ring

/-- **Logarithmic ⟹ link-tangent norm** (uniform on the scaled chart): the link tangent
`α = 𝒥(h ad_A) a` of a logarithmic variation has `‖tanOf v‖²_{link} ≤ K ‖v‖²_{0,h}`,
`K = 1 + 4‖g_m‖ + ‖h_m‖`. -/
theorem massSqP_tanOf_le {h : ℝ} {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32) (v : Grid n → Field 𝔄 𝓗 𝓢) :
    massSqP M h (tanOf h y v) ≤ (1 + 4 * ‖M.gm‖ + ‖M.hm‖) * nodalL2Sq h v := by
  have key : ∀ x, ‖(tanOf h y v).ε x‖ ^ 2 +
      ∑ μ, M.gm ((tanOf h y v).α μ x) ((tanOf h y v).α μ x) +
      M.hm ((tanOf h y v).η x) ((tanOf h y v).η x) + ‖(tanOf h y v).ψ x‖ ^ 2 +
      ‖(tanOf h y v).ψb x‖ ^ 2 ≤ (1 + 4 * ‖M.gm‖ + ‖M.hm‖) * (‖(v x).1‖ ^ 2 +
      ∑ μ, ‖(v x).2.1 μ‖ ^ 2 + ‖(v x).2.2.1‖ ^ 2 + ‖(v x).2.2.2.1‖ ^ 2 +
      ‖(v x).2.2.2.2‖ ^ 2) := fun x => by
    have hg0 := ContinuousLinearMap.opNorm_nonneg M.gm
    have hh0 := ContinuousLinearMap.opNorm_nonneg M.hm
    have hα : ∀ μ, M.gm ((tanOf h y v).α μ x) ((tanOf h y v).α μ x) ≤
        4 * ‖M.gm‖ * ‖(v x).2.1 μ‖ ^ 2 := by
      intro μ
      refine (gm_le M _).trans ?_
      have h1 : ‖(tanOf h y v).α μ x‖ ≤ 2 * ‖(v x).2.1 μ‖ :=
        ((jac h y μ x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (norm_jac_le hs μ x) (norm_nonneg _))
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith
    have hsum : ∑ μ, M.gm ((tanOf h y v).α μ x) ((tanOf h y v).α μ x) ≤
        4 * ‖M.gm‖ * ∑ μ, ‖(v x).2.1 μ‖ ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun μ _ => hα μ
    have hη := hm_le M ((tanOf h y v).η x)
    change ‖(v x).1‖ ^ 2 + ∑ μ, M.gm ((tanOf h y v).α μ x) ((tanOf h y v).α μ x) +
        M.hm (v x).2.2.1 (v x).2.2.1 + ‖(v x).2.2.2.1‖ ^ 2 + ‖(v x).2.2.2.2‖ ^ 2 ≤ _
    have hpos1 : 0 ≤ ∑ μ, ‖(v x).2.1 μ‖ ^ 2 := by positivity
    have hp2 := sq_nonneg ‖(v x).1‖
    have hp3 := sq_nonneg ‖(v x).2.2.1‖
    have hp4 := sq_nonneg ‖(v x).2.2.2.1‖
    have hp5 := sq_nonneg ‖(v x).2.2.2.2‖
    change M.hm (v x).2.2.1 (v x).2.2.1 ≤ ‖M.hm‖ * ‖(v x).2.2.1‖ ^ 2 at hη
    nlinarith
  unfold massSqP nodalL2Sq
  calc h ^ 4 * ∑ x, _ ≤ h ^ 4 * ∑ x, (1 + 4 * ‖M.gm‖ + ‖M.hm‖) * (‖(v x).1‖ ^ 2 +
        ∑ μ, ‖(v x).2.1 μ‖ ^ 2 + ‖(v x).2.2.1‖ ^ 2 + ‖(v x).2.2.2.1‖ ^ 2 +
        ‖(v x).2.2.2.2‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => key x) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- **Link-tangent ⟹ logarithmic norm** (uniform on the scaled chart):
`min(1, c) ‖logTan τ‖²_{0,h} ≤ 16 ‖τ‖²_{link}`. -/
theorem nodalL2Sq_logTan_le {h : ℝ} {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖h • NativeDensity.gauge y μ x‖ < 1 / 32) (τ : Tangent n 𝔄 𝓗 𝓢) :
    min 1 M.c * nodalL2Sq h (logTan h y τ) ≤ 16 * massSqP M h τ := by
  set c₁ := min 1 M.c
  have hc₁ : 0 < c₁ := lt_min one_pos M.c_pos
  have h1 : c₁ ≤ 1 := min_le_left _ _
  have h2 : c₁ ≤ M.c := min_le_right _ _
  have key : ∀ x, c₁ * (‖τ.ε x‖ ^ 2 + ∑ μ, ‖Ring.inverse (jac h y μ x) (τ.α μ x)‖ ^ 2 +
      ‖τ.η x‖ ^ 2 + ‖τ.ψ x‖ ^ 2 + ‖τ.ψb x‖ ^ 2) ≤ 16 * (‖τ.ε x‖ ^ 2 +
      ∑ μ, M.gm (τ.α μ x) (τ.α μ x) + M.hm (τ.η x) (τ.η x) + ‖τ.ψ x‖ ^ 2 +
      ‖τ.ψb x‖ ^ 2) := fun x => by
    have hα : ∀ μ, c₁ * ‖Ring.inverse (jac h y μ x) (τ.α μ x)‖ ^ 2 ≤
        16 * M.gm (τ.α μ x) (τ.α μ x) := by
      intro μ
      have k1 : ‖Ring.inverse (jac h y μ x) (τ.α μ x)‖ ≤ 4 * ‖τ.α μ x‖ :=
        ((Ring.inverse (jac h y μ x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (norm_jac_inv_le hs μ x) (norm_nonneg _))
      have k2 := pow_le_pow_left₀ (norm_nonneg _) k1 2
      have k3 := M.gm_coer (τ.α μ x)
      have k4 : c₁ * ‖τ.α μ x‖ ^ 2 ≤ M.c * ‖τ.α μ x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      nlinarith
    have hsum : c₁ * ∑ μ, ‖Ring.inverse (jac h y μ x) (τ.α μ x)‖ ^ 2 ≤
        16 * ∑ μ, M.gm (τ.α μ x) (τ.α μ x) := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_le_sum fun μ _ => hα μ
    have hη : c₁ * ‖τ.η x‖ ^ 2 ≤ M.hm (τ.η x) (τ.η x) :=
      (mul_le_mul_of_nonneg_right h2 (by positivity)).trans (M.hm_coer _)
    have hhm0 : 0 ≤ M.hm (τ.η x) (τ.η x) := (by positivity : (0 : ℝ) ≤ c₁ * ‖τ.η x‖ ^ 2).trans hη
    have a1 : c₁ * ‖τ.ε x‖ ^ 2 ≤ ‖τ.ε x‖ ^ 2 := mul_le_of_le_one_left (by positivity) h1
    have a4 : c₁ * ‖τ.ψ x‖ ^ 2 ≤ ‖τ.ψ x‖ ^ 2 := mul_le_of_le_one_left (by positivity) h1
    have a5 : c₁ * ‖τ.ψb x‖ ^ 2 ≤ ‖τ.ψb x‖ ^ 2 := mul_le_of_le_one_left (by positivity) h1
    have p1 := sq_nonneg ‖τ.ε x‖
    have p4 := sq_nonneg ‖τ.ψ x‖
    have p5 := sq_nonneg ‖τ.ψb x‖
    nlinarith
  unfold nodalL2Sq massSqP
  calc c₁ * (h ^ 4 * ∑ x, _) = h ^ 4 * ∑ x, c₁ * (‖τ.ε x‖ ^ 2 +
        ∑ μ, ‖Ring.inverse (jac h y μ x) (τ.α μ x)‖ ^ 2 + ‖τ.η x‖ ^ 2 + ‖τ.ψ x‖ ^ 2 +
        ‖τ.ψb x‖ ^ 2) := by rw [mul_left_comm, Finset.mul_sum]; rfl
    _ ≤ h ^ 4 * ∑ x, 16 * (‖τ.ε x‖ ^ 2 + ∑ μ, M.gm (τ.α μ x) (τ.α μ x) +
        M.hm (τ.η x) (τ.η x) + ‖τ.ψ x‖ ^ 2 + ‖τ.ψb x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => key x) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- **The stationarity budget** (`eq:eq-native-stationarity`, Cauchy–Schwarz form): on the scaled
logarithm chart, for every logarithmic-coordinate nodal test `v`,
`|D S_h^{loc}(y)[v]| ≤ σ_h^{link}(y) · √K · ‖v‖_{0,h}`, `K = 1 + 4‖g_m‖ + ‖h_m‖`. -/
theorem abs_deriv_localAction_le {N : ℕ} [NeZero N] {y : Grid N → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖(N : ℝ)⁻¹ • NativeDensity.gauge y μ x‖ < 1 / 32)
    (hd : DifferentiableAt ℝ (localAction C.toData (N : ℝ)⁻¹) y) (v : Grid N → Field 𝔄 𝓗 𝓢) :
    |deriv (fun s : ℝ => localAction C.toData (N : ℝ)⁻¹ (y + s • v)) 0| ≤
      covNormP C M (N : ℝ)⁻¹ (toLinks (N : ℝ)⁻¹ y) *
        (Real.sqrt (1 + 4 * ‖M.gm‖ + ‖M.hm‖) * Real.sqrt (nodalL2Sq (N : ℝ)⁻¹ v)) := by
  have hN : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N))
  rw [nativeVar_eq_linkCov C hs hd v]
  have hc0 : 0 ≤ covNormP C M (N : ℝ)⁻¹ (toLinks (N : ℝ)⁻¹ y) :=
    Real.sSup_nonneg fun _ ⟨_, _, hr⟩ => hr ▸ abs_nonneg _
  refine (abs_linkCov_le C M hN hs hd _).trans (mul_le_mul_of_nonneg_left ?_ hc0)
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (massSqP_tanOf_le M hs v)

end

/-! ### Non-vacuity of the mass metric -/

/-- The Hilbert-space metric of `ℂ` (real part of the Hermitian product) is a positive physical
mass metric for the `U(1)` packet (`𝔄 = 𝓗 = ℂ`): `MassMetric` is inhabited. -/
noncomputable def complexMassMetric : MassMetric ℂ ℂ where
  gm := (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  hm := (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  c := 1
  c_pos := one_pos
  gm_coer X := by
    rw [one_mul]
    exact le_of_eq (real_inner_self_eq_norm_sq X).symm
  hm_coer v := by
    rw [one_mul]
    exact le_of_eq (real_inner_self_eq_norm_sq v).symm

/-- Non-vacuity of `MassMetric.Invariant`: the Hilbert metric of `ℂ` is invariant for the `U(1)`
packet `NativeGauge.u1CovData`. -/
theorem complexMassMetric_invariant : complexMassMetric.Invariant NativeGauge.u1CovData :=
  ⟨fun g _ X => by rw [NativeGauge.conj_units_complex],
    fun g hg v => NativeGauge.u1CovData.hermH_inv g hg v v⟩

end RenewalGeometry.NativeLinkCov
