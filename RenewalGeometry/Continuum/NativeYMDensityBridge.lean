/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeYangMillsMetricVariation
import RenewalGeometry.Continuum.NativeSpinorVariation

/-!
# The Yang–Mills row of the native local action and its first-variation limit along the nodal
  test record (`thm:native-firstvariation-no-band`, Yang–Mills sector)

Einstein–SM action-closure manuscript, `thm:native-firstvariation-no-band` ("the Yang–Mills
identification and variation are `prop:native-YM-identification`").  Unit-torus rendering of the
periodic comparison box (grid `(ℤ/N)⁴`, mesh `h = 1/N`, raw reconstruction `R_h^0 = pc`), as in
`Continuum/NativeGravityFirstJet.lean` and `Continuum/NativeSpinorVariation.lean`.

The Yang–Mills row of the local action `eq:native-densities` is written in two encodings in the
library: `NativeDensity.ymDensity` (inside the full native density `NativeDensity.nativeDensity`,
with the series logarithm `ShiftedPlaquette.logOneAdd` of the gauge plaquette and an abstract
invariant form `D.ipA`) and `NativeYMMetric.ymDens` / `NativeYMMetric.actionYM` (with the Mercator
logarithm `LogBCH.logOnePlus` of the ordered exponential product `curvLog`, the inner product read
through `T : 𝔄 →L[ℝ] E`, and the coefficients `ymCoef e = v(e) g^{μρ} g^{νσ}`), for which the
uniform metric/gauge variation limit `native_YM_metric_variation` is proved.  This file proves
that the two encodings are **the same action** and transfers the variation limit to the nodal
test record `NativeDiracLimit.testRec` of the complete native first variation.

* `logOneAdd_eq_logOnePlus`: the two series logarithms agree on the unit ball.
* `norm_expProd_sub_one_lt`: on the scaled plaquette chart `h Σ|W| ≤ 1/32` the plaquette lies in
  the unit ball around `1`.
* `gaugePlaquette_eq_expProd`, `fieldStrength_eq_curvLog`: the native field strength
  `F^h = h⁻² log(U_μ U_ν U_μ⁻¹ U_ν⁻¹)` of `NativeScaling` is `curvLog`.
* `ymDensity_eq_ymDens`: for an invariant form `⟨X, Y⟩ = ⟪T X, T Y⟫`,
  `NativeDensity.ymDensity = NativeYMMetric.ymDens (ymCoef e) (Fext)` node by node.
* `hasDerivAt_ymAct`: the literal Yang–Mills row `S_{YM,h} = h⁴ Σ_x 𝓛_{YM,h}` of the native
  action has, along any record direction, the derivative `NativeYMMetric.firstVarYM`.
* `ymVar_testRec_eq`: along the nodal test record `𝓘_h v` (symmetric coframe lift of the
  inverse-metric test, sampled gauge test) the Yang–Mills variation is exactly the quantity
  controlled by `native_YM_metric_variation`.
* `native_YM_sector` (**Yang–Mills sector of `eq:native-all-sector-limit`**): under the coframe and
  connection hypotheses `CoHyp` of the Dirac sector and strong `L²` convergence of the literal
  native curvature (`(N2)`), the Yang–Mills first variation along `𝓘_h v` converges to the
  continuum Yang–Mills first variation uniformly on the `C²` unit ball of tests.

Disclosed renderings: the gauge algebra is a finite-dimensional complex normed algebra `𝔸`
(the represented Lie algebra, e.g. matrices; the analytic expansion of the plaquette variation
uses Cauchy estimates over `ℂ`) and the invariant form is `⟨X, Y⟩ = ⟪T X, T Y⟫` for a real-linear
`T : 𝔸 → E` into a real inner-product space (positive semidefinite invariant form).
-/

open MeasureTheory Set Finset Filter Topology NormedSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace RenewalGeometry.NativeYMBridge

open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat omegaLink)
open NativeGravityFirstJet (M4 asM4 coframeM liftM)
open NativeDensity
open NativeYMIdentification (slots curvLog)
open NativeYMMetric (Cof GLc ymCoef ymDens Fext actionYM firstVarYM liftK gMet gInv vol)
open LogBCH (logOnePlus logTerm expProd normSum)
open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The two series logarithms agree -/

section Log

variable {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [NormOneClass 𝔅] [CompleteSpace 𝔅]

/-- **The two series logarithms agree on the unit ball**:
`z · Σ (-1)ⁿ zⁿ/(n+1) = Σ (-1)ⁿ zⁿ⁺¹/(n+1)` for `‖z‖ < 1`. -/
theorem logOneAdd_eq_logOnePlus {z : 𝔅} (hz : ‖z‖ < 1) :
    ShiftedPlaquette.logOneAdd z = logOnePlus z := by
  have hs : Summable (fun n : ℕ => ShiftedPlaquette.logQuotientCoeff n • z ^ n) := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hz) fun n => ?_
    rw [norm_smul]
    have h1 : ‖ShiftedPlaquette.logQuotientCoeff n‖ ≤ 1 := by
      rw [ShiftedPlaquette.norm_logQuotientCoeff]
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    calc ‖ShiftedPlaquette.logQuotientCoeff n‖ * ‖z ^ n‖ ≤ 1 * ‖z‖ ^ n :=
          mul_le_mul h1 (norm_pow_le z n) (norm_nonneg _) zero_le_one
      _ = ‖z‖ ^ n := one_mul _
  unfold ShiftedPlaquette.logOneAdd ShiftedPlaquette.logQuotient
    ShiftedPlaquette.logQuotientSeries logOnePlus
  rw [← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq,
    ← hs.tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [logTerm, ShiftedPlaquette.logQuotientCoeff, mul_smul_comm, pow_succ']

/-- On the chart `Σ‖xᵢ‖ ≤ 1/32` the ordered exponential product lies in the unit ball around `1`. -/
theorem norm_expProd_sub_one_lt (L : List 𝔅) (hs : normSum L ≤ 1 / 32) :
    ‖expProd L - 1‖ < 1 := by
  set s := normSum L
  have hs0 : 0 ≤ s := LogBCH.normSum_nonneg L
  have h1 := LogBCH.norm_expProd_sub_le L
  have h2 := LogBCH.norm_sum_le_normSum L
  have h3 := LogBCH.norm_secondOrder_le L
  have he : Real.exp s ≤ 3 := by
    have : Real.exp s ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    linarith [Real.exp_one_lt_d9]
  have e : expProd L - 1 = (expProd L - (1 + L.sum + LogBCH.secondOrder L)) + L.sum +
      LogBCH.secondOrder L := by abel
  rw [e]
  calc ‖(expProd L - (1 + L.sum + LogBCH.secondOrder L)) + L.sum + LogBCH.secondOrder L‖
      ≤ ‖expProd L - (1 + L.sum + LogBCH.secondOrder L)‖ + ‖L.sum‖ +
          ‖LogBCH.secondOrder L‖ := norm_add₃_le
    _ ≤ s ^ 3 * Real.exp s + s + s ^ 2 / 2 := by gcongr
    _ ≤ s ^ 3 * 3 + s + s ^ 2 / 2 := by gcongr
    _ < 1 := by nlinarith

end Log

/-! ### The native field strength is `curvLog` -/

section FieldStrength

variable {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [NormOneClass 𝔅] [CompleteSpace 𝔅]
variable {N : ℕ} [NeZero N]

/-- The connection array `x ↦ (A_μ(x))_μ` of a family of nodal fields `μ ↦ A_μ`. -/
def arr (A : Fin 4 → Grid N → 𝔅) : Grid N → Fin 4 → 𝔅 := fun x μ => A μ x

/-- The gauge plaquette is the ordered exponential product of the scaled slots. -/
theorem gaugePlaquette_eq_expProd (A : Fin 4 → Grid N → 𝔅) (x : Grid N) (μ ν : Fin 4) :
    NativeScaling.gaugePlaquette (N : ℝ)⁻¹ A x μ ν =
      expProd ((slots (arr A) x μ ν).map fun w => (N : ℝ)⁻¹ • w) := by
  simp only [NativeScaling.gaugePlaquette, expProd, slots, arr, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, smul_neg, mul_assoc, unitVec]

/-- **The native logarithmic field strength is `curvLog`** on the logarithm chart. -/
theorem fieldStrength_eq_curvLog (A : Fin 4 → Grid N → 𝔅) (x : Grid N) (μ ν : Fin 4)
    (hlt : ‖NativeScaling.gaugePlaquette (N : ℝ)⁻¹ A x μ ν - 1‖ < 1) :
    NativeScaling.fieldStrength (N : ℝ)⁻¹ A x μ ν = curvLog N (arr A) x μ ν := by
  unfold NativeScaling.fieldStrength curvLog
  rw [logOneAdd_eq_logOnePlus hlt, gaugePlaquette_eq_expProd, inv_pow, inv_inv]

/-- The scaled slot chart `h Σ|W| ≤ 1/32` puts the plaquette in the logarithm chart. -/
theorem gaugePlaquette_lt_of_chart (A : Fin 4 → Grid N → 𝔅) (x : Grid N) (μ ν : Fin 4)
    (hch : (N : ℝ)⁻¹ * normSum (slots (arr A) x μ ν) ≤ 1 / 32) :
    ‖NativeScaling.gaugePlaquette (N : ℝ)⁻¹ A x μ ν - 1‖ < 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [gaugePlaquette_eq_expProd]
  refine norm_expProd_sub_one_lt _ ?_
  rw [NativeYMIdentification.normSum_map_smul, abs_of_pos (inv_pos.2 hN)]
  exact hch

end FieldStrength

/-! ### The Yang–Mills density in the two encodings -/

section Density

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : Data 𝔄 𝓗 𝓢)
variable {N : ℕ} [NeZero N]

/-- The gauge connection array of a record. -/
def gaugeArr (y : Grid N → Field 𝔄 𝓗 𝓢) : Grid N → Fin 4 → 𝔄 := arr (gauge y)

theorem gMet_eq_metric (e : M4) : gMet e = NativeScaling.metric (show Mat from e) := rfl

theorem vol_eq_volume (e : M4) : vol e = NativeDensity.volume (show Mat from e) := rfl

theorem gInv_eq_ginv (e : M4) (μ ν : Fin 4) : gInv e μ ν = ginv (show Mat from e) μ ν := rfl

theorem liftK_eq_liftM (e k : M4) :
    liftK e k = (liftM (show Mat from e) (show Mat from k) : M4) := by
  funext a μ
  show _ = liftM (show Mat from e) (show Mat from k) a μ
  rw [NativeGravityFirstJet.liftM_apply]
  rfl

/-- **The two encodings of the Yang–Mills density agree**: for the invariant form
`⟨X, Y⟩ = ⟪T X, T Y⟫` and on the logarithm chart,
`𝓛_{YM,h}(y)(x) = -¼ v(e) g^{μρ} g^{νσ} ⟪T F^h_{μν}, T F^h_{ρσ}⟫ = ymDens T (ymCoef e) (Fext)`. -/
theorem ymDensity_eq_ymDens (T : 𝔄 →L[ℝ] E) (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫)
    (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N)
    (hlt : ∀ μ ν, ‖NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge y) x μ ν - 1‖ < 1) :
    ymDensity D (N : ℝ)⁻¹ y x = ymDens T (ymCoef (coframeM y x)) (Fext N (gaugeArr y) x) := by
  have hF : ∀ μ ν, antisym (NativeScaling.fieldStrength (N : ℝ)⁻¹ (gauge y) x) μ ν =
      Fext N (gaugeArr y) x μ ν := by
    intro μ ν
    simp only [antisym, Fext, gaugeArr, fieldStrength_eq_curvLog _ x _ _ (hlt _ _)]
  simp only [ymDensity, ymDens, ymCoef, hF, hip, vol_eq_volume, gInv_eq_ginv,
    NativeGravityFirstJet.coframeM]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  show _ = -(1 / 4) * (NativeDensity.volume (coframe y x) * ginv (coframe y x) μ ρ *
    ginv (coframe y x) ν σ * _)
  ring

end Density


/-! ### The Yang–Mills row and its first variation along record directions -/

section Variation

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : Data 𝔄 𝓗 𝓢)
variable {N : ℕ} [NeZero N]

/-- **The Yang–Mills row** `S_{YM,h}(y) = h⁴ Σ_x 𝓛_{YM,h}(y)(x)` of the native local action. -/
def ymAct (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) : ℝ := h ^ 4 * ∑ x, ymDensity D h y x

/-- The literal Yang–Mills first variation `D S_{YM,h}(y)[v]`, `h = 1/N`, along a record
direction `v`. -/
def ymVar (N : ℕ) [NeZero N] (y v : Grid N → Field 𝔄 𝓗 𝓢) : ℝ :=
  deriv (fun t : ℝ => ymAct D (N : ℝ)⁻¹ (y + t • v)) 0

theorem gaugeArr_add_smul (y v : Grid N → Field 𝔄 𝓗 𝓢) (t : ℝ) :
    gaugeArr (y + t • v) = gaugeArr y + t • gaugeArr v := rfl

theorem continuous_exp_line (a b : 𝔄) (s : ℝ) :
    Continuous fun t : ℝ => exp (s • (a + t • b)) :=
  NativeDiracConvergence.contDiff_exp'.continuous.comp
    (continuous_const.smul (continuous_const.add (continuous_id.smul continuous_const)))

theorem continuous_exp_neg_line (a b : 𝔄) (s : ℝ) :
    Continuous fun t : ℝ => exp (-(s • (a + t • b))) :=
  NativeDiracConvergence.contDiff_exp'.continuous.comp
    (continuous_const.smul (continuous_const.add (continuous_id.smul continuous_const))).neg

theorem continuous_gaugePlaquette_line (y v : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N)
    (μ ν : Fin 4) :
    Continuous fun t : ℝ => NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge (y + t • v)) x μ ν := by
  unfold NativeScaling.gaugePlaquette
  simp only [NativeDirac.gauge_add_smul, Pi.add_apply, Pi.smul_apply]
  exact (((continuous_exp_line _ _ _).mul (continuous_exp_line _ _ _)).mul
    (continuous_exp_neg_line _ _ _)).mul (continuous_exp_neg_line _ _ _)

/-- On the scaled slot chart, the native Yang–Mills row coincides near `t = 0` with
`NativeYMMetric.actionYM` along every record line. -/
theorem eventually_ymAct_eq (T : 𝔄 →L[ℝ] E) (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫)
    (y v : Grid N → Field 𝔄 𝓗 𝓢)
    (hch : ∀ x μ ν, (N : ℝ)⁻¹ * normSum (slots (gaugeArr y) x μ ν) ≤ 1 / 32) :
    (fun t : ℝ => ymAct D (N : ℝ)⁻¹ (y + t • v)) =ᶠ[𝓝 0]
      fun t => actionYM T N (coframeM y + t • coframeM v) (gaugeArr y + t • gaugeArr v) := by
  have hloc : ∀ x μ ν, ∀ᶠ t in 𝓝 (0 : ℝ),
      ‖NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge (y + t • v)) x μ ν - 1‖ < 1 := by
    intro x μ ν
    have hc : Continuous fun t : ℝ =>
        ‖NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge (y + t • v)) x μ ν - 1‖ :=
      ((continuous_gaugePlaquette_line y v x μ ν).sub continuous_const).norm
    have h0 : ‖NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge (y + (0 : ℝ) • v)) x μ ν - 1‖ < 1 := by
      simpa using gaugePlaquette_lt_of_chart (gauge y) x μ ν (hch x μ ν)
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x μ ν,
      ‖NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge (y + t • v)) x μ ν - 1‖ < 1 := by
    simp only [Filter.eventually_all]
    exact hloc
  filter_upwards [hall] with t ht
  unfold ymAct actionYM
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ymDensity_eq_ymDens D T hip (y + t • v) x (ht x)]
  rfl

/-- **The literal Yang–Mills first variation of the native action**: on the nondegenerate coframe
chart and the scaled slot chart, along every record direction `v`,
`d/dt S_{YM,h}(y + t v)|₀ = firstVarYM` (`NativeYMMetric.hasDerivAt_actionYM`). -/
theorem hasDerivAt_ymAct (T : 𝔄 →L[ℝ] E) (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫)
    (y v : Grid N → Field 𝔄 𝓗 𝓢) (hdet : ∀ x, coframeM y x ∈ GLc)
    (hch : ∀ x μ ν, (N : ℝ)⁻¹ * normSum (slots (gaugeArr y) x μ ν) ≤ 1 / 32) :
    HasDerivAt (fun t : ℝ => ymAct D (N : ℝ)⁻¹ (y + t • v))
      (firstVarYM T N (coframeM y) (coframeM v) (gaugeArr y) (gaugeArr v)) 0 := by
  have h1 := NativeYMMetric.hasDerivAt_actionYM T (coframeM y) (coframeM v) (gaugeArr y)
    (gaugeArr v) hdet hch
  rw [firstVarYM, h1.deriv]
  exact h1.congr_of_eventuallyEq (eventually_ymAct_eq D T hip y v hch)

end Variation

/-! ### Gauge tests from `C²` tests and the unit-ball bounds -/

section Tests

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open TorusC2Tests
open NativeYMVariation (C1Test)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- The `C¹` gauge test `(a_ν, ∂_μ a_ν)` underlying a `C²` gauge test `a : 𝕋⁴ → 𝔄⁴`. -/
def toC1 (a : C2Test (Fin 4 → 𝔄)) : C1Test 𝔄 where
  a ν := ⟨fun z => a.f z ν, (continuous_apply ν).comp a.f.continuous⟩
  da μ ν := ⟨fun z => a.df μ z ν, (continuous_apply ν).comp (a.df μ).continuous⟩
  hasDerivAt μ ν z := hasDerivAt_pi.1 (a.hasDerivAt_f μ z) ν

theorem norm_toC1_a_le (a : C2Test (Fin 4 → 𝔄)) (ν : Fin 4) (z : 𝕋) :
    ‖(toC1 a).a ν z‖ ≤ a.norm :=
  (norm_le_pi_norm (a.f z) ν).trans ((a.f.norm_coe_le_norm z).trans a.f_le)

theorem norm_toC1_da_le (a : C2Test (Fin 4 → 𝔄)) (μ ν : Fin 4) (z : 𝕋) :
    ‖(toC1 a).da μ ν z‖ ≤ a.norm :=
  (norm_le_pi_norm (a.df μ z) ν).trans (((a.df μ).norm_coe_le_norm z).trans (a.df_le μ))

theorem norm_toC1_a_sub_le (a : C2Test (Fin 4 → 𝔄)) (ν : Fin 4) (z z' : 𝕋) :
    ‖(toC1 a).a ν z - (toC1 a).a ν z'‖ ≤ a.norm * dist z z' :=
  (norm_le_pi_norm (a.f z - a.f z') ν).trans (NativeSpinorVariation.norm_f_sub_le' a z z')

theorem norm_toC1_da_sub_le (a : C2Test (Fin 4 → 𝔄)) (μ ν : Fin 4) (z z' : 𝕋) :
    ‖(toC1 a).da μ ν z - (toC1 a).da μ ν z'‖ ≤ a.norm * dist z z' := by
  have h1 : ‖a.df μ z - a.df μ z'‖ ≤
      ‖(fun lam => a.df lam z) - fun lam => a.df lam z'‖ :=
    norm_le_pi_norm ((fun lam => a.df lam z) - fun lam => a.df lam z') μ
  exact (norm_le_pi_norm (a.df μ z - a.df μ z') ν).trans
    (h1.trans (NativeSpinorVariation.norm_df_sub_le' a z z'))

/-- A `C²` gauge test of norm at most `M` is a `C^{1,1}`-bounded gauge test. -/
theorem gaugeBound_toC1 (a : C2Test (Fin 4 → 𝔄)) {M : NNReal} (ha : a.norm ≤ M) :
    NativeYMMetric.GaugeBound M (toC1 a) where
  a_le ν z := (norm_toC1_a_le a ν z).trans ha
  a_lip ν := LipschitzWith.of_dist_le_mul fun z z' => (dist_eq_norm _ _).le.trans
    ((norm_toC1_a_sub_le a ν z z').trans (mul_le_mul_of_nonneg_right ha dist_nonneg))
  da_le μ ν z := (norm_toC1_da_le a μ ν z).trans ha
  da_lip μ ν := LipschitzWith.of_dist_le_mul fun z z' => (dist_eq_norm _ _).le.trans
    ((norm_toC1_da_sub_le a μ ν z z').trans (mul_le_mul_of_nonneg_right ha dist_nonneg))

/-- A `C²` inverse-metric test of norm at most `M` is a `C^{0,1}`-bounded metric test. -/
theorem metricBound_of_C2 (k : C2Test M4) {M : NNReal} (hk : k.norm ≤ M) :
    NativeYMMetric.MetricBound M k.f where
  k_le z := ((k.f.norm_coe_le_norm z).trans k.f_le).trans hk
  k_lip := LipschitzWith.of_dist_le_mul fun z z' => (dist_eq_norm _ _).le.trans
    ((NativeSpinorVariation.norm_f_sub_le' k z z').trans
      (mul_le_mul_of_nonneg_right hk dist_nonneg))

end Tests

/-! ### The Yang–Mills sector along the nodal test record -/

section Sector

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open NativeDiracLimit (DTest testRec samp)
open NativeDiracConv (CoHyp)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

theorem coframeM_testRec {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (τ : DTest 𝔄 𝓗 𝓢 W') :
    coframeM (testRec κ N y τ) =
      fun x => liftK (coframeM y x) (τ.k.f (TorusCellEmbedding.samplePt x)) := by
  funext x
  rw [liftK_eq_liftM]
  rfl

theorem gaugeArr_testRec {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (τ : DTest 𝔄 𝓗 𝓢 W') :
    gaugeArr (testRec κ N y τ) = NativeYMVariation.sampleTest N (toC1 τ.a) := rfl

/-- **The Yang–Mills variation along the nodal test record** is the quantity of
`native_YM_metric_variation`: the complete finite first variation of `actionYM` along the
symmetric nodal lift of the inverse-metric test and the sampled gauge test. -/
theorem ymVar_testRec_eq (T : 𝔄 →L[ℝ] E) (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫) {N : ℕ}
    [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W')
    (hdet : ∀ x, coframeM y x ∈ GLc)
    (hch : ∀ x μ ν, (N : ℝ)⁻¹ * normSum (slots (gaugeArr y) x μ ν) ≤ 1 / 32) :
    ymVar D N y (testRec κ N y τ) =
      firstVarYM T N (coframeM y)
        (fun x => liftK (coframeM y x) (τ.k.f (TorusCellEmbedding.samplePt x)))
        (gaugeArr y) (NativeYMVariation.sampleTest N (toC1 τ.a)) := by
  rw [ymVar, (hasDerivAt_ymAct D T hip y (testRec κ N y τ) hdet hch).deriv,
    coframeM_testRec, gaugeArr_testRec]

/-- Strong convergence is inherited by sequences that eventually coincide. -/
theorem lpTendsto_of_eventually_eq {X F : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup F] {p : ℝ≥0∞} {u v : ℕ → X → F} {u' : X → F}
    (hu : LpTendsto ν p u u') (hv : ∀ k, MemLp (v k) p ν) (h : ∀ᶠ k in atTop, u k = v k) :
    LpTendsto ν p v u' :=
  ⟨hv, hu.memLp_lim, hu.tendsto.congr' (h.mono fun k hk => by simp only [hk])⟩

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- **Yang–Mills sector of `eq:native-all-sector-limit`** (`prop:native-YM-identification`
transported to the native local action).  Under the coframe/connection hypotheses `CoHyp`
(compact nondegenerate chart, strong `L²` coframe convergence, strong `L⁴` connection convergence)
and strong `L²` convergence `R_h^0 F_h → F` of the literal native curvature
`F^h = h⁻² log(U_μ U_ν U_μ⁻¹ U_ν⁻¹)` (`(N2)`), the Yang–Mills first variation of the native action
along the nodal test record `𝓘_h v` converges to the continuum Yang–Mills first variation
`∫ -¼ [D_eΘ(e)[ė(k)] ⟨F, F⟩ + Θ(e)(⟨F, d_Aa⟩ + ⟨d_Aa, F⟩)]`, **uniformly on every ball
`‖v‖_{C²} ≤ M`** (in particular on the `C²` unit ball). -/
theorem native_YM_sector (T : 𝔄 →L[ℝ] E) (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫)
    (H : CoHyp n y) {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν)) (M : NNReal) :
    ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧ ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ M →
      |ymVar D (n k) (y k) (testRec κ (n k) (y k) τ) -
        NativeYMMetric.firstVarCont T H.e₀ H.A₀ F τ.k.f (toC1 τ.a)| ≤ β k := by
  have hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => gaugeArr (y k) x μ)) (H.A₀ μ) :=
    H.hA
  obtain ⟨δ, -, hev⟩ := NativeYMMetric.unif_FextV H.hn hA 1
  have hch : ∀ᶠ k in atTop, ∀ x μ ν,
      ((n k : ℝ))⁻¹ * normSum (slots (gaugeArr (y k)) x μ ν) ≤ 1 / 32 :=
    hev.mono fun k hk => hk.1
  have hF' : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => curvLog (n k) (gaugeArr (y k)) x μ ν)) (F μ ν) := by
    intro μ ν
    refine lpTendsto_of_eventually_eq (hF μ ν)
      (fun k => NativeYMIdentification.memLp_pc_gen _ 2) (hch.mono fun k hk => ?_)
    funext z
    simp only [pc]
    exact fieldStrength_eq_curvLog (gauge (y k)) _ μ ν
      (gaugePlaquette_lt_of_chart (gauge (y k)) _ μ ν (hk _ μ ν))
  have hKGL : H.Ke ⊆ GLc := fun M hM => H.hKdet M hM
  obtain ⟨β, hβ, hev2⟩ := NativeYMMetric.native_YM_metric_variation T H.hn hA hF' H.hKe hKGL
    H.he H.hval H.e₀_mem M
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hev2, hch] with k hk hc τ hτ
  rw [ymVar_testRec_eq D κ T hip (y k) τ (fun x => hKGL (H.hval k x)) hc]
  exact hk τ.k.f (toC1 τ.a) (metricBound_of_C2 τ.k (τ.k_le.trans hτ))
    (gaugeBound_toC1 τ.a (τ.a_le.trans hτ))

end Sector

end

end RenewalGeometry.NativeYMBridge
