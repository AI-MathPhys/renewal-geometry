/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeGravityJetDensity
import RenewalGeometry.Continuum.TorusC2TestSampling
import RenewalGeometry.Analysis.HomogeneousJetVariationLimit

/-!
# Literal gravitational consistency from strong first jets (`prop:native-gravity-firstjet`)

Einstein–SM action-closure manuscript, Appendix `app:native-critical-closure`, subsection
"The literal gravitational row at first-jet regularity".

## Setting (disclosed renderings)

Unit-torus rendering of the paper's periodic comparison box (as in
`Continuum/TorusTrigReconstruction.lean`, `prop:native-Higgs-compactness`): the grid `(ℤ/N)⁴`,
mesh `h = 1/N`, the dilation `x ↦ 2πx` maps it onto the paper's box of side `2π`.  The actual nodal
records `y_N : (ℤ/N)⁴ → Field` are those of the native local action
(`NativeDensity.localAction`, `eq:native-local-action`), and `S_{g,h}^{loc}(y) = h⁴ Σ_x 𝓛_{g,h}(y)(x)`
(`gravAction`) is the **literal gravitational row** of `eq:native-densities`, with the Cartan
plaquette logarithm `R^h_{μν}` of `L_μ = exp(h Ω_μ(e, δ⁺_h e))`.  The coframe is real `4×4`
(`e^a_μ`, row `a`), the frame is trivialised (one fixed chart).  Inverse-metric tests are
`C²` fields `k : 𝕋⁴ → ℝ^{4×4}` (`TorusC2Tests.C2Test`), lifted nodally by the symmetric lift
`eq:metric-lift` `ė^a_μ = -½ e^a_α g_{μβ} k^{αβ}` (`liftM`, `liftM_apply`) at the sampled values
`k(x/N)` (`liftRecord`); the first variation `D S_{g,h}^{loc}(e_h)[𝓘_h k]` is the derivative of the
literal action along this lifted record (`gravVariation`).

## The continuum functional

`D𝒮_{g,θ}(e)[k]` is the first variation of the first-order Palatini action
`∫ L^{(1)}(e, ∂e)`, `L^{(1)} = palatiniFirstOrder` (`eq:palatini-first-order`, the integrated-by-
parts representative `-dB ∧ ω + B ∧ ω ∧ ω - (Λ/κ)v` of `app:palatini`, identified explicitly in
`NativeGravityJet.palatiniFirstOrder_eq`), along the lifted variation
`(ė, ∂ė) = (lift(e, k), lift(e, ∂k) + D_e lift(e, k)[∂e])` (`contGravVariation`).  This is the
paper's definition of the gravitational first-variation distribution at `H¹ ∩ L^∞` coframes with
`L^∞` inverse.

## Main results

* `hasDerivAt_gravAction`: on the oriented logarithm chart the literal gravitational first
  variation is the jet sum `h⁴ Σ_x (D_w F_g(h, Ξ_h e(x))[Ξ_h ė(x)] - (Λ/κ) Dv(e(x))[ė(x)])` of the
  coframe first-jet density (`lem:native-firstjet-normal-form` composed with the chain rule).
* `hasDerivAt_palatiniAction` / `contGravVariation_eq_deriv`: the continuum functional is the
  derivative, along the lifted test, of the first-order Palatini action `∫ L^{(1)}(e, p)`
  (differentiation under the integral, dominated by `C(1 + |p|)²`, using the degree-two scaling);
  `limitCov_apply`: its integrand is the limit covector `limitCov(e, p)` on the limit test jet.
* `lpTendsto_gridCov` (analytic core): the grid variation covectors converge strongly in `L¹(𝕋⁴)`
  to `limitCov(e, p)` — `HomogeneousJetVariation.lpTendsto_homogeneous_variation` applied to the
  coframe jet density with its exact scaling (`NativeGravityJet.gravCurv_scale`) on the compact
  normalised chart (`NativeGravityJet.isCompact_gravChart`, membership `normJet_mem_gravChart`).
* `firstJet_eq_weakDeriv`: the limit `p_μ` of `R^0 D⁺_μ e_h` is entrywise the weak derivative
  `∂_μ e` (`lem:native-reconstruction-identification`).
* `native_gravity_firstjet` (**`prop:native-gravity-firstjet`, eq:native-gravity-firstvariation**):
  if `R^0 e_h → e`, `R^0 D⁺_μ e_h → p_μ` strongly in `L²`, the nodal coframes stay in a compact
  oriented chart `K_e ⊂ {det > 0}` and the common logarithm-chart condition
  `h |ω_{μ,h}| ≤ c_*` holds (`c_* ≤ 1/64`, matrix sup norm), then for every `ε > 0`, eventually
  `|D S_{g,h}^{loc}(e_h)[𝓘_h k] - D𝒮_{g,θ}(e, p)[k]| ≤ ε ‖k‖_{C²}` **for all tests `k`
  simultaneously** — hence `sup_{‖k‖_{C^r} ≤ 1} |…| → 0` for every `r ≥ 2`.
* `native_gravity_firstjet_reconstructed` (second clause): the same consistency relative to any
  continuum reconstructions `f_h` staying in the chart and converging with their first jets strongly
  in `L²` (strong `H¹`) to `(e, ∂e)` (`lpTendsto_limitCov`: continuity of the continuum variation
  in the reduced first-jet topology).
* Non-vacuity: the flat records (identity coframe) satisfy all hypotheses (`example`).
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus NormedSpace
open scoped BigOperators Real ENNReal ContDiff

namespace RenewalGeometry.NativeGravityFirstJet

open ShiftedJetAction (Grid unitVec fwdDiff stencil)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity NativeGravityJet TorusC2Tests HomogeneousJetVariation

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-! ### The symmetric metric lift -/

/-- The symmetric coframe lift `ė = -½ e k g` of an inverse-metric test `k` (`eq:metric-lift`). -/
def liftM (e k : Mat) : Mat := -(1 / 2 : ℝ) • (e * k * metric e)

/-- `eq:metric-lift` in components: `ė^a_μ = -½ e^a_α g_{μβ} k^{αβ}`. -/
theorem metric_transpose (e : Mat) : (metric e).transpose = metric e := by
  simp only [metric, Matrix.transpose_mul, Matrix.transpose_transpose, NativeScaling.eta,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

theorem liftM_apply (e k : Mat) (a μ : Fin 4) :
    liftM e k a μ = -(1 / 2) * ∑ α, ∑ β, e a α * metric e μ β * k α β := by
  have hg : ∀ β, metric e β μ = metric e μ β := fun β => by
    rw [← Matrix.transpose_apply (metric e) μ β, metric_transpose]
  rw [liftM, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [hg]; ring

/-- The divided difference of the lift in the coframe: `lift(e₀ + hq, k) - lift(e₀, k)
= h · dqLift(e₀, e₀ + hq, q, k)`. -/
def dqLift (e₀ e₁ q k : Mat) : Mat :=
  -(1 / 2 : ℝ) • (q * k * metric e₁ + e₀ * k * (q.transpose * NativeScaling.eta * e₁ +
    e₀.transpose * NativeScaling.eta * q))

theorem liftM_add_smul_sub (e₀ q k : Mat) (h : ℝ) :
    liftM (e₀ + h • q) k - liftM e₀ k = h • dqLift e₀ (e₀ + h • q) q k := by
  unfold liftM dqLift metric
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  module

theorem liftM_add (e k k' : Mat) : liftM e (k + k') = liftM e k + liftM e k' := by
  unfold liftM; rw [Matrix.mul_add, Matrix.add_mul, smul_add]

theorem liftM_smul (e k : Mat) (c : ℝ) : liftM e (c • k) = c • liftM e k := by
  unfold liftM; rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

theorem dqLift_add_left (e₀ e₁ q q' k : Mat) :
    dqLift e₀ e₁ (q + q') k = dqLift e₀ e₁ q k + dqLift e₀ e₁ q' k := by
  unfold dqLift
  simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  module

theorem dqLift_smul_left (e₀ e₁ q k : Mat) (c : ℝ) :
    dqLift e₀ e₁ (c • q) k = c • dqLift e₀ e₁ q k := by
  unfold dqLift
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add,
    Matrix.add_mul, smul_add]
  module

theorem dqLift_add_right (e₀ e₁ q k k' : Mat) :
    dqLift e₀ e₁ q (k + k') = dqLift e₀ e₁ q k + dqLift e₀ e₁ q k' := by
  unfold dqLift
  simp only [Matrix.add_mul, Matrix.mul_add]
  module

theorem dqLift_smul_right (e₀ e₁ q k : Mat) (c : ℝ) :
    dqLift e₀ e₁ q (c • k) = c • dqLift e₀ e₁ q k := by
  unfold dqLift
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  module

/-! ### Canonical normed carriers

Normed and topological statements are made on the canonical sup-norm spaces of real arrays
`M4 = Fin 4 → Fin 4 → ℝ` (entrywise sup norm, definitionally the matrices `Mat`), so that all
continuous-linear-map types carry the canonical product structures. -/

/-- Real `4 × 4` arrays with the entrywise sup norm. -/
abbrev M4 := Fin 4 → Fin 4 → ℝ

/-- Shifted values over the nine shifts. -/
abbrev V4 := Shift → M4

/-- Normalised first differences at the shifted nodes. -/
abbrev Q4 := Shift × Fin 4 → M4

/-- Coframe (or test) first jets. -/
abbrev T4 := V4 × Q4

/-- The lift as a continuous linear map of the test value. -/
def liftL (e : M4) : M4 →L[ℝ] M4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun k => liftM e k, map_add' := liftM_add e, map_smul' := fun c k => liftM_smul e k c }

@[simp] theorem liftL_apply (e k : M4) : liftL e k = liftM e k := rfl

/-- The divided difference of the lift as a continuous bilinear map. -/
def dqLiftL (e₀ e₁ : M4) : M4 →L[ℝ] M4 →L[ℝ] M4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => LinearMap.toContinuousLinearMap
        { toFun := fun k => dqLift e₀ e₁ q k, map_add' := dqLift_add_right e₀ e₁ q,
          map_smul' := fun c k => dqLift_smul_right e₀ e₁ q k c }
      map_add' := fun q q' => ContinuousLinearMap.ext fun k => dqLift_add_left e₀ e₁ q q' k
      map_smul' := fun c q => ContinuousLinearMap.ext fun k => dqLift_smul_left e₀ e₁ q k c }

@[simp] theorem dqLiftL_apply (e₀ e₁ q k : M4) : dqLiftL e₀ e₁ q k = dqLift e₀ e₁ q k := rfl

theorem continuous_liftL : Continuous liftL :=
  continuous_clm_apply.2 fun k => by
    show Continuous fun e : M4 => liftM e k
    unfold liftM metric; fun_prop

theorem continuous_dqLiftL_apply (q : M4) : Continuous fun p : M4 × M4 => dqLiftL p.1 p.2 q :=
  continuous_clm_apply.2 fun k => by
    show Continuous fun p : M4 × M4 => dqLift p.1 p.2 q k
    unfold dqLift metric; fun_prop

/-- The value block of the lifted test jet: `τ ↦ (lift(v_s, τ_s))_s`. -/
def Lmap (v : V4) : T4 →L[ℝ] V4 :=
  ContinuousLinearMap.pi fun s => (liftL (v s)).comp
    ((ContinuousLinearMap.proj s).comp (ContinuousLinearMap.fst ℝ V4 Q4))

@[simp] theorem Lmap_apply (v : V4) (τ : T4) (s : Shift) : Lmap v τ s = liftM (v s) (τ.1 s) := rfl

/-- The difference block of the lifted test jet acting on the test differences:
`τ ↦ (lift(w_{s,λ}, τ_{s,λ}))_{s,λ}` with `w_{s,λ} = e(x + s + e_λ)`. -/
def Bmap (w : Q4) : T4 →L[ℝ] Q4 :=
  ContinuousLinearMap.pi fun sl => (liftL (w sl)).comp
    ((ContinuousLinearMap.proj sl).comp (ContinuousLinearMap.snd ℝ V4 Q4))

@[simp] theorem Bmap_apply (w : Q4) (τ : T4) (sl : Shift × Fin 4) :
    Bmap w τ sl = liftM (w sl) (τ.2 sl) := rfl

/-- The coframe-difference part of the lifted test differences:
`q ↦ τ ↦ (dqLift(v_s, w_{s,λ}, q_{s,λ}, τ_s))_{s,λ}`. -/
def Amap (v : V4) (w : Q4) : Q4 →L[ℝ] T4 →L[ℝ] Q4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => ContinuousLinearMap.pi fun sl => (dqLiftL (v sl.1) (w sl) (q sl)).comp
        ((ContinuousLinearMap.proj sl.1).comp (ContinuousLinearMap.fst ℝ V4 Q4))
      map_add' := fun q q' => ContinuousLinearMap.ext fun τ => funext fun sl => by
        show dqLift (v sl.1) (w sl) (q sl + q' sl) (τ.1 sl.1) =
          dqLift (v sl.1) (w sl) (q sl) (τ.1 sl.1) + dqLift (v sl.1) (w sl) (q' sl) (τ.1 sl.1)
        exact dqLift_add_left _ _ _ _ _
      map_smul' := fun c q => ContinuousLinearMap.ext fun τ => funext fun sl => by
        show dqLift (v sl.1) (w sl) (c • q sl) (τ.1 sl.1) =
          c • dqLift (v sl.1) (w sl) (q sl) (τ.1 sl.1)
        exact dqLift_smul_left _ _ _ _ _ }

@[simp] theorem Amap_apply (v : V4) (w q : Q4) (τ : T4) (sl : Shift × Fin 4) :
    Amap v w q τ sl = dqLift (v sl.1) (w sl) (q sl) (τ.1 sl.1) := rfl

theorem continuous_dqLiftL : Continuous fun p : M4 × M4 => dqLiftL p.1 p.2 :=
  continuous_clm_apply.2 fun q => continuous_dqLiftL_apply q

theorem continuous_Lmap : Continuous Lmap :=
  continuous_clm_apply.2 fun τ => continuous_pi fun s => by
    show Continuous fun v : V4 => liftM (v s) (τ.1 s)
    unfold liftM metric; fun_prop

theorem continuous_Bmap : Continuous Bmap :=
  continuous_clm_apply.2 fun τ => continuous_pi fun sl => by
    show Continuous fun w : Q4 => liftM (w sl) (τ.2 sl)
    unfold liftM metric; fun_prop

theorem continuous_Amap_apply (q : Q4) : Continuous fun p : V4 × Q4 => Amap p.1 p.2 q :=
  continuous_clm_apply.2 fun τ => continuous_pi fun sl => by
    show Continuous fun p : V4 × Q4 => dqLift (p.1 sl.1) (p.2 sl) (q sl) (τ.1 sl.1)
    unfold dqLift metric; fun_prop

theorem continuous_Amap : Continuous fun p : V4 × Q4 => Amap p.1 p.2 :=
  continuous_clm_apply.2 fun q => continuous_Amap_apply q

/-! ### Coframe stencils and the lifted test jet -/

section Stencil

variable {n : ℕ} [NeZero n]

/-- Shifted coframe values `e(x + s)`. -/
def valsArr (e : Grid n → M4) (x : Grid n) : V4 := fun s => e (x + shiftVec n s)

/-- Normalised first differences `δ⁺_λ e(x + s)`. -/
def diffsArr (h : ℝ) (e : Grid n → M4) (x : Grid n) : Q4 :=
  fun sl => fwdDiff h sl.2 e (x + shiftVec n sl.1)

/-- Doubly shifted coframe values `e(x + s + e_λ)`. -/
def nextArr (e : Grid n → M4) (x : Grid n) : Q4 :=
  fun sl => e (x + shiftVec n sl.1 + unitVec n sl.2)

theorem stencil_eq (h : ℝ) (e : Grid n → M4) (x : Grid n) :
    stencil h (shiftVec n) x e = (valsArr e x, diffsArr h e x) := by
  rw [ShiftedJetAction.stencil_apply]; rfl

/-- The lifted coframe variation `ė(z) = lift(e(z), k(z))`. -/
def liftArr (e kN : Grid n → M4) : Grid n → M4 := fun z => liftM (e z) (kN z)

theorem smul_fwdDiff' {h : ℝ} (hh : h ≠ 0) (μ : Fin 4) (f : Grid n → Mat) (z : Grid n) :
    f (z + unitVec n μ) = f z + h • fwdDiff h μ f z := by
  unfold ShiftedJetAction.fwdDiff
  rw [smul_smul, mul_inv_cancel₀ hh, one_smul, add_sub_cancel]

/-- The difference of a lifted field (matrix form): `δ⁺_λ lift(e, k)(z) = lift(e(z+e_λ), δ⁺_λ k(z))
+ dqLift(e(z), e(z+e_λ), δ⁺_λ e(z), k(z))`. -/
theorem fwdDiff_lift {h : ℝ} (hh : h ≠ 0) (e kN : Grid n → Mat) (lam : Fin 4) (z : Grid n) :
    fwdDiff h lam (fun z => liftM (e z) (kN z)) z =
      liftM (e (z + unitVec n lam)) (fwdDiff h lam kN z) +
        dqLift (e z) (e (z + unitVec n lam)) (fwdDiff h lam e z) (kN z) := by
  have h1 : kN (z + unitVec n lam) = kN z + h • fwdDiff h lam kN z := smul_fwdDiff' hh lam kN z
  have h2 : liftM (e (z + unitVec n lam)) (kN z) - liftM (e z) (kN z) =
      h • dqLift (e z) (e (z + unitVec n lam)) (fwdDiff h lam e z) (kN z) := by
    rw [smul_fwdDiff' hh lam e z]
    exact liftM_add_smul_sub _ _ _ _
  have key : liftM (e (z + unitVec n lam)) (kN (z + unitVec n lam)) - liftM (e z) (kN z) =
      h • (liftM (e (z + unitVec n lam)) (fwdDiff h lam kN z) +
        dqLift (e z) (e (z + unitVec n lam)) (fwdDiff h lam e z) (kN z)) := by
    rw [h1, liftM_add, liftM_smul, smul_add, ← h2]
    abel
  show h⁻¹ • (liftM (e (z + unitVec n lam)) (kN (z + unitVec n lam)) - liftM (e z) (kN z)) = _
  rw [key, smul_smul, inv_mul_cancel₀ hh, one_smul]

/-- **The stencil of the lifted variation** is the image of the test jet under the coefficient
maps: values `L(v)τ`, differences `(B(w) + A(v, w)(q))τ`. -/
theorem stencil_lift {h : ℝ} (hh : h ≠ 0) (e kN : Grid n → M4) (x : Grid n) :
    stencil h (shiftVec n) x (liftArr e kN) =
      (Lmap (valsArr e x) (stencil h (shiftVec n) x kN),
        (Bmap (nextArr e x) + Amap (valsArr e x) (nextArr e x) (diffsArr h e x))
          (stencil h (shiftVec n) x kN)) := by
  rw [ShiftedJetAction.stencil_apply, ShiftedJetAction.stencil_apply]
  refine Prod.ext (funext fun s => rfl) (funext fun sl => ?_)
  show fwdDiff h sl.2 (liftArr e kN) (x + shiftVec n sl.1) =
    liftM (e (x + shiftVec n sl.1 + unitVec n sl.2)) (fwdDiff h sl.2 kN (x + shiftVec n sl.1)) +
      dqLift (e (x + shiftVec n sl.1)) (e (x + shiftVec n sl.1 + unitVec n sl.2))
        (fwdDiff h sl.2 e (x + shiftVec n sl.1)) (kN (x + shiftVec n sl.1))
  exact fwdDiff_lift hh (n := n) (fun z => (e z : Mat)) (fun z => (kN z : Mat)) sl.2 _

end Stencil

/-! ### The literal gravitational action and its first variation on the grid -/

/-- The gravitational curvature density on the canonical carriers. -/
def Γg (κ : ℝ) (z : ℝ × T4) : ℝ := gravCurv κ z

/-- The volume density on the canonical carrier. -/
def volM (M : M4) : ℝ := volume M

theorem Γg_scale (κ : ℝ) : ∀ ρ K (v : V4) (q : Q4), 0 < K →
    Γg κ (ρ, (v, q)) = K ^ 2 * Γg κ (ρ * K, (v, K⁻¹ • q)) :=
  fun ρ K v q hK => gravCurv_scale κ ρ K hK.ne' v q

theorem contDiffAt_Γg (κ : ℝ) {z : ℝ × T4} (hz : GravRegular z) : ContDiffAt ℝ ∞ (Γg κ) z :=
  contDiffAt_gravCurv κ hz

theorem contDiffAt_volM {M : M4} (hM : Matrix.det (show Mat from M) ≠ 0) :
    ContDiffAt ℝ ∞ volM M :=
  contDiffAt_volume hM

section Action

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable {n : ℕ} [NeZero n]

/-- The coframe of a record, on the canonical carrier. -/
def coframeM (y : Grid n → Field 𝔄 𝓗 𝓢) : Grid n → M4 := fun x => coframe y x

/-- **The literal gravitational row** `S_{g,h}^{loc}(y) = h⁴ Σ_x 𝓛_{g,h}(y)(x)` of the local action
`eq:native-local-action`. -/
def gravAction (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) : ℝ := h ^ 4 * ∑ x, gravityDensity D h y x

section LocalNorm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sum_gravityDensity_eq' {h : ℝ} (hh : h ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    ∑ x, gravityDensity D h y x =
      ∑ x, (Γg D.κ (h, stencil h (shiftVec n) x (coframeM y)) -
        D.Λ / D.κ * volM (coframeM y x)) := by
  rw [sum_gravityDensity_eq D hh y hdet hlog]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [stencil_eq, ShiftedJetAction.stencil_apply]
  rfl

theorem coframe_add_smul (y yd : Grid n → Field 𝔄 𝓗 𝓢) (t : ℝ) :
    coframeM (y + t • yd) = coframeM y + t • coframeM yd := by
  funext x; rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- **The literal gravitational first variation as a coframe jet sum.**  On the oriented
logarithm chart, with every base stencil a regular point of the jet density,
`d/dt S_{g,h}^{loc}(y + t yd)|₀ = h⁴ Σ_x (D_wF_g(h, Ξ_h e(x))[Ξ_h ė(x)] - (Λ/κ) Dv(e(x))[ė(x)])`. -/
theorem hasDerivAt_gravAction {h : ℝ} (hh : h ≠ 0) (y yd : Grid n → Field 𝔄 𝓗 𝓢)
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1)
    (hreg : ∀ x, GravRegular (h, (stencil h (shiftVec n) x (coframeM y) : T4))) :
    HasDerivAt (fun t : ℝ => gravAction D h (y + t • yd))
      (h ^ 4 * ∑ x, (jetDeriv (Γg D.κ) h (stencil h (shiftVec n) x (coframeM y))
          (stencil h (shiftVec n) x (coframeM yd)) -
        D.Λ / D.κ * fderiv ℝ volM (coframeM y x) (coframeM yd x))) 0 := by
  have hc : ∀ᶠ t in 𝓝 (0 : ℝ), (∀ x, 0 < (coframe (y + t • yd) x).det) ∧
      ∀ x μ ν, ‖cartanPlaquette h (coframe (y + t • yd)) x μ ν - 1‖ < 1 := by
    have ht : Tendsto (fun t : ℝ => y + t • yd) (𝓝 0) (𝓝 y) := by
      have hcont : Continuous fun t : ℝ => y + t • yd := by fun_prop
      have e0 : y + (0 : ℝ) • yd = y := by
        funext x
        simp only [Pi.add_apply, Pi.smul_apply]
        exact (congrArg (y x + ·) (zero_smul ℝ (yd x))).trans (add_zero _)
      have := hcont.tendsto 0
      rwa [e0] at this
    exact ht.eventually (eventually_chart h hdet hlog)
  have hev : (fun t : ℝ => gravAction D h (y + t • yd)) =ᶠ[𝓝 0] fun t =>
      h ^ 4 * ∑ x, (Γg D.κ (h, stencil h (shiftVec n) x (coframeM y + t • coframeM yd)) -
        D.Λ / D.κ * volM (coframeM y x + t • coframeM yd x)) := by
    filter_upwards [hc] with t ht
    unfold gravAction
    rw [sum_gravityDensity_eq' D hh _ ht.1 ht.2, coframe_add_smul]
    rfl
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun x _ => ?_)
  refine HasDerivAt.sub ?_ (HasDerivAt.const_mul _ ?_)
  · set w := stencil h (shiftVec n) x (coframeM y)
    set w' := stencil h (shiftVec n) x (coframeM yd)
    have hd : DifferentiableAt ℝ (fun w => Γg D.κ (h, w)) w :=
      differentiableAt_slice (z := (h, w)) ((contDiffAt_Γg D.κ (hreg x)).differentiableAt (by simp))
    have hline : HasDerivAt (fun t : ℝ => w + t • w') w' 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const w').const_add w
      simpa using this
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    show Γg D.κ (h, stencil h (shiftVec n) x (coframeM y + t • coframeM yd)) = Γg D.κ (h, w + t • w')
    simp only [w, w', map_add, map_smul]
  · have hd : DifferentiableAt ℝ volM (coframeM y x) :=
      (contDiffAt_volM (hdet x).ne').differentiableAt (by simp)
    have hline : HasDerivAt (fun t : ℝ => coframeM y x + t • coframeM yd x) (coframeM yd x) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const (coframeM yd x)).const_add (coframeM y x)
      simpa using this
    exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)

end LocalNorm

end Action

/-! ### Lifted tests, the literal first variation and its covector form -/

/-- The volume part of the variation covector: `τ ↦ Dv(e)[lift(e, τ_0)]`. -/
def volCov (e : M4) : T4 →L[ℝ] ℝ :=
  (fderiv ℝ volM e).comp ((liftL e).comp
    ((ContinuousLinearMap.proj none).comp (ContinuousLinearMap.fst ℝ V4 Q4)))

/-- **The grid variation covector** at a node: the jet-derivative of the curvature density along
the lifted test jet, minus `(Λ/κ)` times the volume part. -/
def gridCov (κ Λ h : ℝ) {n : ℕ} [NeZero n] (e : Grid n → M4) (x : Grid n) : T4 →L[ℝ] ℝ :=
  varCov (Γg κ) h (valsArr e x) (diffsArr h e x) (Lmap (valsArr e x)) (Bmap (nextArr e x))
    (Amap (valsArr e x) (nextArr e x)) - (Λ / κ) • volCov (e x)

/-- The nodal samples `k(x/N)` of a test. -/
def sampleTest (N : ℕ) (τ : C2Test M4) : Grid N → M4 := fun x => τ.f (TorusCellEmbedding.samplePt x)

/-- The test jet `Ξ_h 𝒮_h k (x)` (shifted samples and their normalised differences). -/
def testJet (h : ℝ) {n : ℕ} [NeZero n] (kN : Grid n → M4) (x : Grid n) : T4 :=
  stencil h (shiftVec n) x kN

section VariationDef

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- **The nodally lifted inverse-metric test** `𝓘_h k`: the record variation whose coframe
component is the symmetric lift `ė(x) = lift(e(x), k(x/N))` and whose other components vanish. -/
def liftRecord (N : ℕ) [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : C2Test M4) : Grid N → Field 𝔄 𝓗 𝓢 :=
  fun x => (liftM (coframe y x) (sampleTest N τ x), 0)

/-- **The literal first variation** `D S_{g,h}^{loc}(e_h)[𝓘_h k]`, `h = 1/N`. -/
def gravVariation (N : ℕ) [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : C2Test M4) : ℝ :=
  deriv (fun t : ℝ => gravAction D (N : ℝ)⁻¹ (y + t • liftRecord N y τ)) 0

variable {N : ℕ} [NeZero N]

theorem coframeM_liftRecord (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : C2Test M4) :
    coframeM (liftRecord N y τ) = liftArr (coframeM y) (sampleTest N τ) := rfl

theorem integral_pc_real (G : Grid N → ℝ) :
    ∫ y, TorusPiecewiseConstantTranslation.pc G y = ((N : ℝ)⁻¹) ^ 4 * ∑ g, G g := by
  rw [integral_pc, smul_eq_mul, inv_pow]

section LocalNorm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- **The literal first variation as an integral of the grid covector against the test jet**:
`D S_{g,h}^{loc}(e_h)[𝓘_h k] = ∫ R^0(gridCov)(y) [R^0(Ξ_h 𝒮_h k)(y)] dy`. -/
theorem gravVariation_eq (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : C2Test M4)
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette (N : ℝ)⁻¹ (coframe y) x μ ν - 1‖ < 1)
    (hreg : ∀ x, GravRegular ((N : ℝ)⁻¹, (stencil (N : ℝ)⁻¹ (shiftVec N) x (coframeM y) : T4))) :
    gravVariation D N y τ =
      ∫ y', TorusPiecewiseConstantTranslation.pc (gridCov D.κ D.Λ (N : ℝ)⁻¹ (coframeM y)) y'
        (TorusPiecewiseConstantTranslation.pc (testJet (N : ℝ)⁻¹ (sampleTest N τ)) y') := by
  have hN : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N))
  unfold gravVariation
  rw [(hasDerivAt_gravAction D hN y (liftRecord N y τ) hdet hlog hreg).deriv]
  have h2 : (fun y' => TorusPiecewiseConstantTranslation.pc
      (gridCov D.κ D.Λ (N : ℝ)⁻¹ (coframeM y)) y'
        (TorusPiecewiseConstantTranslation.pc (testJet (N : ℝ)⁻¹ (sampleTest N τ)) y')) =
      TorusPiecewiseConstantTranslation.pc (fun x => gridCov D.κ D.Λ (N : ℝ)⁻¹ (coframeM y) x
        (testJet (N : ℝ)⁻¹ (sampleTest N τ) x)) := rfl
  rw [h2, integral_pc_real]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coframeM_liftRecord, stencil_lift hN]
  simp only [gridCov, testJet, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, varCov, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.prod_apply, stencil_eq]
  congr 1
  simp only [volCov, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst', liftL_apply]
  simp only [valsArr, shiftVec_none, add_zero]
  rfl

end LocalNorm

end VariationDef

/-! ### The continuum first-order Palatini variation -/

/-- An array regarded on the canonical carrier. -/
def asM4 (M : Mat) : M4 := fun i j => M i j

/-- The constant jet of a continuum first jet `(e, p)`, as a continuous linear map. -/
def constJetL : M4 × (Fin 4 → M4) →L[ℝ] T4 :=
  (ContinuousLinearMap.pi fun _ : Shift => ContinuousLinearMap.fst ℝ M4 (Fin 4 → M4)).prod
    (ContinuousLinearMap.pi fun sl : Shift × Fin 4 =>
      (ContinuousLinearMap.proj sl.2).comp (ContinuousLinearMap.snd ℝ M4 (Fin 4 → M4)))

@[simp] theorem constJetL_apply (w : M4 × (Fin 4 → M4)) :
    constJetL w = ((fun _ => w.1, fun sl => w.2 sl.2) : T4) := rfl

/-- The first-order Palatini density on the canonical carriers:
`L^{(1)}(e, p) = gravCurv κ (0, ē, p̄) - (Λ/κ) v(e)` (`NativeGravityJet.palatiniFirstOrder`). -/
def palatiniL (κ Λ : ℝ) (w : M4 × (Fin 4 → M4)) : ℝ :=
  Γg κ (0, constJetL w) - Λ / κ * volM w.1

theorem palatiniL_eq (κ Λ : ℝ) (w : M4 × (Fin 4 → M4)) :
    palatiniL κ Λ w = palatiniFirstOrder κ Λ w.1 w.2 := rfl

/-- The lifted continuum variation `(ė, ∂ė) = (lift(e, k), lift(e, ∂k) + D_e lift(e, k)[p])`. -/
def liftedVar (e : M4) (p : Fin 4 → M4) (kv : M4) (kd : Fin 4 → M4) : M4 × (Fin 4 → M4) :=
  (liftM e kv, fun lam => liftM e (kd lam) + dqLift e e (p lam) kv)

/-- `dqLift(e, e, p, k)` is the derivative of the lift in the coframe: `D_e lift(e, k)[p]`. -/
theorem hasDerivAt_liftM (e p k : M4) :
    HasDerivAt (fun t : ℝ => asM4 (liftM (e + t • p) k)) (asM4 (dqLift e e p k)) 0 := by
  have h : ∀ t : ℝ, asM4 (liftM (e + t • p) k) =
      asM4 (liftM e k) + t • asM4 (dqLift e (e + t • p) p k) := fun t => by
    funext i j
    have := congrFun (congrFun (liftM_add_smul_sub e p k t) i) j
    simp only [asM4, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
    exact sub_eq_iff_eq_add'.1 this
  simp only [h]
  have hc : Continuous fun t : ℝ => asM4 (dqLift e (e + t • p) p k) := by
    have h1 : Continuous fun t : ℝ => ((e, e + t • p) : M4 × M4) := by fun_prop
    have h2 := ((continuous_dqLiftL_apply p).comp h1).clm_apply (continuous_const (y := k))
    exact h2
  have hd : HasDerivAt (fun t : ℝ => t • asM4 (dqLift e (e + t • p) p k))
      (asM4 (dqLift e e p k)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have h1 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    simp only [zero_smul, add_zero] at h1
    refine h1.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    simp only [slope_def_module, zero_smul, sub_zero]
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  exact hd.const_add _

/-- **The continuum gravitational first variation** `D𝒮_{g,θ}(e)[k]`: the first variation of the
first-order Palatini action `∫ L^{(1)}(e, ∂e)` along the lifted test
`(ė, ∂ė) = (lift(e, k), lift(e, ∂k) + D_e lift(e, k)[∂e])`, at a coframe `e` with first jet `p`. -/
def contGravVariation (κ Λ : ℝ) (e₀ : UnitAddTorus (Fin 4) → M4)
    (p : Fin 4 → UnitAddTorus (Fin 4) → M4) (τ : C2Test M4) : ℝ :=
  ∫ y, fderiv ℝ (palatiniL κ Λ) (e₀ y, fun lam => p lam y)
    (liftedVar (e₀ y) (fun lam => p lam y) (τ.f y) (fun lam => τ.df lam y))

/-- The limit test jet `(k(y) at every shift, ∂_λ k(y))`. -/
def limitJet (kv : M4) (kd : Fin 4 → M4) : T4 := (fun _ => kv, fun sl => kd sl.2)

/-- The limit variation covector at a coframe value `e` with first jet `p`. -/
def limitCov (κ Λ : ℝ) (e : M4) (p : Fin 4 → M4) : T4 →L[ℝ] ℝ :=
  varCov (Γg κ) 0 (fun _ => e) (fun sl => p sl.2) (Lmap fun _ => e) (Bmap fun _ => e)
    (Amap (fun _ => e) fun _ => e) - (Λ / κ) • volCov e

theorem gravRegular_constJet {e : M4} (he : Matrix.det (show Mat from e) ≠ 0) (p : Fin 4 → M4) :
    GravRegular ((0 : ℝ), constJetL (e, p)) := by
  refine ⟨fun s => he, fun μ => ?_, fun μ ν => ?_⟩
  · have : emM μ (constJetL (e, p)) + (0 : ℝ) • pmM μ (constJetL (e, p)) = e := by
      ext i j
      show e i j + (0 : ℝ) * p μ i j = e i j
      ring
    rw [this]; exact he
  · simp [plaqDev, plaqDevGen, slots]

/-- **The limit covector is the first variation of the first-order Palatini density** along the
lifted test: `limitCov(e, p)[k̄] = D L^{(1)}(e, p)[lift(e,k), lift(e,∂k) + D_e lift(e,k)[p]]`. -/
theorem limitCov_apply (κ Λ : ℝ) {e : M4} (he : Matrix.det (show Mat from e) ≠ 0)
    (p : Fin 4 → M4) (kv : M4) (kd : Fin 4 → M4) :
    limitCov κ Λ e p (limitJet kv kd) = fderiv ℝ (palatiniL κ Λ) (e, p) (liftedVar e p kv kd) := by
  have hΓ : DifferentiableAt ℝ (Γg κ) ((0 : ℝ), constJetL (e, p)) :=
    (contDiffAt_Γg κ (gravRegular_constJet he p)).differentiableAt (by simp)
  have hv : DifferentiableAt ℝ volM e := (contDiffAt_volM he).differentiableAt (by simp)
  have hin : HasFDerivAt (fun w : M4 × (Fin 4 → M4) => ((0 : ℝ), constJetL w))
      ((0 : M4 × (Fin 4 → M4) →L[ℝ] ℝ).prod constJetL) (e, p) :=
    (hasFDerivAt_const (0 : ℝ) (e, p)).prodMk constJetL.hasFDerivAt
  have h1 := hΓ.hasFDerivAt.comp (e, p) hin
  have h2 := (hv.hasFDerivAt.comp (e, p) (hasFDerivAt_fst (𝕜 := ℝ) (p := (e, p)))).const_mul
    (Λ / κ)
  have hP : HasFDerivAt (palatiniL κ Λ) ((fderiv ℝ (Γg κ) ((0 : ℝ), constJetL (e, p))).comp
      ((0 : M4 × (Fin 4 → M4) →L[ℝ] ℝ).prod constJetL) -
      (Λ / κ) • (fderiv ℝ volM e).comp (ContinuousLinearMap.fst ℝ M4 (Fin 4 → M4))) (e, p) :=
    h1.sub h2
  rw [hP.fderiv]
  have hJ : jetDeriv (Γg κ) 0 (constJetL (e, p)) =
      (fderiv ℝ (Γg κ) ((0 : ℝ), constJetL (e, p))).comp
        (ContinuousLinearMap.inr ℝ ℝ T4) := jetDeriv_eq (z := ((0 : ℝ), constJetL (e, p))) hΓ
  simp only [limitCov, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, varCov,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
  have e1 : ((fun _ => e, fun sl => p sl.2) : V4 × Q4) = constJetL (e, p) := rfl
  rw [e1, hJ]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply]
  congr 2

/-! ### The grid jets lie in the compact normalised chart -/

section GridChart

variable {N : ℕ} [NeZero N]

theorem omegaM_stencil (h : ℝ) (e : Grid N → M4) (x : Grid N) (μ : Fin 4) :
    omegaM μ (valsArr e x, diffsArr h e x) = omegaLink h e x μ := by
  simp only [omegaM, valsArr, diffsArr, shiftVec_none, add_zero, omegaLink]
  rfl

theorem omegaShiftM_stencil (h : ℝ) (e : Grid N → M4) (x : Grid N) (ν μ : Fin 4) :
    omegaShiftM ν μ (valsArr e x, diffsArr h e x) = omegaLink h e (x + unitVec N μ) ν := by
  simp only [omegaShiftM, valsArr, diffsArr, shiftVec_some_true, omegaLink]
  rfl

theorem fwdDiff_entry (h : ℝ) (f : Grid N → M4) (lam : Fin 4) (z : Grid N) (i j : Fin 4) :
    fwdDiff h lam f z i j = h⁻¹ * (f (z + unitVec N lam) i j - f z i j) := rfl

section LocalNorm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_asM4 (M : Mat) : ‖asM4 M‖ = ‖M‖ := rfl

/-- **The literal stencils of a chart-valued record lie in the compact normalised chart.** -/
theorem normJet_mem_gravChart {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {Ke : Set Mat} {Me c : ℝ}
    (hMe : ∀ M ∈ Ke, ‖M‖ ≤ Me) (e : Grid N → M4) (hval : ∀ x, (e x : Mat) ∈ Ke)
    (hmar : ∀ x μ, h * ‖(omegaLink h e x μ : Mat)‖ ≤ c) (x : Grid N) :
    normJet h (valsArr e x) (diffsArr h e x) ∈ gravChart Ke (1 + 2 * Me) c := by
  set q := diffsArr h e x
  set K := 1 + ‖q‖ with hK
  have hK0 : 0 < K := one_add_norm_pos q
  have hMe0 : 0 ≤ Me := (norm_nonneg _).trans (hMe _ (hval x))
  refine ⟨by unfold normJet; positivity, ?_, fun s => hval _,
    HomogeneousJetVariation.norm_normalize_le q, ?_, ?_⟩
  · -- the normalised mesh
    show h * K ≤ 1 + 2 * Me
    have hq : ‖q‖ ≤ 2 * Me / h := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun sl => ?_
      show ‖fwdDiff h sl.2 e (x + shiftVec N sl.1)‖ ≤ 2 * Me / h
      unfold ShiftedJetAction.fwdDiff
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le), inv_mul_le_iff₀ hh,
        mul_div_cancel₀ _ hh.ne']
      have m1 : ‖e (x + shiftVec N sl.1 + unitVec N sl.2)‖ ≤ Me := hMe _ (hval _)
      have m2 : ‖e (x + shiftVec N sl.1)‖ ≤ Me := hMe _ (hval _)
      exact (norm_sub_le _ _).trans (by linarith)
    have : h * ‖q‖ ≤ 2 * Me := by
      have := mul_le_mul_of_nonneg_left hq hh.le
      rwa [mul_div_cancel₀ _ hh.ne'] at this
    rw [hK]; nlinarith
  · -- the segment values
    intro s lam
    refine (congrArg (· ∈ Ke) ?_).mpr (hval (x + shiftVec N s + unitVec N lam))
    ext i j
    show e (x + shiftVec N s) i j + (h * K) * (K⁻¹ * (h⁻¹ * (e (x + shiftVec N s + unitVec N lam) i j -
      e (x + shiftVec N s) i j))) = e (x + shiftVec N s + unitVec N lam) i j
    field_simp
    ring
  · -- the margin
    intro μ ν
    have e1 : HomogeneousJetVariation.normalize q = K⁻¹ • q := rfl
    have h1 : omegaM μ (valsArr e x, HomogeneousJetVariation.normalize q) =
        K⁻¹ • omegaM μ (valsArr e x, q) := omegaM_smul μ _ q K⁻¹
    have h2 : omegaShiftM ν μ (valsArr e x, HomogeneousJetVariation.normalize q) =
        K⁻¹ • omegaShiftM ν μ (valsArr e x, q) := omegaShiftM_smul ν μ _ q K⁻¹
    have hc1 : h * ‖omegaM μ (valsArr e x, q)‖ ≤ c := by
      rw [omegaM_stencil]; exact hmar x μ
    have hc2 : h * ‖omegaShiftM ν μ (valsArr e x, q)‖ ≤ c := by
      rw [omegaShiftM_stencil]; exact hmar _ ν
    refine ⟨?_, ?_⟩
    · show h * K * ‖omegaM μ (valsArr e x, HomogeneousJetVariation.normalize q)‖ ≤ c
      rw [h1, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hK0.le)]
      calc h * K * (K⁻¹ * ‖omegaM μ (valsArr e x, q)‖) = h * ‖omegaM μ (valsArr e x, q)‖ := by
            field_simp
        _ ≤ c := hc1
    · show h * K * ‖omegaShiftM ν μ (valsArr e x, HomogeneousJetVariation.normalize q)‖ ≤ c
      rw [h2, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hK0.le)]
      calc h * K * (K⁻¹ * ‖omegaShiftM ν μ (valsArr e x, q)‖) =
            h * ‖omegaShiftM ν μ (valsArr e x, q)‖ := by field_simp
        _ ≤ c := hc2

/-- The literal stencils are regular points of the jet density. -/
theorem gravRegular_stencil {h : ℝ} (hh : 0 < h) {Ke : Set Mat} (hdet : ∀ M ∈ Ke, 0 < M.det)
    {c : ℝ} (hc : c ≤ 1 / 64) (e : Grid N → M4) (hval : ∀ x, (e x : Mat) ∈ Ke)
    (hmar : ∀ x μ, h * ‖(omegaLink h e x μ : Mat)‖ ≤ c) (x : Grid N) :
    GravRegular (h, (stencil h (shiftVec N) x e : T4)) := by
  rw [stencil_eq]
  refine ⟨fun s => (hdet _ (hval _)).ne', fun μ => ?_, fun μ ν => ?_⟩
  · have : emM μ (valsArr e x, diffsArr h e x) + h • pmM μ (valsArr e x, diffsArr h e x) =
        e x := by
      ext i j
      show e (x + shiftVec N (some (false, μ))) i j + h * (h⁻¹ * (e (x + shiftVec N (some (false, μ))
        + unitVec N μ) i j - e (x + shiftVec N (some (false, μ))) i j)) = e x i j
      have hx : x + shiftVec N (some (false, μ)) + unitVec N μ = x := by
        rw [shiftVec_some_false, add_assoc, neg_add_cancel, add_zero]
      rw [hx]; field_simp; ring
    have h0 := (hdet _ (hval x)).ne'
    rw [← this] at h0
    exact h0
  · refine norm_plaqDev_lt_of_margin hc hh.le (fun μ ν => ⟨?_, ?_⟩) μ ν
    · show h * ‖omegaM μ (valsArr e x, diffsArr h e x)‖ ≤ c
      rw [omegaM_stencil]; exact hmar x μ
    · show h * ‖omegaShiftM ν μ (valsArr e x, diffsArr h e x)‖ ≤ c
      rw [omegaShiftM_stencil]; exact hmar _ ν

/-- The literal Cartan plaquettes are in the logarithm chart under the margin. -/
theorem cartan_log_lt {h : ℝ} (hh : 0 < h) {c : ℝ} (hc : c ≤ 1 / 64) (e : Grid N → Mat)
    (hmar : ∀ x μ, h * ‖omegaLink h e x μ‖ ≤ c) (x : Grid N) (μ ν : Fin 4) :
    ‖cartanPlaquette h e x μ ν - 1‖ < 1 := by
  unfold cartanPlaquette NativeScaling.gaugePlaquette
  have hb : ∀ z lam, ‖h • matToOp (omegaLink h e z lam)‖ ≤ 4 * c := by
    intro z lam
    rw [norm_smul, Real.norm_of_nonneg hh.le]
    calc h * ‖matToOp (omegaLink h e z lam)‖ ≤ h * (4 * ‖omegaLink h e z lam‖) :=
          mul_le_mul_of_nonneg_left (norm_matToOp_le _) hh.le
      _ = 4 * (h * ‖omegaLink h e z lam‖) := by ring
      _ ≤ 4 * c := by linarith [hmar z lam]
  have h1 := hb x μ
  have h2 := hb (x + unitVec N μ) ν
  have h3 := hb (x + unitVec N ν) μ
  have h4 := hb x ν
  generalize h • matToOp (omegaLink h e x μ) = a at h1 ⊢
  generalize h • matToOp (omegaLink h e (x + unitVec N μ) ν) = b at h2 ⊢
  generalize h • matToOp (omegaLink h e (x + unitVec N ν) μ) = c' at h3 ⊢
  generalize h • matToOp (omegaLink h e x ν) = d at h4 ⊢
  refine norm_exp4_sub_one_lt ?_
  rw [norm_neg, norm_neg]
  linarith

/-- Jets at the mesh origin with chart values and normalised differences lie in the chart. -/
theorem chart_zero_mem {Ke : Set Mat} {v : V4} (hv : ∀ s, (v s : Mat) ∈ Ke) (q : Q4)
    (hq : ‖q‖ ≤ 1) : ((0 : ℝ), (v, q)) ∈ (gravChart Ke 0 0 : Set (ℝ × T4)) := by
  refine ⟨le_rfl, le_rfl, hv, hq, fun s lam => ?_, fun μ ν => ⟨?_, ?_⟩⟩
  · refine (congrArg (· ∈ Ke) ?_).mpr (hv s)
    ext i j
    show v s i j + 0 * q (s, lam) i j = v s i j
    ring
  · show 0 * _ ≤ 0
    simp
  · show 0 * _ ≤ 0
    simp

/-- Constant jets at the mesh origin lie in the normalised chart. -/
theorem normJet_zero_mem {Ke : Set Mat} {M : M4} (hM : (M : Mat) ∈ Ke) (q : Q4) :
    normJet 0 (fun (_ : Shift) => M) q ∈ (gravChart Ke 0 0 : Set (ℝ × T4)) := by
  refine ⟨by simp [normJet], by simp [normJet], fun s => hM,
    HomogeneousJetVariation.norm_normalize_le q, fun s lam => ?_, fun μ ν => ⟨?_, ?_⟩⟩
  · refine (congrArg (· ∈ Ke) ?_).mpr hM
    ext i j
    show M i j + 0 * (1 + ‖q‖) * (HomogeneousJetVariation.normalize q (s, lam) i j) = M i j
    ring
  · show 0 * (1 + ‖q‖) * _ ≤ 0
    simp
  · show 0 * (1 + ‖q‖) * _ ≤ 0
    simp

end LocalNorm

end GridChart

/-! ### Convergence of the variation covectors -/

section Convergence

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

local instance fact_one_le_two_ng : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_one_ng : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩

/-- Shifts by the stencil offsets preserve strong convergence of raw reconstructions. -/
theorem lpTendsto_shiftVec (hn : Tendsto n atTop atTop) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ∀ k, Grid (n k) → E}
    {g : UnitAddTorus (Fin 4) → E} (hv : LpTendsto volume p (fun k => pc (v k)) g) (s : Shift) :
    LpTendsto volume p (fun k => pc (fun x => v k (x + shiftVec (n k) s))) g := by
  rcases s with _ | ⟨b, μ⟩
  · refine hv.congr (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => rfl)
    simp [pc, shiftVec_none]
  · cases b
    · refine (LpTendsto.shiftInt hn hp hv μ (-1)).congr
        (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => rfl)
      simp only [pc, TorusPiecewiseConstantTranslation.shift, shiftVec, unitVec, Int.cast_neg,
        Int.cast_one, Pi.single_neg]
    · refine (LpTendsto.shiftInt hn hp hv μ 1).congr
        (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => rfl)
      simp only [pc, TorusPiecewiseConstantTranslation.shift, shiftVec, unitVec, Int.cast_one]

theorem lpTendsto_unitVec (hn : Tendsto n atTop atTop) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ∀ k, Grid (n k) → E}
    {g : UnitAddTorus (Fin 4) → E} (hv : LpTendsto volume p (fun k => pc (v k)) g) (μ : Fin 4) :
    LpTendsto volume p (fun k => pc (fun x => v k (x + unitVec (n k) μ))) g :=
  lpTendsto_shiftVec hn hp hv (some (true, μ))

theorem shiftVec_mem (N : ℕ) (s : Shift) :
    shiftVec N s = 0 ∨ ∃ μ, shiftVec N s = Pi.single μ 1 ∨ shiftVec N s = -Pi.single μ 1 := by
  rcases s with _ | ⟨b, μ⟩
  · exact Or.inl rfl
  · cases b
    · exact Or.inr ⟨μ, Or.inr rfl⟩
    · exact Or.inr ⟨μ, Or.inl rfl⟩

/-- **Test-jet consistency**: the raw reconstruction of the sampled test jet is uniformly within
`3/N ‖k‖_{C²}` of the limit test jet `(k, ∂k)`. -/
theorem norm_pc_testJet_sub_le {N : ℕ} [NeZero N] (τ : C2Test M4) (y : UnitAddTorus (Fin 4)) :
    ‖pc (testJet (N : ℝ)⁻¹ (sampleTest N τ)) y - limitJet (τ.f y) (fun lam => τ.df lam y)‖ ≤
      3 * (N : ℝ)⁻¹ * τ.norm := by
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hτ := τ.norm_nonneg
  set x := TorusPiecewiseConstantTranslation.index N y
  have hcoord : ∀ s : Shift, ∀ i, ‖TorusCellEmbedding.samplePt (x + shiftVec N s) i - y i‖ ≤
      2 * (N : ℝ)⁻¹ := fun s i => norm_samplePt_index_add_sub_le y _ (shiftVec_mem N s) i
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
    show ‖τ.f (TorusCellEmbedding.samplePt (x + shiftVec N s)) - τ.f y‖ ≤ 3 * (N : ℝ)⁻¹ * τ.norm
    refine (norm_f_samplePt_sub_le τ y _ (hcoord s)).trans ?_
    nlinarith
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun sl => ?_
    show ‖fwdDiff (N : ℝ)⁻¹ sl.2 (sampleTest N τ) (x + shiftVec N sl.1) - τ.df sl.2 y‖ ≤
      3 * (N : ℝ)⁻¹ * τ.norm
    have h := norm_fd_samplePt_sub_le τ y (x + shiftVec N sl.1) sl.2 (hcoord sl.1)
    have e : fwdDiff (N : ℝ)⁻¹ sl.2 (sampleTest N τ) (x + shiftVec N sl.1) =
        (N : ℝ) • (τ.f (TorusCellEmbedding.samplePt (x + shiftVec N sl.1 + Pi.single sl.2 1)) -
          τ.f (TorusCellEmbedding.samplePt (x + shiftVec N sl.1))) := by
      simp only [ShiftedJetAction.fwdDiff, sampleTest, inv_inv, unitVec]
    rw [e]
    refine h.trans (le_of_eq ?_)
    ring

theorem norm_limitJet_le (τ : C2Test M4) (y : UnitAddTorus (Fin 4)) :
    ‖limitJet (τ.f y) (fun lam => τ.df lam y)‖ ≤ τ.norm := by
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · exact (pi_norm_le_iff_of_nonneg τ.norm_nonneg).2 fun _ =>
      ((τ.f).norm_coe_le_norm y).trans τ.f_le
  · exact (pi_norm_le_iff_of_nonneg τ.norm_nonneg).2 fun sl =>
      ((τ.df sl.2).norm_coe_le_norm y).trans (τ.df_le sl.2)

theorem continuousOn_volCov {Ke : Set M4} (hKdet : ∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) :
    ContinuousOn volCov Ke := by
  intro M hM
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fderiv ℝ volM) M :=
    ((contDiffAt_volM (hKdet M hM).ne').fderiv_right (m := 0) (by norm_num)).continuousAt
  have h2 : Continuous fun M : M4 => (liftL M).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Shift => M4) none).comp
        (ContinuousLinearMap.fst ℝ V4 Q4)) :=
    (ContinuousLinearMap.compL ℝ T4 M4 M4 |>.flip _).continuous.comp continuous_liftL
  exact (ContinuousLinearMap.compL ℝ T4 M4 ℝ).continuous₂.continuousAt.comp
    (h1.prodMk h2.continuousAt)

/-- **Strong `L¹` convergence of the variation covectors** (the analytic core of
`prop:native-gravity-firstjet`): under strong `L²` first-jet convergence, a compact oriented chart
and the logarithm margin, `R^0(gridCov_h) → limitCov(e, p)` strongly in `L¹(𝕋⁴)`. -/
theorem lpTendsto_gridCov (κ Λ : ℝ) (hn : Tendsto n atTop atTop) (e : ∀ k, Grid (n k) → M4)
    (e₀ : UnitAddTorus (Fin 4) → M4) (p : Fin 4 → UnitAddTorus (Fin 4) → M4) {Ke : Set Mat}
    (hKe : IsCompact Ke) (hKdet : ∀ M ∈ Ke, 0 < M.det) (hval : ∀ k x, (e k x : Mat) ∈ Ke)
    {c : ℝ} (hc : c ≤ 1 / 64)
    (hmar : ∀ k x μ, (n k : ℝ)⁻¹ * ‖asM4 (omegaLink (n k : ℝ)⁻¹ (e k) x μ)‖ ≤ c)
    (he : LpTendsto volume 2 (fun k => pc (e k)) e₀)
    (hp : ∀ μ, LpTendsto volume 2 (fun k => pc (fwdDiff (n k : ℝ)⁻¹ μ (e k))) (p μ)) :
    LpTendsto volume 1 (fun k => pc (gridCov κ Λ (n k : ℝ)⁻¹ (e k)))
      (fun y' => limitCov κ Λ (e₀ y') (fun lam => p lam y')) := by
  have hNpos : ∀ k, (0 : ℝ) < (n k : ℝ)⁻¹ := fun k => by
    have : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    positivity
  have hN1 : ∀ k, (n k : ℝ)⁻¹ ≤ 1 := fun k => by
    have : (1 : ℝ) ≤ n k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne (n k))
    exact inv_le_one_of_one_le₀ this
  have hρ : Tendsto (fun k => (n k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn)
  let Ke4 : Set M4 := Ke
  have hKe4 : IsCompact Ke4 := hKe
  obtain ⟨Me, hMe⟩ := hKe4.isBounded.exists_norm_le
  set KV : Set V4 := Set.univ.pi fun _ => Ke4
  set KQ : Set Q4 := Set.univ.pi fun _ => Ke4
  have hKV : IsCompact KV := isCompact_univ_pi fun _ => hKe4
  have hKQ : IsCompact KQ := isCompact_univ_pi fun _ => hKe4
  -- strong convergence of the shifted arrays
  have hv2 : LpTendsto volume 2 (fun k => pc (valsArr (e k))) (fun y' _ => e₀ y') :=
    LpTendsto.pi fun s => lpTendsto_shiftVec hn (by norm_num) he s
  have hq2 : LpTendsto volume 2 (fun k => pc (diffsArr (n k : ℝ)⁻¹ (e k)))
      (fun y' sl => p sl.2 y') :=
    LpTendsto.pi fun sl => lpTendsto_shiftVec hn (by norm_num) (hp sl.2) sl.1
  have hw2 : LpTendsto volume 2 (fun k => pc (nextArr (e k))) (fun y' _ => e₀ y') := by
    refine LpTendsto.pi fun sl => ?_
    refine (lpTendsto_unitVec hn (by norm_num) (lpTendsto_shiftVec hn (by norm_num) he sl.1)
      sl.2).congr (fun k => Eventually.of_forall fun y' => ?_) (Eventually.of_forall fun _ => rfl)
    simp only [pc, nextArr, add_right_comm]
  have hvm := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (hv2.memLp k).1)
    hv2.memLp_lim.1 hv2.tendsto
  have hwm := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (hw2.memLp k).1)
    hw2.memLp_lim.1 hw2.tendsto
  have hem := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (he.memLp k).1)
    he.memLp_lim.1 he.tendsto
  have hvK : ∀ k y', pc (valsArr (e k)) y' ∈ KV := fun k y' s _ => hval k _
  have hwK : ∀ k y', pc (nextArr (e k)) y' ∈ KQ := fun k y' sl _ => hval k _
  have hv0K : ∀ᵐ y', (fun _ : Shift => e₀ y') ∈ KV :=
    ae_mem_of_tendstoInMeasure hKV.isClosed hvm fun k => Eventually.of_forall (hvK k)
  have hw0K : ∀ᵐ y', (fun _ : Shift × Fin 4 => e₀ y') ∈ KQ :=
    ae_mem_of_tendstoInMeasure hKQ.isClosed hwm fun k => Eventually.of_forall (hwK k)
  have he0K : ∀ᵐ y', e₀ y' ∈ Ke4 :=
    ae_mem_of_tendstoInMeasure hKe4.isClosed hem fun k => Eventually.of_forall fun y' => hval k _
  -- the coefficient maps
  have hL := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn hKV continuous_Lmap.continuousOn
    (fun k => Eventually.of_forall (hvK k)) hv0K hvm
  have hB := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn hKQ continuous_Bmap.continuousOn
    (fun k => Eventually.of_forall (hwK k)) hw0K hwm
  have hAc : ContinuousOn (fun p : V4 × Q4 => Amap p.1 p.2) (KV ×ˢ KQ) :=
    continuous_Amap.continuousOn
  have hA := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn
    (W := Q4 →L[ℝ] T4 →L[ℝ] Q4) (Φ := fun p : V4 × Q4 => Amap p.1 p.2) (hKV.prod hKQ) hAc
    (fun k => Eventually.of_forall fun y' => ⟨hvK k y', hwK k y'⟩)
    (by filter_upwards [hv0K, hw0K] with y' h1 h2 using ⟨h1, h2⟩)
    (TendstoInMeasure.prodMk hvm hwm)
  obtain ⟨CL, hCL⟩ := IsCompact.exists_bound_of_continuousOn (E := T4 →L[ℝ] V4) hKV
    continuous_Lmap.continuousOn
  obtain ⟨CB, hCB⟩ := IsCompact.exists_bound_of_continuousOn (E := T4 →L[ℝ] Q4) hKQ
    continuous_Bmap.continuousOn
  obtain ⟨CA, hCA⟩ := IsCompact.exists_bound_of_continuousOn (E := Q4 →L[ℝ] T4 →L[ℝ] Q4)
    (hKV.prod hKQ) hAc
  set C := max CL (max CB CA)
  have hmem : ∀ k y', normJet (n k : ℝ)⁻¹ (pc (valsArr (e k)) y') (pc (diffsArr (n k : ℝ)⁻¹ (e k)) y')
      ∈ (gravChart Ke (1 + 2 * Me) c : Set (ℝ × T4)) :=
    fun k y' => normJet_mem_gravChart (hNpos k) (hN1 k) hMe (e k) (hval k) (hmar k) _
  have hKc : IsCompact (gravChart Ke (1 + 2 * Me) c : Set (ℝ × T4)) :=
    isCompact_gravChart hKe hKdet (1 + 2 * Me) c
  have hC1 : ∀ z ∈ (gravChart Ke (1 + 2 * Me) c : Set (ℝ × T4)), ContDiffAt ℝ 1 (Γg κ) z :=
    fun z hz => contDiffAt_of_mem_gravChart κ hKdet hc hz
  have hLm : ∀ k, AEStronglyMeasurable (fun y' => Lmap (pc (valsArr (e k)) y')) MeasureTheory.volume :=
    fun k => (stronglyMeasurable_pc (fun x => Lmap (valsArr (e k) x))).aestronglyMeasurable
  have hBm : ∀ k, AEStronglyMeasurable (fun y' => Bmap (pc (nextArr (e k)) y')) MeasureTheory.volume :=
    fun k => (stronglyMeasurable_pc (fun x => Bmap (nextArr (e k) x))).aestronglyMeasurable
  have hAm : ∀ k, AEStronglyMeasurable
      (fun y' => Amap (pc (valsArr (e k)) y') (pc (nextArr (e k)) y')) MeasureTheory.volume :=
    fun k => (stronglyMeasurable_pc (fun x => Amap (valsArr (e k) x)
      (nextArr (e k) x))).aestronglyMeasurable
  have hvm' : ∀ k, AEStronglyMeasurable (pc (valsArr (e k))) MeasureTheory.volume :=
    fun k => (stronglyMeasurable_pc _).aestronglyMeasurable
  have hLC : ∀ k y', ‖Lmap (pc (valsArr (e k)) y')‖ ≤ C :=
    fun k y' => (hCL _ (hvK k y')).trans (le_max_left _ _)
  have hBC : ∀ k y', ‖Bmap (pc (nextArr (e k)) y')‖ ≤ C :=
    fun k y' => (hCB _ (hwK k y')).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hAC : ∀ k y', ‖Amap (pc (valsArr (e k)) y') (pc (nextArr (e k)) y')‖ ≤ C :=
    fun k y' => (hCA (pc (valsArr (e k)) y', pc (nextArr (e k)) y') ⟨hvK k y', hwK k y'⟩).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hvar := lpTendsto_homogeneous_variation (μ := MeasureTheory.volume) (V := V4) (Q := Q4)
    (T := T4) (Γ := Γg κ) (Γg_scale κ) hKc hC1 hρ hvm' hvm hq2 hmem hLm hL hLC hBm hB hBC
    hAm hA hAC
  have hKdet4 : ∀ M ∈ Ke4, 0 < Matrix.det (show Mat from M) := hKdet
  have hvolc : ContinuousOn volCov Ke4 := continuousOn_volCov hKdet4
  have hvol := (LpProductContinuity.LpTendsto.comp_of_continuousOn (p := 1) ENNReal.one_ne_top
    (W := T4 →L[ℝ] ℝ) (Φ := volCov) hKe4 hvolc
    (fun k => Eventually.of_forall fun y' => hval k _) he0K hem
    (fun k => (stronglyMeasurable_pc (fun x => volCov (e k x))).aestronglyMeasurable)).2
  have hsum := hvar.sub (hvol.const_smul (Λ / κ))
  exact hsum.congr (fun k => Eventually.of_forall fun y' => rfl) (Eventually.of_forall fun y' => rfl)

end Convergence

/-! ### `prop:native-gravity-firstjet` -/

section Main

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem integral_norm_tendsto_zero {G : ℕ → UnitAddTorus (Fin 4) → T4 →L[ℝ] ℝ}
    {G₀ : UnitAddTorus (Fin 4) → T4 →L[ℝ] ℝ} (hG : LpTendsto MeasureTheory.volume 1 G G₀) :
    Tendsto (fun k => ∫ y', ‖G k y' - G₀ y'‖) atTop (𝓝 0) := by
  have e : ∀ k, ∫ y', ‖G k y' - G₀ y'‖ = (eLpNorm (G k - G₀) 1 MeasureTheory.volume).toReal := by
    intro k
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← integral_norm_eq_lintegral_enorm ((hG.memLp k).1.sub hG.memLp_lim.1)]
    rfl
  simp only [e]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG.tendsto
  rwa [ENNReal.toReal_zero] at this

/-- **`prop:native-gravity-firstjet` (`eq:native-gravity-firstvariation`).**  Let the actual
nodal coframes `e_h = coframe(y_h)` (`h = 1/n_k → 0`) of records of the native local action take
values in a compact oriented nondegenerate chart `K_e ⊂ {det > 0}`, satisfy the common
logarithm-chart condition `h |ω_{μ,h}| ≤ c_* ≤ 1/64` (`eq:native-gravity-log-margin`, entrywise sup
norm), and converge with their first differences: `R^0 e_h → e`, `R^0 D⁺_μ e_h → p_μ` strongly in
`L²` (`eq:native-coframe-firstjet`; `p_μ = ∂_μ e`).  Then the literal gravitational first
variation along the symmetric nodal lift of every inverse-metric test converges to the
first-order Palatini variation, **uniformly on the `C²` unit ball**:
for every `ε > 0`, eventually `|D S_{g,h}^{loc}(e_h)[𝓘_h k] - D𝒮_{g,θ}(e)[k]| ≤ ε ‖k‖_{C²}` for all
tests `k`. -/
theorem native_gravity_firstjet (D : Data 𝔄 𝓗 𝓢) (hn : Tendsto n atTop atTop)
    (y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢) (e₀ : UnitAddTorus (Fin 4) → M4)
    (p : Fin 4 → UnitAddTorus (Fin 4) → M4) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, 0 < M.det) (hval : ∀ k x, coframe (y k) x ∈ Ke) {c : ℝ}
    (hc : c ≤ 1 / 64)
    (hmar : ∀ k x μ, (n k : ℝ)⁻¹ * ‖asM4 (omegaLink (n k : ℝ)⁻¹ (coframe (y k)) x μ)‖ ≤ c)
    (he : LpTendsto MeasureTheory.volume 2 (fun k => pc (coframeM (y k))) e₀)
    (hp : ∀ μ, LpTendsto MeasureTheory.volume 2
      (fun k => pc (fwdDiff (n k : ℝ)⁻¹ μ (coframeM (y k)))) (p μ)) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : C2Test M4,
      |gravVariation D (n k) (y k) τ - contGravVariation D.κ D.Λ e₀ p τ| ≤ ε * τ.norm := by
  intro ε hε
  have hNpos : ∀ k, (0 : ℝ) < (n k : ℝ)⁻¹ := fun k => by
    have : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    positivity
  have hN1 : ∀ k, (n k : ℝ)⁻¹ ≤ 1 := fun k => by
    have : (1 : ℝ) ≤ n k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne (n k))
    exact inv_le_one_of_one_le₀ this
  have hρ : Tendsto (fun k => (n k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn)
  set G := fun k => pc (gridCov D.κ D.Λ (n k : ℝ)⁻¹ (coframeM (y k))) with hGdef
  set G₀ := fun y' => limitCov D.κ D.Λ (e₀ y') (fun lam => p lam y') with hG₀def
  have hG : LpTendsto MeasureTheory.volume 1 G G₀ :=
    lpTendsto_gridCov D.κ D.Λ hn (fun k => coframeM (y k)) e₀ p hKe hKdet hval hc hmar he hp
  have hG0int : Integrable G₀ := memLp_one_iff_integrable.1 hG.memLp_lim
  set I0 := ∫ y', ‖G₀ y'‖
  have hI0 : 0 ≤ I0 := integral_nonneg fun _ => norm_nonneg _
  -- the coframe limit lies in the chart a.e.
  let Ke4 : Set M4 := Ke
  have hKe4 : IsCompact Ke4 := hKe
  have hem := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (he.memLp k).1)
    he.memLp_lim.1 he.tendsto
  have he0K : ∀ᵐ y', e₀ y' ∈ Ke4 :=
    ae_mem_of_tendstoInMeasure hKe4.isClosed hem fun k => Eventually.of_forall fun y' => hval k _
  -- the two smallness conditions
  have hev1 : ∀ᶠ k in atTop, ∫ y', ‖G k y' - G₀ y'‖ ≤ ε / 8 :=
    (tendsto_order.1 (integral_norm_tendsto_zero hG)).2 (ε / 8) (by positivity) |>.mono
      fun k hk => hk.le
  have hev2 : ∀ᶠ k in atTop, 3 * (n k : ℝ)⁻¹ * I0 ≤ ε / 2 := by
    have h3 : Tendsto (fun k => 3 * (n k : ℝ)⁻¹ * I0) atTop (𝓝 0) := by
      simpa using (hρ.const_mul 3).mul_const I0
    exact (tendsto_order.1 h3).2 (ε / 2) (by positivity) |>.mono fun k hk => hk.le
  filter_upwards [hev1, hev2] with k hk1 hk2
  intro τ
  have hτ := τ.norm_nonneg
  -- the literal variation as an integral
  have hdet : ∀ x, 0 < (coframe (y k) x).det := fun x => hKdet _ (hval k x)
  have hlog : ∀ x μ ν, ‖cartanPlaquette (n k : ℝ)⁻¹ (coframe (y k)) x μ ν - 1‖ < 1 :=
    cartan_log_lt (hNpos k) hc (coframe (y k)) (hmar k)
  have hreg : ∀ x, GravRegular ((n k : ℝ)⁻¹,
      (stencil (n k : ℝ)⁻¹ (shiftVec (n k)) x (coframeM (y k)) : T4)) :=
    fun x => gravRegular_stencil (hNpos k) hKdet hc (coframeM (y k)) (hval k) (hmar k) x
  rw [gravVariation_eq D (y k) τ hdet hlog hreg]
  -- the continuum variation as an integral of the limit covector
  set T0 : UnitAddTorus (Fin 4) → T4 := fun y' => limitJet (τ.f y') (fun lam => τ.df lam y')
  have hcont : contGravVariation D.κ D.Λ e₀ p τ = ∫ y', G₀ y' (T0 y') := by
    refine integral_congr_ae ?_
    filter_upwards [he0K] with y' hy'
    exact (limitCov_apply D.κ D.Λ (hKdet _ hy').ne' (fun lam => p lam y') (τ.f y')
      (fun lam => τ.df lam y')).symm
  rw [hcont]
  set Tk := pc (testJet (n k : ℝ)⁻¹ (sampleTest (n k) τ))
  have hTk : ∀ y', ‖Tk y' - T0 y'‖ ≤ 3 * (n k : ℝ)⁻¹ * τ.norm := fun y' =>
    norm_pc_testJet_sub_le τ y'
  have hT0 : ∀ y', ‖T0 y'‖ ≤ τ.norm := norm_limitJet_le τ
  have hTkb : ∀ y', ‖Tk y'‖ ≤ 4 * τ.norm := fun y' => by
    have h1 := norm_le_insert' (Tk y') (T0 y')
    have h3 : 3 * (n k : ℝ)⁻¹ * τ.norm ≤ 3 * τ.norm := by
      have := hN1 k; nlinarith
    linarith [hTk y', hT0 y']
  -- integrability
  have hIk : Integrable (fun y' => G k y' (Tk y')) := by
    have : (fun y' => G k y' (Tk y')) = pc (fun x => gridCov D.κ D.Λ (n k : ℝ)⁻¹
        (coframeM (y k)) x (testJet (n k : ℝ)⁻¹ (sampleTest (n k) τ) x)) := rfl
    rw [this]
    exact memLp_one_iff_integrable.1 (NativeYMIdentification.memLp_pc_gen _ 1)
  have hT0c : Continuous T0 := by
    refine continuous_prodMk.2 ⟨continuous_pi fun _ => (τ.f).continuous,
      continuous_pi fun sl => (τ.df sl.2).continuous⟩
  have hI0' : Integrable (fun y' => G₀ y' (T0 y')) := by
    refine Integrable.mono' (hG0int.norm.mul_const τ.norm)
      (LpProductContinuity.aestronglyMeasurable_apply hG.memLp_lim.1
        hT0c.aestronglyMeasurable) (Eventually.of_forall fun y' => ?_)
    exact ((G₀ y').le_opNorm _).trans (mul_le_mul_of_nonneg_left (hT0 y') (norm_nonneg _))
  have hdiffint : Integrable (fun y' => ‖G k y' - G₀ y'‖) :=
    (memLp_one_iff_integrable.1 ((hG.memLp k).sub hG.memLp_lim)).norm
  -- the estimate
  rw [← integral_sub hIk hI0']
  refine (abs_integral_le_integral_abs).trans ?_
  have hpt : ∀ y', |G k y' (Tk y') - G₀ y' (T0 y')| ≤
      ‖G k y' - G₀ y'‖ * (4 * τ.norm) + ‖G₀ y'‖ * (3 * (n k : ℝ)⁻¹ * τ.norm) := by
    intro y'
    have e : G k y' (Tk y') - G₀ y' (T0 y') = (G k y' - G₀ y') (Tk y') + G₀ y' (Tk y' - T0 y') := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]; ring
    rw [e, ← Real.norm_eq_abs]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact ((G k y' - G₀ y').le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hTkb y') (norm_nonneg _))
    · exact ((G₀ y').le_opNorm _).trans (mul_le_mul_of_nonneg_left (hTk y') (norm_nonneg _))
  calc ∫ y', |G k y' (Tk y') - G₀ y' (T0 y')|
      ≤ ∫ y', (‖G k y' - G₀ y'‖ * (4 * τ.norm) + ‖G₀ y'‖ * (3 * (n k : ℝ)⁻¹ * τ.norm)) :=
        integral_mono (hIk.sub hI0').abs
          ((hdiffint.mul_const _).add (hG0int.norm.mul_const _)) hpt
    _ = (∫ y', ‖G k y' - G₀ y'‖) * (4 * τ.norm) + 3 * (n k : ℝ)⁻¹ * I0 * τ.norm := by
        rw [integral_add (hdiffint.mul_const _) (hG0int.norm.mul_const _), integral_mul_const,
          integral_mul_const]
        ring
    _ ≤ ε / 8 * (4 * τ.norm) + ε / 2 * τ.norm := by
        gcongr
    _ = ε * τ.norm := by ring

/-- **The gravitational Euler equation from vanishing finite stationarity** (gravity sector of
the last assertion of `thm:native-firstvariation-no-band`, via `thm:abstract-closure`): under the
hypotheses of `native_gravity_firstjet`, if the literal gravitational first variation tends to zero
on the `C²` unit test family, the limit coframe is a distributional critical point of the
first-order Palatini action: `D𝒮_{g,θ}(e)[k] = 0` for every test `k`. -/
theorem native_gravity_euler (D : Data 𝔄 𝓗 𝓢) (hn : Tendsto n atTop atTop)
    (y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢) (e₀ : UnitAddTorus (Fin 4) → M4)
    (p : Fin 4 → UnitAddTorus (Fin 4) → M4) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, 0 < M.det) (hval : ∀ k x, coframe (y k) x ∈ Ke) {c : ℝ}
    (hc : c ≤ 1 / 64)
    (hmar : ∀ k x μ, (n k : ℝ)⁻¹ * ‖asM4 (omegaLink (n k : ℝ)⁻¹ (coframe (y k)) x μ)‖ ≤ c)
    (he : LpTendsto MeasureTheory.volume 2 (fun k => pc (coframeM (y k))) e₀)
    (hp : ∀ μ, LpTendsto MeasureTheory.volume 2
      (fun k => pc (fwdDiff (n k : ℝ)⁻¹ μ (coframeM (y k)))) (p μ))
    (hstat : ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : C2Test M4,
      |gravVariation D (n k) (y k) τ| ≤ ε * τ.norm) (τ : C2Test M4) :
    contGravVariation D.κ D.Λ e₀ p τ = 0 := by
  have hτ := τ.norm_nonneg
  refine abs_eq_zero.1 (le_antisymm ?_ (abs_nonneg _))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε' : 0 < ε / (2 * (τ.norm + 1)) := by positivity
  obtain ⟨k, hk1, hk2⟩ := ((native_gravity_firstjet D hn y e₀ p hKe hKdet hval hc hmar he hp _
    hε').and (hstat _ hε')).exists
  have h1 := hk1 τ
  have h2 := hk2 τ
  have h3 : |contGravVariation D.κ D.Λ e₀ p τ| ≤
      |gravVariation D (n k) (y k) τ - contGravVariation D.κ D.Λ e₀ p τ| +
        |gravVariation D (n k) (y k) τ| := by
    have := abs_sub_abs_le_abs_sub (contGravVariation D.κ D.Λ e₀ p τ)
      (gravVariation D (n k) (y k) τ)
    rw [abs_sub_comm (contGravVariation D.κ D.Λ e₀ p τ)] at this
    linarith [abs_nonneg (gravVariation D (n k) (y k) τ)]
  have h4 : ε / (2 * (τ.norm + 1)) * τ.norm ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Main

/-! ### Consistency relative to reconstructed coframes (second clause) -/

section Reconstructed

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

local instance fact_one_le_two_rc : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

set_option maxHeartbeats 1000000 in
/-- **Continuity of the continuum first variation** in the reduced first-jet topology (the
gravity sector of `prop:reduced-continuity`, used for the second clause): if continuum coframes
`f_k` with values in the compact chart and first jets `g_k` converge strongly in `L²` to `(e, p)`,
the limit covectors converge strongly in `L¹`. -/
theorem lpTendsto_limitCov (κ Λ : ℝ) {f : ℕ → UnitAddTorus (Fin 4) → M4}
    {e₀ : UnitAddTorus (Fin 4) → M4} {g : ℕ → Fin 4 → UnitAddTorus (Fin 4) → M4}
    {p : Fin 4 → UnitAddTorus (Fin 4) → M4} {Ke : Set Mat} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, 0 < M.det) (hfK : ∀ k y', (f k y' : Mat) ∈ Ke)
    (hf : LpTendsto MeasureTheory.volume 2 f e₀)
    (hg : ∀ μ, LpTendsto MeasureTheory.volume 2 (fun k => g k μ) (p μ)) :
    LpTendsto MeasureTheory.volume 1 (fun k y' => limitCov κ Λ (f k y') (fun μ => g k μ y'))
      (fun y' => limitCov κ Λ (e₀ y') (fun μ => p μ y')) := by
  let Ke4 : Set M4 := Ke
  have hKe4 : IsCompact Ke4 := hKe
  set KV : Set V4 := Set.univ.pi fun _ => Ke4
  set KQ : Set Q4 := Set.univ.pi fun _ => Ke4
  have hKV : IsCompact KV := isCompact_univ_pi fun _ => hKe4
  have hKQ : IsCompact KQ := isCompact_univ_pi fun _ => hKe4
  have hv2 : LpTendsto MeasureTheory.volume 2 (fun k y' (_ : Shift) => f k y') (fun y' _ => e₀ y') :=
    LpTendsto.pi fun _ => hf
  have hw2 : LpTendsto MeasureTheory.volume 2 (fun k y' (_ : Shift × Fin 4) => f k y')
      (fun y' _ => e₀ y') := LpTendsto.pi fun _ => hf
  have hq2 : LpTendsto MeasureTheory.volume 2 (fun k y' (sl : Shift × Fin 4) => g k sl.2 y')
      (fun y' sl => p sl.2 y') := LpTendsto.pi fun sl => hg sl.2
  have hvm := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (hv2.memLp k).1)
    hv2.memLp_lim.1 hv2.tendsto
  have hwm := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (hw2.memLp k).1)
    hw2.memLp_lim.1 hw2.tendsto
  have hfm := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (hf.memLp k).1)
    hf.memLp_lim.1 hf.tendsto
  have hvK : ∀ k y', (fun (_ : Shift) => f k y') ∈ KV := fun k y' s _ => hfK k y'
  have hwK : ∀ k y', (fun (_ : Shift × Fin 4) => f k y') ∈ KQ := fun k y' sl _ => hfK k y'
  have hv0K : ∀ᵐ y', (fun _ : Shift => e₀ y') ∈ KV :=
    ae_mem_of_tendstoInMeasure hKV.isClosed hvm fun k => Eventually.of_forall (hvK k)
  have hw0K : ∀ᵐ y', (fun _ : Shift × Fin 4 => e₀ y') ∈ KQ :=
    ae_mem_of_tendstoInMeasure hKQ.isClosed hwm fun k => Eventually.of_forall (hwK k)
  have he0K : ∀ᵐ y', e₀ y' ∈ Ke4 :=
    ae_mem_of_tendstoInMeasure hKe4.isClosed hfm fun k => Eventually.of_forall (hfK k)
  have hL := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn hKV
    continuous_Lmap.continuousOn (fun k => Eventually.of_forall (hvK k)) hv0K hvm
  have hB := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn hKQ
    continuous_Bmap.continuousOn (fun k => Eventually.of_forall (hwK k)) hw0K hwm
  have hAc : ContinuousOn (fun p : V4 × Q4 => Amap p.1 p.2) (KV ×ˢ KQ) :=
    continuous_Amap.continuousOn
  have hA := LpProductContinuity.tendstoInMeasure_comp_of_continuousOn
    (W := Q4 →L[ℝ] T4 →L[ℝ] Q4) (Φ := fun p : V4 × Q4 => Amap p.1 p.2) (hKV.prod hKQ) hAc
    (fun k => Eventually.of_forall fun y' => ⟨hvK k y', hwK k y'⟩)
    (by filter_upwards [hv0K, hw0K] with y' h1 h2 using ⟨h1, h2⟩)
    (TendstoInMeasure.prodMk hvm hwm)
  obtain ⟨CL, hCL⟩ := IsCompact.exists_bound_of_continuousOn (E := T4 →L[ℝ] V4) hKV
    continuous_Lmap.continuousOn
  obtain ⟨CB, hCB⟩ := IsCompact.exists_bound_of_continuousOn (E := T4 →L[ℝ] Q4) hKQ
    continuous_Bmap.continuousOn
  obtain ⟨CA, hCA⟩ := IsCompact.exists_bound_of_continuousOn (E := Q4 →L[ℝ] T4 →L[ℝ] Q4)
    (hKV.prod hKQ) hAc
  set C := max CL (max CB CA)
  have hmem : ∀ k y', normJet 0 (fun (_ : Shift) => f k y') (fun sl : Shift × Fin 4 => g k sl.2 y')
      ∈ (gravChart Ke 0 0 : Set (ℝ × T4)) := fun k y' => normJet_zero_mem (hfK k y') _
  have hKc : IsCompact (gravChart Ke 0 0 : Set (ℝ × T4)) := isCompact_gravChart hKe hKdet 0 0
  have hC1 : ∀ z ∈ (gravChart Ke 0 0 : Set (ℝ × T4)), ContDiffAt ℝ 1 (Γg κ) z :=
    fun z hz => contDiffAt_of_mem_gravChart κ hKdet (by norm_num) hz
  have hcv : Continuous fun M : M4 => (fun (_ : Shift) => M : V4) := continuous_pi fun _ => continuous_id
  have hcw : Continuous fun M : M4 => (fun (_ : Shift × Fin 4) => M : Q4) :=
    continuous_pi fun _ => continuous_id
  have hfm' : ∀ k, AEStronglyMeasurable (f k) MeasureTheory.volume := fun k => (hf.memLp k).1
  have hvm' : ∀ k, AEStronglyMeasurable (fun y' (_ : Shift) => f k y') MeasureTheory.volume :=
    fun k => hcv.comp_aestronglyMeasurable (hfm' k)
  have hLm : ∀ k, AEStronglyMeasurable (fun y' => Lmap (fun (_ : Shift) => f k y'))
      MeasureTheory.volume := fun k => (continuous_Lmap.comp hcv).comp_aestronglyMeasurable (hfm' k)
  have hBm : ∀ k, AEStronglyMeasurable (fun y' => Bmap (fun (_ : Shift × Fin 4) => f k y'))
      MeasureTheory.volume := fun k => (continuous_Bmap.comp hcw).comp_aestronglyMeasurable (hfm' k)
  have hAm : ∀ k, AEStronglyMeasurable
      (fun y' => Amap (fun (_ : Shift) => f k y') (fun (_ : Shift × Fin 4) => f k y'))
      MeasureTheory.volume := fun k =>
    (continuous_Amap.comp (hcv.prodMk hcw)).comp_aestronglyMeasurable (hfm' k)
  have hLC : ∀ k y', ‖Lmap (fun (_ : Shift) => f k y')‖ ≤ C :=
    fun k y' => (hCL _ (hvK k y')).trans (le_max_left _ _)
  have hBC : ∀ k y', ‖Bmap (fun (_ : Shift × Fin 4) => f k y')‖ ≤ C :=
    fun k y' => (hCB _ (hwK k y')).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hAC : ∀ k y', ‖Amap (fun (_ : Shift) => f k y') (fun (_ : Shift × Fin 4) => f k y')‖ ≤ C :=
    fun k y' => (hCA (_, _) ⟨hvK k y', hwK k y'⟩).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hvar := lpTendsto_homogeneous_variation (μ := MeasureTheory.volume) (V := V4) (Q := Q4)
    (T := T4) (Γ := Γg κ) (Γg_scale κ) hKc hC1 (ρ := fun _ => (0 : ℝ)) tendsto_const_nhds hvm'
    hvm hq2 hmem hLm hL hLC hBm hB hBC hAm hA hAC
  have hKdet4 : ∀ M ∈ Ke4, 0 < Matrix.det (show Mat from M) := hKdet
  have hvol := (LpProductContinuity.LpTendsto.comp_of_continuousOn (p := 1) ENNReal.one_ne_top
    (W := T4 →L[ℝ] ℝ) (Φ := volCov) hKe4 (continuousOn_volCov hKdet4)
    (fun k => Eventually.of_forall (hfK k)) he0K hfm
    (fun k => aestronglyMeasurable_comp_continuousOn hKe4.isClosed (continuousOn_volCov hKdet4)
      (hfm' k) (Eventually.of_forall (hfK k)))).2
  have hsum := hvar.sub (hvol.const_smul (Λ / κ))
  exact hsum.congr (fun k => Eventually.of_forall fun y' => rfl) (Eventually.of_forall fun y' => rfl)

theorem integrable_cov_apply {G : UnitAddTorus (Fin 4) → T4 →L[ℝ] ℝ}
    (hG : Integrable G MeasureTheory.volume) (τ : C2Test M4) :
    Integrable (fun y' => G y' (limitJet (τ.f y') (fun lam => τ.df lam y'))) MeasureTheory.volume := by
  have hT0c : Continuous fun y' => limitJet (τ.f y') (fun lam => τ.df lam y') :=
    continuous_prodMk.2 ⟨continuous_pi fun _ => (τ.f).continuous,
      continuous_pi fun sl => (τ.df sl.2).continuous⟩
  refine Integrable.mono' (hG.norm.mul_const τ.norm)
    (LpProductContinuity.aestronglyMeasurable_apply hG.1 hT0c.aestronglyMeasurable)
    (Eventually.of_forall fun y' => ?_)
  exact ((G y').le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_limitJet_le τ y')
    (norm_nonneg _))

/-- **Second clause of `prop:native-gravity-firstjet`**: if, in addition, continuum (e.g. the
complete unfiltered trigonometric) reconstructions `f_k` of the coframes stay in the same compact
chart and converge with their first jets `g_k` strongly in `L²` to the same `(e, ∂e)` (strong `H¹`
convergence), then the consistency error **relative to the reconstructed coframes** tends to zero
uniformly on the `C²` unit ball:
`|D S_{g,h}^{loc}(e_h)[𝓘_h k] - D𝒮_{g,θ}(f_k)[k]| ≤ ε ‖k‖_{C²}` eventually. -/
theorem native_gravity_firstjet_reconstructed (D : Data 𝔄 𝓗 𝓢) (hn : Tendsto n atTop atTop)
    (y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢) (e₀ : UnitAddTorus (Fin 4) → M4)
    (p : Fin 4 → UnitAddTorus (Fin 4) → M4) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, 0 < M.det) (hval : ∀ k x, coframe (y k) x ∈ Ke) {c : ℝ}
    (hc : c ≤ 1 / 64)
    (hmar : ∀ k x μ, (n k : ℝ)⁻¹ * ‖asM4 (omegaLink (n k : ℝ)⁻¹ (coframe (y k)) x μ)‖ ≤ c)
    (he : LpTendsto MeasureTheory.volume 2 (fun k => pc (coframeM (y k))) e₀)
    (hp : ∀ μ, LpTendsto MeasureTheory.volume 2
      (fun k => pc (fwdDiff (n k : ℝ)⁻¹ μ (coframeM (y k)))) (p μ))
    (f : ℕ → UnitAddTorus (Fin 4) → M4) (g : ℕ → Fin 4 → UnitAddTorus (Fin 4) → M4)
    (hfK : ∀ k y', (f k y' : Mat) ∈ Ke) (hf : LpTendsto MeasureTheory.volume 2 f e₀)
    (hg : ∀ μ, LpTendsto MeasureTheory.volume 2 (fun k => g k μ) (p μ)) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : C2Test M4,
      |gravVariation D (n k) (y k) τ - contGravVariation D.κ D.Λ (f k) (g k) τ| ≤ ε * τ.norm := by
  intro ε hε
  have h1 := native_gravity_firstjet D hn y e₀ p hKe hKdet hval hc hmar he hp (ε / 2)
    (by positivity)
  have hL := lpTendsto_limitCov D.κ D.Λ hKe hKdet hfK hf hg
  have hev : ∀ᶠ k in atTop, ∫ y', ‖limitCov D.κ D.Λ (f k y') (fun μ => g k μ y') -
      limitCov D.κ D.Λ (e₀ y') (fun μ => p μ y')‖ ≤ ε / 2 :=
    (tendsto_order.1 (integral_norm_tendsto_zero hL)).2 (ε / 2) (by positivity) |>.mono
      fun k hk => hk.le
  let Ke4 : Set M4 := Ke
  have hKe4 : IsCompact Ke4 := hKe
  have hfm := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (hf.memLp k).1)
    hf.memLp_lim.1 hf.tendsto
  have he0K : ∀ᵐ y', e₀ y' ∈ Ke4 :=
    ae_mem_of_tendstoInMeasure hKe4.isClosed hfm fun k => Eventually.of_forall (hfK k)
  filter_upwards [h1, hev] with k hk1 hk2
  intro τ
  have hτ := τ.norm_nonneg
  set T0 : UnitAddTorus (Fin 4) → T4 := fun y' => limitJet (τ.f y') (fun lam => τ.df lam y')
  have hck : contGravVariation D.κ D.Λ (f k) (g k) τ =
      ∫ y', limitCov D.κ D.Λ (f k y') (fun μ => g k μ y') (T0 y') :=
    integral_congr_ae (Eventually.of_forall fun y' => (limitCov_apply D.κ D.Λ
      (hKdet _ (hfK k y')).ne' (fun μ => g k μ y') (τ.f y') (fun lam => τ.df lam y')).symm)
  have hc0 : contGravVariation D.κ D.Λ e₀ p τ =
      ∫ y', limitCov D.κ D.Λ (e₀ y') (fun μ => p μ y') (T0 y') := by
    refine integral_congr_ae ?_
    filter_upwards [he0K] with y' hy'
    exact (limitCov_apply D.κ D.Λ (hKdet _ hy').ne' (fun μ => p μ y') (τ.f y')
      (fun lam => τ.df lam y')).symm
  have hIk := integrable_cov_apply (memLp_one_iff_integrable.1 (hL.memLp k)) τ
  have hI0 := integrable_cov_apply (memLp_one_iff_integrable.1 hL.memLp_lim) τ
  have hdiff : |contGravVariation D.κ D.Λ e₀ p τ - contGravVariation D.κ D.Λ (f k) (g k) τ| ≤
      ε / 2 * τ.norm := by
    rw [hck, hc0, ← integral_sub hI0 hIk]
    refine (abs_integral_le_integral_abs).trans ?_
    have hint : Integrable (fun y' => ‖limitCov D.κ D.Λ (f k y') (fun μ => g k μ y') -
        limitCov D.κ D.Λ (e₀ y') (fun μ => p μ y')‖) :=
      (memLp_one_iff_integrable.1 ((hL.memLp k).sub hL.memLp_lim)).norm
    calc ∫ y', |limitCov D.κ D.Λ (e₀ y') (fun μ => p μ y') (T0 y') -
          limitCov D.κ D.Λ (f k y') (fun μ => g k μ y') (T0 y')|
        ≤ ∫ y', ‖limitCov D.κ D.Λ (f k y') (fun μ => g k μ y') -
            limitCov D.κ D.Λ (e₀ y') (fun μ => p μ y')‖ * τ.norm := by
          refine integral_mono (hI0.sub hIk).abs (hint.mul_const _) fun y' => ?_
          rw [← Real.norm_eq_abs, ← ContinuousLinearMap.sub_apply, norm_sub_rev]
          exact ((_ : T4 →L[ℝ] ℝ).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (norm_limitJet_le τ y') (norm_nonneg _))
      _ = (∫ y', ‖limitCov D.κ D.Λ (f k y') (fun μ => g k μ y') -
            limitCov D.κ D.Λ (e₀ y') (fun μ => p μ y')‖) * τ.norm := integral_mul_const _ _
      _ ≤ ε / 2 * τ.norm := mul_le_mul_of_nonneg_right hk2 hτ
  calc |gravVariation D (n k) (y k) τ - contGravVariation D.κ D.Λ (f k) (g k) τ|
      ≤ |gravVariation D (n k) (y k) τ - contGravVariation D.κ D.Λ e₀ p τ| +
        |contGravVariation D.κ D.Λ e₀ p τ - contGravVariation D.κ D.Λ (f k) (g k) τ| :=
          abs_sub_le _ _ _
    _ ≤ ε / 2 * τ.norm + ε / 2 * τ.norm := add_le_add (hk1 τ) hdiff
    _ = ε * τ.norm := by ring

end Reconstructed

/-! ### The first-jet limit is the weak derivative (`p_μ = ∂_μ e`) -/

section WeakDerivative

open TorusPiecewiseConstantTranslation (pc pcLp)

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- The complexified `(a, b)` entry of a real `4 × 4` array. -/
def entryC (a b : Fin 4) : M4 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) a))

theorem norm_pcLp_sub_toLp {u : ∀ k, Grid (n k) → ℂ} {g : UnitAddTorus (Fin 4) → ℂ}
    (h : LpTendsto MeasureTheory.volume 2 (fun k => pc (u k)) g) :
    Tendsto (fun k => ‖pcLp (u k) - h.memLp_lim.toLp g‖) atTop (𝓝 0) := by
  have e : ∀ k, ‖pcLp (u k) - h.memLp_lim.toLp g‖ =
      (eLpNorm (pc (u k) - g) 2 MeasureTheory.volume).toReal := by
    intro k
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (pcLp (u k)) (h.memLp_lim.toLp g),
      (TorusPiecewiseConstantTranslation.memLp_pc (u k)).coeFn_toLp,
      h.memLp_lim.coeFn_toLp] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h3, Pi.sub_apply, ← h2]
    rfl
  simp only [e]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.tendsto
  rwa [ENNReal.toReal_zero] at this

/-- **`eq:native-coframe-firstjet` identifies the limit jet**: if `R^0 e_h → e` and
`R^0 D⁺_μ e_h → p_μ` strongly in `L²`, then every entry of `p_μ` is the weak derivative `∂_μ` of
the corresponding entry of `e` (`lem:native-reconstruction-identification`). -/
theorem firstJet_eq_weakDeriv (hn : Tendsto n atTop atTop) (e : ∀ k, Grid (n k) → M4)
    (e₀ : UnitAddTorus (Fin 4) → M4) (p : Fin 4 → UnitAddTorus (Fin 4) → M4)
    (he : LpTendsto MeasureTheory.volume 2 (fun k => pc (e k)) e₀)
    (hp : ∀ μ, LpTendsto MeasureTheory.volume 2 (fun k => pc (fwdDiff (n k : ℝ)⁻¹ μ (e k))) (p μ))
    (a b μ : Fin 4) :
    TorusSobolev.weakDeriv μ ((he.clm (entryC a b)).memLp_lim.toLp (fun y => entryC a b (e₀ y))) =
      ((hp μ).clm (entryC a b)).memLp_lim.toLp (fun y => entryC a b (p μ y)) := by
  have hu := norm_pcLp_sub_toLp (n := n) (u := fun k x => entryC a b (e k x)) (he.clm (entryC a b))
  have hv : ∀ ν, Tendsto (fun k => ‖pcLp (TorusTrigReconstruction.Dp ν
      (fun x => entryC a b (e k x))) - ((hp ν).clm (entryC a b)).memLp_lim.toLp
        (fun y => entryC a b (p ν y))‖) atTop (𝓝 0) := by
    intro ν
    have h := norm_pcLp_sub_toLp (n := n) (u := fun k x => entryC a b (fwdDiff (n k : ℝ)⁻¹ ν (e k) x))
      ((hp ν).clm (entryC a b))
    refine h.congr fun k => ?_
    congr 3
    funext x
    rw [TorusTrigReconstruction.Dp_apply]
    simp only [entryC, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, ShiftedJetAction.fwdDiff,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, inv_inv, unitVec]
    push_cast
    ring
  exact TorusTrigReconstruction.weakDeriv_eq_of_tendsto hn hu hv μ

end WeakDerivative

/-! ### `contGravVariation` is the derivative of the first-order Palatini action -/

section ActionDerivative

/-- The first-order Palatini action `∫ L^{(1)}(e, p)` of a continuum first jet. -/
def palatiniAction (κ Λ : ℝ) (e₀ : UnitAddTorus (Fin 4) → M4)
    (p : Fin 4 → UnitAddTorus (Fin 4) → M4) : ℝ :=
  ∫ y, palatiniL κ Λ (e₀ y, fun lam => p lam y)

theorem hasFDerivAt_palatiniL (κ Λ : ℝ) {e : M4} (he : Matrix.det (show Mat from e) ≠ 0)
    (p : Fin 4 → M4) :
    HasFDerivAt (palatiniL κ Λ) ((fderiv ℝ (Γg κ) ((0 : ℝ), constJetL (e, p))).comp
      ((0 : M4 × (Fin 4 → M4) →L[ℝ] ℝ).prod constJetL) -
      (Λ / κ) • (fderiv ℝ volM e).comp (ContinuousLinearMap.fst ℝ M4 (Fin 4 → M4))) (e, p) := by
  have hΓ : DifferentiableAt ℝ (Γg κ) ((0 : ℝ), constJetL (e, p)) :=
    (contDiffAt_Γg κ (gravRegular_constJet he p)).differentiableAt (by simp)
  have hv : DifferentiableAt ℝ volM e := (contDiffAt_volM he).differentiableAt (by simp)
  have hin : HasFDerivAt (fun w : M4 × (Fin 4 → M4) => ((0 : ℝ), constJetL w))
      ((0 : M4 × (Fin 4 → M4) →L[ℝ] ℝ).prod constJetL) (e, p) :=
    (hasFDerivAt_const (0 : ℝ) (e, p)).prodMk constJetL.hasFDerivAt
  exact (hΓ.hasFDerivAt.comp (e, p) hin).sub
    ((hv.hasFDerivAt.comp (e, p) (hasFDerivAt_fst (𝕜 := ℝ) (p := (e, p)))).const_mul (Λ / κ))

/-- The pointwise first variation along an arbitrary direction, in jet form. -/
theorem fderiv_palatiniL_apply (κ Λ : ℝ) {e : M4} (he : Matrix.det (show Mat from e) ≠ 0)
    (p : Fin 4 → M4) (w : M4 × (Fin 4 → M4)) :
    fderiv ℝ (palatiniL κ Λ) (e, p) w =
      jetDeriv (Γg κ) 0 (constJetL (e, p)) (constJetL w) - Λ / κ * fderiv ℝ volM e w.1 := by
  have hΓ : DifferentiableAt ℝ (Γg κ) ((0 : ℝ), constJetL (e, p)) :=
    (contDiffAt_Γg κ (gravRegular_constJet he p)).differentiableAt (by simp)
  rw [(hasFDerivAt_palatiniL κ Λ he p).fderiv,
    jetDeriv_eq (z := ((0 : ℝ), constJetL (e, p))) hΓ]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', smul_eq_mul, ContinuousLinearMap.inr_apply]

/-- **Degree-two growth of the jet derivative at the mesh origin**: on a compact chart, the jet
derivative at `(0, v, q)` is bounded by `M((1+‖q‖)²‖v̇‖ + (1+‖q‖)‖q̇‖)`. -/
theorem exists_jetDeriv_bound (κ : ℝ) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, 0 < M.det) :
    ∃ M, ∀ v : V4, ∀ q : Q4, (∀ s, (v s : Mat) ∈ Ke) → ∀ w : T4,
      |jetDeriv (Γg κ) 0 (v, q) w| ≤ M * ((1 + ‖q‖) ^ 2 * ‖w.1‖ + (1 + ‖q‖) * ‖w.2‖) := by
  have hKc : IsCompact (gravChart Ke 0 0 : Set (ℝ × T4)) := isCompact_gravChart hKe hKdet 0 0
  have hC1 : ∀ z ∈ (gravChart Ke 0 0 : Set (ℝ × T4)), ContDiffAt ℝ 1 (Γg κ) z :=
    fun z hz => contDiffAt_of_mem_gravChart κ hKdet (by norm_num) hz
  have hcont : ContinuousOn (fun z : ℝ × T4 => jetDeriv (Γg κ) z.1 z.2)
      (gravChart Ke 0 0 : Set (ℝ × T4)) := continuousOn_jetDeriv hC1
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (f := fun z : ℝ × T4 => jetDeriv (Γg κ) z.1 z.2) hKc hcont
  refine ⟨max M 0, fun v q hv w => ?_⟩
  set K := 1 + ‖q‖ with hK
  have hK0 : 0 < K := one_add_norm_pos q
  have hmem : ((0 : ℝ), (v, K⁻¹ • q)) ∈ (gravChart Ke 0 0 : Set (ℝ × T4)) := by
    exact chart_zero_mem hv (K⁻¹ • q) (HomogeneousJetVariation.norm_normalize_le q)
  have hd : DifferentiableAt ℝ (fun w' => Γg κ (0 * K, w')) (rescale K (v, q)) := by
    have := (hC1 _ hmem).differentiableAt (by norm_num)
    simpa using differentiableAt_slice (z := ((0 : ℝ), (v, K⁻¹ • q))) this
  have hsc := jetDeriv_scale (Γ := Γg κ) (ρ := 0) (K := K)
    (fun v q => Γg_scale κ 0 K v q hK0) (v, q) hd
  rw [hsc]
  have hbd : ‖jetDeriv (Γg κ) (0 * K) (rescale K (v, q))‖ ≤ max M 0 := by
    have := hM _ hmem
    simp only [zero_mul] at this ⊢
    exact this.trans (le_max_left _ _)
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (by positivity)]
  have hw : ‖rescale K w‖ ≤ ‖w.1‖ + K⁻¹ * ‖w.2‖ := by
    rw [rescale_apply, Prod.norm_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hK0.le)]
    exact max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (norm_nonneg _))
  calc K ^ 2 * |jetDeriv (Γg κ) (0 * K) (rescale K (v, q)) (rescale K w)|
      ≤ K ^ 2 * (max M 0 * (‖w.1‖ + K⁻¹ * ‖w.2‖)) := by
        gcongr
        exact (Real.norm_eq_abs _ ▸ (ContinuousLinearMap.le_opNorm _ _)).trans
          (mul_le_mul hbd hw (norm_nonneg _) (le_max_right _ _))
    _ = max M 0 * (K ^ 2 * ‖w.1‖ + K * ‖w.2‖) := by field_simp

theorem aestronglyMeasurable_pi_fin {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Fin 4 → X → E}
    (hg : ∀ i, AEStronglyMeasurable (g i) μ) : AEStronglyMeasurable (fun y i => g i y) μ := by
  have e : (fun y i => g i y) = fun y => ∑ i, Pi.single i (g i y) := by
    funext y; exact (Finset.univ_sum_single _).symm
  rw [e]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => E) i).continuous.comp_aestronglyMeasurable (hg i)

theorem exists_Γ_bound (κ : ℝ) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, 0 < M.det) :
    ∃ M, ∀ v : V4, ∀ q : Q4, (∀ s, (v s : Mat) ∈ Ke) → |Γg κ (0, (v, q))| ≤ M * (1 + ‖q‖) ^ 2 := by
  have hKc : IsCompact (gravChart Ke 0 0 : Set (ℝ × T4)) := isCompact_gravChart hKe hKdet 0 0
  have hC1 : ∀ z ∈ (gravChart Ke 0 0 : Set (ℝ × T4)), ContDiffAt ℝ 1 (Γg κ) z :=
    fun z hz => contDiffAt_of_mem_gravChart κ hKdet (by norm_num) hz
  have hcont : ContinuousOn (Γg κ) (gravChart Ke 0 0 : Set (ℝ × T4)) := fun z hz =>
    (hC1 z hz).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn (f := Γg κ) hKc hcont
  refine ⟨max M 0, fun v q hv => ?_⟩
  have hK0 : 0 < 1 + ‖q‖ := one_add_norm_pos q
  rw [Γg_scale κ 0 (1 + ‖q‖) v q hK0, zero_mul, abs_mul, abs_of_nonneg (by positivity), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact (Real.norm_eq_abs _ ▸ hM _ (chart_zero_mem hv _
    (HomogeneousJetVariation.norm_normalize_le q))).trans (le_max_left _ _)

theorem contDiffAt_palatiniL (κ Λ : ℝ) {w : M4 × (Fin 4 → M4)}
    (hw : Matrix.det (show Mat from w.1) ≠ 0) : ContDiffAt ℝ ∞ (palatiniL κ Λ) w := by
  have hΓ : ContDiffAt ℝ ∞ (Γg κ) ((0 : ℝ), constJetL w) :=
    contDiffAt_Γg κ (gravRegular_constJet hw w.2)
  have h1 : ContDiffAt ℝ ∞ (fun w : M4 × (Fin 4 → M4) => ((0 : ℝ), constJetL w)) w :=
    contDiffAt_const.prodMk constJetL.contDiff.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun w : M4 × (Fin 4 → M4) => volM w.1) w :=
    (contDiffAt_volM hw).comp w contDiffAt_fst
  exact (hΓ.comp w h1).sub (contDiffAt_const.mul h2)

theorem norm_constJet_snd_le (w : M4 × (Fin 4 → M4)) : ‖(constJetL w).2‖ ≤ ‖w.2‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun sl => norm_le_pi_norm w.2 sl.2

theorem norm_constJet_fst_le (w : M4 × (Fin 4 → M4)) : ‖(constJetL w).1‖ ≤ ‖w.1‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => le_rfl

theorem continuous_liftedVar : Continuous fun z : M4 × (Fin 4 → M4) × M4 × (Fin 4 → M4) =>
    liftedVar z.1 z.2.1 z.2.2.1 z.2.2.2 := by
  refine continuous_prodMk.2 ⟨?_, continuous_pi fun lam => ?_⟩
  · exact (continuous_liftL.comp continuous_fst).clm_apply (continuous_fst.comp
      (continuous_snd.comp continuous_snd))
  · refine ((continuous_liftL.comp continuous_fst).clm_apply ((continuous_apply lam).comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd)))).add ?_
    have h1 : Continuous fun z : M4 × (Fin 4 → M4) × M4 × (Fin 4 → M4) => (z.1, z.1) :=
      continuous_fst.prodMk continuous_fst
    exact ((continuous_dqLiftL.comp h1).clm_apply ((continuous_apply lam).comp
      (continuous_fst.comp continuous_snd))).clm_apply
        (continuous_fst.comp (continuous_snd.comp continuous_snd))

/-- **`D𝒮_{g,θ}(e)[k]` is the derivative of the first-order Palatini action along the lift**:
for a coframe `e` with values a.e. in a compact oriented chart and an `L²` first jet `p`,
`d/dt ∫ L^{(1)}((e, p) + t (ė, ṗ))|_{t=0} = contGravVariation κ Λ e p k` (differentiation under the
integral, dominated by `C(1 + |p|)²`). -/
theorem hasDerivAt_palatiniAction (κ Λ : ℝ) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, 0 < M.det) {e₀ : UnitAddTorus (Fin 4) → M4}
    {p : Fin 4 → UnitAddTorus (Fin 4) → M4}
    (he₀m : AEStronglyMeasurable e₀ MeasureTheory.volume)
    (he₀K : ∀ᵐ y, (e₀ y : Mat) ∈ Ke) (hp : ∀ μ, MemLp (p μ) 2 MeasureTheory.volume)
    (τ : C2Test M4) :
    HasDerivAt (fun t : ℝ => ∫ y, palatiniL κ Λ ((e₀ y, fun lam => p lam y) +
        t • liftedVar (e₀ y) (fun lam => p lam y) (τ.f y) (fun lam => τ.df lam y)))
      (contGravVariation κ Λ e₀ p τ) 0 := by
  -- a compact thickening of the chart
  let Ke4 : Set M4 := Ke
  have hKe4 : IsCompact Ke4 := hKe
  have hdetc : Continuous fun M : M4 => Matrix.det (show Mat from M) := by
    show Continuous fun M : M4 => Matrix.det (show Mat from M)
    simp only [Matrix.det_apply']; fun_prop
  set U : Set M4 := {M | 0 < Matrix.det (show Mat from M)} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const hdetc
  obtain ⟨δ, hδ, hδU⟩ := hKe4.exists_cthickening_subset_open hUo fun M hM => hKdet M hM
  set Ke' : Set M4 := Metric.cthickening δ Ke4
  have hKe' : IsCompact Ke' := Metric.isCompact_of_isClosed_isBounded Metric.isClosed_cthickening
    hKe4.isBounded.cthickening
  let KeM : Set Mat := Ke'
  have hKeM : IsCompact KeM := hKe'
  have hKe'det : ∀ M ∈ Ke', 0 < Matrix.det (show Mat from M) := fun M hM => hδU hM
  have hKeMdet : ∀ M ∈ KeM, 0 < M.det := fun M hM => hδU hM
  -- constants
  obtain ⟨CL, hCL⟩ := IsCompact.exists_bound_of_continuousOn (f := liftL) hKe4
    continuous_liftL.continuousOn
  have hdqc : ContinuousOn (fun M : M4 => dqLiftL M M) Ke4 :=
    (continuous_dqLiftL.comp (continuous_id.prodMk continuous_id)).continuousOn
  obtain ⟨CQ, hCQ⟩ := IsCompact.exists_bound_of_continuousOn
    (E := M4 →L[ℝ] M4 →L[ℝ] M4) (f := fun M : M4 => dqLiftL M M) hKe4 hdqc
  have hvc : ContinuousOn (fun M : M4 => fderiv ℝ volM M) Ke' := fun M hM =>
    ((contDiffAt_volM (hKe'det M hM).ne').fderiv_right (m := 0)
      (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨CV, hCV⟩ := IsCompact.exists_bound_of_continuousOn hKe' hvc
  have hvolc : ContinuousOn volM Ke4 := fun M hM =>
    (contDiffAt_volM (hKdet M hM).ne').continuousAt.continuousWithinAt
  obtain ⟨CV0, hCV0⟩ := IsCompact.exists_bound_of_continuousOn hKe4 hvolc
  obtain ⟨MJ, hMJ⟩ := exists_jetDeriv_bound κ hKeM hKeMdet
  obtain ⟨MΓ, hMΓ⟩ := exists_Γ_bound κ hKe hKdet
  have hTn := τ.norm_nonneg
  set Tn := τ.norm
  set Ce := max CL 0 * Tn + 1
  have hCe : 0 < Ce := by positivity
  set Cq := max CQ 0 * Tn
  have hCq : 0 ≤ Cq := by positivity
  set ε := min 1 (δ / Ce)
  have hε : 0 < ε := lt_min one_pos (div_pos hδ hCe)
  -- the field and its lifted variation
  obtain ⟨P, hPdef⟩ : ∃ P : UnitAddTorus (Fin 4) → (Fin 4 → M4), P = fun y lam => p lam y :=
    ⟨_, rfl⟩
  have hPm : MemLp P 2 MeasureTheory.volume := by rw [hPdef]; exact memLp_pi_iff.2 hp
  obtain ⟨w0, hw0def⟩ : ∃ w0 : UnitAddTorus (Fin 4) → M4 × (Fin 4 → M4),
      w0 = fun y => (e₀ y, P y) := ⟨_, rfl⟩
  obtain ⟨wd, hwddef⟩ : ∃ wd : UnitAddTorus (Fin 4) → M4 × (Fin 4 → M4),
      wd = fun y => liftedVar (e₀ y) (P y) (τ.f y) (fun lam => τ.df lam y) := ⟨_, rfl⟩
  have hw0m : AEStronglyMeasurable w0 MeasureTheory.volume := by
    rw [hw0def]; exact he₀m.prodMk hPm.1
  have hdfc : Continuous fun y => fun lam => τ.df lam y :=
    continuous_pi fun lam => (τ.df lam).continuous
  have hLe : AEStronglyMeasurable (fun y => liftL (e₀ y)) MeasureTheory.volume :=
    continuous_liftL.comp_aestronglyMeasurable he₀m
  have hQe : AEStronglyMeasurable (fun y => dqLiftL (e₀ y) (e₀ y)) MeasureTheory.volume :=
    (continuous_dqLiftL.comp (continuous_id.prodMk continuous_id)).comp_aestronglyMeasurable he₀m
  have hwd1 : AEStronglyMeasurable (fun y => liftL (e₀ y) (τ.f y)) MeasureTheory.volume :=
    LpProductContinuity.aestronglyMeasurable_apply hLe (τ.f).continuous.aestronglyMeasurable
  have hwd2 : AEStronglyMeasurable (fun y => fun lam => liftL (e₀ y) (τ.df lam y) +
      dqLiftL (e₀ y) (e₀ y) (P y lam) (τ.f y)) MeasureTheory.volume := by
    refine aestronglyMeasurable_pi_fin fun lam => ?_
    exact (LpProductContinuity.aestronglyMeasurable_apply hLe
      (τ.df lam).continuous.aestronglyMeasurable).add
      (LpProductContinuity.aestronglyMeasurable_apply
        (LpProductContinuity.aestronglyMeasurable_apply hQe
          ((continuous_apply lam).comp_aestronglyMeasurable hPm.1))
        (τ.f).continuous.aestronglyMeasurable)
  have hwdm : AEStronglyMeasurable wd MeasureTheory.volume := by
    rw [hwddef]
    exact hwd1.prodMk hwd2
  -- pointwise bounds on the variation
  have hed : ∀ᵐ y, ‖(wd y).1‖ ≤ Ce := by
    filter_upwards [he₀K] with y hy
    rw [hwddef]
    show ‖liftL (e₀ y) (τ.f y)‖ ≤ Ce
    refine ((liftL (e₀ y)).le_opNorm _).trans ?_
    have := mul_le_mul ((hCL _ hy).trans (le_max_left _ _))
      (((τ.f).norm_coe_le_norm y).trans τ.f_le) (norm_nonneg _) (le_max_right CL 0)
    linarith
  have hpd : ∀ᵐ y, ‖(wd y).2‖ ≤ Ce + Cq * ‖P y‖ := by
    filter_upwards [he₀K] with y hy
    rw [hwddef]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun lam => ?_
    show ‖liftL (e₀ y) (τ.df lam y) + dqLiftL (e₀ y) (e₀ y) (P y lam) (τ.f y)‖ ≤ _
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine ((liftL (e₀ y)).le_opNorm _).trans ?_
      have := mul_le_mul ((hCL _ hy).trans (le_max_left _ _))
        (((τ.df lam).norm_coe_le_norm y).trans (τ.df_le lam)) (norm_nonneg _) (le_max_right CL 0)
      linarith
    · refine ((dqLiftL (e₀ y) (e₀ y) (P y lam)).le_opNorm _).trans ?_
      refine (mul_le_mul_of_nonneg_right ((dqLiftL (e₀ y) (e₀ y)).le_opNorm _)
        (norm_nonneg _)).trans ?_
      have h1 : ‖dqLiftL (e₀ y) (e₀ y)‖ ≤ max CQ 0 := (hCQ _ hy).trans (le_max_left _ _)
      have h2 : ‖P y lam‖ ≤ ‖P y‖ := norm_le_pi_norm (P y) lam
      have h3 : ‖τ.f y‖ ≤ Tn := ((τ.f).norm_coe_le_norm y).trans τ.f_le
      calc ‖dqLiftL (e₀ y) (e₀ y)‖ * ‖P y lam‖ * ‖τ.f y‖ ≤ max CQ 0 * ‖P y‖ * Tn := by gcongr
        _ = Cq * ‖P y‖ := by ring
  -- the perturbed coframes stay in the thickened chart
  have hin : ∀ᵐ y, ∀ t ∈ Metric.ball (0 : ℝ) ε, (w0 y + t • wd y).1 ∈ Ke' := by
    filter_upwards [he₀K, hed] with y hy hy2 t ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    refine Metric.mem_cthickening_of_dist_le _ (e₀ y) δ Ke4 hy ?_
    rw [Prod.fst_add, Prod.smul_fst, hw0def]
    show dist (e₀ y + t • (wd y).1) (e₀ y) ≤ δ
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖(wd y).1‖ ≤ (δ / Ce) * Ce := mul_le_mul (ht.le.trans (min_le_right _ _)) hy2
          (norm_nonneg _) (by positivity)
      _ = δ := div_mul_cancel₀ δ hCe.ne'
  -- regularity along the segment
  have hS : IsClosed {w : M4 × (Fin 4 → M4) | w.1 ∈ Ke'} :=
    Metric.isClosed_cthickening.preimage continuous_fst
  have hPc : ContinuousOn (palatiniL κ Λ) {w : M4 × (Fin 4 → M4) | w.1 ∈ Ke'} := fun w hw =>
    (contDiffAt_palatiniL κ Λ (hKe'det _ hw).ne').continuousAt.continuousWithinAt
  have hPdc : ContinuousOn (fderiv ℝ (palatiniL κ Λ)) {w : M4 × (Fin 4 → M4) | w.1 ∈ Ke'} :=
    fun w hw => ((contDiffAt_palatiniL κ Λ (hKe'det _ hw).ne').fderiv_right (m := 0)
      (by norm_num)).continuousAt.continuousWithinAt
  have hwt : ∀ t : ℝ, AEStronglyMeasurable (fun y => w0 y + t • wd y) MeasureTheory.volume :=
    fun t => hw0m.add (hwdm.const_smul t)
  -- the integrand and its derivative
  let F : ℝ → UnitAddTorus (Fin 4) → ℝ := fun t y => palatiniL κ Λ (w0 y + t • wd y)
  let F' : ℝ → UnitAddTorus (Fin 4) → ℝ := fun t y =>
    fderiv ℝ (palatiniL κ Λ) (w0 y + t • wd y) (wd y)
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) MeasureTheory.volume := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    exact aestronglyMeasurable_comp_continuousOn hS hPc (hwt t)
      (by filter_upwards [hin] with y hy using hy t ht)
  have hin0 : ∀ᵐ y, (w0 y + (0 : ℝ) • wd y).1 ∈ Ke' := by
    filter_upwards [hin] with y hy using hy 0 (Metric.mem_ball_self hε)
  have hF'_meas : AEStronglyMeasurable (F' 0) MeasureTheory.volume :=
    LpProductContinuity.aestronglyMeasurable_apply
      (aestronglyMeasurable_comp_continuousOn hS hPdc (hwt 0) hin0) hwdm
  have hP2 : Integrable (fun y => ‖P y‖ ^ 2) MeasureTheory.volume :=
    (memLp_two_iff_integrable_sq_norm hPm.1).1 hPm
  have hP1 : Integrable (fun y => ‖P y‖) MeasureTheory.volume :=
    (memLp_one_iff_integrable.1 (hPm.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))).norm
  have hsq : Integrable (fun y => (1 + ‖P y‖) ^ 2) MeasureTheory.volume := by
    have : (fun y => (1 + ‖P y‖) ^ 2) = fun y => 1 + 2 * ‖P y‖ + ‖P y‖ ^ 2 := by
      funext y; ring
    rw [this]
    exact ((integrable_const 1).add (hP1.const_mul 2)).add hP2
  have hF_int : Integrable (F 0) MeasureTheory.volume := by
    refine Integrable.mono' ((hsq.const_mul (max MΓ 0)).add (integrable_const (|Λ / κ| * max CV0 0)))
      ((hF_meas.self_of_nhds)) ?_
    filter_upwards [he₀K] with y hy
    show ‖palatiniL κ Λ (w0 y + (0 : ℝ) • wd y)‖ ≤ _
    rw [zero_smul, add_zero, Real.norm_eq_abs, hw0def]
    show |Γg κ (0, constJetL (e₀ y, P y)) - Λ / κ * volM (e₀ y)| ≤ _
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · refine (hMΓ _ _ (fun s => hy)).trans ?_
      have h1 : 1 + ‖(constJetL (e₀ y, P y)).2‖ ≤ 1 + ‖P y‖ := by
        linarith [norm_constJet_snd_le (e₀ y, P y)]
      calc MΓ * (1 + ‖(constJetL (e₀ y, P y)).2‖) ^ 2 ≤ max MΓ 0 * (1 + ‖P y‖) ^ 2 := by
            refine mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) h1 2)
              (by positivity) (le_max_right _ _)
        _ = _ := rfl
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (((Real.norm_eq_abs _) ▸ hCV0 _ hy).trans
        (le_max_left _ _)) (abs_nonneg _)
  -- the bound
  set Bc := max MJ 0 * (Ce + 1) * (2 + Ce + Cq) ^ 2
  set Bv := |Λ / κ| * max CV 0 * Ce
  have h_bound : ∀ᵐ y, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖F' t y‖ ≤ Bc * (1 + ‖P y‖) ^ 2 + Bv := by
    filter_upwards [hin, hed, hpd, he₀K] with y hy hy1 hy2 hyK t ht
    have hdet : Matrix.det (show Mat from (w0 y + t • wd y).1) ≠ 0 := (hKe'det _ (hy t ht)).ne'
    have ht1 : |t| ≤ 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      exact ht.le.trans (min_le_left _ _)
    show ‖fderiv ℝ (palatiniL κ Λ) ((w0 y + t • wd y).1, (w0 y + t • wd y).2) (wd y)‖ ≤ _
    rw [fderiv_palatiniL_apply κ Λ hdet, Real.norm_eq_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · have hJ := hMJ _ (constJetL ((w0 y + t • wd y).1, (w0 y + t • wd y).2)).2
        (fun s => hy t ht) (constJetL (wd y))
      refine hJ.trans ?_
      have hq : ‖(constJetL ((w0 y + t • wd y).1, (w0 y + t • wd y).2)).2‖ ≤
          ‖P y‖ + (Ce + Cq * ‖P y‖) := by
        refine (norm_constJet_snd_le _).trans ?_
        show ‖(w0 y + t • wd y).2‖ ≤ _
        rw [Prod.snd_add, Prod.smul_snd, hw0def]
        show ‖P y + t • (wd y).2‖ ≤ _
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Real.norm_eq_abs]
        calc |t| * ‖(wd y).2‖ ≤ 1 * (Ce + Cq * ‖P y‖) :=
              mul_le_mul ht1 hy2 (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      have hd1 : ‖(constJetL (wd y)).1‖ ≤ Ce := (norm_constJet_fst_le _).trans hy1
      have hd2 : ‖(constJetL (wd y)).2‖ ≤ Ce + Cq * ‖P y‖ := (norm_constJet_snd_le _).trans hy2
      have hA : 1 + ‖P y‖ + (Ce + Cq * ‖P y‖) ≤ (2 + Ce + Cq) * (1 + ‖P y‖) := by
        nlinarith [norm_nonneg (P y)]
      have hA' : Ce + Cq * ‖P y‖ ≤ (2 + Ce + Cq) * (1 + ‖P y‖) := by
        nlinarith [norm_nonneg (P y)]
      have hA0 : 0 ≤ 1 + ‖(constJetL ((w0 y + t • wd y).1, (w0 y + t • wd y).2)).2‖ := by
        positivity
      set Q := 1 + ‖(constJetL ((w0 y + t • wd y).1, (w0 y + t • wd y).2)).2‖
      have hQ : Q ≤ (2 + Ce + Cq) * (1 + ‖P y‖) := by
        show 1 + _ ≤ _
        linarith
      calc MJ * (Q ^ 2 * ‖(constJetL (wd y)).1‖ + Q * ‖(constJetL (wd y)).2‖)
          ≤ max MJ 0 * (Q ^ 2 * Ce + Q * ((2 + Ce + Cq) * (1 + ‖P y‖))) := by
            refine mul_le_mul (le_max_left _ _) ?_ (by positivity) (le_max_right _ _)
            exact add_le_add (mul_le_mul_of_nonneg_left hd1 (by positivity))
              (mul_le_mul_of_nonneg_left (hd2.trans hA') hA0)
        _ ≤ max MJ 0 * (((2 + Ce + Cq) * (1 + ‖P y‖)) ^ 2 * Ce +
              ((2 + Ce + Cq) * (1 + ‖P y‖)) * ((2 + Ce + Cq) * (1 + ‖P y‖))) := by
            gcongr
        _ = Bc * (1 + ‖P y‖) ^ 2 := by ring
    · have hBv : Bv = |Λ / κ| * (max CV 0 * Ce) := by ring
      rw [abs_mul, hBv]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h0 := (fderiv ℝ volM (w0 y + t • wd y).1).le_opNorm ((wd y).1)
      rw [Real.norm_eq_abs] at h0
      refine h0.trans ?_
      have h1 : ‖fderiv ℝ volM (w0 y + t • wd y).1‖ ≤ max CV 0 :=
        (hCV _ (hy t ht)).trans (le_max_left _ _)
      exact mul_le_mul h1 hy1 (norm_nonneg _) (le_max_right _ _)
  have hbound_int : Integrable (fun y => Bc * (1 + ‖P y‖) ^ 2 + Bv) MeasureTheory.volume :=
    (hsq.const_mul Bc).add (integrable_const Bv)
  have h_diff : ∀ᵐ y, ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivAt (fun t => F t y) (F' t y) t := by
    filter_upwards [hin] with y hy t ht
    have hdet : Matrix.det (show Mat from (w0 y + t • wd y).1) ≠ 0 := (hKe'det _ (hy t ht)).ne'
    have hP := (contDiffAt_palatiniL κ Λ hdet).differentiableAt (by simp)
    have hline : HasDerivAt (fun s : ℝ => w0 y + s • wd y) (wd y) t := by
      have := ((hasDerivAt_id t).smul_const (wd y)).const_add (w0 y)
      simpa using this
    exact hP.hasFDerivAt.comp_hasDerivAt t hline
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds 0 hε)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hfin := key.2
  simp only [F, F'] at hfin
  simp only [zero_smul, add_zero] at hfin
  subst hw0def hwddef hPdef
  exact hfin
/-- The continuum gravitational first variation is the derivative of the first-order Palatini
action along the lifted test (`app:palatini`: "its derivative in the lift"). -/
theorem contGravVariation_eq_deriv (κ Λ : ℝ) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hKdet : ∀ M ∈ Ke, 0 < M.det) {e₀ : UnitAddTorus (Fin 4) → M4}
    {p : Fin 4 → UnitAddTorus (Fin 4) → M4}
    (he₀m : AEStronglyMeasurable e₀ MeasureTheory.volume)
    (he₀K : ∀ᵐ y, (e₀ y : Mat) ∈ Ke) (hp : ∀ μ, MemLp (p μ) 2 MeasureTheory.volume)
    (τ : C2Test M4) :
    contGravVariation κ Λ e₀ p τ = deriv (fun t : ℝ => ∫ y, palatiniL κ Λ
      ((e₀ y, fun lam => p lam y) +
        t • liftedVar (e₀ y) (fun lam => p lam y) (τ.f y) (fun lam => τ.df lam y))) 0 :=
  (hasDerivAt_palatiniAction κ Λ hKe hKdet he₀m he₀K hp τ).deriv.symm

end ActionDerivative

/-! ### Non-vacuity -/

section NonVacuity

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-- The flat records `e ≡ 1` (all other fields zero). -/
def flatRecord (N : ℕ) : Grid N → Field 𝔄 𝓗 𝓢 := fun _ => ((1 : Mat), 0)

theorem omegaLink_flat {N : ℕ} [NeZero N] (h : ℝ) (x : Grid N) (μ : Fin 4) :
    omegaLink h (coframe (flatRecord (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) N)) x μ = 0 := by
  have h0 : (fun lam => fwdDiff h lam (coframe (flatRecord (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) N)) x) =
      (0 : ℝ) • (fun _ : Fin 4 => (0 : Mat)) := by
    funext lam
    simp [ShiftedJetAction.fwdDiff, coframe, flatRecord]
  unfold omegaLink
  rw [h0, NativeScaling.readerOmega_smul, zero_smul]

/-- **Non-vacuity of `native_gravity_firstjet`**: the flat records (identity coframe) satisfy every
hypothesis (chart `K_e = {1}`, margin `c_* = 0`, constant first jets). -/
example (D : Data 𝔄 𝓗 𝓢) : ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : C2Test M4,
    |gravVariation D (k + 1) (flatRecord (k + 1)) τ -
      contGravVariation D.κ D.Λ (fun _ => asM4 1) (fun _ _ => 0) τ| ≤ ε * τ.norm := by
  refine native_gravity_firstjet D (n := fun k => k + 1) (tendsto_add_atTop_nat 1)
    (fun k => flatRecord (k + 1)) (fun _ => asM4 1) (fun _ _ => 0) (Ke := {(1 : Mat)})
    isCompact_singleton (by simp) (fun k x => rfl) (c := 0) (by norm_num) ?_ ?_ ?_
  · intro k x μ
    rw [omegaLink_flat]
    have : asM4 (0 : Mat) = 0 := by funext i j; rfl
    rw [this, norm_zero, mul_zero]
  · exact (LpTendsto.const (u := fun _ : UnitAddTorus (Fin 4) => asM4 1)
      (memLp_const _)).congr (fun k => Eventually.of_forall fun y' => rfl)
        (Eventually.of_forall fun _ => rfl)
  · intro μ
    refine (LpTendsto.const (u := fun _ : UnitAddTorus (Fin 4) => (0 : M4))
      (memLp_const _)).congr (fun k => Eventually.of_forall fun y' => ?_)
        (Eventually.of_forall fun _ => rfl)
    funext i j
    show (0 : ℝ) = ((k + 1 : ℕ) : ℝ)⁻¹⁻¹ * ((1 : Mat) i j - (1 : Mat) i j)
    ring

end NonVacuity

end

end RenewalGeometry.NativeGravityFirstJet
