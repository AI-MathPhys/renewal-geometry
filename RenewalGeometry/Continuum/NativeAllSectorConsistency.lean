/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeYMDensityBridge
import RenewalGeometry.Continuum.NativeHiggsSectorVariation

/-!
# All-sector native consistency without a growing band (`thm:native-firstvariation-no-band`)

Einstein–SM action-closure manuscript, `thm:native-firstvariation-no-band`
(`eq:native-all-sector-limit` and the Euler corollary).  Unit-torus rendering of the periodic
comparison box (grid `(ℤ/N)⁴`, mesh `h = 1/N`, raw reconstruction `R_h^0 = pc`; the paper's box of
side `2π` is the dilation `x ↦ 2πx`), trivialised bundles (one fixed frame), as in the sector files.

The complete native first variation `nativeVar` is the literal directional derivative of the
**unchanged local action** `S_h^{loc} = h⁴ Σ_x 𝓛_h` (`NativeDensity.localAction`, all four rows of
`eq:native-densities`) along the nodal test record `𝓘_h v` (`NativeDiracLimit.testRec`: symmetric
coframe lift of the inverse-metric test, sampled gauge, Higgs, spinor and co-spinor tests).

* `localAction_eq_sum`, `nativeVar_testRec_eq`: the native action is the sum of its four rows and
  its first variation along `𝓘_h v` is the sum of the four sector variations (gravity
  `NativeGravityFirstJet.gravVariation`, Yang–Mills `NativeYMBridge.ymVar`, Higgs
  `NativeHiggsVar.higgsVar`, Dirac–Yukawa `NativeDirac.dVar`) on the oriented coframe chart, the
  Cartan logarithm chart and the scaled gauge-slot chart.
* `contAllVar`: the continuum Einstein–SM first variation `D𝒮_θ(z)[v]`, the sum of the
  first-order Palatini variation, the continuum Yang–Mills, Higgs and Dirac–Yukawa covectors (each
  identified with the integrated derivative of its continuum density in the sector files:
  `contGravVariation_eq_deriv`, `NativeYMMetric.firstVarCont`,
  `NativeHiggsVar.contHiggsVar_eq_integral_deriv`,
  `NativeSpinorVariation.contDiracVar_eq_integral_deriv`).
* `native_all_sector_limit` (**`eq:native-all-sector-limit`**): under `(N1)` (strong first-jet
  coframe convergence on a compact oriented chart with the logarithm margin `c_* ≤ 1/64`), `(N2)`
  (strong `L⁴` connections and strong `L²` literal curvature), the Higgs conclusions of
  `prop:native-Higgs-compactness` (`HiggsHyp`) and the spinor extraction outputs of
  `prop:native-spinor-variation` (`SpinHyp`, weak `L²` limit `u₀` of the spinor first
  differences), for every radius `M` and `ε > 0`, eventually
  `|D S_h^{loc}(z_h)[𝓘_h v] - D𝒮_θ(z)[v]| ≤ ε` for **all** tests `‖v‖_{C²} ≤ M` (convergence
  holds sectorwise).
* `native_all_sector_euler` (Euler corollary): if the complete finite variation tends to zero on
  the unit test family, `D𝒮_θ(z)[v] = 0` for **every** test `v` — `z` satisfies the minimally
  coupled Einstein–SM Euler equations in distributions (homogeneity of the finite variation in the
  test, `testRec_smul`, `nativeVar_smul`).
* `exists_higgsHyp`: the Higgs hypotheses follow, after extraction, from `(N3)`
  (`sup ‖H_h‖_{2,h} < ∞`, strong `L²` convergence of the literal Higgs-link packet) by
  `prop:native-Higgs-compactness` (`NativeHiggs.native_Higgs_compactness`), for a Higgs fibre in a
  fixed orthonormal real frame and a unitary internal representation.

Disclosed renderings: as in `NativeYMDensityBridge` (complex finite-dimensional gauge algebra,
invariant form `⟪T ·, T ·⟫`); finite-dimensional real Higgs/spinor fibres; co-spinors read
through a frame `κ`.
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace RenewalGeometry.NativeAllSector

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)
open ShiftedJetAction (Grid unitVec fwdDiff stencil)
open NativeScaling (Mat omegaLink)
open NativeGravityFirstJet (M4 asM4 coframeM liftM gravAction gravVariation liftRecord
  contGravVariation)
open NativeDensity
open NativeDiracLimit (DTest testRec samp)
open NativeDiracConv (CoHyp)
open NativeDiracConvergence (SpinHyp)
open TorusC2Tests

/-! ### Homogeneity of tests -/

section Scaling

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The scaled `C²` test `c k`. -/
def c2smul (c : ℝ) (k : C2Test F) : C2Test F where
  f := c • k.f
  df μ := c • k.df μ
  ddf μ ν := c • k.ddf μ ν
  hasDerivAt_f μ y := (k.hasDerivAt_f μ y).const_smul c
  hasDerivAt_df μ ν y := (k.hasDerivAt_df μ ν y).const_smul c

theorem c2smul_norm (c : ℝ) (k : C2Test F) : (c2smul c k).norm = |c| * k.norm := by
  simp only [C2Test.norm, c2smul, norm_smul, Real.norm_eq_abs, Finset.mul_sum, mul_add]

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']

/-- The scaled test `c v`. -/
def dsmul (c : ℝ) (τ : DTest 𝔄 𝓗 𝓢 W') : DTest 𝔄 𝓗 𝓢 W' :=
  ⟨c2smul c τ.k, c2smul c τ.a, c2smul c τ.η, c2smul c τ.ψ, c2smul c τ.ψb⟩

theorem dsmul_norm (c : ℝ) (τ : DTest 𝔄 𝓗 𝓢 W') : (dsmul c τ).norm = |c| * τ.norm := by
  simp only [DTest.norm, dsmul, c2smul_norm]
  ring

end Scaling

/-! ### The native action is the sum of its four rows -/

section Rows

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

theorem localAction_eq_sum {N : ℕ} [NeZero N] (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) :
    localAction D h y = gravAction D h y + NativeYMBridge.ymAct D h y +
      NativeHiggsVar.higgsAct D h y + NativeDirac.dAct D h y := by
  simp only [localAction, nativeDensity, gravAction, NativeYMBridge.ymAct,
    NativeHiggsVar.higgsAct, NativeDirac.dAct, Finset.sum_add_distrib, mul_add]

/-- **The complete native first variation** `D S_h^{loc}(y)[v]`, `h = 1/N`: the literal
directional derivative of the unchanged local action. -/
def nativeVar (N : ℕ) [NeZero N] (y v : Grid N → Field 𝔄 𝓗 𝓢) : ℝ :=
  deriv (fun s : ℝ => localAction D (N : ℝ)⁻¹ (y + s • v)) 0

/-- The complete native first variation is homogeneous in the direction. -/
theorem nativeVar_smul {N : ℕ} [NeZero N] (y v : Grid N → Field 𝔄 𝓗 𝓢) (c : ℝ) :
    nativeVar D N y (c • v) = c * nativeVar D N y v := by
  have e : (fun s : ℝ => localAction D (N : ℝ)⁻¹ (y + s • c • v)) =
      fun s => (fun u : ℝ => localAction D (N : ℝ)⁻¹ (y + u • v)) (c * s) := by
    funext s
    rw [smul_smul, mul_comm]
  have h1 := deriv_comp_mul_left (𝕜 := ℝ) (c := c) (x := 0)
    (f := fun u : ℝ => localAction D (N : ℝ)⁻¹ (y + u • v))
  rw [nativeVar, e, h1, mul_zero, smul_eq_mul]
  rfl

/-- The nodal test record is linear in the test. -/
theorem testRec_dsmul {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W')
    (c : ℝ) : testRec κ N y (dsmul c τ) = c • testRec κ N y τ := by
  funext x
  simp only [testRec, dsmul, c2smul, samp, Pi.smul_apply, ContinuousMap.smul_apply,
    map_smul, Prod.smul_mk]
  congr 1
  exact NativeGravityFirstJet.liftM_smul _ _ c

theorem coframe_testRec_eq_liftRecord {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (τ : DTest 𝔄 𝓗 𝓢 W') (s : ℝ) :
    coframe (y + s • testRec κ N y τ) = coframe (y + s • liftRecord N y τ.k) := rfl

/-- The gravitational row depends only on the coframe. -/
theorem gravAction_testRec {N : ℕ} [NeZero N] (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢)
    (τ : DTest 𝔄 𝓗 𝓢 W') (s : ℝ) :
    gravAction D h (y + s • testRec κ N y τ) = gravAction D h (y + s • liftRecord N y τ.k) := by
  simp only [gravAction, gravityDensity, cartanCurvature, coframe_testRec_eq_liftRecord κ y τ s]

end Rows


/-! ### The complete native variation along the nodal test record -/

section Decomposition

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- **The complete native first variation along `𝓘_h v` is the sum of the four sector
variations**, on the oriented coframe chart, the Cartan logarithm chart (`GravRegular`) and the
scaled gauge-slot chart. -/
theorem nativeVar_testRec_eq (T : 𝔄 →L[ℝ] E) (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫) {N : ℕ}
    [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W')
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖NativeDensity.cartanPlaquette (N : ℝ)⁻¹ (coframe y) x μ ν - 1‖ < 1)
    (hreg : ∀ x, NativeGravityJet.GravRegular ((N : ℝ)⁻¹,
      (stencil (N : ℝ)⁻¹ (shiftVec N) x (coframeM y) : NativeGravityFirstJet.T4)))
    (hch : ∀ x μ ν, (N : ℝ)⁻¹ * LogBCH.normSum
      (NativeYMIdentification.slots (NativeYMBridge.gaugeArr y) x μ ν) ≤ 1 / 32) :
    nativeVar D N y (testRec κ N y τ) =
      gravVariation D N y τ.k + NativeYMBridge.ymVar D N y (testRec κ N y τ) +
        NativeHiggsVar.higgsVar D N y (testRec κ N y τ) +
        NativeDirac.dVar D (N : ℝ)⁻¹ y (testRec κ N y τ) := by
  have hN : ((N : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N))
  have hdet' : ∀ x, (coframe y x).det ≠ 0 := fun x => (hdet x).ne'
  -- gravity
  have hg1 := NativeGravityFirstJet.hasDerivAt_gravAction D hN y (liftRecord N y τ.k) hdet hlog
    hreg
  have hg : HasDerivAt (fun s : ℝ => gravAction D (N : ℝ)⁻¹ (y + s • testRec κ N y τ))
      (gravVariation D N y τ.k) 0 := by
    have e : (fun s : ℝ => gravAction D (N : ℝ)⁻¹ (y + s • testRec κ N y τ)) =
        fun s => gravAction D (N : ℝ)⁻¹ (y + s • liftRecord N y τ.k) :=
      funext fun s => gravAction_testRec D κ _ y τ s
    rw [e, gravVariation, hg1.deriv]
    exact hg1
  -- Yang–Mills
  have hy := NativeYMBridge.hasDerivAt_ymAct D T hip y (testRec κ N y τ) (fun x => hdet' x) hch
  -- Higgs
  have hh := NativeHiggsVar.hasDerivAt_higgsAct D y (testRec κ N y τ) hdet'
  -- Dirac
  have hd := NativeDirac.hasDerivAt_dAct D (N : ℝ)⁻¹ y (testRec κ N y τ) hdet'
  have htot := ((hg.add hy).add hh).add hd
  have e : (fun s : ℝ => localAction D (N : ℝ)⁻¹ (y + s • testRec κ N y τ)) =
      fun s => gravAction D (N : ℝ)⁻¹ (y + s • testRec κ N y τ) +
        NativeYMBridge.ymAct D (N : ℝ)⁻¹ (y + s • testRec κ N y τ) +
        NativeHiggsVar.higgsAct D (N : ℝ)⁻¹ (y + s • testRec κ N y τ) +
        NativeDirac.dAct D (N : ℝ)⁻¹ (y + s • testRec κ N y τ) :=
    funext fun s => localAction_eq_sum D _ _
  have htot' : HasDerivAt (fun s : ℝ => gravAction D (N : ℝ)⁻¹ (y + s • testRec κ N y τ) +
      NativeYMBridge.ymAct D (N : ℝ)⁻¹ (y + s • testRec κ N y τ) +
      NativeHiggsVar.higgsAct D (N : ℝ)⁻¹ (y + s • testRec κ N y τ) +
      NativeDirac.dAct D (N : ℝ)⁻¹ (y + s • testRec κ N y τ)) _ 0 := htot
  rw [nativeVar, e, htot'.deriv, NativeYMBridge.ymVar, hy.deriv, NativeHiggsVar.higgsVar, hh.deriv,
    NativeDirac.dVar, hd.deriv]

end Decomposition

/-! ### `eq:native-all-sector-limit` -/

section Limit

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢) (T : 𝔄 →L[ℝ] E)
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- **The continuum Einstein–SM first variation** `D𝒮_θ(z)[v]`: first-order Palatini
(`contGravVariation`), Yang–Mills (`firstVarCont`, with the curvature limit `F = F_A`), Higgs
(`contHiggsVar`) and Dirac–Yukawa (`contDiracVar`, with `u₀ = (∂Ψ, ∂χ)`) covectors at the limit
fields. -/
def contAllVar (H : CoHyp n y) (F : Fin 4 → Fin 4 → 𝕋 → 𝔄)
    (P : NativeHiggsVar.HiggsHyp D y) (S : SpinHyp κ y)
    (u₀ : 𝕋 → NativeDiracLimit.Dif 𝓢 W') (τ : DTest 𝔄 𝓗 𝓢 W') : ℝ :=
  contGravVariation D.κ D.Λ H.e₀ H.p τ.k +
    NativeYMMetric.firstVarCont T H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a) +
    NativeHiggsVar.contHiggsVar D H P τ + NativeSpinorVariation.contDiracVar D κ H S u₀ τ

/-- The chart conditions of `nativeVar_testRec_eq` hold eventually along the sequence. -/
theorem eventually_charts (H : CoHyp n y) (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M))
    (hc : H.c ≤ 1 / 64) :
    ∀ᶠ k in atTop, (∀ x, 0 < (coframe (y k) x).det) ∧
      (∀ x μ ν, ‖NativeDensity.cartanPlaquette (n k : ℝ)⁻¹ (coframe (y k)) x μ ν - 1‖ < 1) ∧
      (∀ x, NativeGravityJet.GravRegular ((n k : ℝ)⁻¹,
        (stencil (n k : ℝ)⁻¹ (shiftVec (n k)) x (coframeM (y k)) : NativeGravityFirstJet.T4))) ∧
      (∀ x μ ν, ((n k : ℝ))⁻¹ * LogBCH.normSum
        (NativeYMIdentification.slots (NativeYMBridge.gaugeArr (y k)) x μ ν) ≤ 1 / 32) := by
  have hA : ∀ μ, LpTendsto volume 4
      (fun k => pc (fun x => NativeYMBridge.gaugeArr (y k) x μ)) (H.A₀ μ) := H.hA
  obtain ⟨δ, -, hev⟩ := NativeYMMetric.unif_FextV H.hn hA 1
  filter_upwards [hev] with k hk
  have hNpos : (0 : ℝ) < (n k : ℝ)⁻¹ := by
    have : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    positivity
  have hKe : ∀ M : Mat, M ∈ H.Ke → 0 < M.det := hpos
  refine ⟨fun x => hpos _ (H.hval k x), fun x μ ν => ?_, fun x => ?_, hk.1⟩
  · exact NativeGravityFirstJet.cartan_log_lt hNpos hc (coframe (y k)) (H.hmar k) x μ ν
  · exact NativeGravityFirstJet.gravRegular_stencil hNpos hKe hc (coframeM (y k)) (H.hval k)
      (H.hmar k) x

/-- **`eq:native-all-sector-limit`** (`thm:native-firstvariation-no-band`, unit-torus rendering).
Let the actual nodal records `y_h` of the unchanged local action satisfy
* `(N1)` (`CoHyp`, `hpos`, `hc`): coframes in one compact **oriented** nondegenerate chart with
  the logarithm margin `h|ω_{μ,h}| ≤ c_* ≤ 1/64`, `R^0 e_h → e`, `R^0 D⁺e_h → ∂e` strongly in `L²`;
* `(N2)` (`CoHyp.hA`, `hF`): `R^0 A_h → A` strongly in `L⁴` and the literal logarithmic curvature
  `R^0 F_h → F` strongly in `L²`;
* the Higgs conclusions of `prop:native-Higgs-compactness` (`HiggsHyp`: `R^0 H_h → H` in `L⁴`,
  `R^0 K_h → K` in `L²`; obtained from `(N3)` by `exists_higgsHyp`);
* the spinor extraction outputs of `prop:native-spinor-variation` (`SpinHyp` and the weak `L²`
  limit `u₀ = (∂Ψ, ∂χ)` of the spinor first differences).
Then for every radius `M` and `ε > 0`, eventually
`|D S_h^{loc}(z_h)[𝓘_h v] - D𝒮_θ(z)[v]| ≤ ε` for **all** tests with `‖v‖_{C²} ≤ M`; in
particular `sup_{‖v‖_{C^r} ≤ 1} |…| → 0` for every `r ≥ 2`.  The convergence holds sectorwise. -/
theorem native_all_sector_limit (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫) (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (P : NativeHiggsVar.HiggsHyp D y) (S : SpinHyp κ y) {u₀ : 𝕋 → NativeDiracLimit.Dif 𝓢 W'}
    (hu₀ : MemLp u₀ 2 volume) {C : ℝ}
    (hub : ∀ k, (eLpNorm (pc (NativeDiracLimit.difs (y k) (S.χ k))) 2 volume).toReal ≤ C)
    (hw : ∀ g : 𝕋 → NativeDiracLimit.Dif 𝓢 W' →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (pc (NativeDiracLimit.difs (y k) (S.χ k)) z)) atTop
        (𝓝 (∫ z, g z (u₀ z))))
    (M : NNReal) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ M →
      |nativeVar D (n k) (y k) (testRec κ (n k) (y k) τ) - contAllVar D κ T H F P S u₀ τ| ≤ ε := by
  intro ε hε
  have hM0 : (0 : ℝ) ≤ M := M.2
  set ε' : ℝ := ε / (4 * ((M : ℝ) + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'M : ε' * M ≤ ε / 4 := by
    rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the four sector limits
  have hG := NativeGravityFirstJet.native_gravity_firstjet D H.hn y H.e₀ H.p (Ke := (H.Ke : Set Mat))
    H.hKe hpos H.hval hc H.hmar H.he H.hp ε' hε'0
  obtain ⟨β, hβ, hYM⟩ := NativeYMBridge.native_YM_sector D κ T hip H hF M
  have hβε : ∀ᶠ k in atTop, β k ≤ ε / 4 :=
    (tendsto_order.1 hβ).2 (ε / 4) (by positivity) |>.mono fun k hk => hk.le
  have hHi := NativeHiggsVar.native_Higgs_sector D κ H P ε' hε'0
  have hDi := NativeSpinorVariation.native_spinor_variation D κ H S hu₀ hub hw ε' hε'0
  filter_upwards [hG, hYM, hβε, hHi, hDi, eventually_charts H hpos hc] with k hg hy hb hh hd hch
    τ hτ
  rw [nativeVar_testRec_eq D κ T hip (y k) τ hch.1 hch.2.1 hch.2.2.1 hch.2.2.2]
  have h1 := hg τ.k
  have h2 := hy τ hτ
  have h3 := hh τ
  have h4 := hd τ
  have hk : τ.k.norm ≤ M := τ.k_le.trans hτ
  have hτ' : ε' * τ.norm ≤ ε / 4 := (mul_le_mul_of_nonneg_left hτ hε'0.le).trans hε'M
  have hk' : ε' * τ.k.norm ≤ ε / 4 := (mul_le_mul_of_nonneg_left hk hε'0.le).trans hε'M
  unfold contAllVar
  have e : gravVariation D (n k) (y k) τ.k + NativeYMBridge.ymVar D (n k) (y k)
        (testRec κ (n k) (y k) τ) + NativeHiggsVar.higgsVar D (n k) (y k) (testRec κ (n k) (y k) τ) +
        NativeDirac.dVar D (n k : ℝ)⁻¹ (y k) (testRec κ (n k) (y k) τ) -
      (contGravVariation D.κ D.Λ H.e₀ H.p τ.k +
        NativeYMMetric.firstVarCont T H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a) +
        NativeHiggsVar.contHiggsVar D H P τ + NativeSpinorVariation.contDiracVar D κ H S u₀ τ) =
      (gravVariation D (n k) (y k) τ.k - contGravVariation D.κ D.Λ H.e₀ H.p τ.k) +
      (NativeYMBridge.ymVar D (n k) (y k) (testRec κ (n k) (y k) τ) -
        NativeYMMetric.firstVarCont T H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a)) +
      (NativeHiggsVar.higgsVar D (n k) (y k) (testRec κ (n k) (y k) τ) -
        NativeHiggsVar.contHiggsVar D H P τ) +
      (NativeDirac.dVar D (n k : ℝ)⁻¹ (y k) (testRec κ (n k) (y k) τ) -
        NativeSpinorVariation.contDiracVar D κ H S u₀ τ) := by ring
  rw [e]
  calc _ ≤ |gravVariation D (n k) (y k) τ.k - contGravVariation D.κ D.Λ H.e₀ H.p τ.k| +
        |NativeYMBridge.ymVar D (n k) (y k) (testRec κ (n k) (y k) τ) -
          NativeYMMetric.firstVarCont T H.e₀ H.A₀ F τ.k.f (NativeYMBridge.toC1 τ.a)| +
        |NativeHiggsVar.higgsVar D (n k) (y k) (testRec κ (n k) (y k) τ) -
          NativeHiggsVar.contHiggsVar D H P τ| +
        |NativeDirac.dVar D (n k : ℝ)⁻¹ (y k) (testRec κ (n k) (y k) τ) -
          NativeSpinorVariation.contDiracVar D κ H S u₀ τ| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_three _ _ _) le_rfl)
    _ ≤ ε / 4 + ε / 4 + ε / 4 + ε / 4 := by
        gcongr
        · exact h1.trans hk'
        · exact h2.trans hb
        · exact h3.trans hτ'
        · exact h4.trans hτ'
    _ = ε := by ring

/-- **The Euler corollary of `thm:native-firstvariation-no-band`**: if, in addition, the complete
physical finite variation tends to zero on the unit test family, then the limit `z` satisfies all
minimally coupled torsion-free Einstein–SM Euler equations in distributions:
`D𝒮_θ(z)[v] = 0` for **every** test `v` (vanishing finite stationarity gives zero limiting first
variation, as in `thm:abstract-closure`; the passage from the unit family to all tests uses the
homogeneity of the finite variation in the test). -/
theorem native_all_sector_euler (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫) (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (P : NativeHiggsVar.HiggsHyp D y) (S : SpinHyp κ y) {u₀ : 𝕋 → NativeDiracLimit.Dif 𝓢 W'}
    (hu₀ : MemLp u₀ 2 volume) {C : ℝ}
    (hub : ∀ k, (eLpNorm (pc (NativeDiracLimit.difs (y k) (S.χ k))) 2 volume).toReal ≤ C)
    (hw : ∀ g : 𝕋 → NativeDiracLimit.Dif 𝓢 W' →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (pc (NativeDiracLimit.difs (y k) (S.χ k)) z)) atTop
        (𝓝 (∫ z, g z (u₀ z))))
    (hstat : ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ 1 →
      |nativeVar D (n k) (y k) (testRec κ (n k) (y k) τ)| ≤ ε)
    (τ : DTest 𝔄 𝓗 𝓢 W') :
    contAllVar D κ T H F P S u₀ τ = 0 := by
  have hτ0 := τ.norm_nonneg
  set c : ℝ := τ.norm + 1 with hc'
  have hc0 : 0 < c := by positivity
  refine abs_eq_zero.1 (le_antisymm ?_ (abs_nonneg _))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlim := native_all_sector_limit D κ T hip H hpos hc hF P S hu₀ hub hw ⟨τ.norm, hτ0⟩
    (ε / 2) (by positivity)
  have hst := hstat (ε / (2 * c)) (by positivity)
  obtain ⟨k, hk1, hk2⟩ := (hlim.and hst).exists
  have h1 := hk1 τ le_rfl
  have hτ1 : (dsmul c⁻¹ τ).norm ≤ 1 := by
    rw [dsmul_norm, abs_of_pos (inv_pos.2 hc0), inv_mul_le_iff₀ hc0]
    linarith
  have h2 := hk2 (dsmul c⁻¹ τ) hτ1
  have hrec : testRec κ (n k) (y k) τ = c • testRec κ (n k) (y k) (dsmul c⁻¹ τ) := by
    rw [testRec_dsmul, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
  rw [hrec, nativeVar_smul] at h1
  have h3 : |c * nativeVar D (n k) (y k) (testRec κ (n k) (y k) (dsmul c⁻¹ τ))| ≤ ε / 2 := by
    rw [abs_mul, abs_of_pos hc0]
    calc c * |nativeVar D (n k) (y k) (testRec κ (n k) (y k) (dsmul c⁻¹ τ))|
        ≤ c * (ε / (2 * c)) := mul_le_mul_of_nonneg_left h2 hc0.le
      _ = ε / 2 := by field_simp
  have h4 := abs_sub_abs_le_abs_sub (contAllVar D κ T H F P S u₀ τ)
    (c * nativeVar D (n k) (y k) (testRec κ (n k) (y k) (dsmul c⁻¹ τ)))
  rw [abs_sub_comm] at h4
  linarith

end Limit

/-! ### Non-vacuity -/

section NonVacuity

open NativeGravityFirstJet (flatRecord)

/-- Left multiplication `ℂ → End_ℝ(ℂ)`, a continuous real algebra homomorphism (the
representation of the gauge algebra `ℂ = u(1)_ℂ` on a one-dimensional complex fibre). -/
def mulAlg : ℂ →ₐ[ℝ] (ℂ →L[ℝ] ℂ) where
  toFun z := ContinuousLinearMap.mul ℝ ℂ z
  map_one' := by ext w <;> simp
  map_mul' a b := by ext w <;> simp [mul_assoc]
  map_zero' := by ext w <;> simp
  map_add' a b := by ext w <;> simp [add_mul]
  commutes' r := by ext w <;> simp [Algebra.algebraMap_eq_smul_one]

/-- An abelian Einstein–Higgs–Dirac coefficient packet over `𝔄 = 𝓗 = 𝓢 = ℂ`. -/
def exData : Data ℂ ℂ ℂ where
  κ := 1
  Λ := 0
  lamH := 1
  vH := 1
  ipA := innerSL ℝ
  hermH := innerSL ℝ
  ρH := mulAlg
  ρH_cont := (ContinuousLinearMap.mul ℝ ℂ).continuous
  ρS := mulAlg
  ρS_cont := (ContinuousLinearMap.mul ℝ ℂ).continuous
  σ := 0
  γ := fun _ => 0
  yukawa := 0

theorem exData_hip (X Y : ℂ) :
    exData.ipA X Y = ⟪ContinuousLinearMap.id ℝ ℂ X, ContinuousLinearMap.id ℝ ℂ Y⟫ := rfl

/-- The coframe/connection hypotheses for the flat records (identity coframe, zero connection). -/
def exCoHyp : CoHyp (𝔄 := ℂ) (𝓗 := ℂ) (𝓢 := ℂ) (fun k => k + 1) (fun k => flatRecord (k + 1)) where
  hn := tendsto_add_atTop_nat 1
  Ke := {asM4 1}
  hKe := isCompact_singleton
  hKdet M hM := by
    rw [Set.mem_singleton_iff.1 hM]
    exact (by simp : Matrix.det (1 : Mat) ≠ 0)
  hval k x := rfl
  c := 0
  hmar k x μ := by
    simp only [NativeDiracConv.ωM]
    rw [NativeGravityFirstJet.omegaLink_flat]
    have : asM4 (0 : Mat) = 0 := by funext i j; rfl
    rw [this, norm_zero, mul_zero]
  e₀ := fun _ => asM4 1
  he := (LpTendsto.const (u := fun _ : 𝕋 => asM4 1) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)
  p := fun _ _ => 0
  hp lam := (LpTendsto.const (u := fun _ : 𝕋 => (0 : M4)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => by
      funext i j
      simp only [NativeDiracConv.qM, pc, ShiftedJetAction.fwdDiff, coframe, flatRecord]
      show (0 : ℝ) = (((k + 1 : ℕ) : ℝ)⁻¹)⁻¹ * ((1 : Mat) i j - (1 : Mat) i j)
      ring)
    (Eventually.of_forall fun _ => rfl)
  A₀ := fun _ _ => 0
  hA μ := (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)

theorem exCoHyp_pos : ∀ M ∈ exCoHyp.Ke, 0 < Matrix.det (show Mat from M) := by
  intro M hM
  rw [Set.mem_singleton_iff.1 hM]
  exact (by simp : (0 : ℝ) < Matrix.det (1 : Mat))

theorem fieldStrength_flat (k : ℕ) (x : Grid (k + 1)) (μ ν : Fin 4) :
    NativeScaling.fieldStrength ((k + 1 : ℕ) : ℝ)⁻¹
      (gauge (flatRecord (𝔄 := ℂ) (𝓗 := ℂ) (𝓢 := ℂ) (k + 1))) x μ ν = 0 := by
  have hg : gauge (flatRecord (𝔄 := ℂ) (𝓗 := ℂ) (𝓢 := ℂ) (k + 1)) = fun _ _ => 0 := rfl
  simp [hg, NativeScaling.fieldStrength, NativeScaling.gaugePlaquette,
    ShiftedPlaquette.logOneAdd]

theorem higgsLink_flat (k : ℕ) (x : Grid (k + 1)) (μ : Fin 4) :
    higgsLink exData ((k + 1 : ℕ) : ℝ)⁻¹ (flatRecord (k + 1)) x μ = 0 := by
  have hh : higgs (flatRecord (𝔄 := ℂ) (𝓗 := ℂ) (𝓢 := ℂ) (k + 1)) = fun _ => 0 := rfl
  simp [higgsLink, NativeScaling.higgsLink, hh]

/-- The Higgs hypotheses for the flat records (vanishing Higgs field). -/
def exHiggsHyp : NativeHiggsVar.HiggsHyp exData (n := fun k => k + 1)
    (fun k => flatRecord (k + 1)) where
  H₀ := fun _ => 0
  hH := (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)
  K₀ := fun _ _ => 0
  hK μ := (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => (higgsLink_flat k _ μ).symm)
    (Eventually.of_forall fun _ => rfl)

/-- The co-spinor frame (zero). -/
def exκ : ℂ →L[ℝ] CoSpinor ℂ := 0

/-- The spinor hypotheses for the flat records (vanishing spinors). -/
def exSpinHyp : SpinHyp (W' := ℂ) exκ (n := fun k => k + 1)
    (fun k => flatRecord (𝔄 := ℂ) (𝓗 := ℂ) (𝓢 := ℂ) (k + 1)) where
  H₀ := fun _ => 0
  hH := (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)
  χ k := fun _ => 0
  hχ k := by funext x; simp [exκ]; rfl
  Ψ₀ := fun _ => 0
  hΨ := (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)
  χ₀ := fun _ => 0
  hχ₀ := (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)
  B4 := ‖(0 : ℂ)‖ₑ
  hB4 := enorm_ne_top
  hΨ4 k := NativeDiracConvergence.eLpNorm_const_le (0 : ℂ)
  hχ4 k := NativeDiracConvergence.eLpNorm_const_le (0 : ℂ)

theorem pc_difs_flat (k : ℕ) :
    pc (NativeDiracLimit.difs (flatRecord (𝔄 := ℂ) (𝓗 := ℂ) (𝓢 := ℂ) (k + 1)) (exSpinHyp.χ k)) =
      fun _ => (0 : NativeDiracLimit.Dif ℂ ℂ) := by
  funext z
  simp [NativeDiracLimit.difs, pc, ShiftedJetAction.fwdDiff, psi, flatRecord, exSpinHyp]
  rfl

/-- **Non-vacuity of `native_all_sector_limit`**: the flat records (identity coframe, zero
connection, Higgs and spinor fields) of an abelian Einstein–Higgs–Dirac packet satisfy every
hypothesis — the oriented chart, the logarithm margin, `(N2)` with `F = 0`, the Higgs and spinor
hypotheses with `u₀ = 0`. -/
example (M : NNReal) : ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest ℂ ℂ ℂ ℂ, τ.norm ≤ M →
    |nativeVar exData (k + 1) (flatRecord (k + 1)) (testRec exκ (k + 1) (flatRecord (k + 1)) τ) -
      contAllVar exData exκ (ContinuousLinearMap.id ℝ ℂ) exCoHyp (fun _ _ _ => 0) exHiggsHyp
        exSpinHyp (fun _ => 0) τ| ≤ ε := by
  refine native_all_sector_limit exData exκ (ContinuousLinearMap.id ℝ ℂ) exData_hip exCoHyp
    exCoHyp_pos (by norm_num [exCoHyp]) (fun μ ν => ?_) exHiggsHyp exSpinHyp (memLp_const _)
    (C := 0) (fun k => ?_) (fun g _ => ?_) M
  · refine (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
      (fun k => Eventually.of_forall fun z => (fieldStrength_flat k _ μ ν).symm)
      (Eventually.of_forall fun _ => rfl)
  · rw [pc_difs_flat]
    simp
  · simp only [pc_difs_flat]
    exact tendsto_const_nhds

end NonVacuity
end

end RenewalGeometry.NativeAllSector
