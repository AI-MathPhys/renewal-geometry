/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSpinorVariation
import RenewalGeometry.Continuum.NativeHiggsCompactness

/-!
# The Higgs row of the native local action: first variation and its limit
  (`thm:native-firstvariation-no-band`, Higgs sector)

Einstein–SM action-closure manuscript, `thm:native-firstvariation-no-band` ("the Higgs sector is
`prop:native-Higgs-compactness`").  Unit-torus rendering of the periodic comparison box (grid
`(ℤ/N)⁴`, mesh `h = 1/N`, raw reconstruction `R_h^0 = pc`), as in
`Continuum/NativeGravityFirstJet.lean` and `Continuum/NativeSpinorVariation.lean`.

The Higgs row of `eq:native-densities` is
`𝓛_{H,h} = -v(e) g^{μν} Re⟨K^h_μ, K^h_ν⟩ - v(e) V(H)`,
`K^h_μ = h⁻¹(ρ_H(e^{hA_μ}) H(x+he_μ) - H(x))`, `V(H) = λ_H(|H|² - v_H²)²`
(`NativeDensity.higgsDensity`).

* `HJet`: the Higgs-sector test jet `(k, a, η, δη)`; `HSlots`: the slot values of the first
  variation (coframe `e`, the coframe direction map `L`, the Higgs links `K_μ`, the value `H`,
  the shifted values `T_μH`, the link derivative `Γ_μ = ρ_H ∘ Dexp(hA_μ)`, the internal links
  `U_μ = ρ_H(e^{hA_μ})` and the link coefficients `B_μ = h⁻¹(U_μ - 1)`); `hcov S`: the variation
  covector (`hcov_apply`), whose `μ`-th link variation is
  `δK_μ = Γ_μ(a_μ) T_μH + U_μ δ⁺_μη + B_μ η` (`Qop`).
* `hasDerivAt_higgsDensity`, `hasDerivAt_higgsAct`: **the exact first variation** of the
  literal Higgs row `S_{H,h} = h⁴ Σ_x 𝓛_{H,h}` along any record direction (chain rule through the
  internal links `ρ_H(e^{h(A + s a)})`, the coframe coefficients `v(e) g^{μν}(e)` and the quartic
  potential).
* `higgsVar_testRec_eq`: along the nodal test record `𝓘_h v` (`NativeDiracLimit.testRec`) the
  variation is `∫ R^0(hcov(grid slots))[R^0(J_h v)]`.
* `HiggsHyp.lpTendsto_hcov`: under the coframe/connection hypotheses `CoHyp` and the conclusions of
  `prop:native-Higgs-compactness` (`R^0 H_h → H` strongly in `L⁴`, `R^0 K_h → K` strongly in
  `L²`), the covector fields converge strongly in `L¹` to the continuum covector
  (`Γ = ρ_H`, `T_μH = H`, `U = 1`, `B_μ = ρ_H(A_μ)`).
* `native_Higgs_sector` (**Higgs sector of `eq:native-all-sector-limit`**): the Higgs first
  variation along `𝓘_h v` converges to the continuum Higgs variation uniformly on the `C²` test
  ball: for every `ε > 0`, eventually `|D S_{H,h}(y_h)[𝓘_h v] - 𝒟_H(y)[v]| ≤ ε ‖v‖_{C²}`.
* `hasDerivAt_contHiggsDens`, `contHiggsVar_eq_integral_deriv`: the limit covector is the
  integrated first variation of the continuum Higgs density
  `-v(e) g^{μν} Re⟨K_μ, K_ν⟩ - v(e) V(H)`, `K_μ = ∂_μH + ρ_H(A_μ)H`, along the lifted test line
  (with `K = D_A H` identified by `prop:native-Higgs-compactness`).
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal ContDiff

namespace RenewalGeometry.NativeHiggsVar

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance fact_one_le_two_hv : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_hv : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder221_hv : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
local instance holder442_hv : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat)
open NativeGravityFirstJet (M4 asM4 coframeM liftM liftL volM)
open NativeDensity
open TorusC2Tests

/-! ### The Higgs-sector test jet -/

section Jet

variable (𝔄 𝓗 : Type*) [NormedAddCommGroup 𝔄] [NormedSpace ℝ 𝔄] [NormedAddCommGroup 𝓗]
  [NormedSpace ℝ 𝓗]

/-- The Higgs-sector test jet `(k, a, η, δη)`: inverse-metric (or coframe) direction, gauge
direction, Higgs direction and the first differences of the Higgs direction. -/
abbrev HJet := M4 × (Fin 4 → 𝔄) × 𝓗 × (Fin 4 → 𝓗)

def πk : HJet 𝔄 𝓗 →L[ℝ] M4 := ContinuousLinearMap.fst ℝ _ _
def πa : HJet 𝔄 𝓗 →L[ℝ] (Fin 4 → 𝔄) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
def πη : HJet 𝔄 𝓗 →L[ℝ] 𝓗 :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    (ContinuousLinearMap.snd ℝ _ _))
def πdη : HJet 𝔄 𝓗 →L[ℝ] (Fin 4 → 𝓗) :=
  (ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    (ContinuousLinearMap.snd ℝ _ _))

variable {𝔄 𝓗}

@[simp] theorem πk_apply (t : HJet 𝔄 𝓗) : πk 𝔄 𝓗 t = t.1 := rfl
@[simp] theorem πa_apply (t : HJet 𝔄 𝓗) : πa 𝔄 𝓗 t = t.2.1 := rfl
@[simp] theorem πη_apply (t : HJet 𝔄 𝓗) : πη 𝔄 𝓗 t = t.2.2.1 := rfl
@[simp] theorem πdη_apply (t : HJet 𝔄 𝓗) : πdη 𝔄 𝓗 t = t.2.2.2 := rfl

end Jet

/-! ### Coefficients, slots and the variation covector -/

section Covector

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The kinetic coefficient `v(e) g^{μν}(e)`. -/
def c0 (μ ν : Fin 4) (M : M4) : ℝ := volM M * ginv (show Mat from M) μ ν

theorem contDiffAt_c0 (μ ν : Fin 4) {M : M4} (hM : Matrix.det (show Mat from M) ≠ 0) :
    ContDiffAt ℝ ∞ (c0 μ ν) M :=
  (NativeGravityFirstJet.contDiffAt_volM hM).mul (contDiffAt_ginv μ ν hM)

/-- The derivative of the potential: `DV(H)[η] = 2λ_H(|H|² - v_H²)(Re⟨η, H⟩ + Re⟨H, η⟩)`. -/
def dpotL (Hx : 𝓗) : 𝓗 →L[ℝ] ℝ :=
  (D.lamH * (2 * (D.hermH Hx Hx - D.vH ^ 2))) • (D.hermH.flip Hx + D.hermH Hx)

theorem dpotL_apply (Hx η : 𝓗) :
    dpotL D Hx η = D.lamH * (2 * (D.hermH Hx Hx - D.vH ^ 2)) * (D.hermH η Hx + D.hermH Hx η) := by
  simp [dpotL]
  ring

/-- The slot values of the Higgs first variation at one point. -/
structure HSlots (𝔄 𝓗 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [NormedAddCommGroup 𝓗]
    [NormedSpace ℝ 𝓗] where
  /-- the coframe -/
  e : M4
  /-- the coframe direction map applied to the first jet component (`id` or the lift) -/
  L : M4 →L[ℝ] M4
  /-- the Higgs links `K_μ` -/
  K : Fin 4 → 𝓗
  /-- the Higgs value -/
  Hx : 𝓗
  /-- the shifted Higgs values `T_μ H` -/
  TH : Fin 4 → 𝓗
  /-- the link derivatives `Γ_μ = ρ_H ∘ Dexp(hA_μ)` -/
  Γ : Fin 4 → 𝔄 →L[ℝ] (𝓗 →L[ℝ] 𝓗)
  /-- the internal links `U_μ` -/
  U : Fin 4 → 𝓗 →L[ℝ] 𝓗
  /-- the link coefficients `B_μ` -/
  B : Fin 4 → 𝓗 →L[ℝ] 𝓗

/-- The variation `δK_μ[t] = Γ_μ(a_μ) T_μH + U_μ δη_μ + B_μ η` of the `μ`-th Higgs link. -/
def Qop (S : HSlots 𝔄 𝓗) (μ : Fin 4) : HJet 𝔄 𝓗 →L[ℝ] 𝓗 :=
  (ContinuousLinearMap.apply ℝ 𝓗 (S.TH μ)).comp ((S.Γ μ).comp
      ((ContinuousLinearMap.proj μ).comp (πa 𝔄 𝓗))) +
    (S.U μ).comp ((ContinuousLinearMap.proj μ).comp (πdη 𝔄 𝓗)) + (S.B μ).comp (πη 𝔄 𝓗)

theorem Qop_apply (S : HSlots 𝔄 𝓗) (μ : Fin 4) (t : HJet 𝔄 𝓗) :
    Qop S μ t = S.Γ μ (t.2.1 μ) (S.TH μ) + S.U μ (t.2.2.2 μ) + S.B μ t.2.2.1 := rfl

/-- **The Higgs variation covector**
`t ↦ -Σ_{μν}[D(v g^{μν})[L k] Re⟨K_μ,K_ν⟩ + v g^{μν}(Re⟨δK_μ,K_ν⟩ + Re⟨K_μ,δK_ν⟩)]
  - (Dv[L k] V(H) + v DV(H)[η])`. -/
def hcov (S : HSlots 𝔄 𝓗) : HJet 𝔄 𝓗 →L[ℝ] ℝ :=
  -(∑ μ, ∑ ν, (((fderiv ℝ (c0 μ ν) S.e).comp (S.L.comp (πk 𝔄 𝓗))).smulRight
        (D.hermH (S.K μ) (S.K ν)) +
      c0 μ ν S.e • ((D.hermH.flip (S.K ν)).comp (Qop S μ) + (D.hermH (S.K μ)).comp (Qop S ν)))) -
    (((fderiv ℝ volM S.e).comp (S.L.comp (πk 𝔄 𝓗))).smulRight (potential D S.Hx) +
      volM S.e • (dpotL D S.Hx).comp (πη 𝔄 𝓗))

theorem hcov_apply (S : HSlots 𝔄 𝓗) (t : HJet 𝔄 𝓗) :
    hcov D S t =
      -(∑ μ, ∑ ν, (fderiv ℝ (c0 μ ν) S.e (S.L t.1) * D.hermH (S.K μ) (S.K ν) +
        c0 μ ν S.e * (D.hermH (Qop S μ t) (S.K ν) + D.hermH (S.K μ) (Qop S ν t)))) -
      (fderiv ℝ volM S.e (S.L t.1) * potential D S.Hx + volM S.e * dpotL D S.Hx t.2.2.1) := by
  simp [hcov, ContinuousLinearMap.sum_apply, smul_eq_mul, mul_add]

variable {N : ℕ} [NeZero N]

/-- **The grid slots** of the Higgs first variation at the node `x` (`h = 1/N`). -/
def gridSlots (y : Grid N → Field 𝔄 𝓗 𝓢) (L : M4 →L[ℝ] M4) (x : Grid N) : HSlots 𝔄 𝓗 where
  e := coframeM y x
  L := L
  K μ := higgsLink D (N : ℝ)⁻¹ y x μ
  Hx := higgs y x
  TH μ := higgs y (x + unitVec N μ)
  Γ μ := D.ρHL.comp (fderiv ℝ exp ((N : ℝ)⁻¹ • gauge y μ x))
  U μ := D.ρH (exp ((N : ℝ)⁻¹ • gauge y μ x))
  B μ := (N : ℝ) • (D.ρH (exp ((N : ℝ)⁻¹ • gauge y μ x)) - 1)

/-- The record direction `v` read as a Higgs-sector jet `(ė, a, η, δ⁺η)` at the node `x`. -/
def genJet (v : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) : HJet 𝔄 𝓗 :=
  (coframeM v x, fun μ => gauge v μ x, higgs v x, fun μ => fwdDiff (N : ℝ)⁻¹ μ (higgs v) x)

end Covector

/-! ### The exact first variation of the Higgs row -/

section Variation

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable {N : ℕ} [NeZero N]

/-- **The Higgs row** `S_{H,h}(y) = h⁴ Σ_x 𝓛_{H,h}(y)(x)` of the native local action. -/
def higgsAct (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) : ℝ := h ^ 4 * ∑ x, higgsDensity D h y x

/-- The literal Higgs first variation `D S_{H,h}(y)[v]`, `h = 1/N`. -/
def higgsVar (N : ℕ) [NeZero N] (y v : Grid N → Field 𝔄 𝓗 𝓢) : ℝ :=
  deriv (fun s : ℝ => higgsAct D (N : ℝ)⁻¹ (y + s • v)) 0

theorem higgsDensity_eq (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) :
    higgsDensity D h y x =
      -(∑ μ, ∑ ν, c0 μ ν (coframeM y x) *
        D.hermH (higgsLink D h y x μ) (higgsLink D h y x ν)) -
      volM (coframeM y x) * potential D (higgs y x) := by
  simp only [higgsDensity, c0, Finset.mul_sum, mul_assoc]
  rfl

/-- The derivative of a Higgs link along a record line. -/
theorem hasDerivAt_higgsLink (y v : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4) :
    HasDerivAt (fun s : ℝ => higgsLink D (N : ℝ)⁻¹ (y + s • v) x μ)
      (Qop (gridSlots D y (ContinuousLinearMap.id ℝ M4) x) μ (genJet v x)) 0 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  set h : ℝ := (N : ℝ)⁻¹ with hh
  set A := gauge y μ x
  set a := gauge v μ x
  have hZ : HasDerivAt (fun s : ℝ => h • (A + s • a)) (h • a) 0 :=
    (NativeDirac.hasDerivAt_line A a).const_smul h
  have hE := NativeDirac.hasDerivAt_exp_comp hZ
  have hρ := D.ρHL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hE
  have hv := NativeDirac.hasDerivAt_line (higgs y (x + unitVec N μ)) (higgs v (x + unitVec N μ))
  have happ := hρ.clm_apply hv
  have hw := (happ.sub (NativeDirac.hasDerivAt_line (higgs y x) (higgs v x))).const_smul h⁻¹
  refine hw.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · refine Eventually.of_forall fun s => ?_
    simp only [higgsLink, NativeScaling.higgsLink, Function.comp_apply, NativeDirac.gauge_add_smul,
      NativeDirac.higgs_add_smul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Data.ρHL_apply]
    rfl
  · simp only [Function.comp_apply, Qop_apply, gridSlots, genJet, zero_smul, add_zero,
      ContinuousLinearMap.comp_apply, Data.ρHL_apply, ShiftedJetAction.fwdDiff,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, hh, inv_inv]
    simp only [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hN, one_smul, map_sub, map_smul]
    abel

/-- The derivative of the potential along a line: `d/ds V(H + s η)|₀ = DV(H)[η]`. -/
theorem hasDerivAt_potential (Hx η : 𝓗) :
    HasDerivAt (fun s : ℝ => potential D (Hx + s • η)) (dpotL D Hx η) 0 := by
  have hl := NativeDirac.hasDerivAt_line Hx η
  have hq := (D.hermH.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl).clm_apply hl
  have hp := ((hq.sub_const (D.vH ^ 2)).pow 2).const_mul D.lamH
  refine hp.congr_deriv ?_
  simp only [Function.comp_apply, zero_smul, add_zero, dpotL_apply]
  ring

theorem coframeM_add_smul (y v : Grid N → Field 𝔄 𝓗 𝓢) (s : ℝ) (x : Grid N) :
    coframeM (y + s • v) x = coframeM y x + s • coframeM v x := rfl

/-- **The exact first variation of the Higgs density** at a node along any record direction, on
the nondegenerate coframe chart. -/
theorem hasDerivAt_higgsDensity (y v : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N)
    (hdet : Matrix.det (show Mat from coframeM y x) ≠ 0) :
    HasDerivAt (fun s : ℝ => higgsDensity D (N : ℝ)⁻¹ (y + s • v) x)
      (hcov D (gridSlots D y (ContinuousLinearMap.id ℝ M4) x) (genJet v x)) 0 := by
  have hc : ∀ μ ν, HasDerivAt (fun s : ℝ => c0 μ ν (coframeM y x + s • coframeM v x))
      (fderiv ℝ (c0 μ ν) (coframeM y x) (coframeM v x)) 0 := fun μ ν =>
    NativeDirac.hasDerivAt_comp_line ((contDiffAt_c0 μ ν hdet).differentiableAt (by simp)) _
  have hvol : HasDerivAt (fun s : ℝ => volM (coframeM y x + s • coframeM v x))
      (fderiv ℝ volM (coframeM y x) (coframeM v x)) 0 :=
    NativeDirac.hasDerivAt_comp_line
      ((NativeGravityFirstJet.contDiffAt_volM hdet).differentiableAt (by simp)) _
  have hK := fun μ => hasDerivAt_higgsLink D y v x μ
  have hherm : ∀ μ ν, HasDerivAt (fun s : ℝ => D.hermH (higgsLink D (N : ℝ)⁻¹ (y + s • v) x μ)
      (higgsLink D (N : ℝ)⁻¹ (y + s • v) x ν))
      (D.hermH (Qop (gridSlots D y (ContinuousLinearMap.id ℝ M4) x) μ (genJet v x))
          (higgsLink D (N : ℝ)⁻¹ y x ν) +
        D.hermH (higgsLink D (N : ℝ)⁻¹ y x μ)
          (Qop (gridSlots D y (ContinuousLinearMap.id ℝ M4) x) ν (genJet v x))) 0 := by
    intro μ ν
    have := (D.hermH.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hK μ)).clm_apply (hK ν)
    simpa only [Function.comp_apply, zero_smul, add_zero] using this
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => (hc μ ν).mul (hherm μ ν)
  have hpot := hvol.mul (hasDerivAt_potential D (higgs y x) (higgs v x))
  have htot := hsum.neg.sub hpot
  refine htot.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_) |>.congr_deriv ?_
  · simp only [higgsDensity_eq, coframeM_add_smul, NativeDirac.higgs_add_smul, Pi.add_apply,
      Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, Pi.mul_apply]
  · rw [hcov_apply]
    simp only [zero_smul, add_zero]
    rfl

/-- **The exact first variation of the Higgs row** along any record direction:
`d/ds S_{H,h}(y + s v)|₀ = h⁴ Σ_x hcov(slots(x))[J_v(x)]`. -/
theorem hasDerivAt_higgsAct (y v : Grid N → Field 𝔄 𝓗 𝓢)
    (hdet : ∀ x, Matrix.det (show Mat from coframeM y x) ≠ 0) :
    HasDerivAt (fun s : ℝ => higgsAct D (N : ℝ)⁻¹ (y + s • v))
      (((N : ℝ)⁻¹) ^ 4 * ∑ x, hcov D (gridSlots D y (ContinuousLinearMap.id ℝ M4) x)
        (genJet v x)) 0 :=
  (HasDerivAt.fun_sum (u := Finset.univ) fun x _ =>
    hasDerivAt_higgsDensity D y v x (hdet x)).const_mul _

end Variation

/-! ### The Higgs variation along the nodal test record -/

section TestRecord

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open NativeDiracLimit (DTest testRec samp)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- **The sampled Higgs-sector test jet** `(k, a, η, δ⁺η)(x/N)`. -/
def sampleHJet (N : ℕ) [NeZero N] (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N) : HJet 𝔄 𝓗 :=
  (samp N τ.k.f x, samp N τ.a.f x, samp N τ.η.f x, fun μ => fwdDiff (N : ℝ)⁻¹ μ (samp N τ.η.f) x)

/-- **The continuum Higgs-sector test jet** `(k, a, η, ∂η)`. -/
def contHJet (τ : DTest 𝔄 𝓗 𝓢 W') (z : 𝕋) : HJet 𝔄 𝓗 :=
  (τ.k.f z, τ.a.f z, τ.η.f z, fun μ => τ.η.df μ z)

/-- The grid slots with the symmetric coframe lift as coframe direction map. -/
def liftSlots {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) : HSlots 𝔄 𝓗 :=
  gridSlots D y (liftL (coframeM y x)) x

theorem hcov_genJet_testRec {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N) :
    hcov D (gridSlots D y (ContinuousLinearMap.id ℝ M4) x) (genJet (testRec κ N y τ) x) =
      hcov D (liftSlots D y x) (sampleHJet N τ x) := by
  rw [hcov_apply, hcov_apply]
  rfl

theorem integral_pc_hcov {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W') :
    ∫ z, hcov D (pc (liftSlots D y) z) (pc (sampleHJet N τ) z) =
      ((N : ℝ)⁻¹) ^ 4 * ∑ x, hcov D (liftSlots D y x) (sampleHJet N τ x) :=
  NativeGravityFirstJet.integral_pc_real (fun x => hcov D (liftSlots D y x) (sampleHJet N τ x))

/-- **The Higgs variation along the nodal test record** as an integral of the reconstructed
covector field against the reconstructed sampled test jet. -/
theorem higgsVar_testRec_eq {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (τ : DTest 𝔄 𝓗 𝓢 W') (hdet : ∀ x, Matrix.det (show Mat from coframeM y x) ≠ 0) :
    higgsVar D N y (testRec κ N y τ) =
      ∫ z, hcov D (pc (liftSlots D y) z) (pc (sampleHJet N τ) z) := by
  rw [higgsVar, (hasDerivAt_higgsAct D y (testRec κ N y τ) hdet).deriv, integral_pc_hcov]
  exact congrArg _ (Finset.sum_congr rfl fun x _ => hcov_genJet_testRec D κ y τ x)

end TestRecord


/-! ### Convergence of the Higgs covector fields -/

section Convergence

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open NativeDiracLimit (DTest testRec samp)
open NativeDiracConv (CoHyp)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- **The Higgs hypotheses** (the conclusions of `prop:native-Higgs-compactness` after
extraction): `R^0 H_h → H` strongly in `L⁴` and the literal Higgs-link packet
`R^0 K_h → K` strongly in `L²` (`(N3)`; `K = D_A H` by the same proposition). -/
structure HiggsHyp (D : Data 𝔄 𝓗 𝓢) (y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢) where
  H₀ : 𝕋 → 𝓗
  hH : LpTendsto volume 4 (fun k => pc (higgs (y k))) H₀
  K₀ : Fin 4 → 𝕋 → 𝓗
  hK : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => higgsLink D (n k : ℝ)⁻¹ (y k) x μ))
    (K₀ μ)

variable (D : Data 𝔄 𝓗 𝓢)

/-- **The continuum slots**: `Γ = ρ_H`, `T_μH = H`, `U = 1`, `B_μ = ρ_H(A_μ)`, the Higgs links
replaced by their limit `K = D_A H` and the coframe direction map by the symmetric lift. -/
def contSlots (H : CoHyp n y) (P : HiggsHyp D y) (z : 𝕋) : HSlots 𝔄 𝓗 where
  e := H.e₀ z
  L := liftL (H.e₀ z)
  K μ := P.K₀ μ z
  Hx := P.H₀ z
  TH _ := P.H₀ z
  Γ _ := D.ρHL
  U _ := 1
  B μ := D.ρHL (H.A₀ μ z)

/-- **The continuum Higgs covector** `𝒟_H(y)[v] = ∫ hcov(contSlots)[J_v]`. -/
def contHiggsVar (H : CoHyp n y) (P : HiggsHyp D y) (τ : DTest 𝔄 𝓗 𝓢 W') : ℝ :=
  ∫ z, hcov D (contSlots D H P z) (contHJet τ z)


/-- The scaled connection is uniformly small: `h|A_μ| ≤ meshSup → 0`. -/
theorem norm_hA_le (μ : Fin 4) (k : ℕ) (x : Grid (n k)) :
    ‖(n k : ℝ)⁻¹ • gauge (y k) μ x‖ ≤ NativeCriticalGrid.meshSup (gauge (y k) μ) := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  exact NativeCriticalGrid.le_meshSup (N := n k) _ x

theorem tendsto_meshSup (H : CoHyp n y) (μ : Fin 4) :
    Tendsto (fun k => NativeCriticalGrid.meshSup (gauge (y k) μ)) atTop (𝓝 0) :=
  NativeCriticalGrid.tendsto_meshSup H.hn (A := fun k => gauge (y k) μ) (H.hA μ).memLp_lim
    (H.hA μ).tendsto

/-- Continuous functions of the scaled connection converge in measure to their value at `0` and
stay bounded. -/
theorem chart_link (H : CoHyp n y) (μ : Fin 4) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : 𝔄 → F} (hΦ : Continuous Φ) :
    TendstoInMeasure volume (fun k z => Φ (pc (fun x => (n k : ℝ)⁻¹ • gauge (y k) μ x) z))
      atTop (fun _ => Φ 0) ∧
      ∃ M, ∀ k z, ‖Φ (pc (fun x => (n k : ℝ)⁻¹ • gauge (y k) μ x) z)‖ ≤ M := by
  obtain ⟨R, hR⟩ := (tendsto_meshSup H μ).bddAbove_range
  have hb : ∀ k z, ‖pc (fun x => (n k : ℝ)⁻¹ • gauge (y k) μ x) z‖ ≤ R := fun k z =>
    (norm_hA_le μ k _).trans (hR (Set.mem_range_self k))
  have h0 : TendstoInMeasure volume (fun k => pc (fun x => (n k : ℝ)⁻¹ • gauge (y k) μ x))
      atTop 0 :=
    NativeDiracConv.tendstoInMeasure_zero_of_norm_le (tendsto_meshSup H μ)
      fun k z => norm_hA_le μ k _
  have := NativeDiracConv.tendstoInMeasure_comp_ball h0 hb hΦ.continuousOn
  simpa using this

/-- The link coefficients `B_μ = h⁻¹(ρ_H(e^{hA_μ}) - 1) → ρ_H(A_μ)` strongly in `L⁴`
(`eq:native-link-coeff`). -/
theorem lpTendsto_B (H : CoHyp n y) (μ : Fin 4) :
    LpTendsto volume 4
      (fun k => pc (fun x => (n k : ℝ) • (D.ρH (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) - 1)))
      (fun z => D.ρHL (H.A₀ μ z)) := by
  have h := NativeCriticalGrid.tendsto_linkCoeff H.hn D.ρHL (A := fun k => gauge (y k) μ)
    (H.hA μ).memLp_lim (H.hA μ).tendsto
  refine ⟨fun k => NativeYMIdentification.memLp_pc_gen _ 4,
    (H.hA μ).memLp_lim.continuousLinearMap_comp D.ρHL, ?_⟩
  refine h.congr fun k => ?_
  congr 1
  funext z
  simp only [pc, NativeCriticalGrid.linkCoeff, Pi.sub_apply, Data.ρHL_apply]
  rw [← map_smul, ← algHom_map_exp D.ρH D.ρH_cont]

theorem continuousOn_dc0 (H : CoHyp n y) (t : HJet 𝔄 𝓗) (μ ν : Fin 4) :
    ContinuousOn (fun M : M4 => fderiv ℝ (c0 μ ν) M (liftL M t.1)) H.Ke := fun M hM =>
  (NativeDiracConvergence.continuousAt_fderiv_apply (contDiffAt_c0 μ ν (H.hKdet M hM))
    ((NativeGravityFirstJet.continuous_liftL.clm_apply continuous_const).continuousAt)
    ).continuousWithinAt

theorem continuousOn_dvol (H : CoHyp n y) (t : HJet 𝔄 𝓗) :
    ContinuousOn (fun M : M4 => fderiv ℝ volM M (liftL M t.1)) H.Ke := fun M hM =>
  (NativeDiracConvergence.continuousAt_fderiv_apply
    (NativeGravityFirstJet.contDiffAt_volM (H.hKdet M hM))
    ((NativeGravityFirstJet.continuous_liftL.clm_apply continuous_const).continuousAt)
    ).continuousWithinAt

theorem continuousOn_c0 (H : CoHyp n y) (μ ν : Fin 4) : ContinuousOn (c0 μ ν) H.Ke := fun M hM =>
  (contDiffAt_c0 μ ν (H.hKdet M hM)).continuousAt.continuousWithinAt

theorem continuousOn_vol (H : CoHyp n y) : ContinuousOn volM H.Ke := fun M hM =>
  (NativeGravityFirstJet.contDiffAt_volM (H.hKdet M hM)).continuousAt.continuousWithinAt

/-- Bounded chart coefficients times strongly `L¹`-convergent scalars. -/
theorem chart_mul (H : CoHyp n y) {Φ : M4 → ℝ} (hΦ : ContinuousOn Φ H.Ke) {s : ℕ → 𝕋 → ℝ} {s₀ : 𝕋 → ℝ}
    (hs : LpTendsto volume 1 s s₀) :
    LpTendsto volume 1 (fun k z => Φ (pc (coframeM (y k)) z) * s k z)
      (fun z => Φ (H.e₀ z) * s₀ z) := by
  have := NativeDiracConvergence.lpTendsto_chart_gen (p := 1) ENNReal.one_ne_top H.hKe hΦ
    (fun k => (stronglyMeasurable_pc (fun x => Φ (coframeM (y k) x))).aestronglyMeasurable)
    H.tendstoInMeasure_e (fun k z => H.hval k _) H.e₀_mem (ContinuousLinearMap.mul ℝ ℝ) hs
  exact this.congr (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)

namespace HiggsHyp

variable {D} (P : HiggsHyp D y)

theorem hH2 : LpTendsto volume 2 (fun k => pc (higgs (y k))) P.H₀ :=
  P.hH.mono two_ne_zero (by norm_num)

theorem hTH (H : CoHyp n y) (μ : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x => higgs (y k) (x + unitVec (n k) μ))) P.H₀ :=
  P.hH2.shift H.hn (by norm_num) μ

/-- **The Higgs-link variations converge strongly in `L²`** (fixed test jet `t`):
`Γ_μ(a_μ) T_μH + U_μ δη_μ + B_μ η → ρ_H(a_μ)H + δη_μ + ρ_H(A_μ)η`. -/
theorem lpTendsto_Q (H : CoHyp n y) (t : HJet 𝔄 𝓗) (μ : Fin 4) :
    LpTendsto volume 2 (fun k z => Qop (pc (liftSlots D (y k)) z) μ t)
      (fun z => Qop (contSlots D H P z) μ t) := by
  -- the gauge-direction term
  obtain ⟨hβ1, M1, hM1⟩ := chart_link H μ (Φ := fun X : 𝔄 => D.ρHL (fderiv ℝ exp X (t.2.1 μ)))
    (D.ρHL.continuous.comp (NativeDiracConvergence.continuous_fderiv_exp.clm_apply
      continuous_const))
  have T1 := LpProductContinuity.LpTendsto.coeff (p := 2) (by norm_num)
    (fun k => (stronglyMeasurable_pc (fun x => D.ρHL (fderiv ℝ exp ((n k : ℝ)⁻¹ •
      gauge (y k) μ x) (t.2.1 μ)))).aestronglyMeasurable)
    hβ1 (fun k => Eventually.of_forall fun z => hM1 k z) (P.hTH H μ)
  -- the Higgs-difference term
  obtain ⟨hβ2, M2, hM2⟩ := chart_link H μ (Φ := fun X : 𝔄 => D.ρHL (exp X))
    (D.ρHL.continuous.comp NativeDiracConvergence.contDiff_exp'.continuous)
  have T2 := LpProductContinuity.LpTendsto.coeff (p := 2) (by norm_num)
    (fun k => (stronglyMeasurable_pc (fun x => D.ρHL (exp ((n k : ℝ)⁻¹ •
      gauge (y k) μ x)))).aestronglyMeasurable)
    hβ2 (fun k => Eventually.of_forall fun z => hM2 k z)
    (LpTendsto.const (memLp_const (t.2.2.2 μ)))
  -- the link-coefficient term
  have T3 := ((lpTendsto_B (D := D) H μ).clm (ContinuousLinearMap.apply ℝ 𝓗 t.2.2.1)).mono
    two_ne_zero (by norm_num)
  refine ((T1.add T2).add T3).congr (fun k => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply, Qop_apply, liftSlots, gridSlots, pc, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, Data.ρHL_apply]
  · simp only [Pi.add_apply, Qop_apply, contSlots, ContinuousLinearMap.apply_apply,
      NativeDiracConvergence.fderiv_exp_zero, ContinuousLinearMap.id_apply, exp_zero,
      Data.ρHL_apply, map_one]

/-- The quartic potential converges strongly in `L¹`. -/
theorem lpTendsto_potential :
    LpTendsto volume 1 (fun k z => potential D (pc (higgs (y k)) z))
      (fun z => potential D (P.H₀ z)) := by
  have hq := LpTendsto.bilin (p := 4) (q := 4) (r := 2) D.hermH P.hH P.hH
  have hr := hq.sub (LpTendsto.const (memLp_const (D.vH ^ 2)))
  have hs := (LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℝ) hr
    hr).const_smul D.lamH
  refine hs.congr (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · simp only [potential, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ContinuousLinearMap.mul_apply',
      sq]
  · simp only [potential, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ContinuousLinearMap.mul_apply',
      sq]

/-- The derivative of the potential at a fixed direction converges strongly in `L¹`. -/
theorem lpTendsto_dpot (η : 𝓗) :
    LpTendsto volume 1 (fun k z => dpotL D (pc (higgs (y k)) z) η)
      (fun z => dpotL D (P.H₀ z) η) := by
  have hq := LpTendsto.bilin (p := 4) (q := 4) (r := 2) D.hermH P.hH P.hH
  have hr := hq.sub (LpTendsto.const (memLp_const (D.vH ^ 2)))
  have hw := (P.hH2.clm (D.hermH η)).add (P.hH2.clm (D.hermH.flip η))
  have hs := (LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℝ) hr
    hw).const_smul (D.lamH * 2)
  refine hs.congr (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · simp only [dpotL_apply, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
      ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply]
    ring
  · simp only [dpotL_apply, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
      ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply]
    ring

/-- **The Higgs covector fields converge strongly in `L¹`.** -/
theorem lpTendsto_hcov (H : CoHyp n y) :
    LpTendsto volume 1 (fun k z => hcov D (pc (liftSlots D (y k)) z))
      (fun z => hcov D (contSlots D H P z)) := by
  refine WeakJetPairing.lpTendsto_clm_of_apply fun t => ?_
  have T1 : ∀ μ ν, LpTendsto volume 1
      (fun k z => fderiv ℝ (c0 μ ν) (pc (coframeM (y k)) z) (liftL (pc (coframeM (y k)) z) t.1) *
        D.hermH (pc (fun x => higgsLink D (n k : ℝ)⁻¹ (y k) x μ) z)
          (pc (fun x => higgsLink D (n k : ℝ)⁻¹ (y k) x ν) z))
      (fun z => fderiv ℝ (c0 μ ν) (H.e₀ z) (liftL (H.e₀ z) t.1) *
        D.hermH (P.K₀ μ z) (P.K₀ ν z)) := fun μ ν =>
    chart_mul H (continuousOn_dc0 H t μ ν)
      (LpTendsto.bilin (p := 2) (q := 2) (r := 1) D.hermH (P.hK μ) (P.hK ν))
  have T2 : ∀ μ ν, LpTendsto volume 1
      (fun k z => c0 μ ν (pc (coframeM (y k)) z) *
        (D.hermH (Qop (pc (liftSlots D (y k)) z) μ t)
            (pc (fun x => higgsLink D (n k : ℝ)⁻¹ (y k) x ν) z) +
          D.hermH (pc (fun x => higgsLink D (n k : ℝ)⁻¹ (y k) x μ) z)
            (Qop (pc (liftSlots D (y k)) z) ν t)))
      (fun z => c0 μ ν (H.e₀ z) * (D.hermH (Qop (contSlots D H P z) μ t) (P.K₀ ν z) +
          D.hermH (P.K₀ μ z) (Qop (contSlots D H P z) ν t))) := fun μ ν =>
    chart_mul H (continuousOn_c0 H μ ν)
      ((LpTendsto.bilin (p := 2) (q := 2) (r := 1) D.hermH (P.lpTendsto_Q H t μ) (P.hK ν)).add
        (LpTendsto.bilin (p := 2) (q := 2) (r := 1) D.hermH (P.hK μ) (P.lpTendsto_Q H t ν)))
  have T3 := chart_mul H (continuousOn_dvol H t) (P.lpTendsto_potential (D := D))
  have T4 := chart_mul H (continuousOn_vol H) (P.lpTendsto_dpot (D := D) t.2.2.1)
  have hsum := NativeDiracConv.lpTendsto_finset_sum (p := 1) Finset.univ fun μ _ =>
    NativeDiracConv.lpTendsto_finset_sum (p := 1) Finset.univ fun ν _ => (T1 μ ν).add (T2 μ ν)
  refine (hsum.neg.sub (T3.add T4)).congr (fun k => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, hcov_apply]
    rfl
  · simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, hcov_apply]
    rfl

end HiggsHyp

end Convergence

/-! ### The Higgs sector of `eq:native-all-sector-limit` -/

section Main

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open NativeDiracLimit (DTest testRec samp)
open NativeDiracConv (CoHyp)
open NativeSpinorVariation (norm_f_le' norm_df_le' norm_f_sub_le' norm_df_sub_le'
  norm_samp_sub_le norm_sampD_sub_le)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

theorem continuous_contHJet (τ : DTest 𝔄 𝓗 𝓢 W') : Continuous (contHJet τ) :=
  continuous_prodMk.2 ⟨τ.k.f.continuous, continuous_prodMk.2 ⟨τ.a.f.continuous,
    continuous_prodMk.2 ⟨τ.η.f.continuous, continuous_pi fun μ => (τ.η.df μ).continuous⟩⟩⟩

theorem norm_contHJet_le (τ : DTest 𝔄 𝓗 𝓢 W') (z : 𝕋) : ‖contHJet τ z‖ ≤ τ.norm :=
  norm_prod_le_iff.2 ⟨(norm_f_le' _ z).trans τ.k_le, norm_prod_le_iff.2
    ⟨(norm_f_le' _ z).trans τ.a_le, norm_prod_le_iff.2 ⟨(norm_f_le' _ z).trans τ.η_le,
      (norm_df_le' _ z).trans τ.η_le⟩⟩⟩

theorem norm_contHJet_sub_le (τ : DTest 𝔄 𝓗 𝓢 W') (z z' : 𝕋) :
    ‖contHJet τ z - contHJet τ z'‖ ≤ τ.norm * dist z z' := by
  have hd := dist_nonneg (x := z) (y := z')
  have m : ∀ {a : ℝ}, a ≤ τ.norm → a * dist z z' ≤ τ.norm * dist z z' := fun h =>
    mul_le_mul_of_nonneg_right h hd
  exact norm_prod_le_iff.2 ⟨(norm_f_sub_le' _ z z').trans (m τ.k_le), norm_prod_le_iff.2
    ⟨(norm_f_sub_le' _ z z').trans (m τ.a_le), norm_prod_le_iff.2
      ⟨(norm_f_sub_le' _ z z').trans (m τ.η_le), (norm_df_sub_le' _ z z').trans (m τ.η_le)⟩⟩⟩

/-- **Test-jet consistency**: the raw reconstruction of the sampled Higgs test jet is uniformly
within `3/N ‖v‖_{C²}` of the continuum Higgs test jet. -/
theorem norm_pc_sampleHJet_sub_le {N : ℕ} [NeZero N] (τ : DTest 𝔄 𝓗 𝓢 W') (z : 𝕋) :
    ‖pc (sampleHJet N τ) z - contHJet τ z‖ ≤ 3 * (N : ℝ)⁻¹ * τ.norm := by
  have hN : (0 : ℝ) ≤ 3 * (N : ℝ)⁻¹ := by positivity
  have m : ∀ {a : ℝ}, a ≤ τ.norm → 3 * (N : ℝ)⁻¹ * a ≤ 3 * (N : ℝ)⁻¹ * τ.norm := fun h =>
    mul_le_mul_of_nonneg_left h hN
  exact norm_prod_le_iff.2 ⟨(norm_samp_sub_le _ z).trans (m τ.k_le), norm_prod_le_iff.2
    ⟨(norm_samp_sub_le _ z).trans (m τ.a_le), norm_prod_le_iff.2
      ⟨(norm_samp_sub_le _ z).trans (m τ.η_le), (norm_sampD_sub_le _ z).trans (m τ.η_le)⟩⟩⟩

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}
variable (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- **Higgs sector of `eq:native-all-sector-limit`** (`prop:native-Higgs-compactness`
transported to the first variation of the native action).  Under the coframe/connection
hypotheses `CoHyp` and the Higgs hypotheses `HiggsHyp` (strong `L⁴` Higgs and strong `L²`
Higgs-link convergence), the literal first variation of the Higgs row along the nodal test record
`𝓘_h v` — coframe (through the symmetric lift), gauge (through the internal links
`ρ_H(e^{hA})`) and Higgs directions — converges to the continuum Higgs covector **uniformly on the
`C²` test ball**: for every `ε > 0`, eventually
`|D S_{H,h}(y_h)[𝓘_h v] - 𝒟_H(y)[v]| ≤ ε ‖v‖_{C²}` for all tests `v`. -/
theorem native_Higgs_sector (H : CoHyp n y) (P : HiggsHyp D y) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W',
      |higgsVar D (n k) (y k) (testRec κ (n k) (y k) τ) - contHiggsVar D H P τ| ≤
        ε * τ.norm := by
  intro ε hε
  have hδ : Tendsto (fun k => 3 * ((n k : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using H.tendsto_h.const_mul 3
  have key := WeakJetPairing.weak_jet_variation (P.lpTendsto_hcov H)
    (Λ := fun _ _ => (0 : HJet 𝔄 𝓗 →L[ℝ] ℝ →L[ℝ] ℝ)) (Λ₀ := fun _ => 0)
    (LpTendsto.const (memLp_const (0 : HJet 𝔄 𝓗 →L[ℝ] ℝ →L[ℝ] ℝ)))
    (u := fun _ _ => (0 : ℝ)) (u₀ := fun _ => 0)
    (fun k => MemLp.zero) MemLp.zero (C := 0) (fun k => by simp)
    (fun g _ => by simp) (Θ := DTest 𝔄 𝓗 𝓢 W') DTest.norm contHJet continuous_contHJet
    norm_contHJet_le
    norm_contHJet_sub_le (fun k τ => pc (sampleHJet (n k) τ))
    (fun k τ => (stronglyMeasurable_pc _).aestronglyMeasurable) hδ
    (fun k => by positivity) (fun k τ z => norm_pc_sampleHJet_sub_le τ z) ε hε
  filter_upwards [key] with k hk τ
  have hdet : ∀ x, Matrix.det (show Mat from coframeM (y k) x) ≠ 0 := fun x =>
    H.hKdet _ (H.hval k x)
  rw [higgsVar_testRec_eq D κ (y k) τ hdet]
  have h := hk τ
  simp only [ContinuousLinearMap.zero_apply, add_zero] at h
  exact h

end Main

/-! ### The limit covector is the continuum Higgs first variation -/

section Faithful

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open NativeDiracLimit (DTest)
open NativeDiracConv (CoHyp)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable (D : Data 𝔄 𝓗 𝓢)

/-- **The continuum Higgs density** `-v(e) g^{μν} Re⟨K_μ, K_ν⟩ - v(e) V(H)` with the covariant
gradient `K_μ = ∂_μH + ρ_H(A_μ) H`. -/
def contHiggsDens (e : M4) (A : Fin 4 → 𝔄) (Hx : 𝓗) (dH : Fin 4 → 𝓗) : ℝ :=
  -(∑ μ, ∑ ν, c0 μ ν e * D.hermH (dH μ + D.ρH (A μ) Hx) (dH ν + D.ρH (A ν) Hx)) -
    volM e * potential D Hx

/-- The continuum slots of the fields `(e, A, H, ∂H)`. -/
def slotsOf (e : M4) (A : Fin 4 → 𝔄) (Hx : 𝓗) (dH : Fin 4 → 𝓗) : HSlots 𝔄 𝓗 where
  e := e
  L := liftL e
  K μ := dH μ + D.ρHL (A μ) Hx
  Hx := Hx
  TH _ := Hx
  Γ _ := D.ρHL
  U _ := 1
  B μ := D.ρHL (A μ)

/-- **The pointwise continuum Higgs first variation**: along the lifted test line
`(e + s lift(e, k), A + s a, H + s η, ∂H + s ∂η)` the derivative of the continuum Higgs density is
the covector `hcov` at the continuum slots, evaluated at the test jet `(k, a, η, ∂η)`. -/
theorem hasDerivAt_contHiggsDens (e : M4) (A : Fin 4 → 𝔄) (Hx : 𝓗) (dH : Fin 4 → 𝓗)
    (t : HJet 𝔄 𝓗) (he : Matrix.det (show Mat from e) ≠ 0) :
    HasDerivAt (fun s : ℝ => contHiggsDens D (e + s • liftL e t.1) (A + s • t.2.1)
        (Hx + s • t.2.2.1) (dH + s • t.2.2.2))
      (hcov D (slotsOf D e A Hx dH) t) 0 := by
  have hc : ∀ μ ν, HasDerivAt (fun s : ℝ => c0 μ ν (e + s • liftL e t.1))
      (fderiv ℝ (c0 μ ν) e (liftL e t.1)) 0 := fun μ ν =>
    NativeDirac.hasDerivAt_comp_line ((contDiffAt_c0 μ ν he).differentiableAt (by simp)) _
  have hvol : HasDerivAt (fun s : ℝ => volM (e + s • liftL e t.1))
      (fderiv ℝ volM e (liftL e t.1)) 0 :=
    NativeDirac.hasDerivAt_comp_line
      ((NativeGravityFirstJet.contDiffAt_volM he).differentiableAt (by simp)) _
  have hK : ∀ μ, HasDerivAt (fun s : ℝ => (dH + s • t.2.2.2) μ +
      D.ρH ((A + s • t.2.1) μ) (Hx + s • t.2.2.1)) (Qop (slotsOf D e A Hx dH) μ t) 0 := by
    intro μ
    have h1 := NativeDirac.hasDerivAt_line (dH μ) (t.2.2.2 μ)
    have h2 := D.ρHL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (NativeDirac.hasDerivAt_line (A μ)
      (t.2.1 μ))
    have h3 := h2.clm_apply (NativeDirac.hasDerivAt_line Hx t.2.2.1)
    refine (h1.add h3).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_) |>.congr_deriv ?_
    · simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, Data.ρHL_apply]
    · simp only [Qop_apply, slotsOf, Function.comp_apply, zero_smul, add_zero,
        ContinuousLinearMap.one_apply]
      abel
  have hherm : ∀ μ ν, HasDerivAt (fun s : ℝ => D.hermH ((dH + s • t.2.2.2) μ +
      D.ρH ((A + s • t.2.1) μ) (Hx + s • t.2.2.1)) ((dH + s • t.2.2.2) ν +
      D.ρH ((A + s • t.2.1) ν) (Hx + s • t.2.2.1)))
      (D.hermH (Qop (slotsOf D e A Hx dH) μ t) (dH ν + D.ρH (A ν) Hx) +
        D.hermH (dH μ + D.ρH (A μ) Hx) (Qop (slotsOf D e A Hx dH) ν t)) 0 := by
    intro μ ν
    have := (D.hermH.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hK μ)).clm_apply (hK ν)
    simpa only [Function.comp_apply, zero_smul, add_zero, Pi.add_apply, Pi.smul_apply,
      Pi.zero_apply] using this
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => (hc μ ν).mul (hherm μ ν)
  have hpot := hvol.mul (hasDerivAt_potential D Hx t.2.2.1)
  refine (hsum.neg.sub hpot).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    |>.congr_deriv ?_
  · simp only [contHiggsDens, Pi.neg_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply,
      Pi.smul_apply]
  · rw [hcov_apply]
    simp only [zero_smul, add_zero, slotsOf, Data.ρHL_apply]

/-- **The limit Higgs covector is the integrated continuum Higgs first variation**: if the limit
Higgs-link packet is the covariant gradient, `K_μ = ∂_μH + ρ_H(A_μ)H` (the identification
`K = D_A H` of `prop:native-Higgs-compactness`, with `∂H` the weak derivative), then
`𝒟_H(y)[v] = ∫ d/ds|₀ 𝓛_H(e + s lift(e,k), A + s a, H + s η, ∂H + s ∂η)`. -/
theorem contHiggsVar_eq_integral_deriv {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢} (H : CoHyp n y) (P : HiggsHyp D y)
    (dH : Fin 4 → 𝕋 → 𝓗)
    (hKid : ∀ᵐ z ∂(volume : Measure 𝕋), ∀ μ, P.K₀ μ z = dH μ z + D.ρH (H.A₀ μ z) (P.H₀ z))
    (τ : DTest 𝔄 𝓗 𝓢 W') :
    contHiggsVar D H P τ = ∫ z, deriv (fun s : ℝ => contHiggsDens D
      (H.e₀ z + s • liftL (H.e₀ z) (contHJet τ z).1) ((fun μ => H.A₀ μ z) + s • (contHJet τ z).2.1)
      (P.H₀ z + s • (contHJet τ z).2.2.1) ((fun μ => dH μ z) + s • (contHJet τ z).2.2.2)) 0 := by
  refine integral_congr_ae ?_
  filter_upwards [H.e₀_mem, hKid] with z hz hk
  rw [(hasDerivAt_contHiggsDens D (H.e₀ z) (fun μ => H.A₀ μ z) (P.H₀ z) (fun μ => dH μ z)
    (contHJet τ z) (H.hKdet _ hz)).deriv]
  have hS : contSlots D H P z = slotsOf D (H.e₀ z) (fun μ => H.A₀ μ z) (P.H₀ z)
      (fun μ => dH μ z) := by
    simp only [contSlots, slotsOf, Data.ρHL_apply, hk]
  rw [hS]

end Faithful

/-! ### The Higgs hypotheses from `(N3)` by `prop:native-Higgs-compactness` -/

section Extraction

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {r : ℕ} [NeZero r]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]

/-- The native Higgs link of `NativeDensity` is the literal packet `NativeHiggs.higgsLink` of
`prop:native-Higgs-compactness` (`ρ_H(e^{hA}) = e^{h ρ_H(A)}`). -/
theorem higgsLink_eq_native (D : Data 𝔄 (EuclideanSpace ℝ (Fin r)) 𝓢) {N : ℕ} [NeZero N]
    (y : Grid N → Field 𝔄 (EuclideanSpace ℝ (Fin r)) 𝓢) (x : Grid N) (μ : Fin 4) :
    NativeHiggs.higgsLink N D.ρHL (fun x μ => gauge y μ x) (higgs y) μ x =
      higgsLink D (N : ℝ)⁻¹ y x μ := by
  simp only [NativeHiggs.higgsLink, higgsLink, NativeScaling.higgsLink, inv_inv, Data.ρHL_apply]
  rw [← map_smul, ← algHom_map_exp D.ρH D.ρH_cont]
  rfl

/-- **The Higgs hypotheses from `(N3)`** (`prop:native-Higgs-compactness`, applied to the native
records): if `R^0 A_h → A` strongly in `L⁴`, the internal links `ρ_H(e^{hA})` are unitary,
`sup_h ‖H_h‖_{2,h} < ∞` and the literal Higgs-link packet `R^0 K_h → K` strongly in `L²`, then
after extraction `HiggsHyp` holds with the same `K`, and moreover `R^0 D⁺_μ H_h → K_μ - ρ_H(A_μ)H`
strongly in `L²` (the identification `K = D_A H`). -/
theorem exists_higgsHyp {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin r)) 𝓢}
    (D : Data 𝔄 (EuclideanSpace ℝ (Fin r)) 𝓢) (hn : Tendsto n atTop atTop)
    {A₀ : Fin 4 → 𝕋 → 𝔄} (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (gauge (y k) μ)) (A₀ μ))
    (hU : ∀ k x μ (v : EuclideanSpace ℝ (Fin r)),
      ‖exp ((n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)) v‖ = ‖v‖)
    {BH : ℝ} (hH : ∀ k, TorusPiecewiseConstantTranslation.gridNorm (higgs (y k)) ≤ BH)
    {K₀ : Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin r)}
    (hK : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => higgsLink D (n k : ℝ)⁻¹ (y k) x μ))
      (K₀ μ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : HiggsHyp D (fun k => y (φ k)), P.K₀ = K₀ ∧
      ∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y (φ k)))))
        (fun z => K₀ μ z - D.ρHL (A₀ μ z) (P.H₀ z)) := by
  have hK' : ∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.higgsLink (n k) D.ρHL
      (fun x μ => gauge (y k) μ x) (higgs (y k)) μ)) (K₀ μ) := by
    intro μ
    refine (hK μ).congr (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall
      fun z => rfl)
    simp only [pc, higgsLink_eq_native]
  obtain ⟨φ, hφ, H₀, -, h4, hD, -⟩ := NativeHiggs.native_Higgs_compactness hn D.ρHL
    (A := fun k x μ => gauge (y k) μ x) hA hU hH hK'
  exact ⟨φ, hφ, ⟨H₀, h4, K₀, fun μ => (hK μ).comp_strictMono hφ⟩, rfl, hD⟩

end Extraction
end

end RenewalGeometry.NativeHiggsVar
