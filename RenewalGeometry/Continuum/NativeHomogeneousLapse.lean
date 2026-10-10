/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeStressEulerRow

/-!
# Homogeneous native fields: curvature, stress and Euler rows of lapse-FLRW profiles

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty` (last
sentence) and `prop:homogeneous`: the computations needed to transport the homogeneous
Einstein–Higgs family into the native slab gauges (harmonic time, adapted coframe).

For a homogeneous native field `Y(y) = F(y⁰)` with coframe `e = diag(N, a, a, a)` (lapse `N`,
scale factor `a`), `A ≡ 0`, Higgs profile `h`, `Ψ ≡ 0`, `Ψ̄ ≡ 0`:

* the metric `g = eᵀηe = diag(-N², a², a², a²)` and its jets in the conventions of
  `HarmonicDefect` (`chr_lapse`, `dchr_lapse`, `ricci_lapse_*`, `einstein_lapse_*`): `G₀₀ = 3a'²/a²`,
  `Gₖₖ = -(2aa''/N² - 2aa'N'/N³ + a'²/N²)`, off-diagonal `0`;
* the harmonic defect `C^l = g^{αβ}Γ^l_{αβ}`: `C⁰ = (3a'/a - N'/N)/N²`, `Cᵏ = 0`
  (`cUp_lapse`), so the coordinates are harmonic iff `N'/N = 3a'/a` (harmonic time `N ∝ a³`);
* **`coframe_row_EH`** (any `Data`): for an Einstein–Higgs native field (`A ≡ 0`, `Ψ ≡ 0`,
  `Ψ̄ ≡ 0`) the coframe row in **every** coframe direction `δ` (metric and local Lorentz directions
  alike) is `einsteinCov(e)[δ] + (v/2)T_H^{ab}δg_{ab}`, `δg = metricVarM(e, δ)`;
* the homogeneous profile field `profY N a h` (`Profiles`: smooth, `N, a > 0`), its jets
  (`jet1_profY`, `dF_profY`, `ddF_profY`, `ginvOf_profY`), its Higgs stress (`higgsStressN_profY`),
  its Einstein residual (`einsteinRes_profY`: diagonal, with the Friedmann residual `fried0` and the
  spatial residual `friedK`) and its covariant wave operator (`waveN_profY`);
* **`native_euler_profile`**: if `fried0 = friedK = 0` and the Klein–Gordon relation hold at `z⁰`, the
  native Euler covector of the profile field vanishes on every direction with vanishing gauge part
  (all coframe directions, Higgs, spinor and co-spinor directions).
-/

open Finset

namespace RenewalGeometry.HomogeneousNative

open HarmonicDefect EHJetVariation

noncomputable section

/-! ### The lapse-FLRW metric jet -/

/-- The metric `diag(-N², a², a², a²)`. -/
def gV (N a : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => if i = j then (if i = 0 then -(N ^ 2) else a ^ 2) else 0

/-- The inverse metric `diag(-N⁻², a⁻², a⁻², a⁻²)`. -/
def giV (N a : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => if i = j then (if i = 0 then -(N ^ 2)⁻¹ else (a ^ 2)⁻¹) else 0

/-- `∂_c g_{ij}`: only `∂₀g₀₀ = -2NN'` and `∂₀gₖₖ = 2aa'`. -/
def dgV (N N' a a' : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun c i j => if c = 0 ∧ i = j then (if i = 0 then -(2 * N * N') else 2 * a * a') else 0

/-- `∂_d∂_c g_{ij}`: only `∂₀²g₀₀ = -2(N'² + NN'')` and `∂₀²gₖₖ = 2(a'² + aa'')`. -/
def ddgV (N N' N'' a a' a'' : ℝ) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun d c i j => if d = 0 ∧ c = 0 ∧ i = j then
    (if i = 0 then -(2 * (N' ^ 2 + N * N'')) else 2 * (a' ^ 2 + a * a'')) else 0

/-- The Christoffel symbols `Γ⁰₀₀ = N'/N`, `Γ⁰ₖₖ = aa'/N²`, `Γᵏ₀ₖ = Γᵏₖ₀ = a'/a`. -/
def GamV (N N' a a' : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ := fun c i j =>
  if c = 0 then (if i = 0 ∧ j = 0 then N' / N else if i = j then a * a' / N ^ 2 else 0)
  else (if (i = 0 ∧ j = c) ∨ (j = 0 ∧ i = c) then a' / a else 0)

/-- `∂_dΓ^c_{ij}` (only `d = 0`). -/
def DGamV (N N' N'' a a' a'' : ℝ) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun d c i j =>
  if d = 0 then
    (if c = 0 then
      (if i = 0 ∧ j = 0 then (N * N'' - N' ^ 2) / N ^ 2
       else if i = j then (a' ^ 2 + a * a'') / N ^ 2 - 2 * a * a' * N' / N ^ 3 else 0)
     else (if (i = 0 ∧ j = c) ∨ (j = 0 ∧ i = c) then a'' / a - a' ^ 2 / a ^ 2 else 0))
  else 0

theorem chr_lapse {N a : ℝ} (hN : N ≠ 0) (ha : a ≠ 0) (N' a' : ℝ) :
    chr (giV N a) (dgV N N' a a') = GamV N N' a a' := by
  funext c i j
  unfold chr giV dgV GamV
  fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four] <;> field_simp <;> ring

theorem dchr_lapse {N a : ℝ} (hN : N ≠ 0) (ha : a ≠ 0) (N' N'' a' a'' : ℝ) :
    dchr (giV N a) (dgV N N' a a') (ddgV N N' N'' a a' a'') = DGamV N N' N'' a a' a'' := by
  funext d c i j
  unfold dchr dchr1 dchr2 dginv giV dgV ddgV DGamV
  fin_cases d
  · fin_cases c <;> fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_four] <;> field_simp <;> ring
  all_goals simp


/-- The Ricci tensor of the lapse-FLRW jet: `R₀₀ = -3a''/a + 3a'N'/(aN)`,
`Rₖₖ = (aa'' + 2a'²)/N² - aa'N'/N³`, off-diagonal `0`. -/
def RicV (N N' a a' a'' : ℝ) : Fin 4 → Fin 4 → ℝ := fun i j =>
  if i = j then (if i = 0 then -(3 * a'' / a) + 3 * a' * N' / (a * N)
    else (a * a'' + 2 * a' ^ 2) / N ^ 2 - a * a' * N' / N ^ 3) else 0

theorem ricci_lapse {N a : ℝ} (hN : N ≠ 0) (ha : a ≠ 0) (N' N'' a' a'' : ℝ) :
    ricci (giV N a) (dgV N N' a a') (ddgV N N' N'' a a' a'') = RicV N N' a a' a'' := by
  funext i j
  unfold ricci
  rw [chr_lapse hN ha, dchr_lapse hN ha]
  unfold ricciJ GamV DGamV RicV
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four] <;> field_simp <;> ring

/-- The Einstein tensor of the lapse-FLRW jet: `G₀₀ = 3a'²/a²`,
`Gₖₖ = -(2aa''/N² - 2aa'N'/N³ + a'²/N²)`, off-diagonal `0`. -/
def EinV (N N' a a' a'' : ℝ) : Fin 4 → Fin 4 → ℝ := fun i j =>
  if i = j then (if i = 0 then 3 * a' ^ 2 / a ^ 2
    else -(2 * a * a'' / N ^ 2 - 2 * a * a' * N' / N ^ 3 + a' ^ 2 / N ^ 2)) else 0

theorem einstein_lapse {N a : ℝ} (hN : N ≠ 0) (ha : a ≠ 0) (N' N'' a' a'' : ℝ) :
    einstein (gV N a) (giV N a) (dgV N N' a a') (ddgV N N' N'' a a' a'') =
      EinV N N' a a' a'' := by
  funext i j
  unfold einstein
  rw [ricci_lapse hN ha]
  unfold trG RicV gV giV EinV
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four] <;> field_simp <;> ring

/-- The contravariant Einstein tensor of the lapse-FLRW jet. -/
theorem einsteinUp_lapse {N a : ℝ} (hN : N ≠ 0) (ha : a ≠ 0) (N' N'' a' a'' : ℝ) (μ ν : Fin 4) :
    einsteinUp (gV N a) (giV N a) (dgV N N' a a') (ddgV N N' N'' a a' a'') μ ν =
      giV N a μ μ * giV N a ν ν * EinV N N' a a' a'' μ ν := by
  unfold einsteinUp
  rw [einstein_lapse hN ha]
  rw [Finset.sum_eq_single μ (fun b _ hb => by simp [giV, Ne.symm hb]) (by simp)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by simp [giV, Ne.symm hb]) (by simp)]

/-- **The harmonic defect of the lapse-FLRW jet**: `C⁰ = (3a'/a - N'/N)/N²`, `Cᵏ = 0`. -/
theorem cUp_lapse {N a : ℝ} (hN : N ≠ 0) (ha : a ≠ 0) (N' a' : ℝ) (l : Fin 4) :
    cUp (giV N a) (chr (giV N a) (dgV N N' a a')) l =
      if l = 0 then (3 * a' / a - N' / N) / N ^ 2 else 0 := by
  rw [chr_lapse hN ha]
  unfold cUp giV GamV
  fin_cases l <;> simp [Fin.sum_univ_four] <;> field_simp <;> ring


/-! ### Einstein–Higgs native fields: all coframe rows -/

section EH

open NativeDensity NativeBosonicEuler NativeDiracEuler NativeStressEuler PalatiniEuler
  NativeMatterEuler EHFieldVariation
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic)
open NativeScaling (Mat eta metric)
open SobolevOpen (pd)
open scoped ContDiff

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- A component that vanishes identically has vanishing derivative. -/
theorem clm_fderiv_eq_zero {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (P : V →L[ℝ] W) {Y : R4 → V}
    (hY : Differentiable ℝ Y) (h0 : ∀ y, P (Y y) = 0) (z v : R4) : P (fderiv ℝ Y z v) = 0 := by
  have h1 : fderiv ℝ (fun y => P (Y y)) z = P.comp (fderiv ℝ Y z) :=
    (P.hasFDerivAt.comp z (hY z).hasFDerivAt).fderiv
  have h2 : (fun y => P (Y y)) = fun _ => 0 := funext h0
  rw [h2] at h1
  have := congrArg (fun T : R4 →L[ℝ] W => T v) h1
  simpa using this.symm

/-- The gauge projection of a native field value. -/
def projAll : Field 𝔄 𝓗 𝓢 →L[ℝ] (Fin 4 → 𝔄) :=
  (ContinuousLinearMap.fst ℝ (Fin 4 → 𝔄) _).comp (ContinuousLinearMap.snd ℝ Mat _)

/-- The spinor projection of a native field value. -/
def projPsi : Field 𝔄 𝓗 𝓢 →L[ℝ] 𝓢 :=
  (ContinuousLinearMap.fst ℝ 𝓢 _).comp ((ContinuousLinearMap.snd ℝ 𝓗 _).comp
    ((ContinuousLinearMap.snd ℝ (Fin 4 → 𝔄) _).comp (ContinuousLinearMap.snd ℝ Mat _)))

/-- The co-spinor projection of a native field value. -/
def projPsiBar : Field 𝔄 𝓗 𝓢 →L[ℝ] CoSpinor 𝓢 :=
  (ContinuousLinearMap.snd ℝ 𝓢 _).comp ((ContinuousLinearMap.snd ℝ 𝓗 _).comp
    ((ContinuousLinearMap.snd ℝ (Fin 4 → 𝔄) _).comp (ContinuousLinearMap.snd ℝ Mat _)))

/-- **Einstein–Higgs fields**: `A ≡ 0`, `Ψ ≡ 0`, `Ψ̄ ≡ 0`. -/
structure IsEH (Y : R4 → Field 𝔄 𝓗 𝓢) : Prop where
  A0 : ∀ y, (Y y).2.1 = 0
  Ψ0 : ∀ y, (Y y).2.2.2.1 = 0
  Ψb0 : ∀ y, (Y y).2.2.2.2 = 0

variable {D}

theorem IsEH.jet_A {Y : R4 → Field 𝔄 𝓗 𝓢} (h : IsEH Y) (hY : Differentiable ℝ Y) (y : R4)
    (μ : Fin 4) : ((jet1 Y y).2 μ).2.1 = 0 :=
  clm_fderiv_eq_zero (projAll (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) hY (fun y => h.A0 y) y _

theorem IsEH.jet_Ψ {Y : R4 → Field 𝔄 𝓗 𝓢} (h : IsEH Y) (hY : Differentiable ℝ Y) (y : R4)
    (μ : Fin 4) : ((jet1 Y y).2 μ).2.2.2.1 = 0 :=
  clm_fderiv_eq_zero (projPsi (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) hY (fun y => h.Ψ0 y) y _

theorem IsEH.jet_Ψb {Y : R4 → Field 𝔄 𝓗 𝓢} (h : IsEH Y) (hY : Differentiable ℝ Y) (y : R4)
    (μ : Fin 4) : ((jet1 Y y).2 μ).2.2.2.2 = 0 :=
  clm_fderiv_eq_zero (projPsiBar (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) hY (fun y => h.Ψb0 y) y _

/-- The Yang–Mills density vanishes on jets with vanishing gauge value and gauge jets. -/
theorem LYMc_eq_zero_of {wp : FJ 𝔄 𝓗 𝓢} (hA : wp.1.2.1 = 0) (hdA : ∀ μ, (wp.2 μ).2.1 = 0) :
    LYMc D wp = 0 := by
  have hF : ∀ μ ν, FA wp μ ν = 0 := by
    intro μ ν; unfold FA; simp [hA, hdA]
  unfold LYMc
  simp [hF]

/-- The Dirac density vanishes on jets with vanishing spinor and co-spinor values and jets. -/
theorem LDc_eq_zero_of {wp : FJ 𝔄 𝓗 𝓢} (hΨ : wp.1.2.2.2.1 = 0) (hΨb : wp.1.2.2.2.2 = 0)
    (hdΨ : ∀ μ, (wp.2 μ).2.2.2.1 = 0) (hdΨb : ∀ μ, (wp.2 μ).2.2.2.2 = 0) : LDc D wp = 0 := by
  have hD : ∀ μ, DPsi D wp μ = 0 := by
    intro μ; unfold DPsi; simp [hΨ, hdΨ]
  have hDb : ∀ μ, DPsiBar D wp μ = 0 := by
    intro μ; unfold DPsiBar; simp [hΨb, hdΨb]
  unfold LDc
  simp [hD, hDb, hΨ, hΨb]

theorem IsEH.chartF {Y : R4 → Field 𝔄 𝓗 𝓢} (hdet : ∀ z, 0 < ((Y z).1).det) (y : R4) :
    jet1 Y y ∈ (chartF : Set (FJ 𝔄 𝓗 𝓢)) := (hdet y).ne'

/-- **The coframe rows of an Einstein–Higgs field, in every coframe direction** (metric and local
Lorentz directions alike): `𝓔₀(Y)(z)[(δ, 0, 0, 0, 0)] = einsteinCov(e)[δ] + (v/2)T_H^{ab}δg_{ab}`
with `δg = metricVarM(e, δ)` — in particular the rows vanish in the local Lorentz directions
`δg = 0`. -/
theorem coframe_row_EH {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) {L : ℝ} (hL : 0 < L)
    (hper : IsLPeriodic L (eF Y)) (hdet : ∀ z, 0 < ((Y z).1).det) (hEH : IsEH Y) (z : R4)
    (δ : Mat) :
    contEuler (L0 D) Y z (coframeDir δ) =
      einsteinCov D.κ D.Λ (eF Y) z δ +
        volume (Y z).1 / 2 * ∑ a, ∑ b, raise (Y z).1 (higgsStressN D (jet1 Y z)) a b *
          metricVarM (Y z).1 δ a b := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  have hJU : ∀ y, jet1 Y y ∈ (chartF : Set (FJ 𝔄 𝓗 𝓢)) := fun y => (hdet y).ne'
  rw [contEuler_L0_split D hY hdet z δ,
    palatini_euler_period D.κ D.Λ hL (contDiff_eF hY) hper hdet]
  congr 1
  rw [contEuler_apply (L := Rr D) isOpen_chartF (contDiffOn_Rr D) hY hJU z]
  -- the jet-slot derivatives vanish
  have hnull : ∀ y (μ : Fin 4), fderiv ℝ (Rr D) (jet1 Y y)
      ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (coframeDir δ)) = 0 := by
    intro y μ
    have hd : (((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (coframeDir δ)) : FJ 𝔄 𝓗 𝓢) = jetDir μ δ := rfl
    rw [hd]
    refine fderiv_apply_of_line (differentiableAt_Rr D (hdet y).ne') ?_
    have hconst : ∀ t : ℝ, Rr D (jet1 Y y + t • (jetDir μ δ : FJ 𝔄 𝓗 𝓢)) = Rr D (jet1 Y y) := by
      intro t
      have hYM : LYMc D (jet1 Y y + t • (jetDir μ δ : FJ 𝔄 𝓗 𝓢)) = LYMc D (jet1 Y y) := by
        have hF : ∀ α β, FA (jet1 Y y + t • (jetDir μ δ : FJ 𝔄 𝓗 𝓢)) α β = FA (jet1 Y y) α β := by
          intro α β
          unfold FA
          rw [jd_1, jd_pA, jd_pA]
        unfold LYMc
        simp only [hF, jd_1]
      have hH : LHc D (jet1 Y y + t • (jetDir μ δ : FJ 𝔄 𝓗 𝓢)) = LHc D (jet1 Y y) := by
        have hK : ∀ α, KH D (jet1 Y y + t • (jetDir μ δ : FJ 𝔄 𝓗 𝓢)) α = KH D (jet1 Y y) α := by
          intro α
          unfold KH
          rw [jd_1, jd_pH]
        unfold LHc
        simp only [hK, jd_1]
      have hDc : ∀ wp : FJ 𝔄 𝓗 𝓢, wp.1 = (jet1 Y y).1 → (∀ l, (wp.2 l).2.2.2.1 = 0) →
          (∀ l, (wp.2 l).2.2.2.2 = 0) → LDc D wp = 0 := by
        intro wp h1 h2 h3
        refine LDc_eq_zero_of ?_ ?_ h2 h3
        · rw [h1]; exact hEH.Ψ0 y
        · rw [h1]; exact hEH.Ψb0 y
      have hD1 := hDc _ (jd_1 (jet1 Y y) μ δ t) (fun l => by rw [jd_pΨ]; exact hEH.jet_Ψ hYd y l)
        (fun l => by rw [jd_pΨb]; exact hEH.jet_Ψb hYd y l)
      have hD0 := hDc (jet1 Y y) rfl (fun l => hEH.jet_Ψ hYd y l) (fun l => hEH.jet_Ψb hYd y l)
      unfold Rr
      rw [hYM, hH, hD1, hD0]
    have hfun : (fun t : ℝ => Rr D (jet1 Y y + t • (jetDir μ δ : FJ 𝔄 𝓗 𝓢))) =
        fun _ => Rr D (jet1 Y y) := funext hconst
    rw [hfun]
    exact hasDerivAt_const _ _
  have hsum : ∑ μ, pd (fun z' => fderiv ℝ (Rr D) (jet1 Y z')
      ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (coframeDir δ))) μ z = 0 := by
    refine Finset.sum_eq_zero fun μ _ => ?_
    have h0 : (fun z' => fderiv ℝ (Rr D) (jet1 Y z')
        ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (coframeDir δ))) = fun _ => 0 :=
      funext fun z' => hnull z' μ
    rw [h0]
    unfold SobolevOpen.pd
    simp
  -- the value derivative: only the Higgs sector moves
  set wp := jet1 Y z with hwp
  set d : FJ 𝔄 𝓗 𝓢 := (coframeDir δ, 0) with hd
  have h2 : ∀ t : ℝ, (wp + t • d).2 = wp.2 := fun t => by
    rw [hd]
    funext μ
    show wp.2 μ + t • (0 : Field 𝔄 𝓗 𝓢) = wp.2 μ
    rw [smul_zero_field, add_zero]
  have h1 : ∀ t : ℝ, (wp + t • d).1 = wp.1 + t • coframeDir δ := fun t => by
    rw [hd, Prod.fst_add, Prod.smul_fst]
  have h12 : ∀ t : ℝ, (wp + t • d).1.2 = wp.1.2 := fun t => by
    rw [h1]
    show wp.1.2 + t • (0 : (Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢) = wp.1.2
    have h0 : t • (0 : (Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢) = 0 := by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · funext ν; simp
      · simp
      · simp
      · ext x; simp
    rw [h0, add_zero]
  have he : ∀ t : ℝ, (wp + t • d).1.1 = wp.1.1 + t • δ := fun t => by
    rw [h1]
    rfl
  have hK : ∀ (t : ℝ) μ, KH D (wp + t • d) μ = KH D wp μ := by
    intro t μ
    unfold KH
    rw [h12, h2]
  have hHd : ∀ t : ℝ, (wp + t • d).1.2.2.1 = wp.1.2.2.1 := fun t => by rw [h12]
  have hLH := hasDerivAt_LHc_coframe D wp d (hdet z).ne' δ he hK hHd
  have hw1 : wp.1 = Y z := rfl
  have hYMc : ∀ t : ℝ, LYMc D (wp + t • d) = 0 := by
    intro t
    refine LYMc_eq_zero_of ?_ ?_
    · rw [h12, hw1]; exact hEH.A0 z
    · intro μ; rw [h2]; exact hEH.jet_A hYd z μ
  have hDc : ∀ t : ℝ, LDc D (wp + t • d) = 0 := by
    intro t
    refine LDc_eq_zero_of ?_ ?_ ?_ ?_
    · rw [h12, hw1]; exact hEH.Ψ0 z
    · rw [h12, hw1]; exact hEH.Ψb0 z
    · intro μ; rw [h2]; exact hEH.jet_Ψ hYd z μ
    · intro μ; rw [h2]; exact hEH.jet_Ψb hYd z μ
  have hfun : (fun t : ℝ => Rr D (wp + t • d)) = fun t => LHc D (wp + t • d) := by
    funext t
    unfold Rr
    rw [hYMc, hDc]
    ring
  have hR : HasDerivAt (fun t : ℝ => Rr D (wp + t • d))
      (-(volume wp.1.1 / 2) * ∑ μ, ∑ ν, higgsStressN D wp μ ν * dgi wp.1.1 δ μ ν) 0 := by
    rw [hfun]; exact hLH
  have hmain := fderiv_apply_of_line (differentiableAt_Rr D (hdet z).ne') hR
  have hc := raise_contract wp.1.1 δ (higgsStressN D wp)
  have hfin : -(volume wp.1.1 / 2) * ∑ μ, ∑ ν, higgsStressN D wp μ ν * dgi wp.1.1 δ μ ν =
      volume wp.1.1 / 2 * ∑ a, ∑ b, raise wp.1.1 (higgsStressN D wp) a b *
        metricVarM wp.1.1 δ a b := by
    rw [← hc]
    ring
  exact (congrArg₂ (fun a b : ℝ => a - b) (hmain.trans hfin) hsum).trans (sub_zero _)

end EH

/-! ### Homogeneous profile fields -/

section Profile

open NativeDensity NativeBosonicEuler NativeDiracEuler NativeStressEuler PalatiniEuler
  NativeMatterEuler EHFieldVariation
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic)
open NativeScaling (Mat eta metric)
open SobolevOpen (pd)
open ActualJetSystem (ginvOf)
open scoped ContDiff

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The diagonal coframe `diag(N, a, a, a)`. -/
def diagE (N a : ℝ) : Mat := Matrix.diagonal ![N, a, a, a]

theorem diagE_apply (N a : ℝ) (i j : Fin 4) :
    diagE N a i j = if i = j then (if i = 0 then N else a) else 0 := by
  unfold diagE
  fin_cases i <;> fin_cases j <;> simp

theorem metric_diagE (N a : ℝ) (i j : Fin 4) : metric (diagE N a) i j = gV N a i j := by
  unfold metric diagE gV eta
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem det_diagE (N a : ℝ) : (diagE N a).det = N * a ^ 3 := by
  rw [diagE, Matrix.det_diagonal, Fin.prod_univ_four]
  simp
  ring

/-- **The derivative of a time profile**: `∂_μ(F(y⁰)) = δ_{μ0} F'(y⁰)`. -/
theorem pd_time' {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ → W} {z : R4}
    (hF : DifferentiableAt ℝ F (z 0)) (μ : Fin 4) :
    pd (fun y : R4 => F (y 0)) μ z = if μ = 0 then deriv F (z 0) else 0 := by
  have h1 : HasFDerivAt (fun y : R4 => y 0) (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 4 => ℝ) 0) z := hasFDerivAt_apply 0 z
  have h2 := hF.hasFDerivAt.comp z h1
  unfold SobolevOpen.pd
  rw [show (fun y : R4 => F (y 0)) = F ∘ fun y => y 0 from rfl, h2.fderiv]
  by_cases hμ : μ = 0
  · subst hμ
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same,
      if_true]
    rfl
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, hμ, if_false,
      Pi.single_eq_of_ne (Ne.symm hμ), map_zero]

theorem fderiv_time' {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ → W} {z : R4}
    (hF : DifferentiableAt ℝ F (z 0)) (μ : Fin 4) :
    fderiv ℝ (fun y : R4 => F (y 0)) z (evec μ) = if μ = 0 then deriv F (z 0) else 0 :=
  pd_time' hF μ

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-- The homogeneous profile value `(diag(N, a, a, a), 0, h, 0, 0)` at time `s`. -/
def profF (N a : ℝ → ℝ) (h : ℝ → 𝓗) (s : ℝ) : Field 𝔄 𝓗 𝓢 := (diagE (N s) (a s), 0, h s, 0, 0)

/-- **The homogeneous native field** `Y(y) = (diag(N, a, a, a), 0, h, 0, 0)(y⁰)`. -/
def profY (N a : ℝ → ℝ) (h : ℝ → 𝓗) : R4 → Field 𝔄 𝓗 𝓢 := fun y => profF N a h (y 0)

/-- Smooth time profiles with positive lapse and scale factor. -/
structure Profiles (N a : ℝ → ℝ) (h : ℝ → 𝓗) : Prop where
  N_smooth : ContDiff ℝ ∞ N
  a_smooth : ContDiff ℝ ∞ a
  h_smooth : ContDiff ℝ ∞ h
  N_pos : ∀ s, 0 < N s
  a_pos : ∀ s, 0 < a s

variable {N a : ℝ → ℝ} {h : ℝ → 𝓗}

theorem contDiff_diagE {n : WithTop ℕ∞} {N a : ℝ → ℝ} (hN : ContDiff ℝ n N) (ha : ContDiff ℝ n a) :
    ContDiff ℝ n (fun s => diagE (N s) (a s)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [diagE_apply]
  split_ifs
  · exact hN
  · exact ha
  · exact contDiff_const

theorem Profiles.contDiff_profF (hp : Profiles N a h) :
    ContDiff ℝ ∞ (profF (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) := by
  unfold profF
  exact (contDiff_diagE hp.N_smooth hp.a_smooth).prodMk
    (contDiff_const.prodMk (hp.h_smooth.prodMk contDiff_const))

theorem Profiles.smooth (hp : Profiles N a h) : ContDiff ℝ ∞ (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) :=
  hp.contDiff_profF.comp (contDiff_apply ℝ ℝ (0 : Fin 4))

theorem Profiles.det_pos (hp : Profiles N a h) (y : R4) :
    0 < ((profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h y).1).det := by
  show 0 < (diagE (N (y 0)) (a (y 0))).det
  rw [det_diagE]
  have := hp.N_pos (y 0); have := hp.a_pos (y 0); positivity

theorem profY_isEH : IsEH (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The derivative of the profile value. -/
def profD (N a : ℝ → ℝ) (h : ℝ → 𝓗) (s : ℝ) : Field 𝔄 𝓗 𝓢 :=
  (diagE (deriv N s) (deriv a s), 0, deriv h s, 0, 0)

theorem Profiles.hasDerivAt_profF (hp : Profiles N a h) (s : ℝ) :
    HasDerivAt (profF (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) (profD N a h s) s := by
  have hN := (hp.N_smooth.differentiable (by simp) s).hasDerivAt
  have ha := (hp.a_smooth.differentiable (by simp) s).hasDerivAt
  have hh := (hp.h_smooth.differentiable (by simp) s).hasDerivAt
  have hE : HasDerivAt (fun s => diagE (N s) (a s)) (diagE (deriv N s) (deriv a s)) s := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [diagE_apply]
    split_ifs
    · exact hN
    · exact ha
    · exact hasDerivAt_const _ _
  exact hE.prodMk ((hasDerivAt_const _ _).prodMk (hh.prodMk (hasDerivAt_const _ _)))

/-- **The first jet of the homogeneous field**. -/
theorem Profiles.jet1_profY (hp : Profiles N a h) (z : R4) :
    jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z =
      (profF N a h (z 0), fun μ => if μ = 0 then profD N a h (z 0) else 0) := by
  unfold jet1
  refine Prod.ext rfl (funext fun μ => ?_)
  have h1 := fderiv_time' (F := profF (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) (z := z)
    (hp.hasDerivAt_profF (z 0)).differentiableAt μ
  rw [(hp.hasDerivAt_profF (z 0)).deriv] at h1
  exact h1

end Profile

/-! ### The metric jets, Einstein residual and wave operator of a profile field -/

section ProfileJets

open NativeDensity NativeBosonicEuler NativeDiracEuler NativeStressEuler PalatiniEuler
  NativeMatterEuler EHFieldVariation
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic)
open NativeScaling (Mat eta metric)
open SobolevOpen (pd)
open ActualJetSystem (ginvOf)
open scoped ContDiff

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable {N a : ℝ → ℝ} {h : ℝ → 𝓗}

/-- The metric profile `s ↦ diag(-N², a², a², a²)`. -/
def gProf (N a : ℝ → ℝ) (s : ℝ) : Fin 4 → Fin 4 → ℝ := gV (N s) (a s)

theorem gF_profY (y : R4) :
    gF (eF (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h)) y = gProf N a (y 0) := by
  funext i j
  exact metric_diagE _ _ i j

theorem gF_profY_fun :
    gF (eF (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h)) = fun y => gProf N a (y 0) :=
  funext gF_profY

theorem hasDerivAt_gProf {N a : ℝ → ℝ} {s N1 a1 : ℝ} (hN : HasDerivAt N N1 s)
    (ha : HasDerivAt a a1 s) :
    HasDerivAt (gProf N a) (fun i j => dgV (N s) N1 (a s) a1 0 i j) s := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  unfold gProf gV dgV
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = 0
    · subst hi
      simp only [if_true, true_and]
      refine ((hN.fun_pow 2).neg).congr_deriv ?_
      push_cast; ring
    · simp only [if_true, hi, if_false, true_and]
      refine (ha.fun_pow 2).congr_deriv ?_
      push_cast; ring
  · simp only [hij, if_false, and_false]
    exact hasDerivAt_const _ _

theorem Profiles.deriv_gProf (hp : Profiles N a h) :
    deriv (gProf N a) = fun s i j => dgV (N s) (deriv N s) (a s) (deriv a s) 0 i j := by
  funext s
  exact (hasDerivAt_gProf ((hp.N_smooth.differentiable (by simp) s).hasDerivAt)
    ((hp.a_smooth.differentiable (by simp) s).hasDerivAt)).deriv

theorem Profiles.hasDerivAt_dgProf (hp : Profiles N a h) (s : ℝ) :
    HasDerivAt (fun s => fun i j => dgV (N s) (deriv N s) (a s) (deriv a s) 0 i j)
      (fun i j => ddgV (N s) (deriv N s) (deriv (deriv N) s) (a s) (deriv a s)
        (deriv (deriv a) s) 0 0 i j) s := by
  have hN := (hp.N_smooth.differentiable (by simp) s).hasDerivAt
  have ha := (hp.a_smooth.differentiable (by simp) s).hasDerivAt
  have hN' := ((hp.N_smooth.iterate_deriv 1).differentiable (by simp) s).hasDerivAt
  have ha' := ((hp.a_smooth.iterate_deriv 1).differentiable (by simp) s).hasDerivAt
  simp only [Function.iterate_one] at hN' ha'
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  unfold dgV ddgV
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = 0
    · subst hi
      simp only [if_true, and_self]
      refine (((hN.const_mul 2).mul hN').neg).congr_deriv ?_
      ring
    · simp only [if_true, hi, if_false, and_self]
      refine ((ha.const_mul 2).mul ha').congr_deriv ?_
      ring
  · simp only [hij, if_false, and_false]
    exact hasDerivAt_const _ _

/-- **The first metric jet of the profile field**: `∂g = dgV(N, N', a, a')`. -/
theorem Profiles.dF_profY (hp : Profiles N a h) (z : R4) :
    dF (gF (eF (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h))) z =
      dgV (N (z 0)) (deriv N (z 0)) (a (z 0)) (deriv a (z 0)) := by
  funext α i j
  unfold dF
  rw [gF_profY_fun]
  have hd : DifferentiableAt ℝ (gProf N a) (z 0) :=
    (hasDerivAt_gProf ((hp.N_smooth.differentiable (by simp) _).hasDerivAt)
      ((hp.a_smooth.differentiable (by simp) _).hasDerivAt)).differentiableAt
  rw [pd_time' hd, hp.deriv_gProf]
  by_cases hα : α = 0
  · subst hα; simp
  · simp [hα, dgV]

/-- **The second metric jet of the profile field**: `∂∂g = ddgV(N, N', N'', a, a', a'')`. -/
theorem Profiles.ddF_profY (hp : Profiles N a h) (z : R4) :
    ddF (gF (eF (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h))) z =
      ddgV (N (z 0)) (deriv N (z 0)) (deriv (deriv N) (z 0)) (a (z 0)) (deriv a (z 0))
        (deriv (deriv a) (z 0)) := by
  funext β α i j
  unfold ddF
  rw [gF_profY_fun]
  have hd : ∀ s, DifferentiableAt ℝ (gProf N a) s := fun s =>
    (hasDerivAt_gProf ((hp.N_smooth.differentiable (by simp) _).hasDerivAt)
      ((hp.a_smooth.differentiable (by simp) _).hasDerivAt)).differentiableAt
  have h1 : pd (fun y : R4 => gProf N a (y 0)) α = fun y =>
      (if α = 0 then (fun s i j => dgV (N s) (deriv N s) (a s) (deriv a s) 0 i j) else
        fun _ => (0 : Fin 4 → Fin 4 → ℝ)) (y 0) := by
    funext y
    rw [pd_time' (hd (y 0)), hp.deriv_gProf]
    split_ifs <;> rfl
  rw [h1]
  by_cases hα : α = 0
  · subst hα
    simp only [if_true]
    rw [pd_time' (hp.hasDerivAt_dgProf (z 0)).differentiableAt, (hp.hasDerivAt_dgProf (z 0)).deriv]
    by_cases hβ : β = 0
    · subst hβ; simp
    · simp [hβ, ddgV]
  · simp only [hα, if_false]
    rw [pd_time' (differentiableAt_const _)]
    simp [ddgV, hα]

theorem ginvOf_gV {n b : ℝ} (hn : n ≠ 0) (hb : b ≠ 0) : ginvOf (gV n b) = giV n b := by
  have h : Matrix.of (gV n b) * Matrix.of (giV n b) = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    unfold gV giV
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four] <;> field_simp
  funext i j
  unfold ActualJetSystem.ginvOf
  rw [Matrix.inv_eq_right_inv h]
  rfl

theorem Profiles.ginvOf_profY (hp : Profiles N a h) (z : R4) :
    ginvOf (gF (eF (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h)) z) = giV (N (z 0)) (a (z 0)) := by
  rw [gF_profY]
  exact ginvOf_gV (hp.N_pos _).ne' (hp.a_pos _).ne'

theorem Profiles.ginv_profY (hp : Profiles N a h) (z : R4) (μ ν : Fin 4) :
    ginv ((profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h z).1) μ ν = giV (N (z 0)) (a (z 0)) μ ν := by
  have : ginv ((profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h z).1) μ ν =
      ginvOf (gF (eF (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h)) z) μ ν := rfl
  rw [this, hp.ginvOf_profY]

end ProfileJets

/-! ### Stress, Einstein residual and wave operator of a profile field -/

section ProfileRes

open NativeDensity NativeBosonicEuler NativeDiracEuler NativeStressEuler PalatiniEuler
  NativeMatterEuler EHFieldVariation
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic)
open NativeScaling (Mat eta metric)
open SobolevOpen (pd)
open ActualJetSystem (ginvOf)
open scoped ContDiff

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable {N a : ℝ → ℝ} {h : ℝ → 𝓗}

/-- On Einstein–Higgs jets the Standard-Model stress is the Higgs stress. -/
theorem smStressUp_EH {wp : FJ 𝔄 𝓗 𝓢} (hA : wp.1.2.1 = 0) (hdA : ∀ μ, (wp.2 μ).2.1 = 0)
    (hΨ : wp.1.2.2.2.1 = 0) (hΨb : wp.1.2.2.2.2 = 0) (hdΨ : ∀ μ, (wp.2 μ).2.2.2.1 = 0)
    (hdΨb : ∀ μ, (wp.2 μ).2.2.2.2 = 0) (a b : Fin 4) :
    smStressUp D wp a b = raise wp.1.1 (higgsStressN D wp) a b := by
  have hF : ∀ μ ν, FA wp μ ν = 0 := by
    intro μ ν; unfold FA; simp [hA, hdA]
  have hD : ∀ μ, DPsi D wp μ = 0 := by
    intro μ; unfold DPsi; simp [hΨ, hdΨ]
  have hDb : ∀ μ, DPsiBar D wp μ = 0 := by
    intro μ; unfold DPsiBar; simp [hΨb, hdΨb]
  have hYM : ∀ μ ν, ymStressN D wp μ ν = 0 := by
    intro μ ν; unfold ymStressN; simp [hF]
  have hL : diracLag D wp = 0 := by
    unfold diracLag; simp [hD, hDb, hΨ, hΨb]
  have hθ : ∀ μ b, thetaN D wp μ b = 0 := by
    intro μ b; unfold thetaN; simp [hD, hDb, hΨ, hΨb]
  unfold smStressUp diracStressUp
  simp only [hYM, zero_add, hL, mul_zero, hθ, Finset.sum_const_zero, sub_zero, add_zero]

/-- The Higgs covector `K_μ = δ_{μ0}h'` of a profile field. -/
theorem Profiles.KH_profY (hp : Profiles N a h) (z : R4) (μ : Fin 4) :
    KH D (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z) μ = if μ = 0 then deriv h (z 0) else 0 := by
  rw [hp.jet1_profY]
  unfold KH
  by_cases hμ : μ = 0
  · subst hμ; simp [profF, profD]
  · simp [profF, profD, hμ]

/-- `⟨h', h'⟩` at a time. -/
def KKv (h : ℝ → 𝓗) (s : ℝ) : ℝ := D.hermH (deriv h s) (deriv h s)

/-- **The Higgs stress of a profile field**: `T_{μν} = 2δ_{μ0}δ_{ν0}⟨h',h'⟩ - g_{μν}(-⟨h',h'⟩/N² + V)`. -/
theorem Profiles.higgsStressN_profY (hp : Profiles N a h) (z : R4) (μ ν : Fin 4) :
    higgsStressN D (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z) μ ν =
      (if μ = 0 ∧ ν = 0 then 2 * KKv D h (z 0) else 0) -
        gV (N (z 0)) (a (z 0)) μ ν * (-(N (z 0) ^ 2)⁻¹ * KKv D h (z 0) + potential D (h (z 0))) := by
  have hK := hp.KH_profY D z
  have hE : (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).1.1 = diagE (N (z 0)) (a (z 0)) := by
    rw [hp.jet1_profY]; rfl
  have hH : (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).1.2.2.1 = h (z 0) := by
    rw [hp.jet1_profY]; rfl
  have hsum : ∑ α, ∑ β, ginv (diagE (N (z 0)) (a (z 0))) α β *
      D.hermH (KH D (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z) α)
        (KH D (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z) β) =
      -(N (z 0) ^ 2)⁻¹ * KKv D h (z 0) := by
    have hg : ∀ α β, ginv (diagE (N (z 0)) (a (z 0))) α β = giV (N (z 0)) (a (z 0)) α β :=
      fun α β => hp.ginv_profY (𝔄 := 𝔄) (𝓢 := 𝓢) z α β
    simp only [hg, hK]
    rw [Finset.sum_eq_single (0 : Fin 4) (fun α _ hα => Finset.sum_eq_zero fun β _ => by
      simp [hα]) (by simp)]
    rw [Finset.sum_eq_single (0 : Fin 4) (fun β _ hβ => by simp [hβ]) (by simp)]
    simp only [if_true]
    unfold giV KKv
    simp
  unfold higgsStressN
  rw [hE, hH, hsum, metric_diagE, hK, hK]
  by_cases hμ : μ = 0 <;> by_cases hν : ν = 0
  · subst hμ; subst hν; simp [KKv] <;> ring
  · simp [hμ, hν]
  · simp [hμ, hν]
  · simp [hμ, hν]

theorem Profiles.isEH_jet (hp : Profiles N a h) (z : R4) :
    (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).1.2.1 = 0 ∧
      (∀ μ, ((jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).2 μ).2.1 = 0) ∧
      (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).1.2.2.2.1 = 0 ∧
      (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).1.2.2.2.2 = 0 ∧
      (∀ μ, ((jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).2 μ).2.2.2.1 = 0) ∧
      (∀ μ, ((jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).2 μ).2.2.2.2 = 0) := by
  rw [hp.jet1_profY]
  refine ⟨rfl, fun μ => ?_, rfl, rfl, fun μ => ?_, fun μ => ?_⟩ <;>
    by_cases hμ : μ = 0 <;> simp [hμ, profD]

/-- The Einstein residual equations of a profile field at time `s`:
`R₀ = 3a'²/a² - ΛN² - κ(⟨h',h'⟩ + N²V)` (Friedmann) and
`Rₖ = Gₖₖ + Λa² - κa²(⟨h',h'⟩/N² - V)` (spatial). -/
def fried0 (N a : ℝ → ℝ) (h : ℝ → 𝓗) (s : ℝ) : ℝ :=
  3 * deriv a s ^ 2 / a s ^ 2 - D.Λ * N s ^ 2 - D.κ * (KKv D h s + N s ^ 2 * potential D (h s))

def friedK (N a : ℝ → ℝ) (h : ℝ → 𝓗) (s : ℝ) : ℝ :=
  -(2 * a s * deriv (deriv a) s / N s ^ 2 - 2 * a s * deriv a s * deriv N s / N s ^ 3 +
      deriv a s ^ 2 / N s ^ 2) + D.Λ * a s ^ 2 -
    D.κ * (a s ^ 2 * (KKv D h s / N s ^ 2 - potential D (h s)))

/-- **The Einstein residual of a profile field** (diagonal; the coefficients `g^{μμ}g^{νν}`
are invertible). -/
theorem Profiles.einsteinRes_profY (hp : Profiles N a h) (z : R4) (μ ν : Fin 4) :
    einsteinRes D (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z μ ν =
      if μ = ν then (if μ = 0 then ((N (z 0) ^ 2)⁻¹) ^ 2 * fried0 D N a h (z 0)
        else ((a (z 0) ^ 2)⁻¹) ^ 2 * friedK D N a h (z 0)) else 0 := by
  have hN := (hp.N_pos (z 0)).ne'
  have ha := (hp.a_pos (z 0)).ne'
  obtain ⟨hA, hdA, hΨ, hΨb, hdΨ, hdΨb⟩ := hp.isEH_jet (𝔄 := 𝔄) (𝓢 := 𝓢) z
  unfold einsteinRes
  rw [hp.dF_profY, hp.ddF_profY, gF_profY, gProf, ginvOf_gV hN ha,
    einsteinUp_lapse hN ha, hp.ginv_profY,
    smStressUp_EH D hA hdA hΨ hΨb hdΨ hdΨb]
  have hE : (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).1.1 = diagE (N (z 0)) (a (z 0)) := by
    rw [hp.jet1_profY]; rfl
  have hR : raise (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z).1.1
      (higgsStressN D (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z)) μ ν =
      giV (N (z 0)) (a (z 0)) μ μ * giV (N (z 0)) (a (z 0)) ν ν *
        higgsStressN D (jet1 (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z) μ ν := by
    unfold raise
    rw [hE]
    have hg : ∀ α β, ginv (diagE (N (z 0)) (a (z 0))) α β = giV (N (z 0)) (a (z 0)) α β :=
      fun α β => hp.ginv_profY (𝔄 := 𝔄) (𝓢 := 𝓢) z α β
    simp only [hg]
    rw [Finset.sum_eq_single μ (fun b _ hb => by simp [giV, Ne.symm hb]) (by simp)]
    rw [Finset.sum_eq_single ν (fun b _ hb => by simp [giV, Ne.symm hb]) (by simp)]
  rw [hR, hp.higgsStressN_profY]
  unfold fried0 friedK EinV giV gV
  fin_cases μ <;> fin_cases ν <;> simp <;> field_simp <;> ring

/-- **The covariant wave operator of a profile field**:
`□H = -N⁻²(h'' - (N'/N)h' + 3(a'/a)h')`. -/
theorem Profiles.waveN_profY (hp : Profiles N a h) (z : R4) :
    waveN D (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z =
      -(N (z 0) ^ 2)⁻¹ • (deriv (deriv h) (z 0) - (deriv N (z 0) / N (z 0)) • deriv h (z 0) +
        (3 * deriv a (z 0) / a (z 0)) • deriv h (z 0)) := by
  have hN := (hp.N_pos (z 0)).ne'
  have ha := (hp.a_pos (z 0)).ne'
  have hKf : ∀ y μ, Kf D (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) y μ =
      (if μ = 0 then deriv h else fun _ => (0 : 𝓗)) (y 0) := by
    intro y μ
    unfold Kf
    rw [hp.KH_profY]
    split_ifs <;> rfl
  have hdh : ∀ s, HasDerivAt (deriv h) (deriv (deriv h) s) s := fun s =>
    ((hp.h_smooth.iterate_deriv 1).differentiable (by simp) s).hasDerivAt
  have hpd : ∀ μ ρ, pd (fun y => Kf D (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) y μ) ρ z =
      if μ = 0 ∧ ρ = 0 then deriv (deriv h) (z 0) else 0 := by
    intro μ ρ
    simp only [hKf]
    by_cases hμ : μ = 0
    · subst hμ
      simp only [if_true, true_and]
      rw [pd_time' (hdh (z 0)).differentiableAt]
    · simp only [hμ, if_false, false_and]
      rw [pd_time' (differentiableAt_const _)]
      simp
  have hA : ∀ ρ, ((profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h z).2.1 ρ) = 0 := fun ρ => rfl
  unfold waveN
  simp only [hpd, hA, map_zero, ContinuousLinearMap.zero_apply, add_zero]
  rw [hp.ginvOf_profY, hp.dF_profY, chr_lapse hN ha]
  simp only [hKf]
  simp only [Fin.sum_univ_four, giV, GamV]
  simp
  match_scalars <;> field_simp <;> ring

end ProfileRes

/-! ### The native Euler equations of a profile field -/

section ProfileEuler

open NativeDensity NativeBosonicEuler NativeDiracEuler NativeStressEuler PalatiniEuler
  NativeMatterEuler EHFieldVariation
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic)
open NativeScaling (Mat eta metric)
open SobolevOpen (pd)
open ActualJetSystem (ginvOf)
open scoped ContDiff

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable {N a : ℝ → ℝ} {h : ℝ → 𝓗}

/-- A profile field with `L`-periodic lapse and scale factor has an `L`-periodic coframe. -/
theorem isLPeriodic_profY {L : ℝ} (hN : Function.Periodic N L) (ha : Function.Periodic a L) :
    IsLPeriodic L (eF (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h)) := by
  intro k x
  show diagE (N ((L • (x + PeriodicCube.zvec k)) 0)) (a ((L • (x + PeriodicCube.zvec k)) 0)) =
    diagE (N ((L • x) 0)) (a ((L • x) 0))
  have e : (L • (x + PeriodicCube.zvec k)) 0 = (L • x) 0 + (k 0 : ℤ) * L := by
    simp [PeriodicCube.zvec, smul_eq_mul]; ring
  rw [e, hN.int_mul (k 0) _, ha.int_mul (k 0) _]

/-- A native field value with vanishing gauge part is the sum of its coframe, Higgs, spinor and
co-spinor directions. -/
theorem field_decomp (w : Field 𝔄 𝓗 𝓢) (hw : w.2.1 = 0) :
    w = coframeDir w.1 + higgsDir w.2.2.1 + psiDir w.2.2.2.1 + psiBarDir w.2.2.2.2 := by
  obtain ⟨e, A, H, Ψ, Ψb⟩ := w
  simp only at hw
  subst hw
  simp [coframeDir, higgsDir, psiDir, psiBarDir]

/-- **The native Euler equations of a homogeneous profile field** at a point `z`: if the
Friedmann residuals `fried0`, `friedK` and the Higgs residual vanish at `z⁰`, the Euler covector
vanishes on every direction with vanishing gauge part (all coframe directions, local Lorentz
directions included; Higgs, spinor and co-spinor directions). -/
theorem native_euler_profile (hκ : D.κ ≠ 0) (hsymH : ∀ x y, D.hermH x y = D.hermH y x)
    (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) (hρ : ∀ A a, D.ρS A * D.γ a = D.γ a * D.ρS A)
    (hp : Profiles N a h) {L : ℝ} (hL : 0 < L) (hNL : Function.Periodic N L)
    (haL : Function.Periodic a L) (z : R4)
    (h0 : fried0 D N a h (z 0) = 0) (hk : friedK D N a h (z 0) = 0)
    (hW : ∀ η : 𝓗, 2 * D.hermH η (waveN D (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z) =
      potGrad D (h (z 0)) η)
    (w : Field 𝔄 𝓗 𝓢) (hw : w.2.1 = 0) :
    contEuler (L0 D) (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) z w = 0 := by
  set Y := profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h with hYdef
  have hY : ContDiff ℝ ∞ Y := hp.smooth
  have hdet : ∀ z, 0 < ((Y z).1).det := hp.det_pos
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  have hEH : IsEH Y := profY_isEH
  rw [field_decomp w hw, map_add, map_add, map_add]
  -- coframe rows
  have hcf : contEuler (L0 D) Y z (coframeDir w.1) = 0 := by
    rw [coframe_row_EH hY hL (isLPeriodic_profY hNL haL) hdet hEH z w.1, einsteinCov_apply]
    have hres : ∀ μ ν, einsteinRes D Y z μ ν = 0 := by
      intro μ ν
      rw [hp.einsteinRes_profY D z μ ν, h0, hk]
      simp
    have hrow : ∀ μ ν, einsteinUp (gF (eF Y) z) (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z)
        (ddF (gF (eF Y)) z) μ ν + D.Λ * ginvOf (gF (eF Y) z) μ ν =
        D.κ * raise (Y z).1 (higgsStressN D (jet1 Y z)) μ ν := by
      intro μ ν
      have := hres μ ν
      obtain ⟨hA, hdA, hΨ, hΨb, hdΨ, hdΨb⟩ := hp.isEH_jet (𝔄 := 𝔄) (𝓢 := 𝓢) z
      unfold einsteinRes at this
      rw [smStressUp_EH D hA hdA hΨ hΨb hdΨ hdΨb] at this
      have e : ginv (Y z).1 μ ν = ginvOf (gF (eF Y) z) μ ν := rfl
      rw [e] at this
      have e2 : (jet1 Y z).1.1 = (Y z).1 := rfl
      rw [e2] at this
      linarith
    have hsum : ∑ μ, ∑ ν, (einsteinUp (gF (eF Y) z) (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z)
        (ddF (gF (eF Y)) z) μ ν + D.Λ * ginvOf (gF (eF Y) z) μ ν) * metricVarM (eF Y z) w.1 μ ν =
        D.κ * ∑ a, ∑ b, raise (Y z).1 (higgsStressN D (jet1 Y z)) a b * metricVarM (Y z).1 w.1 a b := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hrow μ ν]
      have : eF Y z = (Y z).1 := rfl
      rw [this]
      ring
    rw [hsum]
    have : eF Y z = (Y z).1 := rfl
    rw [this]
    field_simp
    ring
  -- Higgs rows
  have hH : contEuler (L0 D) Y z (higgsDir w.2.2.1) = 0 := by
    have hskew : ∀ a ∈ ({0} : Set 𝔄), ∀ x y, D.hermH (D.ρH a x) y = -D.hermH x (D.ρH a y) := by
      intro a ha x y
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp
    rw [higgs_euler_row D hsymH {0} hskew hY (fun z μ => rfl) hdet z w.2.2.1]
    have hb : (Y z).2.2.2.2 = 0 := hEH.Ψb0 z
    rw [hb]
    have hW' := hW w.2.2.1
    have hv : (Y z).2.2.1 = h (z 0) := rfl
    rw [hv]
    simp only [ContinuousLinearMap.zero_apply, Complex.zero_re, mul_zero, sub_zero]
    linear_combination (volume (Y z).1) * hW'
  -- spinor rows
  have hψ : contEuler (L0 D) Y z (psiDir w.2.2.2.1) = 0 := by
    rw [psi_euler_row D hcl hσ hρ hY hdet z]
    have hΨb : (jet1 Y z).1.2.2.2.2 = 0 := hEH.Ψb0 z
    have hdΨb : ∀ μ, ((jet1 Y z).2 μ).2.2.2.2 = 0 := fun μ => hEH.jet_Ψb hYd z μ
    have hDb : ∀ μ, DPsiBar D (jet1 Y z) μ = 0 := by
      intro μ; unfold DPsiBar; simp [hΨb, hdΨb]
    have hb : (Y z).2.2.2.2 = 0 := hEH.Ψb0 z
    simp [hDb, hb]
  have hψb : contEuler (L0 D) Y z (psiBarDir w.2.2.2.2) = 0 := by
    rw [psibar_euler_row D hcl hσ hρ hY hdet z]
    have hΨ : (jet1 Y z).1.2.2.2.1 = 0 := hEH.Ψ0 z
    have hdΨ : ∀ μ, ((jet1 Y z).2 μ).2.2.2.1 = 0 := fun μ => hEH.jet_Ψ hYd z μ
    have hD : ∀ μ, DPsi D (jet1 Y z) μ = 0 := by
      intro μ; unfold DPsi; simp [hΨ, hdΨ]
    have hb : (Y z).2.2.2.1 = 0 := hEH.Ψ0 z
    simp [hD, hb]
  rw [hcf, hH, hψ, hψb]
  simp

end ProfileEuler
end

end RenewalGeometry.HomogeneousNative
