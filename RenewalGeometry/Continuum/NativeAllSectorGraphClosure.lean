/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeAllSectorConsistency
import RenewalGeometry.Continuum.NativeSpinorGraphBridge

/-!
# All-sector native consistency from the paper's hypotheses `(N1)–(N4)`
  (`thm:native-firstvariation-no-band`, fixed coefficient bank)

Einstein–SM action-closure manuscript, `thm:native-firstvariation-no-band`.  The assembled limit
`NativeAllSector.native_all_sector_limit` took the Higgs conclusions (`HiggsHyp`) and the spinor
extraction outputs (`SpinHyp`, a weak limit `u₀`) as inputs.  This file derives both from the
theorem's own hypotheses:

* `(N1)` `CoHyp` with an oriented compact chart and the logarithm margin `c_* ≤ 1/64`;
* `(N2)` strong `L⁴` connections and strong `L²` literal curvature `R^0 F_h → F`;
* `(N3)` `sup_h ‖H_h‖_{2,h} < ∞` and strong `L²` convergence of the literal Higgs-link packet,
  for unitary internal Higgs links (Higgs fibre in an orthonormal real frame, as in
  `NativeHiggsVar.exists_higgsHyp`);
* `(N4)` the positive internal-link graph bound `eq:native-spinor-graph`, unitary internal spin
  links (`NativeSpinorGraph.native_spinor_extraction`);

with a **fixed** coefficient bank `D`.  `native_all_sector_closure` gives, after extraction:
`F = F_A` (in the distributional Fourier form of `prop:native-YM-identification`), `K = D_A H`
with `R^0 D⁺H_h → K - ρ_H(A)H` strongly in `L²` and `R^0 H_h → H` in `L⁴`, the weak `H¹` spinor
limits with `u₀ = (∂Ψ, ∂Ψ̄)`, `eq:native-all-sector-limit` uniformly on every `C²` ball, and the
Euler corollary.

Disclosed renderings: as in `NativeAllSectorConsistency` and `NativeSpinorGraphBridge`
(unit torus, co-spinors read with `κ = id`, frames `Θ, Θ'` of the spinor and co-spinor fibres
only used to state `u₀ = (∂Ψ, ∂Ψ̄)` componentwise).  Varying coefficient banks `(N5)` are treated in
`NativeBankContinuity`.  NOT covered: the reconstructed-fields paragraph (YM, Higgs, Dirac
sectors).
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace UnitAddTorus
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace RenewalGeometry.NativeAllSectorGraph

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc gridNorm)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat)
open NativeDensity
open NativeDiracLimit (DTest testRec)
open NativeDiracConv (CoHyp)
open NativeDiracConvergence (SpinHyp)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {r r' : ℕ} [NeZero r] [NeZero r']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- The Higgs fibre in an orthonormal real frame. -/
local notation "𝓗" => EuclideanSpace ℝ (Fin rH)

/-- The Higgs hypotheses along a subsequence. -/
def higgsHypSubseq {D : Data 𝔄 𝓗 𝓢} {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}
    (P : NativeHiggsVar.HiggsHyp D y) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    NativeHiggsVar.HiggsHyp D (fun k => y (φ k)) :=
  ⟨P.H₀, P.hH.comp_strictMono hφ, P.K₀, fun μ => (P.hK μ).comp_strictMono hφ⟩

/-- The literal native curvature is, eventually, the `curvLog` packet of
`prop:native-YM-identification` (scaled slot chart, strong `L⁴` connections). -/
theorem lpTendsto_curvLog {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢} (H : CoHyp n y)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν)) (μ ν : Fin 4) :
    LpTendsto volume 2 (fun k => pc (fun x =>
      NativeYMIdentification.curvLog (n k) (NativeYMBridge.gaugeArr (y k)) x μ ν)) (F μ ν) := by
  have hA : ∀ μ, LpTendsto volume 4
      (fun k => pc (fun x => NativeYMBridge.gaugeArr (y k) x μ)) (H.A₀ μ) := H.hA
  obtain ⟨δ, -, hev⟩ := NativeYMMetric.unif_FextV H.hn hA 1
  refine NativeYMBridge.lpTendsto_of_eventually_eq (hF μ ν)
    (fun k => NativeYMIdentification.memLp_pc_gen _ 2) (hev.mono fun k hk => ?_)
  funext z
  simp only [pc]
  exact NativeYMBridge.fieldStrength_eq_curvLog (gauge (y k)) _ μ ν
    (NativeYMBridge.gaugePlaquette_lt_of_chart (gauge (y k)) _ μ ν (hk.1 _ μ ν))

set_option maxHeartbeats 1600000 in
/-- **`thm:native-firstvariation-no-band`, main assertions, from `(N1)–(N4)`** (fixed coefficient
bank; unit-torus rendering; Higgs fibre `ℝ^{r_H}` in an orthonormal frame; co-spinors read with
`κ = id`).  Let the actual nodal records `y_h` of the unchanged local action satisfy
* `(N1)`: `CoHyp` (strong first-jet coframe convergence on a compact **oriented** nondegenerate
  chart, the logarithm margin `h|ω_h| ≤ c_* ≤ 1/64`, strong `L⁴` connection convergence);
* `(N2)`: the literal logarithmic curvature `R^0 F_h → F` strongly in `L²`;
* `(N3)`: unitary internal Higgs links, `sup_h ‖H_h‖_{2,h} ≤ B_H`, and the literal Higgs-link
  packet `R^0 K_h → K` strongly in `L²`;
* `(N4)`: unitary internal spin links and the positive internal-link graph bound
  `eq:native-spinor-graph` for the spinors and dual spinors.
Then after extraction
* `F = F_A`: for every coordinate functional `ℓ` and frequency `m`, the Fourier coefficients of
  `ℓ(F_{μν} - [A_μ, A_ν])` are those of `ℓ(∂_μA_ν - ∂_νA_μ)`;
* `K = D_A H`: `R^0 H_h → H` in `L⁴` and `R^0 D⁺_μ H_h → K_μ - ρ_H(A_μ) H` strongly in `L²`;
* the spinors and dual spinors converge strongly in `L²`, their first differences weakly in `L²`
  to `u₀ = (∂Ψ, ∂Ψ̄)` (frame components in `H¹`);
* **`eq:native-all-sector-limit`**: for every radius `M` and `ε > 0`, eventually
  `|D S_h^{loc}(z_h)[𝓘_h v] - D𝒮_θ(z)[v]| ≤ ε` for all tests `‖v‖_{C²} ≤ M`;
* **Euler corollary**: if the complete finite variation tends to zero on the unit test family,
  then `D𝒮_θ(z)[v] = 0` for every test `v`. -/
theorem native_all_sector_closure (D : Data 𝔄 𝓗 𝓢) (T : 𝔄 →L[ℝ] E)
    (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢} (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (hUH : ∀ k x μ (v : 𝓗), ‖exp ((n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)) v‖ = ‖v‖)
    {BH : ℝ} (hHb : ∀ k, gridNorm (higgs (y k)) ≤ BH)
    {K₀ : Fin 4 → 𝕋 → 𝓗}
    (hK : ∀ μ, LpTendsto volume 2 (fun k => pc (fun x => higgsLink D (n k : ℝ)⁻¹ (y k) x μ))
      (K₀ μ))
    (hU : ∀ k x μ (v : 𝓢), ‖D.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖)
    {B : ℝ} (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B)
    (hKs : ∀ k μ, gridNorm (fun x => spinGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hKb : ∀ k μ, gridNorm (fun x => dualGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ, ∃ P : NativeHiggsVar.HiggsHyp D (fun k => y (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)), ∃ u₀ : 𝕋 → NativeDiracLimit.Dif 𝓢 (CoSpinor 𝓢),
      -- `F = F_A`
      (∀ μ ν (ℓ : 𝔄 →L[ℝ] ℂ) (m : Fin 4 → ℤ),
        mFourierCoeff (fun z => ℓ (F μ ν z)) m -
            mFourierCoeff (fun z => ℓ (H.A₀ μ z * H.A₀ ν z - H.A₀ ν z * H.A₀ μ z)) m =
          2 * Real.pi * Complex.I * m μ * mFourierCoeff (fun z => ℓ (H.A₀ ν z)) m -
            2 * Real.pi * Complex.I * m ν * mFourierCoeff (fun z => ℓ (H.A₀ μ z)) m) ∧
      -- `K = D_A H`
      P.K₀ = K₀ ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y (φ k)))))
        (fun z => K₀ μ z - D.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      -- `u₀ = (∂Ψ, ∂Ψ̄)`
      (∀ j, ∃ f : L²(𝕋), ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      (∀ j, ∃ f : L²(𝕋), ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ' (S.χ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ' ((u₀ z).2 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit`
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar D (n (φ k)) (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeAllSector.contAllVar D (κid 𝓢) T (coHypSubseq H hφ) F P S u₀ τ| ≤ ε) ∧
      -- the Euler corollary
      ((∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 (CoSpinor 𝓢), τ.norm ≤ 1 →
          |NativeAllSector.nativeVar D (n k) (y k) (testRec (κid 𝓢) (n k) (y k) τ)| ≤ ε) →
        ∀ τ : DTest 𝔄 𝓗 𝓢 (CoSpinor 𝓢),
          NativeAllSector.contAllVar D (κid 𝓢) T (coHypSubseq H hφ) F P S u₀ τ = 0) := by
  -- `(N3)`: the Higgs extraction
  obtain ⟨φ₁, hφ₁, P₁, hP₁, hDH⟩ := NativeHiggsVar.exists_higgsHyp D H.hn H.hA hUH hHb hK
  -- `(N4)`: the spinor extraction along `φ₁`
  have hn₁ : Tendsto (fun k => n (φ₁ k)) atTop atTop := H.hn.comp hφ₁.tendsto_atTop
  obtain ⟨φ₂, hφ₂, S, u₀, -, hu₀, ⟨C, hub⟩, hw, hid1, hid2⟩ :=
    NativeSpinorGraph.native_spinor_extraction D Θ Θ' hn₁
      (fun μ => (H.hA μ).comp_strictMono hφ₁) (P₁.hH.mono (by norm_num) (by norm_num))
      (fun k => hU (φ₁ k)) (fun k => hΨ (φ₁ k)) (fun k => hKs (φ₁ k)) (fun k => hΨb (φ₁ k))
      (fun k => hKb (φ₁ k))
  have hφ : StrictMono (fun k => φ₁ (φ₂ k)) := hφ₁.comp hφ₂
  set P := higgsHypSubseq P₁ hφ₂ with hPdef
  set H' := coHypSubseq H hφ with hH'
  have hF' : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (φ₁ (φ₂ k)) : ℝ)⁻¹ (gauge (y (φ₁ (φ₂ k)))) x μ ν)) (F μ ν) :=
    fun μ ν => (hF μ ν).comp_strictMono hφ
  have hlim := NativeAllSector.native_all_sector_limit D (κid 𝓢) T hip H' hpos hc hF' P S hu₀
    hub hw
  refine ⟨fun k => φ₁ (φ₂ k), hφ, P, S, u₀, fun μ ν ℓ m => ?_, by rw [hPdef]; exact hP₁,
    fun μ => ?_, hid1, hid2, hlim, fun hstat τ => ?_⟩
  · -- `F = F_A`
    have hA : ∀ μ, LpTendsto volume 4
        (fun k => pc (fun x => NativeYMBridge.gaugeArr (y k) x μ)) (H.A₀ μ) := H.hA
    exact (NativeYMIdentification.native_YM_curvature_identification H.hn hA
      (lpTendsto_curvLog H hF) μ ν).2 ℓ m
  · exact (hDH μ).comp_strictMono hφ₂
  · -- the Euler corollary along the extraction
    refine NativeAllSector.native_all_sector_euler D (κid 𝓢) T hip H' hpos hc hF' P S hu₀ hub hw
      (fun ε hε => ?_) τ
    exact (hstat ε hε).filter_mono hφ.tendsto_atTop |>.mono fun k hk => hk

/-! ### Non-vacuity -/

section NonVacuity

open NativeGravityFirstJet (flatRecord asM4)

/-- The real frame `ℂ ≃ ℝ²` (orthonormal basis `1, i`). -/
def frameC : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv

/-- The `u(1)` Higgs representation on `ℝ² ≅ ℂ` (complex multiplication in the frame). -/
def ρH2 : ℂ →ₐ[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
  (frameC.conjContinuousAlgEquiv : (ℂ →L[ℝ] ℂ) →ₐ[ℝ] _).comp NativeAllSector.mulAlg

theorem continuous_ρH2 : Continuous ρH2 :=
  frameC.conjContinuousAlgEquiv.continuous.comp (ContinuousLinearMap.mul ℝ ℂ).continuous

/-- An abelian Einstein–Higgs–Dirac packet with the Higgs fibre in an orthonormal frame `ℝ²`. -/
def exData2 : Data ℂ (EuclideanSpace ℝ (Fin 2)) ℂ where
  κ := 1
  Λ := 0
  lamH := 1
  vH := 1
  ipA := innerSL ℝ
  hermH := innerSL ℝ
  ρH := ρH2
  ρH_cont := continuous_ρH2
  ρS := NativeAllSector.mulAlg
  ρS_cont := (ContinuousLinearMap.mul ℝ ℂ).continuous
  σ := 0
  γ := fun _ => 0
  yukawa := 0

/-- The flat records over the packet `exData2`. -/
abbrev flat2 (N : ℕ) : Grid N → Field ℂ (EuclideanSpace ℝ (Fin 2)) ℂ := flatRecord N

theorem exData2_hip (X Y : ℂ) :
    exData2.ipA X Y = ⟪ContinuousLinearMap.id ℝ ℂ X, ContinuousLinearMap.id ℝ ℂ Y⟫ := rfl

/-- The coframe/connection hypotheses for the flat records. -/
def exCoHyp2 : CoHyp (fun k => k + 1) (fun k => flat2 (k + 1)) where
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
  hp lam := (LpTendsto.const (u := fun _ : 𝕋 => (0 : NativeGravityFirstJet.M4)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => by
      funext i j
      simp only [NativeDiracConv.qM, pc, ShiftedJetAction.fwdDiff, coframe, flat2, flatRecord]
      show (0 : ℝ) = (((k + 1 : ℕ) : ℝ)⁻¹)⁻¹ * ((1 : Mat) i j - (1 : Mat) i j)
      ring)
    (Eventually.of_forall fun _ => rfl)
  A₀ := fun _ _ => 0
  hA μ := (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)

theorem exCoHyp2_pos : ∀ M ∈ exCoHyp2.Ke, 0 < Matrix.det (show Mat from M) := by
  intro M hM
  rw [Set.mem_singleton_iff.1 hM]
  exact (by simp : (0 : ℝ) < Matrix.det (1 : Mat))

theorem gauge_flat2 (k : ℕ) : gauge (flat2 (k + 1)) = fun _ _ => 0 := rfl

local instance : Nontrivial (CoSpinor ℂ) :=
  ⟨⟨0, ContinuousLinearMap.id ℝ ℂ, fun h => by
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) h
    simp at this⟩⟩

local instance : NeZero (Module.finrank ℝ (CoSpinor ℂ)) := ⟨Module.finrank_pos.ne'⟩

/-- A linear frame of the co-spinor fibre. -/
def frameCo : CoSpinor ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (CoSpinor ℂ))) :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin).symm

/-- **Non-vacuity of `native_all_sector_closure`**: the flat records (identity coframe, zero
connection, Higgs and spinor fields) of an abelian Einstein–Higgs–Dirac packet with a unitary
`u(1)` Higgs representation on `ℝ²` satisfy `(N1)–(N4)`; the theorem then yields the extraction
and the all-sector limit. -/
example : ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
    ∃ P : NativeHiggsVar.HiggsHyp exData2 (fun k => flat2 (φ k + 1)),
    ∃ S : SpinHyp (κid ℂ) (fun k => flat2 (φ k + 1)),
    ∃ u₀ : 𝕋 → NativeDiracLimit.Dif ℂ (CoSpinor ℂ),
      ∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest ℂ (EuclideanSpace ℝ (Fin 2)) ℂ
        (CoSpinor ℂ), τ.norm ≤ M →
        |NativeAllSector.nativeVar exData2 (φ k + 1) (flat2 (φ k + 1))
            (testRec (κid ℂ) (φ k + 1) (flat2 (φ k + 1)) τ) -
          NativeAllSector.contAllVar exData2 (κid ℂ) (ContinuousLinearMap.id ℝ ℂ)
            (coHypSubseq exCoHyp2 hφ) (fun _ _ _ => 0) P S u₀ τ| ≤ ε := by
  have hz : ∀ k, (0 : ℝ) ≤ gridNorm (fun _ : Grid (k + 1) => (0 : EuclideanSpace ℝ (Fin 2))) :=
    fun k => TorusPiecewiseConstantTranslation.gridNorm_nonneg _
  obtain ⟨φ, hφ, P, S, u₀, -, -, -, -, -, hlim, -⟩ := native_all_sector_closure exData2
    (ContinuousLinearMap.id ℝ ℂ) exData2_hip frameC frameCo exCoHyp2 exCoHyp2_pos
    (by norm_num [exCoHyp2]) (F := fun _ _ _ => 0)
    (fun μ ν => (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
      (fun k => Eventually.of_forall fun z => by
        rw [gauge_flat2]
        simp [pc, NativeScaling.fieldStrength, NativeScaling.gaugePlaquette,
          ShiftedPlaquette.logOneAdd])
      (Eventually.of_forall fun _ => rfl))
    (fun k x μ v => by rw [gauge_flat2]; simp)
    (BH := 0) (fun k => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, higgs, flat2, flatRecord])
    (K₀ := fun _ _ => 0)
    (fun μ => (LpTendsto.const (u := fun _ : 𝕋 => (0 : EuclideanSpace ℝ (Fin 2)))
      (memLp_const _)).congr (fun k => Eventually.of_forall fun z => by
        simp [pc, higgsLink, NativeScaling.higgsLink, higgs, flat2, flatRecord])
      (Eventually.of_forall fun _ => rfl))
    (fun k x μ v => by rw [gauge_flat2]; simp)
    (B := 0) (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psi, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, spinGraph, psi, flat2, flatRecord])
    (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psiBar, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, dualGraph, psiBar, flat2, flatRecord])
  exact ⟨φ, hφ, P, S, u₀, hlim⟩

/-- **Non-vacuity of `NativeSpinorGraph.native_spinor_variation_of_graph`**
(`prop:native-spinor-variation`): the flat records satisfy its hypotheses. -/
example : ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
    ∃ S : SpinHyp (κid ℂ) (fun k => flat2 (φ k + 1)),
    ∃ u₀ : 𝕋 → NativeDiracLimit.Dif ℂ (CoSpinor ℂ),
      ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest ℂ (EuclideanSpace ℝ (Fin 2)) ℂ (CoSpinor ℂ),
        |NativeDirac.dVar exData2 ((φ k + 1 : ℕ) : ℝ)⁻¹ (flat2 (φ k + 1))
            (testRec (κid ℂ) (φ k + 1) (flat2 (φ k + 1)) τ) -
          NativeSpinorVariation.contDiracVar exData2 (κid ℂ) (coHypSubseq exCoHyp2 hφ) S u₀ τ| ≤
            ε * τ.norm := by
  obtain ⟨φ, hφ, S, u₀, -, -, -, h⟩ := NativeSpinorGraph.native_spinor_variation_of_graph exData2
    frameC frameCo exCoHyp2 (H₀ := fun _ => 0)
    ((LpTendsto.const (u := fun _ : 𝕋 => (0 : EuclideanSpace ℝ (Fin 2))) (memLp_const _)).congr
      (fun k => Eventually.of_forall fun z => by simp [pc, higgs, flat2, flatRecord])
      (Eventually.of_forall fun _ => rfl))
    (fun k x μ v => by rw [gauge_flat2]; simp)
    (B := 0) (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psi, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, spinGraph, psi, flat2, flatRecord])
    (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psiBar, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, dualGraph, psiBar, flat2, flatRecord])
  exact ⟨φ, hφ, S, u₀, h⟩

end NonVacuity

end

end RenewalGeometry.NativeAllSectorGraph
