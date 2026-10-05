/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMRegularDirac

/-!
# `thm:regular-branch`: regularity criterion for variational closure

(Einstein–Standard-Model action-closure manuscript.)  Rendering as in
`EinsteinSMCompactnessCertificates.lean` (`Σ = 𝕋³`, the compact subslab `Q = I × Σ`,
`I = [t₀, t₁] ⊂ (0, T)`, is the slab chart `(t₀, t₁) × (0,1)³` of the lift; fixed local gauges and
frames).

Hypotheses (`thm:regular-branch`):
* `eq:regular-bosonic-bound`: `RegularBosonicBound` — the coframe, connection and Higgs components
  are uniformly bounded in `H^{3+σ}(Q)` (restriction space of `H^{3+σ}(𝕋⁴)`, `TorusRep`), and the
  coframes take values in a fixed compact subset of the nondegenerate oriented chart
  (`CoframeChartCondition`, the library's rendering of `sup_h ‖e_h^{-1}‖_∞ < ∞` in fixed frames);
  the banks lie in a compact physical set;
* the spinors and dual spinors obey the Lorentzian systems of `prop:dirac-stability`, with
  coefficients given by a `DiracModel` (`𝒜^μ(e)` Hermitian `C¹`, `ℬ(e, ∂e, A, H, θ)` continuous)
  with uniformly positive `𝒜⁰`, uniformly bounded `L^∞_tH²_x` norms, precompact initial data in
  `L²(Σ)` (every subsequence has a further subsequence with Cauchy initial data) and residuals
  tending to zero in `L²_tL²_x`;
* first-variation consistency and scaled stationarity (`FirstVariationConsistent`,
  `PhysicallyStationary`) and continuity of the Yukawa map.

* **`regular_branch`** — every cutoff subsequence has a further subsequence converging in the full
  classical strong packet on `Q` (`StrongPacketOn`, with convergent banks), and the limit solves
  the classical Einstein–Standard-Model equations there (first variations converge, all Euler
  equations, `eq:Einstein-SM`; `closure_on_slab_of_strong`).  No compact-screen hypothesis and no
  a-priori spinor first-jet compactness is assumed: the screens are produced by
  `hasCommonCompactScreen_of_cauchy` from the `C¹` compactness of `H^{3+σ}` (`rellich_C1`), and the
  spinor `H¹` compactness by `prop:dirac-stability` (`diracRoute_spinorH1Cauchy`) through
  `diracStabilityHyp_of_model`.
* Non-vacuity: `flatRegulator_regular_branch` (the flat regulator with the trivial Dirac model).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal BigOperators

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace RegularBranch

open SobolevOpen (pd box IsTest MemW12)

set_option linter.unusedSectionVars false

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- Cauchy initial data in `L²(Σ)` at time `t₀`. -/
def InitCauchy {N : Type} [Fintype N] (t₀ : ℝ) (ψ : ℕ → E4 → N → ℂ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ N₀, ∀ m ≥ N₀, ∀ n ≥ N₀,
    eLpNorm (fun y : Fin 3 → ℝ => ψ m (Fin.cons t₀ y) - ψ n (Fin.cons t₀ y)) 2
      (volume.restrict cube3) ≤ ENNReal.ofReal ε

theorem InitCauchy.comp {N : Type} [Fintype N] {t₀ : ℝ} {ψ : ℕ → E4 → N → ℂ}
    (h : InitCauchy t₀ ψ) {φ : ℕ → ℕ} (hφ : StrictMono φ) : InitCauchy t₀ (fun k => ψ (φ k)) :=
  fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun m hm n hn => hN _ (hm.trans (hφ.id_le m)) _ (hn.trans (hφ.id_le n))⟩

/-- Uniform positivity of `𝒜⁰(e_h)` on the slab. -/
def A0Positive {N : Type} [Fintype N] (D : DiracModel N Ysec) (t₀ t₁ : ℝ)
    (z : ℕ → SmoothFields T FC.left) : Prop :=
  ∃ c > (0 : ℝ), ∀ n, ∀ x ∈ slab t₀ t₁, ∀ ξ : N → ℂ,
    c * ∑ i, ‖ξ i‖ ^ 2 ≤ (∑ i, ∑ j, star (ξ i) * D.A 0 ((z n).z.e x) i j * ξ j).re

/-- **The spinor hypotheses of `thm:regular-branch`** for the spinors (`Ψ`) and dual spinors
(`Ψ̄`), with Dirac models `D`, `D̄`: uniformly positive `𝒜⁰`, uniformly bounded `L^∞_tH²_x`,
precompact initial data in `L²(Σ)`, residuals `→ 0` in `L²_tL²_x`. -/
structure RegularSpinorHyp (reg : RegulatorSequence T FC) (t₀ t₁ : ℝ)
    (D Db : DiracModel (Fin 4 × FC.C) Ysec) : Prop where
  pos : A0Positive D t₀ t₁ reg.fields
  posb : A0Positive Db t₀ t₁ reg.fields
  h2 : ∃ Cb : ℝ≥0, ∀ n, ∀ t ∈ Icc t₀ t₁, spatialH2 (spinorC (reg.fields n).z.Ψ) t ≤ Cb
  h2b : ∃ Cb : ℝ≥0, ∀ n, ∀ t ∈ Icc t₀ t₁, spatialH2 (spinorC (reg.fields n).z.Ψb) t ≤ Cb
  init : ∀ s : ℕ → ℕ, StrictMono s → ∃ φ : ℕ → ℕ, StrictMono φ ∧
    InitCauchy t₀ (fun k => spinorC (reg.fields (s (φ k))).z.Ψ) ∧
    InitCauchy t₀ (fun k => spinorC (reg.fields (s (φ k))).z.Ψb)
  res : Tendsto (fun n => eLpNorm (residual (fun μ => D.Acoef (reg.fields n) μ)
    (D.Bcoef (reg.fields n) (reg.bank n)) (spinorC (reg.fields n).z.Ψ)) 2
      (volume.restrict (slabFund t₀ t₁))) atTop (𝓝 0)
  resb : Tendsto (fun n => eLpNorm (residual (fun μ => Db.Acoef (reg.fields n) μ)
    (Db.Bcoef (reg.fields n) (reg.bank n)) (spinorC (reg.fields n).z.Ψb)) 2
      (volume.restrict (slabFund t₀ t₁))) atTop (𝓝 0)

/-- **`thm:regular-branch`.**  Under `eq:regular-bosonic-bound` on the subslab `Q = I × Σ`
(restriction-space rendering, coframe chart condition, banks in a compact physical set), the
spinor hypotheses (`RegularSpinorHyp`: the Lorentzian Dirac systems of `prop:dirac-stability` with
uniformly positive `𝒜⁰`, bounded `L^∞_tH²_x`, precompact initial data, residuals `→ 0`),
first-variation consistency, scaled stationarity and continuity of the Yukawa map: every cutoff
subsequence has a further subsequence converging in the full classical strong packet on `Q`, and the
limit solves the classical Einstein–Standard-Model equations there.  No compact-screen hypothesis
and no a-priori spinor first-jet compactness is assumed. -/
theorem regular_branch (reg : RegulatorSequence T FC) {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁)
    (h1 : t₁ < T) {a : E4} {L σ B : ℝ} (hL : 0 < L) (hσ : 0 < σ)
    (hbos : RegularBosonicBound (slabChart t₀ t₁ h0 h01 h1) a L σ B reg.fields)
    (hch : CoframeChartCondition (slabChart t₀ t₁ h0 h01 h1) reg.fields)
    (hbank : ∃ P, IsCompactBankSet P ∧ ∀ n, reg.bank n ∈ P)
    (D Db : DiracModel (Fin 4 × FC.C) Ysec) (hsp : RegularSpinorHyp reg t₀ t₁ D Db)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (Lim : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      StrongPacketOn (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ns (ψ k))) Lim ∧
      BankTendsto (fun k => reg.bank (ns (ψ k))) θ₀ ∧
      FirstVariationsConvergeOn FC t₀ t₁ h0 h01 h1 reg.r0 (fun k => reg.fields (ns (ψ k)))
        (fun k => reg.bank (ns (ψ k))) Lim θ₀ ∧
      IsDistributionalSolutionOn FC t₀ t₁ h0 h01 h1 reg.r0 Lim θ₀ ∧
      SatisfiesEinsteinSMOn FC t₀ t₁ h0 h01 h1 reg.r0 Lim θ₀ := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  obtain ⟨P, hP, hθP⟩ := hbank
  -- `C¹` extraction (L3)
  obtain ⟨ψ₁, hψ₁, hC1⟩ := exists_subseq_bosonicC1 Q a hL hσ hbos ns hns
  -- banks
  obtain ⟨ψ₂, hψ₂, θ₁, -, hθ₁⟩ := bank_extract hP hθP (ns ∘ ψ₁)
  -- initial data
  obtain ⟨ψ₃, hψ₃, hI, hIb⟩ := hsp.init (ns ∘ ψ₁ ∘ ψ₂) (hns.comp (hψ₁.comp hψ₂))
  set s₃ : ℕ → ℕ := ns ∘ ψ₁ ∘ ψ₂ ∘ ψ₃
  have hs₃ : StrictMono s₃ := hns.comp (hψ₁.comp (hψ₂.comp hψ₃))
  set w : ℕ → SmoothFields T FC.left := fun k => reg.fields (s₃ k)
  have hC1w : BosonicC1Cauchy Q w := (hC1.comp (hψ₂.comp hψ₃) :)
  have hchw : CoframeChartCondition Q w := by
    obtain ⟨Ke, hKe, hKn⟩ := hch
    exact ⟨Ke, hKe, fun k => hKn _⟩
  have hθw : BankTendsto (fun k => reg.bank (s₃ k)) θ₁ :=
    hθ₁.comp hψ₃.tendsto_atTop
  have hbankw : ∃ P, IsCompactBankSet P ∧ ∀ n, reg.bank (s₃ n) ∈ P := ⟨P, hP, fun n => hθP _⟩
  -- L4: the hypotheses of `prop:dirac-stability`
  have hpos : ∀ (D' : DiracModel (Fin 4 × FC.C) Ysec), A0Positive D' t₀ t₁ reg.fields →
      ∃ c > (0 : ℝ), ∀ n, ∀ x ∈ slab t₀ t₁, ∀ ξ : Fin 4 × FC.C → ℂ,
        c * ∑ i, ‖ξ i‖ ^ 2 ≤ (∑ i, ∑ j, star (ξ i) * D'.A 0 ((w n).z.e x) i j * ξ j).re :=
    fun D' ⟨c, hc, h⟩ => ⟨c, hc, fun n => h _⟩
  have hDS : DiracStabilityHyp t₀ t₁ (fun n => spinorC (w n).z.Ψ) :=
    diracStabilityHyp_of_model h0 h01 h1 hC1w hchw hbankw hθw D
      (fun n => DiracStab.spinorC_contDiffOn (w n).smooth_Ψ) (hpos D hsp.pos)
      (by obtain ⟨Cb, h⟩ := hsp.h2; exact ⟨Cb, fun n => h _⟩) hI
      (hsp.res.comp hs₃.tendsto_atTop)
  have hDSb : DiracStabilityHyp t₀ t₁ (fun n => spinorC (w n).z.Ψb) :=
    diracStabilityHyp_of_model h0 h01 h1 hC1w hchw hbankw hθw Db
      (fun n => DiracStab.spinorC_contDiffOn (w n).smooth_Ψb) (hpos Db hsp.posb)
      (by obtain ⟨Cb, h⟩ := hsp.h2b; exact ⟨Cb, fun n => h _⟩) hIb
      (hsp.resb.comp hs₃.tendsto_atTop)
  have hroute : DiracStabilityRoute Q w :=
    ⟨t₀, t₁, h0, h01, h1, by simp [Q, slabChart], by simp [Q, slabChart], hDS, hDSb⟩
  have hspw : SpinorStrongRoute Q w := (DiracStab.diracRoute_spinorH1Cauchy Q hroute).spinorStrongRoute
  -- L1: the reduced certificate, and reduced convergence
  have hcert : ReducedCertificate Q w (fun k => reg.bank (s₃ k)) :=
    reducedCertificate_of_C1 Q hC1w hchw hspw hbankw
  obtain ⟨ψ₄, hψ₄, Lim, θ₀, hRC⟩ := hcert.exists_reducedConvergence id strictMono_id
  -- the strong packet (L5)
  have hSP : StrongPacketOn Q (fun k => w (ψ₄ k)) Lim :=
    StrongPacketOn.of_reduced hRC ((lpPrecompact_coframe_of_C1 Q hC1w).comp ψ₄ le_top)
      (hspw.comp hψ₄)
  have hclos := closure_on_slab_of_strong reg (hs₃.comp hψ₄) h0 h01 h1 hch ⟨P, hP, hθP⟩ hcons hstat
    hyuk hSP hRC.bank_tendsto
  exact ⟨ψ₁ ∘ ψ₂ ∘ ψ₃ ∘ ψ₄, hψ₁.comp (hψ₂.comp (hψ₃.comp hψ₄)), Lim, θ₀, hSP, hRC.bank_tendsto,
    hclos⟩


/-! ### Non-vacuity: the flat regulator -/

section Flat

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

open TorusSobolev SobolevOpen.TorusChart UnitAddTorus in
theorem torusRep_one (a : E4) (L s : ℝ) (Ω : Set E4) :
    TorusRep a L s 1 Ω (fun _ => (1 : ℂ)) := by
  refine ⟨mFourier 0, memH_mFourier s 0, ?_, fun x _ => ?_⟩
  · rw [sobSq_mFourier]; simp [sobWeight]
  · simp [mFourier_zero]

open TorusSobolev SobolevOpen.TorusChart UnitAddTorus in
theorem torusRep_zero (a : E4) (L s : ℝ) {B : ℝ} (hB : 0 ≤ B) (Ω : Set E4) :
    TorusRep a L s B Ω (fun _ => (0 : ℂ)) := by
  have h0 : ∀ n, mFourierCoeff (0 : UnitAddTorus (Fin 4) → ℂ) n = 0 := fun n => by
    simp [mFourierCoeff]
  have h1 : ⇑(0 : C(UnitAddTorus (Fin 4), ℂ)) = 0 := rfl
  refine ⟨0, ?_, ?_, fun x _ => by simp⟩
  · show Summable _
    simp [h1, h0]
  · show coeffSobSq s _ ≤ B
    simp [coeffSobSq, h1, h0, hB]

theorem flat_regularBosonicBound {T : ℝ} (Q : ChartBox T) (a : E4) (L σ : ℝ) :
    RegularBosonicBound Q a L σ 1 (flatRegulator T).fields := by
  refine ⟨fun n p => ?_, fun n q => ?_, fun n i => ?_⟩
  · by_cases h : p.1 = p.2
    · have e : (fun x => ((((flatRegulator T).fields n).z.e x p.1 p.2 : ℝ) : ℂ)) =
          fun _ => (1 : ℂ) := funext fun x => by simp [flatCoframe, h]
      rw [e]; exact torusRep_one a L _ _
    · have e : (fun x => ((((flatRegulator T).fields n).z.e x p.1 p.2 : ℝ) : ℂ)) =
          fun _ => (0 : ℂ) := funext fun x => by simp [flatCoframe, h]
      rw [e]; exact torusRep_zero a L _ zero_le_one _
  · have e : (fun x => ((flatRegulator T).fields n).z.A x q.1 q.2.1 q.2.2) = fun _ => (0 : ℂ) :=
      funext fun x => by simp
    rw [e]; exact torusRep_zero a L _ zero_le_one _
  · have e : (fun x => ((flatRegulator T).fields n).z.H x i) = fun _ => (0 : ℂ) :=
      funext fun x => by simp
    rw [e]; exact torusRep_zero a L _ zero_le_one _

/-- The trivial Dirac model `𝒜⁰ = 1`, `𝒜^j = 0`, `ℬ = 0`. -/
def trivialDirac (N : Type) [Fintype N] [DecidableEq N] (Ysec : Type) : DiracModel N Ysec where
  A μ _ i j := if μ = 0 ∧ i = j then 1 else 0
  B _ _ _ := 0
  smooth_A _ := contDiff_const
  cont_B := continuous_const
  herm μ e i j := by
    by_cases hμ : μ = 0 <;> by_cases hij : i = j <;> simp [hμ, hij, eq_comm]

local instance : DecidableEq (trivialCarrier Unit).C := inferInstanceAs (DecidableEq Unit)

theorem flat_regularSpinorHyp {T t₀ t₁ : ℝ} :
    RegularSpinorHyp (flatRegulator T) t₀ t₁ (trivialDirac (Fin 4 × (trivialCarrier Unit).C) Unit)
      (trivialDirac (Fin 4 × (trivialCarrier Unit).C) Unit) := by
  have hpos : A0Positive (FC := trivialCarrier Unit) (T := T) (trivialDirac (Fin 4 × (trivialCarrier Unit).C) Unit)
      t₀ t₁ (flatRegulator T).fields := by
    refine ⟨1, one_pos, fun n x _ ξ => ?_⟩
    simp only [trivialDirac, true_and, one_mul]
    have : ∀ i, (∑ j, star (ξ i) * (if i = j then (1 : ℂ) else 0) * ξ j) = star (ξ i) * ξ i :=
      fun i => by simp
    simp only [this, Complex.re_sum]
    refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hz : ∀ n, spinorC ((flatRegulator T).fields n).z.Ψ = fun _ _ => 0 := fun n => rfl
  have hzb : ∀ n, spinorC ((flatRegulator T).fields n).z.Ψb = fun _ _ => 0 := fun n => rfl
  have hH2 : ∀ t, spatialH2 (fun _ _ => (0 : ℂ) : E4 → Fin 4 × (trivialCarrier Unit).C → ℂ) t = 0 := fun t => by
    simp only [spatialH2]
    refine Finset.sum_eq_zero fun j _ => ?_
    have e : (fun _ : Fin 3 → ℝ => (fun _ : Fin 4 × (trivialCarrier Unit).C => (0 : ℂ))) =
        fun _ => (0 : Fin 4 × (trivialCarrier Unit).C → ℂ) := rfl
    rw [e, iteratedFDeriv_fun_zero]
    simp
  have hres : ∀ D : DiracModel (Fin 4 × (trivialCarrier Unit).C) Unit, ∀ w : SmoothFields T (trivialCarrier Unit).left,
      ∀ θ : CoefficientBank Unit,
      residual (fun μ => D.Acoef w μ) (D.Bcoef w θ) (fun _ _ => (0 : ℂ)) = 0 := by
    intro D w θ
    funext x i
    have : ∀ μ, pd (fun _ _ => (0 : ℂ) : E4 → Fin 4 × (trivialCarrier Unit).C → ℂ) μ x = 0 := fun μ => by
      simp [SobolevOpen.pd]
    simp [residual, mvec, this]
  have hres' : ∀ D : DiracModel (Fin 4 × (trivialCarrier Unit).C) Unit, ∀ w : SmoothFields T (trivialCarrier Unit).left,
      ∀ θ : CoefficientBank Unit, ∀ ψ : E4 → Fin 4 × (trivialCarrier Unit).C → ℂ, (∀ x i, ψ x i = 0) →
      residual (fun μ => D.Acoef w μ) (D.Bcoef w θ) ψ = 0 := by
    intro D w θ ψ hψ
    have : ψ = fun _ _ => 0 := funext fun x => funext fun i => hψ x i
    subst this; exact hres D w θ
  refine ⟨hpos, hpos, ⟨0, fun n t _ => by rw [hz]; exact (hH2 t).le.trans (by simp)⟩,
    ⟨0, fun n t _ => by rw [hzb]; exact (hH2 t).le.trans (by simp)⟩,
    fun s _ => ⟨id, strictMono_id, fun ε hε => ⟨0, fun m _ n _ => by simp⟩,
      fun ε hε => ⟨0, fun m _ n _ => by simp⟩⟩, ?_, ?_⟩
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [hres' _ _ _ _ ?h1, eLpNorm_zero]
    intro x i; rfl
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [hres' _ _ _ _ ?h2, eLpNorm_zero]
    intro x i; rfl

/-- **Non-vacuity of `regular_branch`**: the flat regulator with the trivial Dirac model satisfies
all hypotheses (on the subslab `(T/3, 2T/3) × 𝕋³`). -/
theorem flatRegulator_regular_branch {T : ℝ} (hT : 0 < T) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (Lim : LimitFields Unit) (θ₀ : CoefficientBank Unit),
      StrongPacketOn (slabChart (T := T) (T / 3) (2 * T / 3) (by positivity) (by linarith)
        (by linarith))
        (fun k => (flatRegulator T).fields (ψ k)) Lim ∧
      BankTendsto (fun k => (flatRegulator T).bank (ψ k)) θ₀ ∧
      FirstVariationsConvergeOn (T := T) (trivialCarrier Unit) (T / 3) (2 * T / 3) (by positivity)
        (by linarith) (by linarith) (flatRegulator T).r0 (fun k => (flatRegulator T).fields (ψ k))
        (fun k => (flatRegulator T).bank (ψ k)) Lim θ₀ ∧
      IsDistributionalSolutionOn (T := T) (trivialCarrier Unit) (T / 3) (2 * T / 3) (by positivity)
        (by linarith) (by linarith) (flatRegulator T).r0 Lim θ₀ ∧
      SatisfiesEinsteinSMOn (T := T) (trivialCarrier Unit) (T / 3) (2 * T / 3) (by positivity)
        (by linarith) (by linarith) (flatRegulator T).r0 Lim θ₀ :=
  regular_branch (flatRegulator T) (by positivity) (by linarith) (by linarith) (a := 0) one_pos
    one_pos
    (flat_regularBosonicBound _ _ 1 1) (flatRegulator_coframeChart T _)
    ⟨_, isCompactBankSet_physical, fun n => rfl⟩ _ _ flat_regularSpinorHyp
    (flatRegulator_consistent hT) flatRegulator_stationary (trivialCarrier_yukawaContinuous Unit)
    id strictMono_id

end Flat

end RegularBranch
end EinsteinSM
end RenewalGeometry
