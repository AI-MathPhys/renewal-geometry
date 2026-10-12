/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.ActualJetSliceShift

/-!
# The actual jets of a completed Cauchy datum on the initial slice

Einstein–Standard-Model action-closure manuscript, `prop:generated-initial`
(`app:generated-dynamics`).  For a completion `D.mkTuple P ε _` of slice data `D`
(`ActualJetConstraintSlice`) we compute its actual jets on the slice `t = 0`:

* `mk_g`, `mk_dg`, `mk_ddg`, `mk_dA`, `mk_ddA`, `mk_dH`, `mk_ddH`, `mk_cψ`: value, first and second
  derivatives in terms of the slice data and the completion data;
* `agree_mk`: two completions agree to first order on the slice (`Agree`), and their second jets
  differ exactly by the differences of the completion data (`ddA_mk`, `ddH_mk`, `ddg_mk`,
  `cψ_mk`);
* `sd D W y` — the unit-lapse zero-shift `ContractedBianchiJet.SliceData` of the datum with
  acceleration `W`, valid (`sd_valid`) and harmonically initialised (`sd_harmonicInit`);
  `ofArrays_mk`: the metric 2-jet of the completion **is** `(sd D P.W y).jet`;
* consequently (`CF_mk`) the harmonic gauge defect vanishes on the slice, and (`einstein_mk_zero`,
  `einstein_mk_succ`) the normal components of the Einstein tensor are the **ADM Hamiltonian and
  momentum expressions** `G₀₀ = ½(R(γ) + (tr_γK)² - |K|²_γ)`, `G₀ᵢ = -(∇^jK_{ji} - ∂ᵢtr_γK)`
  (Gauss–Codazzi, `ContractedBianchiJet.SliceData.einM_zero_zero/_succ`);
* `e_mk_zero`: the adapted normal is `e₀ = ∂_t` on the slice (unit lapse, zero shift).
-/

open Finset
open scoped ContDiff

noncomputable section

namespace MathPhys.GenSlice

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState ActualJetGauge
  ActualJetSpinor SpinorProlongation SliceExt

set_option linter.unusedSectionVars false

/-! ### Calculus on `ℝ³` -/

theorem pd3_apply {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin 3 → ℝ) → ι → E} {y : Fin 3 → ℝ} (hF : DifferentiableAt ℝ F y) (k : Fin 3) (i : ι) :
    pd (fun y => F y i) k y = pd F k y i := by
  have h := pd_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) i) hF k
  simpa using h

theorem pd3_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : (Fin 3 → ℝ) → E}
    {y : Fin 3 → ℝ} (hF : DifferentiableAt ℝ F y) (c : ℝ) (k : Fin 3) :
    pd (fun y => c • F y) k y = c • pd F k y := by
  have h := pd_clm (c • ContinuousLinearMap.id ℝ E) hF k
  simpa using h

theorem pd3_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) (k : Fin 3)
    (y : Fin 3 → ℝ) : pd (fun _ : Fin 3 → ℝ => c) k y = 0 := by
  simp [SobolevOpen.pd]

theorem pd3_pd3_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : (Fin 3 → ℝ) → E}
    (hF : ContDiff ℝ ∞ F) (k l : Fin 3) (y : Fin 3 → ℝ) :
    pd (pd F k) l y = pd (pd F l) k y :=
  pd_pd_comm' (d := 2) hF k l y

/-- `pd` of a symmetric matrix field is symmetric. -/
theorem pd3_symm {F : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : ∀ y i j, F y i j = F y j i) (k : Fin 3) (y : Fin 3 → ℝ) (i j : Fin 3) :
    pd F k y i j = pd F k y j i := by
  have hd : ∀ y, DifferentiableAt ℝ F y := fun y => (hF.differentiable (by simp)) y
  have hdi : ∀ i, DifferentiableAt ℝ (fun y => F y i) y := fun i =>
    ((contDiff_pi.1 hF i).differentiable (by simp)) y
  rw [← pd3_apply (hd y) k i, ← pd3_apply (hdi i) k j, ← pd3_apply (hd y) k j,
    ← pd3_apply (hdi j) k i]
  have : (fun y => F y i j) = fun y => F y j i := funext fun y => hs y i j
  rw [this]

theorem contDiff_cons0 : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => (Fin.cons (0 : ℝ) y : ST 3)) := by
  refine contDiff_pi.2 fun μ => ?_
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp only [Fin.cons_zero]; exact contDiff_const
  · simp only [Fin.cons_succ]; exact contDiff_apply ℝ ℝ i

theorem cons0_add_zvec (y : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    (Fin.cons (0 : ℝ) (y + zvec k) : ST 3) = Fin.cons 0 y + sshift k := by
  rw [sshift, cons_add_cons, add_zero]

/-- Slices of periodic smooth space-time fields are periodic smooth fields on `ℝ³`. -/
theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => f (Fin.cons 0 y)) :=
  hf.comp contDiff_cons0

theorem per_slice {α : Type*} {f : ST 3 → α} (hf : IsSPeriodic f) :
    IsZPeriodic (fun y : Fin 3 → ℝ => f (Fin.cons 0 y)) := fun k y => by
  simp only [cons0_add_zvec, hf k]

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

namespace SliceCauchy

variable (D : SliceCauchy m V S S')

/-! ### The jets of a completion on the slice -/

section Jets

variable {P : Params m V S S'} {ε : ℝ} {hch : ∀ x, GChart (D.gF P ε x)} (y : Fin 3 → ℝ)

theorem mk_g : (D.mkTuple P ε hch).g (Fin.cons 0 y) = D.g0 y := textn_slice ε y

theorem mk_gi : (D.mkTuple P ε hch).gi (Fin.cons 0 y) = met4 (-1) 0 (D.γi y) := by
  show ginvOf ((D.mkTuple P ε hch).g (Fin.cons 0 y)) = _
  rw [D.mk_g y]; exact D.gi0_eq y

theorem pd_g0 (k : Fin 3) : pd D.g0 k y = met4 0 0 (pd D.γ k y) := by
  have := pd_met4 (a := fun _ => (-1 : ℝ)) (b := fun _ => (0 : Fin 3 → ℝ)) contDiff_const
    contDiff_const D.γ_smooth k y
  rw [pd3_const, pd3_const] at this
  exact this

theorem pd_g0_fun (k : Fin 3) : pd D.g0 k = fun y => met4 0 0 (pd D.γ k y) :=
  funext fun y => D.pd_g0 y k

theorem pd_pd_g0 (k l : Fin 3) : pd (pd D.g0 l) k y = met4 0 0 (pd (pd D.γ l) k y) := by
  rw [D.pd_g0_fun l]
  have := pd_met4 (a := fun _ => (0 : ℝ)) (b := fun _ => (0 : Fin 3 → ℝ)) contDiff_const
    contDiff_const (contDiff_pd3 D.γ_smooth l) k y
  rw [pd3_const, pd3_const] at this
  exact this

theorem pd_vt (k : Fin 3) :
    pd D.vt k y = met4 (pd D.v00 k y) (pd D.v0 k y) (fun i j => -2 * pd D.K k y i j) := by
  have := pd_met4 D.contDiff_v00 D.contDiff_v0 D.contDiff_negK k y
  refine this.trans ?_
  congr 1
  funext i j
  have h1 : pd (fun y i j => -2 * D.K y i j) k y = (-2 : ℝ) • pd D.K k y :=
    pd3_smul ((D.K_smooth.differentiable (by simp)) y) (-2) k
  rw [h1]; simp

variable (hε : ε ≠ 0)
include hε

theorem mk_dg (α : Fin 4) :
    (D.mkTuple P ε hch).dg (Fin.cons 0 y) α = Fin.cases (D.vt y) (fun j => pd D.g0 j y) α := by
  show pd (D.gF P ε) α (Fin.cons 0 y) = _
  refine Fin.cases ?_ (fun j => ?_) α
  · exact pd_textn_zero_slice hε D.contDiff_g0 D.contDiff_vt P.W_smooth y
  · exact pd_textn_succ_slice ε D.contDiff_g0 D.contDiff_vt P.W_smooth j y

theorem mk_ddg (β α : Fin 4) :
    (D.mkTuple P ε hch).ddg (Fin.cons 0 y) β α =
      Fin.cases (Fin.cases (P.W y) (fun j => pd D.vt j y) α)
        (fun k => Fin.cases (pd D.vt k y) (fun j => pd (pd D.g0 j) k y) α) β := by
  show pd (pd (D.gF P ε) α) β (Fin.cons 0 y) = _
  refine Fin.cases ?_ (fun k => ?_) β <;> refine Fin.cases ?_ (fun j => ?_) α
  · exact pd_pd_textn_zero_zero_slice hε D.contDiff_g0 D.contDiff_vt P.W_smooth y
  · exact pd_pd_textn_succ_zero_slice hε D.contDiff_g0 D.contDiff_vt P.W_smooth j y
  · exact pd_pd_textn_zero_succ_slice hε D.contDiff_g0 D.contDiff_vt P.W_smooth k y
  · exact pd_pd_textn_succ_succ_slice ε D.contDiff_g0 D.contDiff_vt P.W_smooth j k y

omit hε in
theorem mk_A : (D.mkTuple P ε hch).A (Fin.cons 0 y) = padL (D.A y) := textn_slice ε y

theorem mk_dA (γ : Fin 4) :
    pd (D.mkTuple P ε hch).A γ (Fin.cons 0 y) =
      Fin.cases (padL (D.Ad y)) (fun j => pd (fun y => padL (D.A y)) j y) γ := by
  show pd (D.AF P ε) γ (Fin.cons 0 y) = _
  refine Fin.cases ?_ (fun j => ?_) γ
  · exact pd_textn_zero_slice hε (contDiff_padA D.A_smooth) (contDiff_padA D.Ad_smooth)
      (contDiff_padA P.Aa_smooth) y
  · exact pd_textn_succ_slice ε (contDiff_padA D.A_smooth) (contDiff_padA D.Ad_smooth)
      (contDiff_padA P.Aa_smooth) j y

theorem mk_ddA (δ γ : Fin 4) :
    pd (pd (D.mkTuple P ε hch).A γ) δ (Fin.cons 0 y) =
      Fin.cases (Fin.cases (padL (P.Aa y)) (fun j => pd (fun y => padL (D.Ad y)) j y) γ)
        (fun k => Fin.cases (pd (fun y => padL (D.Ad y)) k y)
          (fun j => pd (pd (fun y => padL (D.A y)) j) k y) γ) δ := by
  show pd (pd (D.AF P ε) γ) δ (Fin.cons 0 y) = _
  have ha := contDiff_padA D.A_smooth
  have hb := contDiff_padA D.Ad_smooth
  have hc := contDiff_padA P.Aa_smooth
  refine Fin.cases ?_ (fun k => ?_) δ <;> refine Fin.cases ?_ (fun j => ?_) γ
  · exact pd_pd_textn_zero_zero_slice hε ha hb hc y
  · exact pd_pd_textn_succ_zero_slice hε ha hb hc j y
  · exact pd_pd_textn_zero_succ_slice hε ha hb hc k y
  · exact pd_pd_textn_succ_succ_slice ε ha hb hc j k y

omit hε in
theorem mk_H : (D.mkTuple P ε hch).H (Fin.cons 0 y) = D.H y := textn_slice ε y

theorem mk_dH (γ : Fin 4) :
    pd (D.mkTuple P ε hch).H γ (Fin.cons 0 y) = Fin.cases (D.Hd y) (fun j => pd D.H j y) γ := by
  show pd (D.HF P ε) γ (Fin.cons 0 y) = _
  refine Fin.cases ?_ (fun j => ?_) γ
  · exact pd_textn_zero_slice hε D.H_smooth D.Hd_smooth P.Ha_smooth y
  · exact pd_textn_succ_slice ε D.H_smooth D.Hd_smooth P.Ha_smooth j y

theorem mk_ddH (δ γ : Fin 4) :
    pd (pd (D.mkTuple P ε hch).H γ) δ (Fin.cons 0 y) =
      Fin.cases (Fin.cases (P.Ha y) (fun j => pd D.Hd j y) γ)
        (fun k => Fin.cases (pd D.Hd k y) (fun j => pd (pd D.H j) k y) γ) δ := by
  show pd (pd (D.HF P ε) γ) δ (Fin.cons 0 y) = _
  refine Fin.cases ?_ (fun k => ?_) δ <;> refine Fin.cases ?_ (fun j => ?_) γ
  · exact pd_pd_textn_zero_zero_slice hε D.H_smooth D.Hd_smooth P.Ha_smooth y
  · exact pd_pd_textn_succ_zero_slice hε D.H_smooth D.Hd_smooth P.Ha_smooth j y
  · exact pd_pd_textn_zero_succ_slice hε D.H_smooth D.Hd_smooth P.Ha_smooth k y
  · exact pd_pd_textn_succ_succ_slice ε D.H_smooth D.Hd_smooth P.Ha_smooth j k y

omit hε in
theorem mk_ψ : (D.mkTuple P ε hch).ψ (Fin.cons 0 y) = D.ψ y := textn_slice ε y

omit hε in
theorem mk_ψb : (D.mkTuple P ε hch).ψb (Fin.cons 0 y) = D.ψb y := textn_slice ε y

theorem mk_cψ (γ : Fin 4) :
    pd (D.mkTuple P ε hch).ψ γ (Fin.cons 0 y) = Fin.cases (P.ψd y) (fun j => pd D.ψ j y) γ := by
  show pd (D.ψF P ε) γ (Fin.cons 0 y) = _
  refine Fin.cases ?_ (fun j => ?_) γ
  · exact pd_textn_zero_slice hε D.ψ_smooth P.ψd_smooth contDiff_const y
  · exact pd_textn_succ_slice ε D.ψ_smooth P.ψd_smooth contDiff_const j y

theorem mk_cψb (γ : Fin 4) :
    pd (D.mkTuple P ε hch).ψb γ (Fin.cons 0 y) =
      Fin.cases (P.ψbd y) (fun j => pd D.ψb j y) γ := by
  show pd (D.ψbF P ε) γ (Fin.cons 0 y) = _
  refine Fin.cases ?_ (fun j => ?_) γ
  · exact pd_textn_zero_slice hε D.ψb_smooth P.ψbd_smooth contDiff_const y
  · exact pd_textn_succ_slice ε D.ψb_smooth P.ψbd_smooth contDiff_const j y

end Jets

/-! ### Two completions agree to first order -/

section Agreement

variable {P P' : Params m V S S'} {ε ε' : ℝ} {hch : ∀ x, GChart (D.gF P ε x)}
  {hch' : ∀ x, GChart (D.gF P' ε' x)} (hε : ε ≠ 0) (hε' : ε' ≠ 0) (y : Fin 3 → ℝ)
include hε hε'

theorem agree_mk :
    Agree ((D.mkTuple P ε hch).jet (Fin.cons 0 y)) ((D.mkTuple P' ε' hch').jet (Fin.cons 0 y)) := by
  have hg : (D.mkTuple P ε hch).g (Fin.cons 0 y) = (D.mkTuple P' ε' hch').g (Fin.cons 0 y) := by
    rw [D.mk_g, D.mk_g]
  have hgi : (D.mkTuple P ε hch).gi (Fin.cons 0 y) = (D.mkTuple P' ε' hch').gi (Fin.cons 0 y) := by
    rw [D.mk_gi, D.mk_gi]
  have hdg : (D.mkTuple P ε hch).dg (Fin.cons 0 y) = (D.mkTuple P' ε' hch').dg (Fin.cons 0 y) := by
    funext α; rw [D.mk_dg y hε, D.mk_dg y hε']
  refine ⟨hg, hgi, hdg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (D.mkTuple P ε hch).e (Fin.cons 0 y) = (D.mkTuple P' ε' hch').e (Fin.cons 0 y)
    funext A μ; simp only [Tuple.e, hgi]
  · show (D.mkTuple P ε hch).de (Fin.cons 0 y) = (D.mkTuple P' ε' hch').de (Fin.cons 0 y)
    funext γ A μ; simp only [Tuple.de, hgi, hdg]
  · show (D.mkTuple P ε hch).A (Fin.cons 0 y) = (D.mkTuple P' ε' hch').A (Fin.cons 0 y)
    rw [D.mk_A, D.mk_A]
  · show (fun γ μ => pd (D.mkTuple P ε hch).A γ (Fin.cons 0 y) μ) =
      fun γ μ => pd (D.mkTuple P' ε' hch').A γ (Fin.cons 0 y) μ
    funext γ μ; rw [D.mk_dA y hε, D.mk_dA y hε']
  · show (D.mkTuple P ε hch).H (Fin.cons 0 y) = (D.mkTuple P' ε' hch').H (Fin.cons 0 y)
    rw [D.mk_H, D.mk_H]
  · show (fun γ => pd (D.mkTuple P ε hch).H γ (Fin.cons 0 y)) =
      fun γ => pd (D.mkTuple P' ε' hch').H γ (Fin.cons 0 y)
    funext γ; rw [D.mk_dH y hε, D.mk_dH y hε']
  · show (D.mkTuple P ε hch).ψ (Fin.cons 0 y) = (D.mkTuple P' ε' hch').ψ (Fin.cons 0 y)
    rw [D.mk_ψ, D.mk_ψ]
  · show (D.mkTuple P ε hch).ψb (Fin.cons 0 y) = (D.mkTuple P' ε' hch').ψb (Fin.cons 0 y)
    rw [D.mk_ψb, D.mk_ψb]
  · intro j
    show pd (D.mkTuple P ε hch).ψ j.succ (Fin.cons 0 y) =
      pd (D.mkTuple P' ε' hch').ψ j.succ (Fin.cons 0 y)
    rw [D.mk_cψ y hε, D.mk_cψ y hε']; rfl
  · intro j
    show pd (D.mkTuple P ε hch).ψb j.succ (Fin.cons 0 y) =
      pd (D.mkTuple P' ε' hch').ψb j.succ (Fin.cons 0 y)
    rw [D.mk_cψb y hε, D.mk_cψb y hε']; rfl

/-- The second gauge jets of two completions differ by `∂_t²A' - ∂_t²A`. -/
theorem ddA_mk :
    ((D.mkTuple P' ε' hch').jet (Fin.cons 0 y)).ddA = fun a b c =>
      ((D.mkTuple P ε hch).jet (Fin.cons 0 y)).ddA a b c +
        (if a = 0 ∧ b = 0 then padL (P'.Aa y - P.Aa y) c else 0) := by
  funext a b c
  show pd (pd (D.mkTuple P' ε' hch').A b) a (Fin.cons 0 y) c =
    pd (pd (D.mkTuple P ε hch).A b) a (Fin.cons 0 y) c + _
  rw [D.mk_ddA y hε, D.mk_ddA y hε']
  refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
    simp [Fin.succ_ne_zero]

theorem ddH_mk :
    ((D.mkTuple P' ε' hch').jet (Fin.cons 0 y)).ddH = fun a b =>
      ((D.mkTuple P ε hch).jet (Fin.cons 0 y)).ddH a b +
        (if a = 0 ∧ b = 0 then P'.Ha y - P.Ha y else 0) := by
  funext a b
  show pd (pd (D.mkTuple P' ε' hch').H b) a (Fin.cons 0 y) =
    pd (pd (D.mkTuple P ε hch).H b) a (Fin.cons 0 y) + _
  rw [D.mk_ddH y hε, D.mk_ddH y hε']
  refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
    simp [Fin.succ_ne_zero]

theorem ddg_mk :
    (D.mkTuple P' ε' hch').ddg (Fin.cons 0 y) = fun a b c d =>
      (D.mkTuple P ε hch).ddg (Fin.cons 0 y) a b c d +
        (if a = 0 ∧ b = 0 then (P'.W y - P.W y) c d else 0) := by
  funext a b c d
  rw [D.mk_ddg y hε, D.mk_ddg y hε']
  refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
    simp [Fin.succ_ne_zero]

theorem cψ_mk :
    ((D.mkTuple P' ε' hch').jet (Fin.cons 0 y)).cψ = fun γ =>
      ((D.mkTuple P ε hch).jet (Fin.cons 0 y)).cψ γ +
        (if γ = 0 then P'.ψd y - P.ψd y else 0) := by
  funext γ
  show pd (D.mkTuple P' ε' hch').ψ γ (Fin.cons 0 y) =
    pd (D.mkTuple P ε hch).ψ γ (Fin.cons 0 y) + _
  rw [D.mk_cψ y hε, D.mk_cψ y hε']
  refine Fin.cases ?_ (fun j => ?_) γ <;> simp [Fin.succ_ne_zero]

theorem cψb_mk :
    ((D.mkTuple P' ε' hch').jet (Fin.cons 0 y)).cψb = fun γ =>
      ((D.mkTuple P ε hch).jet (Fin.cons 0 y)).cψb γ +
        (if γ = 0 then P'.ψbd y - P.ψbd y else 0) := by
  funext γ
  show pd (D.mkTuple P' ε' hch').ψb γ (Fin.cons 0 y) =
    pd (D.mkTuple P ε hch).ψb γ (Fin.cons 0 y) + _
  rw [D.mk_cψb y hε, D.mk_cψb y hε']
  refine Fin.cases ?_ (fun j => ?_) γ <;> simp [Fin.succ_ne_zero]

end Agreement

/-! ### The unit-lapse zero-shift slice jet -/

/-- The slice jet of the datum with acceleration `W` (Gauss–Codazzi conventions of
`ContractedBianchiJet.SliceData`: `γ`, `γ⁻¹`, `∂γ`, `∂∂γ`, `K`, `∂K`, the harmonic completion
`(v₀₀, v₀ᵢ)` of the lapse and shift time derivatives and their spatial derivatives). -/
def sd (W : Met) (y : Fin 3 → ℝ) : ContractedBianchiJet.SliceData :=
  ⟨Matrix.of (D.γ y), Matrix.of (D.γi y), fun k => Matrix.of (pd D.γ k y),
    fun k l => Matrix.of (pd (pd D.γ l) k y), Matrix.of (D.K y), fun k => Matrix.of (pd D.K k y),
    D.v00 y, D.v0 y, fun k => pd D.v00 k y, fun k => pd D.v0 k y, Matrix.of W⟩

theorem sd_valid {W : Met} (hW : ∀ μ ν, W μ ν = W ν μ) (y : Fin 3 → ℝ) : (D.sd W y).Valid where
  γγi := by
    ext i j
    simp only [sd, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact D.γ_mul_γi y i j
  γ_symm := by ext i j; simp [sd, D.γ_symm y j i]
  γi_symm := by ext i j; simp [sd, D.γi_symm y j i]
  dγ_symm := fun k => by ext i j; simp [sd, pd3_symm D.γ_smooth D.γ_symm k y j i]
  ddγ_symm := fun k l => by
    ext i j
    simp only [sd, Matrix.transpose_apply, Matrix.of_apply]
    exact pd3_symm (contDiff_pd3 D.γ_smooth l) (fun y i j => pd3_symm D.γ_smooth D.γ_symm l y i j)
      k y j i
  ddγ_comm := fun k l => by
    ext i j
    simp only [sd, Matrix.of_apply]
    rw [pd3_pd3_comm D.γ_smooth l k y]
  K_symm := by ext i j; simp [sd, D.K_symm y j i]
  dK_symm := fun k => by ext i j; simp [sd, pd3_symm D.K_smooth D.K_symm k y j i]
  w_symm := by ext μ ν; simp [sd, hW ν μ]

theorem sd_harmonicInit (W : Met) (y : Fin 3 → ℝ) : (D.sd W y).HarmonicInit :=
  ⟨rfl, fun _ => rfl⟩

/-- **The metric 2-jet of a completion on the slice is the slice jet** (in the array
conventions of `HarmonicDefect`). -/
theorem ofArrays_mk {P : Params m V S S'} {ε : ℝ} {hch : ∀ x, GChart (D.gF P ε x)} (hε : ε ≠ 0)
    (y : Fin 3 → ℝ) :
    ContractedBianchiJet.ofArrays ((D.mkTuple P ε hch).g (Fin.cons 0 y))
        ((D.mkTuple P ε hch).gi (Fin.cons 0 y)) ((D.mkTuple P ε hch).dg (Fin.cons 0 y))
        ((D.mkTuple P ε hch).ddg (Fin.cons 0 y)) = (D.sd (P.W y) y).jet := by
  have hK : Matrix.of (fun i j => -2 * D.K y i j) = (-2 : ℝ) • Matrix.of (D.K y) := by
    ext i j; simp
  have hdK : ∀ k, Matrix.of (fun i j => -2 * pd D.K k y i j) = (-2 : ℝ) • Matrix.of (pd D.K k y) := by
    intro k; ext i j; simp
  simp only [ContractedBianchiJet.ofArrays, ContractedBianchiJet.SliceData.jet]
  congr 1
  · rw [D.mk_g]; exact of_met4 _ _ _
  · rw [D.mk_gi]; exact of_met4 _ _ _
  · funext a
    rw [D.mk_dg y hε]
    refine Fin.cases ?_ (fun k => ?_) a
    · simp only [Fin.cases_zero, vt, of_met4, hK]; rfl
    · simp only [Fin.cases_succ, D.pd_g0, of_met4]; rfl
  · funext a b
    rw [D.mk_ddg y hε]
    refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun l => ?_) b
    · rfl
    · simp only [Fin.cases_zero, Fin.cases_succ, D.pd_vt, of_met4, hdK]; rfl
    · simp only [Fin.cases_zero, Fin.cases_succ, D.pd_vt, of_met4, hdK]; rfl
    · simp only [Fin.cases_succ, D.pd_pd_g0, of_met4]; rfl

/-- **The harmonic gauge defect of a completion vanishes on the slice** (harmonic
initialisation of the lapse and shift time derivatives). -/
theorem CF_mk {P : Params m V S S'} {ε : ℝ} {hch : ∀ x, GChart (D.gF P ε x)} (hε : ε ≠ 0)
    (y : Fin 3 → ℝ) : CF (D.mkTuple P ε hch) (Fin.cons 0 y) = 0 := by
  funext l
  have h := ContractedBianchiJet.gcUp_ofArrays (g := (D.mkTuple P ε hch).g (Fin.cons 0 y))
    (gi := (D.mkTuple P ε hch).gi (Fin.cons 0 y)) (dg := (D.mkTuple P ε hch).dg (Fin.cons 0 y))
    (ddg := (D.mkTuple P ε hch).ddg (Fin.cons 0 y)) l
  rw [D.ofArrays_mk hε y] at h
  rw [ContractedBianchiJet.SliceData.gcUp_harmonicInit (D.sd_valid (P.W_symm y) y)
    (D.sd_harmonicInit _ y)] at h
  show cUp _ _ l = 0
  exact h.symm

end SliceCauchy

end MathPhys.GenSlice
