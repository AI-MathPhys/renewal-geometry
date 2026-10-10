/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedHarmonicPropagation
import RenewalGeometry.Continuum.GeneratedPhysicalIdentification

/-!
# Physical identification of the symmetric extension from constrained data

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`): assembly of the constraint propagation
(`GenGauss.gauss_propagation`, `GenHarmonic.harmonic_propagation`, with the current and stress
Noether identities of the theory data) and the uniqueness identification
(`GenPhysId.kato_eq_physical_state`, `KatoStab.twoSided_unique`).

## The constrained data class

* `ConstrainedData SM κ U₀` — `U₀` is, on the initial slice `t = 0`, the actual-jet state of a
  smooth field tuple `z₀` which satisfies the complete Einstein–Standard-Model equations (all
  residuals vanish), the harmonic gauge condition `C = 0` and `∂_tC = 0` **on the initial slice**
  (the initial-data constraints with the harmonic initial completion of `prop:generated-initial`;
  only the slice values of `z₀` and its first normal jets enter).
* **Transfer to any other tuple with the same data** (`constraints_transfer`): if the actual-jet
  state of a tuple `z` solves the symmetric system on the slice and agrees with that of `z₀`
  there, then `z` has vanishing Gauss constraint, `C` and `∂_tC` on the slice — the Gauss
  constraint involves only tangential derivatives of the field strength (`gauss_eq_of_slice`), and
  `∂_tC` is fixed by the metric rows of the symmetric system (`ddg_eq_of_slice`: the second
  derivatives of the metric are determined by the state and its first derivatives).

## Main results

* **`physical_of_smooth_state`** — for theory data with smooth sources and the current and stress
  Noether identities, a smooth tuple whose actual-jet state solves the independent symmetric
  system on `(-ε, ε) × 𝕋³` with constrained initial data is a physical solution on `[0, ε) × 𝕋³`.
* `SmoothStateSolution` — existence of such a smooth tuple (a classical solution of the symmetric
  system in the class of actual-jet states of field tuples) for the datum `U₀`.
* **`generated_physical_identification_of_smoothState`** — `lem:generated-physical-
  identification` for the actual-jet system: every constrained datum has a two-sided Kato solution
  of the realized symmetric system on `(-T, T)` (`T` depending only on the `H^q` radius), and
  whenever a smooth actual-jet solution with this datum exists (`SmoothStateSolution`), there is
  `t₁ > 0` such that on `[0, t₁] × 𝕋³` the Kato solution is the actual-jet state of a physical
  solution: its head fields satisfy the complete Einstein, Yang–Mills, Higgs, Dirac equations and
  the harmonic and temporal-gauge constraints.

Disclosed: `Σ = 𝕋³`; smooth data with an `H^q` bound; theory data with the current and stress
Noether identities (proved for variational Yang–Mills–Higgs data, `GenNoether.adjSM_currentNoether`,
`GenStress.adjSM_stressNoether`; Dirac sector decoupled).  `SmoothStateSolution` (existence of a
smooth solution of the symmetric system whose auxiliary variables are the actual jets of its head
fields — local existence for the reduced Einstein–Standard-Model equations in first-order form) is
the remaining analytic input; it is NOT derived here.
-/

open Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.GenPhysIdClosed

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk QLEnergy KatoGalerkin FrameCurvature HarmonicDefect
  ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge
  ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenNoether
  GenGauss GenStress GenHarmonic GenPhysId

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Slice calculus -/

section Slice

/-- Two fields agreeing on a time slice have the same spatial derivatives there. -/
theorem pd_eq_of_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ST 3 → E}
    {t : ℝ} (h : ∀ y : Fin 3 → ℝ, f (Fin.cons t y) = f' (Fin.cons t y)) {x : ST 3} (hx : x 0 = t)
    (hf : DifferentiableAt ℝ f x) (hf' : DifferentiableAt ℝ f' x) (j : Fin 3) :
    pd f j.succ x = pd f' j.succ x := by
  have hline : ∀ s : ℝ, x + s • ev j.succ = Fin.cons t (Fin.tail x + s • Pi.single j 1) := by
    intro s
    funext q
    induction q using Fin.cases with
    | zero => simp [ev, hx]
    | succ q => simp [ev, Pi.single_apply, Fin.succ_inj, Fin.tail]
  have e : (fun s : ℝ => f' (x + s • ev j.succ)) = fun s => f (x + s • ev j.succ) :=
    funext fun s => by rw [hline, h]
  have h1 := hasDerivAt_line0 hf' j.succ
  rw [e] at h1
  exact pd_eq_of_line hf h1

theorem cons_tail_eq {x : ST 3} {t : ℝ} (hx : x 0 = t) : (Fin.cons t (Fin.tail x) : ST 3) = x := by
  rw [← hx]; exact Fin.cons_self_tail x

/-- A frame-contracted normal derivative of an antisymmetric family vanishes:
`Σ_ν e_0^ν Σ_{μ,ρ} g^{μρ} X_{ρμν} = 0` when `X_{jμν} = 0` for spatial `j` and `g^{μ0} = -e_0^0e_0^μ`. -/
theorem contr_normal {M : Type*} [AddCommGroup M] [Module ℝ M] (e0 : Fin 4 → ℝ)
    (gi : Fin 4 → Fin 4 → ℝ) (hgi0 : ∀ μ, gi μ 0 = -(e0 0 * e0 μ))
    (X : Fin 4 → Fin 4 → Fin 4 → M) (hX : ∀ ρ μ ν, X ρ ν μ = -X ρ μ ν)
    (hsp : ∀ (j : Fin 3) μ ν, X j.succ μ ν = 0) :
    ∑ ν, e0 ν • ∑ μ, ∑ ρ, gi μ ρ • X ρ μ ν = 0 := by
  have h1 : ∀ ν, e0 ν • ∑ μ, ∑ ρ, gi μ ρ • X ρ μ ν = ∑ μ, (-(e0 0) * (e0 μ * e0 ν)) • X 0 μ ν := by
    intro ν
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Fin.sum_univ_succ]
    simp only [hsp, smul_zero, Finset.sum_const_zero, add_zero, hgi0, smul_smul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun ν _ => h1 ν, Finset.sum_comm]
  simp only [← smul_smul (-(e0 0)), ← Finset.smul_sum]
  rw [GenNoether.sum_sym_anti_eq_zero (fun μ ν => e0 μ * e0 ν) (fun μ ν => X 0 μ ν)
    (fun μ ν => mul_comm _ _) (fun μ ν => hX 0 μ ν), smul_zero]

end Slice

/-! ### Transfer of the constraints between tuples with the same data -/

section Transfer

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S')

theorem firstJet_eq {z z0 : Tuple m V S S'} {x : ST 3} (h : stateF SM z x = stateF SM z0 x) :
    (z.jet x).firstJet SM = (z0.jet x).firstJet SM := by
  rw [← ActualJet.recon_state, ← ActualJet.recon_state]
  exact congrArg (recon SM) (congrArg ofP h)

/-- **The harmonic defect is a function of the state.** -/
theorem CF_eq_of_state {z z0 : Tuple m V S S'} {x : ST 3} (h : stateF SM z x = stateF SM z0 x) :
    CF z x = CF z0 x := by
  have hfj := firstJet_eq SM h
  have hgi : z.gi x = z0.gi x := congrArg FirstJet.gi hfj
  have hdg : z.dg x = z0.dg x := congrArg FirstJet.dg hfj
  unfold CF
  rw [hgi, hdg]

/-- **The second derivatives of the metric are fixed by the symmetric system**: if the actual-jet
states of two tuples solve the symmetric system at a point of a slice on which they agree, the
metric 2-jets agree there (the `p`- and `q`-rows give the frame components `e_A{}^β∂_γ∂_βg`). -/
theorem ddg_eq_of_slice {z z0 : Tuple m V S S'} {t : ℝ}
    (hS : ∀ y : Fin 3 → ℝ, stateF SM z (Fin.cons t y) = stateF SM z0 (Fin.cons t y)) {x : ST 3}
    (hx : x 0 = t) (hsym : SymEqAt SM z x) (hsym0 : SymEqAt SM z0 x) : z.ddg x = z0.ddg x := by
  have hSx : stateF SM z x = stateF SM z0 x := by
    have := hS (Fin.tail x); rwa [cons_tail_eq hx] at this
  have hdiff : ∀ (w : Tuple m V S S'), DifferentiableAt ℝ (stateF SM w) x := fun w =>
    (contDiff_stateF SM w).differentiable (by simp) x
  have hsp : ∀ j : Fin 3, pd (stateF SM z) j.succ x = pd (stateF SM z0) j.succ x := fun j =>
    pd_eq_of_slice hS hx (hdiff z) (hdiff z0) j
  have ht : pd (stateF SM z) 0 x = pd (stateF SM z0) 0 x := by
    have h1 := hsym
    have h2 := hsym0
    unfold SymEqAt at h1 h2
    rw [hSx] at h1
    simp only [hsp] at h1
    exact add_right_cancel (h1.trans h2.symm)
  have hd : ∀ γ, (z.jet x).dstate SM γ = (z0.jet x).dstate SM γ := by
    intro γ
    have : toP ((z.jet x).dstate SM γ) = toP ((z0.jet x).dstate SM γ) := by
      rw [← pd_stateF SM z x γ, ← pd_stateF SM z0 x γ]
      induction γ using Fin.cases with
      | zero => exact ht
      | succ j => exact hsp j
    exact congrArg ofP this
  have hfj := firstJet_eq SM hSx
  have hdg : z.dg x = z0.dg x := congrArg FirstJet.dg hfj
  have hde : z.de x = z0.de x := congrArg FirstJet.de hfj
  have hAF : (z.jet x).AF = (z0.jet x).AF := congrArg FirstJet.AF hfj
  have he : z.e x = z0.e x := by
    funext A μ
    rw [← Tuple.jet_AF_fr, ← Tuple.jet_AF_fr, hAF]
  funext γ β μ ν
  -- frame components of the difference vanish
  set w : Fin 4 → ℝ := fun β => z.ddg x γ β μ ν - z0.ddg x γ β μ ν with hw
  have hcomp : ∀ A, ∑ β, z.e x A β * w β = 0 := by
    intro A
    have key : ∀ (B : Fin 4), (∑ β, ((z.jet x).FJ.de γ B β * (z.jet x).FJ.dg β μ ν +
        (z.jet x).AF.fr B β * (z.jet x).FJ.ddg γ β μ ν)) =
        ∑ β, ((z0.jet x).FJ.de γ B β * (z0.jet x).FJ.dg β μ ν +
        (z0.jet x).AF.fr B β * (z0.jet x).FJ.ddg γ β μ ν) → ∑ β, z.e x B β * w β = 0 := by
      intro B hB
      simp only [show (z.jet x).FJ.de = z.de x from rfl, show (z0.jet x).FJ.de = z0.de x from rfl,
        show (z.jet x).FJ.dg = z.dg x from rfl, show (z0.jet x).FJ.dg = z0.dg x from rfl,
        show (z.jet x).FJ.ddg = z.ddg x from rfl, show (z0.jet x).FJ.ddg = z0.ddg x from rfl,
        Tuple.jet_AF_fr, hde, hdg, ← he] at hB
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hB
      rw [← hB]
      exact Finset.sum_congr rfl fun β _ => by rw [hw]; ring
    induction A using Fin.cases with
    | zero =>
      refine key 0 ?_
      have := congrArg (fun U => U.p μ ν) (hd γ)
      simpa [ActualJet.dstate, AdaptedFrame.dpJ] using this
    | succ a =>
      refine key a.succ ?_
      have := congrArg (fun U => U.q a μ ν) (hd γ)
      simpa [ActualJet.dstate, AdaptedFrame.dqJ] using this
  have hinv := ActualJetRecon.inv_vec (z.jet x).FJ w β
  have h0 : w β = 0 := by
    rw [hinv]
    refine Finset.sum_eq_zero fun A _ => ?_
    have : ∑ β', (z.jet x).FJ.e A β' • w β' = 0 := by
      simp only [smul_eq_mul]
      exact hcomp A
    rw [this, smul_zero]
  rw [hw] at h0
  linarith

/-- **`∂_tC` is fixed by the symmetric system** (via the metric 2-jet). -/
theorem pdCF_eq_of_slice {z z0 : Tuple m V S S'} {t : ℝ}
    (hS : ∀ y : Fin 3 → ℝ, stateF SM z (Fin.cons t y) = stateF SM z0 (Fin.cons t y)) {x : ST 3}
    (hx : x 0 = t) (hsym : SymEqAt SM z x) (hsym0 : SymEqAt SM z0 x) (γ : Fin 4) :
    pd (CF z) γ x = pd (CF z0) γ x := by
  have hSx : stateF SM z x = stateF SM z0 x := by
    have := hS (Fin.tail x); rwa [cons_tail_eq hx] at this
  have hfj := firstJet_eq SM hSx
  have hgi : z.gi x = z0.gi x := congrArg FirstJet.gi hfj
  have hdg : z.dg x = z0.dg x := congrArg FirstJet.dg hfj
  rw [pd_CF z x γ, pd_CF z0 x γ, hgi, hdg, ddg_eq_of_slice SM hS hx hsym hsym0]

/-- **The Gauss constraint is a function of the data on the slice**: it involves only tangential
derivatives of the field strength. -/
theorem gauss_eq_of_slice {z z0 : Tuple m V S S'} {t : ℝ}
    (hS : ∀ y : Fin 3 → ℝ, stateF SM z (Fin.cons t y) = stateF SM z0 (Fin.cons t y)) {x : ST 3}
    (hx : x 0 = t) : gaussF SM z x = gaussF SM z0 x := by
  have hSx : stateF SM z x = stateF SM z0 x := by
    have := hS (Fin.tail x); rwa [cons_tail_eq hx] at this
  have hfj := firstJet_eq SM hSx
  have hg : z.g x = z0.g x := congrArg FirstJet.g hfj
  have hgi : z.gi x = z0.gi x := congrArg FirstJet.gi hfj
  have hdg : z.dg x = z0.dg x := congrArg FirstJet.dg hfj
  have hA : (z.jet x).A = (z0.jet x).A := congrArg FirstJet.A hfj
  have hF : Fm (z.jet x).A (z.jet x).dA = Fm (z0.jet x).A (z0.jet x).dA := congrArg FirstJet.F hfj
  have hH : (z.jet x).H = (z0.jet x).H := congrArg FirstJet.H hfj
  have hDH : ActualJetGauge.DH (z.jet x).A (z.jet x).H (z.jet x).dH =
      ActualJetGauge.DH (z0.jet x).A (z0.jet x).H (z0.jet x).dH := congrArg FirstJet.DH hfj
  have hψ : (z.jet x).ψ = (z0.jet x).ψ := congrArg FirstJet.ψ hfj
  have hψb : (z.jet x).ψb = (z0.jet x).ψb := congrArg FirstJet.ψb hfj
  -- tangential derivatives of the field strength agree
  have hFld : ∀ y : Fin 3 → ℝ, Fld z (Fin.cons t y) = Fld z0 (Fin.cons t y) := by
    intro y
    have hS' := firstJet_eq SM (hS y)
    exact congrArg FirstJet.F hS'
  have hdF : ∀ (j : Fin 3) μ ν, dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA j.succ μ ν =
      dFm (z0.jet x).A (z0.jet x).dA (z0.jet x).ddA j.succ μ ν := by
    intro j μ ν
    have h1 := pd_eq_of_line ((contDiff_Fld z μ ν).differentiable (by simp) x) (z.line_Fm x j.succ μ ν)
    have h2 := pd_eq_of_line ((contDiff_Fld z0 μ ν).differentiable (by simp) x)
      (z0.line_Fm x j.succ μ ν)
    rw [← h1, ← h2]
    exact pd_eq_of_slice (f := fun y => Fld z y μ ν) (f' := fun y => Fld z0 y μ ν)
      (fun y => by rw [hFld y]) hx ((contDiff_Fld z μ ν).differentiable (by simp) x)
      ((contDiff_Fld z0 μ ν).differentiable (by simp) x) j
  -- the difference of the Gauss constraints is a normal contraction
  have hgi0 : ∀ μ, z.gi x μ 0 = -((frameU (z.gi x)).fr 0 0 * (frameU (z.gi x)).fr 0 μ) := by
    intro μ
    rw [(GenGauss.adapted z x) μ 0, Fin.sum_univ_three]
    simp only [AdaptedFrame.fr_succ_zero, mul_zero, add_zero]
    ring
  unfold gaussF
  have hdiff : ∑ ν, (frameU (z.gi x)).fr 0 ν • (bosF SM z x).2.1 ν -
      ∑ ν, (frameU (z0.gi x)).fr 0 ν • (bosF SM z0 x).2.1 ν =
      ∑ ν, (frameU (z.gi x)).fr 0 ν • ∑ μ, ∑ ρ, z.gi x μ ρ •
        (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA ρ μ ν -
          dFm (z0.jet x).A (z0.jet x).dA (z0.jet x).ddA ρ μ ν) := by
    rw [← hgi, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← smul_sub]
    congr 1
    show ymRes _ _ _ _ _ _ ν - ymRes _ _ _ _ _ _ ν = _
    unfold ymRes ymDiv
    simp only [show (z.jet x).FJ.gi = z.gi x from rfl, show (z0.jet x).FJ.gi = z0.gi x from rfl,
      show (z.jet x).FJ.dg = z.dg x from rfl, show (z0.jet x).FJ.dg = z0.dg x from rfl,
      show (z.jet x).FJ.g = z.g x from rfl, show (z0.jet x).FJ.g = z0.g x from rfl,
      ← hgi, ← hdg, ← hg]
    simp only [hF, hDH]
    simp only [hA, hH, hψ, hψb]
    rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← smul_sub]
    congr 1
    abel
  have hzero := contr_normal ((frameU (z.gi x)).fr 0) (z.gi x) hgi0
    (fun ρ μ ν => dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA ρ μ ν -
      dFm (z0.jet x).A (z0.jet x).dA (z0.jet x).ddA ρ μ ν)
    (fun ρ μ ν => by
      rw [dFm_anti (z.jet x).A (z.jet x).dA (z.jet x).ddA ρ μ ν,
        dFm_anti (z0.jet x).A (z0.jet x).dA (z0.jet x).ddA ρ μ ν]
      abel)
    (fun j μ ν => by rw [hdF j μ ν, sub_self])
  rw [← sub_eq_zero, hdiff, hzero]

end Transfer

/-! ### Constrained data and the physical identification of smooth solutions -/

section Physical

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S')

/-- **A tuple is constrained on the initial slice**: all physical residuals, the harmonic defect
and its time derivative vanish on `t = 0` (the initial-data constraints with the harmonic initial
completion). -/
def SliceConstrained (z₀ : Tuple m V S S') : Prop :=
  ∀ y : Fin 3 → ℝ, bosF SM z₀ (Fin.cons 0 y) = 0 ∧ dirF SM z₀ (Fin.cons 0 y) = 0 ∧
    CF z₀ (Fin.cons 0 y) = 0 ∧ pd (CF z₀) 0 (Fin.cons 0 y) = 0

/-- **The constrained data class** (`prop:generated-initial`): `U₀` is, on the initial slice, the
actual-jet state (in the coordinates `κ`) of a smooth tuple constrained on that slice. -/
def ConstrainedData (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (U₀ : Fin (dimS m V S S') → ST 3 → ℝ) : Prop :=
  ∃ z₀ : Tuple m V S S', (∀ b y, stU κ SM z₀ b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
    SliceConstrained SM z₀

theorem zero_on_slice_pd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    (hf : ContDiff ℝ ∞ f) {t : ℝ} (h : ∀ y : Fin 3 → ℝ, f (Fin.cons t y) = 0) {x : ST 3}
    (hx : x 0 = t) (j : Fin 3) : pd f j.succ x = 0 := by
  have := pd_eq_of_slice (f' := fun _ => (0 : E)) (fun y => h y) hx
    (hf.differentiable (by simp) x) (differentiableAt_const _) j
  rw [this]
  simp [SobolevOpen.pd]

/-- A slice-constrained tuple satisfies the symmetric system on the slice. -/
theorem symEqAt_of_sliceConstrained (hS : SMSmooth SM) {z₀ : Tuple m V S S'}
    (h : SliceConstrained SM z₀) (y : Fin 3 → ℝ) : SymEqAt SM z₀ (Fin.cons 0 y) := by
  rw [symEqAt_iff]
  obtain ⟨hB, hD, hC, hdC⟩ := h y
  have hdD : ∀ j : Fin 3, pd (dirF SM z₀) j.succ (Fin.cons 0 y) = 0 := fun j =>
    zero_on_slice_pd (contDiff_dirF SM z₀) (fun y' => (h y').2.1) rfl j
  have hdCs : ∀ j : Fin 3, pd (CF z₀) j.succ (Fin.cons 0 y) = 0 := fun j =>
    zero_on_slice_pd (contDiff_CF z₀) (fun y' => (h y').2.2.1) rfl j
  unfold errF
  rw [hB, hD, hC, hdC]
  simp only [hdD, hdCs, map_zero, add_zero, Finset.sum_const_zero]

variable {SM}

/-- **Physical identification of a smooth solution of the symmetric system from constrained data**
(`lem:generated-physical-identification`, smooth form): for theory data with smooth sources and
the current and stress Noether identities, if the actual-jet state of a smooth tuple `z` solves the
independent symmetric system on `(-ε, ε) × 𝕋³` and agrees on the initial slice with that of a
slice-constrained tuple `z₀`, then `z` is a physical solution on `[0, ε) × 𝕋³`: its Einstein,
Yang–Mills, Higgs, Dirac and dual Dirac residuals and its harmonic defect vanish there. -/
theorem physical_of_smooth_state (hN : CurrentNoether SM) (hT : StressNoether SM)
    (hS : SMSmooth SM) {z z₀ : Tuple m V S S'} {ε : ℝ} (hε : 0 < ε)
    (hsym : ∀ x ∈ openSlab (-ε) ε, SymEqAt SM z x)
    (hS0 : ∀ y : Fin 3 → ℝ, stateF SM z (Fin.cons 0 y) = stateF SM z₀ (Fin.cons 0 y))
    (hC0 : SliceConstrained SM z₀) :
    ∀ x : ST 3, 0 ≤ x 0 → x 0 < ε → bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 := by
  have hslice : ∀ y : Fin 3 → ℝ, (Fin.cons 0 y : ST 3) ∈ openSlab (-ε) ε := fun y =>
    ⟨by show -ε < 0; linarith, hε⟩
  -- the constraints of `z` on the slice
  have hG : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons 0 y) = 0 := by
    intro y
    rw [gauss_eq_of_slice SM hS0 rfl]
    unfold gaussF
    rw [(hC0 y).1]
    simp
  have hC : ∀ y : Fin 3 → ℝ, CF z (Fin.cons 0 y) = 0 := fun y => by
    rw [CF_eq_of_state SM (hS0 y)]; exact (hC0 y).2.2.1
  have hdC : ∀ y : Fin 3 → ℝ, pd (CF z) 0 (Fin.cons 0 y) = 0 := fun y => by
    rw [pdCF_eq_of_slice SM hS0 rfl (hsym _ (hslice y)) (symEqAt_of_sliceConstrained SM hS hC0 y)]
    exact (hC0 y).2.2.2
  have hphys := physical_of_constraints SM z hN hT hS (a := -ε) (by linarith) hsym hG hC hdC
  intro x hx0 hxε
  rcases hx0.lt_or_eq with hpos | hzero
  · exact hphys x ⟨hpos, hxε⟩
  · -- on the initial slice
    have hx : x = Fin.cons 0 (Fin.tail x) := (cons_tail_eq hzero.symm).symm
    have hxs : SymEqAt SM z x := hsym x ⟨by linarith, hxε⟩
    have hCx : CF z x = 0 := by rw [hx]; exact hC _
    have hdCx : ∀ α, pd (CF z) α x = 0 := by
      intro α
      induction α using Fin.cases with
      | zero => rw [hx]; exact hdC _
      | succ j => exact zero_on_slice_pd (contDiff_CF z) hC hzero.symm j
    obtain ⟨hD, hH, hE⟩ := matter_of_symEqAt SM z hxs
    have hEin := einstein_of_symEqAt SM z hxs hCx hdCx
    have hA : (bosF SM z x).2.1 = 0 := by
      refine eq_zero_of_frame_components z x _ fun A => ?_
      induction A using Fin.cases with
      | zero => rw [hx]; exact hG _
      | succ a => exact hE a
    exact ⟨Prod.ext hEin (Prod.ext hA hH), hD, hCx⟩

end Physical

/-! ### The Kato solution of constrained data -/

section Kato

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- **A smooth actual-jet solution with datum `U₀`**: a smooth field tuple whose actual-jet state
solves the independent symmetric system on `(-ε, ε) × 𝕋³`, stays in the chart margin `K`, and has
the datum `U₀` at `t = 0` (the auxiliary variables of the solution are the actual jets of its head
fields). -/
def SmoothStateSolution (SM : SMData (MatLie m) V S S')
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (K : Set (Fin (dimS m V S S') → ℝ))
    (U₀ : Fin (dimS m V S S') → ST 3 → ℝ) (ε : ℝ) (z : Tuple m V S S') : Prop :=
  0 < ε ∧ (∀ x ∈ openSlab (-ε) ε, SymEqAt SM z x) ∧ (∀ x ∈ openSlab (-ε) ε, κ (stateF SM z x) ∈ K) ∧
    ∀ b y, stU κ SM z b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)

/-- **`lem:generated-physical-identification` for the actual-jet system** (`Σ = 𝕋³`).  For theory
data with smooth sources satisfying the current and stress Noether identities, and forms with the
Clifford unitarity relations, there are Euclidean coordinates `κ` of the state space such that for
every compact chart margin `K` the realized symmetric coefficient maps `A^j, F` (the actual-jet
operators on `K`) satisfy: for every `H^q` radius `R₀` there is a Kato time `T > 0` such that
every constrained smooth periodic datum `U₀` with `‖U₀‖_{H^q} ≤ R₀` has a two-sided Kato solution
`U` on `(-T, T) × 𝕋³` ("the independent symmetric system has a common local Sobolev solution"),
and whenever a smooth actual-jet solution `z` with datum `U₀` exists on some `(-ε, ε)`
(`SmoothStateSolution`), then for `t₁ = min(T, ε)/2`, on `[0, t₁] × 𝕋³` the Kato solution is the
actual-jet state of `z` and `z` satisfies the complete Einstein–Standard-Model equations and the
harmonic and temporal-gauge constraints ("on a possibly smaller interval its head fields satisfy
the complete torsion-free Einstein–Standard-Model equations and the harmonic/temporal-gauge
constraints").  No physical property of `z` is assumed: constraint propagation is proved
(`physical_of_smooth_state`). -/
theorem generated_physical_identification_of_smoothState (hS : SMSmooth SM)
    (hU : UnitaryForms SM bG bV bS bS') (hN : CurrentNoether SM) (hT : StressNoether SM)
    {mm r : ℕ} (hm : (3 : ℝ) / 2 < mm) (hq : 2 * mm ≤ r + 1) (hq2 : mm + 2 ≤ r + 1) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
          energyQ (r + 1) U₀ 0 ≤ R₀ ^ 2 →
          ∃ (U : Fin (dimS m V S S') → ST 3 → ℝ) (P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ),
            KatoGalerkin.TwoSidedSol A F U₀ T U P ∧
            ∀ (z : Tuple m V S S') (ε : ℝ), SmoothStateSolution SM κ K U₀ ε z →
              ∀ x ∈ slab 0 (min T ε / 2), (∀ b, U b x = κ (stateF SM z x) b) ∧
                bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 := by
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K hK hKc => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT0, hkato⟩ := KatoGalerkin.kato_two_sided (d := 3) hm hq hq2 hA hsym hF hR₀
  refine ⟨T, hT0, fun U₀ hCD hU₀ hUp hE => ?_⟩
  obtain ⟨U, P, hUP⟩ := hkato U₀ hU₀ hUp hE
  refine ⟨U, P, hUP, fun z ε hz x hx => ?_⟩
  obtain ⟨hε, hsymz, hKz, hdat⟩ := hz
  obtain ⟨z₀, hdat₀, hC₀⟩ := hCD
  have hmin : 0 < min T ε := lt_min hT0 hε
  have ht₁ : 0 < min T ε / 2 := by positivity
  -- the Kato solution is the actual-jet state of `z`
  have hU : ∀ b, U b x = κ (stateF SM z x) b := by
    have hTS := twoSided_of_symEq hAK hFK z hsymz hKz
    have hTS' := twoSided_congr_data hTS fun b y => hdat b y
    exact KatoStab.twoSided_unique hA hsym hF hUP hTS' ht₁
      (by linarith [min_le_left T ε]) (by linarith [min_le_right T ε]) x hx
  -- the states of `z` and `z₀` agree on the initial slice
  have hS0 : ∀ y : Fin 3 → ℝ, stateF SM z (Fin.cons 0 y) = stateF SM z₀ (Fin.cons 0 y) := by
    intro y
    apply κ.injective
    funext b
    show stU κ SM z b (Fin.cons 0 y) = stU κ SM z₀ b (Fin.cons 0 y)
    rw [hdat b y, hdat₀ b y]
  have hphys := physical_of_smooth_state hN hT hS hε hsymz hS0 hC₀ x hx.1
    (by have := hx.2; linarith [min_le_right T ε])
  exact ⟨hU, hphys⟩

end Kato

/-! ### Non-vacuity: the flat vacuum -/

section NonVacuity

open CoupledBootstrap.FlatVacuum

theorem flat_sliceConstrained : SliceConstrained trivSMM flat := fun y => by
  refine ⟨flat_bosF _, Subsingleton.elim _ _, flat_CF _, ?_⟩
  have : CF flat = fun _ => 0 := funext fun x => flat_CF x
  rw [this]
  simp [SobolevOpen.pd]

/-- **Non-vacuity**: the flat-vacuum datum is constrained and the flat vacuum is a smooth
actual-jet solution with this datum on every slab, so the conclusion of
`generated_physical_identification_of_smoothState` is produced for it (for the vanishing-coupling
data `trivSMM`, which satisfy the current and stress Noether identities). -/
example : ∃ (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ))
    (A : Fin 3 → Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
        (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ)
    (F : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ) (T : ℝ)
    (U : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ST 3 → ℝ)
    (P : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → Fin 3 → ST 3 → ℝ),
    0 < T ∧ KatoGalerkin.TwoSidedSol A F (stU κ trivSMM flat) T U P ∧
      ∀ x ∈ slab 0 (min T 1 / 2), (∀ b, U b x = κ (stateF trivSMM flat x) b) ∧
        bosF trivSMM flat x = 0 ∧ dirF trivSMM flat x = 0 ∧ CF flat x = 0 := by
  obtain ⟨κ, -, h⟩ := generated_physical_identification_of_smoothState trivSMM_smooth
    unitaryForms_triv (currentNoether_of_variational trivSMM_variational) trivSMM_stressNoether
    (mm := 2) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨A, F, -, -, -, -, -, h2⟩ := h {κ minkState} isCompact_singleton (by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    rw [LinearEquiv.symm_apply_apply]
    exact metChart_mink)
  obtain ⟨T, hT, h3⟩ := h2 (Real.sqrt |energyQ (3 + 1) (stU κ trivSMM flat) 0|)
    (Real.sqrt_nonneg _)
  obtain ⟨U, P, hsol, hid⟩ := h3 (stU κ trivSMM flat) ⟨flat, fun _ _ => rfl, flat_sliceConstrained⟩
    (contDiff_stU κ trivSMM flat) (isSPeriodic_stU κ trivSMM flat)
    (by rw [Real.sq_sqrt (abs_nonneg _)]; exact le_abs_self _)
  refine ⟨κ, A, F, T, U, P, hT, hsol, hid flat 1 ⟨one_pos, fun x _ =>
    symEqAt_of_physical trivSMM flat isOpen_univ flat_isPhysicalOn trivial, fun x _ => by
      rw [stateF_flat]; exact Set.mem_singleton _, fun _ _ => rfl⟩⟩

end NonVacuity

end RenewalGeometry.GenPhysIdClosed
