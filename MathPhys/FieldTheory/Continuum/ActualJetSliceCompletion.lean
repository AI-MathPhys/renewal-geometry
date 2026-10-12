/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.ActualJetSliceJets
import MathPhys.FieldTheory.Continuum.ActualJetKatoModified
import MathPhys.FieldTheory.Continuum.RicciJetSymmetry

/-!
# Constraint rows on Cauchy slice data and the completion to slice-constrained tuples

Einstein–Standard-Model action-closure manuscript, `prop:generated-initial`,
`eq:exact-physical-initial-manifold`, `lem:generated-physical-identification` (the constrained
class `GenPhysIdClosed.ConstrainedData`).

## The constraint rows on slice data (task: ADM form of the actual-jet constraint rows)

For smooth periodic slice data `D : SliceCauchy` in the unit-lapse zero-shift temporal gauge, with
the harmonic-gauge completion of the lapse and shift time derivatives
(`∂_tg₀₀ = 2 tr_γK`, `∂_tg₀ₗ = γ^{jk}(∂_jγ_{kl} - ½∂_lγ_{jk})`):

* `hamRow`: the **Hamiltonian constraint** `½(R(γ) + (tr_γK)² - |K|²_γ) - Λ - κT₀₀`;
* `momRow`: the **momentum constraint** `-(∇^jK_{ji} - ∂ᵢtr_γK) - κT₀ᵢ`;
* `gaussRow`: the **Gauss constraint** — the normal row `r^A_0` of the Yang–Mills residual;

where `T` is the complete Einstein–Standard-Model stress (`stressF`) of the first jets of the slice
data, the normal spinor derivatives eliminated through the Dirac equation (`ActualJet.firstJet`).
`Constrained D` is the vanishing of the three rows on the slice.

* `einsteinConstraint_mk`: for every completion of `D` whose Dirac residual vanishes on the slice,
  the Einstein normal rows `(G + Λg - κT)(e₀, ·)` of `GenHarmonic.einsteinConstraint` **are**
  `hamRow`, `momRow` (Gauss–Codazzi, `e₀ = ∂_t`); they do not depend on the second-order
  completion data.

## The Cauchy-data completion (task: slice completion)

* `slice_close`: pointwise constraint closure on the slice — if the harmonic defect `C` vanishes
  on the slice, the reduced Einstein row `𝓔^{tr} = ∇_{(μ}C_{ν)}` holds at a slice point and the
  Einstein normal rows vanish there, then `∂_tC = 0` and the full Einstein residual vanishes there
  (the algebra `GenHarmonic.normal_defect_alg`).
* **`exists_sliceConstrained`**: for theory data with smooth bosonic residual fields and a
  symmetric stress, every `Constrained` slice datum is the slice datum of a smooth field tuple `z`
  (`GenPhysIdClosed.SliceConstrained`): all Einstein, Yang–Mills, Higgs and Dirac residuals,
  `C` and `∂_tC` vanish on the slice.  The second-order data are solved in three stages (normal
  spinor derivatives from the Dirac rows, `∂_t²Aᵢ` and `∂_t²H` from the spatial Yang–Mills and
  the Higgs rows, `∂_t²g` from the reduced Einstein rows), and the Einstein and Gauss constraints
  close the remaining normal rows.
* `constrainedData_of_constrained`: the actual-jet state of the completion is a
  `GenPhysIdClosed.ConstrainedData` datum.
-/

open Finset
open scoped ContDiff

noncomputable section

namespace MathPhys.GenSlice

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState ActualJetGauge
  ActualJetSpinor SpinorProlongation SliceExt GenHarmonic GenStress GenConstraint GenPhysIdClosed
  ActualJetRecon

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-! ### More jet congruences -/

section Agree2

variable {J J' : ActualJet (MatLie m) V S S'}

/-- The Dirac operator of a jet, as a function of an arbitrary spinor 1-jet, depends only on the
first-order data. -/
theorem Agree.rDf (h : Agree J J') {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (D : DiracData (MatLie m) V S₀) (ψ : S₀) (c : Fin 4 → S₀) : J.rD D ψ c = J'.rD D ψ c := by
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ0, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ0', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, -, -, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH
  subst hA hdA hH hdH
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde sg sg'
  subst hg hgi hdg he hde sg sg'
  rfl

/-- The stress of two jets agreeing to first order with the same spinor 1-jets. -/
theorem Agree.Tact_eq (h : Agree J J') (hc : J.cψ = J'.cψ) (hcb : J.cψb = J'.cψb)
    (SM : SMData (MatLie m) V S S') : J.Tact SM = J'.Tact SM := by
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ0, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ0', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, hψ, hψb, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH hψ hψb hc hcb
  subst hA hdA hH hdH hψ hψb hc hcb
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde sg sg'
  subst hg hgi hdg he hde sg sg'
  rfl

/-- **Shift of the Yang–Mills row** between two jets agreeing to first order. -/
theorem Agree.rA_shift (h : Agree J J') (δ : Fin 4 → Fin 4 → Fin 4 → MatLie m)
    (hdd : J'.ddA = fun a b c => J.ddA a b c + δ a b c) (SM : SMData (MatLie m) V S S')
    (ν : Fin 4) :
    (J'.res SM).rA ν = (J.res SM).rA ν + ∑ μ, ∑ ρ, J.FJ.gi μ ρ • (δ ρ μ ν - δ ρ ν μ) := by
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ0, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ0', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, hψ, hψb, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH hψ hψb hdd
  subst hA hdA hH hdH hψ hψb hdd
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde
  subst hg hgi hdg he hde
  exact ymRes_shift _ _ _ δ _ _ _ ν

/-- **Shift of the Higgs row** between two jets agreeing to first order. -/
theorem Agree.rH_shift (h : Agree J J') (δ : Fin 4 → Fin 4 → V)
    (hdd : J'.ddH = fun a b => J.ddH a b + δ a b) (SM : SMData (MatLie m) V S S') :
    (J'.res SM).rH = (J.res SM).rH + ∑ μ, ∑ ρ, J.FJ.gi μ ρ • δ ρ μ := by
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ0, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ0', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, hψ, hψb, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH hψ hψb hdd
  subst hA hdA hH hdH hψ hψb hdd
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde
  subst hg hgi hdg he hde
  exact higgsRes_shift _ _ _ _ _ δ _ _ _

end Agree2

/-! ### Stress symmetry -/

variable (SM : SMData (MatLie m) V S S')

/-- **Symmetric stress**: the complete off-shell stress of first jets with symmetric metric and
inverse metric is symmetric (true for the back-reacting Dirac data `GenDStress.CoupledDirac`,
`stressSymm_of_coupledDirac`). -/
def StressSymm : Prop :=
  ∀ fj : FirstJet (MatLie m) V S S', (∀ a b, fj.g a b = fj.g b a) →
    (∀ a b, fj.gi a b = fj.gi b a) → ∀ μ ν, stressF SM fj μ ν = stressF SM fj ν μ

/-- The residual part of the stress vanishes with the Dirac residuals. -/
theorem stressR_zero (fj : FirstJet (MatLie m) V S S') (r : Res (MatLie m) V S S')
    (hr : r.rD = 0) (hrb : r.rDb = 0) (μ ν : Fin 4) : stressR SM fj r μ ν = 0 := by
  simp [stressR, DiracStressForm.stressRes, hr, hrb]

/-- Where the Dirac residuals vanish, the actual stress is the first-jet stress. -/
theorem Tact_eq_stressF (J : ActualJet (MatLie m) V S S') (hr : (J.res SM).rD = 0)
    (hrb : (J.res SM).rDb = 0) (μ ν : Fin 4) :
    J.Tact SM μ ν = stressF SM (J.firstJet SM) μ ν := by
  rw [J.Tact_eq SM μ ν, stressR_zero SM _ _ hr hrb, sub_zero, J.recon_state SM]

/-! ### The adapted normal on the slice -/

theorem frU_met4_zero (C : Fin 3 → Fin 3 → ℝ) (μ : Fin 4) :
    frU (met4 (-1) 0 C) 0 μ = if μ = 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun j => ?_) μ
  · simp [frU, lapse]
  · simp [frU, shift, lapse, Fin.succ_ne_zero]

namespace SliceCauchy

variable {SM}
variable (D : SliceCauchy m V S S')

theorem e_mk {P : Params m V S S'} {ε : ℝ} {hch : ∀ x, GChart (D.gF P ε x)} (y : Fin 3 → ℝ)
    (μ : Fin 4) : (D.mkTuple P ε hch).e (Fin.cons 0 y) 0 μ = if μ = 0 then 1 else 0 := by
  show frU ((D.mkTuple P ε hch).gi (Fin.cons 0 y)) 0 μ = _
  rw [D.mk_gi]; exact frU_met4_zero _ μ

/-! ### The base completion and the constraint rows -/

theorem exists_eps0 : ∃ ε, 0 < ε ∧ ∀ x, GChart (D.gF Params.zero ε x) := by
  obtain ⟨ε₀, h0, h⟩ := D.exists_chart_eps (Params.zero (m := m) (V := V) (S := S) (S' := S'))
  exact ⟨ε₀, h0, h ε₀ h0 le_rfl⟩

/-- The time scale of the base completion. -/
abbrev ε0 : ℝ := D.exists_eps0.choose

theorem ε0_ne : D.ε0 ≠ 0 := D.exists_eps0.choose_spec.1.ne'

/-- **The base completion** of the slice datum (zero second-order data); only its first jets on
the slice enter the constraint rows. -/
abbrev base : Tuple m V S S' := D.mkTuple Params.zero D.ε0 D.exists_eps0.choose_spec.2

variable (SM)

/-- The stress `T_{μν}` of the slice data (first jets, normal spinor derivatives eliminated by
the Dirac equation). -/
def Tsl (y : Fin 3 → ℝ) (μ ν : Fin 4) : ℝ :=
  stressF SM (((D.base).jet (Fin.cons 0 y)).firstJet SM) μ ν

/-- **The Hamiltonian constraint row** `½(R(γ) + (tr_γK)² - |K|²_γ) - Λ - κT₀₀`. -/
def hamRow (y : Fin 3 → ℝ) : ℝ := (1 / 2) * (D.sd 0 y).hamC - SM.Λ - SM.κ * D.Tsl SM y 0 0

/-- **The momentum constraint rows** `-(∇^jK_{ji} - ∂ᵢtr_γK) - κT₀ᵢ`. -/
def momRow (y : Fin 3 → ℝ) (i : Fin 3) : ℝ := -(D.sd 0 y).momC i - SM.κ * D.Tsl SM y 0 i.succ

/-- **The Gauss constraint row**: the normal row `r^A_0` of the Yang–Mills residual of the slice
data (`e₀ = ∂_t`; it does not involve `∂_t²A`, `Agree.rA_shift`). -/
def gaussRow (y : Fin 3 → ℝ) : MatLie m := (((D.base).jet (Fin.cons 0 y)).res SM).rA 0

/-- **The slice datum satisfies the complete initial constraints** (Hamiltonian, momentum and
Gauss rows) on the slice. -/
def Constrained : Prop :=
  ∀ y, D.hamRow SM y = 0 ∧ (∀ i, D.momRow SM y i = 0) ∧ D.gaussRow SM y = 0

/-- **The Einstein normal rows of a completion are the ADM constraint rows** (where the Dirac
residuals vanish on the slice). -/
theorem einsteinConstraint_mk {P : Params m V S S'} {ε : ℝ} {hch : ∀ x, GChart (D.gF P ε x)}
    (hε : ε ≠ 0) (y : Fin 3 → ℝ)
    (hD : ((D.mkTuple P ε hch).jet (Fin.cons 0 y) |>.res SM).rD = 0)
    (hDb : ((D.mkTuple P ε hch).jet (Fin.cons 0 y) |>.res SM).rDb = 0) :
    einsteinConstraint SM (D.mkTuple P ε hch) (Fin.cons 0 y) 0 = D.hamRow SM y ∧
      ∀ i, einsteinConstraint SM (D.mkTuple P ε hch) (Fin.cons 0 y) i.succ = D.momRow SM y i := by
  set z := D.mkTuple P ε hch
  set x : ST 3 := Fin.cons 0 y
  have hE : ∀ ν, einsteinConstraint SM z x ν =
      einstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) 0 ν + SM.Λ * z.g x 0 ν - SM.κ * Tf SM z x 0 ν := by
    intro ν
    have he0 : ∀ μ, z.e x 0 μ = if μ = 0 then 1 else 0 := D.e_mk y
    unfold einsteinConstraint
    rw [Fin.sum_univ_succ]
    simp only [he0, ite_true, one_mul, Fin.succ_ne_zero, ite_false, zero_mul,
      Finset.sum_const_zero, add_zero]
  have hein : ∀ ν, einstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) 0 ν =
      (D.sd (P.W y) y).jet.einM 0 ν := by
    intro ν
    rw [← ContractedBianchiJet.einM_ofArrays (arraysValid z x) 0 ν, D.ofArrays_mk hε y]
  have hT : ∀ ν, Tf SM z x 0 ν = D.Tsl SM y 0 ν := by
    intro ν
    show (z.jet x).Tact SM 0 ν = _
    rw [Tact_eq_stressF SM _ hD hDb, (D.agree_mk hε D.ε0_ne y).firstJet_eq SM]
    rfl
  have hv := D.sd_valid (P.W_symm y) y
  refine ⟨?_, fun i => ?_⟩
  · rw [hE, hein, ContractedBianchiJet.SliceData.einM_zero_zero hv, hT, D.mk_g]
    simp only [g0, met4_zero_zero, hamRow]
    have : (D.sd (P.W y) y).hamC = (D.sd 0 y).hamC := rfl
    rw [this]; ring
  · rw [hE, hein, ContractedBianchiJet.SliceData.einM_zero_succ hv, hT, D.mk_g]
    simp only [g0, met4_zero_succ, Pi.zero_apply, mul_zero, add_zero, momRow]
    have : (D.sd (P.W y) y).momC i = (D.sd 0 y).momC i := rfl
    rw [this]

end SliceCauchy

/-! ### Pointwise closure of the constraints on the slice -/

/-- **Pointwise constraint closure**: on a slice where the harmonic defect vanishes, the reduced
Einstein row `𝓔^{tr} = ∇_{(μ}C_{ν)}` and the Einstein normal rows at a point imply `∂_tC = 0`
and the vanishing of the complete Einstein residual at that point. -/
theorem slice_close (z : Tuple m V S S') (y : Fin 3 → ℝ)
    (hC0 : ∀ y' : Fin 3 → ℝ, CF z (Fin.cons 0 y') = 0)
    (hred : ∀ μ ν, (bosF SM z (Fin.cons 0 y)).1 μ ν =
      symDefect (z.g (Fin.cons 0 y)) (z.gi (Fin.cons 0 y)) (z.dg (Fin.cons 0 y))
        (z.ddg (Fin.cons 0 y)) μ ν)
    (hE0 : ∀ ν, einsteinConstraint SM z (Fin.cons 0 y) ν = 0) :
    pd (CF z) 0 (Fin.cons 0 y) = 0 ∧ (bosF SM z (Fin.cons 0 y)).1 = 0 := by
  obtain ⟨x, hxdef⟩ : ∃ x : ST 3, x = Fin.cons 0 y := ⟨_, rfl⟩
  rw [← hxdef] at hred hE0 ⊢
  have hC : CF z x = 0 := by rw [hxdef]; exact hC0 y
  have hsp : ∀ j : Fin 3, pd (CF z) j.succ x = 0 := fun j =>
    zero_on_slice_pd (contDiff_CF z) (fun y' => hC0 y') (by rw [hxdef]; rfl) j
  have hgi := fun a b => z.gi_symm x a b
  have hinv := z.hinv x
  have htr : ∀ μ ν, traceRev (z.g x) (z.gi x) (fun a b => reducedEinstein (z.g x) (z.gi x)
      (z.dg x) (z.ddg x) a b + SM.Λ * z.g x a b - SM.κ * Tf SM z x a b) μ ν = 0 := by
    intro μ ν
    rw [harmonic_residual_trace_reversal (z.g x) (z.gi x) (z.dg x) (z.ddg x) hgi hinv
      (by simp) (Tf SM z x) SM.Λ SM.κ μ ν, ← hred μ ν]
    show traceRev _ _ _ μ ν - ((z.jet x).res SM).Etr μ ν = 0
    rw [sub_eq_zero]
    rfl
  have hred' := fun μ ν => traceRev_inj (z.g x) (z.gi x) hgi hinv _ htr μ ν
  set v : Fin 4 → ℝ := fun ν => ∑ l, z.g x ν l * pd (CF z) 0 x l with hv
  have hw : ∀ μ ν, nablaDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν =
      if μ = 0 then v ν else 0 := by
    intro μ ν
    rw [nablaDefect_of_CF z hC]
    induction μ using Fin.cases with
    | zero => rfl
    | succ j => simp [hsp j, Fin.succ_ne_zero]
  have hH : ∀ ν, ∑ μ, z.e x 0 μ * defectTensor (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν = 0 := by
    intro ν
    have h1 := hE0 ν
    unfold einsteinConstraint at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have := hred' μ ν
    rw [reducedEinstein_eq] at this
    congr 1
    linarith
  have hv0 : v = 0 := by
    refine normal_defect_alg (z.g x) (z.gi x) (z.e x 0) v ?_ ?_ ?_ fun ν => ?_
    · rw [GenGauss.e_eq_frameU, AdaptedFrame.fr_zero_zero]
      exact inv_pos.2 (frameU (z.gi x)).N_pos
    · intro β
      rw [z.compl x 0 β, Fin.sum_univ_succ]
      have : ∀ c : Fin 3, z.e x c.succ 0 = 0 := fun c => by
        rw [GenGauss.e_eq_frameU]; exact AdaptedFrame.fr_succ_zero _ c
      simp [lorentzSign, Fin.succ_ne_zero, this]
    · simpa [ipg, lorentzSign] using z.orth_at x 0 0
    · have := hH ν
      simpa only [defectTensor, symDefect, divDefect, trG, hw] using this
  have hdc : pd (CF z) 0 x = 0 := by
    funext l
    have hdc' : pd (CF z) 0 x l = ∑ ν, z.gi x l ν * v ν := by
      rw [hv]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ k, ∑ ν, z.gi x l ν * (z.g x ν k * pd (CF z) 0 x k) =
          (∑ ν, z.g x k ν * z.gi x ν l) * pd (CF z) 0 x k := fun k => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ν _ => by rw [z.g_symm x ν k, z.gi_symm x l ν]; ring
      simp only [this, z.hinv x, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    rw [hdc', hv0]
    simp
  refine ⟨hdc, ?_⟩
  have hnab : ∀ μ ν, nablaDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν = 0 := by
    intro μ ν
    rw [hw μ ν, hv0]
    simp
  funext μ ν
  rw [hred μ ν]
  simp [symDefect, hnab]

end MathPhys.GenSlice
