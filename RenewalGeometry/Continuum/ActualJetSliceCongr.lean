/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ActualJetConstraintSlice

/-!
# Dependence of the actual-jet residuals on the second-order jets

Generic jet algebra for the Cauchy-data completion of `prop:generated-initial`
(Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`).  Two actual jets
that agree to first order (`Agree`: metric 1-jet, adapted frame 1-jet, gauge potential and Higgs
1-jets, spinor values and tangential spinor derivatives) have

* the same first jets, actual-jet state and stress (`firstJet_eq`, `state_eq`, `Tact_eq'`);
* the same Yang–Mills and Higgs residuals when their `∂²A`, resp. `∂²H` agree (`rA_eq`,
  `rH_eq`), and Dirac residuals when their normal spinor derivatives agree (`rD_eq`, `rDb_eq`);

and the residuals change **affinely** with the free second-order data:

* `rD_shift`: `∂_tΨ ↦ ∂_tΨ + d` changes `r_D` by `Σ_b ε_b c_b(e_b{}^0 d)`;
* `rA_shift`: `∂_t²A ↦ ∂_t²A + Ä` changes `r^A_ν` by `g^{00}Ä_ν - δ_{ν0} g^{μ0}Ä_μ`;
* `rH_shift`: `∂_t²H ↦ ∂_t²H + Ḧ` changes `r_H` by `g^{00}Ḧ`;
* `Etr_shift`: `∂_t²g ↦ ∂_t²g + W` changes `𝓔^{tr} - ∇_{(μ}C_{ν)}` by `-½ g^{00}W`
  (the reduced Einstein operator `eq:off-harmonic-metric-wave` is principal in `∂_t²g` with
  coefficient `-½g^{00}`).
-/

open Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenSlice

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState ActualJetGauge
  ActualJetSpinor SpinorProlongation

set_option linter.unusedSectionVars false

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **First-order agreement** of two actual jets: metric and frame 1-jets, gauge and Higgs
1-jets, spinor values and tangential spinor derivatives. -/
structure Agree (J J' : ActualJet (MatLie m) V S S') : Prop where
  g : J.FJ.g = J'.FJ.g
  gi : J.FJ.gi = J'.FJ.gi
  dg : J.FJ.dg = J'.FJ.dg
  e : J.FJ.e = J'.FJ.e
  de : J.FJ.de = J'.FJ.de
  A : J.A = J'.A
  dA : J.dA = J'.dA
  H : J.H = J'.H
  dH : J.dH = J'.dH
  ψ : J.ψ = J'.ψ
  ψb : J.ψb = J'.ψb
  cψ : ∀ j : Fin 3, J.cψ j.succ = J'.cψ j.succ
  cψb : ∀ j : Fin 3, J.cψb j.succ = J'.cψb j.succ

/-- The tangential spinor jets do not involve the normal spinor derivative. -/
theorem Xs_succ_congr {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (J : ActualJet (MatLie m) V S S') (D : DiracData (MatLie m) V S₀) (ψ : S₀)
    {cψ cψ' : Fin 4 → S₀} (h : ∀ j : Fin 3, cψ j.succ = cψ' j.succ) (a : Fin 3) :
    J.Xs D ψ cψ a.succ = J.Xs D ψ cψ' a.succ := by
  unfold ActualJet.Xs cov dψf
  congr 1
  have he : J.FJ.e a.succ 0 = 0 := by rw [J.frame a.succ 0]; rfl
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun γ => J.FJ.e a.succ γ • cψ' γ), he]
  simp only [zero_smul, zero_add, h]

theorem Xn_congr {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (J : ActualJet (MatLie m) V S S') (D : DiracData (MatLie m) V S₀) (ψ : S₀)
    {cψ cψ' : Fin 4 → S₀} (h : ∀ j : Fin 3, cψ j.succ = cψ' j.succ) :
    J.Xn D ψ cψ = J.Xn D ψ cψ' := by
  funext A
  refine Fin.cases ?_ (fun a => ?_) A
  · simp only [ActualJet.Xn, Fin.cases_zero]
    congr 1
    · congr 1; congr 1; funext i; exact Xs_succ_congr J D ψ h i
  · simp only [ActualJet.Xn, Fin.cases_succ]
    exact Xs_succ_congr J D ψ h a

section Agree

variable {J J' : ActualJet (MatLie m) V S S'}

/-- Reduction of a statement about two agreeing jets to jets with identical first-order
fields (the spinor derivatives are kept). -/
theorem Agree.firstJet_eq (h : Agree J J') (SM : SMData (MatLie m) V S S') :
    J.firstJet SM = J'.firstJet SM := by
  have hX := Xn_congr J SM.D J.ψ h.cψ
  have hXb := Xn_congr J SM.Db J.ψb h.cψb
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, hψ, hψb, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH hψ hψb hX hXb
  subst hA hdA hH hdH hψ hψb
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde sg sg'
  subst hg hgi hdg he hde sg sg'
  simp only [ActualJet.firstJet] at hX hXb ⊢
  rw [hX, hXb]
  rfl

theorem Agree.state_eq (h : Agree J J') (SM : SMData (MatLie m) V S S') :
    J.state SM = J'.state SM := by
  have hX : ∀ a : Fin 3, J.Xs SM.D J.ψ J.cψ a.succ = J.Xs SM.D J.ψ J'.cψ a.succ :=
    fun a => Xs_succ_congr J SM.D J.ψ h.cψ a
  have hXb : ∀ a : Fin 3, J.Xs SM.Db J.ψb J.cψb a.succ = J.Xs SM.Db J.ψb J'.cψb a.succ :=
    fun a => Xs_succ_congr J SM.Db J.ψb h.cψb a
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, hψ, hψb, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH hψ hψb hX hXb
  subst hA hdA hH hdH hψ hψb
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde sg sg'
  subst hg hgi hdg he hde sg sg'
  simp only [ActualJet.state]
  simp only [hX, hXb]
  rfl

/-- The Yang–Mills residual depends on the first-order data and `∂²A` only. -/
theorem Agree.rA_eq (h : Agree J J') (hdd : J.ddA = J'.ddA) (SM : SMData (MatLie m) V S S') :
    (J.res SM).rA = (J'.res SM).rA := by
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, hψ, hψb, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH hψ hψb hdd
  subst hA hdA hH hdH hψ hψb hdd
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde
  subst hg hgi hdg he hde
  rfl

/-- The Higgs residual depends on the first-order data and `∂²H` only. -/
theorem Agree.rH_eq (h : Agree J J') (hdd : J.ddH = J'.ddH) (SM : SMData (MatLie m) V S S') :
    (J.res SM).rH = (J'.res SM).rH := by
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, hψ, hψb, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH hψ hψb hdd
  subst hA hdA hH hdH hψ hψb hdd
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde
  subst hg hgi hdg he hde
  rfl

/-- The Dirac residuals depend on the first-order data and the normal spinor derivative. -/
theorem Agree.rD_eq (h : Agree J J') (h0 : J.cψ 0 = J'.cψ 0) (SM : SMData (MatLie m) V S S') :
    (J.res SM).rD = (J'.res SM).rD := by
  have hc : J.cψ = J'.cψ := by
    funext γ; refine Fin.cases h0 (fun j => h.cψ j) γ
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, hψ, hψb, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH hψ hψb hc
  subst hA hdA hH hdH hψ hψb hc
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde sg sg'
  subst hg hgi hdg he hde sg sg'
  rfl

theorem Agree.rDb_eq (h : Agree J J') (h0 : J.cψb 0 = J'.cψb 0)
    (SM : SMData (MatLie m) V S S') : (J.res SM).rDb = (J'.res SM).rDb := by
  have hc : J.cψb = J'.cψb := by
    funext γ; refine Fin.cases h0 (fun j => h.cψb j) γ
  obtain ⟨FJ, ch, sg, fr, dfr, A, dA, ddA, tm, dtm, dds, H, dH, ddH, ddHs, ψ, cψ, ccψ, ccψs,
    ψb, cψb, ccψb, ccψbs⟩ := J
  obtain ⟨FJ', ch', sg', fr', dfr', A', dA', ddA', tm', dtm', dds', H', dH', ddH', ddHs', ψ', cψ',
    ccψ', ccψs', ψb', cψb', ccψb', ccψbs'⟩ := J'
  obtain ⟨hg, hgi, hdg, he, hde, hA, hdA, hH, hdH, hψ, hψb, -, -⟩ := h
  simp only at hg hgi hdg he hde hA hdA hH hdH hψ hψb hc
  subst hA hdA hH hdH hψ hψb hc
  obtain ⟨g, gi, dg, ddg, ε, e, de, dde, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := FJ
  obtain ⟨g', gi', dg', ddg', ε', e', de', dde', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12⟩ := FJ'
  simp only at hg hgi hdg he hde sg sg'
  subst hg hgi hdg he hde sg sg'
  rfl

end Agree

end RenewalGeometry.GenSlice
