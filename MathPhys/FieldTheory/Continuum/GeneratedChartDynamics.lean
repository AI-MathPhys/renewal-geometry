/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.GeneratedChartIdentification
import MathPhys.FieldTheory.Continuum.GeneratedCoupledDynamicsStat
import MathPhys.FieldTheory.Continuum.GeneratedCoupledDynamics
import MathPhys.FieldTheory.Continuum.GeneratedCoupledStationarity

/-!
# `thm:generated-dynamics` and `cor:generated-nonempty` under chart-local smoothness

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`,
`cor:generated-nonempty`, for back-reacting Dirac data (`GenDStress.CoupledDirac`) whose sources
are smooth only near Lorentzian charts (`GenChL.SMSmoothL`; gauge-charged spinors,
`GenChNoGo.not_smSmooth_of_charged`).  The coupled assembly, the record cells and stationarity of
the complete composite action, and the three top theorems re-proved under `SMSmoothL`
(suffix `L`): `generated_dynamics_cpl_statL`, `generated_dynamics_norms_cpl_statL`,
`generated_nonempty_norms_cpl_statL`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! #### `generated_dynamics_ext_cpl` (from `Continuum/GeneratedCoupledDynamics.lean`) -/
namespace MathPhys.GenCplDyn.ChL
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal GenReadout GenNorms
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}
variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
set_option maxHeartbeats 8000000 in
/-- **`thm:generated-dynamics` with back-reacting spinors (readout package)**: the statement of
`GenNorms.generated_dynamics_ext` for theory data with smooth sources, Clifford-unitary forms and
**back-reacting Dirac data** (`GenDStress.CoupledDirac`: symmetric Hilbert Dirac stress in the
Einstein equation, Dirac current in Yang–Mills, Yukawa source in the Higgs equation) instead of
variational data with vanishing Dirac stress, **without** the stationarity clause
(`eq:generated-stationarity`), whose composite action `GenStat.Scmp` is the bosonic first-order
action `S^{(1)}` and has no Dirac term.  The physical identification is
`MathPhys.GenCplId.ChL.core_identification_cplL` with the Noether identities discharged
(`GenDiracCur.currentNoether_of_variationalDirac`, `GenDSN.stressConservation_of_coupledDirac`),
and the realized modified system is `MathPhys.GenCplKato.ChL.modified_kato_realization_cplL`. -/
theorem generated_dynamics_ext_cplL (hS : GenChL.SMSmoothL SM) (hU : UnitaryForms SM bG bV bS bS')
    (hC : GenDStress.CoupledDirac SM) {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K₀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∀ δK : ℝ, 0 < δK → Metric.cthickening δK K₀ ⊆ K →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0, ∃ τstar > 0,
        ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → energyQ (s + p + 8) U₀ 0 ≤ R₀ ^ 2 →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ t₁ ≤ T ∧
            (∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0) ∧
            (∀ b y, stC κ SM z b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
            ∀ {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) {nD : ℕ}
              (eD : S × S' →L[ℝ] (Fin nD → ℝ)),
            ∃ C ≥ 0, ∃ Cz ≥ 0, ∃ η > 0,
              ∃ K2 : Set (J2I 3 × Fin (dimS m V S S') → ℝ),
              IsCompact K2 ∧
              (∀ w ∈ K2, headJ (m := m) (V := V) (S := S) (S' := S') κ w ∈ chartJ2 m V S S') ∧
              ∀ (N : ℕ) (τ : ℝ), 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar →
              τ ≤ τstar → ∀ (a₀ : GS 3 (dimS m V S S') N) (δ : ℝ), ‖a₀‖ ≤ R₀ → 0 ≤ δ →
              (∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 4) k *
                (cf (s + p + 8) a₀ b k - coef (U₀ b) 0 k) ^ 2 ≤ δ ^ 2) →
              τ + δ + 1 / ((N : ℝ) + 1) ^ p ≤ η →
              ∃ Ud : ℕ → GS 3 (dimS m V S S') N, Ud 0 = a₀ ∧
                (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
                  Ud (j + 1) = Ud j + τ • GN A F (s + p + 8)
                    (SpectralGalerkin.mid (Ud j) (Ud (j + 1))))) ∧
                (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ → ∀ θ ∈ Icc (0 : ℝ) 1,
                  ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 2) k *
                    (cf (s + p + 8) (SpectralGalerkin.hermite τ (Ud j) (Ud (j + 1))
                      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                      coef (stC κ SM z b) (j * τ + θ * τ) k) ^ 2 ≤
                    (Cz * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
                (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ → ∀ θ ∈ Icc (0 : ℝ) 1,
                  ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 2) k *
                    (cf (s + p + 8) (SpectralGalerkin.hermiteD τ (Ud j) (Ud (j + 1))
                      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                      coef (pd (stC κ SM z b) 0) (j * τ + θ * τ) k) ^ 2 ≤
                    (Cz * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
                (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ →
                  (∀ y : ST 3, y 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
                    (fun w => j2c (recW τ (j * τ) (Ud j) (Ud (j + 1)) (GN A F (s + p + 8) (Ud j))
                      (GN A F (s + p + 8) (Ud (j + 1))) (s + p + 8)) w y) ∈ K2) ∧
                  (∀ y ∈ openSlab (j * τ) ((j + 1) * τ), HeadChart κ (fun c =>
                    recW τ (j * τ) (Ud j) (Ud (j + 1)) (GN A F (s + p + 8) (Ud j))
                      (GN A F (s + p + 8) (Ud (j + 1))) (s + p + 8) c y)) ∧
                  ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
                    ∑ c : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q s (fun x =>
                      riemR (hjF κ (recW τ (j * τ) (Ud j) (Ud (j + 1))
                        (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1)))
                        (s + p + 8)) x) c - riemR (hj2 z x) c) t ≤
                      (C * (τ + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2 ∧
                    ∑ k, Q s (fun x => eB (bosR SM (hjF κ (recW τ (j * τ) (Ud j) (Ud (j + 1))
                      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1)))
                      (s + p + 8)) x)) k) t ≤ (C * (τ + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2 ∧
                    ∑ k, Q (s + 1) (fun x => eD (GenResMaps.dirR SM (hjF κ (recW τ (j * τ)
                      (Ud j) (Ud (j + 1)) (GN A F (s + p + 8) (Ud j))
                      (GN A F (s + p + 8) (Ud (j + 1))) (s + p + 8)) x)) k) t ≤
                      (C * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) := by
  have hN := GenDiracCur.currentNoether_of_variationalDirac hC.toVariationalDirac
  have hT := GenDSN.stressConservation_of_coupledDirac hC
  obtain ⟨κ, hκ, hreal⟩ := MathPhys.ActualJetKato.ChL.actual_jet_kato_realizationL hS hU
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  obtain ⟨AM, FM, hAM, hsymM, hFM, hAMK, hFMK, hτA, hτF⟩ :=
    MathPhys.GenCplKato.ChL.modified_kato_realization_cplL hS hU hC κ hκ K hK hKc
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  have hm2 : ((3 : ℕ) : ℝ) / 2 < (2 : ℕ) := by norm_num
  obtain ⟨TK, hTK0, hkato⟩ := KatoGalerkin.kato_two_sided (d := 3) (m := 2) (q := s + p + 8)
    hm2 (by omega) (by omega) hA hsym hF hR₀
  obtain ⟨TM, hTM0, hkatoM⟩ := KatoSmooth.kato_two_sided_smooth (m := 2) (q := s + p + 8)
    hm2 (by omega) hAM hsymM hFM hR₀
  obtain ⟨Tr, hTr, R, hR, cstar, hc, τs, hτs, Cr, hCr, hrates⟩ :=
    GenRatesId.generated_dynamics_rates_id (d := 3) (ms := 2) (s := s) (p := p) hm2
      (by omega) hp (by omega) hA hsym hF hR₀
  refine ⟨Tr, hTr, R, hR, cstar, hc, τs, hτs, fun U₀ hCD hU₀ hUp hE hK₀ => ?_⟩
  -- the physical solution (as in `GenPhysIdFinal.generated_physical_identification`)
  obtain ⟨U, P, hUP⟩ := hkato U₀ hU₀ hUp hE
  obtain ⟨UM, PM, hMP, hMs⟩ := hkatoM U₀ hU₀ hUp hE
  obtain ⟨z₀, hdat₀, hC₀⟩ := hCD
  have hU0 : ∀ y, (fun c => U₀ c (Fin.cons 0 y)) = κ (stateF SM z₀ (Fin.cons 0 y)) := fun y =>
    funext fun c => (hdat₀ c y).symm
  have hinv := GenBackward.twoSided_invariant hAM hsymM hFM (tauKL κ) (fun j a v w => hτA j a v w)
    (fun a v => hτF a v) hMP (fun y => by
      rw [tauKL_apply, hU0 y, tauK_of_isSymmP (isSymmP_stateF z₀ _)])
  obtain ⟨τ₀, hτ₀, hKW⟩ := exists_twoSided_mem hMP hδK hKδ hK₀
  set ε := min τ₀ TM with hεdef
  have hε : 0 < ε := lt_min hτ₀ hTM0
  have hKWε : ∀ x : ST 3, x ∈ openSlab (-ε) ε → (fun c => UM c x) ∈ K := fun x hx => by
    have h1 : -ε < x 0 := hx.1
    have h2 : x 0 < ε := hx.2
    exact hKW x ⟨show -τ₀ < x 0 by linarith [min_le_left τ₀ TM],
      show x 0 < τ₀ by linarith [min_le_left τ₀ TM]⟩
  have hsymε : ∀ x : ST 3, x ∈ openSlab (-ε) ε → AJKatoMod.IsSymmP (Wof κ UM x) := fun x hx => by
    have h1 : -ε < x 0 := hx.1
    have h2 : x 0 < ε := hx.2
    exact isSymmP_of_tauK (hinv x ⟨by linarith [min_le_right τ₀ TM],
      by linarith [min_le_right τ₀ TM]⟩)
  obtain ⟨z, t₁', ht₁', hid⟩ := MathPhys.GenCplId.ChL.core_identification_cplL hS hU hC hN hT hκ hKc hA hsym hF hAK hFK
    hAM hFM hAMK hFMK hdat₀ hC₀ hMP hMs hε (min_le_right τ₀ TM) hKWε hsymε hTK0 hUP
  -- the identification interval
  set t₁ := min t₁' (min (TK / 2) Tr) with ht₁def
  have ht₁0 : 0 < t₁ := lt_min ht₁' (lt_min (by linarith) hTr)
  have ht₁t : t₁ ≤ t₁' := min_le_left _ _
  have ht₁K : t₁ < TK := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
    (by linarith)
  have ht₁r : t₁ ≤ Tr := (min_le_right _ _).trans (min_le_right _ _)
  have hsl : ∀ x ∈ slab (d := 3) 0 t₁, x ∈ slab (d := 3) 0 t₁' := fun x hx =>
    ⟨hx.1, hx.2.trans ht₁t⟩
  set Vf := stC κ SM z with hVf
  have hV : ∀ b, ContDiff ℝ ∞ (Vf b) := contDiff_stC κ SM z
  have hVp : ∀ b, IsSPeriodic (Vf b) := isSPeriodic_stC κ SM z
  have hUVf : ∀ x ∈ slab (d := 3) 0 t₁, ∀ b, U b x = Vf b x := fun x hx b =>
    ((hid x (hsl x hx)).1 b)
  have hV0 : ∀ b y, Vf b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y) := fun b y => by
    rw [← hUVf (Fin.cons 0 y) (by show (Fin.cons 0 y : ST 3) 0 ∈ Icc 0 t₁; simpa using ht₁0.le)
      b]
    exact hUP.init b y
  -- the equation of `V` on `[0, t₁]`
  have hVeq : ∀ b, ∀ t ∈ Icc 0 t₁, ∀ y,
      pd (Vf b) 0 (Fin.cons t y) = QLEnergy.genG A F Vf b (Fin.cons t y) := by
    intro b t ht y
    have hx : (Fin.cons t y : ST 3) ∈ slab (d := 3) 0 t₁ := by
      show (Fin.cons t y : ST 3) 0 ∈ Icc 0 t₁; simpa using ht
    have htK : t ∈ Ioo (-TK) TK := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- the spatial derivatives
    have hP : ∀ (b' : Fin (dimS m V S S')) (i : Fin 3),
        P b' i (Fin.cons t y) = pd (Vf b') i.succ (Fin.cons t y) := by
      intro b' i
      have h1 := hUP.space b' i (Fin.cons t y)
      have e : (fun σ : ℝ => U b' ((Fin.cons t y : ST 3) + σ • ev i.succ)) =
          fun σ => Vf b' ((Fin.cons t y : ST 3) + σ • ev i.succ) := by
        funext σ
        refine hUVf _ ?_ b'
        show ((Fin.cons t y : ST 3) + σ • ev i.succ) 0 ∈ Icc 0 t₁
        simpa [Pi.single_apply, Fin.succ_ne_zero] using ht
      rw [e] at h1
      exact h1.unique (hasDerivAt_line0 (hV b') _ i.succ)
    have hgen : KatoGalerkin.genP A F U P b (Fin.cons t y) =
        QLEnergy.genG A F Vf b (Fin.cons t y) := by
      unfold KatoGalerkin.genP QLEnergy.genG QLEnergy.compF
      have hval : (fun c => U c (Fin.cons t y)) = fun c => Vf c (Fin.cons t y) :=
        funext fun c => hUVf _ hx c
      rw [hval]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b' _ => ?_
      rw [hP b' i]
    have hUt := (hUP.time b t htK y).hasDerivWithinAt (s := Icc 0 t₁)
    have hcongr : HasDerivWithinAt (fun σ => Vf b (Fin.cons σ y))
        (KatoGalerkin.genP A F U P b (Fin.cons t y)) (Icc 0 t₁) t :=
      hUt.congr (fun σ hσ => (hUVf _ (by show (Fin.cons σ y : ST 3) 0 ∈ Icc 0 t₁; simpa using hσ)
        b).symm) (hUVf _ hx b).symm
    have hVd := (hasDerivAt_time (hV b) t y).hasDerivWithinAt (s := Icc 0 t₁)
    rw [← hgen]
    exact (uniqueDiffOn_Icc ht₁0 t ht).eq_deriv _ hVd hcongr
  obtain ⟨Ur, Pr, D₂, hUrc, hUrper, hUr0, hPr, hUrt, hUrcoef, hD₂d, hunique, hrec⟩ :=
    hrates U₀ hU₀ hUp hE
  have hUrV := hunique Vf t₁ ht₁r hV hVp hV0 hVeq
  obtain ⟨hVt, hVtt⟩ := exact_time_derivs ht₁0 ht₁r hUrt hD₂d hV hUrV
  refine ⟨z, t₁, ht₁0, ht₁r, fun x hx => (hid x (hsl x hx)).2, hV0, fun {nB} eB {nD} eD => ?_⟩
  have hphys : ∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 := fun x hx =>
    ⟨((hid x (hsl x hx)).2).1, ((hid x (hsl x hx)).2).2.1⟩
  obtain ⟨C, hC0, η, hη, K2, hK2, hK2c, hread⟩ := MathPhys.GenReadout.ChL.readouts_of_identifiedL κ hS hs hphys hUrV hVt
    hVtt hCr hτs eB eD
  refine ⟨C, hC0, Cr, hCr, η, hη, K2, hK2, hK2c,
    fun N τ hτ hcfl hττ a₀ δ ha₀ hδ hdata hsmall => ?_⟩
  obtain ⟨Ud, hUd0, hUdrec, -, hherm⟩ := hrec N τ hτ hcfl hττ a₀ δ ha₀ hδ hdata
  set ν : ℝ := 1 / ((N : ℝ) + 1) ^ p with hν
  have hν0 : 0 ≤ ν := by positivity
  refine ⟨Ud, hUd0, hUdrec, fun j hj θ hθ S₀ => ?_, fun j hj θ hθ S₀ => ?_, fun j hj => ?_⟩
  · -- the state-level rate against the exact solution
    have hjr : ((j : ℝ) + 1) * τ ≤ Tr := hj.trans ht₁r
    have hh := (hherm j hjr θ hθ S₀).1
    have ht : (j : ℝ) * τ + θ * τ ∈ Icc 0 t₁ := by
      constructor
      · have := hθ.1; positivity
      · have : θ * τ ≤ τ := by nlinarith [hθ.2]
        nlinarith
    have hcoef : ∀ b k, coef (Ur b) ((j : ℝ) * τ + θ * τ) k =
        coef (stC κ SM z b) ((j : ℝ) * τ + θ * τ) k := fun b k =>
      GenGalCons.coef_congr_slice (fun y => hUrV _ (by
        show (Fin.cons ((j : ℝ) * τ + θ * τ) y : ST 3) 0 ∈ Icc 0 t₁
        simpa using ht) b) k
    simp only [hcoef] at hh
    exact hh
  · -- the time-derivative rate against the exact solution
    have hjr : ((j : ℝ) + 1) * τ ≤ Tr := hj.trans ht₁r
    have hh := (hherm j hjr θ hθ S₀).2.1
    have ht : (j : ℝ) * τ + θ * τ ∈ Icc 0 t₁ := by
      constructor
      · have := hθ.1; positivity
      · have : θ * τ ≤ τ := by nlinarith [hθ.2]
        nlinarith
    have hcoef : ∀ b k, coef (KatoGalerkin.genP A F Ur Pr b) ((j : ℝ) * τ + θ * τ) k =
        coef (pd (stC κ SM z b) 0) ((j : ℝ) * τ + θ * τ) k := fun b k =>
      GenGalCons.coef_congr_slice (fun y => (hVt b _ ht y).symm) k
    simp only [hcoef] at hh
    exact hh
  · have hjr : ((j : ℝ) + 1) * τ ≤ Tr := hj.trans ht₁r
    exact hread τ hτ hττ δ ν hδ hν0 hsmall j (Ud j) (Ud (j + 1))
      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) hj
      (fun θ hθ S₀ => (hherm j hjr θ hθ S₀).1) (fun θ hθ S₀ => (hherm j hjr θ hθ S₀).2.1)
      (fun θ hθ S₀ => (hherm j hjr θ hθ S₀).2.2)
end MathPhys.GenCplDyn.ChL

/-! #### `record_cell_cpl` (from `Continuum/GeneratedCoupledStationarity.lean`) -/
namespace MathPhys.GenCplSt.ChL
open Finset Set Filter Topology
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite GenResMaps GenPhysIdFinal
  GenReadout EHJetVariation EHFieldVariation GenMatVar GenNoether GenFOGrav GenMatEuler GenFOAction
  GenCell GenCellVar GenCellBulk KatoGalerkin GenRecCell SpectralGalerkin CubicHermite GenRecNodes
  GenStat GenDAct GenDEul GenDFld GenDStress GenDiracCur GenCplCV GenCplCD
open MeasureTheory
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {n : ℕ} (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ))
set_option maxHeartbeats 8000000 in
/-- **The first variation of the complete first-order action on a record cell** (smooth
back-reacting Dirac data, `κ ≠ 0`): bulk plus end fluxes, the bulk being the complete bosonic rows
plus the Dirac rows, bounded through the bosonic and the Dirac readouts. -/
theorem record_cell_cplL (SM : SMData (MatLie m) V S S') (hS : GenChL.SMSmoothL SM)
    (hC : CoupledDirac SM) (hκ : SM.κ ≠ 0) {W Y : Fin n → ST 3 → ℝ}
    (hW : ∀ c, ContDiff ℝ ∞ (W c)) (hWp : ∀ c, IsSPeriodic (W c))
    (hY : ∀ c, ContDiff ℝ ∞ (Y c)) (hYp : ∀ c, IsSPeriodic (Y c)) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ x : ST 3, x 0 ∈ Icc a b → HeadChart κ (fun c => W c x))
    {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) (eBs : (Fin nB → ℝ) →L[ℝ] BosP m V)
    (heB : ∀ r, eBs (eB r) = r) {nD : ℕ} (eD : S × S' →L[ℝ] (Fin nD → ℝ))
    (eDs : (Fin nD → ℝ) →L[ℝ] S × S') (heD : ∀ r, eDs (eD r) = r)
    {Kg : Set Met} {Kh : Set (Met × S × S')} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ g ∈ Kg, ∀ (c : Fin nB → ℝ) (y : Fin n → ℝ),
      |bulkJ SM g (eBs c) (Lg κ y) (LA κ y) (LH κ y)| ≤ M * ‖c‖ * ‖y‖)
    (hMD : ∀ h ∈ Kh, ∀ (c : Fin nD → ℝ) (y : Fin n → ℝ),
      |dirJ hC.toDiracPairing h.1 (Lg κ y) h.2.1 h.2.2 (eDs c) (Lψ κ y) (Lψb κ y)| ≤
        M * ‖c‖ * ‖y‖)
    (hKg : ∀ x : ST 3, x 0 ∈ Icc a b → Lg κ (fun c => W c x) ∈ Kg)
    (hKh : ∀ x : ST 3, x 0 ∈ Icc a b →
      (Lg κ (fun c => W c x), Lψ κ (fun c => W c x), Lψb κ (fun c => W c x)) ∈ Kh)
    {s sD : ℕ} {B BD : ℝ}
    (hB : ∀ t ∈ Ioo a b, ∑ k, Q s (fun x => eB (bosR SM (hjF κ W x)) k) t ≤ B ^ 2)
    (hBD : ∀ t ∈ Ioo a b, ∑ k, Q sD (fun x => eD (dirR SM (hjF κ W x)) k) t ≤ BD ^ 2) :
    ∃ D : ℝ, cellInt a b (fun x => fderiv ℝ (L1C SM hC.toDiracPairing.P) (hjet1C κ W x)
        (hjet1C κ Y x)) =
        D + (fluxRC κ hC.toDiracPairing W Y b - fluxRC κ hC.toDiracPairing W Y a) ∧
      |D| ≤ M * ((Real.sqrt ((b - a) * B ^ 2) + Real.sqrt ((b - a) * BD ^ 2)) *
        Real.sqrt (cellInt a b (fun x => ∑ c, Y c x ^ 2))) := by
  set hP := hC.toDiracPairing with hPdef
  set SB := GenDSN.bos0 SM hC.toVariationalDirac with hSB
  obtain ⟨z', hz'⟩ := exists_cell_ext (m := m) (V := V) (S := S) (S' := S') κ hW hWp hab hc
  have hYv : ContDiff ℝ ∞ (fun x => fun c => Y c x) := contDiff_pi.2 hY
  set kY : ST 3 → Met := fun x => Lg κ (fun c => Y c x) with hkY
  set XY : ST 3 → Fin 4 → MatLie m := fun x => LA κ (fun c => Y c x) with hXY
  set ηY : ST 3 → V := fun x => LH κ (fun c => Y c x) with hηY
  set φY : ST 3 → S := fun x => Lψ κ (fun c => Y c x) with hφY
  set φbY : ST 3 → S' := fun x => Lψb κ (fun c => Y c x) with hφbY
  have hk : ContDiff ℝ ∞ kY := (Lg κ).contDiff.comp hYv
  have hX : ContDiff ℝ ∞ XY := (LA κ).contDiff.comp hYv
  have hη : ContDiff ℝ ∞ ηY := (LH κ).contDiff.comp hYv
  have hφ : ContDiff ℝ ∞ φY := (Lψ κ).contDiff.comp hYv
  have hφb : ContDiff ℝ ∞ φbY := (Lψb κ).contDiff.comp hYv
  have hks : ∀ y μ ν, kY y μ ν = kY y ν μ := fun y μ ν => symL_symm _ μ ν
  have hkp : IsSPeriodic kY := fun k x => by simp only [hkY, hYp _ k x]
  have hXp : IsSPeriodic XY := fun k x => by simp only [hXY, hYp _ k x]
  have hηp : IsSPeriodic ηY := fun k x => by simp only [hηY, hYp _ k x]
  have hφp : IsSPeriodic φY := fun k x => by simp only [hφY, hYp _ k x]
  have hφbp : IsSPeriodic φbY := fun k x => by simp only [hφbY, hYp _ k x]
  have ha : a - 1 < a := by linarith
  have hb : b < b + 1 := by linarith
  -- the bosonic and the Dirac cell variations
  have hcv : cellInt a b (fun x => fderiv ℝ (L1SM SM) (j1F z'.g z'.A z'.H x) (j1F kY XY ηY x)) =
      cellInt a b (bulkT SB z' kY XY ηY) + (fluxT SB z' kY XY ηY b - fluxT SB z' kY XY ηY a) :=
    cell_variation SB (GenDSN.bos0Var hC) z' hk hks hkp hX hXp hη hηp hab
  have hcd := cell_dirac hP z' hk hks hkp hX hη hφ hφp hφb hφbp hab
  -- the jets on the closed cell
  have hsl : ∀ t ∈ Icc a b, ∀ y : Fin 3 → ℝ, (Fin.cons t y : ST 3) 0 ∈ Icc a b := fun t ht y => by
    simpa using ht
  have hj1 : ∀ x : ST 3, x 0 ∈ Icc a b → j1F z'.g z'.A z'.H x = hjet1 κ W x := fun x hx => by
    obtain ⟨h1, h2, h3, -, -⟩ := hz' x hx
    exact j1F_of_near κ h1 h2 h3
  have hjC : ∀ x : ST 3, x 0 ∈ Icc a b → jC z' x = hjet1C κ W x := fun x hx => by
    obtain ⟨-, -, -, h4, h5⟩ := hz' x hx
    have e4 : ∀ γ, pd z'.ψ γ x = Lψ κ (fun c => pd (W c) γ x) := fun γ => by
      rw [(SlabLocal.pd_eventuallyEq h4 γ).eq_of_nhds, pd_famL _ hW]
    have e5 : ∀ γ, pd z'.ψb γ x = Lψb κ (fun c => pd (W c) γ x) := fun γ => by
      rw [(SlabLocal.pd_eventuallyEq h5 γ).eq_of_nhds, pd_famL _ hW]
    unfold jC hjet1C
    rw [hj1 x hx, h4.eq_of_nhds, h5.eq_of_nhds]
    simp only [e4, e5]
  have hjW : ∀ x, jW kY XY ηY φY φbY x = hjet1C κ Y x := fun x => by
    have e4 : ∀ γ, pd φY γ x = Lψ κ (fun c => pd (Y c) γ x) := fun γ => pd_famL _ hY γ x
    have e5 : ∀ γ, pd φbY γ x = Lψb κ (fun c => pd (Y c) γ x) := fun γ => pd_famL _ hY γ x
    unfold jW hjet1C
    simp only [e4, e5]
    rfl
  have hpt : ∀ x : ST 3, x 0 ∈ Icc a b →
      fderiv ℝ (L1C SM hP.P) (hjet1C κ W x) (hjet1C κ Y x) =
        fderiv ℝ (L1SM SM) (j1F z'.g z'.A z'.H x) (j1F kY XY ηY x) +
          fderiv ℝ (L1D SM hP.P) (jC z' x) (jW kY XY ηY φY φbY x) := fun x hx => by
    have hm : jC z' x ∈ chart1C m V S S' := ⟨GenCell.Tuple_det_neg z' x, z'.lor x⟩
    rw [← hjC x hx, ← hjW x, fderiv_L1C SM hP.P hm]
    rfl
  have hc1 : ContinuousOn (fun x => fderiv ℝ (L1SM SM) (j1F z'.g z'.A z'.H x) (j1F kY XY ηY x))
      (openSlab (a - 1) (b + 1)) :=
    continuousOn_fderiv_jet isOpen_chart1 (contDiffOn_L1SM SM)
      (continuous_j1F z'.g_smooth z'.A_smooth z'.H_smooth) (continuous_j1F hk hX hη)
      fun x _ => GenCell.Tuple_det_neg z' x
  have hc2 : ContinuousOn (fun x => fderiv ℝ (L1D SM hP.P) (jC z' x) (jW kY XY ηY φY φbY x))
      (openSlab (a - 1) (b + 1)) :=
    continuousOn_fderiv_jet isOpen_chart1C (contDiffOn_L1D SM hP.P) (continuous_jC z')
      (continuous_jW hk hX hη hφ hφb) fun x _ => ⟨GenCell.Tuple_det_neg z' x, z'.lor x⟩
  have hL : cellInt a b (fun x => fderiv ℝ (L1C SM hP.P) (hjet1C κ W x) (hjet1C κ Y x)) =
      cellInt a b (fun x => fderiv ℝ (L1SM SM) (j1F z'.g z'.A z'.H x) (j1F kY XY ηY x)) +
        cellInt a b (fun x => fderiv ℝ (L1D SM hP.P) (jC z' x) (jW kY XY ηY φY φbY x)) := by
    rw [← cellInt_add_on hc1 hc2 ha hab hb]
    exact cellInt_congr hab fun t ht y _ => hpt _ (hsl t ht y)
  -- the fluxes
  have hfl : ∀ t ∈ Icc a b, fluxT SB z' kY XY ηY t = fluxR (V := V) κ SM W Y t := by
    intro t ht
    show fluxT SB z' kY XY ηY t = fluxR (V := V) κ SB W Y t
    unfold fluxT fluxR
    have e1 : ∀ y : Fin 3 → ℝ, PFJ 0 (j1M z'.g (Fin.cons t y)) (j1M kY (Fin.cons t y)) =
        PFJ 0 (hjet1 κ W (Fin.cons t y)).1 (hjet1 κ Y (Fin.cons t y)).1 := fun y => by
      rw [← hj1 _ (hsl t ht y)]; rfl
    have e2 : ∀ y : Fin 3 → ℝ, fderiv ℝ (WJ 0) (j1M z'.g (Fin.cons t y)) (j1M kY (Fin.cons t y)) =
        fderiv ℝ (WJ 0) (hjet1 κ W (Fin.cons t y)).1 (hjet1 κ Y (Fin.cons t y)).1 := fun y => by
      rw [← hj1 _ (hsl t ht y)]; rfl
    have e3 : ∀ y : Fin 3 → ℝ, matFlux z' SB XY ηY 0 (Fin.cons t y) =
        MFJ SB (hjet1 κ W (Fin.cons t y)) (hjet1 κ Y (Fin.cons t y)) := fun y => by
      rw [matFlux_eq_MFJ SB z' XY ηY kY, hj1 _ (hsl t ht y)]; rfl
    unfold sint
    simp only [e1, e2, e3]
  have hfd : ∀ t ∈ Icc a b, sint (fluxD hP z' kY φY φbY 0) t = fluxDR κ hP W Y t := by
    intro t ht
    have e : ∀ y : Fin 3 → ℝ, fluxD hP z' kY φY φbY 0 (Fin.cons t y) =
        fluxDJ hP 0 (Lg κ (fun c => W c (Fin.cons t y))) (Lψ κ (fun c => W c (Fin.cons t y)))
          (Lψb κ (fun c => W c (Fin.cons t y))) (Lg κ (fun c => Y c (Fin.cons t y)))
          (Lψ κ (fun c => Y c (Fin.cons t y))) (Lψb κ (fun c => Y c (Fin.cons t y))) := fun y => by
      obtain ⟨h1, -, -, h4, h5⟩ := hz' _ (hsl t ht y)
      rw [fluxD_eq, h1.eq_of_nhds, h4.eq_of_nhds, h5.eq_of_nhds]
    unfold fluxDR sint
    simp only [e]
  -- the bulk
  have hBI : ∀ x, bulkT SB z' kY XY ηY x + bulkD hP z' kY XY ηY φY φbY x =
      bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x) +
        dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x) (φbY x) :=
    fun x => bulk_identity z' hC hκ kY XY ηY φY φbY x
  have hbF : Continuous (bosF SM z') := (MathPhys.ActualJetState.ChL.contDiff_bosFL SM z' hS).continuous
  have hdF : ContDiff ℝ ∞ (dirF SM z') := contDiff_dirF SM z'
  have hJc : Continuous fun x => bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hp : Continuous fun x : ST 3 => (z'.g x, bosF SM z' x, (kY x, XY x, ηY x)) :=
      z'.g_smooth.continuous.prodMk (hbF.prodMk (hk.continuous.prodMk (hX.continuous.prodMk
        hη.continuous)))
    exact ContinuousAt.comp (x := x)
      (g := fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
        bulkJ SM q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
      (f := fun x : ST 3 => (z'.g x, bosF SM z' x, (kY x, XY x, ηY x)))
      (continuousAt_bulkJ SM (p := (z'.g x, bosF SM z' x, (kY x, XY x, ηY x)))
      (GenCell.Tuple_det_neg z' x).ne) hp.continuousAt
  have hDc : Continuous fun x =>
      dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x) (φbY x) :=
    continuous_iff_continuousAt.2 fun x => (contDiffAt_dirJ_comp hP z'.g_smooth.contDiffAt
      hk.contDiffAt z'.ψ_smooth.contDiffAt z'.ψb_smooth.contDiffAt hdF.contDiffAt hφ.contDiffAt
      hφb.contDiffAt (chartM_tuple z' x)).continuousAt
  have hBDc : Continuous (bulkD hP z' kY XY ηY φY φbY) :=
    continuous_bulkD hP z' hk hks hX hη hφ hφb
  have hBTc : Continuous (bulkT SB z' kY XY ηY) :=
    ((hJc.add hDc).sub hBDc).congr fun x => by
      show bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x) +
        dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x) (φbY x) -
        bulkD hP z' kY XY ηY φY φbY x = bulkT SB z' kY XY ηY x
      rw [← hBI x]; ring
  have hsum : cellInt a b (bulkT SB z' kY XY ηY) + cellInt a b (bulkD hP z' kY XY ηY φY φbY) =
      cellInt a b (fun x => bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x)) +
        cellInt a b (fun x => dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x)
          (φbY x)) := by
    rw [← cellInt_add_on hBTc.continuousOn hBDc.continuousOn ha hab hb,
      ← cellInt_add_on hJc.continuousOn hDc.continuousOn ha hab hb]
    exact cellInt_congr hab fun t _ y _ => hBI _
  refine ⟨cellInt a b (fun x => bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x)) +
    cellInt a b (fun x => dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x)
      (φbY x)), ?_, ?_⟩
  · rw [hL, hcv, hcd, hfl a ⟨le_rfl, hab⟩, hfl b ⟨hab, le_rfl⟩, hfd a ⟨le_rfl, hab⟩,
      hfd b ⟨hab, le_rfl⟩, ← hsum]
    unfold fluxRC
    ring
  -- the bounds
  have hg' : ∀ x : ST 3, x 0 ∈ Icc a b → z'.g x = Lg κ (fun c => W c x) := fun x hx =>
    (hz' x hx).1.eq_of_nhds
  have hB1 := abs_cellInt_readout hJc hY hab (R := fun x => eB (bosF SM z' x))
    (Rr := fun x => eB (bosR SM (hjF κ W x))) (eB.continuous.comp hbF) hM0
    (fun x hx => by
      have := hM _ (hKg x hx) (eB (bosF SM z' x)) (fun c => Y c x)
      rw [heB, ← hg' x hx] at this
      exact this)
    (fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hz' x hx
      show eB (bosF SM z' x) = eB (bosR SM (hjF κ W x))
      rw [← bosR_hj2 z' x SM, hj2_of_near κ h1 h2 h3 h4 h5]) hB
  have hB2 := abs_cellInt_readout hDc hY hab (R := fun x => eD (dirF SM z' x))
    (Rr := fun x => eD (dirR SM (hjF κ W x))) (eD.continuous.comp hdF.continuous) hM0
    (fun x hx => by
      have := hMD _ (hKh x hx) (eD (dirF SM z' x)) (fun c => Y c x)
      rw [heD] at this
      obtain ⟨h1, -, -, h4, h5⟩ := hz' x hx
      rw [h1.eq_of_nhds, h4.eq_of_nhds, h5.eq_of_nhds]
      exact this)
    (fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hz' x hx
      show eD (dirF SM z' x) = eD (dirR SM (hjF κ W x))
      rw [← dirR_hj2 z' x SM, hj2_of_near κ h1 h2 h3 h4 h5]) hBD
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hB1 hB2
    _ = _ := by ring
end MathPhys.GenCplSt.ChL

/-! #### `stationarity_of_cells_cpl` (from `Continuum/GeneratedCoupledStationarity.lean`) -/
namespace MathPhys.GenCplSt.ChL
open Finset Set Filter Topology
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite GenResMaps GenPhysIdFinal
  GenReadout EHJetVariation EHFieldVariation GenMatVar GenNoether GenFOGrav GenMatEuler GenFOAction
  GenCell GenCellVar GenCellBulk KatoGalerkin GenRecCell SpectralGalerkin CubicHermite GenRecNodes
  GenStat GenDAct GenDEul GenDFld GenDStress GenDiracCur GenCplCV GenCplCD
open MeasureTheory
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {n : ℕ} (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ))
set_option maxHeartbeats 4000000 in
/-- **`eq:generated-stationarity` for the complete action on a chart record** (smooth
back-reacting Dirac data, `κ ≠ 0`): if every cell of the Hermite reconstruction `R(U, P)` on
`[0, Jτ]` is in the Lorentzian chart, with head metric in `K_g` and head metric/spinor values in
`K_h` (bulk constant `M` for the bosonic rows `bulkJ` and the Dirac rows `dirJ`), and the bosonic
and Dirac readouts satisfy `Σ_k Q_s(e_B R_B)_k ≤ B²`, `Σ_k Q_{s_D}(e_D R_D)_k ≤ B_D²` on every
slice, then for every nodal variation `V = (v, w)` with fixed collar the derivative
`D S^{cmp}[V]` of the complete composite action (bosonic plus Dirac) exists and
`|D S^{cmp}[V]| ≤ M (B + B_D) √(8Jτ) ‖V‖_{0,τ}`. -/
theorem stationarity_of_cells_cplL (SM : SMData (MatLie m) V S S') (hS : GenChL.SMSmoothL SM)
    (hC : CoupledDirac SM) (hκ : SM.κ ≠ 0) {N q : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {J : ℕ} {U P : ℕ → GS 3 n N}
    (hc : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      HeadChart κ (fun c => recF q τ U P j c x))
    {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) (eBs : (Fin nB → ℝ) →L[ℝ] BosP m V)
    (heB : ∀ r, eBs (eB r) = r) {nD : ℕ} (eD : S × S' →L[ℝ] (Fin nD → ℝ))
    (eDs : (Fin nD → ℝ) →L[ℝ] S × S') (heD : ∀ r, eDs (eD r) = r)
    {Kg : Set Met} {Kh : Set (Met × S × S')} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ g ∈ Kg, ∀ (c : Fin nB → ℝ) (y : Fin n → ℝ),
      |bulkJ SM g (eBs c) (Lg κ y) (LA κ y) (LH κ y)| ≤ M * ‖c‖ * ‖y‖)
    (hMD : ∀ h ∈ Kh, ∀ (c : Fin nD → ℝ) (y : Fin n → ℝ),
      |dirJ hC.toDiracPairing h.1 (Lg κ y) h.2.1 h.2.2 (eDs c) (Lψ κ y) (Lψb κ y)| ≤
        M * ‖c‖ * ‖y‖)
    (hKg : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      Lg κ (fun c => recF q τ U P j c x) ∈ Kg)
    (hKh : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      (Lg κ (fun c => recF q τ U P j c x), Lψ κ (fun c => recF q τ U P j c x),
        Lψb κ (fun c => recF q τ U P j c x)) ∈ Kh)
    {s sD : ℕ} {B BD : ℝ} (hB0 : 0 ≤ B) (hBD0 : 0 ≤ BD)
    (hB : ∀ j < J, ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ k, Q s (fun x => eB (bosR SM (hjF κ (recF q τ U P j) x)) k) t ≤ B ^ 2)
    (hBD : ∀ j < J, ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ k, Q sD (fun x => eD (dirR SM (hjF κ (recF q τ U P j) x)) k) t ≤ BD ^ 2)
    (v w : ℕ → GS 3 n N) (hv0 : v 0 = 0) (hw0 : w 0 = 0) (hvJ : v J = 0) (hwJ : w J = 0) :
    ∃ D : ℝ, HasDerivAt (fun ε : ℝ => ScmpC κ SM hC.toDiracPairing.P q τ J
        (fun j => U j + ε • v j) (fun j => P j + ε • w j)) D 0 ∧
      |D| ≤ M * (B + BD) * Real.sqrt (8 * (J * τ)) * vnorm q τ J v w := by
  set hP := hC.toDiracPairing with hPdef
  set W : ℕ → Fin n → ST 3 → ℝ := fun j => recF q τ U P j with hWdef
  set Y : ℕ → Fin n → ST 3 → ℝ := fun j => recF q τ v w j with hYdef
  have hWs : ∀ j c, ContDiff ℝ ∞ (W j c) := fun j c => contDiff_recF q τ U P j c
  have hWp : ∀ j c, IsSPeriodic (W j c) := fun j c => isSPeriodic_recF q τ U P j c
  have hYs : ∀ j c, ContDiff ℝ ∞ (Y j c) := fun j c => contDiff_recF q τ v w j c
  have hYp : ∀ j c, IsSPeriodic (Y j c) := fun j c => isSPeriodic_recF q τ v w j c
  have hab : ∀ j : ℕ, (j : ℝ) * τ ≤ ((j : ℝ) + 1) * τ := fun j => by nlinarith
  -- linearity of the composite action
  have hlin : ∀ (ε : ℝ) (j : ℕ) (x : ST 3),
      hjet1C κ (recF q τ (fun i => U i + ε • v i) (fun i => P i + ε • w i) j) x =
        hjet1C κ (W j) x + ε • hjet1C κ (Y j) x := fun ε j x => by
    have e : recF q τ (fun i => U i + ε • v i) (fun i => P i + ε • w i) j =
        fun c y => W j c y + ε * Y j c y :=
      funext fun c => funext fun y => recF_add_smul q τ U P v w ε j c y
    rw [e]
    exact hjet1C_add_smul κ (hWs j) (hYs j) ε x
  have hSe : (fun ε : ℝ => ScmpC κ SM hP.P q τ J (fun j => U j + ε • v j)
      (fun j => P j + ε • w j)) =
      fun ε => ∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
        (fun x => L1C SM hP.P (hjet1C κ (W j) x + ε • hjet1C κ (Y j) x)) := by
    funext ε
    unfold ScmpC
    simp only [hlin]
  have hder : HasDerivAt (fun ε : ℝ => ScmpC κ SM hP.P q τ J (fun j => U j + ε • v j)
      (fun j => P j + ε • w j))
      (∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
        (fun x => fderiv ℝ (L1C SM hP.P) (hjet1C κ (W j) x) (hjet1C κ (Y j) x))) 0 := by
    rw [hSe]
    exact HasDerivAt.fun_sum fun j hj => cell_hasDerivAt_C κ SM hP.P (hWs j) (hWp j) (hYs j)
      (hYp j) (hab j) (hc j (Finset.mem_range.1 hj))
  refine ⟨_, hder, ?_⟩
  -- the cells
  have hcell : ∀ j ∈ Finset.range J, ∃ Dj : ℝ,
      cellInt (j * τ) ((j + 1) * τ)
          (fun x => fderiv ℝ (L1C SM hP.P) (hjet1C κ (W j) x) (hjet1C κ (Y j) x)) =
        Dj + (fluxRC κ hP (W j) (Y j) (((j : ℝ) + 1) * τ) -
          fluxRC κ hP (W j) (Y j) ((j : ℝ) * τ)) ∧
      |Dj| ≤ M * ((Real.sqrt ((((j : ℝ) + 1) * τ - j * τ) * B ^ 2) +
          Real.sqrt ((((j : ℝ) + 1) * τ - j * τ) * BD ^ 2)) *
        Real.sqrt (cellInt (j * τ) ((j + 1) * τ) (fun x => ∑ c, Y j c x ^ 2))) := fun j hj =>
    MathPhys.GenCplSt.ChL.record_cell_cplL κ SM hS hC hκ (hWs j) (hWp j) (hYs j) (hYp j) (hab j)
      (hc j (Finset.mem_range.1 hj)) eB eBs heB eD eDs heD hM0 hM hMD
      (hKg j (Finset.mem_range.1 hj)) (hKh j (Finset.mem_range.1 hj))
      (hB j (Finset.mem_range.1 hj)) (hBD j (Finset.mem_range.1 hj))
  choose! Dj hDj using hcell
  -- the fluxes telescope
  set G : ℕ → ℝ := fun j => fluxRC κ hP (W j) (Y j) ((j : ℝ) * τ) with hG
  have hnode : ∀ j, fluxRC κ hP (W j) (Y j) (((j : ℝ) + 1) * τ) = G (j + 1) := fun j => by
    simp only [hG, fluxRC]
    push_cast
    rw [fluxR_congr κ SM (fun y => recF_node κ q τ hτ.ne' U P j y)
      (fun y => recF_node κ q τ hτ.ne' v w j y),
      fluxDR_congr κ hP (fun y c => recF_node_val q τ hτ.ne' U P j c y)
      (fun y c => recF_node_val q τ hτ.ne' v w j c y)]
  have hG0 : G 0 = 0 := by
    simp only [hG, fluxRC]
    rw [fluxR_zero κ SM fun y => recF_node_zero κ q τ hτ.ne' v w 0 hv0 hw0 y,
      fluxDR_zero κ hP fun y c => recF_node_val_zero q τ hτ.ne' v w 0 hv0 hw0 c y]
    simp
  have hGJ : G J = 0 := by
    simp only [hG, fluxRC]
    rw [fluxR_zero κ SM fun y => recF_node_zero κ q τ hτ.ne' v w J hvJ hwJ y,
      fluxDR_zero κ hP fun y c => recF_node_val_zero q τ hτ.ne' v w J hvJ hwJ c y]
    simp
  have hsum : ∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
      (fun x => fderiv ℝ (L1C SM hP.P) (hjet1C κ (W j) x) (hjet1C κ (Y j) x)) =
      ∑ j ∈ Finset.range J, Dj j := by
    rw [Finset.sum_congr rfl fun j hj => (hDj j hj).1]
    simp only [hnode, Finset.sum_add_distrib]
    have := Finset.sum_range_sub G J
    rw [hG0, hGJ] at this
    simp only [hG] at this ⊢
    linarith
  rw [hsum]
  -- the bound
  set c : ℕ → ℝ := fun j => nrm2 q (v j) + τ ^ 2 * nrm2 q (w j) with hcdef
  have hc0 : ∀ j, 0 ≤ c j := fun j =>
    add_nonneg (nrm2_nonneg q _) (mul_nonneg (sq_nonneg τ) (nrm2_nonneg q _))
  set X : ℕ → ℝ := fun j => 4 * (c j + c (j + 1)) with hX
  have hX0 : ∀ j, 0 ≤ X j := fun j => by have := hc0 j; have := hc0 (j + 1); positivity
  have hBB : 0 ≤ B + BD := add_nonneg hB0 hBD0
  have hDb : ∀ j ∈ Finset.range J,
      |Dj j| ≤ M * (B + BD) * (Real.sqrt τ * Real.sqrt (τ * X j)) := by
    intro j hj
    refine (hDj j hj).2.trans ?_
    have e1 : ∀ C : ℝ, (((j : ℝ) + 1) * τ - j * τ) * C = τ * C := fun C => by ring
    have e2 : Real.sqrt (τ * B ^ 2) = Real.sqrt τ * B := by
      rw [Real.sqrt_mul hτ.le, Real.sqrt_sq hB0]
    have e3 : Real.sqrt (τ * BD ^ 2) = Real.sqrt τ * BD := by
      rw [Real.sqrt_mul hτ.le, Real.sqrt_sq hBD0]
    have hL2 := recF_L2 q hτ v w j
    have hL2' : cellInt (j * τ) ((j + 1) * τ) (fun x => ∑ c, Y j c x ^ 2) ≤ τ * X j := by
      refine hL2.trans (le_of_eq ?_)
      simp only [hX, hcdef]; ring
    rw [e1, e1, e2, e3]
    have := Real.sqrt_le_sqrt hL2'
    have hB' : 0 ≤ Real.sqrt τ * B + Real.sqrt τ * BD :=
      add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB0) (mul_nonneg (Real.sqrt_nonneg _) hBD0)
    calc M * ((Real.sqrt τ * B + Real.sqrt τ * BD) * Real.sqrt (cellInt (j * τ) ((j + 1) * τ)
          (fun x => ∑ c, Y j c x ^ 2))) ≤
          M * ((Real.sqrt τ * B + Real.sqrt τ * BD) * Real.sqrt (τ * X j)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hB') hM0
      _ = M * (B + BD) * (Real.sqrt τ * Real.sqrt (τ * X j)) := by ring
  have hCS := Real.sum_sqrt_mul_sqrt_le (Finset.range J) (f := fun _ => τ) (g := fun j => τ * X j)
    (fun _ => hτ.le) (fun j => mul_nonneg hτ.le (hX0 j))
  have hsumτ : ∑ _j ∈ Finset.range J, τ = J * τ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsumX : ∑ j ∈ Finset.range J, τ * X j ≤ 8 * (τ * ∑ j ∈ Finset.range (J + 1), c j) := by
    rw [← Finset.mul_sum]
    have := sum_adj_le (J := J) c hc0
    have e : ∑ j ∈ Finset.range J, X j = 4 * ∑ j ∈ Finset.range J, (c j + c (j + 1)) := by
      simp only [hX, Finset.mul_sum]
    rw [e]
    nlinarith
  have hvn : vnorm q τ J v w = Real.sqrt (τ * ∑ j ∈ Finset.range (J + 1), c j) := rfl
  have hMB : 0 ≤ M * (B + BD) := mul_nonneg hM0 hBB
  calc |∑ j ∈ Finset.range J, Dj j| ≤ ∑ j ∈ Finset.range J, |Dj j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range J, M * (B + BD) * (Real.sqrt τ * Real.sqrt (τ * X j)) :=
        Finset.sum_le_sum hDb
    _ = M * (B + BD) * ∑ j ∈ Finset.range J, Real.sqrt τ * Real.sqrt (τ * X j) := by
        rw [Finset.mul_sum]
    _ ≤ M * (B + BD) * (Real.sqrt (J * τ) *
          Real.sqrt (8 * (τ * ∑ j ∈ Finset.range (J + 1), c j))) := by
        refine mul_le_mul_of_nonneg_left (hCS.trans ?_) hMB
        rw [hsumτ]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsumX) (Real.sqrt_nonneg _)
    _ = M * (B + BD) * Real.sqrt (8 * (J * τ)) * vnorm q τ J v w := by
        rw [hvn, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
        ring
end MathPhys.GenCplSt.ChL

/-! #### `generated_dynamics_cpl_stat` (from `Continuum/GeneratedCoupledDynamicsStat.lean`) -/
namespace MathPhys.GenCplDynS.ChL
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal GenReadout GenNorms
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}
variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
set_option maxHeartbeats 8000000 in
/-- **`thm:generated-dynamics` with back-reacting spinors, including stationarity**: the statement
of `MathPhys.GenCplDyn.ChL.generated_dynamics_ext_cplL` (smooth sources, Clifford-unitary forms, back-reacting
Dirac data `GenDStress.CoupledDirac`) for `κ ≠ 0`, with in addition the stationarity clause
`eq:generated-stationarity`: for every `J` with `Jτ ≤ t₁` and every nodal variation
`V = (v_j, v̇_j)` with fixed collar the derivative of the **complete** composite action
`S^{cmp} = (L1SM + L1D) ∘ R` (`GenCplSt.ScmpC`, nodal slopes `G_N(U^j)`) along `V` exists and
`|D S^{cmp}[V]| ≤ C_st(τ + δ + ν)‖V‖_{0,τ}`. -/
theorem generated_dynamics_cpl_statL (hS : GenChL.SMSmoothL SM) (hU : UnitaryForms SM bG bV bS bS')
    (hC : GenDStress.CoupledDirac SM) (hκ0 : SM.κ ≠ 0) {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K₀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∀ δK : ℝ, 0 < δK → Metric.cthickening δK K₀ ⊆ K →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0, ∃ τstar > 0,
        ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → energyQ (s + p + 8) U₀ 0 ≤ R₀ ^ 2 →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ t₁ ≤ T ∧
            (∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0) ∧
            (∀ b y, stC κ SM z b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
            ∀ {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) {nD : ℕ}
              (eD : S × S' →L[ℝ] (Fin nD → ℝ)),
            ∃ C ≥ 0, ∃ Cz ≥ 0, ∃ Cst ≥ 0, ∃ η > 0,
              ∃ K2 : Set (J2I 3 × Fin (dimS m V S S') → ℝ),
              IsCompact K2 ∧
              (∀ w ∈ K2, headJ (m := m) (V := V) (S := S) (S' := S') κ w ∈ chartJ2 m V S S') ∧
              ∀ (N : ℕ) (τ : ℝ), 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar →
              τ ≤ τstar → ∀ (a₀ : GS 3 (dimS m V S S') N) (δ : ℝ), ‖a₀‖ ≤ R₀ → 0 ≤ δ →
              (∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 4) k *
                (cf (s + p + 8) a₀ b k - coef (U₀ b) 0 k) ^ 2 ≤ δ ^ 2) →
              τ + δ + 1 / ((N : ℝ) + 1) ^ p ≤ η →
              ∃ Ud : ℕ → GS 3 (dimS m V S S') N, Ud 0 = a₀ ∧
                (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
                  Ud (j + 1) = Ud j + τ • GN A F (s + p + 8)
                    (SpectralGalerkin.mid (Ud j) (Ud (j + 1))))) ∧
                (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ → ∀ θ ∈ Icc (0 : ℝ) 1,
                  ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 2) k *
                    (cf (s + p + 8) (SpectralGalerkin.hermite τ (Ud j) (Ud (j + 1))
                      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                      coef (stC κ SM z b) (j * τ + θ * τ) k) ^ 2 ≤
                    (Cz * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
                (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ → ∀ θ ∈ Icc (0 : ℝ) 1,
                  ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 2) k *
                    (cf (s + p + 8) (SpectralGalerkin.hermiteD τ (Ud j) (Ud (j + 1))
                      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                      coef (pd (stC κ SM z b) 0) (j * τ + θ * τ) k) ^ 2 ≤
                    (Cz * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
                (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ →
                  (∀ y : ST 3, y 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
                    (fun w => j2c (recW τ (j * τ) (Ud j) (Ud (j + 1)) (GN A F (s + p + 8) (Ud j))
                      (GN A F (s + p + 8) (Ud (j + 1))) (s + p + 8)) w y) ∈ K2) ∧
                  (∀ y ∈ openSlab (j * τ) ((j + 1) * τ), HeadChart κ (fun c =>
                    recW τ (j * τ) (Ud j) (Ud (j + 1)) (GN A F (s + p + 8) (Ud j))
                      (GN A F (s + p + 8) (Ud (j + 1))) (s + p + 8) c y)) ∧
                  ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
                    ∑ c : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q s (fun x =>
                      riemR (hjF κ (recW τ (j * τ) (Ud j) (Ud (j + 1))
                        (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1)))
                        (s + p + 8)) x) c - riemR (hj2 z x) c) t ≤
                      (C * (τ + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2 ∧
                    ∑ k, Q s (fun x => eB (bosR SM (hjF κ (recW τ (j * τ) (Ud j) (Ud (j + 1))
                      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1)))
                      (s + p + 8)) x)) k) t ≤ (C * (τ + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2 ∧
                    ∑ k, Q (s + 1) (fun x => eD (GenResMaps.dirR SM (hjF κ (recW τ (j * τ)
                      (Ud j) (Ud (j + 1)) (GN A F (s + p + 8) (Ud j))
                      (GN A F (s + p + 8) (Ud (j + 1))) (s + p + 8)) x)) k) t ≤
                      (C * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
                ∀ J : ℕ, (J : ℝ) * τ ≤ t₁ → ∀ v w : ℕ → GS 3 (dimS m V S S') N,
                  v 0 = 0 → w 0 = 0 → v J = 0 → w J = 0 →
                  ∃ D : ℝ, HasDerivAt (fun ε : ℝ => GenCplSt.ScmpC κ SM hC.toDiracPairing.P
                      (s + p + 8) τ J (fun j => Ud j + ε • v j)
                      (fun j => GN A F (s + p + 8) (Ud j) + ε • w j)) D 0 ∧
                    |D| ≤ Cst * (τ + δ + 1 / ((N : ℝ) + 1) ^ p) *
                      GenStat.vnorm (s + p + 8) τ J v w := by
  obtain ⟨κ, hκ, h⟩ := MathPhys.GenCplDyn.ChL.generated_dynamics_ext_cplL (bG := bG) (bV := bV) (bS := bS)
    (bS' := bS') hS hU hC hs hp
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK, h2⟩ := h K₀ K hK hKc δK hδK hKδ
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT, R, hR, cstar, hc, τs, hτs, h3⟩ := h2 R₀ hR₀
  refine ⟨T, hT, R, hR, cstar, hc, τs, hτs, fun U₀ hCD hU₀ hUp hE hK₀ => ?_⟩
  obtain ⟨z, t₁, ht₁, ht₁T, hphys, hinit, h4⟩ := h3 U₀ hCD hU₀ hUp hE hK₀
  refine ⟨z, t₁, ht₁, ht₁T, hphys, hinit, fun {nB} eB {nD} eD => ?_⟩
  -- fixed coordinates of the residual spaces
  set bB := Module.finBasis ℝ (BosP m V) with hbB
  set eB0 : BosP m V →L[ℝ] (Fin (Module.finrank ℝ (BosP m V)) → ℝ) :=
    LinearMap.toContinuousLinearMap bB.equivFun.toLinearMap with heB0def
  set eBs0 : (Fin (Module.finrank ℝ (BosP m V)) → ℝ) →L[ℝ] BosP m V :=
    LinearMap.toContinuousLinearMap bB.equivFun.symm.toLinearMap with heBs0def
  have heB0 : ∀ r, eBs0 (eB0 r) = r := fun r => by
    simp only [heB0def, heBs0def, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  set bD := Module.finBasis ℝ (S × S') with hbD
  set eD0 : S × S' →L[ℝ] (Fin (Module.finrank ℝ (S × S')) → ℝ) :=
    LinearMap.toContinuousLinearMap bD.equivFun.toLinearMap with heD0def
  set eDs0 : (Fin (Module.finrank ℝ (S × S')) → ℝ) →L[ℝ] S × S' :=
    LinearMap.toContinuousLinearMap bD.equivFun.symm.toLinearMap with heDs0def
  have heD0 : ∀ r, eDs0 (eD0 r) = r := fun r => by
    simp only [heD0def, heDs0def, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  -- one record controlling the requested and the fixed coordinates
  obtain ⟨C, hC0, Cz, hCz, η, hη, K2, hK2, hK2c, hread⟩ := h4 (catL eB eB0) (catL eD eD0)
  -- the compact sets of head metrics and head values
  set Kg : Set Met := (fun w => (headJ (m := m) (V := V) (S := S) (S' := S') κ w).1.1) '' K2
    with hKg
  set Kh : Set (Met × S × S') := (fun w => ((headJ (m := m) (V := V) (S := S) (S' := S') κ w).1.1,
    (headJ (m := m) (V := V) (S := S) (S' := S') κ w).2.2.2.1.1,
    (headJ (m := m) (V := V) (S := S) (S' := S') κ w).2.2.2.2.1)) '' K2 with hKh
  have hHc := (contDiff_headJ (m := m) (V := V) (S := S) (S' := S') κ).continuous
  have hKgc : IsCompact Kg := hK2.image ((continuous_fst.comp continuous_fst).comp hHc)
  have hKhc : IsCompact Kh := by
    have c1 : Continuous fun w => (headJ (m := m) (V := V) (S := S) (S' := S') κ w).1.1 :=
      (continuous_fst.comp continuous_fst).comp hHc
    have c2 : Continuous fun w => (headJ (m := m) (V := V) (S := S) (S' := S') κ w).2.2.2.1.1 :=
      (continuous_fst.comp (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp
        continuous_snd)))).comp hHc
    have c3 : Continuous fun w => (headJ (m := m) (V := V) (S := S) (S' := S') κ w).2.2.2.2.1 :=
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp
        continuous_snd)))).comp hHc
    exact hK2.image (c1.prodMk (c2.prodMk c3))
  have hKgd : ∀ g ∈ Kg, (Matrix.of g).det ≠ 0 := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hK2c w hw).1
  have hKhch : ∀ h ∈ Kh, GenDFJ.ChartM h.1 := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨(hK2c w hw).1, (hK2c w hw).2, fun μ ν => symL_symm _ μ ν⟩
  obtain ⟨M1, hM10, hM1⟩ := GenStat.exists_bulk_bound κ SM eBs0 hKgc hKgd
  obtain ⟨M2, hM20, hM2⟩ := GenCplCD.exists_dirJ_bound hC.toDiracPairing (Lg κ) (Lψ κ) (Lψb κ)
    eDs0 hKhc hKhch
  set M := max M1 M2 with hMdef
  have hM0 : 0 ≤ M := le_max_of_le_left hM10
  have hMb : ∀ g ∈ Kg, ∀ (c : Fin (Module.finrank ℝ (BosP m V)) → ℝ)
      (y : Fin (dimS m V S S') → ℝ),
      |GenCellBulk.bulkJ SM g (eBs0 c) (Lg κ y) (LA κ y) (LH κ y)| ≤ M * ‖c‖ * ‖y‖ :=
    fun g hg c y => (hM1 g hg c y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (norm_nonneg _))
  have hMd : ∀ h ∈ Kh, ∀ (c : Fin (Module.finrank ℝ (S × S')) → ℝ)
      (y : Fin (dimS m V S S') → ℝ),
      |GenCplCV.dirJ hC.toDiracPairing h.1 (Lg κ y) h.2.1 h.2.2 (eDs0 c) (Lψ κ y) (Lψb κ y)| ≤
        M * ‖c‖ * ‖y‖ :=
    fun h hh c y => (hM2 h hh c y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) (norm_nonneg _))
  refine ⟨C, hC0, Cz, hCz, M * C * (2 + τs) * Real.sqrt (8 * T), by positivity, η, hη, K2, hK2,
    hK2c, fun N τ hτ hcfl hττ a₀ δ ha₀ hδ hdata hsmall => ?_⟩
  obtain ⟨Ud, hUd0, hUdrec, hherm, hhermD, hcells⟩ :=
    hread N τ hτ hcfl hττ a₀ δ ha₀ hδ hdata hsmall
  set ν : ℝ := 1 / ((N : ℝ) + 1) ^ p with hν
  have hν0 : 0 ≤ ν := by positivity
  refine ⟨Ud, hUd0, hUdrec, hherm, hhermD, fun j hj => ?_, fun J hJ v w hv0 hw0 hvJ hwJ => ?_⟩
  · -- the readouts in the requested coordinates
    obtain ⟨h1, h2, h3⟩ := hcells j hj
    refine ⟨h1, h2, fun t ht => ?_⟩
    obtain ⟨hr, hb, hd⟩ := h3 t ht
    exact ⟨hr, (sum_Q_cat_le eB eB0 _ s t).1.trans hb, (sum_Q_cat_le eD eD0 _ (s + 1) t).1.trans hd⟩
  -- stationarity on `[0, Jτ]`
  have hjJ : ∀ j < J, ((j : ℝ) + 1) * τ ≤ t₁ := fun j hj => by
    have : ((j : ℝ) + 1) ≤ J := by exact_mod_cast hj
    nlinarith
  have hc' : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      HeadChart κ (fun c => GenRecNodes.recF (s + p + 8) τ Ud
        (fun i => GN A F (s + p + 8) (Ud i)) j c x) := fun j hj x hx =>
    headChart_of_mem κ (hK2c _ ((hcells j (hjJ j hj)).1 x hx))
  have hKg' : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      Lg κ (fun c => GenRecNodes.recF (s + p + 8) τ Ud
        (fun i => GN A F (s + p + 8) (Ud i)) j c x) ∈ Kg := fun j hj x hx =>
    ⟨_, (hcells j (hjJ j hj)).1 x hx, rfl⟩
  have hKh' : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      (Lg κ (fun c => GenRecNodes.recF (s + p + 8) τ Ud (fun i => GN A F (s + p + 8) (Ud i)) j c x),
        Lψ κ (fun c => GenRecNodes.recF (s + p + 8) τ Ud (fun i => GN A F (s + p + 8) (Ud i)) j c x),
        Lψb κ (fun c => GenRecNodes.recF (s + p + 8) τ Ud
          (fun i => GN A F (s + p + 8) (Ud i)) j c x)) ∈ Kh := fun j hj x hx =>
    ⟨_, (hcells j (hjJ j hj)).1 x hx, rfl⟩
  have hB : ∀ j < J, ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ k, Q s (fun x => eB0 (bosR SM (hjF κ (GenRecNodes.recF (s + p + 8) τ Ud
        (fun i => GN A F (s + p + 8) (Ud i)) j) x)) k) t ≤ (C * (τ + δ + ν)) ^ 2 :=
    fun j hj t ht => (sum_Q_cat_le eB eB0 _ s t).2.trans ((hcells j (hjJ j hj)).2.2 t ht).2.1
  have hBD : ∀ j < J, ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ k, Q (s + 1) (fun x => eD0 (GenResMaps.dirR SM (hjF κ (GenRecNodes.recF (s + p + 8) τ Ud
        (fun i => GN A F (s + p + 8) (Ud i)) j) x)) k) t ≤ (C * (τ ^ 2 + δ + ν)) ^ 2 :=
    fun j hj t ht => (sum_Q_cat_le eD eD0 _ (s + 1) t).2.trans
      ((hcells j (hjJ j hj)).2.2 t ht).2.2
  obtain ⟨D, hD, hDb⟩ := MathPhys.GenCplSt.ChL.stationarity_of_cells_cplL κ SM hS hC hκ0 hτ hc' eB0 eBs0 heB0
    eD0 eDs0 heD0 hM0 hMb hMd hKg' hKh' (by positivity) (by positivity) hB hBD v w hv0 hw0 hvJ hwJ
  refine ⟨D, hD, hDb.trans ?_⟩
  have hJT : (J : ℝ) * τ ≤ T := hJ.trans ht₁T
  have hsq : Real.sqrt (8 * ((J : ℝ) * τ)) ≤ Real.sqrt (8 * T) := Real.sqrt_le_sqrt (by linarith)
  have hvn : 0 ≤ GenStat.vnorm (s + p + 8) τ J v w := Real.sqrt_nonneg _
  have hτ2 : τ ^ 2 ≤ τs * τ := by nlinarith
  have hsumB : C * (τ + δ + ν) + C * (τ ^ 2 + δ + ν) ≤ C * (2 + τs) * (τ + δ + ν) := by
    have h1 : 0 ≤ τs * (δ + ν) := by positivity
    have h2 : τ + δ + ν + (τ ^ 2 + δ + ν) ≤ (2 + τs) * (τ + δ + ν) := by nlinarith
    nlinarith
  have hX : 0 ≤ Real.sqrt (8 * T) := Real.sqrt_nonneg _
  calc M * (C * (τ + δ + ν) + C * (τ ^ 2 + δ + ν)) * Real.sqrt (8 * ((J : ℝ) * τ)) *
        GenStat.vnorm (s + p + 8) τ J v w
      ≤ M * (C * (2 + τs) * (τ + δ + ν)) * Real.sqrt (8 * T) *
          GenStat.vnorm (s + p + 8) τ J v w := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hsumB hM0) hsq
          (Real.sqrt_nonneg _) (by positivity)) hvn
    _ = M * C * (2 + τs) * Real.sqrt (8 * T) * (τ + δ + ν) *
          GenStat.vnorm (s + p + 8) τ J v w := by ring
end MathPhys.GenCplDynS.ChL

/-! #### `generated_dynamics_norms_cpl_stat` (from `Continuum/GeneratedCoupledDynamicsStat.lean`) -/
namespace MathPhys.GenCplDynS.ChL
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal GenReadout GenNorms
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}
variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
set_option maxHeartbeats 8000000 in
/-- **`thm:generated-dynamics` with back-reacting spinors in the manuscript's norms**: the
statement of `GenNorms.generated_dynamics_norms` (`C_t`/`L^∞_t` slice norms, data rate
`‖U_{0,N} - U₀‖_{H^{s+4}} ≤ C₀N^{-p}`, rates `eq:generated-first`, `eq:generated-bosonic`,
`eq:generated-Dirac`) for back-reacting Dirac data (`GenDStress.CoupledDirac`), with the
stationarity clause for the complete composite action `GenCplSt.ScmpC` (`κ ≠ 0`):
`|D S^{cmp}[V]| ≤ C(N^{-p} + τ)‖V‖_{0,τ}`. -/
theorem generated_dynamics_norms_cpl_statL (hS : GenChL.SMSmoothL SM) (hU : UnitaryForms SM bG bV bS bS')
    (hC : GenDStress.CoupledDirac SM) (hκ0 : SM.κ ≠ 0) {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K₀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∀ δK : ℝ, 0 < δK → Metric.cthickening δK K₀ ⊆ K →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0,
        ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → sliceH (s + p + 8) U₀ 0 ≤ R₀ →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ t₁ ≤ T ∧
            (∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0) ∧
            (∀ b y, stC κ SM z b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
            ∀ {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) {nD : ℕ}
              (eD : S × S' →L[ℝ] (Fin nD → ℝ)) (C₀ : ℝ), 0 ≤ C₀ →
            ∃ C ≥ 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ τ₀ > 0,
              ∀ (N : ℕ) (τ : ℝ), N₀ ≤ N → 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τ₀ →
              ∀ a₀ : GS 3 (dimS m V S S') N,
                sliceH (s + p + 8) (fld (s + p + 8) a₀) 0 ≤ R₀ →
                sliceH (s + 4) (fun b x => fld (s + p + 8) a₀ b x - U₀ b x) 0 ≤
                  C₀ * ((N : ℝ) ^ p)⁻¹ →
              ∃ Ud : ℕ → GS 3 (dimS m V S S') N, Ud 0 = a₀ ∧
                (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
                  Ud (j + 1) = Ud j + τ • GN A F (s + p + 8)
                    (SpectralGalerkin.mid (Ud j) (Ud (j + 1))))) ∧
                ∀ J : ℕ, 1 ≤ J → (J : ℝ) * τ ≤ t₁ →
                  supNorm (stErr SM κ (s + p + 8) (s + 2) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  supNorm (stErrD SM κ (s + p + 8) (s + 2) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  essNorm (riemErr κ (s + p + 8) s τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ)) ∧
                  essNorm (bosRes SM κ eB (s + p + 8) s τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i))) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ)) ∧
                  supNorm (dirRes SM κ eD (s + p + 8) (s + 1) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i))) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  ∀ v w : ℕ → GS 3 (dimS m V S S') N, v 0 = 0 → w 0 = 0 → v J = 0 → w J = 0 →
                    ∃ D : ℝ, HasDerivAt (fun ε : ℝ => GenCplSt.ScmpC κ SM hC.toDiracPairing.P
                        (s + p + 8) τ J (fun j => Ud j + ε • v j)
                        (fun j => GN A F (s + p + 8) (Ud j) + ε • w j)) D 0 ∧
                      |D| ≤ C * (((N : ℝ) ^ p)⁻¹ + τ) * GenStat.vnorm (s + p + 8) τ J v w := by
  obtain ⟨κ, hκ, h⟩ := MathPhys.GenCplDynS.ChL.generated_dynamics_cpl_statL (bG := bG) (bV := bV) (bS := bS) (bS' := bS')
    hS hU hC hκ0 hs hp
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK, h2⟩ := h K₀ K hK hKc δK hδK hKδ
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT, R, hR, cstar, hc, τs, hτs, h3⟩ := h2 R₀ hR₀
  refine ⟨T, hT, R, hR, cstar, hc, fun U₀ hCD hU₀ hUp hE hK₀ => ?_⟩
  have hE' : energyQ (s + p + 8) U₀ 0 ≤ R₀ ^ 2 := (sliceH_le_iff hR₀).1 hE
  obtain ⟨z, t₁, ht₁, ht₁T, hphys, hinit, h4⟩ := h3 U₀ hCD hU₀ hUp hE' hK₀
  refine ⟨z, t₁, ht₁, ht₁T, hphys, hinit, fun {nB} eB {nD} eD C₀ hC₀ => ?_⟩
  obtain ⟨C₁, hC₁0, Cz, hCz, Cst, hCst, η, hη, K2, -, hK2c, h5⟩ := h4 eB eD
  set Cm : ℝ := max (max C₁ Cz) Cst with hCm
  have hCm0 : 0 ≤ Cm := le_max_of_le_right hCst
  have hC₁m : C₁ ≤ Cm := (le_max_left _ _).trans (le_max_left _ _)
  have hCzm : Cz ≤ Cm := (le_max_right _ _).trans (le_max_left _ _)
  have hCstm : Cst ≤ Cm := le_max_right _ _
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 * (C₀ + 1) / η)
  set N₀ : ℕ := k₀ + 1 with hN₀
  have hN₀1 : 1 ≤ N₀ := Nat.le_add_left 1 k₀
  refine ⟨Cm * (C₀ + 1), by positivity, N₀, hN₀1, min τs (η / 2), lt_min hτs (by positivity),
    fun N τ hN hτ hcfl hττ a₀ ha₀ hdist => ?_⟩
  have hN1 : 1 ≤ N := hN₀1.trans hN
  set νp : ℝ := ((N : ℝ) ^ p)⁻¹ with hνp
  have hνp0 : 0 ≤ νp := by positivity
  set ν : ℝ := 1 / ((N : ℝ) + 1) ^ p with hν
  have hν0 : 0 ≤ ν := by positivity
  have hννp : ν ≤ νp := inv_succ_pow_le hN1
  set δ : ℝ := C₀ * νp with hδ
  have hδ0 : 0 ≤ δ := by positivity
  -- the smallness of the data distance
  have hsm : τ + δ + ν ≤ η := by
    have h1 : νp ≤ 1 / (N₀ : ℝ) := npow_inv_le_inv hp hN₀1 hN
    have hN₀pos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀1
    have h2 : (C₀ + 1) * (1 / (N₀ : ℝ)) ≤ η / 2 := by
      have hk : 2 * (C₀ + 1) / η < N₀ := by
        have : (k₀ : ℝ) < N₀ := by rw [hN₀]; push_cast; linarith
        linarith
      rw [div_lt_iff₀ hη] at hk
      rw [mul_one_div, div_le_iff₀ hN₀pos]
      nlinarith
    have h3 : (C₀ + 1) * νp ≤ η / 2 := (mul_le_mul_of_nonneg_left h1 (by linarith)).trans h2
    have h4 : τ ≤ η / 2 := hττ.trans (min_le_right _ _)
    nlinarith
  -- the finite data in the form of the readout package
  have ha₀' : ‖a₀‖ ≤ R₀ := by rwa [sliceH_fld] at ha₀
  have hdata : ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 4) k *
      (cf (s + p + 8) a₀ b k - coef (U₀ b) 0 k) ^ 2 ≤ δ ^ 2 := by
    intro S₀
    have hf := (sliceH_le_iff_fourier (r := s + 4)
      (f := fun b x => fld (s + p + 8) a₀ b x - U₀ b x)
      (fun b => (contDiff_fld _ a₀ b).sub (hU₀ b))
      (fun b k x => by simp only [isSPeriodic_fld _ a₀ b k x, hUp b k x]) hδ0).1 hdist S₀
    refine le_of_eq_of_le ?_ hf
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
    rw [coef_sub (contDiff_fld _ a₀ b).continuous (hU₀ b).continuous, KatoRates.coef_fld]
  obtain ⟨Ud, hUd0, hrec, hstate, hderiv, hcells, hstat⟩ := h5 N τ hτ hcfl
    (hττ.trans (min_le_left _ _)) a₀ δ ha₀' hδ0 hdata hsm
  refine ⟨Ud, hUd0, hrec, fun J hJ hJt => ?_⟩
  -- the rate algebra
  have hr2 : τ ^ 2 + δ + ν ≤ (C₀ + 1) * (νp + τ ^ 2) := rate_le hC₀ (sq_nonneg τ) hννp hνp0
  have hr1 : τ + δ + ν ≤ (C₀ + 1) * (νp + τ) := rate_le hC₀ hτ.le hννp hνp0
  have hB2 : ∀ C' : ℝ, 0 ≤ C' → C' ≤ Cm → C' * (τ ^ 2 + δ + ν) ≤ Cm * (C₀ + 1) * (νp + τ ^ 2) :=
    fun C' hC' hCC => by
      calc C' * (τ ^ 2 + δ + ν) ≤ Cm * ((C₀ + 1) * (νp + τ ^ 2)) :=
            mul_le_mul hCC hr2 (by positivity) hCm0
        _ = _ := by ring
  have hB1 : ∀ C' : ℝ, 0 ≤ C' → C' ≤ Cm → C' * (τ + δ + ν) ≤ Cm * (C₀ + 1) * (νp + τ) :=
    fun C' hC' hCC => by
      calc C' * (τ + δ + ν) ≤ Cm * ((C₀ + 1) * (νp + τ)) :=
            mul_le_mul hCC hr1 (by positivity) hCm0
        _ = _ := by ring
  have hpos2 : 0 ≤ Cm * (C₀ + 1) * (νp + τ ^ 2) := by positivity
  have hpos1 : 0 ≤ Cm * (C₀ + 1) * (νp + τ) := by positivity
  -- the cell of a time of `[0, Jτ]`
  have hcell : ∀ t ∈ Icc (0 : ℝ) (J * τ), cellIdx τ t < J ∧
      t ∈ Icc ((cellIdx τ t : ℝ) * τ) (((cellIdx τ t : ℝ) + 1) * τ) ∧
      ((cellIdx τ t : ℝ) + 1) * τ ≤ t₁ := by
    intro t ht
    have hlt := cellIdx_lt hτ hJ ht.2
    refine ⟨hlt, cellIdx_mem hτ ht.1, ?_⟩
    have : ((cellIdx τ t : ℝ) + 1) ≤ J := by exact_mod_cast hlt
    nlinarith
  have hcellO : ∀ t ∈ Ioo (0 : ℝ) (J * τ), t ∉ Set.range (fun j : ℕ => (j : ℝ) * τ) →
      cellIdx τ t < J ∧
      t ∈ Ioo ((cellIdx τ t : ℝ) * τ) (((cellIdx τ t : ℝ) + 1) * τ) ∧
      ((cellIdx τ t : ℝ) + 1) * τ ≤ t₁ := by
    intro t ht hn
    obtain ⟨h1, -, h3⟩ := hcell t (Ioo_subset_Icc_self ht)
    exact ⟨h1, mem_open_cell hτ ht.1 hn, h3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `C_tH^{s+2}` state rate
    rw [supNorm_le_iff hpos2]
    intro t ht
    obtain ⟨-, hmem, hjt⟩ := hcell t ht
    exact (sliceH_recW_le hτ (contDiff_stC κ SM z) (isSPeriodic_stC κ SM z) (by positivity)
      (hstate _ hjt) hmem).trans (hB2 Cz hCz hCzm)
  · -- `C_tH^{s+2}` time-derivative rate
    rw [supNorm_le_iff hpos2]
    intro t ht
    obtain ⟨-, hmem, hjt⟩ := hcell t ht
    exact (sliceH_recWD_le hτ (contDiff_stC κ SM z) (isSPeriodic_stC κ SM z) (by positivity)
      (hderiv _ hjt) hmem).trans (hB2 Cz hCz hCzm)
  · -- `L^∞_tH^s` Riemann rate
    refine essNorm_le_of_off_countable (nodes_countable τ) fun t ht hn => ?_
    obtain ⟨-, hmem, hjt⟩ := hcellO t ht hn
    have hb := (((hcells _ hjt).2.2 t hmem).1)
    refine ((sliceHι_le_iff (by positivity)).2 hb).trans (hB1 C₁ hC₁0 hC₁m)
  · -- `L^∞_tH^s` bosonic residual
    refine essNorm_le_of_off_countable (nodes_countable τ) fun t ht hn => ?_
    obtain ⟨-, hmem, hjt⟩ := hcellO t ht hn
    have hb := (((hcells _ hjt).2.2 t hmem).2.1)
    exact ((sliceH_le_iff (by positivity)).2 hb).trans (hB1 C₁ hC₁0 hC₁m)
  · -- `C_tH^{s+1}` Dirac residual: open-cell bound and continuity up to the nodes
    rw [supNorm_le_iff hpos2]
    intro t ht
    obtain ⟨-, hmem, hjt⟩ := hcell t ht
    set j := cellIdx τ t with hjdef
    have hcont := continuousOn_dirQ κ (SM := SM) eD
      (fun b => GenRecNodes.contDiff_recF (s + p + 8) τ Ud (fun i => GN A F (s + p + 8) (Ud i)) j b)
      (fun b => GenRecNodes.isSPeriodic_recF (s + p + 8) τ Ud (fun i => GN A F (s + p + 8) (Ud i))
        j b)
      (by nlinarith : (j : ℝ) * τ ≤ ((j : ℝ) + 1) * τ)
      (fun y hy => hK2c _ ((hcells j hjt).1 y hy)) (s + 1)
    have hopen : ∀ t' ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
        ∑ k, Q (s + 1) (fun x => eD (dirR SM (hjF κ (GenRecNodes.recF (s + p + 8) τ Ud
          (fun i => GN A F (s + p + 8) (Ud i)) j) x)) k) t' ≤
          (C₁ * (τ ^ 2 + δ + ν)) ^ 2 := fun t' ht' => ((hcells j hjt).2.2 t' ht').2.2
    have hclosed := le_on_Icc_of_Ioo (by nlinarith) hcont hopen t hmem
    exact ((sliceH_le_iff (by positivity)).2 hclosed).trans (hB2 C₁ hC₁0 hC₁m)
  · -- stationarity of the complete composite action
    intro v w hv0 hw0 hvJ hwJ
    obtain ⟨D, hD, hDb⟩ := hstat J hJt v w hv0 hw0 hvJ hwJ
    exact ⟨D, hD, hDb.trans (mul_le_mul_of_nonneg_right (hB1 Cst hCst hCstm) (Real.sqrt_nonneg _))⟩
end MathPhys.GenCplDynS.ChL

/-! #### `generated_nonempty_norms_cpl_stat` (from `Continuum/GeneratedCoupledDynamicsStat.lean`) -/
namespace MathPhys.GenCplDynS.ChL
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal GenReadout GenNorms
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}
variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
set_option maxHeartbeats 8000000 in
/-- **`cor:generated-nonempty` with back-reacting spinors in the manuscript's norms**: the statement
of `GenNorms.generated_nonempty_norms` (finite data `U_{0,N} = P_N U₀`, `eq:generated-nonempty`,
summable dyadic budget) for back-reacting Dirac data (`GenDStress.CoupledDirac`), **with** the
stationarity clause for the complete composite action `GenCplSt.ScmpC` (`κ ≠ 0`). -/
theorem generated_nonempty_norms_cpl_statL (hS : GenChL.SMSmoothL SM) (hU : UnitaryForms SM bG bV bS bS')
    (hC : GenDStress.CoupledDirac SM) (hκ0 : SM.κ ≠ 0) {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K₀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∀ δK : ℝ, 0 < δK → Metric.cthickening δK K₀ ⊆ K →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0,
        (∀ τd : ℕ → ℝ, (∀ n, 0 ≤ τd n ∧ τd n * ((2 : ℝ) ^ n + 1) ≤ cstar) →
          Summable (fun n : ℕ => 1 / ((2 : ℝ) ^ n + 1) ^ p + τd n)) ∧
        ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → sliceH (s + p + 8) U₀ 0 ≤ R₀ →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ t₁ ≤ T ∧
            (∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0) ∧
            (∀ b y, stC κ SM z b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
            ∀ {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) {nD : ℕ}
              (eD : S × S' →L[ℝ] (Fin nD → ℝ)),
            ∃ C ≥ 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ τ₀ > 0,
              ∀ (N : ℕ) (τ : ℝ), N₀ ≤ N → 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τ₀ →
              ∃ Ud : ℕ → GS 3 (dimS m V S S') N, Ud 0 = P0 (s + p + 8) N U₀ ∧
                (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
                  Ud (j + 1) = Ud j + τ • GN A F (s + p + 8)
                    (SpectralGalerkin.mid (Ud j) (Ud (j + 1))))) ∧
                ∀ J : ℕ, 1 ≤ J → (J : ℝ) * τ ≤ t₁ →
                  supNorm (stErr SM κ (s + p + 8) (s + 2) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  supNorm (stErrD SM κ (s + p + 8) (s + 2) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  essNorm (riemErr κ (s + p + 8) s τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ)) ∧
                  essNorm (bosRes SM κ eB (s + p + 8) s τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i))) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ)) ∧
                  supNorm (dirRes SM κ eD (s + p + 8) (s + 1) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i))) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  ∀ v w : ℕ → GS 3 (dimS m V S S') N, v 0 = 0 → w 0 = 0 → v J = 0 → w J = 0 →
                    ∃ D : ℝ, HasDerivAt (fun ε : ℝ => GenCplSt.ScmpC κ SM hC.toDiracPairing.P
                        (s + p + 8) τ J (fun j => Ud j + ε • v j)
                        (fun j => GN A F (s + p + 8) (Ud j) + ε • w j)) D 0 ∧
                      |D| ≤ C * (((N : ℝ) ^ p)⁻¹ + τ) * GenStat.vnorm (s + p + 8) τ J v w := by
  obtain ⟨κ, hκ, h⟩ := MathPhys.GenCplDynS.ChL.generated_dynamics_norms_cpl_statL (bG := bG) (bV := bV) (bS := bS)
    (bS' := bS') hS hU hC hκ0 hs hp
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK, h2⟩ := h K₀ K hK hKc δK hδK hKδ
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT, R, hR, cstar, hc, h3⟩ := h2 R₀ hR₀
  refine ⟨T, hT, R, hR, cstar, hc, fun τd hτd => GenReadout.summable_dyadic hp τd hτd,
    fun U₀ hCD hU₀ hUp hE hK₀ => ?_⟩
  obtain ⟨z, t₁, ht₁, ht₁T, hphys, hinit, h4⟩ := h3 U₀ hCD hU₀ hUp hE hK₀
  refine ⟨z, t₁, ht₁, ht₁T, hphys, hinit, fun {nB} eB {nD} eD => ?_⟩
  obtain ⟨C, hC, N₀, hN₀, τ₀, hτ₀, h5⟩ := h4 eB eD R₀ hR₀
  refine ⟨C, hC, N₀, hN₀, τ₀, hτ₀, fun N τ hN hτ hcfl hττ => ?_⟩
  obtain ⟨hsup, hrate⟩ := initial_rate_P0 (s := s) (p := p) hU₀ hUp
  have hN1 : 1 ≤ N := hN₀.trans hN
  have hd : sliceH (s + 4) (fun b x => fld (s + p + 8) (P0 (d := 3) (s + p + 8) N U₀) b x -
      U₀ b x) 0 ≤ R₀ * ((N : ℝ) ^ p)⁻¹ :=
    (hrate N hN1).trans (mul_le_mul_of_nonneg_right hE (by positivity))
  exact h5 N τ hN hτ hcfl hττ (P0 (s + p + 8) N U₀) ((hsup N).trans hE) hd
end MathPhys.GenCplDynS.ChL
