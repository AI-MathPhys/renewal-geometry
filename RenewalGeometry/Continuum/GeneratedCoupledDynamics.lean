/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDynamicsNormForm
import RenewalGeometry.Continuum.GeneratedCoupledIdentificationFinal

/-!
# `thm:generated-dynamics` and `cor:generated-nonempty` with back-reacting spinors

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`,
`cor:generated-nonempty` (`Σ = 𝕋³`), for the complete Einstein–Standard-Model system with Dirac
back-reaction (`GenDStress.CoupledDirac`).  The decoupled versions (`GenNorms.generated_dynamics_ext`,
`GenNorms.generated_dynamics_norms`, `GenNorms.generated_nonempty_norms`) are kept unchanged.

The proofs re-run the decoupled assembly with the coupled ingredients:
`GenCplKato.modified_kato_realization_cpl` (realized modified system without the decoupling
hypothesis) and `GenCplId.core_identification_cpl` (identification of the Kato solution with a
physical tuple through the coupled constraint system, `GenCplCon.coupled_constraints_vanish`), with
the Noether identities discharged by `GenDiracCur.currentNoether_of_variationalDirac` and
`GenDSN.stressConservation_of_coupledDirac`.  The Galerkin record, the Hermite rates and the
readout package (`GenReadout.readouts_of_identified`) do not depend on the decoupling.

* **`generated_dynamics_ext_cpl`**, **`generated_dynamics_norms_cpl`**,
  **`generated_nonempty_norms_cpl`**.

Disclosure: the stationarity clause `eq:generated-stationarity` is **not** included: the composite
action `GenStat.Scmp` is the first-order Einstein–Yang–Mills–Higgs action, and its variation
(`GenStat.stationarity_of_cells`) is controlled by the bosonic residual only when the Dirac stress
vanishes; with back-reaction the composite action must contain the Dirac action and its cell
variation the Dirac residual.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace RenewalGeometry.GenCplDyn

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

section Main

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
`GenCplId.core_identification_cpl` with the Noether identities discharged
(`GenDiracCur.currentNoether_of_variationalDirac`, `GenDSN.stressConservation_of_coupledDirac`),
and the realized modified system is `GenCplKato.modified_kato_realization_cpl`. -/
theorem generated_dynamics_ext_cpl (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
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
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  obtain ⟨AM, FM, hAM, hsymM, hFM, hAMK, hFMK, hτA, hτF⟩ :=
    GenCplKato.modified_kato_realization_cpl hS hU hC κ hκ K hK hKc
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
  obtain ⟨z, t₁', ht₁', hid⟩ := GenCplId.core_identification_cpl hS hU hC hN hT hκ hKc hA hsym hF hAK hFK
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
  obtain ⟨C, hC0, η, hη, K2, hK2, hK2c, hread⟩ := readouts_of_identified κ hS hs hphys hUrV hVt
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

set_option maxHeartbeats 8000000 in
/-- **`thm:generated-dynamics` with back-reacting spinors in the manuscript's norms**: the
statement of `GenNorms.generated_dynamics_norms` (`C_t`/`L^∞_t` slice norms, data rate
`‖U_{0,N} - U₀‖_{H^{s+4}} ≤ C₀N^{-p}`, rates `eq:generated-first`, `eq:generated-bosonic`,
`eq:generated-Dirac`) for back-reacting Dirac data (`GenDStress.CoupledDirac`), without the
stationarity clause (see `generated_dynamics_ext_cpl`); no `κ ≠ 0` hypothesis is needed. -/
theorem generated_dynamics_norms_cpl (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
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
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) := by
  obtain ⟨κ, hκ, h⟩ := generated_dynamics_ext_cpl (bG := bG) (bV := bV) (bS := bS) (bS' := bS')
    hS hU hC hs hp
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK, h2⟩ := h K₀ K hK hKc δK hδK hKδ
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT, R, hR, cstar, hc, τs, hτs, h3⟩ := h2 R₀ hR₀
  refine ⟨T, hT, R, hR, cstar, hc, fun U₀ hCD hU₀ hUp hE hK₀ => ?_⟩
  have hE' : energyQ (s + p + 8) U₀ 0 ≤ R₀ ^ 2 := (sliceH_le_iff hR₀).1 hE
  obtain ⟨z, t₁, ht₁, ht₁T, hphys, hinit, h4⟩ := h3 U₀ hCD hU₀ hUp hE' hK₀
  refine ⟨z, t₁, ht₁, ht₁T, hphys, hinit, fun {nB} eB {nD} eD C₀ hC₀ => ?_⟩
  obtain ⟨C₁, hC₁0, Cz, hCz, η, hη, K2, -, hK2c, h5⟩ := h4 eB eD
  set Cm : ℝ := max C₁ Cz with hCm
  have hCm0 : 0 ≤ Cm := le_max_of_le_left hC₁0
  have hC₁m : C₁ ≤ Cm := le_max_left _ _
  have hCzm : Cz ≤ Cm := le_max_right _ _
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
  obtain ⟨Ud, hUd0, hrec, hstate, hderiv, hcells⟩ := h5 N τ hτ hcfl
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

set_option maxHeartbeats 8000000 in
/-- **`cor:generated-nonempty` with back-reacting spinors in the manuscript's norms**: the statement
of `GenNorms.generated_nonempty_norms` (finite data `U_{0,N} = P_N U₀`, `eq:generated-nonempty`,
summable dyadic budget) for back-reacting Dirac data (`GenDStress.CoupledDirac`), without the
stationarity clause. -/
theorem generated_nonempty_norms_cpl (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
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
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) := by
  obtain ⟨κ, hκ, h⟩ := generated_dynamics_norms_cpl (bG := bG) (bV := bV) (bS := bS) (bS' := bS')
    hS hU hC hs hp
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

end Main

/-! ### Non-vacuity -/

section NonVacuity

open GenCplIdF GenDiracCur in
/-- **The hypotheses of the coupled dynamics theorems hold for back-reacting data with a nonzero
Dirac stress**: the gauge-neutral quaternionic data `GenCplIdF.quatN` (smooth sources, unitary
forms, `CoupledDirac`, nonzero Dirac stress `GenCplIdF.quatN_stress_ne`), so
`generated_nonempty_norms_cpl` applies to them and yields Euclidean coordinates `κ` of the state
space orthonormal for the block form. -/
example : ∃ κ : StateP 1 (MatLie 1) SQ SQ ≃ₗ[ℝ] (Fin (dimS 1 (MatLie 1) SQ SQ) → ℝ),
    ∀ v w, ipP (frob 1) (frob 1) PQ PQ (κ.symm v) (κ.symm w) = ∑ i, v i * w i := by
  obtain ⟨κ, hκ, -⟩ := generated_nonempty_norms_cpl quatN_smooth quatN_unitary quatNCoupled
    (s := 3) (p := 1) le_rfl le_rfl
  exact ⟨κ, hκ⟩

end NonVacuity

end RenewalGeometry.GenCplDyn
