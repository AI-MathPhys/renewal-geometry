/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDynamicsReadouts
import RenewalGeometry.Continuum.GeneratedStationarity
import RenewalGeometry.Continuum.GeneratedDynamicsClosed

/-!
# `thm:generated-dynamics`: the readout package with the time-derivative rate

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`, `eq:generated-first`
(`Σ = 𝕋³`).  `GenReadout.generated_dynamics_closed` exports the state-level Hermite rate
`‖z_{N,τ} - z‖_{H^{s+2}}` but not the rate of the time derivative `‖∂_tz_{N,τ} - ∂_tz‖`.  This file
re-runs the same assembly (same identified physical solution, same record, same readout package)
and exports, in addition, the Fourier-form rate of the time derivative of the Hermite record
(`hermiteD`, the time derivative of the cubic Hermite reconstruction) against the time derivative
of the coordinate state of the exact solution, on every closed cell of `[0, t₁]`.

* **`GenNorms.generated_dynamics_ext`**.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenNorms

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal GenReadout

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}

section Closed

variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

set_option maxHeartbeats 8000000 in
/-- **`thm:generated-dynamics` on the actual-jet system, with the time-derivative rate**
(same statement as `GenReadout.generated_dynamics_closed`, plus the clause
`‖∂_tz_{N,τ} - ∂_tz‖_{H^{s+2}} ≤ C_z(τ² + δ + ν)` on every closed cell, Fourier form).  For variational
theory data (`GenStress.VariationalStress`: Higgs current and potential force, symmetric forms,
vanishing Dirac stress; this gives the hypotheses of `lem:generated-physical-identification`) with
smooth sources, Clifford-unitary forms and `κ ≠ 0`, there are Euclidean coordinates `κ` such that
for every compact chart margin the realized symmetric system `(A, F)` satisfies, for every data
radius `R₀`, with `T`, `R`, `c_*`, `τ_*`: every constrained smooth periodic datum `U₀` with
`‖U₀‖_{H^{s+p+8}} ≤ R₀` and values in `K₀` generates a smooth physical tuple `z` on `[0, t₁]`
(`R_B(z) = R_D(z) = 0`, harmonic gauge, actual-jet state `= U₀` at `t = 0`), and for all
coordinates `e_B`, `e_D` there are `C`, `C_z`, `C_st`, `η > 0` and a compact chart set `K₂` such that for
every cutoff `N`, step `τ` (`τ(N+1) ≤ c_*`, `τ ≤ τ_*`) and finite datum `U_{0,N}` (`‖U_{0,N}‖ ≤ R₀`,
`‖U_{0,N} - U₀‖_{H^{s+4}} ≤ δ`) with `τ + δ + ν ≤ η`, `ν = (N+1)^{-p}`, the implicit-midpoint
record `U^j` exists on `[0, T]`, its cubic-Hermite reconstruction is `C_z(τ² + δ + ν)`-close to
the coordinate state `κ(𝒰(z))` of the exact solution in `H^{s+2}` (Fourier form) on `[0, t₁]`,
its physical reconstruction on every cell `[jτ, (j+1)τ] ⊆ [0, t₁]` has its 2-jets in `K₂`, its metric in the chart and the readout bounds
of `eq:generated-bosonic` / `eq:generated-Dirac`, and **stationarity**: for every `J` with
`Jτ ≤ t₁` and every nodal variation `V = (v_j, v̇_j)` with fixed collar
(`v_0 = v̇_0 = v_J = v̇_J = 0`) the derivative of the composite action
`S^{cmp} = S^{(1)} ∘ R` (`GenStat.Scmp`, nodal slopes `G_N(U^j)`) along `V` exists and
`|D S^{cmp}[V]| ≤ C_st(τ + δ + ν)‖V‖_{0,τ}`. -/
theorem generated_dynamics_ext (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    (hVS : GenStress.VariationalStress SM) (hκ0 : SM.κ ≠ 0) {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
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
                  ∃ D : ℝ, HasDerivAt (fun ε : ℝ => GenStat.Scmp κ SM (s + p + 8) τ J
                      (fun j => Ud j + ε • v j) (fun j => GN A F (s + p + 8) (Ud j) + ε • w j)) D 0 ∧
                    |D| ≤ Cst * (τ + δ + 1 / ((N : ℝ) + 1) ^ p) *
                      GenStat.vnorm (s + p + 8) τ J v w := by
  have hD := decoupled_of_variationalStress hVS
  have hN := GenNoether.currentNoether_of_variational hVS.toVariationalBosonic
  have hT := GenStress.stressNoether_of_variational hVS
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  obtain ⟨AM, FM, hAM, hsymM, hFM, hAMK, hFMK, hτA, hτF⟩ :=
    AJKatoMod.modified_kato_realization hS hU hD κ hκ K hK hKc
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
  obtain ⟨z, t₁', ht₁', hid⟩ := core_identification hS hU hD hN hT hκ hKc hA hsym hF hAK hFK
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
  -- fixed coordinates of the bosonic residual space
  set bB := Module.finBasis ℝ (BosP m V) with hbB
  set eB0 : BosP m V →L[ℝ] (Fin (Module.finrank ℝ (BosP m V)) → ℝ) :=
    LinearMap.toContinuousLinearMap bB.equivFun.toLinearMap with heB0def
  set eBs0 : (Fin (Module.finrank ℝ (BosP m V)) → ℝ) →L[ℝ] BosP m V :=
    LinearMap.toContinuousLinearMap bB.equivFun.symm.toLinearMap with heBs0def
  have heB0 : ∀ r, eBs0 (eB0 r) = r := fun r => by
    simp only [heB0def, heBs0def, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  obtain ⟨C0, hC00, η0, hη0, K20, hK20, hK2c0, hread0⟩ := readouts_of_identified κ hS hs hphys
    hUrV hVt hVtt hCr hτs eB0 eD
  -- the bulk constant
  set Kg : Set Met := (fun w => (headJ (m := m) (V := V) (S := S) (S' := S') κ w).1.1) '' K20
    with hKg
  have hKgc : IsCompact Kg :=
    hK20.image ((continuous_fst.comp continuous_fst).comp (contDiff_headJ κ).continuous)
  have hKgd : ∀ g ∈ Kg, (Matrix.of g).det ≠ 0 := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hK2c0 w hw).1
  obtain ⟨M, hM0, hM⟩ := GenStat.exists_bulk_bound κ SM eBs0 hKgc hKgd
  refine ⟨C, hC0, Cr, hCr, M * C0 * Real.sqrt (8 * Tr), by positivity, min η η0,
    lt_min hη hη0, K2, hK2, hK2c, fun N τ hτ hcfl hττ a₀ δ ha₀ hδ hdata hsmall => ?_⟩
  obtain ⟨Ud, hUd0, hUdrec, -, hherm⟩ := hrec N τ hτ hcfl hττ a₀ δ ha₀ hδ hdata
  set ν : ℝ := 1 / ((N : ℝ) + 1) ^ p with hν
  have hν0 : 0 ≤ ν := by positivity
  refine ⟨Ud, hUd0, hUdrec, fun j hj θ hθ S₀ => ?_, fun j hj θ hθ S₀ => ?_, fun j hj => ?_,
    fun J hJ v w hv0 hw0 hvJ hwJ => ?_⟩
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
    exact hread τ hτ hττ δ ν hδ hν0 (hsmall.trans (min_le_left _ _)) j (Ud j) (Ud (j + 1))
      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) hj
      (fun θ hθ S₀ => (hherm j hjr θ hθ S₀).1) (fun θ hθ S₀ => (hherm j hjr θ hθ S₀).2.1)
      (fun θ hθ S₀ => (hherm j hjr θ hθ S₀).2.2)
  -- stationarity on `[0, Jτ]`
  have hjJ : ∀ j < J, ((j : ℝ) + 1) * τ ≤ t₁ := fun j hj => by
    have : ((j : ℝ) + 1) ≤ J := by exact_mod_cast hj
    nlinarith
  have hR0 := fun j (hj : j < J) => hread0 τ hτ hττ δ ν hδ hν0 (hsmall.trans (min_le_right _ _)) j
    (Ud j) (Ud (j + 1)) (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) (hjJ j hj)
    (fun θ hθ S₀ => (hherm j ((hjJ j hj).trans ht₁r) θ hθ S₀).1)
    (fun θ hθ S₀ => (hherm j ((hjJ j hj).trans ht₁r) θ hθ S₀).2.1)
    (fun θ hθ S₀ => (hherm j ((hjJ j hj).trans ht₁r) θ hθ S₀).2.2)
  have hc : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      HeadChart κ (fun c => GenRecNodes.recF (s + p + 8) τ Ud (fun i => GN A F (s + p + 8) (Ud i))
        j c x) := fun j hj x hx => headChart_of_mem κ (hK2c0 _ ((hR0 j hj).1 x hx))
  have hKgm : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      Lg κ (fun c => GenRecNodes.recF (s + p + 8) τ Ud (fun i => GN A F (s + p + 8) (Ud i))
        j c x) ∈ Kg := fun j hj x hx => ⟨_, (hR0 j hj).1 x hx, rfl⟩
  have hB : ∀ j < J, ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ k, Q s (fun x => eB0 (bosR SM (hjF κ (GenRecNodes.recF (s + p + 8) τ Ud
        (fun i => GN A F (s + p + 8) (Ud i)) j) x)) k) t ≤ (C0 * (τ + δ + ν)) ^ 2 :=
    fun j hj t ht => ((hR0 j hj).2.2 t ht).2.1
  obtain ⟨D, hD, hDb⟩ := GenStat.stationarity_of_cells κ SM hS hVS hκ0 hτ hc eB0 eBs0 heB0 hM0 hM
    hKgm (by positivity) hB v w hv0 hw0 hvJ hwJ
  refine ⟨D, hD, hDb.trans ?_⟩
  have hJT : (J : ℝ) * τ ≤ Tr := hJ.trans ht₁r
  have hsq : Real.sqrt (8 * ((J : ℝ) * τ)) ≤ Real.sqrt (8 * Tr) := Real.sqrt_le_sqrt (by linarith)
  have hvn : 0 ≤ GenStat.vnorm (s + p + 8) τ J v w := Real.sqrt_nonneg _
  have hε : 0 ≤ τ + δ + ν := by positivity
  have hX : 0 ≤ M * C0 * (τ + δ + ν) * GenStat.vnorm (s + p + 8) τ J v w := by positivity
  calc M * (C0 * (τ + δ + ν)) * Real.sqrt (8 * ((J : ℝ) * τ)) * GenStat.vnorm (s + p + 8) τ J v w
      = (M * C0 * (τ + δ + ν) * GenStat.vnorm (s + p + 8) τ J v w) *
          Real.sqrt (8 * ((J : ℝ) * τ)) := by ring
    _ ≤ (M * C0 * (τ + δ + ν) * GenStat.vnorm (s + p + 8) τ J v w) * Real.sqrt (8 * Tr) :=
        mul_le_mul_of_nonneg_left hsq hX
    _ = M * C0 * Real.sqrt (8 * Tr) * (τ + δ + ν) * GenStat.vnorm (s + p + 8) τ J v w := by ring

end Closed

end RenewalGeometry.GenNorms
