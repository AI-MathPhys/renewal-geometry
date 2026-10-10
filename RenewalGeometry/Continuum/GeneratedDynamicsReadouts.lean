/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedReadoutResiduals

/-!
# `thm:generated-dynamics`: the bosonic and Dirac readouts on the actual-jet system

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`, clauses
`eq:generated-bosonic` and `eq:generated-Dirac` (`Σ = 𝕋³`), assembled from
`lem:generated-physical-identification` (`GenPhysIdFinal.core_identification`), the identified
rate package (`GenRatesId.generated_dynamics_rates_id`) and the readouts of an identified exact
solution (`GenReadout.readouts_of_identified`).

* **`GenReadout.generated_readouts`**.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenReadout

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}

/-! ### The readouts of the generated dynamics -/

section Main

variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

set_option maxHeartbeats 8000000 in
/-- **`thm:generated-dynamics`, clauses `eq:generated-bosonic` and `eq:generated-Dirac`, on the
actual-jet system (`Σ = 𝕋³`).**  For theory data with smooth sources, Clifford-unitary forms,
decoupled spinors and the current and stress Noether identities (the hypotheses of
`lem:generated-physical-identification`), there are Euclidean coordinates `κ` such that for every
compact chart margin `K ⊇ cthickening δ_K K₀` the realized symmetric system `(A, F)` (equal to
the actual-jet operators on `K`) satisfies, for every data radius `R₀`, with `T`, `R`, `c_*`,
`τ_*` depending only on `R₀`: every constrained smooth periodic datum `U₀` with
`‖U₀‖_{H^{s+p+8}} ≤ R₀` and values in `K₀` generates a smooth physical tuple `z` on
`[0, t₁] × 𝕋³` (`R_B(z) = R_D(z) = 0`, harmonic gauge, actual-jet state `= U₀` at `t = 0`), and for
all coordinates `e_B`, `e_D` of the residual spaces there are `C`, `η > 0` such that for every
cutoff `N`, step `τ` with `τ(N+1) ≤ c_*`, `τ ≤ τ_*`, and finite datum `U_{0,N}`
(`‖U_{0,N}‖_{H^q} ≤ R₀`, `‖U_{0,N} - U₀‖_{H^{s+4}} ≤ δ`) with `τ + δ + (N+1)^{-p} ≤ η`, the
implicit-midpoint record `U^j` exists on `[0, T]` (bound `R`), and on every cell
`[jτ, (j+1)τ] ⊆ [0, t₁]` the cubic-Hermite physical reconstruction (head fields of the Hermite
record with nodal slopes `G_N(U^j)`; symmetrized metric) has its coordinate 2-jets on the closed
cell in a fixed compact set `K₂` of the Lorentzian chart (independent of `N`, `τ`, the cell and
the datum `U_{0,N}`), its metric in the Lorentzian chart (so it is a slab-local field tuple,
`cell_tuple_residuals`) and on every slice of the open cell
`Σ_c ‖Riem(g_{N,τ}) - Riem(g)‖²_{H^s} ≤ (C(τ + δ + ν))²`,
`Σ_k ‖(e_B R_B(z_{N,τ}))_k‖²_{H^s} ≤ (C(τ + δ + ν))²`,
`Σ_k ‖(e_D R_D(z_{N,τ}))_k‖²_{H^{s+1}} ≤ (C(τ² + δ + ν))²`, `ν = (N+1)^{-p}`. -/
theorem generated_readouts (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    (hD : AJKatoMod.Decoupled SM) (hN : GenNoether.CurrentNoether SM)
    (hT : GenStress.StressNoether SM) {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
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
            ∃ C ≥ 0, ∃ η > 0, ∃ K2 : Set (J2I 3 × Fin (dimS m V S S') → ℝ), IsCompact K2 ∧
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
                ∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ →
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
                      (C * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2 := by
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
  obtain ⟨C, hC0, η, hη, K2, hK2, hK2c, hread⟩ := readouts_of_identified κ hS hs
    (fun x hx => ⟨((hid x (hsl x hx)).2).1, ((hid x (hsl x hx)).2).2.1⟩) hUrV hVt hVtt hCr hτs eB eD
  refine ⟨C, hC0, η, hη, K2, hK2, hK2c, fun N τ hτ hcfl hττ a₀ δ ha₀ hδ hdata hsmall => ?_⟩
  obtain ⟨Ud, hUd0, hUdrec, -, hherm⟩ := hrec N τ hτ hcfl hττ a₀ δ ha₀ hδ hdata
  refine ⟨Ud, hUd0, hUdrec, fun j hj => ?_⟩
  have hjr : ((j : ℝ) + 1) * τ ≤ Tr := hj.trans ht₁r
  exact hread τ hτ hττ δ (1 / ((N : ℝ) + 1) ^ p) hδ (by positivity) hsmall j (Ud j) (Ud (j + 1))
    (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) hj
    (fun θ hθ S₀ => (hherm j hjr θ hθ S₀).1) (fun θ hθ S₀ => (hherm j hjr θ hθ S₀).2.1)
    (fun θ hθ S₀ => (hherm j hjr θ hθ S₀).2.2)

end Main

end RenewalGeometry.GenReadout
