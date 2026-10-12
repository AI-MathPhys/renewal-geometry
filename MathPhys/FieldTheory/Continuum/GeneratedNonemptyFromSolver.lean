/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.LichnerowiczActualJetSolver
import MathPhys.FieldTheory.Continuum.GeneratedCoupledDynamicsStat
import MathPhys.FieldTheory.Continuum.GeneratedChartDynamics

/-!
# `cor:generated-nonempty` fed by the constrained-initial solver

Einstein–Standard-Model action-closure manuscript, `cor:generated-nonempty`,
`prop:generated-initial`, `thm:generated-dynamics`: the composition the paper makes — the
constrained initial class is the **output of the constrained-initial solver**
(`GenSlice.ConfSolver.solver_constrainedData`: Banach contraction for the conformal factor,
elliptic regularity at all orders, conformal identity with the actual-jet Hamiltonian, momentum
and Gauss rows, Cauchy-data completion to a slice-constrained tuple) and the generated finite
dynamics is run from it (`GenCplDynS.generated_nonempty_norms_cpl_stat`).

* **`generated_nonempty_from_solver`** — the composed statement (smooth sources);
* `exists_chart_for_state` — the chart hypotheses of the chain (`K₀ ⊆ K` compact in the
  Lorentzian chart, with a thickening margin) hold for the actual-jet state of every smooth tuple,
  so the composed statement is never vacuous in its data hypotheses.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Real

noncomputable section

namespace MathPhys.GenNonemptySolver

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal GenReadout GenNorms GenSlice GenSlice.ConfSolver LichnerowiczContraction
  TorusSobolevTransfer PeriodicGridSobolev.Composition GenPhysId

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
variable {Pi0 : V} {τH : ℝ}

set_option maxHeartbeats 8000000 in
/-- **`cor:generated-nonempty` composed with the constrained-initial solver**
(`prop:generated-initial` → `lem:generated-physical-identification` → `thm:generated-dynamics`,
as the paper composes it): for back-reacting Dirac theory data with smooth sources, unitary forms,
`κ ≠ 0`, a Yang–Mills source vanishing at zero Higgs field and zero spinors, and an admissible
background (`Background`: `𝖠_* = 2κ|Π₀|² > 0`, `⅔τ² - 2Λ - 2κλv⁴ = 𝖠_*`), the class of initial data
is the **output of the solver**: for every transverse–traceless seed with `‖|σ|²‖_{H^r} ≤ ε_r` the
Banach contraction gives a smooth conformal factor whose conformal Cauchy datum is constrained, its
completion `z₀` is slice-constrained, its actual-jet state `U₀ = stU κ SM z₀` is a
`ConstrainedData` datum, and — with the uniform constants of the chain (depending only on the
chart `K` and the bound `R₀`) — the fully finite spectral–midpoint evolution from `P_N U₀`
satisfies `eq:generated-nonempty`, the Dirac rate, the stationarity estimate and the summable
dyadic budget, as in `GenCplDynS.generated_nonempty_norms_cpl_stat`. -/
theorem generated_nonempty_from_solver (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    (hC : GenDStress.CoupledDirac SM) (hκ0 : SM.κ ≠ 0) (hb : Background SM Pi0 τH)
    (hJ : ∀ (g gi : Met) (DH : Fin 4 → V), SM.Jcur g gi 0 DH 0 0 = 0) {r : ℕ} (hr : 2 ≤ r)
    {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
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
        ∀ σ : Conf.TTSeed, sn r ⇑(seedSource σ) ≤ eps (bgData SM Pi0 τH hb) r hr →
          ∃ (wc : CT) (Fc : Conf.ConfFactor) (z₀ : Tuple m V S S'),
            (HamiltonianEq (bgData SM Pi0 τH hb) (seedSource σ) 0 0 wc ∧ Fc.w = liftR wc ∧
            (∀ y, 1 / 2 < Fc.w y ∧ Fc.w y < 3 / 2) ∧
            (Conf.confDatum (m := m) (S := S) (S' := S') Fc σ τH Pi0).Constrained SM ∧
            GenPhysIdClosed.SliceConstrained SM z₀ ∧
            GenPhysIdClosed.ConstrainedData SM κ (stU κ SM z₀) ∧
            (∀ y : Fin 3 → ℝ, z₀.g (Fin.cons 0 y) = met4 (-1) 0 (Conf.confγ Fc.w y) ∧
              z₀.H (Fin.cons 0 y) = 0 ∧ pd z₀.H 0 (Fin.cons 0 y) = (Fc.w y ^ 6)⁻¹ • Pi0 ∧
              z₀.ψ (Fin.cons 0 y) = 0 ∧ z₀.ψb (Fin.cons 0 y) = 0)) ∧
          (sliceH (s + p + 8) (stU κ SM z₀) 0 ≤ R₀ →
          (∀ y, (fun c => stU κ SM z₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ t₁ ≤ T ∧
            (∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0) ∧
            (∀ b y, stC κ SM z b (Fin.cons 0 y) = (stU κ SM z₀) b (Fin.cons 0 y)) ∧
            ∀ {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) {nD : ℕ}
              (eD : S × S' →L[ℝ] (Fin nD → ℝ)),
            ∃ C ≥ 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ τ₀ > 0,
              ∀ (N : ℕ) (τ : ℝ), N₀ ≤ N → 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τ₀ →
              ∃ Ud : ℕ → GS 3 (dimS m V S S') N, Ud 0 = P0 (s + p + 8) N (stU κ SM z₀) ∧
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
                      |D| ≤ C * (((N : ℝ) ^ p)⁻¹ + τ) * GenStat.vnorm (s + p + 8) τ J v w) := by
  obtain ⟨κ, hκ, h⟩ := GenCplDynS.generated_nonempty_norms_cpl_stat (bG := bG) (bV := bV) (bS := bS)
    (bS' := bS') hS hU hC hκ0 hs hp
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK, h2⟩ := h K₀ K hK hKc δK hδK hKδ
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT, R, hR, cstar, hc, hsum, h3⟩ := h2 R₀ hR₀
  refine ⟨T, hT, R, hR, cstar, hc, hsum, fun σ hσ => ?_⟩
  obtain ⟨wc, Fc, z₀, -, hE, -, hFw, hbds, hcons, hz, hcd, hd⟩ :=
    solver_constrainedData SM Pi0 τH (fun z => contDiff_bosF SM z hS)
      (GenSlice.stressSymm_of_coupledDirac hC) hb hJ hr σ hσ κ
  refine ⟨wc, Fc, z₀, ⟨hE, hFw, hbds, hcons, hz, hcd, fun y => ?_⟩, fun hR0 hK0 => ?_⟩
  · obtain ⟨h1, -, h3', h4, h5, h6⟩ := hd y
    exact ⟨h1, h3', h4, h5, h6⟩
  · exact h3 (stU κ SM z₀) hcd (fun b => GenPhysId.contDiff_stU (κ := κ) (SM := SM) (z := z₀) b)
      (fun b => GenPhysId.isSPeriodic_stU κ SM z₀ b) hR0 hK0



set_option maxHeartbeats 8000000 in
/-- **`cor:generated-nonempty` composed with the constrained-initial solver, chart-local smoothness**
(`GenChL.SMSmoothL`: charged back-reacting spinors) —
(`prop:generated-initial` → `lem:generated-physical-identification` → `thm:generated-dynamics`,
as the paper composes it): for back-reacting Dirac theory data with smooth sources, unitary forms,
`κ ≠ 0`, a Yang–Mills source vanishing at zero Higgs field and zero spinors, and an admissible
background (`Background`: `𝖠_* = 2κ|Π₀|² > 0`, `⅔τ² - 2Λ - 2κλv⁴ = 𝖠_*`), the class of initial data
is the **output of the solver**: for every transverse–traceless seed with `‖|σ|²‖_{H^r} ≤ ε_r` the
Banach contraction gives a smooth conformal factor whose conformal Cauchy datum is constrained, its
completion `z₀` is slice-constrained, its actual-jet state `U₀ = stU κ SM z₀` is a
`ConstrainedData` datum, and — with the uniform constants of the chain (depending only on the
chart `K` and the bound `R₀`) — the fully finite spectral–midpoint evolution from `P_N U₀`
satisfies `eq:generated-nonempty`, the Dirac rate, the stationarity estimate and the summable
dyadic budget, as in `GenCplDynS.ChL.generated_nonempty_norms_cpl_statL`. -/
theorem generated_nonempty_from_solverL (hS : GenChL.SMSmoothL SM) (hU : UnitaryForms SM bG bV bS bS')
    (hC : GenDStress.CoupledDirac SM) (hκ0 : SM.κ ≠ 0) (hb : Background SM Pi0 τH)
    (hJ : ∀ (g gi : Met) (DH : Fin 4 → V), SM.Jcur g gi 0 DH 0 0 = 0) {r : ℕ} (hr : 2 ≤ r)
    {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
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
        ∀ σ : Conf.TTSeed, sn r ⇑(seedSource σ) ≤ eps (bgData SM Pi0 τH hb) r hr →
          ∃ (wc : CT) (Fc : Conf.ConfFactor) (z₀ : Tuple m V S S'),
            (HamiltonianEq (bgData SM Pi0 τH hb) (seedSource σ) 0 0 wc ∧ Fc.w = liftR wc ∧
            (∀ y, 1 / 2 < Fc.w y ∧ Fc.w y < 3 / 2) ∧
            (Conf.confDatum (m := m) (S := S) (S' := S') Fc σ τH Pi0).Constrained SM ∧
            GenPhysIdClosed.SliceConstrained SM z₀ ∧
            GenPhysIdClosed.ConstrainedData SM κ (stU κ SM z₀) ∧
            (∀ y : Fin 3 → ℝ, z₀.g (Fin.cons 0 y) = met4 (-1) 0 (Conf.confγ Fc.w y) ∧
              z₀.H (Fin.cons 0 y) = 0 ∧ pd z₀.H 0 (Fin.cons 0 y) = (Fc.w y ^ 6)⁻¹ • Pi0 ∧
              z₀.ψ (Fin.cons 0 y) = 0 ∧ z₀.ψb (Fin.cons 0 y) = 0)) ∧
          (sliceH (s + p + 8) (stU κ SM z₀) 0 ≤ R₀ →
          (∀ y, (fun c => stU κ SM z₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ t₁ ≤ T ∧
            (∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0) ∧
            (∀ b y, stC κ SM z b (Fin.cons 0 y) = (stU κ SM z₀) b (Fin.cons 0 y)) ∧
            ∀ {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) {nD : ℕ}
              (eD : S × S' →L[ℝ] (Fin nD → ℝ)),
            ∃ C ≥ 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ τ₀ > 0,
              ∀ (N : ℕ) (τ : ℝ), N₀ ≤ N → 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τ₀ →
              ∃ Ud : ℕ → GS 3 (dimS m V S S') N, Ud 0 = P0 (s + p + 8) N (stU κ SM z₀) ∧
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
                      |D| ≤ C * (((N : ℝ) ^ p)⁻¹ + τ) * GenStat.vnorm (s + p + 8) τ J v w) := by
  obtain ⟨κ, hκ, h⟩ := GenCplDynS.ChL.generated_nonempty_norms_cpl_statL (bG := bG) (bV := bV) (bS := bS)
    (bS' := bS') hS hU hC hκ0 hs hp
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK, h2⟩ := h K₀ K hK hKc δK hδK hKδ
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT, R, hR, cstar, hc, hsum, h3⟩ := h2 R₀ hR₀
  refine ⟨T, hT, R, hR, cstar, hc, hsum, fun σ hσ => ?_⟩
  obtain ⟨wc, Fc, z₀, -, hE, -, hFw, hbds, hcons, hz, hcd, hd⟩ :=
    solver_constrainedData SM Pi0 τH (fun z => ActualJetState.ChL.contDiff_bosFL SM z hS)
      (GenSlice.stressSymm_of_coupledDirac hC) hb hJ hr σ hσ κ
  refine ⟨wc, Fc, z₀, ⟨hE, hFw, hbds, hcons, hz, hcd, fun y => ?_⟩, fun hR0 hK0 => ?_⟩
  · obtain ⟨h1, -, h3', h4, h5, h6⟩ := hd y
    exact ⟨h1, h3', h4, h5, h6⟩
  · exact h3 (stU κ SM z₀) hcd (fun b => GenPhysId.contDiff_stU (κ := κ) (SM := SM) (z := z₀) b)
      (fun b => GenPhysId.isSPeriodic_stU κ SM z₀ b) hR0 hK0


/-! ### The chart hypotheses are satisfiable for every smooth tuple -/

theorem exists_chart_for_state (SM : SMData (MatLie m) V S S')
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (z : Tuple m V S S') :
    ∃ (K₀ K : Set (Fin (dimS m V S S') → ℝ)) (δK : ℝ), IsCompact K ∧
      (∀ v ∈ K, MetChart (κ.symm v).1) ∧ 0 < δK ∧ Metric.cthickening δK K₀ ⊆ K ∧
      ∀ y, (fun c => stU κ SM z c (Fin.cons 0 y)) ∈ K₀ := by
  set f : (Fin 3 → ℝ) → (Fin (dimS m V S S') → ℝ) := fun y => κ (stateF SM z (Fin.cons 0 y))
    with hf
  have hfc : Continuous f :=
    (LinearMap.continuous_of_finiteDimensional κ.toLinearMap).comp
      ((contDiff_stateF SM z).continuous.comp contDiff_cons0.continuous)
  have hfp : PeriodicCube.IsZPeriodic f := fun k y =>
    congrArg κ (per_slice (isSPeriodic_stateF SM z) k y)
  have hK₀ := isCompact_range_of_zperiodic hfc hfp
  set O : Set (Fin (dimS m V S S') → ℝ) := {v | MetChart (κ.symm v).1} with hO
  have hOo : IsOpen O := by
    have hc : Continuous fun v : Fin (dimS m V S S') → ℝ => κ.symm v :=
      LinearMap.continuous_of_finiteDimensional κ.symm.toLinearMap
    exact (isOpen_chart (m := m) (V := V) (S := S) (S' := S')).preimage hc
  have hsub : Set.range f ⊆ O := by
    rintro _ ⟨y, rfl⟩
    show MetChart (κ.symm (κ (stateF SM z (Fin.cons 0 y)))).1
    rw [LinearEquiv.symm_apply_apply]
    exact ⟨z.det_ne _, z.lor _⟩
  obtain ⟨δ, hδ, hδs⟩ := hK₀.exists_cthickening_subset_open hOo hsub
  refine ⟨Set.range f, Metric.cthickening δ (Set.range f), δ, hK₀.cthickening, fun v hv => hδs hv,
    hδ, subset_rfl, fun y => ⟨y, rfl⟩⟩

/-! ### Non-vacuity: a transverse–traceless seed and the quaternionic data -/

section NonVacuity

open GenCplIdF GenDiracCur GenSlice.Conf GenNoether GenPhysIdClosed

/-- The trace-free diagonal pattern `diag(1, -1, 0)`. -/
def cTT (i j : Fin 3) : ℝ := if i = 0 ∧ j = 0 then 1 else if i = 1 ∧ j = 1 then -1 else 0

theorem cTT_symm (i j : Fin 3) : cTT i j = cTT j i := by
  unfold cTT; split_ifs <;> simp_all

theorem cTT_two (i : Fin 3) : cTT 2 i = 0 := by unfold cTT; simp

/-- The profile `y ↦ cos(2π y₃)`. -/
def cosP (y : Fin 3 → ℝ) : ℝ := Real.cos (2 * π * y 2)

theorem contDiff_cosP : ContDiff ℝ ∞ cosP := by
  unfold cosP
  exact Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ (2 : Fin 3)))

theorem cosP_per : PeriodicCube.IsZPeriodic cosP := by
  intro k y
  simp only [cosP, Pi.add_apply, PeriodicCube.zvec]
  rw [show 2 * π * (y 2 + (k 2 : ℝ)) = 2 * π * y 2 + (k 2 : ℤ) * (2 * π) by ring,
    Real.cos_add_int_mul_two_pi]

theorem pd_cosP (k : Fin 3) (y : Fin 3 → ℝ) (hk : k ≠ 2) : pd cosP k y = 0 := by
  have hd : DifferentiableAt ℝ (fun y : Fin 3 → ℝ => y 2) y := differentiableAt_apply 2 y
  have hφ : HasDerivAt (fun x => Real.cos (2 * π * x)) (-Real.sin (2 * π * y 2) * (2 * π)) (y 2) := by
    have := ((hasDerivAt_id (y 2)).const_mul (2 * π)).cos
    simpa using this
  have h := pd3_comp hd hφ k
  have h2 : pd (fun y : Fin 3 → ℝ => y 2) k y = 0 := by
    show fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2) y
      (Pi.single k 1) = 0
    rw [ContinuousLinearMap.fderiv]
    simp [Pi.single_apply, Ne.symm hk]
  rw [show (fun y : Fin 3 → ℝ => Real.cos (2 * π * y 2)) = cosP from rfl, h2, mul_zero] at h
  exact h

/-- **A non-trivial transverse–traceless seed**: `σ_ε = ε cos(2π y₃) diag(1, -1, 0)`. -/
def cosSeed (ε : ℝ) : TTSeed where
  σ := fun y i j => ε * cosP y * cTT i j
  smooth := by
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    exact (contDiff_const.mul contDiff_cosP).mul contDiff_const
  per := fun k y => by simp only [cosP_per k y]
  symm := fun y i j => by rw [cTT_symm]
  tr := fun y => by simp [cTT]
  div := fun y i => by
    have hc : ∀ i j, ContDiff ℝ ∞ (fun y => ε * cosP y * cTT i j) := fun i j =>
      (contDiff_const.mul contDiff_cosP).mul contDiff_const
    have hpd : ∀ k i j, pd (fun y (i j : Fin 3) => ε * cosP y * cTT i j) k y i j =
        ε * pd cosP k y * cTT i j := by
      intro k i j
      have hF : ContDiff ℝ ∞ (fun y (i j : Fin 3) => ε * cosP y * cTT i j) :=
        contDiff_pi.2 fun i => contDiff_pi.2 fun j => hc i j
      rw [← pd3_apply (F := fun y (i j : Fin 3) => ε * cosP y * cTT i j)
        (hF.differentiable (by simp) y) k i,
        ← pd3_apply (F := fun y (j : Fin 3) => ε * cosP y * cTT i j)
        ((contDiff_pi.2 fun j => hc i j).differentiable (by simp) y) k j]
      have e : (fun y => ε * cosP y * cTT i j) = fun y => (ε * cTT i j) • cosP y := by
        funext y; simp [smul_eq_mul]; ring
      rw [e, pd3_smul ((contDiff_cosP.differentiable (by simp)) y)]
      simp [smul_eq_mul]; ring
    simp only [hpd, pd_cosP 0 y (by decide), pd_cosP 1 y (by decide), cTT_two, mul_zero, zero_mul,
      add_zero]

theorem cosSeed_ne (ε : ℝ) (hε : ε ≠ 0) : (cosSeed ε).σ 0 0 0 ≠ 0 := by
  simp [cosSeed, cosP, cTT, hε]

theorem seedSource_cosSeed (ε : ℝ) :
    seedSource (cosSeed ε) = ((ε ^ 2 : ℝ) : ℂ) • seedSource (cosSeed 1) := by
  ext t
  simp only [seedSource, SobolevBoxCr.descend, SobolevBoxCr.descendFun, ContinuousMap.coe_mk,
    ContinuousMap.smul_apply, smul_eq_mul, sqσ, cosSeed]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `Π₀ = 1 ∈ gl(1)`. -/
def pi1 : MatLie 1 := (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin 1) (Fin 1) ℝ)

theorem quatN_background : Background quatN pi1 (Real.sqrt 3) where
  pos := by
    show 0 < 2 * (1 : ℝ) * traceForm 1 pi1 pi1
    rw [traceForm_one]; simp [pi1]
  bg := by
    show 2 / 3 * Real.sqrt 3 ^ 2 - 2 * (0 : ℝ) - 2 * 1 * (0 * 0 ^ 4) = 2 * 1 * traceForm 1 pi1 pi1
    rw [traceForm_one, Real.sq_sqrt (by norm_num)]
    simp [pi1]

theorem quatN_Jcur_zero (g gi : Met) (DH : Fin 4 → MatLie 1) :
    quatN.Jcur g gi 0 DH 0 0 = 0 := by
  funext ν
  show (2 : ℝ) • (0 : MatLie 1 →ₗ[ℝ] MatLie 1 →ₗ[ℝ] MatLie 1) 0 (DH ν) +
    diracCur (0 : SQ →ₗ[ℝ] SQ →ₗ[ℝ] MatLie 1) _ g gi 0 0 ν = 0
  simp [diracCur]

/-- **Non-vacuity of the composed statement**: for the back-reacting quaternionic data `quatN`
(`Λ = 0`, `κ = 1`, real Higgs `Π₀ = 1`, `τ = √3`) and every order `r ≥ 2`, there is a nonzero
transverse–traceless seed `σ_ε = ε cos(2πy₃) diag(1,-1,0)` with small source, and the solver
produces a constrained conformal datum whose completion is slice-constrained and lies in the
constrained actual-jet class. -/
theorem quatN_solver_nonvacuous {r : ℕ} (hr : 2 ≤ r)
    (κ : StateP 1 (MatLie 1) SQ SQ ≃ₗ[ℝ] (Fin (dimS 1 (MatLie 1) SQ SQ) → ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ (cosSeed ε).σ 0 0 0 ≠ 0 ∧
      ∃ (w : CT) (F : ConfFactor) (z : Tuple 1 (MatLie 1) SQ SQ),
        HamiltonianEq (bgData quatN pi1 (Real.sqrt 3) quatN_background) (seedSource (cosSeed ε)) 0 0 w ∧
        (confDatum (m := 1) (S := SQ) (S' := SQ) F (cosSeed ε) (Real.sqrt 3) pi1).Constrained quatN ∧
        SliceConstrained quatN z ∧ ConstrainedData quatN κ (stU κ quatN z) := by
  set D := bgData quatN pi1 (Real.sqrt 3) quatN_background
  set S1 := sn r ⇑(seedSource (cosSeed 1))
  have hS1 : 0 ≤ S1 := sn_nonneg _ _
  have he := eps_pos D r hr
  set ε := Real.sqrt (eps D r hr / (S1 + 1)) with hεdef
  have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have hη : sn r ⇑(seedSource (cosSeed ε)) ≤ eps D r hr := by
    rw [seedSource_cosSeed, sn_smul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ε), hεdef,
      Real.sq_sqrt (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨w, F, z, -, hE, -, -, -, hc, hz, hcd, -⟩ := solver_constrainedData quatN pi1 (Real.sqrt 3)
    (fun z => contDiff_bosF quatN z quatN_smooth) (stressSymm_of_coupledDirac quatNCoupled)
    quatN_background quatN_Jcur_zero hr (cosSeed ε) hη κ
  exact ⟨ε, hε, cosSeed_ne ε hε.ne', w, F, z, hE, hc, hz, hcd⟩

end NonVacuity

end MathPhys.GenNonemptySolver
