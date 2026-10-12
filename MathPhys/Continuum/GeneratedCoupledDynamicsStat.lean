/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.GeneratedCoupledDynamics
import MathPhys.Continuum.GeneratedCoupledStationarity

/-!
# `thm:generated-dynamics` with back-reacting spinors, including stationarity

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`
(`eq:generated-stationarity` included), for the complete Einstein–Standard-Model system with Dirac
back-reaction (`GenDStress.CoupledDirac`).

`GenCplDyn.generated_dynamics_ext_cpl` gives the physical solution, the Galerkin record, the
Hermite rates and the readouts for back-reacting data but omits the stationarity clause.  Here the
composite action is the **complete** first-order action `S^{cmp} = (L1SM + L1D) ∘ R`
(`GenCplSt.ScmpC`: first-derivative Einstein–Yang–Mills–Higgs density plus the first-order Dirac
density with spin connection, gauge coupling and Yukawa term) and its first variation is controlled
by the bosonic **and** the Dirac readouts (`GenCplSt.stationarity_of_cells_cpl`).

* `catL`, `sum_Q_cat_le` — concatenated readout coordinates (one record controls both the requested
  coordinates and fixed coordinates of the residual spaces);
* **`generated_dynamics_cpl_stat`** — the statement of `generated_dynamics_ext_cpl` plus
  `|D S^{cmp}[V]| ≤ C_st(τ + δ + ν)‖V‖_{0,τ}` for `κ ≠ 0`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace MathPhys.GenCplDynS

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal GenReadout GenNorms

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Concatenated coordinates -/

section Cat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n₁ n₂ : ℕ}

/-- The concatenation `(f₁, f₂) : E → ℝ^{n₁ + n₂}` of two coordinate maps. -/
def catL (f₁ : E →L[ℝ] (Fin n₁ → ℝ)) (f₂ : E →L[ℝ] (Fin n₂ → ℝ)) : E →L[ℝ] (Fin (n₁ + n₂) → ℝ) :=
  ContinuousLinearMap.pi fun i => Fin.addCases (motive := fun _ => E →L[ℝ] ℝ)
    (fun i => (ContinuousLinearMap.proj i).comp f₁) (fun i => (ContinuousLinearMap.proj i).comp f₂) i

theorem catL_left (f₁ : E →L[ℝ] (Fin n₁ → ℝ)) (f₂ : E →L[ℝ] (Fin n₂ → ℝ)) (r : E) (i : Fin n₁) :
    catL f₁ f₂ r (Fin.castAdd n₂ i) = f₁ r i := by
  simp [catL]

theorem catL_right (f₁ : E →L[ℝ] (Fin n₁ → ℝ)) (f₂ : E →L[ℝ] (Fin n₂ → ℝ)) (r : E) (i : Fin n₂) :
    catL f₁ f₂ r (Fin.natAdd n₁ i) = f₂ r i := by
  simp [catL]

theorem sum_Q_cat_le (f₁ : E →L[ℝ] (Fin n₁ → ℝ)) (f₂ : E →L[ℝ] (Fin n₂ → ℝ)) (R : ST 3 → E)
    (s : ℕ) (t : ℝ) :
    ∑ k, Q s (fun x => f₁ (R x) k) t ≤ ∑ k, Q s (fun x => catL f₁ f₂ (R x) k) t ∧
      ∑ k, Q s (fun x => f₂ (R x) k) t ≤ ∑ k, Q s (fun x => catL f₁ f₂ (R x) k) t := by
  rw [Fin.sum_univ_add]
  simp only [catL_left, catL_right]
  have h1 : 0 ≤ ∑ k, Q s (fun x => f₁ (R x) k) t := Finset.sum_nonneg fun k _ => Q_nonneg s _ t
  have h2 : 0 ≤ ∑ k, Q s (fun x => f₂ (R x) k) t := Finset.sum_nonneg fun k _ => Q_nonneg s _ t
  exact ⟨by linarith, by linarith⟩

end Cat

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
/-- **`thm:generated-dynamics` with back-reacting spinors, including stationarity**: the statement
of `GenCplDyn.generated_dynamics_ext_cpl` (smooth sources, Clifford-unitary forms, back-reacting
Dirac data `GenDStress.CoupledDirac`) for `κ ≠ 0`, with in addition the stationarity clause
`eq:generated-stationarity`: for every `J` with `Jτ ≤ t₁` and every nodal variation
`V = (v_j, v̇_j)` with fixed collar the derivative of the **complete** composite action
`S^{cmp} = (L1SM + L1D) ∘ R` (`GenCplSt.ScmpC`, nodal slopes `G_N(U^j)`) along `V` exists and
`|D S^{cmp}[V]| ≤ C_st(τ + δ + ν)‖V‖_{0,τ}`. -/
theorem generated_dynamics_cpl_stat (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
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
  obtain ⟨κ, hκ, h⟩ := GenCplDyn.generated_dynamics_ext_cpl (bG := bG) (bV := bV) (bS := bS)
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
  obtain ⟨D, hD, hDb⟩ := GenCplSt.stationarity_of_cells_cpl κ SM hS hC hκ0 hτ hc' eB0 eBs0 heB0
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

set_option maxHeartbeats 8000000 in
/-- **`thm:generated-dynamics` with back-reacting spinors in the manuscript's norms**: the
statement of `GenNorms.generated_dynamics_norms` (`C_t`/`L^∞_t` slice norms, data rate
`‖U_{0,N} - U₀‖_{H^{s+4}} ≤ C₀N^{-p}`, rates `eq:generated-first`, `eq:generated-bosonic`,
`eq:generated-Dirac`) for back-reacting Dirac data (`GenDStress.CoupledDirac`), with the
stationarity clause for the complete composite action `GenCplSt.ScmpC` (`κ ≠ 0`):
`|D S^{cmp}[V]| ≤ C(N^{-p} + τ)‖V‖_{0,τ}`. -/
theorem generated_dynamics_norms_cpl_stat (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
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
  obtain ⟨κ, hκ, h⟩ := generated_dynamics_cpl_stat (bG := bG) (bV := bV) (bS := bS) (bS' := bS')
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

set_option maxHeartbeats 8000000 in
/-- **`cor:generated-nonempty` with back-reacting spinors in the manuscript's norms**: the statement
of `GenNorms.generated_nonempty_norms` (finite data `U_{0,N} = P_N U₀`, `eq:generated-nonempty`,
summable dyadic budget) for back-reacting Dirac data (`GenDStress.CoupledDirac`), **with** the
stationarity clause for the complete composite action `GenCplSt.ScmpC` (`κ ≠ 0`). -/
theorem generated_nonempty_norms_cpl_stat (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
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
  obtain ⟨κ, hκ, h⟩ := generated_dynamics_norms_cpl_stat (bG := bG) (bV := bV) (bS := bS)
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


end Main

/-! ### Non-vacuity -/

section NonVacuity

open GenCplIdF GenDiracCur

/-- **The hypotheses of the coupled dynamics theorems with stationarity hold** for back-reacting
data with a nonzero Dirac stress: the gauge-neutral quaternionic data `GenCplIdF.quatN` have smooth
sources, unitary forms, back-reacting Dirac data, `κ = 1 ≠ 0` and a nonzero frame Dirac stress
component (`GenCplIdF.quatN_stress_ne`). -/
theorem quatN_stat_hyps : SMSmooth quatN ∧ UnitaryForms quatN (frob 1) (frob 1) PQ PQ ∧
    Nonempty (GenDStress.CoupledDirac quatN) ∧ quatN.κ ≠ 0 ∧
    quatN.TD.frame 0 ((1 : Quaternion ℝ), 0)
      (fun A => if A = 0 then ((1 : Quaternion ℝ), 0) else 0) (qU 0, 0) 0 0 1 ≠ 0 :=
  ⟨quatN_smooth, quatN_unitary, ⟨quatNCoupled⟩, by norm_num [quatN],
    by rw [quatN_stress_ne]; norm_num⟩

/-- `generated_nonempty_norms_cpl_stat` applies to `quatN` and yields Euclidean coordinates `κ`
of the state space orthonormal for the block form. -/
example : ∃ κ : StateP 1 (MatLie 1) SQ SQ ≃ₗ[ℝ] (Fin (dimS 1 (MatLie 1) SQ SQ) → ℝ),
    ∀ v w, ipP (frob 1) (frob 1) PQ PQ (κ.symm v) (κ.symm w) = ∑ i, v i * w i := by
  obtain ⟨κ, hκ, -⟩ := generated_nonempty_norms_cpl_stat quatN_smooth quatN_unitary quatNCoupled
    quatN_stat_hyps.2.2.2.1 (s := 3) (p := 1) le_rfl le_rfl
  exact ⟨κ, hκ⟩

end NonVacuity

end MathPhys.GenCplDynS
