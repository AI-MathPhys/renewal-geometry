/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedReadoutHeads
import RenewalGeometry.Continuum.GeneratedReadoutCore
import RenewalGeometry.Continuum.GeneratedReadoutCells

/-!
# The residual readouts of the generated dynamics (`eq:generated-bosonic`, `eq:generated-Dirac`)

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`, clauses
`eq:generated-bosonic` and `eq:generated-Dirac` (`Σ = 𝕋³`), on the actual-jet system:

for theory data with smooth sources, decoupled spinors and the Noether identities (the hypotheses
of `GenPhysIdFinal.generated_physical_identification`), every constrained datum generates a
physical solution `z` (Einstein, Yang–Mills, Higgs, Dirac, harmonic gauge), and for the fully
finite spectral–midpoint record `U^j` (cutoff `N`, step `τ`, finite data with
`‖U_{0,N} - U₀‖_{H^{s+4}} ≤ δ`), the cubic-Hermite physical reconstruction `z_{N,τ}` (head fields
of the Hermite record, symmetrized metric) is, on every cell inside the identification interval,
a Lorentzian slab-local field tuple whose residuals satisfy

* `Σ_c ‖Riem(g_{N,τ})_c - Riem(g)_c‖²_{H^s} ≤ (C(τ + δ + N^{-p}))²`,
* `Σ_k ‖(e_B R_B(z_{N,τ}))_k‖²_{H^s} ≤ (C(τ + δ + N^{-p}))²`,
* `Σ_k ‖(e_D R_D(z_{N,τ}))_k‖²_{H^{s+1}} ≤ (C(τ² + δ + N^{-p}))²`

on every slice of the cell (`L^∞_tH^s`, resp. `C_tH^{s+1}` on the cells), for any coordinates
`e_B`, `e_D` of the residual spaces, whenever `τ + δ + N^{-p} ≤ η` (`η > 0` depending on the
datum: the record must stay in the Lorentzian chart).  With the data of
`eq:generated-initial-rate` (`δ ≤ C N^{-p}`) these are the rates `C(N^{-p} + τ)`,
`C(N^{-p} + τ²)` of the theorem.

* **`generated_readouts`** — the statement above;
* **`cell_tuple_residuals`** — on each cell the head fields of the record form a slab-local tuple
  (`GenReadout.recTuple`) and every global extension has the residuals `bosR(hjF)`, `dirR(hjF)`,
  i.e. the displayed quantities are the actual residuals of an actual field tuple.

Proof: physical identification (`GenPhysIdFinal.core_identification`), the identified rate package
(`GenRatesId.generated_dynamics_rates_id`: the limit of the rates is the actual-jet state of `z`),
slice energies of the record (`GenHermite.cell_energies`, Parseval), jet energies
(`GenHermite.jet2_energy_le`, `jet1_energy_le`), smoothness of the raw residual maps on the chart
(`GenResMaps.bosR_smooth`, `dirR_smooth`, `riemR_smooth`) and the readout core (cutoff,
margin, Lipschitz composition on frozen slices, `GenHermite.readout_core`).
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

/-! ### Small lemmas -/

theorem card_J2I : Fintype.card (J2I 3) = 21 := by simp [J2I]

theorem card_J1I : Fintype.card (J1I 3) = 5 := by simp [J1I]

/-- The values of a continuous periodic field on the slices of `[0, t₁]` lie in a compact set. -/
theorem exists_compact_slices {ι : Type*} [Fintype ι] {w : ι → ST 3 → ℝ}
    (hw : ∀ i, Continuous (w i)) (hwp : ∀ i, IsSPeriodic (w i)) (t₁ : ℝ) :
    ∃ K₁ : Set (ι → ℝ), IsCompact K₁ ∧ K₁ ⊆ Set.range (fun x => fun i => w i x) ∧
      ∀ t ∈ Icc 0 t₁, ∀ y : Fin 3 → ℝ, (fun i => w i (Fin.cons t y)) ∈ K₁ := by
  set Kc : Set (ST 3) := (fun q : ℝ × (Fin 3 → ℝ) => (Fin.cons q.1 q.2 : ST 3)) ''
    (Icc 0 t₁ ×ˢ Icc 0 1) with hKc
  have hKcc : IsCompact Kc := (isCompact_Icc.prod isCompact_Icc).image continuous_cons2
  refine ⟨(fun x => fun i => w i x) '' Kc, hKcc.image (continuous_pi hw),
    fun _ ⟨x, _, hx⟩ => ⟨x, hx⟩, fun t ht y => ?_⟩
  have hfr : (fun i => Int.fract (y i)) ∈ Icc (0 : Fin 3 → ℝ) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  refine ⟨Fin.cons t (fun i => Int.fract (y i)), ⟨(t, _), ⟨ht, hfr⟩, rfl⟩, ?_⟩
  funext i
  exact ((hwp i).slice t).apply_fract y

/-- Smoothness on an open preimage of a chart-smooth map composed with a smooth map. -/
theorem contDiffOn_comp_preimage {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {h : E → F} (hh : ContDiff ℝ ∞ h) {Φ : F → G} {O : Set F}
    (hΦ : ∀ w ∈ O, ContDiffAt ℝ ∞ Φ w) : ContDiffOn ℝ ∞ (fun w => Φ (h w)) (h ⁻¹' O) :=
  fun w hw => ((hΦ (h w) hw).comp w hh.contDiffAt).contDiffWithinAt

/-! ### The record on a cell as a field tuple -/

/-- **The record on a cell is a slab-local field tuple with the readout residuals**: if the head
metric of a smooth periodic coordinate family is in the Lorentzian chart on the open slab
`(a, b) × 𝕋³`, its head fields form a slab-local tuple (`recTuple`), and for every `x` of the
slab there is a global smooth tuple agreeing with these head fields near `x` whose actual-jet
residuals and Riemann tensor at `x` are the raw readouts `bosR(hjF)`, `dirR(hjF)`, `riemR(hjF)`. -/
theorem cell_tuple_residuals (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    {W : Fin (dimS m V S S') → ST 3 → ℝ} (hW : ∀ b, ContDiff ℝ ∞ (W b))
    (hWp : ∀ b, IsSPeriodic (W b)) {a b : ℝ}
    (hc : ∀ y ∈ openSlab a b, HeadChart κ (fun c => W c y)) {x : ST 3}
    (hx : x ∈ openSlab a b) :
    ∃ z' : Tuple m V S S', (z'.g =ᶠ[𝓝 x] fun y => Lg κ (fun c => W c y)) ∧
      (z'.A =ᶠ[𝓝 x] fun y => LA κ (fun c => W c y)) ∧
      (z'.H =ᶠ[𝓝 x] fun y => LH κ (fun c => W c y)) ∧
      (z'.ψ =ᶠ[𝓝 x] fun y => Lψ κ (fun c => W c y)) ∧
      (z'.ψb =ᶠ[𝓝 x] fun y => Lψb κ (fun c => W c y)) ∧
      bosF SM z' x = bosR SM (hjF κ W x) ∧ dirF SM z' x = GenResMaps.dirR SM (hjF κ W x) ∧
      ∀ c, riemR (hj2 z' x) c = riemR (hjF κ W x) c := by
  set L := recTuple κ W hW hWp hc with hL
  have h1 : a < x 0 := hx.1
  have h2 : x 0 < b := hx.2
  obtain ⟨z', hz'⟩ := SlabLocal.exists_ext L (c := (a + x 0) / 2) (d := (x 0 + b) / 2)
    (by linarith) (by linarith) (by linarith)
  have hxin : x ∈ openSlab ((a + x 0) / 2) ((x 0 + b) / 2) :=
    ⟨show (a + x 0) / 2 < x 0 by linarith, show x 0 < (x 0 + b) / 2 by linarith⟩
  obtain ⟨hg, hA, hH, hψ, hψb⟩ := hz' x hxin
  have hj := hj2_of_near κ hg hA hH hψ hψb
  refine ⟨z', hg, hA, hH, hψ, hψb, ?_, ?_, fun c => by rw [hj]⟩
  · rw [← bosR_hj2, hj]
  · rw [← dirR_hj2, hj]

/-! ### The readouts for an identified exact solution -/

theorem Lg_stC (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (z : Tuple m V S S')
    (x : ST 3) : Lg κ (fun b => stC κ SM z b x) = z.g x := by
  have h := congrArg (fun j : HJ2 m V S S' => j.1.1) (hj2_eq_headJ κ SM z x)
  exact h.symm

theorem headChart_of_mem (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    {W : Fin (dimS m V S S') → ST 3 → ℝ} {y : ST 3}
    (h : headJ (m := m) (V := V) (S := S) (S' := S') κ (fun p => j2c W p y) ∈ chartJ2 m V S S') :
    HeadChart κ (fun c => W c y) := h

theorem slab_of_cell {τ t₁ : ℝ} (hτ : 0 < τ) {j : ℕ} (hj : ((j : ℝ) + 1) * τ ≤ t₁) {t : ℝ}
    (ht : t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)) : t ∈ Icc 0 t₁ :=
  ⟨le_trans (by positivity) ht.1, ht.2.trans hj⟩

set_option maxHeartbeats 4000000 in
/-- **The residual readouts for an identified exact solution.**  Let `z` be a physical smooth
tuple on `[0, t₁] × 𝕋³` (`R_B(z) = R_D(z) = 0`), `V = κ(𝒰(z))` its coordinate actual-jet state,
and let a one-sided classical solution `U` coincide with `V` there, with the time derivatives
`∂_tV = U_t` and `c_k(∂_t²V) = D₂`.  Then for all coordinates `e_B`, `e_D` there are `C`, `η > 0`
such that every Hermite cell `[jτ, (j+1)τ] ⊆ [0, t₁]` whose Fourier-form rates against `U` are
`C_r(τ² + δ + ν)` (values, slopes) and `C_r(τ + δ + ν)` (second derivatives), with
`τ + δ + ν ≤ η`, has its head metric in the Lorentzian chart and the residual bounds of
`eq:generated-bosonic` / `eq:generated-Dirac` on every slice of the open cell. -/
theorem readouts_of_identified (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (hS : SMSmooth SM) {s : ℕ} (hs : 3 ≤ s) {z : Tuple m V S S'} {t₁ : ℝ}
    (hphys : ∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0)
    {U Ut : Fin (dimS m V S S') → ST 3 → ℝ} {D₂ : Fin (dimS m V S S') → (Fin 3 → ℤ) → ℝ → ℝ}
    (hUV : ∀ x ∈ slab (d := 3) 0 t₁, ∀ b, U b x = stC κ SM z b x)
    (hVt : ∀ b, ∀ t ∈ Icc 0 t₁, ∀ y,
      pd (stC κ SM z b) 0 (Fin.cons t y) = Ut b (Fin.cons t y))
    (hVtt : ∀ b k, ∀ t ∈ Icc 0 t₁, coef (pd (pd (stC κ SM z b) 0) 0) t k = D₂ b k t)
    {Cr τs : ℝ} (hCr : 0 ≤ Cr) (hτs : 0 < τs) {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ))
    {nD : ℕ} (eD : S × S' →L[ℝ] (Fin nD → ℝ)) :
    ∃ C ≥ 0, ∃ η > 0, ∃ K2 : Set (J2I 3 × Fin (dimS m V S S') → ℝ), IsCompact K2 ∧
      (∀ w ∈ K2, headJ (m := m) (V := V) (S := S) (S' := S') κ w ∈ chartJ2 m V S S') ∧
      ∀ {q N : ℕ} (τ : ℝ), 0 < τ → τ ≤ τs → ∀ δ ν : ℝ, 0 ≤ δ → 0 ≤ ν →
      τ + δ + ν ≤ η → ∀ (j : ℕ) (Uj Uj1 Gj Gj1 : GS 3 (dimS m V S S') N),
      ((j : ℝ) + 1) * τ ≤ t₁ →
      (∀ θ ∈ Icc (0 : ℝ) 1, ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 2) k *
        (cf q (SpectralGalerkin.hermite τ Uj Uj1 Gj Gj1 θ) b k -
          coef (U b) (j * τ + θ * τ) k) ^ 2 ≤ (Cr * (τ ^ 2 + δ + ν)) ^ 2) →
      (∀ θ ∈ Icc (0 : ℝ) 1, ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 2) k *
        (cf q (SpectralGalerkin.hermiteD τ Uj Uj1 Gj Gj1 θ) b k -
          coef (Ut b) (j * τ + θ * τ) k) ^ 2 ≤ (Cr * (τ ^ 2 + δ + ν)) ^ 2) →
      (∀ θ ∈ Icc (0 : ℝ) 1, ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq s k *
        (cf q (SpectralGalerkin.hermiteDD τ Uj Uj1 Gj Gj1 θ) b k -
          D₂ b k (j * τ + θ * τ)) ^ 2 ≤ (Cr * (τ + δ + ν)) ^ 2) →
      (∀ y : ST 3, y 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
        (fun p => j2c (recW τ (j * τ) Uj Uj1 Gj Gj1 q) p y) ∈ K2) ∧
      (∀ y ∈ openSlab (j * τ) ((j + 1) * τ),
        HeadChart κ (fun c => recW τ (j * τ) Uj Uj1 Gj Gj1 q c y)) ∧
      ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
        ∑ c : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q s (fun x =>
          riemR (hjF κ (recW τ (j * τ) Uj Uj1 Gj Gj1 q) x) c - riemR (hj2 z x) c) t ≤
            (C * (τ + δ + ν)) ^ 2 ∧
        ∑ k, Q s (fun x => eB (bosR SM (hjF κ (recW τ (j * τ) Uj Uj1 Gj Gj1 q) x)) k) t ≤
          (C * (τ + δ + ν)) ^ 2 ∧
        ∑ k, Q (s + 1) (fun x =>
          eD (GenResMaps.dirR SM (hjF κ (recW τ (j * τ) Uj Uj1 Gj Gj1 q) x)) k) t ≤
            (C * (τ ^ 2 + δ + ν)) ^ 2 := by
  set Vf := stC κ SM z with hVfdef
  have hV : ∀ b, ContDiff ℝ ∞ (Vf b) := contDiff_stC κ SM z
  have hVp : ∀ b, IsSPeriodic (Vf b) := isSPeriodic_stC κ SM z
  have hj2V : ∀ p, ContDiff ℝ ∞ (j2c Vf p) := fun p => contDiff_jop2 p.1 (hV p.2)
  have hj2Vp : ∀ p, IsSPeriodic (j2c Vf p) := fun p => isSPeriodic_jop2 p.1 (hVp p.2)
  have hj1V : ∀ p, ContDiff ℝ ∞ (j1c Vf p) := fun p => contDiff_jop1 p.1 (hV p.2)
  have hj1Vp : ∀ p, IsSPeriodic (j1c Vf p) := fun p => isSPeriodic_jop1 p.1 (hVp p.2)
  -- the compact jet sets of the exact solution
  obtain ⟨K1, hK1, hK1r, hK1m⟩ := exists_compact_slices (fun p => (hj2V p).continuous) hj2Vp t₁
  obtain ⟨K1', hK1', hK1r', hK1m'⟩ :=
    exists_compact_slices (fun p => (hj1V p).continuous) hj1Vp t₁
  -- the charts
  set O := headJ (m := m) (V := V) (S := S) (S' := S') κ ⁻¹' chartJ2 m V S S' with hOdef
  have hO : IsOpen O := isOpen_chartJ2.preimage (contDiff_headJ κ).continuous
  set O1 := head1J (m := m) (V := V) (S := S) (S' := S') κ ⁻¹' chartJ2 m V S S' with hO1def
  have hO1 : IsOpen O1 := isOpen_chartJ2.preimage (contDiff_head1J κ).continuous
  have hK1O : K1 ⊆ O := by
    intro w hw
    obtain ⟨x, rfl⟩ := hK1r hw
    show headJ κ (fun p => j2c Vf p x) ∈ chartJ2 m V S S'
    rw [← hj2_eq_headJ κ SM z x]
    exact ⟨z.det_ne x, z.lor x⟩
  have hK1O' : K1' ⊆ O1 := by
    intro w hw
    obtain ⟨x, rfl⟩ := hK1r' hw
    show head1J κ (fun p => j1c Vf p x) ∈ chartJ2 m V S S'
    have hg : (head1J (m := m) (V := V) (S := S) (S' := S') κ (fun p => j1c Vf p x)).1.1 =
        z.g x := Lg_stC κ z x
    show (Matrix.of (head1J κ (fun p => j1c Vf p x)).1.1).det ≠ 0 ∧
      IsLorChart (ginvOf (head1J κ (fun p => j1c Vf p x)).1.1)
    rw [hg]
    exact ⟨z.det_ne x, z.lor x⟩
  -- the readout families
  have hΨR : ∀ c : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      ContDiffOn ℝ ∞ (fun w => riemR (headJ (m := m) (V := V) (S := S) (S' := S') κ w) c) O :=
    fun c => contDiffOn_comp_preimage (contDiff_headJ κ) fun w hw => riemR_smooth hw c
  have hΨB : ∀ k : Fin nB,
      ContDiffOn ℝ ∞ (fun w => eB (bosR SM (headJ κ w)) k) O := fun k =>
    contDiffOn_comp_preimage (Φ := fun j => eB (bosR SM j) k) (contDiff_headJ κ) fun w hw =>
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nB => ℝ) k).comp eB).contDiff
        |>.contDiffAt).comp w (bosR_smooth SM hS hw)
  have hΨD : ∀ k : Fin nD,
      ContDiffOn ℝ ∞ (fun w => eD (GenResMaps.dirR SM (head1J κ w)) k) O1 := fun k =>
    contDiffOn_comp_preimage (Φ := fun j => eD (GenResMaps.dirR SM j) k) (contDiff_head1J κ)
      fun w hw => (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nD => ℝ) k).comp
        eD).contDiff |>.contDiffAt).comp w (dirR_smooth SM hw)
  -- energy bounds of the exact jets
  have hMb : ∀ {ι : Type} [Fintype ι] (r : ℕ) (f : ι → ST 3 → ℝ), (∀ i, ContDiff ℝ ∞ (f i)) →
      ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc 0 t₁, ∑ i, Q r (f i) t ≤ M := by
    intro ι _ r f hf
    have hc : ContinuousOn (fun t => ∑ i, Q r (f i) t) (Icc 0 t₁) :=
      (continuous_finsetSum _ fun i _ => continuous_Q r (hf i)).continuousOn
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine ⟨|M|, abs_nonneg _, fun t ht => ?_⟩
    have := hM t ht
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_abs_self _))
  obtain ⟨M2, hM2, hM2b⟩ := hMb s (j2c Vf) hj2V
  obtain ⟨M1, hM1, hM1b⟩ := hMb (s + 1) (j1c Vf) hj1V
  -- the readout cores
  obtain ⟨εR, hεR, hsubR, ΨR, hΨRs, hΨRK, KR, hKR, CSR, hCSR, coreR⟩ :=
    readout_core (r := s) hs hO hK1 hK1O hΨR hM2
  obtain ⟨εB, hεB, hsubB, ΨB, hΨBs, hΨBK, KB, hKB, CSB, hCSB, coreB⟩ :=
    readout_core (r := s) hs hO hK1 hK1O hΨB hM2
  obtain ⟨εD, hεD, hsubD, ΨD, hΨDs, hΨDK, KD, hKD, CSD, hCSD, coreD⟩ :=
    readout_core (r := s + 1) (by omega) hO1 hK1' hK1O' hΨD hM1
  -- the constants
  set Mst : ℝ := max 1 τs with hMst
  have hMst1 : 1 ≤ Mst := le_max_left _ _
  have hMstτ : τs ≤ Mst := le_max_right _ _
  set CE : ℝ := 21 * (Cr ^ 2 + 2 * (Cr ^ 2 * Mst ^ 2)) with hCE
  set CE1 : ℝ := 5 * (2 * (Cr ^ 2 * Mst ^ 2)) with hCE1
  have hCE0 : 0 ≤ CE := by positivity
  have hCE10 : 0 ≤ CE1 := by positivity
  set εm : ℝ := min εR (min εB εD) with hεm
  have hεm0 : 0 < εm := lt_min hεR (lt_min hεB hεD)
  set Λ : ℝ := (CE + CE1 + 1) * (CSR + CSB + CSD + 1) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have h1 : 1 ≤ CE + CE1 + 1 := by linarith
    have h2 : 1 ≤ CSR + CSB + CSD + 1 := by linarith
    nlinarith
  have hΛ0 : 0 < Λ := by linarith
  set η : ℝ := min 1 εm / Real.sqrt Λ with hη
  have hη0 : 0 < η := div_pos (lt_min one_pos hεm0) (Real.sqrt_pos.2 hΛ0)
  set C : ℝ := Real.sqrt (256 * (KR * CE)) + Real.sqrt (nB * (KB * CE)) +
    Real.sqrt (nD * (KD * (10 * Cr ^ 2))) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, η, hη0, Metric.cthickening εR K1, hK1.cthickening, fun w hw => hsubR hw,
    fun {q N} τ hτ hττ δ ν hδ hν hεη j Uj Uj1 Gj Gj1 hj h0 h1 h2 => ?_⟩
  set W := recW τ (j * τ) Uj Uj1 Gj Gj1 q with hWdef
  have hW : ∀ b, ContDiff ℝ ∞ (W b) := fun b => contDiff_recW τ _ Uj Uj1 Gj Gj1 b
  have hWp : ∀ b, IsSPeriodic (W b) := fun b => isSPeriodic_recW τ _ Uj Uj1 Gj Gj1 b
  have hj2W : ∀ p, ContDiff ℝ ∞ (j2c W p) := fun p => contDiff_jop2 p.1 (hW p.2)
  have hj2Wp : ∀ p, IsSPeriodic (j2c W p) := fun p => isSPeriodic_jop2 p.1 (hWp p.2)
  have hj1W : ∀ p, ContDiff ℝ ∞ (j1c W p) := fun p => contDiff_jop1 p.1 (hW p.2)
  have hj1Wp : ∀ p, IsSPeriodic (j1c W p) := fun p => isSPeriodic_jop1 p.1 (hWp p.2)
  set ε : ℝ := τ + δ + ν with hεdef
  set ε₂ : ℝ := τ ^ 2 + δ + ν with hε₂def
  have hε0 : 0 ≤ ε := by positivity
  have hε₂0 : 0 ≤ ε₂ := by positivity
  have hε₂ε : ε₂ ≤ Mst * ε := by
    have h1 : τ ^ 2 ≤ Mst * τ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (hττ.trans hMstτ) hτ.le
    have h2 : δ + ν ≤ Mst * (δ + ν) := le_mul_of_one_le_left (by positivity) hMst1
    rw [hε₂def, hεdef]; nlinarith
  -- `ε` is small
  have hεsq : ε ^ 2 * Λ ≤ (min 1 εm) ^ 2 := by
    have h1 : ε ≤ min 1 εm / Real.sqrt Λ := hεη
    have h2 : ε * Real.sqrt Λ ≤ min 1 εm := by
      rwa [le_div_iff₀ (Real.sqrt_pos.2 hΛ0)] at h1
    have h3 : (ε * Real.sqrt Λ) ^ 2 ≤ (min 1 εm) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rwa [mul_pow, Real.sq_sqrt hΛ0.le] at h3
  have hmin1 : (min 1 εm) ^ 2 ≤ 1 := by
    have := min_le_left 1 εm
    have h0 : 0 ≤ min 1 εm := le_min zero_le_one hεm0.le
    nlinarith
  have hmin2 : ∀ e, e ≥ εm → (min 1 εm) ^ 2 ≤ e ^ 2 := fun e he => by
    have h0 : 0 ≤ min 1 εm := le_min zero_le_one hεm0.le
    exact pow_le_pow_left₀ h0 ((min_le_right 1 εm).trans he) 2
  have hsmall : ∀ A B : ℝ, A * B ≤ Λ → A * (B * ε ^ 2) ≤ (min 1 εm) ^ 2 := fun A B h => by
    have := mul_le_mul_of_nonneg_right h (sq_nonneg ε)
    nlinarith [hεsq]
  have hp1 : 0 ≤ CSB + CSD + 1 := by positivity
  have hp2 : 0 ≤ CSR + CSD + 1 := by positivity
  have hp3 : 0 ≤ CSR + CSB + 1 := by positivity
  have hCSRΛ : CSR * CE ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg hCE0 hp1, mul_nonneg (add_nonneg hCE10 zero_le_one)
      (add_nonneg (add_nonneg (add_nonneg hCSR hCSB) hCSD) zero_le_one)]
  have hCSBΛ : CSB * CE ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg hCE0 hp2, mul_nonneg (add_nonneg hCE10 zero_le_one)
      (add_nonneg (add_nonneg (add_nonneg hCSR hCSB) hCSD) zero_le_one)]
  have hCSDΛ : CSD * CE1 ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg hCE10 hp3, mul_nonneg (add_nonneg hCE0 zero_le_one)
      (add_nonneg (add_nonneg (add_nonneg hCSR hCSB) hCSD) zero_le_one)]
  have hCEΛ : 1 * CE ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg (add_nonneg (add_nonneg hCE0 hCE10) zero_le_one)
      (add_nonneg (add_nonneg hCSR hCSB) hCSD)]
  have hCE1Λ : 1 * CE1 ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg (add_nonneg (add_nonneg hCE0 hCE10) zero_le_one)
      (add_nonneg (add_nonneg hCSR hCSB) hCSD)]
  have hE1 : CE * ε ^ 2 ≤ 1 := by
    have := hsmall 1 CE hCEΛ; linarith
  have hE1' : CE1 * ε ^ 2 ≤ 1 := by
    have := hsmall 1 CE1 hCE1Λ; linarith
  have hεmR : (min 1 εm) ^ 2 ≤ εR ^ 2 := hmin2 εR (min_le_left _ _)
  have hεmB : (min 1 εm) ^ 2 ≤ εB ^ 2 := hmin2 εB ((min_le_right _ _).trans (min_le_left _ _))
  have hεmD : (min 1 εm) ^ 2 ≤ εD ^ 2 := hmin2 εD ((min_le_right _ _).trans (min_le_right _ _))
  -- the Dirac energy
  set ED : ℝ := 10 * Cr ^ 2 * ε₂ ^ 2 with hED
  have hED0 : 0 ≤ ED := by positivity
  have hEDle : ED ≤ CE1 * ε ^ 2 := by
    have h1 : ε₂ ^ 2 ≤ Mst ^ 2 * ε ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hε₂0 hε₂ε 2
    have h2 : 0 ≤ Cr ^ 2 := sq_nonneg _
    rw [hED, hCE1]; nlinarith
  -- energies on the cell
  have hen : ∀ t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ p : J2I 3 × Fin (dimS m V S S'), Q s (fun x => j2c W p x - j2c Vf p x) t ≤ CE * ε ^ 2 ∧
      ∑ p : J1I 3 × Fin (dimS m V S S'), Q (s + 1) (fun x => j1c W p x - j1c Vf p x) t ≤ ED := by
    intro t ht
    obtain ⟨e0, e1, e2⟩ := cell_energies (q := q) (s := s) hτ hV hVp hUV hVt hVtt h0 h1 h2 ht hj
    have E2 := jet2_energy_le (r := s) hW hV e0 e1 e2
    have E1 := jet1_energy_le (r := s) hW hV e0 e1
    rw [card_J2I] at E2
    rw [card_J1I] at E1
    constructor
    · refine E2.trans ?_
      have h1 : (Cr * ε₂) ^ 2 ≤ Cr ^ 2 * Mst ^ 2 * ε ^ 2 := by
        rw [mul_pow, mul_assoc, ← mul_pow Mst]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε₂0 hε₂ε 2) (sq_nonneg _)
      have h2 : (Cr * ε) ^ 2 = Cr ^ 2 * ε ^ 2 := by ring
      rw [hCE]
      push_cast
      nlinarith
    · refine E1.trans (le_of_eq ?_)
      push_cast
      rw [hED]; ring
  -- the readout cores on the cell
  have hcR : ∀ t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (∀ y, (fun p => j2c W p (Fin.cons t y)) ∈ Metric.cthickening εR K1) ∧
      ∀ c, Q s (fun x => ΨR c (fun p => j2c W p x) - ΨR c (fun p => j2c Vf p x)) t ≤
        KR * (CE * ε ^ 2) := fun t ht =>
    coreR (j2c W) (j2c Vf) hj2W hj2V hj2Wp hj2Vp t (CE * ε ^ 2) (by positivity) hE1
      ((hsmall CSR CE hCSRΛ).trans hεmR) (hK1m t (slab_of_cell hτ hj ht))
      (hM2b t (slab_of_cell hτ hj ht)) (hen t ht).1
  have hcB : ∀ t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (∀ y, (fun p => j2c W p (Fin.cons t y)) ∈ Metric.cthickening εB K1) ∧
      ∀ k, Q s (fun x => ΨB k (fun p => j2c W p x) - ΨB k (fun p => j2c Vf p x)) t ≤
        KB * (CE * ε ^ 2) := fun t ht =>
    coreB (j2c W) (j2c Vf) hj2W hj2V hj2Wp hj2Vp t (CE * ε ^ 2) (by positivity) hE1
      ((hsmall CSB CE hCSBΛ).trans hεmB) (hK1m t (slab_of_cell hτ hj ht))
      (hM2b t (slab_of_cell hτ hj ht)) (hen t ht).1
  have hcD : ∀ t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (∀ y, (fun p => j1c W p (Fin.cons t y)) ∈ Metric.cthickening εD K1') ∧
      ∀ k, Q (s + 1) (fun x => ΨD k (fun p => j1c W p x) - ΨD k (fun p => j1c Vf p x)) t ≤
        KD * ED := fun t ht =>
    coreD (j1c W) (j1c Vf) hj1W hj1V hj1Wp hj1Vp t ED hED0 (hEDle.trans hE1')
      (le_trans (mul_le_mul_of_nonneg_left hEDle hCSD) ((hsmall CSD CE1 hCSDΛ).trans hεmD))
      (hK1m' t (slab_of_cell hτ hj ht)) (hM1b t (slab_of_cell hτ hj ht)) (hen t ht).2
  -- points of the open cell
  have hcell : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) := fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hx_cons : ∀ x : ST 3, (Fin.cons (x 0) (Fin.tail x) : ST 3) = x := Fin.cons_self_tail
  have hmR : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j2c W p x) ∈ Metric.cthickening εR K1 := fun x hx => by
    have := (hcR (x 0) (hcell x hx)).1 (Fin.tail x)
    rwa [hx_cons] at this
  have hmB : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j2c W p x) ∈ Metric.cthickening εB K1 := fun x hx => by
    have := (hcB (x 0) (hcell x hx)).1 (Fin.tail x)
    rwa [hx_cons] at this
  have hmD : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j1c W p x) ∈ Metric.cthickening εD K1' := fun x hx => by
    have := (hcD (x 0) (hcell x hx)).1 (Fin.tail x)
    rwa [hx_cons] at this
  have hexK : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j2c Vf p x) ∈ K1 := fun x hx => by
    have := hK1m (x 0) (slab_of_cell hτ hj (hcell x hx)) (Fin.tail x)
    rwa [hx_cons] at this
  have hexK' : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j1c Vf p x) ∈ K1' := fun x hx => by
    have := hK1m' (x 0) (slab_of_cell hτ hj (hcell x hx)) (Fin.tail x)
    rwa [hx_cons] at this
  have hphysx : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      bosF SM z x = 0 ∧ dirF SM z x = 0 := fun x hx =>
    hphys x (slab_of_cell hτ hj (hcell x hx))
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun t ht => ?_⟩
  · have := (hcR (y 0) hy).1 (Fin.tail y)
    rwa [hx_cons] at this
  · -- the chart
    exact headChart_of_mem κ (hsubR (hmR y hy))
  · have hO' : IsOpen (openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)) :=
      isOpen_openSlab _ _
    have hsl : ∀ y : Fin 3 → ℝ, (Fin.cons t y : ST 3) ∈
        openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) := fun y => by
      show (j : ℝ) * τ < (Fin.cons t y : ST 3) 0 ∧ (Fin.cons t y : ST 3) 0 < ((j : ℝ) + 1) * τ
      simpa using ht
    have htI : t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) := ⟨ht.1.le, ht.2.le⟩
    have hCsq : ∀ a b : ℝ, 0 ≤ a → Real.sqrt a ≤ C → a * b ^ 2 ≤ (C * b) ^ 2 :=
      fun a b ha hac => by
        have := pow_le_pow_left₀ (Real.sqrt_nonneg a) hac 2
        rw [Real.sq_sqrt ha] at this
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right this (sq_nonneg b)
    have hs1 : Real.sqrt (256 * (KR * CE)) ≤ C := by
      rw [hC]; linarith [Real.sqrt_nonneg ((nB : ℝ) * (KB * CE)),
        Real.sqrt_nonneg ((nD : ℝ) * (KD * (10 * Cr ^ 2)))]
    have hs2 : Real.sqrt ((nB : ℝ) * (KB * CE)) ≤ C := by
      rw [hC]; linarith [Real.sqrt_nonneg (256 * (KR * CE)),
        Real.sqrt_nonneg ((nD : ℝ) * (KD * (10 * Cr ^ 2)))]
    have hs3 : Real.sqrt ((nD : ℝ) * (KD * (10 * Cr ^ 2))) ≤ C := by
      rw [hC]; linarith [Real.sqrt_nonneg (256 * (KR * CE)),
        Real.sqrt_nonneg ((nB : ℝ) * (KB * CE))]
    refine ⟨?_, ?_, ?_⟩
    · -- the Riemann tensor
      have hc : ∀ c : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q s (fun x =>
          riemR (hjF κ W x) c - riemR (hj2 z x) c) t ≤ KR * (CE * ε ^ 2) := by
        intro c
        refine le_of_eq_of_le (Q_congr_open hO' (fun x hx => ?_) hsl) ((hcR t htI).2 c)
        show riemR (hjF κ W x) c - riemR (hj2 z x) c =
          ΨR c (fun p => j2c W p x) - ΨR c (fun p => j2c Vf p x)
        rw [hΨRK c _ (hmR x hx), hΨRK c _ (Metric.self_subset_cthickening _ (hexK x hx)),
          hjF_eq κ hW x, hj2_eq_headJ κ SM z x]
      refine (Finset.sum_le_sum fun c _ => hc c).trans ?_
      rw [Finset.sum_const, Finset.card_univ]
      simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      have := hCsq (256 * (KR * CE)) ε (by positivity) hs1
      push_cast
      exact le_trans (le_of_eq (by ring)) this
    · -- the bosonic residual
      have hk : ∀ k, Q s (fun x => eB (bosR SM (hjF κ W x)) k) t ≤ KB * (CE * ε ^ 2) := by
        intro k
        refine le_of_eq_of_le (Q_congr_open hO' (fun x hx => ?_) hsl) ((hcB t htI).2 k)
        show eB (bosR SM (hjF κ W x)) k =
          ΨB k (fun p => j2c W p x) - ΨB k (fun p => j2c Vf p x)
        rw [hΨBK k _ (hmB x hx), hΨBK k _ (Metric.self_subset_cthickening _ (hexK x hx)),
          ← hj2_eq_headJ κ SM z x, bosR_hj2, (hphysx x hx).1, map_zero, Pi.zero_apply,
          sub_zero, hjF_eq κ hW x]
      refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have := hCsq ((nB : ℝ) * (KB * CE)) ε (by positivity) hs2
      exact le_trans (le_of_eq (by ring)) this
    · -- the Dirac residual
      have hk : ∀ k, Q (s + 1) (fun x => eD (GenResMaps.dirR SM (hjF κ W x)) k) t ≤
          KD * ED := by
        intro k
        refine le_of_eq_of_le (Q_congr_open hO' (fun x hx => ?_) hsl) ((hcD t htI).2 k)
        show eD (GenResMaps.dirR SM (hjF κ W x)) k =
          ΨD k (fun p => j1c W p x) - ΨD k (fun p => j1c Vf p x)
        have hex : GenResMaps.dirR SM (head1J κ (fun p => j1c Vf p x)) = 0 := by
          rw [← dirR_hjF κ SM hV x, hjF_eq κ hV x, ← hj2_eq_headJ κ SM z x, dirR_hj2,
            (hphysx x hx).2]
        rw [hΨDK k _ (hmD x hx), hΨDK k _ (Metric.self_subset_cthickening _ (hexK' x hx)),
          hex, map_zero, Pi.zero_apply, sub_zero, dirR_hjF κ SM hW x]
      refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have := hCsq ((nD : ℝ) * (KD * (10 * Cr ^ 2))) ε₂ (by positivity) hs3
      rw [hED]
      exact le_trans (le_of_eq (by ring)) this

end RenewalGeometry.GenReadout
