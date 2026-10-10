/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCellBulk
import RenewalGeometry.Continuum.GeneratedReadoutHeads

/-!
# The first variation of `S^{(1)}` on a record cell

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics` (stationarity of the
composite action): on one time cell `[a, b] × 𝕋³` on which the head metric of a smooth periodic
coordinate family `W` (the Hermite record) is in the Lorentzian chart, the cell integral of the
first variation of the first-derivative Einstein–Yang–Mills–Higgs density `L^{(1)}` at the head
1-jet of `W` along the head 1-jet of a smooth periodic coordinate family `Y`:

* is a bulk term plus the difference of a time flux `fluxR` at the cell ends, where `fluxR` only
  depends on the head 1-jets of `W` and `Y` on the end slices (**`record_cell`**);
* the bulk term is bounded by `M √((b-a)B²) ‖Y‖_{L²(cell)}` whenever the bosonic readouts
  `Σ_k Q_s(e_B R_B(hjF W))_k ≤ B²` on the open cell and the head metric stays in a compact set
  `K_g` of nondegenerate metrics, with `M` depending only on `K_g` (through `exists_hom_bound`).

The proof extends the record cell to a global smooth tuple (`SlabLocal.exists_ext`), applies the
tuple identity `GenCellVar.cell_variation` and the residual form of its bulk rows
(`GenCellBulk.bulkT_eq`), and estimates by Cauchy–Schwarz on the cell.
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenRecCell

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite GenResMaps GenPhysIdFinal
  GenReadout EHJetVariation EHFieldVariation GenMatVar GenNoether GenFOGrav GenMatEuler GenFOAction
  GenCell GenCellVar GenCellBulk KatoGalerkin
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

/-! ### Head 1-jets and the time flux -/

/-- The head 1-jet `(g, ∂g; A, ∂A; H, ∂H)` of the head fields of a coordinate family. -/
def hjet1 (W : Fin n → ST 3 → ℝ) (x : ST 3) : HJ1 m V :=
  j1F (fun y => Lg κ (fun c => W c y)) (fun y => LA κ (fun c => W c y))
    (fun y => LH κ (fun c => W c y)) x

/-- The matter time flux `B^0 = Σ_δ⟨𝔉^{0δ}, X_δ⟩ + 2⟨𝔇^0, η⟩` on pairs of 1-jets. -/
def MFJ (SM : SMData (MatLie m) V S S') (j v : HJ1 m V) : ℝ :=
  ∑ δ, SM.ipG (DnJ (volM j.1.1) (ginvOf j.1.1) (Fm j.2.1.1 j.2.1.2) 0 δ) (v.2.1.1 δ) +
    2 * SM.ipV (DhJ (volM j.1.1) (ginvOf j.1.1) (ActualJetGauge.DH j.2.1.1 j.2.2.1 j.2.2.2) 0)
      v.2.2.1

/-- **The time flux of the first variation of `S^{(1)}` through the slice `t`**, as a function
of the head 1-jets of the record `W` and the variation `Y` on that slice. -/
def fluxR (SM : SMData (MatLie m) V S S') (W Y : Fin n → ST 3 → ℝ) (t : ℝ) : ℝ :=
  (1 / (2 * SM.κ)) * (sint (fun x => PFJ 0 (hjet1 κ W x).1 (hjet1 κ Y x).1) t -
    sint (fun x => fderiv ℝ (WJ 0) (hjet1 κ W x).1 (hjet1 κ Y x).1) t) -
  sint (fun x => MFJ SM (hjet1 (V := V) κ W x) (hjet1 κ Y x)) t

/-- The flux only sees the head 1-jets on the slice. -/
theorem fluxR_congr (SM : SMData (MatLie m) V S S') {W Y W' Y' : Fin n → ST 3 → ℝ} {t : ℝ}
    (hW : ∀ y : Fin 3 → ℝ, hjet1 (V := V) κ W (Fin.cons t y) = hjet1 κ W' (Fin.cons t y))
    (hY : ∀ y : Fin 3 → ℝ, hjet1 (V := V) κ Y (Fin.cons t y) = hjet1 κ Y' (Fin.cons t y)) :
    fluxR (V := V) κ SM W Y t = fluxR (V := V) κ SM W' Y' t := by
  unfold fluxR sint
  simp only [hW, hY]

/-- A variation with vanishing head 1-jet on the slice has no flux. -/
theorem fluxR_zero (SM : SMData (MatLie m) V S S') {W Y : Fin n → ST 3 → ℝ} {t : ℝ}
    (hY : ∀ y : Fin 3 → ℝ, hjet1 (V := V) κ Y (Fin.cons t y) = 0) :
    fluxR (V := V) κ SM W Y t = 0 := by
  unfold fluxR sint
  simp only [hY]
  have h1 : ∀ p : Met × (Fin 4 → Met), PFJ 0 p (0 : HJ1 m V).1 = 0 := fun p => by
    simp [PFJ, chrVar, ginvVar, chr, fluxV]
  have h3 : ∀ j : HJ1 m V, MFJ SM j 0 = 0 := fun j => by simp [MFJ]
  simp only [h1, h3, map_zero, ContinuousLinearMap.zero_apply]
  simp

/-! ### The chart is open -/

theorem isOpen_headChart : IsOpen {w : Fin n → ℝ | HeadChart (m := m) (V := V) (S := S) (S' := S') κ w} := by
  have hc : Continuous fun w : Fin n → ℝ =>
      ((((Lg κ w, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0), (0, 0)) : HJ2 m V S S')) := by
    fun_prop
  exact (isOpen_chartJ2 (m := m) (V := V) (S := S) (S' := S')).preimage hc

/-! ### Global extensions of a record cell -/

/-- The 1-jet of a tuple agreeing with the head fields near `x` is the head 1-jet there. -/
theorem j1F_of_near {W : Fin n → ST 3 → ℝ} {z' : Tuple m V S S'} {x : ST 3}
    (hg : z'.g =ᶠ[𝓝 x] fun y => Lg κ (fun c => W c y))
    (hA : z'.A =ᶠ[𝓝 x] fun y => LA κ (fun c => W c y))
    (hH : z'.H =ᶠ[𝓝 x] fun y => LH κ (fun c => W c y)) :
    j1F z'.g z'.A z'.H x = hjet1 κ W x := by
  unfold hjet1 j1F
  rw [hg.eq_of_nhds, hA.eq_of_nhds, hH.eq_of_nhds]
  have e1 : ∀ α, pd z'.g α x = pd (fun y => Lg κ (fun c => W c y)) α x := fun α =>
    (SlabLocal.pd_eventuallyEq hg α).eq_of_nhds
  have e3 : ∀ α, pd z'.A α x = pd (fun y => LA κ (fun c => W c y)) α x := fun α =>
    (SlabLocal.pd_eventuallyEq hA α).eq_of_nhds
  have e5 : ∀ α, pd z'.H α x = pd (fun y => LH κ (fun c => W c y)) α x := fun α =>
    (SlabLocal.pd_eventuallyEq hH α).eq_of_nhds
  simp only [e1, e3, e5]

/-- The matter flux of a tuple is the jet flux `MFJ` of its 1-jets. -/
theorem matFlux_eq_MFJ (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
    (X : ST 3 → Fin 4 → MatLie m) (η : ST 3 → V) (k : ST 3 → Met) (x : ST 3) :
    matFlux z SM X η 0 x = MFJ SM (j1F z.g z.A z.H x) (j1F k X η x) := by
  unfold matFlux MFJ
  simp only [← DnJ_eq_dens, ← DhJ_eq_densH]
  rfl

/-- **Extension of a record cell**: if the head metric of `W` is in the chart on the closed cell,
there is a global smooth tuple whose fields agree with the head fields of `W` near every point of
the closed cell. -/
theorem exists_cell_ext {W : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c))
    (hWp : ∀ c, IsSPeriodic (W c)) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ x : ST 3, x 0 ∈ Icc a b → HeadChart κ (fun c => W c x)) :
    ∃ z' : Tuple m V S S', ∀ x : ST 3, x 0 ∈ Icc a b →
      z'.g =ᶠ[𝓝 x] (fun y => Lg κ (fun c => W c y)) ∧ z'.A =ᶠ[𝓝 x] (fun y => LA κ (fun c => W c y)) ∧
      z'.H =ᶠ[𝓝 x] (fun y => LH κ (fun c => W c y)) ∧ z'.ψ =ᶠ[𝓝 x] (fun y => Lψ κ (fun c => W c y)) ∧
      z'.ψb =ᶠ[𝓝 x] (fun y => Lψb κ (fun c => W c y)) := by
  have hj : Continuous (fun x : ST 3 => fun c => W c x) := continuous_pi fun c => (hW c).continuous
  have hjp : IsSPeriodic (fun x : ST 3 => fun c => W c x) := fun k x => by
    funext c; exact hWp c k x
  obtain ⟨σ, hσ, hmar⟩ := GenCellVar.exists_line_margin (v := fun _ => (0 : Fin n → ℝ)) hj
    continuous_const hjp (fun _ _ => rfl) (isOpen_headChart (m := m) (V := V) (S := S) (S' := S') κ)
    hab hc
  have hc' : ∀ y ∈ openSlab (a - σ) (b + σ), HeadChart (m := m) (V := V) (S := S) (S' := S') κ
      (fun c => W c y) := fun y hy => by
    have := hmar 0 ⟨by linarith, hσ.le⟩ y ⟨hy.1.le, hy.2.le⟩
    simpa using this
  set L := recTuple (m := m) (V := V) (S := S) (S' := S') κ W hW hWp hc' with hL
  obtain ⟨z', hz'⟩ := SlabLocal.exists_ext L (c := a - σ / 2) (d := b + σ / 2) (by linarith)
    (by linarith) (by linarith)
  refine ⟨z', fun x hx => hz' x ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩

/-! ### Cauchy–Schwarz on a cell -/

section CS

theorem norm_le_sqrt_sum_sq {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    ‖c‖ ≤ Real.sqrt (∑ i, c i ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => c i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ i))

theorem cellInt_mono_cell {f g : ST 3 → ℝ} (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (hab : a ≤ b) (h : ∀ x : ST 3, x 0 ∈ Icc a b → f x ≤ g x) : cellInt a b f ≤ cellInt a b g := by
  unfold cellInt
  refine intervalIntegral.integral_mono_on hab (intervalIntegrable_sint hf a b)
    (intervalIntegrable_sint hg a b) fun t ht => ?_
  unfold sint
  exact integral_mono (integrableOn_slice hf t) (integrableOn_slice hg t)
    fun y => h _ (by simpa using ht)

/-- **Cauchy–Schwarz on a cell** for a pointwise product bound. -/
theorem abs_cellInt_le {F f h : ST 3 → ℝ} (hF : Continuous F) (hf : Continuous f)
    (hh : Continuous h) {M a b : ℝ} (hM : 0 ≤ M) (hab : a ≤ b)
    (hb : ∀ x : ST 3, x 0 ∈ Icc a b → |F x| ≤ M * (f x * h x)) :
    |cellInt a b F| ≤ M * (Real.sqrt (cellInt a b (fun x => f x ^ 2)) *
      Real.sqrt (cellInt a b (fun x => h x ^ 2))) := by
  have hc : Continuous fun x => M * (f x * h x) := continuous_const.mul (hf.mul hh)
  have h1 : cellInt a b F ≤ cellInt a b (fun x => M * (f x * h x)) :=
    cellInt_mono_cell hF hc hab fun x hx => (le_abs_self _).trans (hb x hx)
  have h2 : cellInt a b (fun x => (-1) * F x) ≤ cellInt a b (fun x => M * (f x * h x)) :=
    cellInt_mono_cell (f := fun x => (-1) * F x) (continuous_const.mul hF) hc hab fun x hx => by
      show (-1) * F x ≤ M * (f x * h x)
      have := hb x hx
      have := neg_abs_le (F x)
      linarith
  rw [cellInt_smul] at h1 h2
  rw [cellInt_smul] at h2
  have hCS := cellInt_mul_sq_le hf hh hab
  have h3 : cellInt a b (fun x => f x * h x) ≤
      Real.sqrt (cellInt a b (fun x => f x ^ 2)) * Real.sqrt (cellInt a b (fun x => h x ^ 2)) := by
    rw [← Real.sqrt_mul (cellInt_nonneg (fun x => sq_nonneg (f x)) hab)]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hCS)
  rw [abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left h3 hM
    linarith
  · have := mul_le_mul_of_nonneg_left h3 hM
    linarith

end CS

/-! ### The record cell -/

set_option maxHeartbeats 2000000 in
/-- **The first variation of `S^{(1)}` on a record cell** (variational smooth theory data,
`κ ≠ 0`): bulk plus end fluxes, with the bulk bounded through the bosonic readouts. -/
theorem record_cell (SM : SMData (MatLie m) V S S') (hS : SMSmooth SM)
    (hV : GenStress.VariationalStress SM) (hκ : SM.κ ≠ 0) {W Y : Fin n → ST 3 → ℝ}
    (hW : ∀ c, ContDiff ℝ ∞ (W c)) (hWp : ∀ c, IsSPeriodic (W c))
    (hY : ∀ c, ContDiff ℝ ∞ (Y c)) (hYp : ∀ c, IsSPeriodic (Y c)) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ x : ST 3, x 0 ∈ Icc a b → HeadChart κ (fun c => W c x))
    {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) (eBs : (Fin nB → ℝ) →L[ℝ] BosP m V)
    (heB : ∀ r, eBs (eB r) = r) {Kg : Set Met} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ g ∈ Kg, ∀ (c : Fin nB → ℝ) (y : Fin n → ℝ),
      |bulkJ SM g (eBs c) (Lg κ y) (LA κ y) (LH κ y)| ≤ M * ‖c‖ * ‖y‖)
    (hKg : ∀ x : ST 3, x 0 ∈ Icc a b → Lg κ (fun c => W c x) ∈ Kg) {s : ℕ} {B : ℝ}
    (hB : ∀ t ∈ Ioo a b, ∑ k, Q s (fun x => eB (bosR SM (hjF κ W x)) k) t ≤ B ^ 2) :
    ∃ D : ℝ, cellInt a b (fun x => fderiv ℝ (L1SM SM) (hjet1 κ W x) (hjet1 κ Y x)) =
        D + (fluxR (V := V) κ SM W Y b - fluxR (V := V) κ SM W Y a) ∧
      |D| ≤ M * (Real.sqrt ((b - a) * B ^ 2) *
        Real.sqrt (cellInt a b (fun x => ∑ c, Y c x ^ 2))) := by
  obtain ⟨z', hz'⟩ := exists_cell_ext (m := m) (V := V) (S := S) (S' := S') κ hW hWp hab hc
  have hYv : ContDiff ℝ ∞ (fun x => fun c => Y c x) := contDiff_pi.2 hY
  set kY : ST 3 → Met := fun x => Lg κ (fun c => Y c x) with hkY
  set XY : ST 3 → Fin 4 → MatLie m := fun x => LA κ (fun c => Y c x) with hXY
  set ηY : ST 3 → V := fun x => LH κ (fun c => Y c x) with hηY
  have hk : ContDiff ℝ ∞ kY := (Lg κ).contDiff.comp hYv
  have hX : ContDiff ℝ ∞ XY := (LA κ).contDiff.comp hYv
  have hη : ContDiff ℝ ∞ ηY := (LH κ).contDiff.comp hYv
  have hks : ∀ y μ ν, kY y μ ν = kY y ν μ := fun y μ ν => symL_symm _ μ ν
  have hkp : IsSPeriodic kY := fun k x => by simp only [hkY, hYp _ k x]
  have hXp : IsSPeriodic XY := fun k x => by simp only [hXY, hYp _ k x]
  have hηp : IsSPeriodic ηY := fun k x => by simp only [hηY, hYp _ k x]
  have hcv := cell_variation SM hV z' hk hks hkp hX hXp hη hηp hab
  -- the jets on the closed cell
  have hj1 : ∀ x : ST 3, x 0 ∈ Icc a b → j1F z'.g z'.A z'.H x = hjet1 κ W x := fun x hx => by
    obtain ⟨h1, h2, h3, -, -⟩ := hz' x hx
    exact j1F_of_near κ h1 h2 h3
  have hjY : ∀ x, j1F kY XY ηY x = hjet1 κ Y x := fun x => rfl
  have hsl : ∀ t ∈ Icc a b, ∀ y : Fin 3 → ℝ, (Fin.cons t y : ST 3) 0 ∈ Icc a b := fun t ht y => by
    simpa using ht
  have hL : cellInt a b (fun x => fderiv ℝ (L1SM SM) (hjet1 κ W x) (hjet1 κ Y x)) =
      cellInt a b (fun x => fderiv ℝ (L1SM SM) (j1F z'.g z'.A z'.H x) (j1F kY XY ηY x)) :=
    cellInt_congr hab fun t ht y _ => by rw [hj1 _ (hsl t ht y), hjY]
  have hfl : ∀ t ∈ Icc a b, fluxT SM z' kY XY ηY t = fluxR (V := V) κ SM W Y t := by
    intro t ht
    unfold fluxT fluxR
    have e1 : ∀ y : Fin 3 → ℝ, PFJ 0 (j1M z'.g (Fin.cons t y)) (j1M kY (Fin.cons t y)) =
        PFJ 0 (hjet1 κ W (Fin.cons t y)).1 (hjet1 κ Y (Fin.cons t y)).1 := fun y => by
      rw [← hj1 _ (hsl t ht y)]; rfl
    have e2 : ∀ y : Fin 3 → ℝ, fderiv ℝ (WJ 0) (j1M z'.g (Fin.cons t y)) (j1M kY (Fin.cons t y)) =
        fderiv ℝ (WJ 0) (hjet1 κ W (Fin.cons t y)).1 (hjet1 κ Y (Fin.cons t y)).1 := fun y => by
      rw [← hj1 _ (hsl t ht y)]; rfl
    have e3 : ∀ y : Fin 3 → ℝ, matFlux z' SM XY ηY 0 (Fin.cons t y) =
        MFJ SM (hjet1 κ W (Fin.cons t y)) (hjet1 κ Y (Fin.cons t y)) := fun y => by
      rw [matFlux_eq_MFJ SM z' XY ηY kY, hj1 _ (hsl t ht y), hjY]
    unfold sint
    simp only [e1, e2, e3]
  refine ⟨cellInt a b (bulkT SM z' kY XY ηY), ?_, ?_⟩
  · rw [hL, hcv, hfl a ⟨le_rfl, hab⟩, hfl b ⟨hab, le_rfl⟩]
  -- the bound
  have hbF : Continuous (bosF SM z') := (contDiff_bosF SM z' hS).continuous
  have hB' : ∀ x : ST 3, x 0 ∈ Icc a b → bosF SM z' x = bosR SM (hjF κ W x) := fun x hx => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hz' x hx
    rw [← bosR_hj2 z' x SM, hj2_of_near κ h1 h2 h3 h4 h5]
  have hg' : ∀ x : ST 3, x 0 ∈ Icc a b → z'.g x = Lg κ (fun c => W c x) := fun x hx =>
    (hz' x hx).1.eq_of_nhds
  set f : ST 3 → ℝ := fun x => Real.sqrt (∑ k, eB (bosF SM z' x) k ^ 2) with hf
  set h : ST 3 → ℝ := fun x => Real.sqrt (∑ c, Y c x ^ 2) with hh
  have hfc : Continuous f := Real.continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
    (((continuous_apply k).comp (eB.continuous.comp hbF))).pow 2)
  have hhc : Continuous h := Real.continuous_sqrt.comp (continuous_finsetSum _ fun c _ =>
    (hY c).continuous.pow 2)
  have hT : ∀ x, bulkT SM z' kY XY ηY x = bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x) :=
    fun x => bulkT_eq SM hV hκ z' kY XY ηY x
  have hTc : Continuous (bulkT SM z' kY XY ηY) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hp : Continuous fun x : ST 3 => (z'.g x, bosF SM z' x, (kY x, XY x, ηY x)) :=
      z'.g_smooth.continuous.prodMk (hbF.prodMk (hk.continuous.prodMk (hX.continuous.prodMk
        hη.continuous)))
    have := ContinuousAt.comp (x := x)
      (g := fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
        bulkJ SM q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
      (f := fun x : ST 3 => (z'.g x, bosF SM z' x, (kY x, XY x, ηY x)))
      (continuousAt_bulkJ SM (p := (z'.g x, bosF SM z' x, (kY x, XY x, ηY x)))
      (GenCell.Tuple_det_neg z' x).ne) hp.continuousAt
    exact this.congr (Filter.Eventually.of_forall fun y => (hT y).symm)
  have hpt : ∀ x : ST 3, x 0 ∈ Icc a b → |bulkT SM z' kY XY ηY x| ≤ M * (f x * h x) := by
    intro x hx
    rw [hT x, hg' x hx, ← heB (bosF SM z' x)]
    have h1 := hM _ (hKg x hx) (eB (bosF SM z' x)) (fun c => Y c x)
    have h2 := norm_le_sqrt_sum_sq (eB (bosF SM z' x))
    have h3 := norm_le_sqrt_sum_sq (fun c => Y c x)
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (norm_nonneg _) (Real.sqrt_nonneg _)) hM0
  have hmain := abs_cellInt_le hTc hfc hhc hM0 hab hpt
  have hf2 : (fun x => f x ^ 2) = fun x => ∑ k, eB (bosF SM z' x) k ^ 2 := by
    funext x; rw [hf]; exact Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hh2 : (fun x => h x ^ 2) = fun x => ∑ c, Y c x ^ 2 := by
    funext x; rw [hh]; exact Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)
  have hfI : cellInt a b (fun x => f x ^ 2) ≤ (b - a) * B ^ 2 := by
    rw [hf2]
    have hc2 : ∀ k, Continuous fun x => eB (bosF SM z' x) k ^ 2 := fun k =>
      ((continuous_apply k).comp (eB.continuous.comp hbF)).pow 2
    refine cellInt_le_of_slices (continuous_finsetSum _ fun k _ => hc2 k) hab fun t ht => ?_
    rw [sint_sum _ hc2]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hB t ht)
    have e : sint (fun x => eB (bosF SM z' x) k ^ 2) t =
        ∫ y in Icc (0 : Fin 3 → ℝ) 1, (eB (bosR SM (hjF κ W (Fin.cons t y))) k) ^ 2 := by
      unfold sint
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      rw [hB' _ (hsl t ⟨ht.1.le, ht.2.le⟩ y)]
    rw [e]
    exact integral_sq_le_Q s (fun x => eB (bosR SM (hjF κ W x)) k) t
  rw [hh2] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt hfI) (Real.sqrt_nonneg _)) hM0)

end RenewalGeometry.GenRecCell
