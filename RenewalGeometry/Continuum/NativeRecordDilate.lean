/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeRecordRows
import RenewalGeometry.Continuum.NativeTailTransferBounds

/-!
# From native records on the `2π` grid to actual field tuples of the slab model

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` (the record → tuple map
of the composition plan: the complete trigonometric reconstruction `z_h = 𝓘_h^trig u_h` of a
record on the odd periodic grid of side `2π`, in the adapted Lorentz gauge and temporal internal
gauge, is mapped to the unit-period slab by the dilation `ξ = 2πx + t₀e₀`).

## Main results

* `recon_clm` (generic) — the trigonometric reconstruction commutes with continuous linear maps.
* `isZPeriodic_of_single` (generic) — single-step periodicity implies lattice periodicity.
* `NodalGauge` — the nodal gauge conditions of a record: adapted Lorentz gauge (lower-triangular
  coframes with positive diagonal), temporal internal gauge `A₀ = 0`, gauge potential in the gauge
  Lie subspace, physical co-spinors; they propagate to the reconstruction
  (`recon_adapted`, `recon_temporal`, `recon_gauge`, `recon_clin`; positivity of the diagonal by
  connectedness).
* `dilField` — the dilated tensorial field `x ↦ Φ_{2π}(z_h(2πx + t₀e₀))`; **`tupleHyp_dil`** — it
  satisfies `RecordTuple.TupleHyp`, so it has an actual field tuple `RecordTuple.toTuple`.
* **`bosF_dil`**, **`dirF_dil`** — the slab residuals of that tuple are `NB(e_h(ξ))𝓡_B(z_h)(ξ)`
  and `ND(e_h(ξ))𝓡_D(z_h)(ξ)` with continuous linear maps `NB(e)`, `ND(e)` depending smoothly on
  the coframe value only (`contDiffOn_NB`, `contDiffOn_ND`).
-/

open Finset Set
open scoped Matrix ContDiff Real

namespace RenewalGeometry.RecordTuple

open SobolevOpen (pd)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open NativeScaling (Mat eta metric readerOmega readerG)
open NativeDensity NativeModel NativeFrameBridge NativeBosonicEuler NativeDiracEuler PalatiniEuler
open ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetFrame SlabData SpinorProlongation
open HarmonicDefect NativeStressEuler NativeTail ActualJetState ActualJetCompleteForcing
open FieldScaling
open TrigInterp (recon reconLow tau gpos)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Generic lemmas -/

section Generic

variable {d : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **The reconstruction commutes with continuous linear maps.** -/
theorem recon_clm {n : ℕ} [NeZero n] (L : V →L[ℝ] W) (u : (Fin d → ZMod n) → V) (x : Fin d → ℝ) :
    L (TrigInterp.recon n u x) = TrigInterp.recon n (fun y => L (u y)) x := by
  unfold TrigInterp.recon VecTrig.tp TrigInterp.coefOf
  simp only [map_sum, map_add, map_smul]

/-- Single-step periodicity with period `L` in every coordinate implies periodicity under
`L ℤ^ι`. -/
theorem isZPeriodic_of_single {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    {f : (ι → ℝ) → α} {L : ℝ} (hf : ∀ x μ, f (x + Pi.single μ L) = f x) (k : ι → ℤ)
    (x : ι → ℝ) : f (x + L • PeriodicCube.zvec k) = f x := by
  have h1 : ∀ (m : ℤ) (μ : ι) (x : ι → ℝ), f (x + m • Pi.single μ L) = f x := by
    intro m μ
    induction m using Int.induction_on with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [add_zsmul, one_zsmul, ← add_assoc, hf, ih]
    | pred i ih =>
      intro x
      calc f (x + (-(i : ℤ) - 1) • (Pi.single μ L : ι → ℝ))
          = f (x + (-(i : ℤ) - 1) • (Pi.single μ L : ι → ℝ) + Pi.single μ L) := (hf _ _).symm
        _ = f (x + (-(i : ℤ)) • (Pi.single μ L : ι → ℝ)) := by
          congr 1
          rw [add_assoc, ← add_one_zsmul]
          congr 2
          ring
        _ = f x := ih x
  have hsum : L • PeriodicCube.zvec k = ∑ μ, k μ • Pi.single μ L := by
    funext i
    simp [PeriodicCube.zvec, Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hsum]
  have h2 : ∀ s : Finset ι, ∀ x, f (x + ∑ μ ∈ s, k μ • Pi.single μ L) = f x := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | insert a s ha ih =>
      intro x
      rw [Finset.sum_insert ha]
      have e : x + (k a • (Pi.single a L : ι → ℝ) + ∑ μ ∈ s, k μ • (Pi.single μ L : ι → ℝ)) =
          (x + ∑ μ ∈ s, k μ • (Pi.single μ L : ι → ℝ)) + k a • (Pi.single a L : ι → ℝ) := by abel
      rw [e, h1, ih]
  exact h2 _ x

end Generic

theorem recon_zero {d n : ℕ} [NeZero n] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : Fin d → ℝ) : TrigInterp.recon n (fun _ : Fin d → ZMod n => (0 : V)) x = 0 := by
  unfold TrigInterp.recon VecTrig.tp TrigInterp.coefOf
  simp

/-- If a continuous linear functional vanishes at every node, it vanishes on the
reconstruction. -/
theorem recon_clm_eq_zero {d n : ℕ} [NeZero n] {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    {u : (Fin d → ZMod n) → V} (hu : ∀ y, L (u y) = 0) (x : Fin d → ℝ) :
    L (TrigInterp.recon n u x) = 0 := by
  rw [recon_clm]
  simp only [hu]
  exact recon_zero x

/-! ### Nodal gauge conditions and their propagation to the reconstruction -/

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- **The nodal gauge conditions** of a record: adapted Lorentz gauge (lower-triangular coframes
with positive diagonal), temporal internal gauge, gauge potential in the gauge Lie subspace,
physical (`ℂ`-linear) co-spinors. -/
structure NodalGauge {n : ℕ} (u : (Fin 4 → ZMod n) → Field 𝔄 𝓗 𝓢) : Prop where
  adapted : ∀ y, IsAdaptedCoframe (u y).1
  temporal : ∀ y, (u y).2.1 0 = 0
  gauge : ∀ y μ, (u y).2.1 μ ∈ M.gSub
  clin : ∀ y, IsCLin M.toModel (u y).2.2.2.2

variable {M}
variable {n : ℕ} [NeZero n] {u : (Fin 4 → ZMod n) → Field 𝔄 𝓗 𝓢}

/-- The coframe entry functional. -/
def entryL (a μ : Fin 4) : Field 𝔄 𝓗 𝓢 →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ a μ).toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢))

theorem recon_lower (hu : NodalGauge M u) (x : R4) (a μ : Fin 4) (h : a < μ) :
    (TrigInterp.recon n u x).1 a μ = 0 :=
  recon_clm_eq_zero (entryL (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) a μ)
    (fun y => by show (u y).1 a μ = 0; exact (hu.adapted y).1 a μ h) x

theorem recon_temporal (hu : NodalGauge M u) (x : R4) : (TrigInterp.recon n u x).2.1 0 = 0 :=
  recon_clm_eq_zero (projAμ (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) 0)
    (fun y => hu.temporal y) x

theorem recon_gauge (hu : NodalGauge M u) (x : R4) (μ : Fin 4) :
    (TrigInterp.recon n u x).2.1 μ ∈ M.gSub := by
  by_contra hx
  obtain ⟨f, hf, hfp⟩ := M.gSub.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hf0 : ∀ y ∈ M.gSub, f y = 0 := fun y hy => by
    have : f y ∈ M.gSub.map f := Submodule.mem_map_of_mem hy
    rw [hfp] at this
    exact (Submodule.mem_bot ℝ).1 this
  set L : Field 𝔄 𝓗 𝓢 →L[ℝ] ℝ :=
    (LinearMap.toContinuousLinearMap f).comp (projAμ (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) μ)
  have := recon_clm_eq_zero L (u := u) (fun y => hf0 _ (hu.gauge y μ)) x
  exact hf this

theorem recon_clin (hu : NodalGauge M u) (x : R4) :
    IsCLin M.toModel (TrigInterp.recon n u x).2.2.2.2 := by
  rw [isCLin_iff_defect]
  exact recon_clm_eq_zero ((clinDefect M.toModel).comp (projψb (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)))
    (fun y => (isCLin_iff_defect M.toModel _).1 (hu.clin y)) x

theorem recon_diag_ne (hu : NodalGauge M u) {Ke : Set Mat} (hdet : ∀ e ∈ Ke, 0 < e.det)
    (hK : ∀ x, (TrigInterp.recon n u x).1 ∈ Ke) (x : R4) (a : Fin 4) :
    (TrigInterp.recon n u x).1 a a ≠ 0 := by
  intro h0
  have hl : Matrix.BlockTriangular (TrigInterp.recon n u x).1 OrderDual.toDual :=
    fun i j hij => recon_lower hu x i j hij
  have hd := hdet _ (hK x)
  rw [Matrix.det_of_lowerTriangular _ hl] at hd
  have hz := Finset.prod_eq_zero (s := Finset.univ)
    (f := fun i => (TrigInterp.recon n u x).1 i i) (Finset.mem_univ a) h0
  rw [hz] at hd
  exact lt_irrefl 0 hd

/-- **Adaptedness of the reconstruction** (positive diagonal by connectedness). -/
theorem recon_adapted (hn : Odd n) (hu : NodalGauge M u) {Ke : Set Mat}
    (hdet : ∀ e ∈ Ke, 0 < e.det) (hK : ∀ x, (TrigInterp.recon n u x).1 ∈ Ke) (x : R4) :
    IsAdaptedCoframe (TrigInterp.recon n u x).1 := by
  refine ⟨fun a μ h => recon_lower hu x a μ h, fun a => ?_⟩
  set p : R4 := gpos n (0 : Fin 4 → ZMod n)
  have hp : 0 < (TrigInterp.recon n u p).1 a a := by
    rw [TrigInterp.recon_gpos n hn]
    exact (hu.adapted 0).2 a
  set f : ℝ → ℝ := fun t => (TrigInterp.recon n u (p + t • (x - p))).1 a a with hf
  have hfc : Continuous f := by
    have := (contDiff_recon (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) u).continuous
    have h2 : Continuous fun t : ℝ => p + t • (x - p) := by fun_prop
    exact (entryL (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) a a).continuous.comp (this.comp h2)
  by_contra hneg
  rw [not_lt] at hneg
  have h0 : f 0 > 0 := by simpa [hf] using hp
  have h1 : f 1 ≤ 0 := by simpa [hf] using hneg
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hfc.continuousOn
    ⟨h1, h0.le⟩
  exact recon_diag_ne hu hdet hK _ a ht

/-! ### The dilated field and its actual tuple -/

theorem two_pi_ne : (2 * π : ℝ) ≠ 0 := by positivity

theorem two_pi_pos : (0 : ℝ) < 2 * π := by positivity

/-- **The dilated native field** `x ↦ Φ_{2π}(Y(2πx + t₀e₀))` on the unit-period slab
coordinates. -/
def dilField (t₀ : ℝ) (Y : R4 → Field 𝔄 𝓗 𝓢) : R4 → Field 𝔄 𝓗 𝓢 :=
  dilateF (fieldScale two_pi_ne) (2 * π) (Pi.single 0 t₀) Y

theorem dilField_apply (t₀ : ℝ) (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) :
    dilField t₀ Y x = fieldScale two_pi_ne (Y ((2 * π) • x + Pi.single 0 t₀)) := rfl

theorem sshift_eq_zvec (k : Fin 3 → ℤ) :
    (SymHypEnergy.sshift k : R4) = PeriodicCube.zvec (Fin.cons 0 k : Fin 4 → ℤ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [SymHypEnergy.sshift, PeriodicCube.zvec]
  | succ j => simp [SymHypEnergy.sshift, PeriodicCube.zvec]

theorem recon_lattice (u : (Fin 4 → ZMod n) → Field 𝔄 𝓗 𝓢) (k : Fin 4 → ℤ) (z : R4) :
    TrigInterp.recon n u (z + (2 * π) • PeriodicCube.zvec k) = TrigInterp.recon n u z :=
  isZPeriodic_of_single (fun x μ => TrigInterp.recon_periodic n u x μ) k z

theorem dil_shift (t₀ : ℝ) (u : (Fin 4 → ZMod n) → Field 𝔄 𝓗 𝓢) (k : Fin 4 → ℤ) (x : R4) :
    dilField t₀ (TrigInterp.recon n u) (x + PeriodicCube.zvec k) =
      dilField t₀ (TrigInterp.recon n u) x := by
  rw [dilField_apply, dilField_apply]
  congr 1
  rw [smul_add, add_right_comm, recon_lattice]

/-- **The dilated reconstruction of a record in the nodal gauges satisfies the tuple
hypotheses**, provided the scaled coframe chart lies in the margin `δ`. -/
theorem tupleHyp_dil (hn : Odd n) (hu : NodalGauge M u) {Ke : Set Mat}
    (hdet : ∀ e ∈ Ke, 0 < e.det) (hK : ∀ x, (TrigInterp.recon n u x).1 ∈ Ke) {δ : ℝ}
    (hmarg : ∀ e ∈ Ke, IsAdaptedCoframe e →
      Margin δ (ginvOf (fun i j => metric ((2 * π) • e) i j))) (t₀ : ℝ) :
    TupleHyp M δ (dilField t₀ (TrigInterp.recon n u)) where
  smooth := (fieldScale (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) two_pi_ne).contDiff.comp
    ((contDiff_recon u).comp ((contDiff_const_smul (2 * π)).add contDiff_const))
  per k x := by
    rw [sshift_eq_zvec]
    exact dil_shift t₀ u _ x
  perL k x := by
    show eF _ ((1 : ℝ) • (x + PeriodicCube.zvec k)) = eF _ ((1 : ℝ) • x)
    rw [one_smul, one_smul]
    unfold eF
    rw [dil_shift]
  adapted x := by
    have ha := recon_adapted hn hu hdet hK ((2 * π) • x + Pi.single 0 t₀)
    rw [dilField_apply, fieldScale_apply]
    refine ⟨fun a μ h => ?_, fun a => ?_⟩
    · simp [ha.1 a μ h]
    · simpa using mul_pos two_pi_pos (ha.2 a)
  margin x := by
    have ha := recon_adapted hn hu hdet hK ((2 * π) • x + Pi.single 0 t₀)
    exact hmarg _ (hK _) ha
  temporal x := by
    rw [dilField_apply, fieldScale_apply]
    simp [recon_temporal hu]
  gauge x μ := by
    rw [dilField_apply, fieldScale_apply, ← M.gLie_eq]
    exact M.gSub.smul_mem _ (recon_gauge hu _ μ)
  clin x := by
    rw [dilField_apply, fieldScale_apply]
    exact recon_clin hu _

end

end RenewalGeometry.RecordTuple
