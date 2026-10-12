/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.GeneratedChartSmooth
import MathPhys.FieldTheory.Continuum.GeneratedPhysicalIdentificationClosed
import MathPhys.FieldTheory.Continuum.GeneratedPhysicalIdentificationFinal
import MathPhys.FieldTheory.Continuum.GeneratedDefiningJetPropagation
import MathPhys.FieldTheory.Continuum.GeneratedHiggsDefect
import MathPhys.FieldTheory.Continuum.GeneratedCoupledMatter
import MathPhys.FieldTheory.Continuum.GeneratedCoupledKato

/-!
# Chart-local smoothness of the sources: propagation and the coupled Kato realization

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(back-reacting charged spinors).  The propagation layer of the coupled identification re-proved
under `GenChL.SMSmoothL` (suffix `L`, statements identical up to `SMSmooth ↦ SMSmoothL`): the
metric defect propagation and its forcing estimate, the metric and Higgs sectors of the defect
system, the slice derivative identity, the symmetric system on a constrained slice, Gauss
propagation with matter, `∇T = 0` for coupled solutions and the coupled modified Kato realization.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! #### `symEqAt_of_sliceConstrained` (from `Continuum/GeneratedPhysicalIdentificationClosed.lean`) -/
namespace MathPhys.GenPhysIdClosed.ChL
open Filter Topology Set
open scoped BigOperators ContDiff
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk QLEnergy KatoGalerkin FrameCurvature HarmonicDefect
  ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge
  ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenNoether
  GenGauss GenStress GenHarmonic GenPhysId
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
/-- A slice-constrained tuple satisfies the symmetric system on the slice. -/
theorem symEqAt_of_sliceConstrainedL (hS : GenChL.SMSmoothL SM) {z₀ : Tuple m V S S'}
    (h : SliceConstrained SM z₀) (y : Fin 3 → ℝ) : SymEqAt SM z₀ (Fin.cons 0 y) := by
  rw [symEqAt_iff]
  obtain ⟨hB, hD, hC, hdC⟩ := h y
  have hdD : ∀ j : Fin 3, pd (dirF SM z₀) j.succ (Fin.cons 0 y) = 0 := fun j =>
    zero_on_slice_pd (contDiff_dirF SM z₀) (fun y' => (h y').2.1) rfl j
  have hdCs : ∀ j : Fin 3, pd (CF z₀) j.succ (Fin.cons 0 y) = 0 := fun j =>
    zero_on_slice_pd (contDiff_CF z₀) (fun y' => (h y').2.2.1) rfl j
  unfold errF
  rw [hB, hD, hC, hdC]
  simp only [hdD, hdCs, map_zero, add_zero, Finset.sum_const_zero]
end MathPhys.GenPhysIdClosed.ChL

/-! #### `slice_pd_eq` (from `Continuum/GeneratedPhysicalIdentificationFinal.lean`) -/
namespace MathPhys.GenPhysIdFinal.ChL
open Filter Topology Set
open scoped BigOperators ContDiff NNReal
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk QLEnergy KatoGalerkin FrameCurvature HarmonicDefect
  ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge
  ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}
variable (SM) in
/-- **All first derivatives of a solution of the shift-transported system agree on the initial
slice with those of a slice-constrained tuple with the same data** (spatial derivatives from the
data, the time derivative from the rows: the constrained tuple satisfies the system on the
slice). -/
theorem slice_pd_eqL (hS : GenChL.SMSmoothL SM) {W : ST 3 → StateP m V S S'} {z₀ : Tuple m V S S'}
    {O : Set (ST 3)} (hO : IsOpen O) (hW : ContDiffOn ℝ 1 W O)
    (hC₀ : GenPhysIdClosed.SliceConstrained SM z₀)
    (hdat : ∀ y, W (Fin.cons 0 y) = stateF SM z₀ (Fin.cons 0 y)) {y : Fin 3 → ℝ}
    (hy : (Fin.cons 0 y : ST 3) ∈ O)
    (hrow : pd W 0 (Fin.cons 0 y) + ∑ j : Fin 3, AJKatoMod.princPM SM (W (Fin.cons 0 y)) j
      (pd W j.succ (Fin.cons 0 y)) = toP (AJKatoMod.FsysM SM (ofP (W (Fin.cons 0 y))))) :
    ∀ μ, pd W μ (Fin.cons 0 y) = pd (stateF SM z₀) μ (Fin.cons 0 y) := by
  have hdW : DifferentiableAt ℝ W (Fin.cons 0 y) :=
    GenHarmonic.diffAt_of_contDiffOn hO hW one_ne_zero hy
  have hdU : DifferentiableAt ℝ (stateF SM z₀) (Fin.cons 0 y) :=
    (contDiff_stateF SM z₀).differentiable (by simp) _
  have hsp : ∀ j : Fin 3, pd W j.succ (Fin.cons 0 y) = pd (stateF SM z₀) j.succ (Fin.cons 0 y) :=
    fun j => GenPhysIdClosed.pd_eq_of_slice hdat rfl hdW hdU j
  have hsym0 := MathPhys.GenPhysIdClosed.ChL.symEqAt_of_sliceConstrainedL SM hS hC₀ y
  have herr : errF SM z₀ (Fin.cons 0 y) = 0 := (symEqAt_iff SM z₀ _).1 hsym0
  have h0 := AJKatoMod.writer_pde_errM (SM := SM) z₀ (Fin.cons 0 y)
  rw [herr, add_zero] at h0
  rw [hdat y] at hrow
  simp only [hsp] at hrow
  intro μ
  induction μ using Fin.cases with
  | zero => exact add_right_cancel (hrow.trans h0.symm)
  | succ j => exact hsp j
end MathPhys.GenPhysIdFinal.ChL

/-! #### `forcing_lip_q` (from `Continuum/GeneratedDefiningJetPropagation.lean`) -/
namespace MathPhys.GenDefJet.ChL
open Filter Topology Set
open scoped BigOperators ContDiff NNReal
open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
/-- **Uniform Lipschitz bound of the `q`-forcing** along the segments joining `W` to the state with
the head and auxiliary metric blocks of `U = 𝒰(z)` and the matter blocks of `W`. -/
theorem forcing_lip_qL (hS : GenChL.SMSmoothL SM) {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
    {a t₀ t₁ b : ℝ} (ha : a < t₀) (hb : t₁ < b) (hW : ContDiffOn ℝ 1 W (openSlab a b))
    (hWp : IsSPeriodic W) (hg : ∀ x ∈ openSlab a b, (W x).1.1 = z.g x) :
    ∃ L, ∀ x ∈ slab t₀ t₁, ‖(toP (Fsys SM (ofP (W x)))).1.2.2 -
        (toP (Fsys SM (ofP (stateF SM z x)))).1.2.2‖ ≤
      L * ‖W x - ((stateF SM z x).1, (W x).2)‖ := by
  set U := stateF SM z with hUdef
  have hU : ContDiff ℝ ∞ U := contDiff_stateF SM z
  have hUp : IsSPeriodic U := isSPeriodic_stateF SM z
  set Φ : StateP m V S S' → (Fin 3 → Fin 4 → Fin 4 → ℝ) :=
    fun v => (toP (Fsys SM (ofP v))).1.2.2 with hΦ
  set Ut : ST 3 → StateP m V S S' := fun x => ((U x).1, (W x).2) with hUt
  have hΦc : ContDiffOn ℝ 1 Φ (chartSet (m := m) (V := V) (S := S) (S' := S')) := fun v hv =>
    (((prQ (m := m) (V := V) (S := S) (S' := S')).contDiff.contDiffAt.comp v
      (MathPhys.ActualJetKato.ChL.contDiffAt_Fsys_stateL hS hv)).of_le (by norm_cast)).contDiffWithinAt
  have hUtc : ContinuousOn Ut (openSlab a b) :=
    (hU.continuous.fst.continuousOn).prodMk hW.continuousOn.snd
  have hUtp : IsSPeriodic Ut := fun k x => by simp only [hUt, hUp k x, hWp k x]
  have hseg : ∀ x ∈ openSlab a b, ∀ s ∈ Icc (0 : ℝ) 1,
      Ut x + s • (W x - Ut x) ∈ chartSet (m := m) (V := V) (S := S) (S' := S') := by
    intro x hx s _
    have hgx : (Ut x + s • (W x - Ut x)).1.1 = z.g x := by
      rw [Prod.fst_add, Prod.fst_add, Prod.smul_fst, Prod.smul_fst, Prod.fst_sub, Prod.fst_sub,
        hg x hx]
      have : (Ut x).1.1 = z.g x := stateF_fst_fst SM z x
      rw [this, sub_self, smul_zero, add_zero]
    exact ⟨by rw [hgx]; exact z.det_ne x, by rw [hgx]; exact z.lor x⟩
  obtain ⟨L, hL⟩ :=
    lip_slab (isOpen_chartSet) hΦc ha hb hUtc hW.continuousOn hUtp hWp hseg
  refine ⟨L, fun x hx => ?_⟩
  have h := hL x hx
  have hΦUt : Φ (Ut x) = Φ (U x) := Fsys_q_metric SM (Ut x) (U x) rfl
  rw [hΦUt] at h
  exact h
end MathPhys.GenDefJet.ChL

/-! #### `metric_defect_propagation` (from `Continuum/GeneratedDefiningJetPropagation.lean`) -/
namespace MathPhys.GenDefJet.ChL
open Filter Topology Set
open scoped BigOperators ContDiff NNReal
open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
/-- **Propagation of the metric defining-jet identities** (shift-transported head row).  Let `W` be
a `C¹` spatially periodic state field on `(a, b) × 𝕋³` whose metric block is the metric of a
smooth tuple `z`, satisfying the shift-transported head row `∂_tg - βʲ∂_jg = Np` and the `q`-rows
of the symmetric system.  Then `p(W) = e_0(g)` on the slab, and if `q(W) = e_a(g)` on the slice
`t = t₀`, then `q(W) = e_a(g)` on `[t₀, t₁] × 𝕋³`. -/
theorem metric_defect_propagationL (hS : GenChL.SMSmoothL SM) {W : ST 3 → StateP m V S S'}
    {z : Tuple m V S S'} {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hW : ContDiffOn ℝ 1 W (openSlab a b)) (hWp : IsSPeriodic W)
    (hg : ∀ x ∈ openSlab a b, (W x).1.1 = z.g x)
    (hMg : ∀ x ∈ openSlab a b, ∀ μ ν, (pd W 0 x).1.1 μ ν -
      ∑ j : Fin 3, (frameU (z.gi x)).β j * (pd W j.succ x).1.1 μ ν =
        (frameU (z.gi x)).N * (W x).1.2.1 μ ν)
    (hMq : ∀ x ∈ openSlab a b, (pd W 0 x).1.2.2 +
      ∑ j : Fin 3, (princL SM (W x) j (pd W j.succ x)).1.2.2 =
        (toP (Fsys SM (ofP (W x)))).1.2.2)
    (hq0 : ∀ y : Fin 3 → ℝ, (W (Fin.cons t₀ y)).1.2.2 = (stateF SM z (Fin.cons t₀ y)).1.2.2) :
    (∀ x ∈ openSlab a b, (W x).1.2.1 = (stateF SM z x).1.2.1) ∧
      ∀ x ∈ slab t₀ t₁, (W x).1.2.2 = (stateF SM z x).1.2.2 := by
  have hp := metric_p_block SM hW hg hMg
  refine ⟨hp, ?_⟩
  have hpdp := metric_pd_p_block SM hW hp
  obtain ⟨L, hL⟩ := MathPhys.GenDefJet.ChL.forcing_lip_qL SM hS ha hb hW hWp hg
  have heq : ∀ x ∈ slab t₀ t₁, ‖∑ μ, shiftCoef z μ x • pd (qDefect W (stateF SM z)) μ x‖ ≤
      max L 0 * ‖qDefect W (stateF SM z) x‖ := by
    intro x hx
    have hxO : x ∈ openSlab a b := slab_subset_openSlab ha hb hx
    have hdW : DifferentiableAt ℝ W x :=
      GenHarmonic.diffAt_of_contDiffOn (isOpen_openSlab a b) hW one_ne_zero hxO
    have hdU : DifferentiableAt ℝ (stateF SM z) x :=
      (contDiff_stateF SM z).differentiable (by simp) x
    have hrow := q_row_difference SM z (W x) (fun μ => pd W μ x) x (hg x hxO)
      (fun j => hpdp x hxO j.succ) (hMq x hxO)
    have hsum : ∑ μ, shiftCoef z μ x • pd (qDefect W (stateF SM z)) μ x =
        qC ((toP (Fsys SM (ofP (W x)))).1.2.2 -
          (toP (Fsys SM (ofP (stateF SM z x)))).1.2.2) := by
      rw [Fin.sum_univ_succ, ← hrow, map_add, map_sum]
      simp only [pd_qDefect hdW hdU, map_smul, shiftCoef_zero, one_smul]
    rw [hsum, norm_qC]
    have hd := norm_diff_q (W x) (stateF SM z x) (by rw [hg x hxO, stateF_fst_fst]) (hp x hxO)
    calc _ ≤ L * ‖W x - ((stateF SM z x).1, (W x).2)‖ := hL x hx
      _ ≤ max L 0 * ‖W x - ((stateF SM z x).1, (W x).2)‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max L 0 * ‖qDefect W (stateF SM z) x‖ :=
          mul_le_mul_of_nonneg_left hd (le_max_right _ _)
  have h0 : ∀ y : Fin 3 → ℝ, qDefect W (stateF SM z) (Fin.cons t₀ y) = 0 := by
    intro y
    unfold qDefect
    rw [map_sub, prQ_apply, prQ_apply, hq0 y, sub_self, map_zero]
  have hzero := GenGauss.transport_unique (N := Fin 3 × Fin 4 × Fin 4) (c := shiftCoef z) ha
    h01 hb (contDiffOn_qDefect hW ((contDiff_stateF SM z).of_le (by norm_cast)).contDiffOn)
    (isSPeriodic_qDefect hWp (isSPeriodic_stateF SM z))
    (fun μ => (contDiff_shiftCoef z μ).contDiffOn) (isSPeriodic_shiftCoef z) one_pos
    (fun x _ => (shiftCoef_zero z x).ge) (le_max_right L 0) heq h0
  intro x hx
  have h1 := qC_eq_zero (hzero x hx)
  rw [map_sub, prQ_apply, prQ_apply] at h1
  exact sub_eq_zero.1 h1
end MathPhys.GenDefJet.ChL

/-! #### `metric_sector` (from `Continuum/GeneratedHiggsDefect.lean`) -/
namespace MathPhys.GenHiggsDefect.ChL
open Filter Topology Set
open scoped BigOperators ContDiff NNReal
open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {SM}
/-- **The metric sector**: the metric variables of `W` are the actual ones on the whole open
slab, provided `q(W)` is actual on one slice. -/
theorem metric_sectorL (hS : GenChL.SMSmoothL SM) {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
    {a t₀ b : ℝ} (ha : a < t₀) (hb : t₀ < b) (hW : MSol SM W z a b)
    (hq0 : ∀ y : Fin 3 → ℝ, (W (Fin.cons t₀ y)).1.2.2 = (stateF SM z (Fin.cons t₀ y)).1.2.2) :
    ∀ x ∈ openSlab a b, (W x).1 = (stateF SM z x).1 := by
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := hW.smooth.of_le (by norm_cast)
  have hp := GenDefJet.metric_p_block SM hW1 hW.g (fun y hy μ ν => hW.row_g hy μ ν)
  have hq : ∀ x ∈ openSlab a b, (W x).1.2.2 = (stateF SM z x).1.2.2 := by
    refine of_forward_backward ha hb (fun t₁ h01 h1b => ?_) (fun t₁ ha1 h10 => ?_)
    · exact (MathPhys.GenDefJet.ChL.metric_defect_propagationL SM hS ha h01 h1b hW1 hW.per hW.g
        (fun y hy μ ν => hW.row_g hy μ ν) (fun y hy => hW.row_q hy) hq0).2
    · -- backward: the transport equation of the `q`-defect, reversed in time
      have hpdp := GenDefJet.metric_pd_p_block SM hW1 hp
      obtain ⟨L, hL⟩ := MathPhys.GenDefJet.ChL.forcing_lip_qL SM hS ha1 hb hW1 hW.per hW.g
      have heq : ∀ x ∈ slab t₁ t₀, ‖∑ μ, GenDefJet.shiftCoef z μ x •
          pd (GenDefJet.qDefect W (stateF SM z)) μ x‖ ≤
          max L 0 * ‖GenDefJet.qDefect W (stateF SM z) x‖ := by
        intro x hx
        have hxO : x ∈ openSlab a b := slab_subset_openSlab ha1 hb hx
        have hdW : DifferentiableAt ℝ W x :=
          GenHarmonic.diffAt_of_contDiffOn (isOpen_openSlab a b) hW1 one_ne_zero hxO
        have hdU : DifferentiableAt ℝ (stateF SM z) x :=
          (contDiff_stateF SM z).differentiable (by simp) x
        have hrow := GenDefJet.q_row_difference SM z (W x) (fun μ => pd W μ x) x (hW.g x hxO)
          (fun j => hpdp x hxO j.succ) (hW.row_q hxO)
        have hsum : ∑ μ, GenDefJet.shiftCoef z μ x •
            pd (GenDefJet.qDefect W (stateF SM z)) μ x =
            GenDefJet.qC ((toP (Fsys SM (ofP (W x)))).1.2.2 -
              (toP (Fsys SM (ofP (stateF SM z x)))).1.2.2) := by
          rw [Fin.sum_univ_succ, ← hrow, map_add, map_sum]
          simp only [GenDefJet.pd_qDefect hdW hdU, map_smul, GenDefJet.shiftCoef_zero, one_smul]
        rw [hsum, GenDefJet.norm_qC]
        have hd := GenDefJet.norm_diff_q (W x) (stateF SM z x)
          (by rw [hW.g x hxO, GenDefJet.stateF_fst_fst]) (hp x hxO)
        calc _ ≤ L * ‖W x - ((stateF SM z x).1, (W x).2)‖ := hL x hx
          _ ≤ max L 0 * ‖W x - ((stateF SM z x).1, (W x).2)‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
          _ ≤ max L 0 * ‖GenDefJet.qDefect W (stateF SM z) x‖ :=
              mul_le_mul_of_nonneg_left hd (le_max_right _ _)
      have h0 : ∀ y : Fin 3 → ℝ, GenDefJet.qDefect W (stateF SM z) (Fin.cons t₀ y) = 0 := by
        intro y
        unfold GenDefJet.qDefect
        rw [map_sub, GenDefJet.prQ_apply, GenDefJet.prQ_apply, hq0 y, sub_self, map_zero]
      have hzero := GenBackward.transport_unique_backward (N := Fin 3 × Fin 4 × Fin 4)
        (c := GenDefJet.shiftCoef z) ha1 h10 hb
        (GenDefJet.contDiffOn_qDefect hW1 ((contDiff_stateF SM z).of_le (by norm_cast)).contDiffOn)
        (GenDefJet.isSPeriodic_qDefect hW.per (isSPeriodic_stateF SM z))
        (fun μ => (GenDefJet.contDiff_shiftCoef z μ).contDiffOn) (GenDefJet.isSPeriodic_shiftCoef z)
        one_pos (fun x _ => (GenDefJet.shiftCoef_zero z x).ge) (le_max_right L 0) heq h0
      intro x hx
      have h1 := GenDefJet.qC_eq_zero (hzero x hx)
      rw [map_sub, GenDefJet.prQ_apply, GenDefJet.prQ_apply] at h1
      exact sub_eq_zero.1 h1
  intro x hx
  have hg : (W x).1.1 = (stateF SM z x).1.1 := by rw [hW.g x hx, GenDefJet.stateF_fst_fst]
  exact Prod.ext hg (Prod.ext (hp x hx) (hq x hx))
end MathPhys.GenHiggsDefect.ChL

/-! #### `higgs_sector` (from `Continuum/GeneratedHiggsDefect.lean`) -/
namespace MathPhys.GenHiggsDefect.ChL
open Filter Topology Set
open scoped BigOperators ContDiff NNReal
open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {SM}
/-- **The Higgs sector**: once the metric and gauge variables of `W` are actual on the open slab,
`Q(W) = D_{e_a}H` on the open slab if it holds on one slice. -/
theorem higgs_sectorL (hS : GenChL.SMSmoothL SM) {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
    {a t₀ b : ℝ} (ha : a < t₀) (hb : t₀ < b) (hW : MSol SM W z a b)
    (hmet : ∀ x ∈ openSlab a b, (W x).1 = (stateF SM z x).1)
    (hEB : ∀ x ∈ openSlab a b, (W x).2.2.1 = (stateF SM z x).2.2.1 ∧
      (W x).2.2.2.1 = (stateF SM z x).2.2.2.1)
    (hQ0 : ∀ y : Fin 3 → ℝ, (W (Fin.cons t₀ y)).2.2.2.2.2.2.1 =
      (stateF SM z (Fin.cons t₀ y)).2.2.2.2.2.2.1) :
    ∀ x ∈ openSlab a b, (W x).2.2.2.2.2.2.1 = (stateF SM z x).2.2.2.2.2.2.1 := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := hW.smooth.of_le (by norm_cast)
  set U := stateF SM z with hU
  have hUs : ContDiff ℝ ∞ U := contDiff_stateF SM z
  have hPi := higgs_Pi hW
  have hpdPm := pd_block_eq' hO hW1 (hUs.differentiable (by simp)).differentiableOn
    (prPm m V S S') (fun y hy => by rw [prPm_apply, prPm_apply, hPi y hy])
  -- the defect and its transport equation
  set dQ : ST 3 → (Fin 3 → V) := fun x => (W x).2.2.2.2.2.2.1 - (U x).2.2.2.2.2.2.1 with hdQ
  have hdQs : ContDiffOn ℝ 1 dQ (openSlab a b) :=
    ((prQh m V S S').contDiff.comp_contDiffOn hW1).sub
      ((prQh m V S S').contDiff.comp (hUs.of_le (by norm_cast))).contDiffOn
  have hdQp : IsSPeriodic dQ := fun q x => by
    simp only [hdQ, hW.per q x]
    rw [show U (x + sshift q) = U x from isSPeriodic_stateF SM z q x]
  have hpd_dQ : ∀ x ∈ openSlab a b, ∀ μ, pd dQ μ x =
      (pd W μ x).2.2.2.2.2.2.1 - (pd U μ x).2.2.2.2.2.2.1 := by
    intro x hx μ
    have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW1 one_ne_zero hx
    have hdU : DifferentiableAt ℝ U x := hUs.differentiable (by simp) x
    have e : dQ = fun y => prQh m V S S' (W y - U y) := by
      funext y; simp only [hdQ, map_sub, prQh_apply]
    rw [e, GenHarmonic.pd_clm (prQh m V S S') (hdW.fun_sub hdU) μ, GenDefJet.pd_sub_eq hdW hdU,
      map_sub]
    rfl
  -- the forcing difference
  have hlip : ∀ t₁ t₂, a < t₁ → t₂ < b → ∃ L, ∀ x ∈ slab t₁ t₂,
      ‖(toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.1 - (toP (Fsys SM (ofP (U x)))).2.2.2.2.2.2.1‖ ≤
        L * ‖dQ x‖ := by
    intro t₁ t₂ h1 h2
    set Φ : StateP m V S S' → (Fin 3 → V) := fun v => (toP (Fsys SM (ofP v))).2.2.2.2.2.2.1
      with hΦ
    have hΦc : ContDiffOn ℝ 1 Φ (chartSet (m := m) (V := V) (S := S) (S' := S')) := fun v hv =>
      ((((prQh m V S S').contDiff.contDiffAt.comp v (MathPhys.ActualJetKato.ChL.contDiffAt_Fsys_stateL hS hv)).of_le
        (by norm_cast))).contDiffWithinAt
    set u : ST 3 → StateP m V S S' := fun x => replQ (W x) ((U x).2.2.2.2.2.2.1) with hu
    have huc : ContinuousOn u (openSlab a b) := by
      have h1c : ContinuousOn W (openSlab a b) := hW1.continuousOn
      have h2c : Continuous fun x => (U x).2.2.2.2.2.2.1 :=
        (prQh m V S S').continuous.comp hUs.continuous
      have hrc : Continuous (fun p : StateP m V S S' × (Fin 3 → V) => replQ p.1 p.2) := by
        unfold replQ; fun_prop
      exact hrc.comp_continuousOn (h1c.prodMk h2c.continuousOn)
    have hup : IsSPeriodic u := fun q x => by
      simp only [hu, hW.per q x]
      rw [show U (x + sshift q) = U x from isSPeriodic_stateF SM z q x]
    have hseg : ∀ x ∈ openSlab a b, ∀ s ∈ Icc (0 : ℝ) 1,
        u x + s • (W x - u x) ∈ chartSet (m := m) (V := V) (S := S) (S' := S') := by
      intro x hx s _
      have hfst : (u x + s • (W x - u x)).1 = (W x).1 := by
        simp only [hu, replQ, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, sub_self, smul_zero,
          add_zero]
      show MetChart (u x + s • (W x - u x)).1
      rw [hfst]; exact hW.chart x hx
    obtain ⟨L, hL⟩ := GenDefJet.lip_slab isOpen_chartSet hΦc h1 h2 huc hW1.continuousOn hup
      hW.per hseg
    refine ⟨max L 0, fun x hx => ?_⟩
    have hxO : x ∈ openSlab a b := slab_subset_openSlab h1 h2 hx
    have hΦu : Φ (u x) = Φ (U x) := FsysQ_congr (hmet x hxO)
      (by funext i; exact hW.A x hxO i) (hEB x hxO).1 (hEB x hxO).2 (hW.H x hxO) (hPi x hxO) rfl
    have h := hL x hx
    rw [hΦu] at h
    calc ‖Φ (W x) - Φ (U x)‖ ≤ L * ‖W x - u x‖ := h
      _ ≤ max L 0 * ‖W x - u x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max L 0 * ‖dQ x‖ := mul_le_mul_of_nonneg_left (norm_sub_replQ (W x) _) (le_max_right _ _)
  -- the transport identity
  have hgW : ∀ x ∈ openSlab a b, frameU (ginvOf (W x).1.1) = frameU (z.gi x) := fun x hx =>
    frameU_W hW hx
  have hgU : ∀ x, frameU (ginvOf (U x).1.1) = frameU (z.gi x) := fun x => by
    rw [GenDefJet.stateF_fst_fst]; rfl
  have htr : ∀ x ∈ openSlab a b, ∑ μ, GenDefJet.shiftCoef z μ x • pd dQ μ x =
      (toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.1 - (toP (Fsys SM (ofP (U x)))).2.2.2.2.2.2.1 := by
    intro x hx
    rw [← hW.row_Q hx, ← writer_Q_row z x, Fin.sum_univ_succ, GenDefJet.shiftCoef_zero, one_smul]
    simp only [hpd_dQ x hx]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      GenDefJet.shiftCoef_eq_neg_beta]
    have ePW : ∀ j : Fin 3, (princL SM (W x) j (pd W j.succ x)).2.2.2.2.2.2.1 i =
        -((frameU (ginvOf (W x).1.1)).β j • (pd W j.succ x).2.2.2.2.2.2.1 i) -
          (frameU (ginvOf (W x).1.1)).N • ((frameU (ginvOf (W x).1.1)).E i j •
            (pd W j.succ x).2.2.2.2.2.1) := fun j => rfl
    have ePU : ∀ j : Fin 3, (princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x)).2.2.2.2.2.2.1 i
        = -((frameU (ginvOf (stateF SM z x).1.1)).β j • (pd (stateF SM z) j.succ x).2.2.2.2.2.2.1 i) -
          (frameU (ginvOf (stateF SM z x).1.1)).N • ((frameU (ginvOf (stateF SM z x).1.1)).E i j •
            (pd (stateF SM z) j.succ x).2.2.2.2.2.1) := fun j => rfl
    have hgU' : frameU (ginvOf (stateF SM z x).1.1) = frameU (z.gi x) := hgU x
    simp only [ePW, ePU, hgW x hx, hgU']
    have hPm : ∀ j : Fin 3, (pd W j.succ x).2.2.2.2.2.1 =
        (pd (stateF SM z) j.succ x).2.2.2.2.2.1 := fun j => hpdPm x hx j.succ
    simp only [hPm, smul_sub, neg_smul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    module
  -- complex coordinates and the transport uniqueness
  obtain ⟨C, hC0, hC⟩ := exists_le_cQ (V := V)
  set w : ST 3 → Fin 3 × Fin (Module.finrank ℝ V) → ℂ := fun x => cQ V (dQ x) with hw
  have hws : ContDiffOn ℝ 1 w (openSlab a b) := (cQ V).contDiff.comp_contDiffOn hdQs
  have hwp : IsSPeriodic w := fun q x => by simp only [hw, hdQp q x]
  have hbound : ∀ t₁ t₂, a < t₁ → t₂ < b → ∃ K, 0 ≤ K ∧ ∀ x ∈ slab t₁ t₂,
      ‖∑ μ, GenDefJet.shiftCoef z μ x • pd w μ x‖ ≤ K * ‖w x‖ := by
    intro t₁ t₂ h1 h2
    obtain ⟨L, hL⟩ := hlip t₁ t₂ h1 h2
    refine ⟨‖cQ V‖ * max L 0 * C, by positivity, fun x hx => ?_⟩
    have hxO : x ∈ openSlab a b := slab_subset_openSlab h1 h2 hx
    have hd : DifferentiableAt ℝ dQ x := GenHarmonic.diffAt_of_contDiffOn hO hdQs one_ne_zero hxO
    have e : ∑ μ, GenDefJet.shiftCoef z μ x • pd w μ x =
        cQ V (∑ μ, GenDefJet.shiftCoef z μ x • pd dQ μ x) := by
      simp only [hw, GenHarmonic.pd_clm (cQ V) hd, map_sum, map_smul]
    rw [e, htr x hxO]
    calc ‖cQ V _‖ ≤ ‖cQ V‖ * ‖(toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.1 -
          (toP (Fsys SM (ofP (U x)))).2.2.2.2.2.2.1‖ := (cQ V).le_opNorm _
      _ ≤ ‖cQ V‖ * (max L 0 * ‖dQ x‖) :=
          mul_le_mul_of_nonneg_left ((hL x hx).trans (mul_le_mul_of_nonneg_right
            (le_max_left _ _) (norm_nonneg _))) (norm_nonneg _)
      _ ≤ ‖cQ V‖ * (max L 0 * (C * ‖w x‖)) := by
          gcongr; exact hC (dQ x)
      _ = ‖cQ V‖ * max L 0 * C * ‖w x‖ := by ring
  have h0 : ∀ y : Fin 3 → ℝ, w (Fin.cons t₀ y) = 0 := by
    intro y
    simp only [hw, hdQ, hQ0 y, sub_self, map_zero]
  have hz : ∀ x ∈ openSlab a b, w x = 0 := by
    refine of_forward_backward ha hb (fun t₁ h01 h1b => ?_) (fun t₁ ha1 h10 => ?_)
    · obtain ⟨K, hK0, hK⟩ := hbound t₀ t₁ ha h1b
      exact GenGauss.transport_unique (N := Fin 3 × Fin (Module.finrank ℝ V))
        (c := GenDefJet.shiftCoef z) ha h01 h1b hws hwp
        (fun μ => (GenDefJet.contDiff_shiftCoef z μ).contDiffOn)
        (GenDefJet.isSPeriodic_shiftCoef z) one_pos
        (fun x _ => (GenDefJet.shiftCoef_zero z x).ge) hK0 hK h0
    · obtain ⟨K, hK0, hK⟩ := hbound t₁ t₀ ha1 hb
      exact GenBackward.transport_unique_backward (N := Fin 3 × Fin (Module.finrank ℝ V))
        (c := GenDefJet.shiftCoef z) ha1 h10 hb hws hwp
        (fun μ => (GenDefJet.contDiff_shiftCoef z μ).contDiffOn)
        (GenDefJet.isSPeriodic_shiftCoef z) one_pos
        (fun x _ => (GenDefJet.shiftCoef_zero z x).ge) hK0 hK h0
  intro x hx
  exact sub_eq_zero.1 (cQ_eq_zero (hz x hx))
end MathPhys.GenHiggsDefect.ChL

/-! #### `gauss_transport_m` (from `Continuum/GeneratedCoupledMatter.lean`) -/
namespace MathPhys.GenCplMat.ChL
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  JetCurve GenConstraint GenNoether GenGauss ActualJetCompleteForcing ActualJetRecon
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
/-- **The Gauss transport equation**: on an open set where the actual-jet state solves the symmetric
system, `∂_ν(ϱe_0{}^νG) + [A_ν, ϱe_0{}^νG] = 0` (Yang–Mills Bianchi identity + current Noether
identity + residual slaving of the Higgs and Dirac equations). -/
theorem gauss_transport_mL (hN : CurrentNoether SM) (hS : GenChL.SMSmoothL SM) {O : Set (ST 3)}
    (hO : IsOpen O) (hmat : ∀ y ∈ O, MatterAt SM z y) {x : ST 3} (hx : x ∈ O) :
    ∑ ν, (pd (fun y => w0 z ν y • gaussF SM z y) ν x + ⁅z.A x ν, w0 z ν x • gaussF SM z x⁆) =
      0 := by
  obtain ⟨hD, hH, -⟩ := hmat x hx
  have h0 := MathPhys.GenNoether.ChL.div_rA_eq_zeroL z hN hS hH hD
  have hloc : ∀ ν, (fun y => densR SM z y ν) =ᶠ[𝓝 x]
      fun y => -(w0 z ν y • gaussF SM z y) :=
    fun ν => Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => densR_eq_gauss_m SM z (hmat y hy) ν
  have hpd : ∀ ν, pd (fun y => densR SM z y ν) ν x =
      -pd (fun y => w0 z ν y • gaussF SM z y) ν x := by
    intro ν
    unfold SobolevOpen.pd
    rw [(hloc ν).fderiv_eq]
    exact pd_neg'_m (fun y => w0 z ν y • gaussF SM z y) ν x
  simp only [hpd, densR_eq_gauss_m SM z (hmat x hx), lie_neg] at h0
  rw [← neg_eq_zero, ← h0, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  abel
end MathPhys.GenCplMat.ChL

/-! #### `gauss_transport'_m` (from `Continuum/GeneratedCoupledMatter.lean`) -/
namespace MathPhys.GenCplMat.ChL
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  JetCurve GenConstraint GenNoether GenGauss ActualJetCompleteForcing ActualJetRecon
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
/-- The transport equation solved for the normal derivative:
`Σ_ν ϱe_0^ν∂_νG = -(Σ_ν∂_ν(ϱe_0^ν))G - Σ_ν ϱe_0^ν[A_ν, G]`. -/
theorem gauss_transport'_mL (hN : CurrentNoether SM) (hS : GenChL.SMSmoothL SM) {O : Set (ST 3)}
    (hO : IsOpen O) (hmat : ∀ y ∈ O, MatterAt SM z y) {x : ST 3} (hx : x ∈ O) :
    ∑ ν, w0 z ν x • pd (gaussF SM z) ν x =
      -((∑ ν, pd (w0 z ν) ν x) • gaussF SM z x) -
        ∑ ν, w0 z ν x • ⁅z.A x ν, gaussF SM z x⁆ := by
  have h := MathPhys.GenCplMat.ChL.gauss_transport_mL SM z hN hS hO hmat hx
  have hprod : ∀ ν, pd (fun y => w0 z ν y • gaussF SM z y) ν x =
      pd (w0 z ν) ν x • gaussF SM z x + w0 z ν x • pd (gaussF SM z) ν x := by
    intro ν
    unfold SobolevOpen.pd
    rw [fderiv_fun_smul (((contDiff_w0 z ν).differentiable (by simp)) x)
      (((MathPhys.GenGauss.ChL.contDiff_gaussFL SM z hS).differentiable (by simp)) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [add_comm]
  simp only [hprod, lie_smul] at h
  rw [Finset.sum_smul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]
  refine Finset.sum_congr rfl fun ν _ => ?_
  abel
end MathPhys.GenCplMat.ChL

/-! #### `gauss_propagation_m` (from `Continuum/GeneratedCoupledMatter.lean`) -/
namespace MathPhys.GenCplMat.ChL
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  JetCurve GenConstraint GenNoether GenGauss ActualJetCompleteForcing ActualJetRecon
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
/-- **Propagation of the Gauss constraint** (`lem:generated-physical-identification`, the Gauss
part of constraint propagation): for theory data with smooth sources satisfying the current
Noether identity, if the actual-jet state field of a smooth tuple solves the independent symmetric
system `eq:generated-extension` on the open slab `(a, b) × 𝕋³` and the Gauss constraint
`e_0{}^νr^A_ν` vanishes at `t₀ ∈ (a, b)`, then it vanishes on `[t₀, t₁] × 𝕋³` for every
`t₁ ∈ (t₀, b)`. -/
theorem gauss_propagation_mL (hN : CurrentNoether SM) (hS : GenChL.SMSmoothL SM) {a t₀ t₁ b : ℝ}
    (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b) (hmat : ∀ x ∈ openSlab a b, MatterAt SM z x)
    (h0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, gaussF SM z x = 0 := by
  have hGs := MathPhys.GenGauss.ChL.contDiff_gaussFL SM z hS
  have hGd : ∀ x, DifferentiableAt ℝ (gaussF SM z) x := fun x =>
    (hGs.differentiable (by simp)) x
  set w : ST 3 → Fin m × Fin m → ℂ := fun x => cplxL m (gaussF SM z x) with hw
  have hws : ContDiffOn ℝ 1 w (openSlab a b) :=
    ((cplxL m).contDiff.comp (hGs.of_le (by exact_mod_cast le_top))).contDiffOn
  have hwp : IsSPeriodic w := fun k x => by simp only [hw, isSPeriodic_gaussF SM z k x]
  have hc : ∀ μ, ContDiffOn ℝ 1 (w0 z μ) (openSlab a b) := fun μ =>
    ((contDiff_w0 z μ).of_le (by exact_mod_cast le_top)).contDiffOn
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_lower_slab (contDiff_w0 z 0).continuous.continuousOn
    (isSPeriodic_w0 z 0) (w0_zero_pos z) ha hb
  -- bounds for the transport coefficients on the slab
  have hDc : ContinuousOn (fun x => ∑ ν, pd (w0 z ν) ν x) (openSlab a b) :=
    (continuous_finset_sum _ fun ν _ => (contDiff_pd (contDiff_w0 z ν) ν).continuous).continuousOn
  have hDp : IsSPeriodic (fun x => ∑ ν, pd (w0 z ν) ν x) := fun k x => by
    simp only [GenGauss.isSPeriodic_pd (isSPeriodic_w0 z _) _ k x]
  obtain ⟨CD, hCD⟩ := KatoGalerkin.exists_bound_slab hDc hDp ha hb
  have hW : ∀ ν, ∃ C, ∀ x ∈ slab t₀ t₁, ‖w0 z ν x‖ ≤ C := fun ν =>
    KatoGalerkin.exists_bound_slab (contDiff_w0 z ν).continuous.continuousOn
      (isSPeriodic_w0 z ν) ha hb
  choose CW hCW using hW
  have hAb : ∀ ν, ∃ C, ∀ x ∈ slab t₀ t₁, ‖z.A x ν‖ ≤ C := fun ν =>
    KatoGalerkin.exists_bound_slab (Tuple.contDiff_vec z.A_smooth ν).continuous.continuousOn
      (fun k x => by simp only [z.A_per k x]) ha hb
  choose CA hCA using hAb
  obtain ⟨Cb, hCb0, hCb⟩ := exists_lie_bound m
  set K : ℝ := |CD| + ∑ ν, |CW ν| * (Cb * |CA ν|) with hK
  have hK0 : 0 ≤ K := by positivity
  have heq : ∀ x ∈ slab t₀ t₁, ‖∑ μ, w0 z μ x • pd w μ x‖ ≤ K * ‖w x‖ := by
    intro x hx
    have hxo : x ∈ openSlab a b := slab_subset_openSlab ha hb hx
    have e1 : ∑ μ, w0 z μ x • pd w μ x = cplxL m (∑ μ, w0 z μ x • pd (gaussF SM z) μ x) := by
      simp only [hw, pd_cplxL_m (hGd x), map_sum, map_smul]
    rw [e1, norm_cplxL, MathPhys.GenCplMat.ChL.gauss_transport'_mL SM z hN hS (isOpen_openSlab a b) hmat hxo]
    have hwx : ‖w x‖ = ‖gaussF SM z x‖ := norm_cplxL _
    rw [hwx]
    set G := gaussF SM z x
    calc ‖-((∑ ν, pd (w0 z ν) ν x) • G) - ∑ ν, w0 z ν x • ⁅z.A x ν, G⁆‖
        ≤ ‖(∑ ν, pd (w0 z ν) ν x) • G‖ + ‖∑ ν, w0 z ν x • ⁅z.A x ν, G⁆‖ := by
          rw [sub_eq_add_neg, ← neg_add]
          rw [norm_neg]
          exact norm_add_le _ _
      _ ≤ |CD| * ‖G‖ + ∑ ν, |CW ν| * (Cb * |CA ν|) * ‖G‖ := by
          gcongr
          · rw [norm_smul]
            exact mul_le_mul_of_nonneg_right ((hCD x hx).trans (le_abs_self _)) (norm_nonneg _)
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
            rw [norm_smul]
            have h1 : ‖w0 z ν x‖ ≤ |CW ν| := (hCW ν x hx).trans (le_abs_self _)
            have h2 : ‖⁅z.A x ν, G⁆‖ ≤ Cb * |CA ν| * ‖G‖ :=
              (hCb _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                ((hCA ν x hx).trans (le_abs_self _)) hCb0) (norm_nonneg _))
            calc ‖w0 z ν x‖ * ‖⁅z.A x ν, G⁆‖ ≤ |CW ν| * (Cb * |CA ν| * ‖G‖) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)
              _ = |CW ν| * (Cb * |CA ν|) * ‖G‖ := by ring
      _ = K * ‖G‖ := by rw [hK, add_mul, Finset.sum_mul]
  have hw0 : ∀ y : Fin 3 → ℝ, w (Fin.cons t₀ y) = 0 := fun y => by
    simp only [hw, h0 y, map_zero]
  have := transport_unique (N := Fin m × Fin m) (c := w0 z) ha h01 hb hws hwp hc
    (isSPeriodic_w0 z) hκ hκle hK0 heq hw0
  intro x hx
  exact cplxL_eq_zero (this x hx)
end MathPhys.GenCplMat.ChL

/-! #### `divT_zero_cpl` (from `Continuum/GeneratedCoupledMatter.lean`) -/
namespace MathPhys.GenCplMat.ChL
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  JetCurve GenConstraint GenNoether GenGauss ActualJetCompleteForcing ActualJetRecon
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
variable {SM z} {W : ST 3 → StateP m V S S'} {a b : ℝ}
/-- **The complete stress is conserved along a coupled solution** (Gauss law propagated from the
initial slice; current and stress Noether identities of the theory data). -/
theorem divT_zero_cplL (hN : CurrentNoether SM) (hT : StressConservation SM)
    (hS : GenChL.SMSmoothL SM) (h : GenCplRows.CplSol SM W z a b) {t₀ t₁ : ℝ} (ha : a < t₀)
    (h01 : t₀ < t₁) (hb : t₁ < b) (hG0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, (∀ ν, GenStress.divT SM z x ν = 0) ∧ (bosF SM z x).2.1 = 0 := by
  have hmat : ∀ x ∈ openSlab a b, MatterAt SM z x := fun x hx => matterAt_cpl h hx
  have hG := MathPhys.GenCplMat.ChL.gauss_propagation_mL SM z hN hS ha h01 hb hmat hG0
  intro x hx
  have hxo : x ∈ openSlab a b := slab_subset_openSlab ha hb hx
  obtain ⟨hD, hH, hE⟩ := hmat x hxo
  have hA : (bosF SM z x).2.1 = 0 := by
    refine eq_zero_of_frame_components z x _ fun A => ?_
    induction A using Fin.cases with
    | zero => exact hG x hx
    | succ c => exact hE c
  have hDn : ∀ᶠ y in 𝓝 x, dirF SM z y = 0 :=
    Filter.eventually_of_mem ((isOpen_openSlab a b).mem_nhds hxo) fun y hy => (hmat y hy).1
  exact ⟨hT z x hDn hA hH, hA⟩
end MathPhys.GenCplMat.ChL

/-! #### `modified_kato_realization_cpl` (from `Continuum/GeneratedCoupledKato.lean`) -/
namespace MathPhys.GenCplKato.ChL
open Finset Set Filter Topology
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint TwistedHalfRicci
  SpinorProlongation ActualJetSpinor AJKatoMod
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
/-- **The Kato realization of the shift-transported actual-jet system.**  For theory data with
smooth sources and back-reacting Dirac data with the symmetric Dirac stress (`CoupledDirac`), forms with
the Clifford unitarity relations and any Euclidean coordinates `κ` of the block inner product, for
every compact chart set `K` there are globally smooth coefficient maps `A^j`, `F` with
`A^j(v)` symmetric, both equivariant under the coordinate transposition `τ_κ` of the metric blocks,
which at the **symmetric** states of `K` are the modified principal operators `𝒜_M^j` and the
modified forcing `𝓕_M`. -/
theorem modified_kato_realization_cplL (hS : GenChL.SMSmoothL SM) (hU : UnitaryForms SM bG bV bS bS')
    (hC : GenDStress.CoupledDirac SM) (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (hκ : ∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) :
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, IsSymmP (κ.symm v) → ∀ j a (w : Fin (dimS m V S S') → ℝ),
          ∑ b, A j a b v * w b = κ (princPM SM (κ.symm v) j (κ.symm w)) a) ∧
        (∀ v ∈ K, IsSymmP (κ.symm v) → ∀ a, F a v = κ (toP (FsysM SM (ofP (κ.symm v)))) a) ∧
        (∀ j a v w, ∑ b, A j a b (tauK κ v) * tauK κ w b =
          tauK κ (fun a' => ∑ b, A j a' b v * w b) a) ∧
        (∀ a v, F a (tauK κ v) = tauK κ (fun a' => F a' v) a) := by
  intro K hK hKc
  set O : Set (Fin (dimS m V S S') → ℝ) := κ.symm ⁻¹' chartSet with hOdef
  have hκc : Continuous κ.symm := (contDiff_linearEquiv κ.symm.toLinearMap).continuous
  have hO : IsOpen O := isOpen_chartSet.preimage hκc
  have hKO : K ⊆ O := fun v hv => hKc v hv
  have hκs : ContDiff ℝ ∞ κ.symm := contDiff_linearEquiv κ.symm.toLinearMap
  have hκf : ContDiff ℝ ∞ κ := contDiff_linearEquiv κ.toLinearMap
  have hframe : ∀ v ∈ O, ContDiffAt ℝ ∞
      (fun v => (frameU (ginvOf (κ.symm v).1.1)).N) v ∧
      (∀ j, ContDiffAt ℝ ∞ (fun v => (frameU (ginvOf (κ.symm v).1.1)).β j) v) ∧
      (∀ a j, ContDiffAt ℝ ∞ (fun v => (frameU (ginvOf (κ.symm v).1.1)).E a j) v) := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := contDiffAt_frame_state (m := m) (V := V) (S := S) (S' := S') hv
    exact ⟨h1.comp v hκs.contDiffAt, fun j => (h2 j).comp v hκs.contDiffAt,
      fun a j => (h3 a j).comp v hκs.contDiffAt⟩
  have hL : ContDiffOn ℝ ∞ (fun v => Real.log (frameU (ginvOf (κ.symm v).1.1)).N) O :=
    fun v hv => ((hframe v hv).1.log (frameU _).N_pos.ne').contDiffWithinAt
  obtain ⟨L', hL's, hL'K⟩ := SlabMoser.exists_contDiff_eqOn hO hK hKO hL
  obtain ⟨β', hβ's, hβ'K⟩ := exists_contDiff_eqOn_family hO hK hKO
    (Φ := fun j v => (frameU (ginvOf (κ.symm v).1.1)).β j)
    fun j v hv => ((hframe v hv).2.1 j).contDiffWithinAt
  obtain ⟨E', hE's, hE'K⟩ := exists_contDiff_eqOn_family hO hK hKO
    (Φ := fun p : Fin 3 × Fin 3 => fun v => (frameU (ginvOf (κ.symm v).1.1)).E p.1 p.2)
    fun p v hv => ((hframe v hv).2.2 p.1 p.2).contDiffWithinAt
  obtain ⟨F', hF's, hF'K⟩ := exists_contDiff_eqOn_family hO hK hKO
    (Φ := fun a v => κ (toP (FsysM SM (ofP (κ.symm v)))) a)
    fun a v hv => by
      have h0 : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => toS (Fsys SM (ofP x))) (κ.symm v) :=
        MathPhys.ActualJetKato.ChL.contDiffAt_Fsys_stateL hS hv
      have hN : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).N) (κ.symm v) :=
        (contDiffAt_frame_state (m := m) (V := V) (S := S) (S' := S') hv).1
      have hβ : ∀ j, ContDiffAt ℝ ∞
          (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).β j) (κ.symm v) :=
        (contDiffAt_frame_state (m := m) (V := V) (S := S) (S' := S') hv).2.1
      have hM : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => toP (FsysM SM (ofP x))) (κ.symm v) := by
        have e : (fun x : StateP m V S S' => toP (FsysM SM (ofP x))) = fun x =>
            toS (Fsys SM (ofP x)) + fDiff SM x := funext fun x => FsysM_eq SM x
        rw [e]
        refine h0.add ?_
        unfold fDiff
        have hg : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (Fsys SM (ofP x)).g) (κ.symm v) :=
          contDiffAt_pi.2 fun μ => contDiffAt_pi.2 fun ν =>
            (MathPhys.ActualJetSmooth.ChL.Fsys_smoothL SM hS hv).1 μ ν
        have hH : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (Fsys SM (ofP x)).H) (κ.symm v) :=
          (MathPhys.ActualJetSmooth.ChL.Fsys_smoothL SM hS hv).2.2.2.2.2.2.1
        have hp : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.1.2.1) (κ.symm v) := by fun_prop
        have hPm : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.2.2.2.2.2.1) (κ.symm v) := by
          fun_prop
        have hA : ∀ j, ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.2.1 j) (κ.symm v) := by
          intro j; fun_prop
        have hHv : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.2.2.2.2.1) (κ.symm v) := by
          fun_prop
        have hbr : ∀ j, ContDiffAt ℝ ∞
            (fun x : StateP m V S S' => ⁅x.2.1 j, x.2.2.2.2.1⁆) (κ.symm v) := fun j =>
          ContDiffAt.lie_mod (hA j) hHv
        refine ContDiffAt.prodMk (ContDiffAt.prodMk ?_ contDiffAt_const) ?_
        · exact contDiffAt_pi.2 fun μ => contDiffAt_pi.2 fun ν =>
            (hN.mul ((contDiffAt_pi.1 (contDiffAt_pi.1 hp μ)) ν)).sub
              ((contDiffAt_pi.1 (contDiffAt_pi.1 hg μ)) ν)
        · refine ContDiffAt.prodMk contDiffAt_const (ContDiffAt.prodMk contDiffAt_const
            (ContDiffAt.prodMk contDiffAt_const (ContDiffAt.prodMk ?_ contDiffAt_const)))
          exact ((hN.smul hPm).add (ContDiffAt.sum fun j _ => (hβ j).smul (hbr j))).sub hH
      have h2 := (hκf.contDiffAt (x := toP (FsysM SM (ofP (κ.symm v))))).comp v
        (hM.comp v hκs.contDiffAt)
      exact ((contDiffAt_pi.1 h2) a).contDiffWithinAt
  -- the frame data, composed with the symmetrization
  set AF' : (Fin (dimS m V S S') → ℝ) → AdaptedFrame := fun v =>
    mkFrame (L' (symK κ v)) (fun j => β' j (symK κ v)) (fun a j => E' (a, j) (symK κ v))
    with hAF'
  have hAFK : ∀ v ∈ K, IsSymmP (κ.symm v) → AF' v = frameU (ginvOf (κ.symm v).1.1) := by
    intro v hv hs
    simp only [hAF', symK_of_symm κ hs]
    exact mkFrame_eq (hL'K v hv) (funext fun j => hβ'K j v hv) (funext fun a => funext fun j =>
      hE'K (a, j) v hv)
  have hAFτ : ∀ v, AF' (tauK κ v) = AF' v := fun v => by simp only [hAF', symK_tauK]
  set Fs : Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ := fun a v =>
    (1 / 2 : ℝ) * (F' a v + tauK κ (fun a' => F' a' (tauK κ v)) a) with hFs
  have hsymKs : ContDiff ℝ ∞ (symK κ) := (symK κ).contDiff
  have htauKs : ContDiff ℝ ∞ (tauK κ) := by
    have : tauK κ = (κ.toLinearMap.comp ((tauP m V S S').toLinearMap.comp κ.symm.toLinearMap)) :=
      funext fun v => rfl
    rw [this]
    exact contDiff_linearEquiv _
  refine ⟨fun j a b v => princEntryM SM bG bV bS bS' κ (AF' v) j a b, Fs, fun j a b => ?_,
    fun j a b v => princEntryM_symm hU κ (AF' v) j a b, fun a => ?_, fun v hv hs j a w => ?_,
    fun v hv hs a => ?_, fun j a v w => ?_, fun a v => ?_⟩
  · exact contDiff_princEntryM_mkFrame κ (hL's.comp hsymKs) (fun j => (hβ's j).comp hsymKs)
      (fun a j => (hE's (a, j)).comp hsymKs) j a b
  · have hT : ContDiff ℝ ∞ fun v => tauK κ (fun a' => F' a' (tauK κ v)) := by
      have hlin : tauK κ = (κ.toLinearMap.comp ((tauP m V S S').toLinearMap.comp
          κ.symm.toLinearMap)) := funext fun v => rfl
      rw [hlin]
      exact (contDiff_linearEquiv _).comp ((contDiff_pi.2 hF's).comp htauKs)
    exact contDiff_const.mul ((hF's a).add ((contDiff_pi.1 hT) a))
  · rw [sum_princEntryM hU hκ, hAFK v hv hs]
    rfl
  · have hτv : tauK κ v = v := by
      unfold tauK; rw [hs, LinearEquiv.apply_symm_apply]
    have hsF : IsSymmP (toP (FsysM SM (ofP (κ.symm v)))) := FsysM_symm_cpl hC hs
    simp only [hFs, hτv]
    have h1 : (fun a' => F' a' v) = κ (toP (FsysM SM (ofP (κ.symm v)))) :=
      funext fun a' => hF'K a' v hv
    rw [h1, hF'K a v hv]
    have h2 : tauK κ (κ (toP (FsysM SM (ofP (κ.symm v))))) = κ (toP (FsysM SM (ofP (κ.symm v)))) := by
      unfold tauK; rw [LinearEquiv.symm_apply_apply, hsF]
    rw [h2]
    ring
  · rw [sum_princEntryM hU hκ, hAFτ]
    have e : (fun a' => ∑ b, princEntryM SM bG bV bS bS' κ (AF' v) j a' b * w b) =
        κ (toS (princM (AF' v) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) :=
      funext fun a' => sum_princEntryM hU hκ (AF' v) j a' w
    rw [e]
    unfold tauK
    simp only [LinearEquiv.symm_apply_apply]
    rw [princM_tauP]
  · simp only [hFs, tauK_tauK]
    have e : (fun a' => (1 / 2 : ℝ) * (F' a' v + tauK κ (fun a'' => F' a'' (tauK κ v)) a')) =
        (1 / 2 : ℝ) • ((fun a' => F' a' v) + tauK κ (fun a'' => F' a'' (tauK κ v))) := by
      funext a'; simp [smul_eq_mul]
    rw [e, tauK_smul, tauK_add, tauK_tauK]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
end MathPhys.GenCplKato.ChL
