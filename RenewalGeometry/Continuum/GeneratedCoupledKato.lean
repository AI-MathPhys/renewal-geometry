/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ActualJetKatoModified
import RenewalGeometry.Continuum.GeneratedDiracStress

/-!
# The Kato realization of the shift-transported system for back-reacting Dirac data

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.  `AJKatoMod.modified_kato_realization` needs the modified forcing to preserve the
symmetric states (`AJKatoMod.FsysM_symm`), which it proves for decoupled spinors (`T^D = 0`).  The
only property used is the symmetry of the complete stress; for back-reacting theory data with the
**symmetric Dirac stress** (`GenDStress.CoupledDirac`) the stress is symmetric as well:

* `coord_symm_cpl` — `T^D_{μν} = T^D_{νμ}`;
* `FsysM_symm_cpl` — the modified forcing preserves the symmetric states;
* **`modified_kato_realization_cpl`** — the Kato realization of the shift-transported system for
  `CoupledDirac` data (the proof of `AJKatoMod.modified_kato_realization`, verbatim, with
  `FsysM_symm_cpl`).
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplKato

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

section Transpose

variable {SM : SMData (MatLie m) V S S'}

/-- **The symmetric Dirac stress is symmetric in coordinates.** -/
theorem coord_symm_cpl (hC : GenDStress.CoupledDirac SM) (g : Met) (ε : Fin 4 → ℝ) (e : Met)
    (H : V) (ψ : S) (X : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S') (μ ν : Fin 4) :
    SM.TD.coord g ε e H ψ X ψb Xb μ ν = SM.TD.coord g ε e H ψ X ψb Xb ν μ := by
  rw [hC.TD_eq]
  unfold DiracStressForm.coord
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  rw [GenDStress.frame_symTD_symm]
  ring

theorem FsysM_symm_cpl (hC : GenDStress.CoupledDirac SM) {v : StateP m V S S'} (hv : IsSymmP v) :
    IsSymmP (toP (FsysM SM (ofP v))) := by
  rw [isSymmP_iff] at hv ⊢
  obtain ⟨hg, hp, hq⟩ := hv
  set fj := recon SM (ofP v) with hfj
  have hgs : ∀ a b, fj.g a b = fj.g b a := hg
  have hgis : ∀ a b, fj.gi a b = fj.gi b a := AJKatoMod.ginvOf_symm hg
  have hdgs : ∀ α μ ν, fj.dg α μ ν = fj.dg α ν μ := by
    intro α μ ν
    simp only [hfj, recon, ofP, hp μ ν, fun a => hq a μ ν]
  have hst : ∀ μ ν, stressF SM fj μ ν = stressF SM fj ν μ := by
    intro μ ν
    unfold stressF
    rw [coord_symm_cpl hC, ymStressB_symm hC.ipG_symm hgs hgis,
      higgsStressB_symm hC.ipV_symm _ _ hgs]
  refine ⟨fun μ ν => ?_, fun μ ν => ?_, fun a μ ν => ?_⟩
  · show (frameU (ginvOf (ofP v).g)).N * (ofP v).p μ ν =
      (frameU (ginvOf (ofP v).g)).N * (ofP v).p ν μ
    rw [show (ofP v).p μ ν = (ofP v).p ν μ from hp μ ν]
  · show (lowerOf SM fj).p μ ν = (lowerOf SM fj).p ν μ
    simp only [lowerOf]
    have hL : fj.AF.Lp fj.de (fun α => fj.dg α μ ν) = fj.AF.Lp fj.de (fun α => fj.dg α ν μ) := by
      congr 1; funext α; exact hdgs α μ ν
    rw [hL, qRem_symm hgs hgis hdgs μ ν, traceRev_symm hgs hst μ ν, hgs μ ν]
  · show (lowerOf SM fj).q a μ ν = (lowerOf SM fj).q a ν μ
    simp only [lowerOf]
    congr 2
    funext α; exact hdgs α μ ν

end Transpose

section Realization

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- **The Kato realization of the shift-transported actual-jet system.**  For theory data with
smooth sources and back-reacting Dirac data with the symmetric Dirac stress (`CoupledDirac`), forms with
the Clifford unitarity relations and any Euclidean coordinates `κ` of the block inner product, for
every compact chart set `K` there are globally smooth coefficient maps `A^j`, `F` with
`A^j(v)` symmetric, both equivariant under the coordinate transposition `τ_κ` of the metric blocks,
which at the **symmetric** states of `K` are the modified principal operators `𝒜_M^j` and the
modified forcing `𝓕_M`. -/
theorem modified_kato_realization_cpl (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
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
        contDiffAt_Fsys_state hS hv
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
            (Fsys_smooth SM hS hv).1 μ ν
        have hH : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (Fsys SM (ofP x)).H) (κ.symm v) :=
          (Fsys_smooth SM hS hv).2.2.2.2.2.2.1
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

end Realization

end RenewalGeometry.GenCplKato
