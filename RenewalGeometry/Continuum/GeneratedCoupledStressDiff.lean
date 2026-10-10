/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledBox

/-!
# The auxiliary Dirac stress and its divergence

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors, for back-reacting theory data (`GenDStress.CoupledDirac`: the symmetric Dirac
stress).  The stress difference `ΔS` of a coupled solution (`GenCplEin.stressDiff`) is the kinetic
Dirac stress of the spinor defects (`stressDiff_eq`): no trace part survives because both spinor
one-forms obey the normal Dirac relation.  Its divergence, the source of the subsidiary equation,
is controlled by the defects and the twisted Dirac operators `𝒟'Y`, `𝒟̄'Ȳ`:

* `ΔSf` — the coordinate kinetic stress `Σ θ^A{}_μθ^B{}_ν K_{AB}(Y, Ȳ)`;
* **`stressDiff_eq`** — `ΔS = ΔSf` on the slab;
* `divY_eq` — `Σ_Aε_Ae_A(Y_A) = -½(κ(𝒟'Y) - …)` (the divergence of a Clifford-traceless
  one-form is a Clifford trace of its Dirac operator).
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplSD

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov GenCplN GenCplRows GenCplX GenCplP GenCplEin GenDStress GenCplBox

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

variable {SM : SMData (MatLie m) V S S'} (hC : CoupledDirac SM) (W : ST 3 → StateP m V S S')
  (z : Tuple m V S S')

/-- The coframe of the tuple. -/
def θF (y : ST 3) (A μ : Fin 4) : ℝ := cof (z.g y) lorentzSign (frameU (z.gi y)).fr A μ

/-- **The coordinate kinetic Dirac stress of the spinor defects.** -/
def ΔSf (y : ST 3) (μ ν : Fin 4) : ℝ :=
  ∑ A, ∑ B, θF z y A μ * θF z y B ν *
    kinT SM.D hC.P (z.ψ y) (Yf SM W z y) (z.ψb y) (Ybf SM W z y) A B

variable {W z} {a b : ℝ}

/-- **The stress difference of a coupled solution is the kinetic stress of the defects.** -/
theorem stressDiff_eq (h : CplSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) (μ ν : Fin 4) :
    stressDiff SM W z y μ ν = ΔSf hC W z y μ ν := by
  obtain ⟨hg, hgi, hdg, hAF, hde, hA, hF, hH, hDH, hψ, hψb⟩ := recon_fields h hy
  unfold stressDiff stressF
  rw [hg, hgi, hF, hH, hDH, hψ, hψb, hAF]
  set fU := recon SM (ofP (stateF SM z y))
  set fW := recon SM (ofP (W y))
  have hXrel : ∀ (fj : FirstJet (MatLie m) V S S'), fj = fU ∨ fj = fW →
      ∑ C, lorentzSign C • SM.D.Fr.c C (fj.X C) = mass SM.D.m0 SM.D.L fU.H fU.ψ ∧
      ∑ C, lorentzSign C • SM.Db.Fr.c C (fj.Xb C) = mass SM.Db.m0 SM.Db.L fU.H fU.ψb := by
    rintro fj (rfl | rfl)
    · exact ⟨dirac_rel_Xnat SM.D _ _ _, dirac_rel_Xnat SM.Db _ _ _⟩
    · refine ⟨?_, ?_⟩
      · have := dirac_rel_Xnat SM.D (W y).2.2.2.2.2.2.2.1 (W y).2.2.2.2.2.2.2.2.1 (W y).2.2.2.2.1
        rw [← hH, ← hψ]
        exact this
      · have := dirac_rel_Xnat SM.Db (W y).2.2.2.2.2.2.2.2.2.1 (W y).2.2.2.2.2.2.2.2.2.2
          (W y).2.2.2.2.1
        rw [← hH, ← hψb]
        exact this
  obtain ⟨hU1, hU2⟩ := hXrel fU (Or.inl rfl)
  obtain ⟨hW1, hW2⟩ := hXrel fW (Or.inr rfl)
  have hTD := hC.TD_eq
  unfold DiracStressForm.coord
  rw [hTD]
  simp only [add_sub_add_left_eq_sub]
  rw [← Finset.sum_sub_distrib]
  unfold ΔSf θF
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [← mul_sub, frame_symTD_sub hC.toDiracPairing fU.H fU.ψ fW.X fU.X fU.ψb fW.Xb fU.Xb hW1 hW2
    hU1 hU2 A B, recon_X_sub h hy, recon_Xb_sub h hy]
  rfl

end RenewalGeometry.GenCplSD
