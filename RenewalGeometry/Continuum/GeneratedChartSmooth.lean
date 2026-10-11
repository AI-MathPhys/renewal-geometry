/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetSmoothness
import RenewalGeometry.Continuum.ActualJetKatoRealization
import RenewalGeometry.Continuum.ActualJetStateField
import RenewalGeometry.Continuum.GeneratedResidualSmooth
import RenewalGeometry.Continuum.GeneratedNoetherIdentities
import RenewalGeometry.Continuum.GeneratedGaussPropagation

/-!
# Chart-local smoothness of the sources: the smoothness layer

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
`thm:generated-dynamics` (back-reacting **charged** spinors).

`SMSmoothL` replaces the global smoothness hypothesis `ActualJetSmooth.SMSmooth` by smoothness
of the Yang–Mills source near Lorentzian charts of the inverse-metric slot (what charged Dirac
currents satisfy; `GenChNoGo.not_smSmooth_of_charged`).  `SMSmooth.toL` shows it is weaker.  This
file re-proves the smoothness layer of the actual-jet chain under `SMSmoothL` (declarations with
the suffix `L`, same statements with `SMSmooth` replaced by `SMSmoothL`): the source blocks of the
symmetric system at chart states (`Fsys_smoothL`, `contDiffAt_Fsys_stateL`), the Kato realization
(`actual_jet_kato_realizationL`), the residual fields along a tuple (`contDiff_bosFL`), the
residual maps on the chart (`bosR_smoothL`), the current divergence (`div_rA_eq_zeroL`) and the
Gauss field (`contDiff_gaussFL`).  Every evaluation point is in the chart (tuples are Lorentzian
everywhere, states are `MetChart`), which is where `SMSmoothL` gives smoothness.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

namespace RenewalGeometry.GenChL

/-! ### Chart-local smoothness of the sources -/

section Prelude

open ActualJetSystem ActualJetSmooth ActualJetFrame
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **Chart-local smoothness of the sources**: the Yang–Mills source `J_ν(g, g⁻¹, H, DH, Ψ, Ψ̄)` is
smooth near every point whose inverse-metric slot is a Lorentzian chart (`IsLorChart`), the Higgs
source and the Dirac-stress coefficients are smooth.  This is what back-reacting **charged**
spinors satisfy: their current contains the adapted frame `frU(g⁻¹)`, smooth exactly on the
Lorentzian charts (`GenChNoGo.not_smSmooth_of_charged`: the global `SMSmooth` fails). -/
structure SMSmoothL (SM : SMData (MatLie m) V S S') : Prop where
  J : ∀ ν (p : Met × Met × V × (Fin 4 → V) × S × S'), IsLorChart p.2.1 →
    ContDiffAt ℝ ∞ (fun p : Met × Met × V × (Fin 4 → V) × S × S' =>
      SM.Jcur p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ν) p
  SH : ContDiff ℝ ∞ (fun p : Met × Met × V × S × S' =>
    SM.SH p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  P2 : ∀ A B, ContDiff ℝ ∞ (fun p : V × S' × S => SM.TD.P'' A B p.1 p.2.1 p.2.2)

variable {SM : SMData (MatLie m) V S S'}

/-- Global smoothness implies chart-local smoothness. -/
theorem SMSmooth.toL (hS : SMSmooth SM) : SMSmoothL SM :=
  ⟨fun ν _ _ => (hS.J ν).contDiffAt, hS.SH, hS.P2⟩

@[fun_prop]
theorem ContDiffAt.JcurL (hS : SMSmoothL SM) {f1 f2 : E → Met} {f3 : E → V}
    {f4 : E → Fin 4 → V} {f5 : E → S} {f6 : E → S'} {x : E} (h1 : ContDiffAt ℝ ∞ f1 x)
    (h2 : ContDiffAt ℝ ∞ f2 x) (h3 : ContDiffAt ℝ ∞ f3 x) (h4 : ContDiffAt ℝ ∞ f4 x)
    (h5 : ContDiffAt ℝ ∞ f5 x) (h6 : ContDiffAt ℝ ∞ f6 x) (hc : IsLorChart (f2 x)) (ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => SM.Jcur (f1 y) (f2 y) (f3 y) (f4 y) (f5 y) (f6 y) ν) x :=
  (hS.J ν (f1 x, f2 x, f3 x, f4 x, f5 x, f6 x) hc).comp
    (f := fun y => (f1 y, f2 y, f3 y, f4 y, f5 y, f6 y)) x
    (h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk h6)))))

@[fun_prop]
theorem ContDiffAt.SHL (hS : SMSmoothL SM) {f1 f2 : E → Met} {f3 : E → V} {f5 : E → S}
    {f6 : E → S'} {x : E} (h1 : ContDiffAt ℝ ∞ f1 x) (h2 : ContDiffAt ℝ ∞ f2 x)
    (h3 : ContDiffAt ℝ ∞ f3 x) (h5 : ContDiffAt ℝ ∞ f5 x) (h6 : ContDiffAt ℝ ∞ f6 x) :
    ContDiffAt ℝ ∞ (fun y => SM.SH (f1 y) (f2 y) (f3 y) (f5 y) (f6 y)) x :=
  hS.SH.contDiffAt.comp (f := fun y => (f1 y, f2 y, f3 y, f5 y, f6 y)) x
    (h1.prodMk (h2.prodMk (h3.prodMk (h5.prodMk h6))))

@[fun_prop]
theorem ContDiffAt.P2L (hS : SMSmoothL SM) {f3 : E → V} {f5 : E → S} {f6 : E → S'} {x : E}
    (h3 : ContDiffAt ℝ ∞ f3 x) (h6 : ContDiffAt ℝ ∞ f6 x) (h5 : ContDiffAt ℝ ∞ f5 x)
    (A B : Fin 4) : ContDiffAt ℝ ∞ (fun y => SM.TD.P'' A B (f3 y) (f6 y) (f5 y)) x :=
  (hS.P2 A B).contDiffAt.comp (f := fun y => (f3 y, f6 y, f5 y)) x (h3.prodMk (h6.prodMk h5))

end Prelude

end RenewalGeometry.GenChL

/-! #### `smooth_E` (from `Gravity/ActualJetSmoothness.lean`) -/
namespace RenewalGeometry.ActualJetSmooth.ChL
open RenewalGeometry ActualJetSystem ActualJetFrame ActualJetWriter HarmonicDefect FrameCurvature
  ActualJetRecon ActualJetGauge SpinorProlongation TwistedHalfRicci ActualJetSpinor
open scoped ContDiff
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
theorem smooth_EL (hS : GenChL.SMSmoothL SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) (a : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).E a) x0 := by
  simp (config := { maxSteps := 4000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    gradOfPQ, lorentzSign, LEf, lowT, ymCorrF, dginv, chr]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)
end RenewalGeometry.ActualJetSmooth.ChL

/-! #### `smooth_Pm` (from `Gravity/ActualJetSmoothness.lean`) -/
namespace RenewalGeometry.ActualJetSmooth.ChL
open RenewalGeometry ActualJetSystem ActualJetFrame ActualJetWriter HarmonicDefect FrameCurvature
  ActualJetRecon ActualJetGauge SpinorProlongation TwistedHalfRicci ActualJetSpinor
open scoped ContDiff
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
theorem smooth_PmL (hS : GenChL.SMSmoothL SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Pm) x0 := by
  simp only [Fsys, recon, lowerOf, ofP, cof, gradOfpq, gradOfPQ, lorentzSign, LPif, lowVf,
    dginv, chr]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)
end RenewalGeometry.ActualJetSmooth.ChL

/-! #### `smooth_p` (from `Gravity/ActualJetSmoothness.lean`) -/
namespace RenewalGeometry.ActualJetSmooth.ChL
open RenewalGeometry ActualJetSystem ActualJetFrame ActualJetWriter HarmonicDefect FrameCurvature
  ActualJetRecon ActualJetGauge SpinorProlongation TwistedHalfRicci ActualJetSpinor
open scoped ContDiff
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
set_option maxHeartbeats 3000000 in
theorem smooth_pL (hS : GenChL.SMSmoothL SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).p μ ν) x0 := by
  simp (config := { maxSteps := 8000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    gradOfPQ, lorentzSign, AdaptedFrame.Lp, qRem, ricciJ, dchr1, nablaC, cUp, dcUp, cDown, chr,
    dginv, traceRev, trG, stressF, ymStressB, higgsStressB, DiracStressForm.coord,
    DiracStressForm.frame, XnatU, mass, Module.End.smul_def, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)
end RenewalGeometry.ActualJetSmooth.ChL

/-! #### `smooth_X` (from `Gravity/ActualJetSmoothness.lean`) -/
namespace RenewalGeometry.ActualJetSmooth.ChL
open RenewalGeometry ActualJetSystem ActualJetFrame ActualJetWriter HarmonicDefect FrameCurvature
  ActualJetRecon ActualJetGauge SpinorProlongation TwistedHalfRicci ActualJetSpinor
open scoped ContDiff
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
set_option maxHeartbeats 8000000 in
theorem smooth_XL (hS : GenChL.SMSmoothL SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) (a : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).X a) x0 := by
  simp (config := { maxSteps := 16000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    gradOfPQ, lorentzSign, XrowF, omegaU, Gfun, spinPart, mass, ipg, cv1, chr, dginv, lcΓ, DHf,
    frT2, traceRev, trG, stressF, ymStressB, higgsStressB, DiracStressForm.coord,
    DiracStressForm.frame, rhoF, XnatU, Module.End.smul_def, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)
end RenewalGeometry.ActualJetSmooth.ChL

/-! #### `smooth_Xb` (from `Gravity/ActualJetSmoothness.lean`) -/
namespace RenewalGeometry.ActualJetSmooth.ChL
open RenewalGeometry ActualJetSystem ActualJetFrame ActualJetWriter HarmonicDefect FrameCurvature
  ActualJetRecon ActualJetGauge SpinorProlongation TwistedHalfRicci ActualJetSpinor
open scoped ContDiff
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
set_option maxHeartbeats 8000000 in
theorem smooth_XbL (hS : GenChL.SMSmoothL SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) (a : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Xb a) x0 := by
  simp (config := { maxSteps := 16000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    gradOfPQ, lorentzSign, XrowF, omegaU, Gfun, spinPart, mass, ipg, cv1, chr, dginv, lcΓ, DHf,
    frT2, traceRev, trG, stressF, ymStressB, higgsStressB, DiracStressForm.coord,
    DiracStressForm.frame, rhoF, XnatU, Module.End.smul_def, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)
end RenewalGeometry.ActualJetSmooth.ChL

/-! #### `Fsys_smooth` (from `Gravity/ActualJetSmoothness.lean`) -/
namespace RenewalGeometry.ActualJetSmooth.ChL
open RenewalGeometry ActualJetSystem ActualJetFrame ActualJetWriter HarmonicDefect FrameCurvature
  ActualJetRecon ActualJetGauge SpinorProlongation TwistedHalfRicci ActualJetSpinor
open scoped ContDiff
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
/-- **`prop:actual-jet-writer`: the forcing `𝓕(𝒰)` is a smooth function of the actual-jet state**
on the Lorentzian chart (every block). -/
theorem Fsys_smoothL (SM : SMData (MatLie m) V S S') (hS : GenChL.SMSmoothL SM) {x0 : StateP m V S S'}
    (hx : MetChart x0.1) :
    (∀ μ ν, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).g μ ν) x0) ∧
    (∀ μ ν, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).p μ ν) x0) ∧
    (∀ a μ ν, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).q a μ ν) x0) ∧
    (∀ i, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).A i) x0) ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).E a) x0) ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).B a) x0) ∧
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).H) x0 ∧
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Pm) x0 ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Q a) x0) ∧
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).ψ) x0 ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).X a) x0) ∧
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).ψb) x0 ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Xb a) x0) :=
  ⟨smooth_g SM hx, RenewalGeometry.ActualJetSmooth.ChL.smooth_pL SM hS hx, smooth_q SM hx, smooth_A SM hx, RenewalGeometry.ActualJetSmooth.ChL.smooth_EL SM hS hx,
    smooth_B SM hx, smooth_H SM hx, RenewalGeometry.ActualJetSmooth.ChL.smooth_PmL SM hS hx, smooth_Q SM hx, smooth_ψ SM hx,
    RenewalGeometry.ActualJetSmooth.ChL.smooth_XL SM hS hx, smooth_ψb SM hx, RenewalGeometry.ActualJetSmooth.ChL.smooth_XbL SM hS hx⟩
end RenewalGeometry.ActualJetSmooth.ChL

/-! #### `contDiffAt_Fsys_state` (from `Continuum/ActualJetKatoRealization.lean`) -/
namespace RenewalGeometry.ActualJetKato.ChL
open Finset Set Filter Topology
open scoped ContDiff
open ActualJetSystem ActualJetSmooth ActualJetWriter FrameCurvature
  TwistedHalfRicci
set_option linter.unusedSectionVars false
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ) (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)
variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
/-- The forcing `𝓕` is smooth on the chart as a `StateP`-valued map. -/
theorem contDiffAt_Fsys_stateL (hS : GenChL.SMSmoothL SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x : StateP m V S S' => toS (Fsys SM (ofP x))) x0 := by
  obtain ⟨hg, hp, hq, hA, hE, hB, hH, hPm, hQ, hψ, hX, hψb, hXb⟩ := RenewalGeometry.ActualJetSmooth.ChL.Fsys_smoothL SM hS hx
  have pi2 : ∀ {f : StateP m V S S' → Fin 4 → Fin 4 → ℝ},
      (∀ μ ν, ContDiffAt ℝ ∞ (fun x => f x μ ν) x0) → ContDiffAt ℝ ∞ f x0 := by
    intro f h
    rw [contDiffAt_pi]; intro μ; rw [contDiffAt_pi]; intro ν; exact h μ ν
  have pi3 : ∀ {f : StateP m V S S' → Fin 3 → Fin 4 → Fin 4 → ℝ},
      (∀ a μ ν, ContDiffAt ℝ ∞ (fun x => f x a μ ν) x0) → ContDiffAt ℝ ∞ f x0 := by
    intro f h
    rw [contDiffAt_pi]; intro a; exact pi2 (h a)
  simp only [toS]
  exact ((pi2 hg).prodMk ((pi2 hp).prodMk (pi3 hq))).prodMk
    ((contDiffAt_pi.2 hA).prodMk ((contDiffAt_pi.2 hE).prodMk ((contDiffAt_pi.2 hB).prodMk
      (hH.prodMk (hPm.prodMk ((contDiffAt_pi.2 hQ).prodMk (hψ.prodMk
        ((contDiffAt_pi.2 hX).prodMk (hψb.prodMk (contDiffAt_pi.2 hXb))))))))))
end RenewalGeometry.ActualJetKato.ChL

/-! #### `actual_jet_kato_realization` (from `Continuum/ActualJetKatoRealization.lean`) -/
namespace RenewalGeometry.ActualJetKato.ChL
open Finset Set Filter Topology
open scoped ContDiff
open ActualJetSystem ActualJetSmooth ActualJetWriter FrameCurvature
  TwistedHalfRicci
set_option linter.unusedSectionVars false
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ) (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)
variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
/-- **The actual-jet system as a quasilinear symmetric hyperbolic system**
(`eq:generated-symmetric-system`; `prop:actual-jet-writer`).  For theory data with smooth
sources (`GenChL.SMSmoothL`) and forms satisfying the positivity and Clifford unitarity relations
(`UnitaryForms`) there are Euclidean coordinates `κ` of the realified actual-jet state space
(`ipState(κ⁻¹v, κ⁻¹w) = v ⬝ w`) such that for every compact set `K` of coordinate states in the
Lorentzian chart there are **globally smooth coefficient maps** `A^j(v)` (`j = 1, 2, 3`), `F(v)`
on `ℝ^n` with **symmetric** `A^j(v)`, which on `K` are the actual-jet principal operators and
forcing: `Σ_b A^j(v)_{ab} w_b = (κ 𝒜^j(g(v)) κ⁻¹ w)_a` with the adapted frame
`frameU(g(v)⁻¹)`, and `F(v) = κ 𝓕(κ⁻¹v)`. -/
theorem actual_jet_kato_realizationL (hS : GenChL.SMSmoothL SM) (hU : UnitaryForms SM bG bV bS bS') :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) := by
  obtain ⟨κ, hκ⟩ := exists_state_coords hU
  refine ⟨κ, hκ, fun K hK hKc => ?_⟩
  set O : Set (Fin (dimS m V S S') → ℝ) := κ.symm ⁻¹' chartSet with hOdef
  have hκc : Continuous κ.symm := (contDiff_linearEquiv κ.symm.toLinearMap).continuous
  have hO : IsOpen O := isOpen_chartSet.preimage hκc
  have hKO : K ⊆ O := fun v hv => hKc v hv
  have hκs : ContDiff ℝ ∞ κ.symm := contDiff_linearEquiv κ.symm.toLinearMap
  have hκf : ContDiff ℝ ∞ κ := contDiff_linearEquiv κ.toLinearMap
  -- the chart coefficient functions are smooth on `O`
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
    (Φ := fun a v => κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    fun a v hv => by
      have h1 := (RenewalGeometry.ActualJetKato.ChL.contDiffAt_Fsys_stateL hS hv).comp v hκs.contDiffAt
      have h2 := (hκf.contDiffAt (x := toS (Fsys SM (ofP (κ.symm v))))).comp v h1
      exact ((contDiffAt_pi.1 h2) a).contDiffWithinAt
  set AF' : (Fin (dimS m V S S') → ℝ) → AdaptedFrame := fun v =>
    mkFrame (L' v) (fun j => β' j v) (fun a j => E' (a, j) v) with hAF'
  have hAFK : ∀ v ∈ K, AF' v = frameU (ginvOf (κ.symm v).1.1) := fun v hv =>
    mkFrame_eq (hL'K v hv) (funext fun j => hβ'K j v hv) (funext fun a => funext fun j =>
      hE'K (a, j) v hv)
  refine ⟨fun j a b v => princEntry SM bG bV bS bS' κ (AF' v) j a b, F', fun j a b => ?_,
    fun j a b v => princEntry_symm hU κ (AF' v) j a b, hF's, fun v hv j a w => ?_,
    fun v hv a => hF'K a v hv⟩
  · exact contDiff_princEntry_mkFrame κ hL's (fun j => hβ's j) (fun a j => hE's (a, j)) j a b
  · rw [sum_princEntry hU hκ, hAFK v hv]
end RenewalGeometry.ActualJetKato.ChL

/-! #### `contDiff_rA` (from `Continuum/ActualJetStateField.lean`) -/
namespace RenewalGeometry.ActualJetState.ChL
open Finset Set
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci JetCurve
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
set_option maxHeartbeats 4000000 in
theorem contDiff_rAL (hS : GenChL.SMSmoothL SM) (ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => ((z.jet y).res SM).rA ν) := by
  refine contDiff_iff_contDiffAt.2 fun y0 => ?_
  have hgc := fun μ ν => (z.contDiff_gc μ ν).contDiffAt (x := y0)
  have hgi := fun μ ν => (z.contDiff_gi μ ν).contDiffAt (x := y0)
  have hdg := fun α μ ν => (z.contDiff_dg α μ ν).contDiffAt (x := y0)
  have hA := fun μ => (Tuple.contDiff_vec z.A_smooth μ).contDiffAt (x := y0)
  have hdA := fun γ μ => (Tuple.contDiff_pdc z.A_smooth γ μ).contDiffAt (x := y0)
  have hddA := fun δ γ μ => (Tuple.contDiff_pdpdc z.A_smooth δ γ μ).contDiffAt (x := y0)
  have hH := z.H_smooth.contDiffAt (x := y0)
  have hdH := fun γ => (contDiff_pd z.H_smooth γ).contDiffAt (x := y0)
  have hψ := z.ψ_smooth.contDiffAt (x := y0)
  have hψb := z.ψb_smooth.contDiffAt (x := y0)
  have hgfun : ContDiffAt ℝ ∞ (fun y => z.g y) y0 := z.g_smooth.contDiffAt
  have hgifun : ContDiffAt ℝ ∞ (fun y => z.gi y) y0 := z.contDiffAt_gi_fun y0
  have hDH : ContDiffAt ℝ ∞ (fun y => fun μ => pd z.H μ y + ⁅z.A y μ, z.H y⁆) y0 := by
    rw [contDiffAt_pi]; intro μ; fun_prop
  show ContDiffAt ℝ ∞ (fun y => ymRes (z.A y) (fun γ μ => pd z.A γ y μ)
    (fun δ γ μ => pd (pd z.A γ) δ y μ) (z.gi y) (chr (z.gi y) (z.dg y))
    (SM.Jcur (z.g y) (z.gi y) (z.H y) (fun μ => pd z.H μ y + ⁅z.A y μ, z.H y⁆) (z.ψ y) (z.ψb y)) ν)
    y0
  unfold ymRes ymDiv dFm Fm fieldStrength chr
  fun_prop (disch := first | exact hS | exact z.lor y0)
end RenewalGeometry.ActualJetState.ChL

/-! #### `contDiff_rH` (from `Continuum/ActualJetStateField.lean`) -/
namespace RenewalGeometry.ActualJetState.ChL
open Finset Set
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci JetCurve
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
set_option maxHeartbeats 4000000 in
theorem contDiff_rHL (hS : GenChL.SMSmoothL SM) :
    ContDiff ℝ ∞ (fun y => ((z.jet y).res SM).rH) := by
  refine contDiff_iff_contDiffAt.2 fun y0 => ?_
  have hgc := fun μ ν => (z.contDiff_gc μ ν).contDiffAt (x := y0)
  have hgi := fun μ ν => (z.contDiff_gi μ ν).contDiffAt (x := y0)
  have hdg := fun α μ ν => (z.contDiff_dg α μ ν).contDiffAt (x := y0)
  have hA := fun μ => (Tuple.contDiff_vec z.A_smooth μ).contDiffAt (x := y0)
  have hdA := fun γ μ => (Tuple.contDiff_pdc z.A_smooth γ μ).contDiffAt (x := y0)
  have hH := z.H_smooth.contDiffAt (x := y0)
  have hdH := fun γ => (contDiff_pd z.H_smooth γ).contDiffAt (x := y0)
  have hddH := fun δ γ => (contDiff_pd (contDiff_pd z.H_smooth γ) δ).contDiffAt (x := y0)
  have hψ := z.ψ_smooth.contDiffAt (x := y0)
  have hψb := z.ψb_smooth.contDiffAt (x := y0)
  have hgfun : ContDiffAt ℝ ∞ (fun y => z.g y) y0 := z.g_smooth.contDiffAt
  have hgifun : ContDiffAt ℝ ∞ (fun y => z.gi y) y0 := z.contDiffAt_gi_fun y0
  show ContDiffAt ℝ ∞ (fun y => higgsRes (z.A y) (fun γ μ => pd z.A γ y μ) (z.H y)
    (fun γ => pd z.H γ y) (fun δ γ => pd (pd z.H γ) δ y) (z.gi y) (chr (z.gi y) (z.dg y))
    (SM.SH (z.g y) (z.gi y) (z.H y) (z.ψ y) (z.ψb y))) y0
  unfold higgsRes waveH dDH ActualJetGauge.DH chr
  fun_prop (disch := first | exact hS | exact z.lor y0)
end RenewalGeometry.ActualJetState.ChL

/-! #### `contDiff_Etr` (from `Continuum/ActualJetStateField.lean`) -/
namespace RenewalGeometry.ActualJetState.ChL
open Finset Set
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci JetCurve
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
set_option maxHeartbeats 8000000 in
theorem contDiff_EtrL (hS : GenChL.SMSmoothL SM) (μ ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => ((z.jet y).res SM).Etr μ ν) := by
  refine contDiff_iff_contDiffAt.2 fun y0 => ?_
  have hgc := fun μ ν => (z.contDiff_gc μ ν).contDiffAt (x := y0)
  have hgi := fun μ ν => (z.contDiff_gi μ ν).contDiffAt (x := y0)
  have hdg := fun α μ ν => (z.contDiff_dg α μ ν).contDiffAt (x := y0)
  have hddg := fun β α μ ν => (z.contDiff_ddg β α μ ν).contDiffAt (x := y0)
  have he := fun A μ => (z.contDiff_e A μ).contDiffAt (x := y0)
  have hA := fun μ => (Tuple.contDiff_vec z.A_smooth μ).contDiffAt (x := y0)
  have hdA := fun γ μ => (Tuple.contDiff_pdc z.A_smooth γ μ).contDiffAt (x := y0)
  have hH := z.H_smooth.contDiffAt (x := y0)
  have hdH := fun γ => (contDiff_pd z.H_smooth γ).contDiffAt (x := y0)
  have hψ := z.ψ_smooth.contDiffAt (x := y0)
  have hψb := z.ψb_smooth.contDiffAt (x := y0)
  have hX := fun A => (z.contDiff_Xs SM.D z.ψ_smooth A).contDiffAt (x := y0)
  have hXb := fun A => (z.contDiff_Xs SM.Db z.ψb_smooth A).contDiffAt (x := y0)
  show ContDiffAt ℝ ∞ (fun y => traceRev (z.g y) (z.gi y) (fun a b =>
    einstein (z.g y) (z.gi y) (z.dg y) (z.ddg y) a b + SM.Λ * z.g y a b -
      SM.κ * (ymStressB SM.ipG (z.g y) (z.gi y) (Fm (z.jet y).A (z.jet y).dA) a b +
        higgsStressB SM.ipV SM.lamH SM.vH (z.g y) (z.gi y) (z.H y)
          (fun μ => pd z.H μ y + ⁅z.A y μ, z.H y⁆) a b +
        SM.TD.coord (z.g y) lorentzSign (z.e y) (z.H y) (z.ψ y)
          ((z.jet y).Xs SM.D (z.ψ y) (fun γ => pd z.ψ γ y)) (z.ψb y)
          ((z.jet y).Xs SM.Db (z.ψb y) (fun γ => pd z.ψb γ y)) a b)) μ ν) y0
  simp only [traceRev, trG, einstein, ricci, ricciJ, dchr, dchr1, dchr2, dginv, chr, ymStressB,
    higgsStressB, DiracStressForm.coord, DiracStressForm.frame, cof, Fm, fieldStrength,
    Tuple.jet]
  fun_prop (disch := first | exact hS | exact z.lor y0)
end RenewalGeometry.ActualJetState.ChL

/-! #### `contDiff_bosF` (from `Continuum/ActualJetStateField.lean`) -/
namespace RenewalGeometry.ActualJetState.ChL
open Finset Set
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci JetCurve
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
/-- **The bosonic residual field is smooth** (for smooth theory data). -/
theorem contDiff_bosFL (hS : GenChL.SMSmoothL SM) : ContDiff ℝ ∞ (bosF SM z) :=
  (contDiff_pi.2 fun μ => contDiff_pi.2 fun ν => RenewalGeometry.ActualJetState.ChL.contDiff_EtrL SM z hS μ ν).prodMk
    ((contDiff_pi.2 fun ν => RenewalGeometry.ActualJetState.ChL.contDiff_rAL SM z hS ν).prodMk (RenewalGeometry.ActualJetState.ChL.contDiff_rHL SM z hS))
end RenewalGeometry.ActualJetState.ChL

/-! #### `bosR_smooth_E` (from `Continuum/GeneratedResidualSmooth.lean`) -/
namespace RenewalGeometry.GenResMaps.ChL
open Finset Set Filter Topology
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetSpinor
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {j₀ : HJ2 m V S S'}
set_option maxHeartbeats 8000000 in
/-- **The Einstein component of the raw bosonic residual is smooth on the chart.** -/
theorem bosR_smooth_EL (SM : SMData (MatLie m) V S S') (hS : GenChL.SMSmoothL SM)
    (hj : j₀ ∈ chartJ2 m V S S') (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => (bosR SM j).1 μ ν) j₀ := by
  have hx := hj
  simp (config := { maxSteps := 16000000 }) only [bosR, TactR, XsR, omR, frR, deR, dψR, cov,
    omegaU, Gfun, spinPart, ipg, cv1, chr, dginv, traceRev, trG, einstein, ricci, ricciJ, dchr,
    dchr1, dchr2, ymStressB, higgsStressB, DiracStressForm.coord, DiracStressForm.frame, cof,
    lorentzSign, Fm, fieldStrength, ActualJetGauge.DH, mass, Module.End.smul_def,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)
end RenewalGeometry.GenResMaps.ChL

/-! #### `bosR_smooth_A` (from `Continuum/GeneratedResidualSmooth.lean`) -/
namespace RenewalGeometry.GenResMaps.ChL
open Finset Set Filter Topology
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetSpinor
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {j₀ : HJ2 m V S S'}
set_option maxHeartbeats 4000000 in
/-- **The Yang–Mills component of the raw bosonic residual is smooth on the chart.** -/
theorem bosR_smooth_AL (SM : SMData (MatLie m) V S S') (hS : GenChL.SMSmoothL SM)
    (hj : j₀ ∈ chartJ2 m V S S') (ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => (bosR SM j).2.1 ν) j₀ := by
  have hx := hj
  simp (config := { maxSteps := 4000000 }) only [bosR, ymRes, ymDiv, dFm, Fm, fieldStrength, chr,
    DH_eta]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)
end RenewalGeometry.GenResMaps.ChL

/-! #### `bosR_smooth_H` (from `Continuum/GeneratedResidualSmooth.lean`) -/
namespace RenewalGeometry.GenResMaps.ChL
open Finset Set Filter Topology
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetSpinor
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {j₀ : HJ2 m V S S'}
set_option maxHeartbeats 4000000 in
/-- **The Higgs component of the raw bosonic residual is smooth on the chart.** -/
theorem bosR_smooth_HL (SM : SMData (MatLie m) V S S') (hS : GenChL.SMSmoothL SM)
    (hj : j₀ ∈ chartJ2 m V S S') :
    ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => (bosR SM j).2.2) j₀ := by
  have hx := hj
  simp (config := { maxSteps := 4000000 }) only [bosR, higgsRes, waveH, dDH, chr,
    ActualJetGauge.DH]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)
end RenewalGeometry.GenResMaps.ChL

/-! #### `bosR_smooth` (from `Continuum/GeneratedResidualSmooth.lean`) -/
namespace RenewalGeometry.GenResMaps.ChL
open Finset Set Filter Topology
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetSpinor
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {j₀ : HJ2 m V S S'}
/-- **The raw bosonic residual map is smooth on the chart.** -/
theorem bosR_smoothL (SM : SMData (MatLie m) V S S') (hS : GenChL.SMSmoothL SM)
    (hj : j₀ ∈ chartJ2 m V S S') : ContDiffAt ℝ ∞ (bosR SM) j₀ := by
  have h1 : ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => (bosR SM j).1) j₀ := by
    rw [contDiffAt_pi]; intro μ; rw [contDiffAt_pi]; intro ν
    exact RenewalGeometry.GenResMaps.ChL.bosR_smooth_EL SM hS hj μ ν
  have h2 : ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => (bosR SM j).2.1) j₀ := by
    rw [contDiffAt_pi]; intro ν
    exact RenewalGeometry.GenResMaps.ChL.bosR_smooth_AL SM hS hj ν
  exact h1.prodMk (h2.prodMk (RenewalGeometry.GenResMaps.ChL.bosR_smooth_HL SM hS hj))
end RenewalGeometry.GenResMaps.ChL

/-! #### `contDiff_densR` (from `Continuum/GeneratedNoetherIdentities.lean`) -/
namespace RenewalGeometry.GenNoether.ChL
open Finset Set
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState JetCurve
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
theorem contDiff_densRL (hS : GenChL.SMSmoothL SM) (ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => densR SM z y ν) := by
  have h1 := contDiff_rho z
  have h2 := z.contDiff_gi
  have h3 := fun β => RenewalGeometry.ActualJetState.ChL.contDiff_rAL SM z hS β
  show ContDiff ℝ ∞ (fun y => rho z y • ∑ β, z.gi y ν β • ((z.jet y).res SM).rA β)
  fun_prop
end RenewalGeometry.GenNoether.ChL

/-! #### `contDiff_densJ` (from `Continuum/GeneratedNoetherIdentities.lean`) -/
namespace RenewalGeometry.GenNoether.ChL
open Finset Set
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState JetCurve
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
/-- The current density is smooth for smooth theory data. -/
theorem contDiff_densJL (hS : GenChL.SMSmoothL SM) (ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => densJ SM z y ν) := by
  have : (fun y => densJ SM z y ν) = fun y => ymDens z y ν - densR SM z y ν :=
    funext fun y => by rw [densR_eq]; abel
  rw [this]
  exact (contDiff_ymDens z ν).sub (RenewalGeometry.GenNoether.ChL.contDiff_densRL SM z hS ν)
end RenewalGeometry.GenNoether.ChL

/-! #### `div_rA` (from `Continuum/GeneratedNoetherIdentities.lean`) -/
namespace RenewalGeometry.GenNoether.ChL
open Finset Set
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState JetCurve
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
/-- **The divergence of the Yang–Mills residual** (Yang–Mills Bianchi identity): for every smooth
tuple and smooth theory data, `ϱ D^νr^A_ν = -ϱ D^νJ_ν`. -/
theorem div_rAL (hS : GenChL.SMSmoothL SM) (x : ST 3) :
    ∑ ν, (pd (fun y => densR SM z y ν) ν x + ⁅z.A x ν, densR SM z x ν⁆) = -divJ SM z x := by
  have hpd : ∀ ν, pd (fun y => densR SM z y ν) ν x =
      pd (fun y => ymDens z y ν) ν x - pd (fun y => densJ SM z y ν) ν x := by
    intro ν
    have : (fun y => densR SM z y ν) = fun y => ymDens z y ν - densJ SM z y ν :=
      funext fun y => densR_eq SM z y ν
    rw [this]
    unfold SobolevOpen.pd
    rw [fderiv_fun_sub (((contDiff_ymDens z ν).differentiable (by simp)) x)
      (((RenewalGeometry.GenNoether.ChL.contDiff_densJL SM z hS ν).differentiable (by simp)) x)]
    rfl
  have h0 := ym_bianchi_density z x
  unfold divJ
  rw [Finset.sum_congr rfl fun ν _ => by rw [hpd ν, densR_eq, lie_sub], ← sub_eq_zero]
  have : ∑ ν, (pd (fun y => ymDens z y ν) ν x - pd (fun y => densJ SM z y ν) ν x +
      (⁅z.A x ν, ymDens z x ν⁆ - ⁅z.A x ν, densJ SM z x ν⁆)) -
      -∑ ν, (pd (fun y => densJ SM z y ν) ν x + ⁅z.A x ν, densJ SM z x ν⁆) =
      ∑ ν, (pd (fun y => ymDens z y ν) ν x + ⁅z.A x ν, ymDens z x ν⁆) := by
    rw [sub_neg_eq_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    abel
  rw [this, h0]
end RenewalGeometry.GenNoether.ChL

/-! #### `div_rA_eq_zero` (from `Continuum/GeneratedNoetherIdentities.lean`) -/
namespace RenewalGeometry.GenNoether.ChL
open Finset Set
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState JetCurve
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
variable {SM}
/-- **The Yang–Mills residual is covariantly conserved wherever the Higgs and Dirac equations hold**
(`ϱ D^νr^A_ν = 0`), for theory data satisfying the current Noether identity. -/
theorem div_rA_eq_zeroL (hN : CurrentNoether SM) (hS : GenChL.SMSmoothL SM) {x : ST 3}
    (hH : (bosF SM z x).2.2 = 0) (hD : dirF SM z x = 0) :
    ∑ ν, (pd (fun y => densR SM z y ν) ν x + ⁅z.A x ν, densR SM z x ν⁆) = 0 := by
  rw [RenewalGeometry.GenNoether.ChL.div_rAL SM z hS x, divJ_eq_zero z hN hH hD, neg_zero]
end RenewalGeometry.GenNoether.ChL

/-! #### `contDiff_gaussF` (from `Continuum/GeneratedGaussPropagation.lean`) -/
namespace RenewalGeometry.GenGauss.ChL
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  JetCurve GenConstraint GenNoether
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')
theorem contDiff_gaussFL (hS : GenChL.SMSmoothL SM) : ContDiff ℝ ∞ (gaussF SM z) := by
  have : gaussF SM z = fun y => ∑ ν, z.e y 0 ν • ((z.jet y).res SM).rA ν :=
    funext (gaussF_eq SM z)
  rw [this]
  have h1 := z.contDiff_e
  have h2 := fun ν => RenewalGeometry.ActualJetState.ChL.contDiff_rAL SM z hS ν
  fun_prop
end RenewalGeometry.GenGauss.ChL
