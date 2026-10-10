/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledRows
import RenewalGeometry.Continuum.GeneratedHarmonicPropagation

/-!
# The metric rows of the coupled defect system: the reduced Einstein equation with the
# auxiliary Dirac stress

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.  For a coupled solution (`GenCplRows.CplSol`), the metric `p`-rows of `W` and of
the actual-jet state of its head tuple `z` differ only through the Dirac stress evaluated at the
auxiliary spinor jets of `W` instead of the actual ones:

* `stressDiff` — `ΔS = T^{SM}(j¹W) - T^{SM}(j¹z)` (the stress at the reconstructed first jets);
* **`etr_eq`** — `𝓔^{tr}(z) = κ trRev(ΔS) + ∇_{(μ}C_{ν)}`;
* **`reduced_einstein_cpl`** — `Ĝ(z) + Λg - κ(T(z) + ΔS) = 0` on the slab: the head metric solves
  the reduced Einstein equation with the source `T(z) + ΔS`.
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplEin

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState GenConstraint
  GenSpinorDefect GenHiggsDefect SymHypEnergy GenCplRows GenStress

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
  {a b : ℝ}

variable (SM) in
/-- **The stress difference** `ΔS = T^{SM}(j¹W) - T^{SM}(j¹𝒰(z))` at the reconstructed first jets. -/
def stressDiff (W : ST 3 → StateP m V S S') (z : Tuple m V S S') (x : ST 3) (μ ν : Fin 4) : ℝ :=
  stressF SM (recon SM (ofP (W x))) μ ν - stressF SM (recon SM (ofP (stateF SM z x))) μ ν

/-- Principal operators of increments with vanishing metric blocks have vanishing metric blocks. -/
theorem princL_met_zero (v : StateP m V S S') (j : Fin 3) {u : StateP m V S S'} (hu : u.1 = 0) :
    (princL SM v j u).1 = 0 := by
  obtain ⟨⟨ug, up, uq⟩, ur⟩ := u
  simp only [Prod.mk.injEq] at hu
  obtain ⟨rfl, rfl, rfl⟩ := hu
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext μ ν; rfl
  · funext μ ν
    simp [princL, ActualJetSystem.princ, toP, ofP]
  · funext c μ ν
    simp [princL, ActualJetSystem.princ, toP, ofP]

/-- The `p`-block of the forcing. -/
theorem Fsys_p (v : StateP m V S S') (μ ν : Fin 4) : (toP (Fsys SM (ofP v))).1.2.1 μ ν =
    (recon SM (ofP v)).AF.N * ((recon SM (ofP v)).AF.Lp (recon SM (ofP v)).de
      (fun α => (recon SM (ofP v)).dg α μ ν) - 2 * qRem (recon SM (ofP v)).g
      (recon SM (ofP v)).gi (recon SM (ofP v)).dg μ ν +
      2 * SM.κ * traceRev (recon SM (ofP v)).g (recon SM (ofP v)).gi
        (stressF SM (recon SM (ofP v))) μ ν + 2 * SM.Λ * (recon SM (ofP v)).g μ ν) := rfl

theorem stressF_withX (fj : FirstJet (MatLie m) V S S') (X : Fin 4 → S) (Xb : Fin 4 → S')
    (μ ν : Fin 4) : stressF SM (withX fj X Xb) μ ν - stressF SM fj μ ν =
      SM.TD.coord fj.g lorentzSign fj.AF.fr fj.H fj.ψ X fj.ψb Xb μ ν -
        SM.TD.coord fj.g lorentzSign fj.AF.fr fj.H fj.ψ fj.X fj.ψb fj.Xb μ ν := by
  simp only [stressF, withX]
  ring

/-- **The metric rows of a coupled solution**: `2N𝓔^{tr} + 𝔊 = 2Nκ trRev(ΔS)`. -/
theorem p_rows (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) (μ ν : Fin 4) :
    2 * (frameU (z.gi x)).N * (bosF SM z x).1 μ ν +
        gaugeForce (frameU (z.gi x)) (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν =
      (frameU (z.gi x)).N * (2 * SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν) := by
  have hO := isOpen_openSlab (d := 3) a b
  have hrow := congrArg (fun v : StateP m V S S' => v.1.2.1 μ ν) (diff_row h hx)
  -- the metric blocks of the difference and of its derivatives vanish
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := h.ms.smooth.of_le (by norm_cast)
  have hUd : DifferentiableOn ℝ (stateF SM z) (openSlab a b) :=
    ((contDiff_stateF SM z).differentiable (by simp)).differentiableOn
  have hpdB := pd_block_eq' hO hW1 hUd (prB m V S S') h.bos
  have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW1 one_ne_zero hx
  have hdU : DifferentiableAt ℝ (stateF SM z) x := (contDiff_stateF SM z).differentiable (by simp) x
  have hm0 : ∀ γ, (pd (fun y => W y - stateF SM z y) γ x).1 = 0 := by
    intro γ
    rw [GenDefJet.pd_sub_eq hdW hdU, Prod.fst_sub, sub_eq_zero]
    exact (prB_eq_iff.1 (hpdB x hx γ)).1
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum, Prod.fst_sub, Prod.snd_sub,
    Pi.add_apply, Pi.sub_apply, Finset.sum_apply] at hrow
  rw [hm0 0] at hrow
  simp only [princL_met_zero (SM := SM) _ _ (hm0 _)] at hrow
  simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Finset.sum_const_zero, add_zero] at hrow
  -- the forcing difference
  have hD : dirF SM z x = 0 := h.dir x hx
  have hdD : ∀ j : Fin 3, pd (dirF SM z) j.succ x = 0 := fun j =>
    pd_eq_zero_of_eventually (Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => h.dir y hy)
      j.succ
  have herr := GenHarmonic.errF_p_gen SM z x hD hdD μ ν
  have hrec := recon_withX (SM := SM) (h.bos x hx) (h.ψ_eq hx) (h.ψb_eq hx)
  have hN : (recon SM (ofP (stateF SM z x))).AF = frameU (z.gi x) := rfl
  have hg : (recon SM (ofP (stateF SM z x))).g = z.g x := rfl
  have hgi : (recon SM (ofP (stateF SM z x))).gi = z.gi x := rfl
  rw [Fsys_p, Fsys_p, herr] at hrow
  rw [hrec] at hrow
  have hsd : stressDiff SM W z x = fun μ ν =>
      stressF SM (withX (recon SM (ofP (stateF SM z x))) (recon SM (ofP (W x))).X
        (recon SM (ofP (W x))).Xb) μ ν - stressF SM (recon SM (ofP (stateF SM z x))) μ ν := by
    funext μ ν
    unfold stressDiff
    rw [← hrec]
  rw [hsd, ActualJetSystem.traceRev_sub]
  simp only [withX] at hrow ⊢
  rw [hN, hg, hgi] at hrow ⊢
  linarith

/-- **`𝓔^{tr}(z) = κ trRev(ΔS) + ∇_{(μ}C_{ν)}`** along a coupled solution. -/
theorem etr_eq (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) (μ ν : Fin 4) :
    (bosF SM z x).1 μ ν = SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν +
      symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν := by
  have hp := p_rows h hx μ ν
  have hNpos := (frameU (z.gi x)).N_pos
  unfold gaugeForce at hp
  have h2 : 2 * (frameU (z.gi x)).N * ((bosF SM z x).1 μ ν - (SM.κ * traceRev (z.g x) (z.gi x)
      (stressDiff SM W z x) μ ν + symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν)) = 0 := by
    linarith
  have hN2 : 2 * (frameU (z.gi x)).N ≠ 0 := by positivity
  linarith [(mul_eq_zero.mp h2).resolve_left hN2]

/-- **The reduced Einstein equation with the auxiliary Dirac stress**:
`Ĝ(z) + Λg - κ(T(z) + ΔS) = 0` along a coupled solution. -/
theorem reduced_einstein_cpl (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b)
    (μ ν : Fin 4) :
    reducedEinstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν + SM.Λ * z.g x μ ν -
      SM.κ * (Tf SM z x μ ν + stressDiff SM W z x μ ν) = 0 := by
  have hgi := fun a b => z.gi_symm x a b
  have hinv := z.hinv x
  have htr : ∀ μ ν, traceRev (z.g x) (z.gi x) (fun a b => reducedEinstein (z.g x) (z.gi x)
      (z.dg x) (z.ddg x) a b + SM.Λ * z.g x a b -
        SM.κ * (Tf SM z x a b + stressDiff SM W z x a b)) μ ν = 0 := by
    intro μ ν
    have e1 : (fun a b => reducedEinstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) a b +
        SM.Λ * z.g x a b - SM.κ * (Tf SM z x a b + stressDiff SM W z x a b)) =
        fun a b => (reducedEinstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) a b + SM.Λ * z.g x a b -
          SM.κ * Tf SM z x a b) - SM.κ * stressDiff SM W z x a b := by
      funext a b; ring
    rw [e1, ActualJetSystem.traceRev_sub, harmonic_residual_trace_reversal (z.g x) (z.gi x)
      (z.dg x) (z.ddg x) hgi hinv (by simp) (Tf SM z x) SM.Λ SM.κ μ ν]
    have e2 : traceRev (z.g x) (z.gi x) (fun a b => einstein (z.g x) (z.gi x) (z.dg x) (z.ddg x)
        a b + SM.Λ * z.g x a b - SM.κ * Tf SM z x a b) μ ν = (bosF SM z x).1 μ ν := rfl
    have e3 : traceRev (z.g x) (z.gi x) (fun a b => SM.κ * stressDiff SM W z x a b) μ ν =
        SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν := by
      have htr : trG (z.gi x) (fun a b => SM.κ * stressDiff SM W z x a b) =
          SM.κ * trG (z.gi x) (stressDiff SM W z x) := by
        unfold trG
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      unfold traceRev
      rw [htr]
      ring
    rw [e2, e3, etr_eq h hx μ ν]
    ring
  exact GenHarmonic.traceRev_inj (z.g x) (z.gi x) hgi hinv _ htr μ ν

end RenewalGeometry.GenCplEin
