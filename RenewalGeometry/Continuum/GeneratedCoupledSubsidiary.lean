/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledStressDiff

/-!
# The subsidiary equation of the coupled defect system

Einstein–Standard-Model action-closure manuscript, `prop:subsidiary`
(`eq:subsidiary`) and `lem:generated-physical-identification`, coupled spinors.  Along a coupled
solution with back-reacting theory data, the head metric solves the reduced Einstein equation with
the source `T(z) + ΔS` (`GenCplEin.reduced_einstein_cpl`, `GenCplSD.stressDiff_eq`); the
contracted Bianchi identity (`ContractedBianchiJet.SubsidiarySource.subsidiary_with_source`)
gives

`□c_b + Ric^l{}_bc_l = -2κ(∇^μT_{μb}(z) + ∇^μΔS_{μb})`,

so that, where the stress of `z` is conserved (Noether identity on the matter equations), the
harmonic gauge covector is forced only by the divergence of the auxiliary Dirac stress
(**`coupled_subsidiary`**).
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplSub

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov GenCplN GenCplRows GenCplX GenCplP GenCplEin GenDStress GenCplBox GenCplSD GenStress
  GenHarmonic ContractedBianchiJet ContractedBianchiJet.SubsidiarySource

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} (hC : CoupledDirac SM) {W : ST 3 → StateP m V S S'}
  {z : Tuple m V S S'} {a b : ℝ}

theorem contDiff_θF (A μ : Fin 4) : ContDiff ℝ ∞ (fun y => θF z y A μ) := by
  have h1 := z.contDiff_gc
  have h2 := contDiff_fr (z := z)
  unfold θF cof
  fun_prop

theorem contDiff_kinT {S₁ S₂ : Type*} [NormedAddCommGroup S₁] [NormedSpace ℝ S₁]
    [FiniteDimensional ℝ S₁] [NormedAddCommGroup S₂] [NormedSpace ℝ S₂] [FiniteDimensional ℝ S₂]
    (D : DiracData (MatLie m) V S₁) (P : S₂ →ₗ[ℝ] S₁ →ₗ[ℝ] ℝ) {ψ : ST 3 → S₁} {ψb : ST 3 → S₂}
    {X : ST 3 → Fin 4 → S₁} {Xb : ST 3 → Fin 4 → S₂} (hψ : ContDiff ℝ ∞ ψ)
    (hψb : ContDiff ℝ ∞ ψb) (hX : ContDiff ℝ ∞ X) (hXb : ContDiff ℝ ∞ Xb) (A B : Fin 4) :
    ContDiff ℝ ∞ (fun y => kinT D P (ψ y) (X y) (ψb y) (Xb y) A B) := by
  have hc : ∀ (C : Fin 4) {f : ST 3 → S₁}, ContDiff ℝ ∞ f →
      ContDiff ℝ ∞ (fun y => D.Fr.c C (f y)) := fun C f hf =>
    (LinearMap.toContinuousLinearMap (D.Fr.c C)).contDiff.comp hf
  have hP : ∀ {f : ST 3 → S₂} {g : ST 3 → S₁}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      ContDiff ℝ ∞ (fun y => P (f y) (g y)) := fun hf hg =>
    contDiff_iff_contDiffAt.2 fun y => ContDiffAt.bilinApply P hf.contDiffAt hg.contDiffAt
  have hXc := fun C => contDiff_pi.1 hX C
  have hXbc := fun C => contDiff_pi.1 hXb C
  unfold kinT
  exact contDiff_const.mul ((((hP hψb (hc A (hXc B))).add (hP hψb (hc B (hXc A)))).sub
    (hP (hXbc B) (hc A hψ))).sub (hP (hXbc A) (hc B hψ)))

theorem contDiff_ΔSf (hW : ContDiff ℝ ∞ W) (μ ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => ΔSf hC W z y μ ν) := by
  unfold ΔSf
  refine ContDiff.sum fun A _ => ContDiff.sum fun B _ => ?_
  refine ((contDiff_θF A μ).mul (contDiff_θF B ν)).mul ?_
  have hYb : ContDiff ℝ ∞ (Ybf SM W z) := by
    have : Ybf SM W z = fun y => oneFormL SM.Db (Ybt SM W z y) := rfl
    rw [this]
    have hYbt : ContDiff ℝ ∞ (Ybt SM W z) := by
      have : Ybt SM W z = fun y => prXb m V S S' (W y - stateF SM z y) := by
        funext y; simp [Ybt, prXb]
      rw [this]
      exact (prXb m V S S').contDiff.comp (hW.sub (contDiff_stateF SM z))
    exact (LinearMap.toContinuousLinearMap (oneFormL SM.Db)).contDiff.comp hYbt
  exact contDiff_kinT SM.D hC.P z.ψ_smooth z.ψb_smooth (contDiff_Yf SM W z hW) hYb A B

theorem contDiff_reducedE (a' b' : Fin 4) :
    ContDiff ℝ ∞ (fun y => reducedEinstein (z.g y) (z.gi y) (z.dg y) (z.ddg y) a' b' +
      SM.Λ * z.g y a' b') :=
  (contDiff_reducedEinstein z a' b').add (contDiff_const.mul (z.contDiff_gc a' b'))

/-- **The reduced Einstein equation with the auxiliary Dirac stress, with its first
derivatives.** -/
theorem coupled_reduced_jets (hW : ContDiff ℝ ∞ W) (h : CplSol SM W z a b) {x : ST 3}
    (hx : x ∈ openSlab a b) :
    (jet3 z x).resM (jet3 z x).gc (jet3 z x).dgc + SM.Λ • (jet3 z x).g =
        SM.κ • Matrix.of (Tf SM z x) + SM.κ • Matrix.of (ΔSf hC W z x) ∧
      ∀ e, (jet3 z x).dresM (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc e +
        SM.Λ • (jet3 z x).dg e =
        SM.κ • Matrix.of (fun a' b' => pd (fun y => Tf SM z y a' b') e x) +
          SM.κ • Matrix.of (fun a' b' => pd (fun y => ΔSf hC W z y a' b') e x) := by
  have hO := isOpen_openSlab (d := 3) a b
  have hRE : ∀ y ∈ openSlab a b, ∀ a' b', reducedEinstein (z.g y) (z.gi y) (z.dg y) (z.ddg y) a' b' +
      SM.Λ * z.g y a' b' = SM.κ * Tf SM z y a' b' + SM.κ * ΔSf hC W z y a' b' := by
    intro y hy a' b'
    have := reduced_einstein_cpl h hy a' b'
    rw [stressDiff_eq hC h hy] at this
    linarith
  refine ⟨?_, fun e => ?_⟩
  · ext a' b'
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, jet3_resM, Matrix.of_apply]
    exact hRE x hx a' b'
  · ext a' b'
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    set G : ST 3 → ℝ := fun y => reducedEinstein (z.g y) (z.gi y) (z.dg y) (z.ddg y) a' b' +
      SM.Λ * z.g y a' b' with hG
    have hGs : ContDiff ℝ ∞ G := contDiff_reducedE a' b'
    have hline : HasDerivAt (fun s : ℝ => G (x + s • ev e))
        ((jet3 z x).dresM (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc e a' b' +
          SM.Λ * (jet3 z x).dg e a' b') 0 := by
      have h1 := (pathDeriv_jet3 z x e).resM a' b'
      simp only [jet3_line_zero] at h1
      have h2 := (z.line_g x e a' b').const_mul SM.Λ
      have hf : (fun s : ℝ => G (x + s • ev e)) = fun s =>
          (jet3 z (x + s • ev e)).resM (jet3 z (x + s • ev e)).gc (jet3 z (x + s • ev e)).dgc a' b' +
            SM.Λ * z.g (x + s • ev e) a' b' := funext fun s => by rw [hG, jet3_resM]
      rw [hf]
      exact h1.add h2
    have hpdG : pd G e x = (jet3 z x).dresM (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc e a' b' +
        SM.Λ * (jet3 z x).dg e a' b' :=
      pd_eq_of_line (hGs.differentiable (by simp) x) hline
    rw [← hpdG]
    have hΔ := contDiff_ΔSf (z := z) hC hW a' b'
    by_cases hκ : SM.κ = 0
    · rw [hκ, zero_mul, zero_mul, add_zero]
      have ev : G =ᶠ[𝓝 x] fun _ => 0 := Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => by
        have := hRE y hy a' b'
        rw [hκ, zero_mul, zero_mul, add_zero] at this
        exact this
      rw [pd_eq_of_eventuallyEq ev e]
      simp [SobolevOpen.pd]
    · have ev : (fun y => Tf SM z y a' b') =ᶠ[𝓝 x] fun y => SM.κ⁻¹ * G y - ΔSf hC W z y a' b' :=
        Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => by
          show Tf SM z y a' b' = SM.κ⁻¹ * (reducedEinstein (z.g y) (z.gi y) (z.dg y) (z.ddg y) a' b' +
            SM.Λ * z.g y a' b') - ΔSf hC W z y a' b'
          rw [hRE y hy a' b']
          field_simp
          ring
      rw [pd_eq_of_eventuallyEq ev e]
      have hd : pd (fun y => SM.κ⁻¹ * G y - ΔSf hC W z y a' b') e x =
          SM.κ⁻¹ * pd G e x - pd (fun y => ΔSf hC W z y a' b') e x := by
        refine pd_eq_of_line (((contDiff_const.mul hGs).sub hΔ).differentiable (by simp) x) ?_
        exact ((hasDerivAt_line0 (hGs.differentiable (by simp) x) e).const_mul _).sub
          (hasDerivAt_line0 (hΔ.differentiable (by simp) x) e)
      rw [hd]
      field_simp
      ring

/-- **The coupled subsidiary equation** (`eq:subsidiary`):
`□c_b + Ric^l{}_bc_l = -2κ(∇^μT_{μb}(z) + ∇^μΔS_{μb})`. -/
theorem coupled_subsidiary (hW : ContDiff ℝ ∞ W) (h : CplSol SM W z a b) {x : ST 3}
    (hx : x ∈ openSlab a b) (c : Fin 4) :
    (jet3 z x).boxC (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc c +
      (jet3 z x).ricC (jet3 z x).gc c =
      -2 * (SM.κ * divT SM z x c + SM.κ * divS (jet3 z x) (Matrix.of (ΔSf hC W z x))
        (fun e => Matrix.of fun a' b' => pd (fun y => ΔSf hC W z y a' b') e x) c) := by
  obtain ⟨heq, hdeq⟩ := coupled_reduced_jets hC hW h hx
  have hv := jet3_valid z x
  have hs := subsidiary_with_source hv (jet3 z x).gc (jet3 z x).dgc (jet3 z x).ddgc
    (fun e a' => Jet3.ddgc_swap hv e a') SM.Λ SM.κ (Matrix.of (Tf SM z x))
    (SM.κ • Matrix.of (ΔSf hC W z x))
    (fun e => Matrix.of fun a' b' => pd (fun y => Tf SM z y a' b') e x)
    (fun e => SM.κ • Matrix.of fun a' b' => pd (fun y => ΔSf hC W z y a' b') e x) heq hdeq c
  rw [hs, divS_eq_divT, divS_smul]

end RenewalGeometry.GenCplSub
