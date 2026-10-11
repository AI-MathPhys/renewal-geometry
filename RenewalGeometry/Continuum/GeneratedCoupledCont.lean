/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledDivS
import RenewalGeometry.Continuum.GeneratedCoupledUniquenessE

/-!
# Continuity of the coefficients of the coupled subsidiary system

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors: the zero-order coefficients of the coupled constraint system (the twisted spin
connection `ω`, the one-form connection `ω'`, its frame derivative and the curvature `R'`) are
pointwise-continuous families of linear maps along a smooth tuple, hence uniformly bounded on
every compact period cell (`GenCplE.endBdd_cube`).

* `PC` — pointwise continuity of a family of linear maps, with its closure lemmas;
* `contDiff_dGc` — smoothness of the frame-derivative jets of the connection coefficients;
* `pc_ωF`, `pc_omegaP`, `pc_dωP`, **`pc_curv`**.
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplCont

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov GenCplN

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Pointwise continuous families of linear maps -/

section PC

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A pointwise continuous family of linear maps**: `y ↦ T(y)v` is continuous for every `v`. -/
def PC (T : ST 3 → E →ₗ[ℝ] F) : Prop := ∀ v, Continuous fun y => T y v

theorem PC.apply {T : ST 3 → E →ₗ[ℝ] F} (hT : PC T) {f : ST 3 → E} (hf : Continuous f) :
    Continuous fun y => T y (f y) := by
  set L : ST 3 → E →L[ℝ] F := fun y => LinearMap.toContinuousLinearMap (T y)
  have hL : Continuous L := continuous_clm_apply.2 hT
  exact hL.clm_apply hf

theorem PC.const (T : E →ₗ[ℝ] F) : PC fun _ => T := fun _ => continuous_const

theorem PC.add {T T' : ST 3 → E →ₗ[ℝ] F} (h : PC T) (h' : PC T') : PC fun y => T y + T' y :=
  fun v => (h v).add (h' v)

theorem PC.sub {T T' : ST 3 → E →ₗ[ℝ] F} (h : PC T) (h' : PC T') : PC fun y => T y - T' y :=
  fun v => (h v).sub (h' v)

theorem PC.smul {c : ST 3 → ℝ} (hc : Continuous c) {T : ST 3 → E →ₗ[ℝ] F} (h : PC T) :
    PC fun y => c y • T y := fun v => hc.smul (h v)

theorem PC.sum {ι : Type*} (t : Finset ι) {T : ι → ST 3 → E →ₗ[ℝ] F} (h : ∀ i ∈ t, PC (T i)) :
    PC fun y => ∑ i ∈ t, T i y := by
  intro v
  simp only [LinearMap.sum_apply]
  exact continuous_finsetSum _ fun i hi => h i hi v

theorem PC.mul {T T' : ST 3 → Module.End ℝ E} (h : PC T) (h' : PC T') :
    PC fun y => T y * T' y := fun v => by
  simp only [Module.End.mul_apply]
  exact h.apply (h' v)

end PC

section Lifts

variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

theorem pc_liftE {T : ST 3 → Module.End ℝ S₀} (h : PC T) : PC fun y => liftE (T y) := fun Y =>
  continuous_pi fun i => by simpa only [liftE_apply] using h (Y i)

theorem pc_formΓ {Γ : ST 3 → Fin 4 → Fin 4 → ℝ} (h : ∀ A C, Continuous fun y => Γ y A C) :
    PC fun y => formΓ (S := S₀) (Γ y) := fun Y =>
  continuous_pi fun A => by
    show Continuous fun y => ∑ C, Γ y A C • Y C
    exact continuous_finsetSum _ fun C _ => (h A C).smul continuous_const

theorem pc_spinPart (Fr : CliffordFrame (Fin 4) (Module.End ℝ S₀)) {W : ST 3 → Fin 4 → Fin 4 → ℝ}
    (h : ∀ c d, Continuous fun y => W y c d) : PC fun y => spinPart Fr (W y) := by
  unfold spinPart
  refine PC.smul continuous_const (PC.sum _ fun c _ => PC.sum _ fun d _ => ?_)
  exact PC.smul (continuous_const.mul (h c d)) (PC.const _)

end Lifts


/-! ### The connection coefficients along a smooth tuple -/

section Tuple

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

variable (z : Tuple m V S S') (D : DiracData (MatLie m) V S₀)

theorem contDiff_dGc (δ A B C : Fin 4) : ContDiff ℝ ∞ (fun y => (z.FJ y).dGc δ A B C) := by
  have h1 := z.contDiff_gc
  have h2 := z.contDiff_dg
  have h3 := z.contDiff_ddg
  have h4 := z.contDiff_gi
  have h5 := z.contDiff_e
  have h6 := z.contDiff_de
  have h7 := z.contDiff_dde
  show ContDiff ℝ ∞ (fun y => ∑ γ, (z.de y δ A γ * ipg (z.g y)
      (fun μ => cv1 (chr (z.gi y) (z.dg y)) (z.e y B) (fun γ μ => z.de y γ B μ) γ μ) (z.e y C) +
    z.e y A γ * dipg (z.g y) (z.dg y)
      (fun μ => cv1 (chr (z.gi y) (z.dg y)) (z.e y B) (fun γ μ => z.de y γ B μ) γ μ)
      (fun δ μ => dcv1 (chr (z.gi y) (z.dg y)) (dchr (z.gi y) (z.dg y) (z.ddg y)) (z.e y B)
        (fun γ μ => z.de y γ B μ) (fun δ γ μ => z.dde y δ γ B μ) δ γ μ)
      (z.e y C) (fun δ μ => z.de y δ C μ) δ))
  unfold ipg dipg cv1 dcv1 chr dchr dchr1 dchr2 dginv
  beta_reduce
  fun_prop

theorem continuous_ρ (μ : Fin 4) {f : ST 3 → MatLie m} (hf : Continuous f) (v : S₀) :
    Continuous fun y => D.ρ (f y) v := by
  have hL : Continuous (D.ρ.flip v) := LinearMap.continuous_of_finiteDimensional _
  exact hL.comp hf

theorem ωF_apply (y : ST 3) (B : Fin 4) (v : S₀) :
    ωF z D y B v = spinPart D.Fr ((z.FJ y).G B) v + ∑ μ, z.e y B μ • D.ρ (z.A y μ) v := by
  rw [ωF_eq]
  show (spinPart D.Fr ((z.FJ y).G B) + ∑ μ, z.e y B μ • D.ρ (z.A y μ)) v = _
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply]

theorem pc_ωF (B : Fin 4) : PC fun y => ωF z D y B := by
  intro v
  simp only [ωF_apply]
  have hA : Continuous z.A := z.A_smooth.continuous
  refine Continuous.add ?_ (continuous_finsetSum _ fun μ _ =>
    (z.contDiff_e B μ).continuous.smul (continuous_ρ D μ (continuous_apply μ |>.comp hA) v))
  exact pc_spinPart D.Fr (fun c d => (z.contDiff_G B c d).continuous) v

theorem pc_omegaP (B : Fin 4) : PC fun y => omegaP (ωF z D y) (ΓF z y) B :=
  (pc_liftE (pc_ωF z D B)).sub (pc_formΓ fun A C => (contDiff_ΓF z B A C).continuous)

theorem dωP_apply (y : ST 3) (a b : Fin 4) :
    dωP z D y a b = liftE (spinPart D.Fr (fun c d => ∑ δ, z.e y a δ * (z.FJ y).dGc δ b c d) +
      ∑ δ, z.e y a δ • ∑ μ, (z.de y δ b μ • D.ρ (z.A y μ) + z.e y b μ • D.ρ (pd z.A δ y μ))) -
      formΓ (lcΓ D.Fr.ε (fun c d e => ∑ δ, z.e y a δ * (z.FJ y).dGc δ c d e) b) := rfl

theorem pc_dωP (a b : Fin 4) : PC fun y => dωP z D y a b := by
  have hA : Continuous z.A := z.A_smooth.continuous
  have hdA : ∀ δ, Continuous (pd z.A δ) := fun δ => (contDiff_pd z.A_smooth δ).continuous
  have he := fun A μ => (z.contDiff_e A μ).continuous
  have hde := fun γ A μ => (z.contDiff_de γ A μ).continuous
  have hdG := fun δ A B C => (contDiff_dGc z δ A B C).continuous
  simp only [dωP_apply]
  refine PC.sub (pc_liftE (PC.add ?_ ?_)) (pc_formΓ fun A C => ?_)
  · exact pc_spinPart D.Fr fun c d => continuous_finsetSum _ fun δ _ => (he a δ).mul (hdG δ b c d)
  · refine PC.sum _ fun δ _ => PC.smul (he a δ) (PC.sum _ fun μ _ => PC.add ?_ ?_)
    · refine PC.smul (hde δ b μ) fun v => continuous_ρ D μ ((continuous_apply μ).comp hA) v
    · refine PC.smul (he b μ) fun v => continuous_ρ D μ ((continuous_apply μ).comp (hdA δ)) v
  · unfold lcΓ
    exact continuous_const.mul (continuous_finsetSum _ fun δ _ => (he a δ).mul (hdG δ b A C))

theorem continuous_GJ (A B C : Fin 4) : Continuous fun y => (Jx z D y).G A B C :=
  (z.contDiff_G A B C).continuous

/-- **The curvature `R'` of the one-form connection is a pointwise continuous family.** -/
theorem pc_curv (a b : Fin 4) : PC fun y => curv (lcΛ D.Fr.ε (Jx z D y).G)
    (omegaP (ωF z D y) (ΓF z y)) (dωP z D y) a b := by
  unfold curv
  refine PC.sub (PC.add (PC.sub (pc_dωP z D a b) (pc_dωP z D b a))
    (PC.sub (PC.mul (pc_omegaP z D a) (pc_omegaP z D b))
      (PC.mul (pc_omegaP z D b) (pc_omegaP z D a)))) (PC.sum _ fun c _ => ?_)
  refine PC.smul ?_ (pc_omegaP z D c)
  unfold lcΛ lcΓ
  exact (continuous_const.mul (continuous_GJ z D a b c)).sub
    (continuous_const.mul (continuous_GJ z D b a c))

end Tuple

end RenewalGeometry.GenCplCont
