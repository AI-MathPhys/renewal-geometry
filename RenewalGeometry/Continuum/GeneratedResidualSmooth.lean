/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedResidualMaps

/-!
# Smoothness of the raw-jet residual maps on the Lorentzian chart

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`
(`eq:generated-bosonic`, `eq:generated-Dirac`): the raw residual maps of
`GeneratedResidualMaps.lean` are smooth (real-analytic in the metric part) on the open Lorentzian
chart `chartJ2 = {det g ≠ 0, g⁻¹ ∈ chart of frameOf}` of the head 2-jets, for theory data with
smooth sources (`SMSmooth`).

* `isOpen_chartJ2`;
* **`riemR_smooth`**, **`bosR_smooth`**, **`dirR_smooth`** — `ContDiffAt ℝ ∞` at every chart point.
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenResMaps

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

variable (m V S S') in
/-- **The Lorentzian chart of the head 2-jets.** -/
def chartJ2 : Set (HJ2 m V S S') :=
  {j | (Matrix.of j.1.1).det ≠ 0 ∧ IsLorChart (ginvOf j.1.1)}

theorem isOpen_chartJ2 : IsOpen (chartJ2 m V S S') := by
  have hdet : Continuous fun j : HJ2 m V S S' => (Matrix.of j.1.1).det :=
    Continuous.matrix_det (A := fun j : HJ2 m V S S' => Matrix.of j.1.1)
      (continuous_fst.comp continuous_fst)
  rw [isOpen_iff_mem_nhds]
  intro j hj
  have hc : ContinuousAt (fun y : HJ2 m V S S' => ginvOf y.1.1) j := by
    have : ContDiffAt ℝ ∞ (fun y : HJ2 m V S S' => ginvOf y.1.1) j :=
      ContDiffAt.ginvOf_fun (by fun_prop) hj.1
    exact this.continuousAt
  have h1 : ∀ᶠ y in 𝓝 j, (Matrix.of y.1.1).det ≠ 0 :=
    (isOpen_ne_fun hdet continuous_const).mem_nhds hj.1
  have h2 : ∀ᶠ y in 𝓝 j, IsLorChart (ginvOf y.1.1) := eventually_chart hc hj.2
  filter_upwards [h1, h2] with y hy1 hy2
  exact ⟨hy1, hy2⟩

/-- The adapted frame is smooth on the chart. -/
@[fun_prop]
theorem ContDiffAt.frU_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {gi : E → Fin 4 → Fin 4 → ℝ} {x : E} {n : WithTop ℕ∞} (hg : ContDiffAt ℝ n gi x)
    (h : IsLorChart (gi x)) (A μ : Fin 4) : ContDiffAt ℝ n (fun y => frU (gi y) A μ) x :=
  ((contDiffAt_frU h A μ).of_le le_top).comp x hg

variable {j₀ : HJ2 m V S S'}

theorem DH_eta (A : Fin 4 → MatLie m) (H : V) (dH : Fin 4 → V) :
    ActualJetGauge.DH A H dH = fun μ => dH μ + ⁅A μ, H⁆ := rfl

/-- **The Riemann tensor is a smooth function of the metric 2-jet** (`det g ≠ 0`). -/
theorem riemR_smooth (hj : j₀ ∈ chartJ2 m V S S') (c : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => riemR j c) j₀ := by
  have hx := hj
  simp only [riemR, rie, chr, dchr, dchr1, dchr2, dginv]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

set_option maxHeartbeats 8000000 in
/-- **The Einstein component of the raw bosonic residual is smooth on the chart.** -/
theorem bosR_smooth_E (SM : SMData (MatLie m) V S S') (hS : SMSmooth SM)
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

set_option maxHeartbeats 4000000 in
/-- **The Yang–Mills component of the raw bosonic residual is smooth on the chart.** -/
theorem bosR_smooth_A (SM : SMData (MatLie m) V S S') (hS : SMSmooth SM)
    (hj : j₀ ∈ chartJ2 m V S S') (ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => (bosR SM j).2.1 ν) j₀ := by
  have hx := hj
  simp (config := { maxSteps := 4000000 }) only [bosR, ymRes, ymDiv, dFm, Fm, fieldStrength, chr,
    DH_eta]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)

set_option maxHeartbeats 4000000 in
/-- **The Higgs component of the raw bosonic residual is smooth on the chart.** -/
theorem bosR_smooth_H (SM : SMData (MatLie m) V S S') (hS : SMSmooth SM)
    (hj : j₀ ∈ chartJ2 m V S S') :
    ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => (bosR SM j).2.2) j₀ := by
  have hx := hj
  simp (config := { maxSteps := 4000000 }) only [bosR, higgsRes, waveH, dDH, chr,
    ActualJetGauge.DH]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)

/-- **The raw bosonic residual map is smooth on the chart.** -/
theorem bosR_smooth (SM : SMData (MatLie m) V S S') (hS : SMSmooth SM)
    (hj : j₀ ∈ chartJ2 m V S S') : ContDiffAt ℝ ∞ (bosR SM) j₀ := by
  have h1 : ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => (bosR SM j).1) j₀ := by
    rw [contDiffAt_pi]; intro μ; rw [contDiffAt_pi]; intro ν
    exact bosR_smooth_E SM hS hj μ ν
  have h2 : ContDiffAt ℝ ∞ (fun j : HJ2 m V S S' => (bosR SM j).2.1) j₀ := by
    rw [contDiffAt_pi]; intro ν
    exact bosR_smooth_A SM hS hj ν
  exact h1.prodMk (h2.prodMk (bosR_smooth_H SM hS hj))

set_option maxHeartbeats 4000000 in
/-- **The raw Dirac residual map is smooth on the chart.** -/
theorem dirR_smooth (SM : SMData (MatLie m) V S S') (hj : j₀ ∈ chartJ2 m V S S') :
    ContDiffAt ℝ ∞ (dirR SM) j₀ := by
  have hx := hj
  refine ContDiffAt.prodMk ?_ ?_
  · simp (config := { maxSteps := 4000000 }) only [dirR, rDR, resD, dirac, omR, frR, deR, dψR, cov,
      omegaU, Gfun, spinPart, ipg, cv1, chr, dginv, mass, Module.End.smul_def,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      Module.End.mul_apply]
    fun_prop (disch := first | exact hx.1 | exact hx.2)
  · simp (config := { maxSteps := 4000000 }) only [dirR, rDR, resD, dirac, omR, frR, deR, dψR, cov,
      omegaU, Gfun, spinPart, ipg, cv1, chr, dginv, mass, Module.End.smul_def,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      Module.End.mul_apply]
    fun_prop (disch := first | exact hx.1 | exact hx.2)

end RenewalGeometry.GenResMaps
