/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.GeneratedDiracStress

/-!
# Gauge-charged Dirac sources are not globally smooth

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
`thm:generated-dynamics` (back-reacting spinors).

The coupled theorems (`GenCplIdF.generated_physical_identification_coupledDirac`,
`GenCplDyn.generated_dynamics_ext_cpl`, `GenCplDynS.generated_dynamics_cpl_stat`) assume
`SMSmooth SM`: the sources `J_ν(g, g⁻¹, H, DH, Ψ, Ψ̄)`, `S_H` are smooth on **all** of
`Met × Met × ⋯`, the inverse-metric slot included.  For variational Dirac data the Dirac current
`J^D_ν = -g_{νμ} Σ_A ε_A e_A{}^μ μ_S(Ψ̄, c_AΨ)` contains the adapted frame `e = frU(g⁻¹)`, which is
smooth only on Lorentzian charts.

* **`not_smSmooth_of_charged`** — if some gauge generator acts on spinors nontrivially through the
  pairing (`⟨φ, ρ(X)x⟩ ≠ 0` for some `X, φ, x`, i.e. the spinors are gauge-charged and source the
  gauge field), then `SMSmooth SM` fails: along `g⁻¹(t) = diag(t, 1, 1, 1)` the time component
  of the Dirac current is `√(-t) μ_S(Ψ̄, c_0Ψ)` (`frU(g⁻¹)_0{}^0 = √(-g^{00})`, `frU_a{}^0 = 0`),
  not differentiable at `t = 0`.

Hence the coupled theorems apply to back-reacting data only when the spinors are gauge-neutral
through the pairing; a charged instance requires replacing `SMSmooth` by smoothness on the
Lorentzian chart throughout the chain (not done).
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace MathPhys.GenChNoGo

open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState JetCurve GenNoether
  GenDiracCur

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-- **`t ↦ √(-t)` is not differentiable at `0`.** -/
theorem not_differentiableAt_sqrt_neg : ¬ DifferentiableAt ℝ (fun t : ℝ => Real.sqrt (-t)) 0 := by
  intro hd
  have h2' : HasDerivWithinAt (fun t : ℝ => Real.sqrt (-t) ^ 2) 0 (Iic 0) 0 := by
    have := (hd.hasDerivAt.fun_pow 2).hasDerivWithinAt (s := Iic 0)
    simpa using this
  have h3 : HasDerivWithinAt (fun t : ℝ => Real.sqrt (-t) ^ 2) (-1) (Iic 0) 0 := by
    have hl : HasDerivWithinAt (fun t : ℝ => -t) (-1) (Iic 0) 0 :=
      (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
    refine hl.congr (fun t ht => ?_) (by simp)
    exact Real.sq_sqrt (by simpa using ht)
  have := (uniqueDiffWithinAt_Iic (0 : ℝ)).eq_deriv _ h2' h3
  norm_num at this

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}

/-- The line of inverse metrics `diag(t, 1, 1, 1)`. -/
def giLine (t : ℝ) : Met := fun i j => if i = j then (if i = 0 then t else 1) else 0

/-- The unit metric `δ`. -/
def gOne : Met := fun i j => if i = j then 1 else 0

theorem frU_giLine_zero (t : ℝ) : frU (giLine t) 0 0 = Real.sqrt (-t) := by
  simp [frU, lapse, giLine]

theorem frU_succ_zero (gi : Met) (a : Fin 3) : frU gi a.succ 0 = 0 := by
  simp [frU]

/-- The time component of the Dirac current along the line `diag(t, 1, 1, 1)`. -/
theorem diracCur_giLine (μS : S' →ₗ[ℝ] S →ₗ[ℝ] MatLie m)
    (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) (t : ℝ) (ψ : S) (ψb : S') :
    diracCur μS Fr gOne (giLine t) ψ ψb 0 = Real.sqrt (-t) • μS ψb (Fr.c 0 ψ) := by
  unfold diracCur
  rw [Fin.sum_univ_succ]
  simp only [gOne, if_true, one_smul]
  have h0 : ∀ i : Fin 3, (if (0 : Fin 4) = i.succ then (1 : ℝ) else 0) = 0 := fun i => by
    simp [(Fin.succ_ne_zero i).symm]
  simp only [h0, zero_smul, Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_succ]
  simp only [frU_succ_zero, mul_zero, zero_smul, Finset.sum_const_zero, add_zero,
    frU_giLine_zero, lorentzSign]
  simp

/-- **No-go: gauge-charged back-reacting Dirac data do not have globally smooth sources.**  For
variational Dirac data in which some gauge generator acts on the spinors nontrivially through the
pairing, `SMSmooth SM` fails. -/
theorem not_smSmooth_of_charged (hV : VariationalDirac SM)
    (hch : ∃ (X : MatLie m) (φ : S') (x : S), hV.P φ (SM.D.ρ X x) ≠ 0) : ¬ SMSmooth SM := by
  intro hS
  obtain ⟨X, φ, x, hne⟩ := hch
  -- the spinor `Ψ = c_0 x`, so that `c_0Ψ = x`
  have hc0 : SM.D.Fr.c 0 * SM.D.Fr.c 0 = 1 := by
    have h := SM.D.Fr.anticomm 0 0
    rw [if_pos rfl, SM.D.lorentz.1] at h
    have h2 : (2 : ℝ) • (SM.D.Fr.c 0 * SM.D.Fr.c 0) = (2 : ℝ) • (1 : Module.End ℝ S) := by
      rw [two_smul, h]; norm_num
    exact smul_right_injective (Module.End ℝ S) (two_ne_zero) h2
  set ψ : S := SM.D.Fr.c 0 x with hψ
  have hcψ : SM.D.Fr.c 0 ψ = x := by
    rw [hψ, ← Module.End.mul_apply, hc0, Module.End.one_apply]
  -- the value `ipG X (μ_S(φ, x)) ≠ 0`
  have hw : SM.ipG X (hV.μS φ x) ≠ 0 := by rw [hV.μS_dual]; exact hne
  -- smoothness along the line
  have hline : ContDiff ℝ ∞ (fun t : ℝ => SM.Jcur gOne (giLine t) 0 (fun _ => 0) ψ φ 0) := by
    have hp : ContDiff ℝ ∞ (fun t : ℝ => ((gOne, giLine t, (0 : V), (fun _ => (0 : V)), ψ, φ) :
        Met × Met × V × (Fin 4 → V) × S × S')) := by
      refine contDiff_const.prodMk (ContDiff.prodMk ?_ contDiff_const)
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
      simp only [giLine]
      split_ifs
      · exact contDiff_id
      · exact contDiff_const
      · exact contDiff_const
    exact (hS.J 0).comp hp
  have hval : ∀ t : ℝ, SM.Jcur gOne (giLine t) 0 (fun _ => 0) ψ φ 0 =
      Real.sqrt (-t) • hV.μS φ x := fun t => by
    rw [hV.J_eq, diracCur_giLine, hcψ]
    simp
  set c : ℝ := SM.ipG X (hV.μS φ x) with hcdef
  have hf : DifferentiableAt ℝ (fun t : ℝ => SM.ipG X (SM.Jcur gOne (giLine t) 0 (fun _ => 0) ψ φ 0))
      0 := by
    have h1 : DifferentiableAt ℝ (fun t : ℝ => SM.Jcur gOne (giLine t) 0 (fun _ => 0) ψ φ 0) 0 :=
      (hline.differentiable (by simp)) 0
    exact (LinearMap.toContinuousLinearMap (SM.ipG X)).differentiableAt.comp 0 h1
  have heq : (fun t : ℝ => SM.ipG X (SM.Jcur gOne (giLine t) 0 (fun _ => 0) ψ φ 0)) =
      fun t => c * Real.sqrt (-t) := by
    funext t
    rw [hval, map_smul, smul_eq_mul, mul_comm]
  rw [heq] at hf
  have hg : DifferentiableAt ℝ (fun t : ℝ => c⁻¹ * (c * Real.sqrt (-t))) 0 :=
    hf.const_mul c⁻¹
  have e : (fun t : ℝ => c⁻¹ * (c * Real.sqrt (-t))) = fun t => Real.sqrt (-t) := by
    funext t; field_simp
  rw [e] at hg
  exact not_differentiableAt_sqrt_neg hg

/-- The no-go with the charge expressed through the spinor moment map: `μ_S ≠ 0`. -/
theorem not_smSmooth_of_muS (hV : VariationalDirac SM) (hμ : ∃ (φ : S') (x : S), hV.μS φ x ≠ 0) :
    ¬ SMSmooth SM := by
  obtain ⟨φ, x, hne⟩ := hμ
  refine not_smSmooth_of_charged hV ?_
  by_contra hall
  push_neg at hall
  exact hne (hV.ipG_nondeg _ fun X => by rw [hV.μS_dual]; exact hall X φ x)

/-- **The charged back-reacting quaternionic data `GenDStress.quatSMT` (a `CoupledDirac` instance
with nonzero Dirac stress, `GenDStress.quatSMT_stress_ne`) do not satisfy `SMSmooth`**, so the
coupled theorems do not apply to them. -/
theorem not_smSmooth_quatSMT : ¬ SMSmooth GenDStress.quatSMT := by
  refine not_smSmooth_of_muS GenDStress.quatVarT ⟨((0 : Quaternion ℝ), qU 0),
    (GenDiracCur.quatSM.D.Fr.c 0 ((1 : Quaternion ℝ), 0)), ?_⟩
  intro h
  have h1 := congrFun (congrFun h 0) 0
  change PQ ((0 : Quaternion ℝ), qU 0) (rightI (swapQ ((1 : Quaternion ℝ), 0))) = 0 at h1
  simp [PQ_apply, dotQ] at h1
  change (0 : ℝ) * 0 + 0 * 0 + 0 * 0 + 0 * 0 + 1 = 0 at h1
  norm_num at h1

end MathPhys.GenChNoGo
