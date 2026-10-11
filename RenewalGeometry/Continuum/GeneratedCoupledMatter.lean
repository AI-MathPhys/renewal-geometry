/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledConstraints

/-!
# The matter equations and the Gauss constraint along a coupled solution

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.  Let `W` solve the shift-transported system with the bosonic blocks and head
spinors of `z` (`GenCplRows.CplSol`).  The electric, Higgs and Dirac rows of `W` do not involve
the auxiliary spinor jets, so:

* **`matterAt_cpl`** — the Dirac equations, the Higgs equation and the spatial frame components
  of the Yang–Mills equation hold for `z` (`MatterAt`);
* **`gauss_propagation_m`** — the Gauss constraint propagates wherever these matter equations
  hold (the proof of `GenGauss.gauss_propagation` uses the symmetric system only through them);
* `StressConservation` — on-shell conservation of the complete stress (property of the theory
  data); `stressConservation_of_noether`;
* **`divT_zero_cpl`** — hence, for theory data with the current Noether identity and on-shell
  stress conservation,
  the complete stress of `z` is conserved.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.GenCplMat

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

/-- **The matter equations at a point**: Dirac and dual Dirac equations, Higgs equation and the
spatial frame components of the Yang–Mills equation. -/
def MatterAt (y : ST 3) : Prop :=
  dirF SM z y = 0 ∧ (bosF SM z y).2.2 = 0 ∧
    ∀ a : Fin 3, ∑ ν, (frameU (z.gi y)).fr a.succ ν • (bosF SM z y).2.1 ν = 0

section Gauss

/-- **Along a solution of the symmetric system the Yang–Mills residual density is normal**:
`ϱ g^{νβ}r^A_β = -ϱ e_0{}^ν G` (the spatial frame components of `r^A` vanish by residual slaving,
and `g^{νβ} = -e_0^νe_0^β + Σ_a e_a^νe_a^β`). -/
theorem densR_eq_gauss_m {y : ST 3} (hmat : MatterAt SM z y) (ν : Fin 4) :
    densR SM z y ν = -(w0 z ν y • gaussF SM z y) := by
  obtain ⟨-, -, hE⟩ := hmat
  have had := adapted z y
  unfold densR w0
  set F := frameU (z.gi y)
  have hsum : ∑ β, z.gi y ν β • (bosF SM z y).2.1 β =
      -(F.fr 0 ν • ∑ β, F.fr 0 β • (bosF SM z y).2.1 β) +
        ∑ a : Fin 3, F.fr a.succ ν • ∑ β, F.fr a.succ β • (bosF SM z y).2.1 β := by
    simp only [had ν, add_smul, neg_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.smul_sum, smul_smul, Finset.sum_smul]
    congr 1
    rw [Finset.sum_comm]
  have hz : ∑ a : Fin 3, F.fr a.succ ν • ∑ β, F.fr a.succ β • (bosF SM z y).2.1 β = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hE a, smul_zero]
  rw [hsum, hz, add_zero, e_eq_frameU]
  unfold gaussF
  rw [smul_neg, mul_smul]

theorem pd_neg'_m {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ST 3 → E) (i : Fin 4)
    (x : ST 3) : pd (fun y => -f y) i x = -pd f i x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_neg]
  rfl

/-- **The Gauss transport equation**: on an open set where the actual-jet state solves the symmetric
system, `∂_ν(ϱe_0{}^νG) + [A_ν, ϱe_0{}^νG] = 0` (Yang–Mills Bianchi identity + current Noether
identity + residual slaving of the Higgs and Dirac equations). -/
theorem gauss_transport_m (hN : CurrentNoether SM) (hS : SMSmooth SM) {O : Set (ST 3)}
    (hO : IsOpen O) (hmat : ∀ y ∈ O, MatterAt SM z y) {x : ST 3} (hx : x ∈ O) :
    ∑ ν, (pd (fun y => w0 z ν y • gaussF SM z y) ν x + ⁅z.A x ν, w0 z ν x • gaussF SM z x⁆) =
      0 := by
  obtain ⟨hD, hH, -⟩ := hmat x hx
  have h0 := div_rA_eq_zero z hN hS hH hD
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

/-- The transport equation solved for the normal derivative:
`Σ_ν ϱe_0^ν∂_νG = -(Σ_ν∂_ν(ϱe_0^ν))G - Σ_ν ϱe_0^ν[A_ν, G]`. -/
theorem gauss_transport'_m (hN : CurrentNoether SM) (hS : SMSmooth SM) {O : Set (ST 3)}
    (hO : IsOpen O) (hmat : ∀ y ∈ O, MatterAt SM z y) {x : ST 3} (hx : x ∈ O) :
    ∑ ν, w0 z ν x • pd (gaussF SM z) ν x =
      -((∑ ν, pd (w0 z ν) ν x) • gaussF SM z x) -
        ∑ ν, w0 z ν x • ⁅z.A x ν, gaussF SM z x⁆ := by
  have h := gauss_transport_m SM z hN hS hO hmat hx
  have hprod : ∀ ν, pd (fun y => w0 z ν y • gaussF SM z y) ν x =
      pd (w0 z ν) ν x • gaussF SM z x + w0 z ν x • pd (gaussF SM z) ν x := by
    intro ν
    unfold SobolevOpen.pd
    rw [fderiv_fun_smul (((contDiff_w0 z ν).differentiable (by simp)) x)
      (((contDiff_gaussF SM z hS).differentiable (by simp)) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [add_comm]
  simp only [hprod, lie_smul] at h
  rw [Finset.sum_smul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]
  refine Finset.sum_congr rfl fun ν _ => ?_
  abel

theorem isSPeriodic_pd_m {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    (hf : IsSPeriodic f) (i : Fin 4) : IsSPeriodic (pd f i) := fun k x => by
  unfold SobolevOpen.pd
  rw [KatoGalerkin.isSPeriodic_fderiv hf k x]

theorem pd_cplxL_m {G : ST 3 → MatLie m} {x : ST 3} (hG : DifferentiableAt ℝ G x) (i : Fin 4) :
    pd (fun y => cplxL m (G y)) i x = cplxL m (pd G i x) := by
  unfold SobolevOpen.pd
  have h : HasFDerivAt (fun y => cplxL m (G y)) ((cplxL m).comp (fderiv ℝ G x)) x :=
    (cplxL m).hasFDerivAt.comp x hG.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- **Propagation of the Gauss constraint** (`lem:generated-physical-identification`, the Gauss
part of constraint propagation): for theory data with smooth sources satisfying the current
Noether identity, if the actual-jet state field of a smooth tuple solves the independent symmetric
system `eq:generated-extension` on the open slab `(a, b) × 𝕋³` and the Gauss constraint
`e_0{}^νr^A_ν` vanishes at `t₀ ∈ (a, b)`, then it vanishes on `[t₀, t₁] × 𝕋³` for every
`t₁ ∈ (t₀, b)`. -/
theorem gauss_propagation_m (hN : CurrentNoether SM) (hS : SMSmooth SM) {a t₀ t₁ b : ℝ}
    (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b) (hmat : ∀ x ∈ openSlab a b, MatterAt SM z x)
    (h0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, gaussF SM z x = 0 := by
  have hGs := contDiff_gaussF SM z hS
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
    rw [e1, norm_cplxL, gauss_transport'_m SM z hN hS (isOpen_openSlab a b) hmat hxo]
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

end Gauss

/-! ### The matter equations along a coupled solution -/

section Coupled

variable {SM z} {W : ST 3 → StateP m V S S'} {a b : ℝ}

theorem princL_E_zero (v : StateP m V S S') (j : Fin 3) {u : StateP m V S S'}
    (hE : u.2.2.1 = 0) (hB : u.2.2.2.1 = 0) : (princL SM v j u).2.2.1 = 0 := by
  obtain ⟨u1, uA, uE, uB, ur⟩ := u
  simp only at hE hB
  subst hE hB
  funext c
  simp [princL, ActualJetSystem.princ, toP, ofP]

theorem princL_Pm_zero (v : StateP m V S S') (j : Fin 3) {u : StateP m V S S'}
    (hP : u.2.2.2.2.2.1 = 0) (hQ : u.2.2.2.2.2.2.1 = 0) : (princL SM v j u).2.2.2.2.2.1 = 0 := by
  obtain ⟨u1, uA, uE, uB, uH, uP, uQ, ur⟩ := u
  simp only at hP hQ
  subst hP hQ
  simp [princL, ActualJetSystem.princ, toP, ofP]

/-- **The matter equations hold along a coupled solution.** -/
theorem matterAt_cpl (h : GenCplRows.CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) :
    MatterAt SM z x := by
  have hO := isOpen_openSlab (d := 3) a b
  have hrow := GenCplRows.diff_row h hx
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := h.ms.smooth.of_le (by norm_cast)
  have hUd : DifferentiableOn ℝ (stateF SM z) (openSlab a b) :=
    ((contDiff_stateF SM z).differentiable (by simp)).differentiableOn
  have hpdB := GenHiggsDefect.pd_block_eq' hO hW1 hUd (GenSpinorDefect.prB m V S S') h.bos
  have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW1 one_ne_zero hx
  have hdU : DifferentiableAt ℝ (stateF SM z) x := (contDiff_stateF SM z).differentiable (by simp) x
  have hB : ∀ γ, GenSpinorDefect.prB m V S S' (pd (fun y => W y - stateF SM z y) γ x) = 0 := by
    intro γ
    rw [GenDefJet.pd_sub_eq hdW hdU, map_sub, hpdB x hx γ, sub_self]
  have hBc : ∀ γ, (pd (fun y => W y - stateF SM z y) γ x).1 = 0 ∧
      (pd (fun y => W y - stateF SM z y) γ x).2.1 = 0 ∧
      (pd (fun y => W y - stateF SM z y) γ x).2.2.1 = 0 ∧
      (pd (fun y => W y - stateF SM z y) γ x).2.2.2.1 = 0 ∧
      (pd (fun y => W y - stateF SM z y) γ x).2.2.2.2.1 = 0 ∧
      (pd (fun y => W y - stateF SM z y) γ x).2.2.2.2.2.1 = 0 ∧
      (pd (fun y => W y - stateF SM z y) γ x).2.2.2.2.2.2.1 = 0 := fun γ =>
    GenSpinorDefect.prB_eq_iff.1 ((hB γ).trans (map_zero _).symm)
  have hrec := GenCplRows.recon_withX (SM := SM) (h.bos x hx) (h.ψ_eq hx) (h.ψb_eq hx)
  have hFE : (toP (Fsys SM (ofP (W x)))).2.2.1 = (toP (Fsys SM (ofP (stateF SM z x)))).2.2.1 := by
    show (Fsys SM (ofP (W x))).E = (Fsys SM (ofP (stateF SM z x))).E
    unfold Fsys
    rw [hrec]
    rfl
  have hFP : (toP (Fsys SM (ofP (W x)))).2.2.2.2.2.1 =
      (toP (Fsys SM (ofP (stateF SM z x)))).2.2.2.2.2.1 := by
    show (Fsys SM (ofP (W x))).Pm = (Fsys SM (ofP (stateF SM z x))).Pm
    unfold Fsys
    rw [hrec]
    rfl
  have hE := congrArg (fun v : StateP m V S S' => v.2.2.1) hrow
  have hP := congrArg (fun v : StateP m V S S' => v.2.2.2.2.2.1) hrow
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum, Prod.fst_sub,
    Prod.snd_sub] at hE hP
  rw [(hBc 0).2.2.1, Finset.sum_eq_zero fun j _ => princL_E_zero _ j (hBc _).2.2.1
    (hBc _).2.2.2.1, hFE, add_zero, sub_self, zero_sub] at hE
  rw [(hBc 0).2.2.2.2.2.1, Finset.sum_eq_zero fun j _ => princL_Pm_zero _ j (hBc _).2.2.2.2.2.1
    (hBc _).2.2.2.2.2.2, hFP, add_zero, sub_self, zero_sub] at hP
  have hN := (frameU (ginvOf (ofP (stateF SM z x)).g)).N_pos
  have hE0 : (errF SM z x).2.2.1 = 0 := neg_eq_zero.1 hE.symm
  have hP0 : (errF SM z x).2.2.2.2.2.1 = 0 := neg_eq_zero.1 hP.symm
  refine ⟨h.dir x hx, ?_, fun a' => ?_⟩
  · have h2 := errF_Pm SM z x
    rw [hP0] at h2
    have h3 := h2.symm
    rw [neg_eq_zero] at h3
    exact (smul_eq_zero.mp h3).resolve_left hN.ne'
  · have h2 := errF_E SM z x a'
    have h4 : (errF SM z x).2.2.1 a' = 0 := by rw [hE0]; rfl
    rw [h4] at h2
    have h3 := h2.symm
    rw [neg_eq_zero] at h3
    exact (smul_eq_zero.mp h3).resolve_left hN.ne'

variable (SM) in
/-- **On-shell stress conservation** (the stress Noether identity on solutions of the matter
equations, a property of the theory data): wherever the Dirac equations hold on a neighbourhood
and the Yang–Mills and Higgs equations hold at the point, the complete stress (with the Dirac
stress) is covariantly conserved.  For back-reacting spinors the off-shell identity involves the
first derivatives of the Dirac residuals, so `GenStress.StressNoether` (residual values only) is
not the right form; it implies this one (`stressConservation_of_noether`). -/
def StressConservation : Prop :=
  ∀ (z : Tuple m V S S') (x : ST 3), (∀ᶠ y in 𝓝 x, dirF SM z y = 0) →
    (bosF SM z x).2.1 = 0 → (bosF SM z x).2.2 = 0 → ∀ ν, GenStress.divT SM z x ν = 0

theorem stressConservation_of_noether (hT : GenStress.StressNoether SM) :
    StressConservation SM := fun z _ hD hA hH ν =>
  GenStress.divT_eq_zero z hT hA hH hD.self_of_nhds ν


/-- **The complete stress is conserved along a coupled solution** (Gauss law propagated from the
initial slice; current and stress Noether identities of the theory data). -/
theorem divT_zero_cpl (hN : CurrentNoether SM) (hT : StressConservation SM)
    (hS : SMSmooth SM) (h : GenCplRows.CplSol SM W z a b) {t₀ t₁ : ℝ} (ha : a < t₀)
    (h01 : t₀ < t₁) (hb : t₁ < b) (hG0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, (∀ ν, GenStress.divT SM z x ν = 0) ∧ (bosF SM z x).2.1 = 0 := by
  have hmat : ∀ x ∈ openSlab a b, MatterAt SM z x := fun x hx => matterAt_cpl h hx
  have hG := gauss_propagation_m SM z hN hS ha h01 hb hmat hG0
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

end Coupled

end RenewalGeometry.GenCplMat
