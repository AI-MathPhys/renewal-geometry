/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledBounds2

/-!
# The coupled constraint system is symmetric hyperbolic: vanishing of the coupled defects

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors (Dirac back-reaction).  Let `W` solve the shift-transported system on a slab with
the bosonic blocks and head spinors of a smooth tuple `z`, and suppose the complete stress of `z`
(with the symmetric Dirac stress) is conserved.  The unknown
`𝒰 = (c; Y, P, Ȳ, P̄)` — lowered harmonic defect, tangential spinor defects and **normal
prolongation defects** — solves a system consisting of a wave block for `c` and a first-order block
`∂_tw + Σ_j𝒜^j∂_jw` for `w = (Y, P, Ȳ, P̄)`, coupled at order zero:

* `bW` — **the symmetriser**: the block form `Σ_abS(Y_a, Y'_a) + bS(P, P') + (dual)`; the
  principal operators `Aop j = diag(𝒜^j_Dirac)` are `bW`-symmetric (Clifford unitarity);
* **`coupled_constraints_vanish`** — zero Cauchy data of `(c, ∂_tc, w)` on `t = t₀` force
  `c = 0` and `w = 0` on `[t₀, t₁] × 𝕋³`.
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplCon

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov GenCplN GenCplRows GenCplX GenCplP GenCplCont GenCtrl GenCplE GenCplBd

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

/-! ### The symmetriser and the principal operators -/

section Symmetriser

variable (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)

/-- **The symmetriser** of the first-order block `(Y, P, Ȳ, P̄)`. -/
def bW : ((Fin 3 → S) × S × (Fin 3 → S') × S') →ₗ[ℝ]
    ((Fin 3 → S) × S × (Fin 3 → S') × S') →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => ∑ a, bS (v.1 a) (w.1 a) + bS v.2.1 w.2.1 +
      ∑ a, bS' (v.2.2.1 a) (w.2.2.1 a) + bS' v.2.2.2 w.2.2.2)
    (fun v v' w => by simp [Finset.sum_add_distrib]; ring)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, mul_add, Finset.mul_sum])
    (fun v w w' => by simp [Finset.sum_add_distrib]; ring)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, smul_eq_mul,
        mul_add, Finset.mul_sum])

theorem bW_apply (v w : (Fin 3 → S) × S × (Fin 3 → S') × S') :
    bW bS bS' v w = ∑ a, bS (v.1 a) (w.1 a) + bS v.2.1 w.2.1 +
      ∑ a, bS' (v.2.2.1 a) (w.2.2.1 a) + bS' v.2.2.2 w.2.2.2 := rfl

theorem bW_symm (hS : ∀ x y, bS x y = bS y x) (hS' : ∀ x y, bS' x y = bS' y x)
    (v w : (Fin 3 → S) × S × (Fin 3 → S') × S') : bW bS bS' v w = bW bS bS' w v := by
  simp only [bW_apply, hS, hS']

theorem nonneg_of_pos {E : Type*} [AddCommGroup E] [Module ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ x, x ≠ 0 → 0 < B x x) (x : E) : 0 ≤ B x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (hB x hx).le

theorem bW_pos (hS : ∀ x, x ≠ 0 → 0 < bS x x) (hS' : ∀ x, x ≠ 0 → 0 < bS' x x)
    (v : (Fin 3 → S) × S × (Fin 3 → S') × S') (hv : v ≠ 0) : 0 < bW bS bS' v v := by
  rw [bW_apply]
  have h1 : 0 ≤ ∑ a, bS (v.1 a) (v.1 a) := Finset.sum_nonneg fun a _ => nonneg_of_pos bS hS _
  have h2 : 0 ≤ bS v.2.1 v.2.1 := nonneg_of_pos bS hS _
  have h3 : 0 ≤ ∑ a, bS' (v.2.2.1 a) (v.2.2.1 a) :=
    Finset.sum_nonneg fun a _ => nonneg_of_pos bS' hS' _
  have h4 : 0 ≤ bS' v.2.2.2 v.2.2.2 := nonneg_of_pos bS' hS' _
  obtain ⟨Y, P, Yb, Pb⟩ := v
  by_cases hY : Y = 0
  · by_cases hP : P = 0
    · by_cases hYb : Yb = 0
      · have hPb : Pb ≠ 0 := fun h => hv (by simp [hY, hP, hYb, h])
        have := hS' Pb hPb
        simp only at h1 h2 h3 h4 this ⊢
        linarith
      · obtain ⟨a, ha⟩ : ∃ a, Yb a ≠ 0 := by
          by_contra hc; push Not at hc; exact hYb (funext hc)
        have h3' : 0 < ∑ a, bS' (Yb a) (Yb a) := Finset.sum_pos' (fun a _ =>
          nonneg_of_pos bS' hS' _) ⟨a, Finset.mem_univ a, hS' _ ha⟩
        simp only at h1 h2 h3 h4 h3' ⊢
        linarith
    · have := hS P hP
      simp only at h1 h2 h3 h4 this ⊢
      linarith
  · obtain ⟨a, ha⟩ : ∃ a, Y a ≠ 0 := by
      by_contra hc; push Not at hc; exact hY (funext hc)
    have h1' : 0 < ∑ a, bS (Y a) (Y a) := Finset.sum_pos' (fun a _ =>
      nonneg_of_pos bS hS _) ⟨a, Finset.mem_univ a, hS _ ha⟩
    simp only at h1 h2 h3 h4 h1' ⊢
    linarith

end Symmetriser

/-- The Dirac principal operator `𝒜^j = -βʲ - Ne_iʲc_0c_i` as an endomorphism. -/
def dPL (AF : AdaptedFrame) (Fr : CliffordFrame (Fin 4) (Module.End ℝ S₀)) (j : Fin 3) :
    Module.End ℝ S₀ :=
  -(AF.β j • (1 : Module.End ℝ S₀)) - AF.N • ∑ i : Fin 3, AF.E i j • (Fr.c 0 * Fr.c i.succ)

theorem dPL_apply (AF : AdaptedFrame) (Fr : CliffordFrame (Fin 4) (Module.End ℝ S₀)) (j : Fin 3)
    (x : S₀) : dPL AF Fr j x = diracP AF Fr j x := by
  unfold dPL diracP
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    Module.End.one_apply, LinearMap.sum_apply, Module.End.smul_def]

variable (SM : SMData (MatLie m) V S S')

/-- **The principal operators of the first-order block**: `𝒜^j_Dirac` on each component. -/
def Aop (AF : AdaptedFrame) (j : Fin 3) :
    ((Fin 3 → S) × S × (Fin 3 → S') × S') →ₗ[ℝ] ((Fin 3 → S) × S × (Fin 3 → S') × S') :=
  LinearMap.prodMap (LinearMap.pi fun a => dPL AF SM.D.Fr j ∘ₗ LinearMap.proj a)
    (LinearMap.prodMap (dPL AF SM.D.Fr j)
      (LinearMap.prodMap (LinearMap.pi fun a => dPL AF SM.Db.Fr j ∘ₗ LinearMap.proj a)
        (dPL AF SM.Db.Fr j)))

theorem Aop_apply (AF : AdaptedFrame) (j : Fin 3) (v : (Fin 3 → S) × S × (Fin 3 → S') × S') :
    Aop SM AF j v = (fun a => diracP AF SM.D.Fr j (v.1 a), diracP AF SM.D.Fr j v.2.1,
      fun a => diracP AF SM.Db.Fr j (v.2.2.1 a), diracP AF SM.Db.Fr j v.2.2.2) := by
  refine Prod.ext (funext fun a => ?_) (Prod.ext ?_ (Prod.ext (funext fun a => ?_) ?_)) <;>
    exact dPL_apply _ _ _ _

variable {SM}

theorem Aop_symm {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
    (hU : ActualJetKato.UnitaryForms SM bG bV bS bS') (AF : AdaptedFrame) (j : Fin 3)
    (v w : (Fin 3 → S) × S × (Fin 3 → S') × S') :
    bW bS bS' (Aop SM AF j v) w = bW bS bS' v (Aop SM AF j w) := by
  have hD := diracP_symm AF SM.D.Fr bS (c0ci_selfAdjoint SM.D.Fr bS hU.c0 hU.ci) j
  have hDb := diracP_symm AF SM.Db.Fr bS' (c0ci_selfAdjoint SM.Db.Fr bS' hU.c0b hU.cib) j
  simp only [bW_apply, Aop_apply, hD, hDb]

/-! ### Smoothness and periodicity of the coefficients and of the unknown -/

section Fields

variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}

theorem frame_β (AF : AdaptedFrame) (j : Fin 3) : AF.β j = -(AF.fr 0 j.succ * AF.N) := by
  rw [AdaptedFrame.fr_zero_succ]
  field_simp [AF.N_ne]

theorem contDiff_frameN : ContDiff ℝ ∞ fun y => (frameU (z.gi y)).N := by
  have e : (fun y => (frameU (z.gi y)).N) = fun y => ((frameU (z.gi y)).fr 0 0)⁻¹ := by
    funext y; rw [AdaptedFrame.fr_zero_zero, inv_inv]
  rw [e]
  exact (GenCplP.contDiff_fr (z := z) 0 0).inv fun y => by
    rw [AdaptedFrame.fr_zero_zero]; exact inv_ne_zero (frameU (z.gi y)).N_pos.ne'

theorem contDiff_frameβ (j : Fin 3) : ContDiff ℝ ∞ fun y => (frameU (z.gi y)).β j := by
  simp only [frame_β]
  exact ((GenCplP.contDiff_fr (z := z) 0 j.succ).mul contDiff_frameN).neg

theorem contDiff_frameE (i j : Fin 3) : ContDiff ℝ ∞ fun y => (frameU (z.gi y)).E i j := by
  simp only [← AdaptedFrame.fr_succ_succ]
  exact GenCplP.contDiff_fr (z := z) i.succ j.succ

theorem contDiff_diracP (D : DiracData (MatLie m) V S₀) (j : Fin 3) (v : S₀) :
    ContDiff ℝ ∞ fun y => diracP (frameU (z.gi y)) D.Fr j v := by
  unfold diracP
  exact ((contDiff_frameβ j).smul contDiff_const).neg.sub (contDiff_frameN.smul
    (ContDiff.sum fun i _ => (contDiff_frameE i j).smul contDiff_const))

theorem contDiff_Aop (j : Fin 3) (v : (Fin 3 → S) × S × (Fin 3 → S') × S') :
    ContDiff ℝ ∞ fun y => Aop SM (frameU (z.gi y)) j v := by
  simp only [Aop_apply]
  exact (contDiff_pi.2 fun a => contDiff_diracP SM.D j _).prodMk ((contDiff_diracP SM.D j _).prodMk
    ((contDiff_pi.2 fun a => contDiff_diracP SM.Db j _).prodMk (contDiff_diracP SM.Db j _)))

theorem isSPeriodic_Aop (j : Fin 3) : IsSPeriodic fun y => Aop SM (frameU (z.gi y)) j :=
  fun k y => by simp only [ActualJetState.gi_per z k y]

variable (SM W z)

theorem isSPeriodic_Yt (hWp : IsSPeriodic W) : IsSPeriodic (Yt SM W z) := fun k y => by
  simp only [Yt, hWp k y, ActualJetState.isSPeriodic_stateF SM z k y]

theorem isSPeriodic_Ybt (hWp : IsSPeriodic W) : IsSPeriodic (Ybt SM W z) := fun k y => by
  simp only [Ybt, hWp k y, ActualJetState.isSPeriodic_stateF SM z k y]

theorem isSPeriodic_Yf (hWp : IsSPeriodic W) : IsSPeriodic (Yf SM W z) := fun k y => by
  simp only [Yf, isSPeriodic_Yt SM W z hWp k y]

theorem isSPeriodic_Ybf (hWp : IsSPeriodic W) : IsSPeriodic (Ybf SM W z) := fun k y => by
  simp only [Ybf, isSPeriodic_Ybt SM W z hWp k y]

theorem ωF_per (D : DiracData (MatLie m) V S₀) (k : Fin 3 → ℤ) (y : ST 3) :
    ωF z D (y + sshift k) = ωF z D y := by
  funext B
  simp only [ωF, z.g_per k y, ActualJetState.gi_per z k y, ActualJetState.dg_per z k y,
    ActualJetState.de_per z k y, z.A_per k y]

theorem ΓF_per (k : Fin 3 → ℤ) (y : ST 3) : ΓF z (y + sshift k) = ΓF z y := by
  funext B A C
  simp only [ΓF, z.g_per k y, ActualJetState.gi_per z k y, ActualJetState.dg_per z k y,
    ActualJetState.de_per z k y]

theorem sD_per (k : Fin 3 → ℤ) (y : ST 3) : sD z (y + sshift k) = sD z y := by
  funext μ ν
  simp only [sD, z.g_per k y, ActualJetState.gi_per z k y, ActualJetState.dg_per z k y,
    GenHarmonic.ddg_per z k y]

theorem isSPeriodic_Pf (hWp : IsSPeriodic W) : IsSPeriodic (Pf SM W z) := fun k y => by
  have hY := isSPeriodic_Yf SM W z hWp
  have hpY : ∀ μ, pd (Yf SM W z) μ (y + sshift k) = pd (Yf SM W z) μ y := fun μ =>
    GenGauss.isSPeriodic_pd hY μ k y
  simp only [Pf, Qf, Rf, QF, RF, fd, ωF_per, ΓF_per, sD_per, hY k y, hpY, z.g_per k y,
    ActualJetState.gi_per z k y, ActualJetState.dg_per z k y, ActualJetState.de_per z k y,
    GenHarmonic.ddg_per z k y, z.A_per k y, z.H_per k y, z.ψ_per k y]

theorem isSPeriodic_Pbf (hWp : IsSPeriodic W) : IsSPeriodic (Pbf SM W z) := fun k y => by
  have hY := isSPeriodic_Ybf SM W z hWp
  have hpY : ∀ μ, pd (Ybf SM W z) μ (y + sshift k) = pd (Ybf SM W z) μ y := fun μ =>
    GenGauss.isSPeriodic_pd hY μ k y
  simp only [Pbf, Qbf, Rbf, QF, RF, fd, ωF_per, ΓF_per, sD_per, hY k y, hpY, z.g_per k y,
    ActualJetState.gi_per z k y, ActualJetState.dg_per z k y, ActualJetState.de_per z k y,
    GenHarmonic.ddg_per z k y, z.A_per k y, z.H_per k y, z.ψb_per k y]

theorem isSPeriodic_wF (hWp : IsSPeriodic W) : IsSPeriodic (wF SM W z) := fun k y => by
  simp only [wF, isSPeriodic_Yt SM W z hWp k y, isSPeriodic_Pf SM W z hWp k y,
    isSPeriodic_Ybt SM W z hWp k y, isSPeriodic_Pbf SM W z hWp k y]

theorem contDiff_wF (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (wF SM W z) :=
  (contDiff_Yt SM W z hW).prodMk ((contDiff_Pf (SM := SM) (W := W) (z := z) hW).prodMk
    ((contDiff_Ybt SM W z hW).prodMk (contDiff_Pbf (SM := SM) (W := W) (z := z) hW)))

theorem pd_wF (hW : ContDiff ℝ ∞ W) (x : ST 3) (μ : Fin 4) :
    pd (wF SM W z) μ x = (pd (Yt SM W z) μ x, pd (Pf SM W z) μ x, pd (Ybt SM W z) μ x,
      pd (Pbf SM W z) μ x) := by
  have d1 := (contDiff_Yt SM W z hW).differentiable (by simp) x
  have d2 := (contDiff_Pf (SM := SM) (W := W) (z := z) hW).differentiable (by simp) x
  have d3 := (contDiff_Ybt SM W z hW).differentiable (by simp) x
  have d4 := (contDiff_Pbf (SM := SM) (W := W) (z := z) hW).differentiable (by simp) x
  have e : wF SM W z = fun y => (Yt SM W z y, Pf SM W z y, Ybt SM W z y, Pbf SM W z y) := rfl
  unfold SobolevOpen.pd
  rw [e, DifferentiableAt.fderiv_prodMk d1 (d2.prodMk (d3.prodMk d4)),
    DifferentiableAt.fderiv_prodMk d2 (d3.prodMk d4), DifferentiableAt.fderiv_prodMk d3 d4]
  rfl

end Fields

/-! ### The vanishing of the coupled defects -/

section Vanish

variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
  {a b : ℝ}

theorem Ctrl.prod {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] {U : ST 3 → E} {s : Set (ST 3)} {r : ST 3 → F} {r' : ST 3 → G}
    (h : Ctrl U s r) (h' : Ctrl U s r') : Ctrl U s (fun y => (r y, r' y)) := by
  obtain ⟨K, hK, hb⟩ := h
  obtain ⟨K', hK', hb'⟩ := h'
  refine ⟨K + K', add_nonneg hK hK', fun y hy => ?_⟩
  rw [Prod.norm_def]
  have hU := norm_nonneg (U y)
  refine max_le ((hb y hy).trans ?_) ((hb' y hy).trans ?_) <;> nlinarith

/-- The rows of the first-order block, componentwise. -/
theorem row_eq (hW : ContDiff ℝ ∞ W) (x : ST 3) :
    pd (wF SM W z) 0 x + ∑ j : Fin 3, Aop SM (frameU (z.gi x)) j (pd (wF SM W z) j.succ x) =
      (fun a' => pd (Yt SM W z) 0 x a' + ∑ j : Fin 3, diracP (frameU (z.gi x)) SM.D.Fr j
          (pd (Yt SM W z) j.succ x a'),
        pd (Pf SM W z) 0 x + ∑ j : Fin 3, diracP (frameU (z.gi x)) SM.D.Fr j
          (pd (Pf SM W z) j.succ x),
        fun a' => pd (Ybt SM W z) 0 x a' + ∑ j : Fin 3, diracP (frameU (z.gi x)) SM.Db.Fr j
          (pd (Ybt SM W z) j.succ x a'),
        pd (Pbf SM W z) 0 x + ∑ j : Fin 3, diracP (frameU (z.gi x)) SM.Db.Fr j
          (pd (Pbf SM W z) j.succ x)) := by
  simp only [pd_wF SM W z hW, Aop_apply]
  refine Prod.ext (funext fun a' => ?_) (Prod.ext ?_ (Prod.ext (funext fun a' => ?_) ?_)) <;>
    simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- **The coupled defects vanish** (`lem:generated-physical-identification`, coupled spinors):
if `W` solves the shift-transported system with the bosonic blocks and head spinors of `z`
(`CplSol`), the complete stress of `z` (with the symmetric Dirac stress of back-reacting theory
data) is conserved on `[t₀, t₁] × 𝕋³`, and the lowered harmonic defect `c`, its time
derivative and the first-order defects `(Y, P, Ȳ, P̄)` vanish on `t = t₀`, then `c = 0` and
`(Y, P, Ȳ, P̄) = 0` on `[t₀, t₁] × 𝕋³`. -/
theorem coupled_constraints_vanish (hC : GenDStress.CoupledDirac SM)
    (hU : ActualJetKato.UnitaryForms SM bG bV bS bS') (hW : ContDiff ℝ ∞ W)
    (hWp : IsSPeriodic W) (h : CplSol SM W z a b) {t₀ t₁ : ℝ} (ha : a < t₀) (h01 : t₀ < t₁)
    (hb : t₁ < b) (hdivT : ∀ x ∈ slab t₀ t₁, ∀ ν, GenStress.divT SM z x ν = 0)
    (h0 : ∀ y : Fin 3 → ℝ, GenHarmonic.cF z (Fin.cons t₀ y) = 0)
    (h0t : ∀ y : Fin 3 → ℝ, pd (GenHarmonic.cF z) 0 (Fin.cons t₀ y) = 0)
    (hw0 : ∀ y : Fin 3 → ℝ, wF SM W z (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, GenHarmonic.cF z x = 0 ∧ wF SM W z x = 0 := by
  have hdivT' : ∀ x ∈ cube t₀ t₁, ∀ ν, GenStress.divT SM z x ν = 0 := fun x hx =>
    hdivT x (cube_subset_slab t₀ t₁ hx)
  have hbox := fun i => ctrl_boxc hC hW h ha hb hdivT' i
  -- the frame data
  have heC : ContDiff ℝ ∞ (fun x => z.e x) :=
    contDiff_pi.2 fun A => contDiff_pi.2 fun μ => z.contDiff_e A μ
  have hep : IsSPeriodic (fun x => z.e x) := fun k y => funext fun A => funext fun μ =>
    GenGauss.e_per z k y A μ
  have he0 : ∀ x (c : Fin 3), z.e x c.succ 0 = 0 := fun x c => by
    rw [GenGauss.e_eq_frameU]; exact AdaptedFrame.fr_succ_zero _ c
  have he00 : ∀ x, 0 < z.e x 0 0 := fun x => by
    rw [GenGauss.e_eq_frameU, AdaptedFrame.fr_zero_zero]; exact inv_pos.2 (frameU (z.gi x)).N_pos
  have hadapt : ∀ x μ ν, z.gi x μ ν = -(z.e x 0 μ * z.e x 0 ν) +
      ∑ c : Fin 3, z.e x c.succ μ * z.e x c.succ ν := fun x μ ν => by
    rw [z.compl x μ ν, Fin.sum_univ_succ]
    simp [lorentzSign, Fin.succ_ne_zero]
  have hθ : Continuous (GenHarmonic.cofF z) := by
    have h1 := z.contDiff_gc
    have h2 := z.contDiff_e
    refine continuous_pi fun A => continuous_pi fun γ => ?_
    show Continuous fun x => lorentzSign A * ∑ ν, z.g x γ ν * z.e x A ν
    have : ContDiff ℝ ∞ fun x => lorentzSign A * ∑ ν, z.g x γ ν * z.e x A ν := by fun_prop
    exact this.continuous
  have hθp : IsSPeriodic (GenHarmonic.cofF z) := fun k y => by
    funext A γ
    simp only [GenHarmonic.cofF, cof, z.g_per k y, GenGauss.e_per z k y]
  have hcof : ∀ x, ∀ (v : Fin 4 → ℝ) γ, v γ = ∑ B, GenHarmonic.cofF z x B γ *
      ∑ β, z.e x B β * v β := fun x v γ => by
    have := ActualJetRecon.inv_vec (z.jet x).FJ v γ
    simp only [smul_eq_mul] at this
    exact this
  -- the bounds
  obtain ⟨K1, hK1, hb1⟩ := Ctrl.pi (U := UF SM W z) (s := cube t₀ t₁) (F' := fun _ => ℝ)
    (r := fun x i => GenCplBox.boxc z x i) hbox
  have hrows : Ctrl (UF SM W z) (cube t₀ t₁) (fun x => pd (wF SM W z) 0 x +
      ∑ j : Fin 3, Aop SM (frameU (z.gi x)) j (pd (wF SM W z) j.succ x)) := by
    refine Ctrl.congr ?_ fun x _ => row_eq hW x
    have hxo : ∀ x ∈ cube t₀ t₁, x ∈ openSlab a b := fun x hx => cube_subset_openSlab ha hb hx
    refine Ctrl.prod (Ctrl.pi (F' := fun _ => S) fun a' => ?_) (Ctrl.prod ?_
      (Ctrl.prod (Ctrl.pi (F' := fun _ => S') fun a' => ?_) ?_))
    · exact (ctrl_Yrow_gen SM.D z.ψ_smooth.continuous ctrl_Yf a'.succ).congr fun x hx =>
        x_row_cpl h (hxo x hx) a'
    · exact ctrl_Prow_gen SM.D z.ψ_smooth (contDiff_Yf SM W z hW) ctrl_Yf
        (fun B => ctrl_Qf h ha hb B) ctrl_Pf hbox fun x hx => P_dirac hW h (hxo x hx)
    · exact (ctrl_Yrow_gen SM.Db z.ψb_smooth.continuous ctrl_Ybf a'.succ).congr fun x hx =>
        x_row_cpl_b h (hxo x hx) a'
    · exact ctrl_Prow_gen SM.Db z.ψb_smooth (contDiff_Ybf SM W z hW) ctrl_Ybf
        (fun B => ctrl_Qbf h ha hb B) ctrl_Pbf hbox fun x hx => P_dirac_b hW h (hxo x hx)
  obtain ⟨K2, hK2, hb2⟩ := hrows
  have hUle := fun x => norm_UF_le SM W z x
  refine coupled_unique_E (bW bS bS') (bW_symm bS bS' hU.symS hU.symS')
    (bW_pos bS bS' hU.posS hU.posS') (u := GenHarmonic.cF z) (w := wF SM W z)
    (e := fun x => z.e x) (gi := z.gi) (θ := GenHarmonic.cofF z)
    (Aop := fun j y => Aop SM (frameU (z.gi y)) j) ha h01 hb (GenHarmonic.contDiff_cF z)
    (GenHarmonic.isSPeriodic_cF z) (contDiff_wF SM W z hW) (isSPeriodic_wF SM W z hWp) heC hep
    he0 he00 hadapt hθ hθp hcof (fun j v => contDiff_Aop j v) (fun j => isSPeriodic_Aop j)
    (fun j y v v' => Aop_symm hU _ j v v') (le_max_left 0 (max K1 K2)) ?_ ?_ h0 h0t hw0
  · intro x hx i
    have h1 := hb1 x hx
    have h2 : |GenCplBox.boxc z x i| ≤ ‖(fun i => GenCplBox.boxc z x i)‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm (fun i => GenCplBox.boxc z x i) i
    have h3 := hUle x
    have hU0 := norm_nonneg (UF SM W z x)
    have hK : K1 ≤ max 0 (max K1 K2) := (le_max_left _ _).trans (le_max_right _ _)
    calc |∑ μ, ∑ β, z.gi x μ β * pd (pd (GenHarmonic.cF z) β) μ x i| =
        |GenCplBox.boxc z x i| := rfl
      _ ≤ K1 * ‖UF SM W z x‖ := h2.trans h1
      _ ≤ max 0 (max K1 K2) * ‖UF SM W z x‖ := mul_le_mul_of_nonneg_right hK hU0
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (le_max_left _ _)
  · intro x hx
    have h1 := hb2 x hx
    have h3 := hUle x
    have hU0 := norm_nonneg (UF SM W z x)
    have hK : K2 ≤ max 0 (max K1 K2) := (le_max_right _ _).trans (le_max_right _ _)
    calc _ ≤ K2 * ‖UF SM W z x‖ := h1
      _ ≤ max 0 (max K1 K2) * ‖UF SM W z x‖ := mul_le_mul_of_nonneg_right hK hU0
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (le_max_left _ _)

end Vanish

end RenewalGeometry.GenCplCon
