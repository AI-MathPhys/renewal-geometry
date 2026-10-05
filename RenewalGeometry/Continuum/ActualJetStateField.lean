/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetFieldBridge
import RenewalGeometry.Continuum.ActualJetCompleteForcing

/-!
# The actual-jet state field of a smooth field tuple and its first-order system

Einstein–Standard-Model action-closure manuscript, `prop:coupled-bootstrap` (and
`thm:native-closure`: "the state `𝒰_h` is built from the actual derivatives and curvatures of
`z_h`").

For a smooth actual field tuple `z` (`ActualJetBridge.Tuple`) the **actual-jet state field**
`𝒰(z)(x) = toP(state(jet_x z))` (`stateF`) is a smooth `StateP`-valued field on space-time, its
coordinate derivatives are the derivative jets of `prop:actual-jet-writer`
(`pd_stateF : ∂_δ𝒰 = toP(dstate δ)`), and therefore (`writer_pde`) it satisfies the
gauge-defect-aware block-symmetric system `eq:actual-jet-writer` **as a partial differential
equation** at every point:
`∂_t𝒰 + Σ_j 𝒜^j(g)∂_j𝒰 = 𝓕(𝒰) + 𝓑(𝒰)(𝓔, r^A, r_H, r_D, r̄_D) + Σ_j 𝒬^j(g)∂_j(r_D, r̄_D) + 𝔊(𝒰; C, ∂C)`,
with the residuals and the harmonic defect those of the tuple, and with `∂_j r_D`, `∂C` the actual
derivatives of the residual and defect fields (`pd_rD`, `pd_C`).
-/

open Finset Set
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.ActualJetState

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

/-- **The actual-jet state field** `𝒰(z)` in the coordinates `StateP`. -/
def stateF (x : ST 3) : StateP m V S S' := toP ((z.jet x).state SM)

theorem ofP_toP (U : State (MatLie m) V S S') : ofP (toP U) = U := rfl

/-! ### Smoothness of the state field -/

theorem contDiff_p : ContDiff ℝ ∞ (fun y => ((z.jet y).state SM).p) := by
  have he := z.contDiff_e
  have hdg := z.contDiff_dg
  refine contDiff_pi.2 fun μ => contDiff_pi.2 fun ν => ?_
  show ContDiff ℝ ∞ (fun y => ∑ β, z.e y 0 β * z.dg y β μ ν)
  fun_prop

theorem contDiff_q : ContDiff ℝ ∞ (fun y => ((z.jet y).state SM).q) := by
  have he := z.contDiff_e
  have hdg := z.contDiff_dg
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun μ => contDiff_pi.2 fun ν => ?_
  show ContDiff ℝ ∞ (fun y => ∑ β, z.e y a.succ β * z.dg y β μ ν)
  fun_prop

theorem contDiff_Fm (μ ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => Fm (z.jet y).A (z.jet y).dA μ ν) := by
  have hA := Tuple.contDiff_vec z.A_smooth
  have hdA := Tuple.contDiff_pdc z.A_smooth
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  show ContDiffAt ℝ ∞ (fun y => pd z.A μ y ν - pd z.A ν y μ + ⁅z.A y μ, z.A y ν⁆) y
  fun_prop

theorem contDiff_frT (b c : Fin 4) :
    ContDiff ℝ ∞ (fun y => frT (z.jet y).AF (Fm (z.jet y).A (z.jet y).dA) b c) := by
  have he := z.contDiff_e
  have hF := contDiff_Fm z
  show ContDiff ℝ ∞ (fun y => ∑ μ, ∑ ν, (z.e y b μ * z.e y c ν) •
    Fm (z.jet y).A (z.jet y).dA μ ν)
  fun_prop

theorem contDiff_frV (B : Fin 4) :
    ContDiff ℝ ∞ (fun y => frV (z.jet y).AF (z.jet y).A (z.jet y).H (z.jet y).dH B) := by
  have he := z.contDiff_e
  have hA := Tuple.contDiff_vec z.A_smooth
  have hH := z.H_smooth
  have hdH : ∀ μ, ContDiff ℝ ∞ (pd z.H μ) := fun μ => contDiff_pd z.H_smooth μ
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  show ContDiffAt ℝ ∞ (fun y => ∑ μ, z.e y B μ • (pd z.H μ y + ⁅z.A y μ, z.H y⁆)) y
  fun_prop

/-- **The state field is smooth.** -/
theorem contDiff_stateF : ContDiff ℝ ∞ (stateF SM z) := by
  unfold stateF toP
  refine ContDiff.prodMk (ContDiff.prodMk z.g_smooth (ContDiff.prodMk (contDiff_p SM z)
    (contDiff_q SM z))) ?_
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ (ContDiff.prodMk ?_ (ContDiff.prodMk z.H_smooth
    (ContDiff.prodMk (contDiff_frV z 0) (ContDiff.prodMk ?_ (ContDiff.prodMk z.ψ_smooth
      (ContDiff.prodMk ?_ (ContDiff.prodMk z.ψb_smooth ?_))))))))
  · exact contDiff_pi.2 fun i => Tuple.contDiff_vec z.A_smooth i.succ
  · exact contDiff_pi.2 fun a => contDiff_frT z 0 a.succ
  · refine contDiff_pi.2 fun a => ?_
    show ContDiff ℝ ∞ (fun y => dualVec (fun b c => frT (z.jet y).AF
      (Fm (z.jet y).A (z.jet y).dA) b.succ c.succ) a)
    have h := fun b c : Fin 3 => contDiff_frT z b.succ c.succ
    unfold dualVec
    fun_prop
  · exact contDiff_pi.2 fun a => contDiff_frV z a.succ
  · exact contDiff_pi.2 fun a => z.contDiff_Xs SM.D z.ψ_smooth a.succ
  · exact contDiff_pi.2 fun a => z.contDiff_Xs SM.Db z.ψb_smooth a.succ

/-! ### The bridge `∂_δ𝒰 = dstate δ` -/

theorem line_met {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] {f : ℝ → Fin 4 → Fin 4 → M}
    {f' : Fin 4 → Fin 4 → M} (h : ∀ μ ν, HasDerivAt (fun s => f s μ ν) (f' μ ν) 0) :
    HasDerivAt f f' 0 :=
  hasDerivAt_pi.2 fun μ => hasDerivAt_pi.2 fun ν => h μ ν

/-- **The state field has the derivative jets of `prop:actual-jet-writer` along every line.** -/
theorem line_stateF (x : ST 3) (δ : Fin 4) :
    HasDerivAt (fun s : ℝ => stateF SM z (x + s • ev δ)) (toP ((z.jet x).dstate SM δ)) 0 := by
  unfold stateF toP
  refine HasDerivAt.prodMk (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)) ?_
  · exact line_met fun μ ν => z.line_g x δ μ ν
  · exact line_met fun μ ν => z.line_p SM x δ μ ν
  · exact hasDerivAt_pi.2 fun a => line_met fun μ ν => z.line_q SM x δ a μ ν
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_
    (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_
      (HasDerivAt.prodMk ?_ ?_))))))))
  · exact hasDerivAt_pi.2 fun i => z.line_A x δ i.succ
  · exact hasDerivAt_pi.2 fun a => z.line_E SM x δ a
  · exact hasDerivAt_pi.2 fun a => z.line_B SM x δ a
  · exact z.line_H x δ
  · exact z.line_Pm SM x δ
  · exact hasDerivAt_pi.2 fun a => z.line_Q SM x δ a
  · exact hasDerivAt_line0 (z.ψ_smooth.differentiable (by simp) x) δ
  · exact hasDerivAt_pi.2 fun a => z.line_X SM x δ a
  · exact hasDerivAt_line0 (z.ψb_smooth.differentiable (by simp) x) δ
  · exact hasDerivAt_pi.2 fun a => z.line_Xb SM x δ a

/-- **`∂_δ𝒰 = dstate δ`**: the coordinate derivatives of the actual-jet state field are the
derivative jets of `prop:actual-jet-writer`. -/
theorem pd_stateF (x : ST 3) (δ : Fin 4) : pd (stateF SM z) δ x = toP ((z.jet x).dstate SM δ) :=
  pd_eq_of_line ((contDiff_stateF SM z).differentiable (by simp) x) (line_stateF SM z x δ)


/-! ### The residual and harmonic-defect fields -/

/-- The bosonic residual field `R_B = (𝓔^{tr}, r^A, r_H)` of the tuple. -/
def bosF (x : ST 3) : BosP m V :=
  (((z.jet x).res SM).Etr, ((z.jet x).res SM).rA, ((z.jet x).res SM).rH)

/-- The Dirac residual field `R_D = (r_D, r̄_D)` of the tuple. -/
def dirF (x : ST 3) : S × S' := (((z.jet x).res SM).rD, ((z.jet x).res SM).rDb)

/-- The harmonic-defect field `C^l = g^{αβ}Γ^l_{αβ}` of the metric. -/
def CF (x : ST 3) : Fin 4 → ℝ := fun l => ActualJetWriter.C (z.gi x) (z.dg x) l

theorem rD_eq' {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (D : DiracData (MatLie m) V S₀) (ψf : ST 3 → S₀) (y : ST 3) :
    (z.jet y).rD D (ψf y) (fun γ => pd ψf γ y) =
      ∑ b, D.Fr.ε b • D.Fr.c b ((z.jet y).Xs D (ψf y) (fun γ => pd ψf γ y) b) -
        (D.m0 (ψf y) + D.L (z.H y) (ψf y)) := by
  unfold ActualJet.rD resD dirac mass
  simp only [Module.End.smul_def, LinearMap.add_apply]
  rfl

theorem contDiff_rD {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    [FiniteDimensional ℝ S₀] (D : DiracData (MatLie m) V S₀) {ψf : ST 3 → S₀}
    (hψ : ContDiff ℝ ∞ ψf) :
    ContDiff ℝ ∞ (fun y => (z.jet y).rD D (ψf y) (fun γ => pd ψf γ y)) := by
  simp only [rD_eq' z D ψf]
  have hX := fun b => z.contDiff_Xs D hψ b
  have hc : ∀ b, ContDiff ℝ ∞ (fun y => D.Fr.c b ((z.jet y).Xs D (ψf y) (fun γ => pd ψf γ y) b)) :=
    fun b => (LinearMap.toContinuousLinearMap (D.Fr.c b)).contDiff.comp (hX b)
  have hm : ContDiff ℝ ∞ (fun y => D.m0 (ψf y)) :=
    (LinearMap.toContinuousLinearMap D.m0).contDiff.comp hψ
  have hL : ContDiff ℝ ∞ (fun y => D.L (z.H y) (ψf y)) :=
    contDiff_iff_contDiffAt.2 fun y =>
      ContDiffAt.bilinApply D.L z.H_smooth.contDiffAt hψ.contDiffAt
  fun_prop

theorem contDiff_dirF : ContDiff ℝ ∞ (dirF SM z) :=
  (contDiff_rD z SM.D z.ψ_smooth).prodMk (contDiff_rD z SM.Db z.ψb_smooth)

theorem contDiff_CF : ContDiff ℝ ∞ (CF z) := by
  refine contDiff_pi.2 fun l => ?_
  have h1 := z.contDiff_gi
  have h2 := z.contDiff_chr
  show ContDiff ℝ ∞ (fun y => ∑ a, ∑ b, z.gi y a b * chr (z.gi y) (z.dg y) l a b)
  fun_prop

/-- **The Dirac residual jets are the derivatives of the Dirac residual field.** -/
theorem pd_dirF (x : ST 3) (δ : Fin 4) :
    pd (dirF SM z) δ x = ((z.jet x).drD SM.D (z.ψ x) (fun γ => pd z.ψ γ x)
        (fun δ γ => pd (pd z.ψ γ) δ x) δ,
      (z.jet x).drD SM.Db (z.ψb x) (fun γ => pd z.ψb γ x) (fun δ γ => pd (pd z.ψb γ) δ x) δ) :=
  pd_eq_of_line ((contDiff_dirF SM z).differentiable (by simp) x)
    ((z.line_rD x δ SM.D z.ψ_smooth).prodMk (z.line_rD x δ SM.Db z.ψb_smooth))

/-- **The harmonic-defect jets are the derivatives of the harmonic-defect field.** -/
theorem pd_CF (x : ST 3) (δ : Fin 4) :
    pd (CF z) δ x = fun l => ActualJetWriter.dC (z.gi x) (z.dg x) (z.ddg x) δ l :=
  pd_eq_of_line ((contDiff_CF z).differentiable (by simp) x)
    (hasDerivAt_pi.2 fun l => z.line_C x δ l)

/-! ### The system as a partial differential equation -/

/-- The principal operators `𝒜^j(g)` as linear maps of state increments (coordinates). -/
def princL (v : StateP m V S S') (j : Fin 3) : StateP m V S S' →ₗ[ℝ] StateP m V S S' where
  toFun W := toP (princ (frameU (ginvOf v.1.1)) SM.D.Fr SM.Db.Fr j (ofP W))
  map_add' W W' := by
    ext <;> simp only [toP, ofP, princ, Prod.fst_add, Prod.snd_add, Pi.add_apply, diracP,
      Module.End.smul_def, map_add, smul_add, Finset.sum_add_distrib, mul_add, neg_add] <;>
      first | ring | abel
  map_smul' c W := by
    ext <;> simp only [toP, ofP, princ, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, diracP,
      Module.End.smul_def, map_smul, smul_eq_mul, RingHom.id_apply, smul_add, smul_sub, smul_neg,
      Finset.smul_sum, Finset.mul_sum, smul_smul, mul_zero, smul_zero, neg_zero, sub_zero] <;>
      ring_nf <;> simp only [Finset.mul_sum] <;> ring_nf


/-- `WriterEq` (`eq:actual-jet-writer`, blockwise) as one equation in the state coordinates. -/
theorem writerEq_toP {dU : Fin 4 → State (MatLie m) V S S'}
    {P : Fin 3 → State (MatLie m) V S S' → State (MatLie m) V S S'}
    {F B G : State (MatLie m) V S S'} {Qj : Fin 3 → State (MatLie m) V S S'}
    (h : WriterEq dU P F B G Qj) :
    toP (dU 0) + ∑ j, toP (P j (dU j.succ)) = toP F + toP B + ∑ j, toP (Qj j) + toP G := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  ext <;> simp only [toP, Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum, Pi.add_apply,
    Finset.sum_apply]
  all_goals first
    | exact h1 _ _
    | exact h2 _ _
    | exact h3 _ _ _
    | exact h4 _
    | exact h5 _
    | exact h6 _
    | exact h7
    | exact h8
    | exact h9 _
    | exact h10
    | exact h11 _
    | exact h12
    | exact h13 _

theorem jet_dg_eq (x : ST 3) : (z.jet x).FJ.dg = dgOf (stateF SM z x).1 :=
  (congrArg FirstJet.dg (ActualJet.recon_state (z.jet x) SM)).symm

/-- **The actual-jet state field satisfies `eq:actual-jet-writer` as a PDE** at every point:
`∂_t𝒰 + Σ_j𝒜^j(g)∂_j𝒰 = 𝓕(𝒰) + 𝓑(𝒰)(R_B, R_D) + Σ_j𝒬^j(g)∂_jR_D + 𝒥_C C + 𝒥_C^0∂_tC +
Σ_j𝒥_C^j∂_jC`, with the actual residual fields `R_B = bosF`, `R_D = dirF` and harmonic defect
`C = CF` of the tuple. -/
theorem writer_pde (x : ST 3) :
    pd (stateF SM z) 0 x + ∑ j : Fin 3, princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x) =
      toP (Fsys SM (ofP (stateF SM z x))) +
        (BmL SM (stateF SM z x) (bosF SM z x) + DmL SM (stateF SM z x) (dirF SM z x)) +
        ∑ j : Fin 3, QmL SM j (stateF SM z x) (pd (dirF SM z) j.succ x) +
        (GcL (stateF SM z x) (CF z x) + GdL 0 (stateF SM z x) (pd (CF z) 0 x) +
          ∑ j : Fin 3, GdL j.succ (stateF SM z x) (pd (CF z) j.succ x)) := by
  have hw := writerEq_toP (ActualJetSystem.actual_jet_writer (z.jet x) SM)
  have hB : toP (Bsys SM ((z.jet x).state SM) ((z.jet x).res SM)) =
      BmL SM (stateF SM z x) (bosF SM z x) + DmL SM (stateF SM z x) (dirF SM z x) :=
    Bsys_split SM (stateF SM z x) ((bosF SM z x).1, (bosF SM z x).2.1, (bosF SM z x).2.2,
      (dirF SM z x).1, (dirF SM z x).2)
  have hG : toP (Gsys (𝔤 := MatLie m) (V := V) (S := S) (S' := S')
      (frameU (ginvOf ((z.jet x).state SM).g)) ((z.jet x).state SM).g
      (ginvOf ((z.jet x).state SM).g) (z.jet x).FJ.dg (z.jet x).FJ.ddg) =
      GcL (stateF SM z x) (CF z x) + GdL 0 (stateF SM z x) (pd (CF z) 0 x) +
        ∑ j : Fin 3, GdL j.succ (stateF SM z x) (pd (CF z) j.succ x) := by
    rw [jet_dg_eq SM z x]
    have := Gsys_split (V := V) (S := S) (S' := S') (stateF SM z x) (z.jet x).FJ.ddg
    refine this.trans ?_
    rw [pd_CF z x 0]
    simp only [pd_CF z x]
    rw [← jet_dg_eq SM z x]
    rfl
  have hQ : ∀ j : Fin 3, toP (Qsys SM ((z.jet x).state SM) j
      ((z.jet x).drD SM.D (z.jet x).ψ (z.jet x).cψ (z.jet x).ccψ j.succ)
      ((z.jet x).drD SM.Db (z.jet x).ψb (z.jet x).cψb (z.jet x).ccψb j.succ)) =
      QmL SM j (stateF SM z x) (pd (dirF SM z) j.succ x) := by
    intro j
    rw [pd_dirF SM z x j.succ]
    rfl
  have hP : ∀ j : Fin 3, toP (princ (frameU (ginvOf ((z.jet x).state SM).g)) SM.D.Fr SM.Db.Fr j
      ((z.jet x).dstate SM j.succ)) = princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x) := by
    intro j
    rw [pd_stateF SM z x j.succ]
    rfl
  rw [← pd_stateF SM z x 0] at hw
  simp only [hP, hQ] at hw
  rw [hB, hG] at hw
  exact hw

/-! ### Smoothness of the residual fields -/

set_option maxHeartbeats 4000000 in
theorem contDiff_rA (hS : SMSmooth SM) (ν : Fin 4) :
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
  fun_prop (disch := exact hS)

set_option maxHeartbeats 4000000 in
theorem contDiff_rH (hS : SMSmooth SM) :
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
  fun_prop (disch := exact hS)

set_option maxHeartbeats 8000000 in
theorem contDiff_Etr (hS : SMSmooth SM) (μ ν : Fin 4) :
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
  fun_prop (disch := exact hS)

/-- **The bosonic residual field is smooth** (for smooth theory data). -/
theorem contDiff_bosF (hS : SMSmooth SM) : ContDiff ℝ ∞ (bosF SM z) :=
  (contDiff_pi.2 fun μ => contDiff_pi.2 fun ν => contDiff_Etr SM z hS μ ν).prodMk
    ((contDiff_pi.2 fun ν => contDiff_rA SM z hS ν).prodMk (contDiff_rH SM z hS))

/-! ### Spatial periodicity -/

theorem isSPeriodic_pd' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ST 3 → E}
    (hF : SymHypEnergy.IsSPeriodic F) (μ : Fin 4) : SymHypEnergy.IsSPeriodic (pd F μ) :=
  fun k x => by
  unfold SobolevOpen.pd
  have h : (fun y => F (y + SymHypEnergy.sshift k)) = F := funext fun y => hF k y
  rw [← fderiv_comp_add_right, h]

theorem dg_per (k : Fin 3 → ℤ) (y : ST 3) : z.dg (y + SymHypEnergy.sshift k) = z.dg y :=
  funext fun α => isSPeriodic_pd' z.g_per α k y

theorem gi_per (k : Fin 3 → ℤ) (y : ST 3) : z.gi (y + SymHypEnergy.sshift k) = z.gi y := by
  simp only [Tuple.gi, z.g_per k y]

theorem de_per (k : Fin 3 → ℤ) (y : ST 3) : z.de (y + SymHypEnergy.sshift k) = z.de y := by
  funext γ A μ
  simp only [Tuple.de, gi_per z k y, dg_per z k y]

theorem FJ_per (k : Fin 3 → ℤ) (x : ST 3) : z.FJ (x + SymHypEnergy.sshift k) = z.FJ x := by
  have e_g : z.g (x + SymHypEnergy.sshift k) = z.g x := z.g_per k x
  have e_gi := gi_per z k x
  have e_dg := dg_per z k x
  have e_ddg : z.ddg (x + SymHypEnergy.sshift k) = z.ddg x :=
    funext fun β => funext fun α => isSPeriodic_pd' (isSPeriodic_pd' z.g_per α) β k x
  have e_e : z.e (x + SymHypEnergy.sshift k) = z.e x := by
    funext A μ; simp only [Tuple.e, e_gi]
  have e_de := de_per z k x
  have hdeF : ∀ γ A μ, SymHypEnergy.IsSPeriodic (fun y => z.de y γ A μ) := fun γ A μ k y => by
    simp only [de_per z k y]
  have e_dde : z.dde (x + SymHypEnergy.sshift k) = z.dde x := by
    funext δ γ A μ; exact isSPeriodic_pd' (hdeF γ A μ) δ k x
  unfold Tuple.FJ
  congr 1

theorem jet_per (k : Fin 3 → ℤ) (x : ST 3) : z.jet (x + SymHypEnergy.sshift k) = z.jet x := by
  unfold Tuple.jet
  congr 1
  · exact FJ_per z k x
  · exact z.A_per k x
  · funext γ μ; rw [isSPeriodic_pd' z.A_per γ k x]
  · funext δ γ μ; rw [isSPeriodic_pd' (isSPeriodic_pd' z.A_per γ) δ k x]
  · exact z.H_per k x
  · funext γ; exact isSPeriodic_pd' z.H_per γ k x
  · funext δ γ; exact isSPeriodic_pd' (isSPeriodic_pd' z.H_per γ) δ k x
  · exact z.ψ_per k x
  · funext γ; exact isSPeriodic_pd' z.ψ_per γ k x
  · funext δ γ; exact isSPeriodic_pd' (isSPeriodic_pd' z.ψ_per γ) δ k x
  · exact z.ψb_per k x
  · funext γ; exact isSPeriodic_pd' z.ψb_per γ k x
  · funext δ γ; exact isSPeriodic_pd' (isSPeriodic_pd' z.ψb_per γ) δ k x

theorem isSPeriodic_stateF : SymHypEnergy.IsSPeriodic (stateF SM z) := fun k x => by
  simp only [stateF, jet_per z k x]

theorem isSPeriodic_bosF : SymHypEnergy.IsSPeriodic (bosF SM z) := fun k x => by
  simp only [bosF, jet_per z k x]

theorem isSPeriodic_dirF : SymHypEnergy.IsSPeriodic (dirF SM z) := fun k x => by
  simp only [dirF, jet_per z k x]

theorem isSPeriodic_CF : SymHypEnergy.IsSPeriodic (CF z) := fun k x => by
  funext l
  simp only [CF, gi_per z k x, dg_per z k x]

end RenewalGeometry.ActualJetState
