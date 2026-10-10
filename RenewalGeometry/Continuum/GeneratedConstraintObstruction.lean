/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedPhysicalIdentification

/-!
# Constraint propagation fails for non-variational theory data

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`.

The physical identification of the independent symmetric system `eq:generated-extension` cannot
be proved for the general theory data `ActualJetSystem.SMData` of the library: the Yang–Mills
source `Jcur`, the Higgs source `SH` and the Dirac stress `TD` are arbitrary functions there, while
the propagation of the Gauss constraint needs covariant conservation of the current on solutions
(and the propagation of the harmonic constraint needs conservation of the stress) — Noether
identities that hold for the Standard-Model Lagrangian but are not encoded in `SMData`.

* `badSM` — the vanishing-coupling data `trivSMM` (gauge algebra `gl(1)`, adjoint Higgs, zero
  spinor spaces, zero stress forms) with the **non-conserved charge density** `J_0 = H`
  (smooth sources, `badSM_smooth`).
* `bad` — Minkowski metric, `A = 0`, Higgs field `H(t, x) = t`, trivial spinors.
* **`bad_obstruction`** — the actual-jet state field of `bad` solves the independent symmetric
  system everywhere (`GenConstraint.SymEqAt`); at `t = 0` all physical residuals and the harmonic
  defect vanish (the datum is constrained); but for every `t ≠ 0` the Gauss constraint fails
  (`GenConstraint.gaussF ≠ 0`), so `bad` is not a physical solution on any slab `[0, t₁]`,
  `t₁ > 0` (`bad_not_physical`).
* **`kato_solution_not_physical`** — with the realized symmetric coefficients
  (`ActualJetKato.actual_jet_kato_realization`) on a compact chart margin containing the states of
  `bad`, every classical two-sided solution of the realized system with the datum `𝒰(bad)(0)`
  coincides with `𝒰(bad)` on `[0, t₁]` (uniqueness), hence violates the Gauss law at every
  `t ∈ (0, t₁]`: the conclusion of `lem:generated-physical-identification` is false for these
  data, and `KatoStab.AnalyticCoreContinuation` / `GenPhysId.PhysicalCauchyCore` cannot hold for
  a core containing this datum.

Consequence for the formalisation plan: constraint propagation for the actual-jet system needs, in
addition to the symmetric system, the Noether identities of the Standard-Model couplings
(`D^μJ_μ = 0` and `∇^μT_{μν} = 0` modulo the residuals) as hypotheses on the theory data.
-/

open Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.GenConstraintObs

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk QLEnergy FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetCompleteForcing
  ActualJetState ActualJetRecon ActualJetKato GenConstraint GenPhysId CoupledBootstrap.FlatVacuum

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-- **Theory data with a non-conserved charge density**: `trivSMM` with `J_ν = δ_ν^0 H`. -/
def badSM : SMData (MatLie 1) (MatLie 1) PUnit PUnit :=
  { trivSMM with Jcur := fun _ _ H _ _ _ ν => if ν = 0 then H else 0 }

theorem badSM_smooth : SMSmooth badSM where
  J ν := by
    by_cases h : ν = 0
    · have : (fun p : Met × Met × MatLie 1 × (Fin 4 → MatLie 1) × PUnit × PUnit =>
          badSM.Jcur p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ν) =
          fun p => p.2.2.1 := by funext p; simp [badSM, h]
      rw [this]
      exact contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
    · have : (fun p : Met × Met × MatLie 1 × (Fin 4 → MatLie 1) × PUnit × PUnit =>
          badSM.Jcur p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ν) =
          fun _ => 0 := by funext p; simp [badSM, h]
      rw [this]
      exact contDiff_const
  SH := trivSMM_smooth.SH
  P2 := trivSMM_smooth.P2

/-- The Higgs field `H(t, x) = t`. -/
def hgs (x : ST 3) : MatLie 1 := x 0 • (1 : MatLie 1)

theorem hgs_eq : hgs = fun x => ((ContinuousLinearMap.proj 0 : ST 3 →L[ℝ] ℝ).smulRight
    (1 : MatLie 1)) x := rfl

theorem contDiff_hgs : ContDiff ℝ ∞ hgs := by
  rw [hgs_eq]; exact ContinuousLinearMap.contDiff _

theorem pd_hgs (γ : Fin 4) (x : ST 3) : pd hgs γ x = (Pi.single γ (1 : ℝ) : ST 3) 0 • (1 : MatLie 1) := by
  unfold SobolevOpen.pd
  rw [hgs_eq, ContinuousLinearMap.fderiv]
  rfl

theorem pd_pd_hgs (γ δ : Fin 4) (x : ST 3) : pd (pd hgs γ) δ x = 0 := by
  have : pd hgs γ = fun _ => (Pi.single γ (1 : ℝ) : ST 3) 0 • (1 : MatLie 1) :=
    funext fun y => pd_hgs γ y
  rw [this]
  exact pd_const' _ δ x

/-- **The obstruction tuple**: Minkowski metric, vanishing gauge potential, Higgs field `H = t`,
trivial spinors. -/
def bad : Tuple 1 (MatLie 1) PUnit.{1} PUnit.{1} where
  g := fun _ => minkInv
  A := fun _ => 0
  H := hgs
  ψ := fun _ => PUnit.unit
  ψb := fun _ => PUnit.unit
  g_smooth := contDiff_const
  A_smooth := contDiff_const
  H_smooth := contDiff_hgs
  ψ_smooth := contDiff_const
  ψb_smooth := contDiff_const
  g_per := fun _ _ => rfl
  A_per := fun _ _ => rfl
  H_per := fun k x => by simp [hgs, sshift]
  ψ_per := fun _ _ => rfl
  ψb_per := fun _ _ => rfl
  g_symm := fun _ => ActualJetFrame.minkInv_symm
  temporal := fun _ => rfl
  det_ne := fun _ => minkInv_det
  lor := fun _ => by rw [ginvOf_minkInv]; exact minkInv_isLorChart

theorem bad_dg (x : ST 3) : bad.dg x = 0 := by
  funext α; exact pd_const' _ α x

theorem bad_ddg (x : ST 3) : bad.ddg x = 0 := by
  funext β α; simp [Tuple.ddg, bad, pd_const_fun]

theorem bad_jet_dA (x : ST 3) : (bad.jet x).dA = 0 := by
  funext γ μ; simp [Tuple.jet, bad, pd_const_fun]

theorem bad_jet_ddA (x : ST 3) : (bad.jet x).ddA = 0 := by
  funext δ γ μ; simp [Tuple.jet, bad, pd_const_fun]

theorem bad_jet_dH (x : ST 3) (γ : Fin 4) :
    (bad.jet x).dH γ = (Pi.single γ (1 : ℝ) : ST 3) 0 • (1 : MatLie 1) := by
  show pd hgs γ x = _
  exact pd_hgs γ x

theorem bad_jet_ddH (x : ST 3) : (bad.jet x).ddH = 0 := by
  funext δ γ
  show pd (pd hgs γ) δ x = 0
  exact pd_pd_hgs γ δ x

/-- The bosonic residual of `bad`: vanishing Einstein and Higgs residuals, Yang–Mills residual
`r^A_ν = -δ_ν^0 H` (the uncompensated charge density). -/
theorem bad_bosF (x : ST 3) :
    bosF badSM bad x = (0, fun ν => if ν = 0 then -hgs x else 0, 0) := by
  have h1 : (bad.jet x).FJ.dg = 0 := bad_dg x
  have h2 : (bad.jet x).FJ.ddg = 0 := bad_ddg x
  have h3 : (bad.jet x).A = 0 := rfl
  have h6 : (bad.jet x).H = hgs x := rfl
  have h7 : (bad.jet x).ddH = 0 := bad_jet_ddH x
  simp only [bosF, ActualJet.res, ActualJet.Tact, h1, h2, h3, bad_jet_dA, bad_jet_ddA, h6, h7]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext μ ν
    simp [einstein, ricci, ricciJ, chr, dchr, dchr1, dchr2, dginv, trG, traceRev,
      ymStressB, higgsStressB, badSM, trivSMM, DiracStressForm.coord, DiracStressForm.frame]
  · funext ν
    by_cases hν : ν = 0
    · subst hν
      simp [ActualJetGauge.ymRes, ActualJetGauge.ymDiv, ActualJetGauge.dFm,
        ActualJetGauge.Fm, fieldStrength, badSM]
    · simp [ActualJetGauge.ymRes, ActualJetGauge.ymDiv, ActualJetGauge.dFm,
        ActualJetGauge.Fm, fieldStrength, badSM, hν]
  · simp [ActualJetGauge.higgsRes, ActualJetGauge.waveH, ActualJetGauge.dDH,
      ActualJetGauge.DH, chr, badSM, trivSMM]

theorem bad_dirF (x : ST 3) : dirF badSM bad x = 0 := Subsingleton.elim _ _

theorem bad_CF (x : ST 3) : CF bad x = 0 := by
  funext l
  simp [CF, ActualJetWriter.C, cUp, chr, bad_dg]

theorem bad_CF_fun : CF bad = fun _ => 0 := funext bad_CF

theorem one_ne_zero_matLie : (1 : MatLie 1) ≠ 0 := by
  intro h
  have h' : (1 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := h
  have := congrFun (congrFun h' 0) 0
  simp at this

theorem hgs_ne_zero {x : ST 3} (hx : x 0 ≠ 0) : hgs x ≠ 0 := by
  unfold hgs
  exact smul_ne_zero hx one_ne_zero_matLie

/-- **The state field of `bad` solves the independent symmetric system everywhere**: the only
non-vanishing residual is the normal (Gauss) component of the Yang–Mills residual, which does not
enter `eq:actual-jet-writer`'s evolution rows. -/
theorem bad_symEqAt (x : ST 3) : SymEqAt badSM bad x := by
  rw [symEqAt_iff]
  have hdD : ∀ j : Fin 3, pd (dirF badSM bad) j.succ x = 0 := fun _ => Subsingleton.elim _ _
  have hdC : ∀ α, pd (CF bad) α x = 0 := fun α => by rw [bad_CF_fun]; exact pd_const' _ α x
  unfold errF
  rw [bad_bosF, bad_dirF, bad_CF]
  simp only [hdD, hdC, map_zero, add_zero, Finset.sum_const_zero]
  ext <;> simp [BmL, toP, Bsys, bosR, ofR, recon, stressR, DiracStressForm.stressRes, badSM,
    trivSMM, traceRev, trG]

/-- The Gauss residual of `bad`: `e_0{}^0 r^A_0 = -N⁻¹ H`. -/
theorem bad_gaussF (x : ST 3) :
    gaussF badSM bad x = -((frameU (bad.gi x)).N⁻¹ • hgs x) := by
  unfold gaussF
  rw [bad_bosF]
  simp

/-- **Constraint propagation fails for the non-variational data `badSM`**: the actual-jet state
field of `bad` solves the independent symmetric system everywhere; on `{t = 0}` all physical
residuals and the harmonic defect vanish (constrained data); for every `t ≠ 0` the Gauss
constraint is violated. -/
theorem bad_obstruction : SMSmooth badSM ∧ (∀ x, SymEqAt badSM bad x) ∧
    (∀ x : ST 3, x 0 = 0 → bosF badSM bad x = 0 ∧ dirF badSM bad x = 0 ∧ CF bad x = 0) ∧
    ∀ x : ST 3, x 0 ≠ 0 → gaussF badSM bad x ≠ 0 := by
  refine ⟨badSM_smooth, bad_symEqAt, fun x hx => ⟨?_, bad_dirF x, bad_CF x⟩, fun x hx => ?_⟩
  · rw [bad_bosF]
    have : hgs x = 0 := by simp [hgs, hx]
    simp only [this, neg_zero, ite_self]
    rfl
  · rw [bad_gaussF, neg_ne_zero]
    exact smul_ne_zero (inv_ne_zero (frameU (bad.gi x)).N_pos.ne') (hgs_ne_zero hx)

/-- `bad` is not a physical solution on any slab `[0, t₁] × 𝕋³`, `t₁ > 0`. -/
theorem bad_not_physical {t₁ : ℝ} (ht₁ : 0 < t₁) : ¬ IsPhysicalOn badSM bad (slab 0 t₁) := by
  intro h
  set x : ST 3 := Fin.cons t₁ 0
  have hx : x ∈ slab 0 t₁ := ⟨by simp [x, ht₁.le], by simp [x]⟩
  have hG := bad_obstruction.2.2.2 x (by simp [x, ht₁.ne'])
  apply hG
  unfold gaussF
  rw [(h x hx).1]
  simp

/-- The metric block of the state of `bad` is the Minkowski block. -/
theorem bad_state_met (x : ST 3) : (stateF badSM bad x).1 = (minkInv, 0, 0) := by
  have h1 : (bad.jet x).FJ.dg = 0 := bad_dg x
  simp only [stateF, toP, ActualJet.state, h1]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext μ ν; simp [AdaptedFrame.pJ]
  · funext a μ ν; simp [AdaptedFrame.qJ]

theorem unitaryForms_bad : UnitaryForms badSM (frob 1) (frob 1)
    (0 : PUnit.{1} →ₗ[ℝ] PUnit.{1} →ₗ[ℝ] ℝ) (0 : PUnit.{1} →ₗ[ℝ] PUnit.{1} →ₗ[ℝ] ℝ) where
  symG := unitaryForms_triv.symG
  symV := unitaryForms_triv.symV
  symS := unitaryForms_triv.symS
  symS' := unitaryForms_triv.symS'
  posG := unitaryForms_triv.posG
  posV := unitaryForms_triv.posV
  posS := unitaryForms_triv.posS
  posS' := unitaryForms_triv.posS'
  c0 := unitaryForms_triv.c0
  ci := unitaryForms_triv.ci
  c0b := unitaryForms_triv.c0b
  cib := unitaryForms_triv.cib

/-- **A compact chart margin containing the states of `bad` on `(-1, 1) × 𝕋³`** (for any linear
coordinates `κ`). -/
theorem exists_margin_bad (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
    (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ)) :
    ∃ K : Set (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ), IsCompact K ∧
      (∀ v ∈ K, MetChart (κ.symm v).1) ∧ ∀ y ∈ openSlab (-1) 1, κ (stateF badSM bad y) ∈ K := by
  have hc : Continuous fun y => κ (stateF badSM bad y) :=
    (LinearMap.toContinuousLinearMap κ.toLinearMap).continuous.comp
      (contDiff_stateF badSM bad).continuous
  have hp : IsSPeriodic fun y => κ (stateF badSM bad y) := fun k x => by
    show κ (stateF badSM bad (x + sshift k)) = κ (stateF badSM bad x)
    rw [isSPeriodic_stateF badSM bad k x]
  obtain ⟨C, hC⟩ := KatoGalerkin.exists_bound_slab (a := -2) (b := 2) (t₀ := -1) (t₁ := 1)
    hc.continuousOn hp (by norm_num) (by norm_num)
  have hκc : Continuous κ.symm := (LinearMap.toContinuousLinearMap κ.symm.toLinearMap).continuous
  refine ⟨{v | (κ.symm v).1 = (minkInv, 0, 0)} ∩ Metric.closedBall 0 C, ?_, ?_, ?_⟩
  · exact (isCompact_closedBall 0 C).inter_left
      (isClosed_eq (continuous_fst.comp hκc) continuous_const)
  · intro v hv
    rw [hv.1]
    exact metChart_mink
  · intro y hy
    refine ⟨?_, ?_⟩
    · show (κ.symm (κ (stateF badSM bad y))).1 = _
      rw [LinearEquiv.symm_apply_apply, bad_state_met]
    · rw [mem_closedBall_zero_iff]
      exact hC y ⟨hy.1.le, hy.2.le⟩

/-- **The Kato solution of the constrained datum `𝒰(bad)(0)` is not physical**: with realized
symmetric coefficients agreeing with the actual-jet operators on a compact chart margin `K`
containing the states of `bad` on `(-1, 1) × 𝕋³`, every classical two-sided solution of the
realized system with this datum coincides with `𝒰(bad)` on `[0, t₁] × 𝕋³` (`t₁ < min(T, 1)`) and
therefore violates the Gauss law at every point with `t ∈ (0, t₁]`, although its datum satisfies
all physical identities at `t = 0`. -/
theorem kato_solution_not_physical
    {κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ)}
    {K : Set (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ)}
    {A : Fin 3 → Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
        (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ}
    {F : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (hAK : ∀ v ∈ K, ∀ j a (w : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ),
      ∑ b, A j a b v * w b = κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) badSM.D.Fr
        badSM.Db.Fr j (ofP (κ.symm w)))) a)
    (hFK : ∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys badSM (ofP (κ.symm v)))) a)
    (hK : ∀ y ∈ openSlab (-1) 1, κ (stateF badSM bad y) ∈ K)
    {T : ℝ} {U : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ST 3 → ℝ}
    {P : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → Fin 3 → ST 3 → ℝ}
    (hU : KatoGalerkin.TwoSidedSol A F (stU κ badSM bad) T U P) {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hT : t₁ < T) (h1 : t₁ < 1) :
    (∀ x ∈ slab 0 t₁, ∀ b, U b x = κ (stateF badSM bad x) b) ∧
      ∀ x ∈ slab 0 t₁, x 0 ≠ 0 → gaussF badSM bad x ≠ 0 :=
  ⟨KatoStab.twoSided_unique hA hsym hF hU
    (twoSided_of_symEq hAK hFK bad (fun y _ => bad_symEqAt y) hK) ht₁ hT h1,
    fun x _ hx => bad_obstruction.2.2.2 x hx⟩

/-- **Non-vacuity of `kato_solution_not_physical`**: the realized coefficients for `badSM` exist
(`actual_jet_kato_realization` with the Frobenius forms) on the margin of `exists_margin_bad`, and
`𝒰(bad)` itself is a two-sided solution of the realized system on `(-1, 1)`. -/
example : ∃ (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ))
    (A : Fin 3 → Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
        (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ)
    (F : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ),
    KatoGalerkin.TwoSidedSol A F (stU κ badSM bad) 1 (stU κ badSM bad) (stP κ badSM bad) ∧
      ∀ t₁, 0 < t₁ → t₁ < 1 → ∀ x ∈ slab 0 t₁, x 0 ≠ 0 → gaussF badSM bad x ≠ 0 := by
  obtain ⟨κ, -, h⟩ := actual_jet_kato_realization badSM_smooth unitaryForms_bad
  obtain ⟨K, hKc, hKch, hK⟩ := exists_margin_bad κ
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := h K hKc hKch
  have hsol := twoSided_of_symEq hAK hFK bad (ε := 1) (fun y _ => bad_symEqAt y) hK
  exact ⟨κ, A, F, hsol, fun t₁ ht₁ h1 =>
    (kato_solution_not_physical hA hsym hF hAK hFK hK hsol ht₁ h1 h1).2⟩

end RenewalGeometry.GenConstraintObs
