/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedGaugeDefectRows

/-!
# Propagation of the defining-jet identities: metric (two-sided) and Higgs sectors

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`), for solutions of the **shift-transported** actual-jet system
(`AJKatoMod.FsysM`, `AJKatoMod.princPM`): metric head row `∂_tg - βʲ∂_jg = Np`, Higgs head row
`∂_tH - βʲD_jH = NΠ`.

* `MSol` — a smooth periodic state field on `(a, b) × 𝕋³` in the chart, solving the modified
  system, whose head fields `(g, A_i, H, Ψ, Ψ̄)` are those of a smooth tuple `z`;
* **`metric_sector`** — if `q(W) = e_a(g)` on one slice then `(g, p, q)(W)` are the actual metric
  variables on the whole open slab (the `p`-block from the head row, the `q`-block by forward and
  backward transport, `GenDefJet` / `GenBackward.transport_unique_backward`);
* **`higgs_Pi`** — `Π(W) = D_{e_0}H` on the slab (immediate from the modified head row);
* **`higgs_sector`** — once the metric and gauge variables are actual, `Q(W) = D_{e_a}H` on the
  open slab if it holds on one slice (transport with the shift, both directions).
-/

open Filter Topology Set
open scoped BigOperators ContDiff NNReal

noncomputable section

namespace RenewalGeometry.GenHiggsDefect

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S')

/-- **A solution of the shift-transported system with the head fields of a tuple.** -/
structure MSol (W : ST 3 → StateP m V S S') (z : Tuple m V S S') (a b : ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ W (openSlab a b)
  per : IsSPeriodic W
  chart : ∀ y ∈ openSlab a b, MetChart (W y).1
  g : ∀ y ∈ openSlab a b, (W y).1.1 = z.g y
  A : ∀ y ∈ openSlab a b, ∀ i : Fin 3, (W y).2.1 i = z.A y i.succ
  H : ∀ y ∈ openSlab a b, (W y).2.2.2.2.1 = z.H y
  ψ : ∀ y ∈ openSlab a b, (W y).2.2.2.2.2.2.2.1 = z.ψ y
  ψb : ∀ y ∈ openSlab a b, (W y).2.2.2.2.2.2.2.2.2.1 = z.ψb y
  row : ∀ y ∈ openSlab a b, pd W 0 y + ∑ j : Fin 3, AJKatoMod.princPM SM (W y) j (pd W j.succ y) =
    toP (AJKatoMod.FsysM SM (ofP (W y)))

variable {SM}

/-- Two-sided propagation from forward and backward propagation. -/
theorem of_forward_backward {P : ST 3 → Prop} {a t₀ b : ℝ} (_ha : a < t₀) (hb : t₀ < b)
    (hf : ∀ t₁, t₀ < t₁ → t₁ < b → ∀ x ∈ slab t₀ t₁, P x)
    (hbk : ∀ t₁, a < t₁ → t₁ < t₀ → ∀ x ∈ slab t₁ t₀, P x) : ∀ x ∈ openSlab a b, P x := by
  intro x hx
  rcases le_or_gt t₀ (x 0) with h | h
  · obtain ⟨t₁, ht₁, ht₁b⟩ := exists_between (show max t₀ (x 0) < b from max_lt hb hx.2)
    exact hf t₁ ((le_max_left _ _).trans_lt ht₁) ht₁b x ⟨h, ((le_max_right _ _).trans ht₁.le)⟩
  · obtain ⟨t₁, ht₁a, ht₁⟩ := exists_between hx.1
    exact hbk t₁ ht₁a (ht₁.trans h) x ⟨ht₁.le, h.le⟩

theorem frameU_W {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b : ℝ}
    (hW : MSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) :
    frameU (ginvOf (W y).1.1) = frameU (z.gi y) := by
  rw [hW.g y hy]; rfl

/-- The metric head row of a solution of the modified system. -/
theorem MSol.row_g {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b : ℝ}
    (hW : MSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) (μ ν : Fin 4) :
    (pd W 0 y).1.1 μ ν - ∑ j : Fin 3, (frameU (z.gi y)).β j * (pd W j.succ y).1.1 μ ν =
      (frameU (z.gi y)).N * (W y).1.2.1 μ ν := by
  have h := congrArg (fun v : StateP m V S S' => v.1.1 μ ν) (hW.row y hy)
  simp only [Prod.fst_add, Prod.fst_sum, Finset.sum_apply, Pi.add_apply] at h
  have e1 : ∀ j : Fin 3, (AJKatoMod.princPM SM (W y) j (pd W j.succ y)).1.1 μ ν =
      -((frameU (ginvOf (W y).1.1)).β j * (pd W j.succ y).1.1 μ ν) := fun j => rfl
  have e2 : (toP (AJKatoMod.FsysM SM (ofP (W y)))).1.1 μ ν =
      (frameU (ginvOf (W y).1.1)).N * (W y).1.2.1 μ ν := rfl
  rw [e2] at h
  simp only [e1, Finset.sum_neg_distrib] at h
  rw [frameU_W hW hy] at h
  linarith

/-- The `q`-rows of a solution of the modified system (those of the original system). -/
theorem MSol.row_q {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b : ℝ}
    (hW : MSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) :
    (pd W 0 y).1.2.2 + ∑ j : Fin 3, (princL SM (W y) j (pd W j.succ y)).1.2.2 =
      (toP (Fsys SM (ofP (W y)))).1.2.2 := by
  have h := congrArg (fun v : StateP m V S S' => v.1.2.2) (hW.row y hy)
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum] at h
  exact h

/-- **The metric sector**: the metric variables of `W` are the actual ones on the whole open
slab, provided `q(W)` is actual on one slice. -/
theorem metric_sector (hS : SMSmooth SM) {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
    {a t₀ b : ℝ} (ha : a < t₀) (hb : t₀ < b) (hW : MSol SM W z a b)
    (hq0 : ∀ y : Fin 3 → ℝ, (W (Fin.cons t₀ y)).1.2.2 = (stateF SM z (Fin.cons t₀ y)).1.2.2) :
    ∀ x ∈ openSlab a b, (W x).1 = (stateF SM z x).1 := by
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := hW.smooth.of_le (by norm_cast)
  have hp := GenDefJet.metric_p_block SM hW1 hW.g (fun y hy μ ν => hW.row_g hy μ ν)
  have hq : ∀ x ∈ openSlab a b, (W x).1.2.2 = (stateF SM z x).1.2.2 := by
    refine of_forward_backward ha hb (fun t₁ h01 h1b => ?_) (fun t₁ ha1 h10 => ?_)
    · exact (GenDefJet.metric_defect_propagation SM hS ha h01 h1b hW1 hW.per hW.g
        (fun y hy μ ν => hW.row_g hy μ ν) (fun y hy => hW.row_q hy) hq0).2
    · -- backward: the transport equation of the `q`-defect, reversed in time
      have hpdp := GenDefJet.metric_pd_p_block SM hW1 hp
      obtain ⟨L, hL⟩ := GenDefJet.forcing_lip_q SM hS ha1 hb hW1 hW.per hW.g
      have heq : ∀ x ∈ slab t₁ t₀, ‖∑ μ, GenDefJet.shiftCoef z μ x •
          pd (GenDefJet.qDefect W (stateF SM z)) μ x‖ ≤
          max L 0 * ‖GenDefJet.qDefect W (stateF SM z) x‖ := by
        intro x hx
        have hxO : x ∈ openSlab a b := slab_subset_openSlab ha1 hb hx
        have hdW : DifferentiableAt ℝ W x :=
          GenHarmonic.diffAt_of_contDiffOn (isOpen_openSlab a b) hW1 one_ne_zero hxO
        have hdU : DifferentiableAt ℝ (stateF SM z) x :=
          (contDiff_stateF SM z).differentiable (by simp) x
        have hrow := GenDefJet.q_row_difference SM z (W x) (fun μ => pd W μ x) x (hW.g x hxO)
          (fun j => hpdp x hxO j.succ) (hW.row_q hxO)
        have hsum : ∑ μ, GenDefJet.shiftCoef z μ x •
            pd (GenDefJet.qDefect W (stateF SM z)) μ x =
            GenDefJet.qC ((toP (Fsys SM (ofP (W x)))).1.2.2 -
              (toP (Fsys SM (ofP (stateF SM z x)))).1.2.2) := by
          rw [Fin.sum_univ_succ, ← hrow, map_add, map_sum]
          simp only [GenDefJet.pd_qDefect hdW hdU, map_smul, GenDefJet.shiftCoef_zero, one_smul]
        rw [hsum, GenDefJet.norm_qC]
        have hd := GenDefJet.norm_diff_q (W x) (stateF SM z x)
          (by rw [hW.g x hxO, GenDefJet.stateF_fst_fst]) (hp x hxO)
        calc _ ≤ L * ‖W x - ((stateF SM z x).1, (W x).2)‖ := hL x hx
          _ ≤ max L 0 * ‖W x - ((stateF SM z x).1, (W x).2)‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
          _ ≤ max L 0 * ‖GenDefJet.qDefect W (stateF SM z) x‖ :=
              mul_le_mul_of_nonneg_left hd (le_max_right _ _)
      have h0 : ∀ y : Fin 3 → ℝ, GenDefJet.qDefect W (stateF SM z) (Fin.cons t₀ y) = 0 := by
        intro y
        unfold GenDefJet.qDefect
        rw [map_sub, GenDefJet.prQ_apply, GenDefJet.prQ_apply, hq0 y, sub_self, map_zero]
      have hzero := GenBackward.transport_unique_backward (N := Fin 3 × Fin 4 × Fin 4)
        (c := GenDefJet.shiftCoef z) ha1 h10 hb
        (GenDefJet.contDiffOn_qDefect hW1 ((contDiff_stateF SM z).of_le (by norm_cast)).contDiffOn)
        (GenDefJet.isSPeriodic_qDefect hW.per (isSPeriodic_stateF SM z))
        (fun μ => (GenDefJet.contDiff_shiftCoef z μ).contDiffOn) (GenDefJet.isSPeriodic_shiftCoef z)
        one_pos (fun x _ => (GenDefJet.shiftCoef_zero z x).ge) (le_max_right L 0) heq h0
      intro x hx
      have h1 := GenDefJet.qC_eq_zero (hzero x hx)
      rw [map_sub, GenDefJet.prQ_apply, GenDefJet.prQ_apply] at h1
      exact sub_eq_zero.1 h1
  intro x hx
  have hg : (W x).1.1 = (stateF SM z x).1.1 := by rw [hW.g x hx, GenDefJet.stateF_fst_fst]
  exact Prod.ext hg (Prod.ext (hp x hx) (hq x hx))

/-! ### Block projections -/

section Blocks

/-- A linear block of two fields which agree on an open set has agreeing partial derivatives. -/
theorem pd_block_eq' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W U : ST 3 → StateP m V S S'} {O : Set (ST 3)} (hO : IsOpen O) (hW : ContDiffOn ℝ 1 W O)
    (hU : DifferentiableOn ℝ U O) (Lm : StateP m V S S' →L[ℝ] F)
    (h0 : ∀ y ∈ O, Lm (W y) = Lm (U y)) : ∀ x ∈ O, ∀ γ, Lm (pd W γ x) = Lm (pd U γ x) := by
  intro x hx γ
  have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW one_ne_zero hx
  have hdU : DifferentiableAt ℝ U x := (hU x hx).differentiableAt (hO.mem_nhds hx)
  have ev : (fun y => Lm (W y - U y)) =ᶠ[𝓝 x] 0 :=
    Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => by
      show Lm (W y - U y) = 0
      rw [map_sub, h0 y hy, sub_self]
  have h1 := pd_eq_zero_of_eventually ev γ
  rw [GenHarmonic.pd_clm Lm (hdW.fun_sub hdU) γ, GenDefJet.pd_sub_eq hdW hdU, map_sub,
    sub_eq_zero] at h1
  exact h1

variable (m V S S') in
/-- The Higgs block of a state. -/
def prH : StateP m V S S' →L[ℝ] V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v.2.2.2.2.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

variable (m V S S') in
/-- The Higgs momentum block of a state. -/
def prPm : StateP m V S S' →L[ℝ] V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v.2.2.2.2.2.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

variable (m V S S') in
/-- The Higgs tangential block of a state. -/
def prQh : StateP m V S S' →L[ℝ] (Fin 3 → V) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v.2.2.2.2.2.2.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem prH_apply (v : StateP m V S S') : prH m V S S' v = v.2.2.2.2.1 := rfl
theorem prPm_apply (v : StateP m V S S') : prPm m V S S' v = v.2.2.2.2.2.1 := rfl
theorem prQh_apply (v : StateP m V S S') : prQh m V S S' v = v.2.2.2.2.2.2.1 := rfl

end Blocks

/-! ### The Higgs sector -/

section Higgs

/-- The modified Higgs head row of a solution of the modified system. -/
theorem MSol.row_H {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b : ℝ}
    (hW : MSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) :
    (pd W 0 y).2.2.2.2.1 - ∑ j : Fin 3, (frameU (z.gi y)).β j • (pd W j.succ y).2.2.2.2.1 =
      (frameU (z.gi y)).N • (W y).2.2.2.2.2.1 +
        ∑ j : Fin 3, (frameU (z.gi y)).β j • ⁅(W y).2.1 j, (W y).2.2.2.2.1⁆ := by
  have h := congrArg (fun v : StateP m V S S' => v.2.2.2.2.1) (hW.row y hy)
  simp only [Prod.snd_add, Prod.fst_add, Prod.snd_sum, Prod.fst_sum] at h
  have e1 : ∀ j : Fin 3, (AJKatoMod.princPM SM (W y) j (pd W j.succ y)).2.2.2.2.1 =
      -((frameU (ginvOf (W y).1.1)).β j • (pd W j.succ y).2.2.2.2.1) := fun j => rfl
  have e2 : (toP (AJKatoMod.FsysM SM (ofP (W y)))).2.2.2.2.1 =
      (frameU (ginvOf (W y).1.1)).N • (W y).2.2.2.2.2.1 +
        ∑ j : Fin 3, (frameU (ginvOf (W y).1.1)).β j • ⁅(W y).2.1 j, (W y).2.2.2.2.1⁆ := rfl
  rw [e2] at h
  simp only [e1, Finset.sum_neg_distrib] at h
  rw [frameU_W hW hy] at h
  rw [← h]; abel

/-- **The Higgs momentum is actual**: `Π(W) = D_{e_0}H` on the slab (modified head row). -/
theorem higgs_Pi {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b : ℝ}
    (hW : MSol SM W z a b) : ∀ x ∈ openSlab a b,
      (W x).2.2.2.2.2.1 = (stateF SM z x).2.2.2.2.2.1 := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := hW.smooth.of_le (by norm_cast)
  have hpdH := pd_block_eq' hO hW1 ((contDiff_stateF SM z).differentiable (by simp)).differentiableOn
    (prH m V S S') (fun y hy => by rw [prH_apply, prH_apply, hW.H y hy]; rfl)
  intro x hx
  have h1 := hW.row_H hx
  have h2 := AJKatoMod.higgs_head_row_actual (SM := SM) z x
  have e : ∀ γ, (pd W γ x).2.2.2.2.1 = (pd (stateF SM z) γ x).2.2.2.2.1 := fun γ => hpdH x hx γ
  simp only [e] at h1
  have hA : ∀ j : Fin 3, (W x).2.1 j = (stateF SM z x).2.1 j := fun j => hW.A x hx j
  have hH : (W x).2.2.2.2.1 = (stateF SM z x).2.2.2.2.1 := hW.H x hx
  simp only [hA, hH] at h1
  have h3 : (frameU (z.gi x)).N • (W x).2.2.2.2.2.1 =
      (frameU (z.gi x)).N • (stateF SM z x).2.2.2.2.2.1 := by
    have := h1.symm.trans h2
    exact add_right_cancel this
  exact smul_right_injective V (frameU (z.gi x)).N_pos.ne' h3

end Higgs

/-! ### The tangential Higgs defect -/

section HiggsQ

/-- The actual-jet state satisfies the `Q`-rows exactly (no residual forcing in the `Q`-block). -/
theorem writer_Q_row (z : Tuple m V S S') (x : ST 3) :
    (pd (stateF SM z) 0 x).2.2.2.2.2.2.1 +
        ∑ j : Fin 3, (princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x)).2.2.2.2.2.2.1 =
      (toP (Fsys SM (ofP (stateF SM z x)))).2.2.2.2.2.2.1 := by
  have h := writer_pde_err SM z x
  have h0 : (errF SM z x).2.2.2.2.2.2.1 = 0 := by
    simp [errF, BmL, DmL, QmL, GcL, GdL, toP, Bsys, Qsys, pState, Prod.fst_sum, Prod.snd_sum]
    funext a
    simp
  have := congrArg (fun U : StateP m V S S' => U.2.2.2.2.2.2.1) h
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum] at this
  rw [this, h0, add_zero]

/-- The `Q`-rows of a solution of the modified system. -/
theorem MSol.row_Q {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b : ℝ}
    (hW : MSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) :
    (pd W 0 y).2.2.2.2.2.2.1 + ∑ j : Fin 3, (princL SM (W y) j (pd W j.succ y)).2.2.2.2.2.2.1 =
      (toP (Fsys SM (ofP (W y)))).2.2.2.2.2.2.1 := by
  have h := congrArg (fun v : StateP m V S S' => v.2.2.2.2.2.2.1) (hW.row y hy)
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum] at h
  exact h

/-- The state with its tangential Higgs block replaced. -/
def replQ (v : StateP m V S S') (Q' : Fin 3 → V) : StateP m V S S' :=
  (v.1, (v.2.1, (v.2.2.1, (v.2.2.2.1, (v.2.2.2.2.1, (v.2.2.2.2.2.1, (Q', v.2.2.2.2.2.2.2)))))))

/-- The `Q`-forcing depends only on the bosonic blocks of the state. -/
theorem FsysQ_congr {v w : StateP m V S S'} (h1 : v.1 = w.1) (hA : v.2.1 = w.2.1)
    (hE : v.2.2.1 = w.2.2.1) (hB : v.2.2.2.1 = w.2.2.2.1) (hH : v.2.2.2.2.1 = w.2.2.2.2.1)
    (hP : v.2.2.2.2.2.1 = w.2.2.2.2.2.1) (hQ : v.2.2.2.2.2.2.1 = w.2.2.2.2.2.2.1) :
    (toP (Fsys SM (ofP v))).2.2.2.2.2.2.1 = (toP (Fsys SM (ofP w))).2.2.2.2.2.2.1 := by
  obtain ⟨v1, vA, vE, vB, vH, vP, vQ, vrest⟩ := v
  obtain ⟨w1, wA, wE, wB, wH, wP, wQ, wrest⟩ := w
  simp only at h1 hA hE hB hH hP hQ
  subst h1 hA hE hB hH hP hQ
  rfl

theorem norm_sub_replQ (v : StateP m V S S') (Q' : Fin 3 → V) :
    ‖v - replQ v Q'‖ ≤ ‖v.2.2.2.2.2.2.1 - Q'‖ := by
  obtain ⟨v1, vA, vE, vB, vH, vP, vQ, vrest⟩ := v
  simp [replQ, Prod.norm_def]

/-- Real coordinates of `(Fin 3 → V)`. -/
def coordQ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    (Fin 3 → V) ≃ₗ[ℝ] (Fin 3 × Fin (Module.finrank ℝ V) → ℝ) :=
  (LinearEquiv.piCongrRight fun _ : Fin 3 => (Module.finBasis ℝ V).equivFun).trans
    (LinearEquiv.curry ℝ ℝ (Fin 3) (Fin (Module.finrank ℝ V))).symm

/-- Complex coordinates of `(Fin 3 → V)`. -/
def cQ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    (Fin 3 → V) →L[ℝ] (Fin 3 × Fin (Module.finrank ℝ V) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w p => ((coordQ V w p : ℝ) : ℂ)
      map_add' := fun w w' => by funext p; simp
      map_smul' := fun c w => by funext p; simp }

theorem norm_cQ (w : Fin 3 → V) : ‖cQ V w‖ = ‖coordQ V w‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_)
  · show ‖((coordQ V w p : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real]; exact norm_le_pi_norm _ p
  · have := norm_le_pi_norm (cQ V w) p
    show ‖coordQ V w p‖ ≤ _
    rwa [show cQ V w p = ((coordQ V w p : ℝ) : ℂ) from rfl, Complex.norm_real] at this

theorem exists_le_cQ : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Fin 3 → V, ‖w‖ ≤ C * ‖cQ V w‖ := by
  set e := (coordQ V).toContinuousLinearEquiv with he
  refine ⟨‖(e.symm : (Fin 3 × Fin (Module.finrank ℝ V) → ℝ) →L[ℝ] (Fin 3 → V))‖, norm_nonneg _,
    fun w => ?_⟩
  rw [norm_cQ]
  have h := (e.symm : (Fin 3 × Fin (Module.finrank ℝ V) → ℝ) →L[ℝ] (Fin 3 → V)).le_opNorm
    (coordQ V w)
  have e1 : (e.symm : (Fin 3 × Fin (Module.finrank ℝ V) → ℝ) →L[ℝ] (Fin 3 → V)) (coordQ V w) = w :=
    (coordQ V).symm_apply_apply w
  rw [e1] at h
  exact h

theorem cQ_eq_zero {w : Fin 3 → V} (h : cQ V w = 0) : w = 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_le_cQ (V := V)
  have := hC w
  rw [h, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- **The Higgs sector**: once the metric and gauge variables of `W` are actual on the open slab,
`Q(W) = D_{e_a}H` on the open slab if it holds on one slice. -/
theorem higgs_sector (hS : SMSmooth SM) {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
    {a t₀ b : ℝ} (ha : a < t₀) (hb : t₀ < b) (hW : MSol SM W z a b)
    (hmet : ∀ x ∈ openSlab a b, (W x).1 = (stateF SM z x).1)
    (hEB : ∀ x ∈ openSlab a b, (W x).2.2.1 = (stateF SM z x).2.2.1 ∧
      (W x).2.2.2.1 = (stateF SM z x).2.2.2.1)
    (hQ0 : ∀ y : Fin 3 → ℝ, (W (Fin.cons t₀ y)).2.2.2.2.2.2.1 =
      (stateF SM z (Fin.cons t₀ y)).2.2.2.2.2.2.1) :
    ∀ x ∈ openSlab a b, (W x).2.2.2.2.2.2.1 = (stateF SM z x).2.2.2.2.2.2.1 := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := hW.smooth.of_le (by norm_cast)
  set U := stateF SM z with hU
  have hUs : ContDiff ℝ ∞ U := contDiff_stateF SM z
  have hPi := higgs_Pi hW
  have hpdPm := pd_block_eq' hO hW1 (hUs.differentiable (by simp)).differentiableOn
    (prPm m V S S') (fun y hy => by rw [prPm_apply, prPm_apply, hPi y hy])
  -- the defect and its transport equation
  set dQ : ST 3 → (Fin 3 → V) := fun x => (W x).2.2.2.2.2.2.1 - (U x).2.2.2.2.2.2.1 with hdQ
  have hdQs : ContDiffOn ℝ 1 dQ (openSlab a b) :=
    ((prQh m V S S').contDiff.comp_contDiffOn hW1).sub
      ((prQh m V S S').contDiff.comp (hUs.of_le (by norm_cast))).contDiffOn
  have hdQp : IsSPeriodic dQ := fun q x => by
    simp only [hdQ, hW.per q x]
    rw [show U (x + sshift q) = U x from isSPeriodic_stateF SM z q x]
  have hpd_dQ : ∀ x ∈ openSlab a b, ∀ μ, pd dQ μ x =
      (pd W μ x).2.2.2.2.2.2.1 - (pd U μ x).2.2.2.2.2.2.1 := by
    intro x hx μ
    have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW1 one_ne_zero hx
    have hdU : DifferentiableAt ℝ U x := hUs.differentiable (by simp) x
    have e : dQ = fun y => prQh m V S S' (W y - U y) := by
      funext y; simp only [hdQ, map_sub, prQh_apply]
    rw [e, GenHarmonic.pd_clm (prQh m V S S') (hdW.fun_sub hdU) μ, GenDefJet.pd_sub_eq hdW hdU,
      map_sub]
    rfl
  -- the forcing difference
  have hlip : ∀ t₁ t₂, a < t₁ → t₂ < b → ∃ L, ∀ x ∈ slab t₁ t₂,
      ‖(toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.1 - (toP (Fsys SM (ofP (U x)))).2.2.2.2.2.2.1‖ ≤
        L * ‖dQ x‖ := by
    intro t₁ t₂ h1 h2
    set Φ : StateP m V S S' → (Fin 3 → V) := fun v => (toP (Fsys SM (ofP v))).2.2.2.2.2.2.1
      with hΦ
    have hΦc : ContDiffOn ℝ 1 Φ (chartSet (m := m) (V := V) (S := S) (S' := S')) := fun v hv =>
      ((((prQh m V S S').contDiff.contDiffAt.comp v (contDiffAt_Fsys_state hS hv)).of_le
        (by norm_cast))).contDiffWithinAt
    set u : ST 3 → StateP m V S S' := fun x => replQ (W x) ((U x).2.2.2.2.2.2.1) with hu
    have huc : ContinuousOn u (openSlab a b) := by
      have h1c : ContinuousOn W (openSlab a b) := hW1.continuousOn
      have h2c : Continuous fun x => (U x).2.2.2.2.2.2.1 :=
        (prQh m V S S').continuous.comp hUs.continuous
      have hrc : Continuous (fun p : StateP m V S S' × (Fin 3 → V) => replQ p.1 p.2) := by
        unfold replQ; fun_prop
      exact hrc.comp_continuousOn (h1c.prodMk h2c.continuousOn)
    have hup : IsSPeriodic u := fun q x => by
      simp only [hu, hW.per q x]
      rw [show U (x + sshift q) = U x from isSPeriodic_stateF SM z q x]
    have hseg : ∀ x ∈ openSlab a b, ∀ s ∈ Icc (0 : ℝ) 1,
        u x + s • (W x - u x) ∈ chartSet (m := m) (V := V) (S := S) (S' := S') := by
      intro x hx s _
      have hfst : (u x + s • (W x - u x)).1 = (W x).1 := by
        simp only [hu, replQ, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, sub_self, smul_zero,
          add_zero]
      show MetChart (u x + s • (W x - u x)).1
      rw [hfst]; exact hW.chart x hx
    obtain ⟨L, hL⟩ := GenDefJet.lip_slab isOpen_chartSet hΦc h1 h2 huc hW1.continuousOn hup
      hW.per hseg
    refine ⟨max L 0, fun x hx => ?_⟩
    have hxO : x ∈ openSlab a b := slab_subset_openSlab h1 h2 hx
    have hΦu : Φ (u x) = Φ (U x) := FsysQ_congr (hmet x hxO)
      (by funext i; exact hW.A x hxO i) (hEB x hxO).1 (hEB x hxO).2 (hW.H x hxO) (hPi x hxO) rfl
    have h := hL x hx
    rw [hΦu] at h
    calc ‖Φ (W x) - Φ (U x)‖ ≤ L * ‖W x - u x‖ := h
      _ ≤ max L 0 * ‖W x - u x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max L 0 * ‖dQ x‖ := mul_le_mul_of_nonneg_left (norm_sub_replQ (W x) _) (le_max_right _ _)
  -- the transport identity
  have hgW : ∀ x ∈ openSlab a b, frameU (ginvOf (W x).1.1) = frameU (z.gi x) := fun x hx =>
    frameU_W hW hx
  have hgU : ∀ x, frameU (ginvOf (U x).1.1) = frameU (z.gi x) := fun x => by
    rw [GenDefJet.stateF_fst_fst]; rfl
  have htr : ∀ x ∈ openSlab a b, ∑ μ, GenDefJet.shiftCoef z μ x • pd dQ μ x =
      (toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.1 - (toP (Fsys SM (ofP (U x)))).2.2.2.2.2.2.1 := by
    intro x hx
    rw [← hW.row_Q hx, ← writer_Q_row z x, Fin.sum_univ_succ, GenDefJet.shiftCoef_zero, one_smul]
    simp only [hpd_dQ x hx]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      GenDefJet.shiftCoef_eq_neg_beta]
    have ePW : ∀ j : Fin 3, (princL SM (W x) j (pd W j.succ x)).2.2.2.2.2.2.1 i =
        -((frameU (ginvOf (W x).1.1)).β j • (pd W j.succ x).2.2.2.2.2.2.1 i) -
          (frameU (ginvOf (W x).1.1)).N • ((frameU (ginvOf (W x).1.1)).E i j •
            (pd W j.succ x).2.2.2.2.2.1) := fun j => rfl
    have ePU : ∀ j : Fin 3, (princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x)).2.2.2.2.2.2.1 i
        = -((frameU (ginvOf (stateF SM z x).1.1)).β j • (pd (stateF SM z) j.succ x).2.2.2.2.2.2.1 i) -
          (frameU (ginvOf (stateF SM z x).1.1)).N • ((frameU (ginvOf (stateF SM z x).1.1)).E i j •
            (pd (stateF SM z) j.succ x).2.2.2.2.2.1) := fun j => rfl
    have hgU' : frameU (ginvOf (stateF SM z x).1.1) = frameU (z.gi x) := hgU x
    simp only [ePW, ePU, hgW x hx, hgU']
    have hPm : ∀ j : Fin 3, (pd W j.succ x).2.2.2.2.2.1 =
        (pd (stateF SM z) j.succ x).2.2.2.2.2.1 := fun j => hpdPm x hx j.succ
    simp only [hPm, smul_sub, neg_smul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    module
  -- complex coordinates and the transport uniqueness
  obtain ⟨C, hC0, hC⟩ := exists_le_cQ (V := V)
  set w : ST 3 → Fin 3 × Fin (Module.finrank ℝ V) → ℂ := fun x => cQ V (dQ x) with hw
  have hws : ContDiffOn ℝ 1 w (openSlab a b) := (cQ V).contDiff.comp_contDiffOn hdQs
  have hwp : IsSPeriodic w := fun q x => by simp only [hw, hdQp q x]
  have hbound : ∀ t₁ t₂, a < t₁ → t₂ < b → ∃ K, 0 ≤ K ∧ ∀ x ∈ slab t₁ t₂,
      ‖∑ μ, GenDefJet.shiftCoef z μ x • pd w μ x‖ ≤ K * ‖w x‖ := by
    intro t₁ t₂ h1 h2
    obtain ⟨L, hL⟩ := hlip t₁ t₂ h1 h2
    refine ⟨‖cQ V‖ * max L 0 * C, by positivity, fun x hx => ?_⟩
    have hxO : x ∈ openSlab a b := slab_subset_openSlab h1 h2 hx
    have hd : DifferentiableAt ℝ dQ x := GenHarmonic.diffAt_of_contDiffOn hO hdQs one_ne_zero hxO
    have e : ∑ μ, GenDefJet.shiftCoef z μ x • pd w μ x =
        cQ V (∑ μ, GenDefJet.shiftCoef z μ x • pd dQ μ x) := by
      simp only [hw, GenHarmonic.pd_clm (cQ V) hd, map_sum, map_smul]
    rw [e, htr x hxO]
    calc ‖cQ V _‖ ≤ ‖cQ V‖ * ‖(toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.1 -
          (toP (Fsys SM (ofP (U x)))).2.2.2.2.2.2.1‖ := (cQ V).le_opNorm _
      _ ≤ ‖cQ V‖ * (max L 0 * ‖dQ x‖) :=
          mul_le_mul_of_nonneg_left ((hL x hx).trans (mul_le_mul_of_nonneg_right
            (le_max_left _ _) (norm_nonneg _))) (norm_nonneg _)
      _ ≤ ‖cQ V‖ * (max L 0 * (C * ‖w x‖)) := by
          gcongr; exact hC (dQ x)
      _ = ‖cQ V‖ * max L 0 * C * ‖w x‖ := by ring
  have h0 : ∀ y : Fin 3 → ℝ, w (Fin.cons t₀ y) = 0 := by
    intro y
    simp only [hw, hdQ, hQ0 y, sub_self, map_zero]
  have hz : ∀ x ∈ openSlab a b, w x = 0 := by
    refine of_forward_backward ha hb (fun t₁ h01 h1b => ?_) (fun t₁ ha1 h10 => ?_)
    · obtain ⟨K, hK0, hK⟩ := hbound t₀ t₁ ha h1b
      exact GenGauss.transport_unique (N := Fin 3 × Fin (Module.finrank ℝ V))
        (c := GenDefJet.shiftCoef z) ha h01 h1b hws hwp
        (fun μ => (GenDefJet.contDiff_shiftCoef z μ).contDiffOn)
        (GenDefJet.isSPeriodic_shiftCoef z) one_pos
        (fun x _ => (GenDefJet.shiftCoef_zero z x).ge) hK0 hK h0
    · obtain ⟨K, hK0, hK⟩ := hbound t₁ t₀ ha1 hb
      exact GenBackward.transport_unique_backward (N := Fin 3 × Fin (Module.finrank ℝ V))
        (c := GenDefJet.shiftCoef z) ha1 h10 hb hws hwp
        (fun μ => (GenDefJet.contDiff_shiftCoef z μ).contDiffOn)
        (GenDefJet.isSPeriodic_shiftCoef z) one_pos
        (fun x _ => (GenDefJet.shiftCoef_zero z x).ge) hK0 hK h0
  intro x hx
  exact sub_eq_zero.1 (cQ_eq_zero (hz x hx))

end HiggsQ

end RenewalGeometry.GenHiggsDefect
