/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedHarmonicPropagation
import RenewalGeometry.Continuum.ActualJetKatoRealization
import RenewalGeometry.Continuum.SlabLocalTuples

/-!
# Propagation of the defining-jet identities: the metric sector

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`): a solution `W` of the independent symmetric system is the actual-jet
state of its head fields only if the auxiliary variables `(p, q, E, B, Π, Q, X, X̄)` coincide with
the frame derivatives of the head (`U = 𝒰(head U)`).

## The obstruction of the actual-jet system and the shift-transport modification

The head row of the metric in `prop:actual-jet-writer` is algebraic, `∂_tg = Np + βʲ∂̃_jg` with
the spatial derivatives `∂̃_jg` *reconstructed from `q`*.  For the defect `δ_j = ∂_jg - ∂̃_jg` this
gives `∂_tδ_j = β^k(∂_kδ_j - ∂_jδ_k) + (lower order)`, whose principal symbol
`(β·ξ)1 - ξ⊗β` is not diagonalisable where `β·ξ = 0` (a Jordan block): the defect system of the
actual-jet system is only weakly hyperbolic when the shift does not vanish, and the
symmetric-hyperbolic energy method does not propagate the defining-jet identities.  Replacing the
metric head row by the **shift-transported** row `∂_tg - βʲ∂_jg = Np` (`p` is then exactly
`e_0(g)`; the two rows agree on actual-jet states, `metric_head_row_actual`) makes the defect a
transport equation.

## Main results (generic in the theory data)

* `lip_on_segments`, `lip_slab` — a `C¹` map is uniformly Lipschitz along a compact family of segments in
  the open set where it is `C¹`;
* `metric_head_row_actual` — the actual-jet state of a smooth tuple satisfies the
  shift-transported head row `∂_tg - βʲ∂_jg = Np`;
* `writer_q_row` — it satisfies the `q`-rows of the symmetric system exactly (no residual
  forcing in the `q`-block);
* `metric_p_block`, `forcing_lip_q`, `q_row_difference` — the `p`-block identity, the uniform
  Lipschitz bound of the `q`-forcing, and the shift transport `∑ c^μ ∂_μ δq = F(W) - F(𝒰)` of the
  `q`-defect `δq` (`c = (1, -β)`, `shiftCoef`);
* **`metric_defect_propagation`** — let `W` be a `C¹` periodic state field on `(a, b) × 𝕋³` whose
  metric is the metric of a smooth tuple `z`, satisfying the shift-transported head row and the
  `q`-rows of the symmetric system.  Then `p(W) = e_0(g)` on the slab, and if `q(W) = e_a(g)` at
  `t₀`, then `q(W) = e_a(g)` on `[t₀, t₁] × 𝕋³`: the metric auxiliary variables of `W` are the
  actual frame derivatives of its metric (transport uniqueness `GenGauss.transport_unique`).

Not proved here (recorded in the ledger notes): the gauge sector (the magnetic defect obeys an
induction-type equation which closes only together with the magnetic Gauss constraint, via the
Bianchi identity of the reconstructed field strength), the Higgs sector (which needs the gauge
sector), the Kato realization of the shift-transported system and the smoothness of its solutions.
-/

open Filter Topology Set
open scoped BigOperators ContDiff NNReal

noncomputable section

namespace RenewalGeometry.GenDefJet

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Uniform Lipschitz bounds along compact families of segments -/

section Lip

/-- A `C¹` map is uniformly Lipschitz along every segment contained in a compact subset of the open
set where it is `C¹`. -/
theorem lip_on_segments {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F} {O : Set E} (hO : IsOpen O)
    (hΦ : ContDiffOn ℝ 1 Φ O) {C : Set E} (hC : IsCompact C) (hCO : C ⊆ O) :
    ∃ L, ∀ u v, segment ℝ u v ⊆ C → ‖Φ v - Φ u‖ ≤ L * ‖v - u‖ := by
  have hcont : ContinuousOn (fderiv ℝ Φ) O := hΦ.continuousOn_fderiv_of_isOpen hO le_rfl
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn (hcont.mono hCO)
  refine ⟨L, fun u v hseg => ?_⟩
  have hdiff : ∀ w ∈ segment ℝ u v, DifferentiableAt ℝ Φ w := fun w hw =>
    (hΦ.differentiableOn one_ne_zero w (hCO (hseg hw))).differentiableAt
      (hO.mem_nhds (hCO (hseg hw)))
  exact (convex_segment u v).norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun w hw => hL w (hseg hw)) (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)

/-- **Uniform Lipschitz bound on a slab**: for continuous periodic fields `u, v` on `(a, b) × 𝕋³`
whose connecting segments lie in the open set where `Φ` is `C¹`,
`‖Φ(v) - Φ(u)‖ ≤ L‖v - u‖` on every closed sub-slab. -/
theorem lip_slab {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F} {O : Set E} (hO : IsOpen O)
    (hΦ : ContDiffOn ℝ 1 Φ O) {u v : ST 3 → E} {a t₀ t₁ b : ℝ} (ha : a < t₀) (hb : t₁ < b)
    (hu : ContinuousOn u (openSlab a b)) (hv : ContinuousOn v (openSlab a b))
    (hup : IsSPeriodic u) (hvp : IsSPeriodic v)
    (hseg : ∀ x ∈ openSlab a b, ∀ s ∈ Icc (0 : ℝ) 1, u x + s • (v x - u x) ∈ O) :
    ∃ L, ∀ x ∈ slab t₀ t₁, ‖Φ (v x) - Φ (u x)‖ ≤ L * ‖v x - u x‖ := by
  set P : Set (ℝ × (Fin 3 → ℝ) × ℝ) := Icc t₀ t₁ ×ˢ Icc (0 : Fin 3 → ℝ) 1 ×ˢ Icc (0 : ℝ) 1 with hP
  set f : ℝ × (Fin 3 → ℝ) × ℝ → E := fun p =>
    u (Fin.cons p.1 p.2.1) + p.2.2 • (v (Fin.cons p.1 p.2.1) - u (Fin.cons p.1 p.2.1)) with hf
  have hPc : IsCompact P := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hmem : ∀ p ∈ P, (Fin.cons p.1 p.2.1 : ST 3) ∈ openSlab a b := fun p hp =>
    ⟨by have := hp.1.1; show a < p.1; linarith, by have := hp.1.2; show p.1 < b; linarith⟩
  have hcons : Continuous fun p : ℝ × (Fin 3 → ℝ) × ℝ => (Fin.cons p.1 p.2.1 : ST 3) :=
    continuous_cons2.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hfc : ContinuousOn f P := by
    have hu' : ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) × ℝ => u (Fin.cons p.1 p.2.1)) P :=
      hu.comp hcons.continuousOn fun p hp => hmem p hp
    have hv' : ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) × ℝ => v (Fin.cons p.1 p.2.1)) P :=
      hv.comp hcons.continuousOn fun p hp => hmem p hp
    exact hu'.add ((continuous_snd.comp continuous_snd).continuousOn.smul (hv'.sub hu'))
  set C := f '' P with hC
  have hCc : IsCompact C := hPc.image_of_continuousOn hfc
  have hCO : C ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact hseg _ (hmem p hp) p.2.2 hp.2.2
  obtain ⟨L, hL⟩ := lip_on_segments hO hΦ hCc hCO
  refine ⟨L, fun x hx => ?_⟩
  -- reduce to the fundamental cube
  set y' : Fin 3 → ℝ := fun i => Int.fract (Fin.tail x i) with hy'
  have hper : ∀ {w : ST 3 → E}, IsSPeriodic w → w x = w (Fin.cons (x 0) y') := by
    intro w hw
    have h := (hw.slice (x 0)).apply_fract (Fin.tail x)
    rw [Fin.cons_self_tail] at h
    exact h.symm
  rw [hper hup, hper hvp]
  refine hL _ _ fun w hw => ?_
  rw [segment_eq_image'] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  refine ⟨(x 0, y', s), ⟨hx, ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩,
    hs⟩, ?_⟩
  rfl

end Lip

/-! ### Complexification of the `q`-block -/

section QBlock

/-- The `q`-block `(Fin 3 → Met)` complexified and flattened. -/
def qC : (Fin 3 → Fin 4 → Fin 4 → ℝ) →L[ℝ] (Fin 3 × Fin 4 × Fin 4 → ℂ) :=
  ContinuousLinearMap.pi fun p => Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) p.2.2).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) p.2.1).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 4 → Fin 4 → ℝ) p.1)))

theorem qC_apply (v : Fin 3 → Fin 4 → Fin 4 → ℝ) (p : Fin 3 × Fin 4 × Fin 4) :
    qC v p = (v p.1 p.2.1 p.2.2 : ℂ) := rfl

theorem norm_qC (v : Fin 3 → Fin 4 → Fin 4 → ℝ) : ‖qC v‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_)
  · rw [qC_apply, Complex.norm_real]
    exact ((norm_le_pi_norm (v p.1 p.2.1) p.2.2).trans (norm_le_pi_norm (v p.1) p.2.1)).trans
      (norm_le_pi_norm v p.1)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ν => ?_
    have := norm_le_pi_norm (qC v) (a, μ, ν)
    rwa [qC_apply, Complex.norm_real] at this

theorem qC_eq_zero {v : Fin 3 → Fin 4 → Fin 4 → ℝ} (h : qC v = 0) : v = 0 := by
  have := norm_qC v
  rw [h, norm_zero] at this
  exact norm_eq_zero.1 this.symm

end QBlock

/-! ### The metric head and `q` rows of actual-jet states -/

section Rows

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

theorem jet_AF_eq (x : ST 3) : (z.jet x).AF = frameU (z.gi x) :=
  (ActualJet.frameU_eq' (z.jet x)).symm

/-- **The shift-transported metric head row holds on actual-jet states**:
`∂_tg - βʲ∂_jg = Np` (`p = e_0(g)` with the actual derivatives). -/
theorem metric_head_row_actual (x : ST 3) (μ ν : Fin 4) :
    (pd (stateF SM z) 0 x).1.1 μ ν -
        ∑ j : Fin 3, (frameU (z.gi x)).β j * (pd (stateF SM z) j.succ x).1.1 μ ν =
      (frameU (z.gi x)).N * (stateF SM z x).1.2.1 μ ν := by
  simp only [pd_stateF]
  show (z.jet x).FJ.dg 0 μ ν - ∑ j : Fin 3, (frameU (z.gi x)).β j * (z.jet x).FJ.dg j.succ μ ν =
    (frameU (z.gi x)).N * (z.jet x).AF.pJ (fun α => (z.jet x).FJ.dg α μ ν)
  rw [jet_AF_eq, (frameU (z.gi x)).head_row (fun α => (z.jet x).FJ.dg α μ ν)]
  ring

/-- **The `q`-rows of the symmetric system hold exactly on actual-jet states** (no residual or
gauge forcing enters the `q`-block of `eq:actual-jet-writer`). -/
theorem writer_q_row (x : ST 3) :
    (pd (stateF SM z) 0 x).1.2.2 +
        ∑ j : Fin 3, (princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x)).1.2.2 =
      (toP (Fsys SM (ofP (stateF SM z x)))).1.2.2 := by
  have h := writer_pde_err SM z x
  have h0 : (errF SM z x).1.2.2 = 0 := by
    simp [errF, BmL, DmL, QmL, GcL, GdL, toP, Bsys, Qsys, pState, Prod.fst_sum, Prod.snd_sum]
    funext a μ ν
    simp
  have := congrArg (fun U : StateP m V S S' => U.1.2.2) h
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum] at this
  rw [this, h0, add_zero]

/-- The principal `q`-row of a state increment: `-(N e_aʲD_p) - βʲD_{q,a}`. -/
theorem princL_q (v D : StateP m V S S') (j : Fin 3) (a : Fin 3) (μ ν : Fin 4) :
    (princL SM v j D).1.2.2 a μ ν = -((frameU (ginvOf v.1.1)).N * (frameU (ginvOf v.1.1)).E a j *
      D.1.2.1 μ ν) - (frameU (ginvOf v.1.1)).β j * D.1.2.2 a μ ν := rfl

/-- The `q`-block of the forcing depends only on the metric block of the state. -/
theorem Fsys_q_metric (v w : StateP m V S S') (h : v.1 = w.1) :
    (toP (Fsys SM (ofP v))).1.2.2 = (toP (Fsys SM (ofP w))).1.2.2 := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  simp only at h
  subst h
  simp only [Fsys, lowerOf, toP, recon, ofP]

end Rows

/-! ### Propagation of the metric defining-jet identities -/

section MetricDefect

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S')

/-- The projections of a state onto its metric, `p`- and `q`-blocks. -/
def prG : StateP m V S S' →L[ℝ] (Fin 4 → Fin 4 → ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)
/-- The projection of a state onto its `p`-block. -/
def prP : StateP m V S S' →L[ℝ] (Fin 4 → Fin 4 → ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    (ContinuousLinearMap.fst ℝ _ _))
/-- The projection of a state onto its `q`-block. -/
def prQ : StateP m V S S' →L[ℝ] (Fin 3 → Fin 4 → Fin 4 → ℝ) :=
  (ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    (ContinuousLinearMap.fst ℝ _ _))

theorem prG_apply (v : StateP m V S S') : prG v = v.1.1 := rfl
theorem prP_apply (v : StateP m V S S') : prP v = v.1.2.1 := rfl
theorem prQ_apply (v : StateP m V S S') : prQ v = v.1.2.2 := rfl

theorem frameU_beta (z : Tuple m V S S') (x : ST 3) (j : Fin 3) :
    (frameU (z.gi x)).β j = -(z.e x 0 j.succ / z.e x 0 0) := by
  rw [e_eq_frameU, e_eq_frameU, AdaptedFrame.fr_zero_succ, AdaptedFrame.fr_zero_zero]
  have hN := (frameU (z.gi x)).N_pos
  field_simp

/-- The shift-transport coefficients `c = (1, e_0^j/e_0^0) = (1, -βʲ)`. -/
def shiftCoef (z : Tuple m V S S') (μ : Fin 4) (x : ST 3) : ℝ :=
  Fin.cases 1 (fun j : Fin 3 => z.e x 0 j.succ / z.e x 0 0) μ

theorem shiftCoef_zero (z : Tuple m V S S') (x : ST 3) : shiftCoef z 0 x = 1 := rfl

theorem shiftCoef_succ (z : Tuple m V S S') (j : Fin 3) (x : ST 3) :
    shiftCoef z j.succ x = z.e x 0 j.succ / z.e x 0 0 := rfl

theorem e00_pos (z : Tuple m V S S') (x : ST 3) : 0 < z.e x 0 0 := by
  rw [e_eq_frameU, AdaptedFrame.fr_zero_zero]; exact inv_pos.2 (frameU (z.gi x)).N_pos

theorem contDiff_shiftCoef (z : Tuple m V S S') (μ : Fin 4) : ContDiff ℝ 1 (shiftCoef z μ) := by
  induction μ using Fin.cases with
  | zero =>
    have : shiftCoef z 0 = fun _ => 1 := funext fun x => shiftCoef_zero z x
    rw [this]; exact contDiff_const
  | succ j =>
    have : shiftCoef z j.succ = fun x => z.e x 0 j.succ / z.e x 0 0 :=
      funext fun x => shiftCoef_succ z j x
    rw [this]
    exact ((z.contDiff_e 0 j.succ).div (z.contDiff_e 0 0) fun x => (e00_pos z x).ne').of_le
      (by norm_cast)

theorem isSPeriodic_shiftCoef (z : Tuple m V S S') (μ : Fin 4) :
    IsSPeriodic (shiftCoef z μ) := by
  intro k x
  induction μ using Fin.cases with
  | zero => rw [shiftCoef_zero, shiftCoef_zero]
  | succ j => rw [shiftCoef_succ, shiftCoef_succ, e_per z k x, e_per z k x]

theorem shiftCoef_eq_neg_beta (z : Tuple m V S S') (j : Fin 3) (x : ST 3) :
    shiftCoef z j.succ x = -(frameU (z.gi x)).β j := by
  rw [shiftCoef_succ, frameU_beta, neg_neg]

/-- The complexified `q`-defect of two state fields. -/
def qDefect (W U : ST 3 → StateP m V S S') (x : ST 3) : Fin 3 × Fin 4 × Fin 4 → ℂ :=
  qC (prQ (W x - U x))

theorem contDiffOn_qDefect {W U : ST 3 → StateP m V S S'} {O : Set (ST 3)}
    (hW : ContDiffOn ℝ 1 W O) (hU : ContDiffOn ℝ 1 U O) : ContDiffOn ℝ 1 (qDefect W U) O := by
  have h := (qC.comp prQ).contDiff.comp_contDiffOn (hW.sub hU)
  have e : qDefect W U = (qC.comp prQ) ∘ fun x => W x - U x := by
    funext x; simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, qDefect]
  rw [e]; exact h

theorem isSPeriodic_qDefect {W U : ST 3 → StateP m V S S'} (hW : IsSPeriodic W)
    (hU : IsSPeriodic U) : IsSPeriodic (qDefect W U) := fun k x => by
  unfold qDefect; rw [hW k x, hU k x]

theorem pd_sub_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W U : ST 3 → E}
    {x : ST 3} (hW : DifferentiableAt ℝ W x) (hU : DifferentiableAt ℝ U x) (γ : Fin 4) :
    pd (fun y => W y - U y) γ x = pd W γ x - pd U γ x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_sub hW hU, ContinuousLinearMap.sub_apply]

theorem pd_qDefect {W U : ST 3 → StateP m V S S'} {x : ST 3} (hW : DifferentiableAt ℝ W x)
    (hU : DifferentiableAt ℝ U x) (μ : Fin 4) :
    pd (qDefect W U) μ x = qC (prQ (pd W μ x - pd U μ x)) := by
  have h1 : qDefect W U = fun y => (qC.comp prQ) (W y - U y) := by
    funext y; simp only [ContinuousLinearMap.comp_apply, qDefect]
  rw [h1, GenHarmonic.pd_clm (qC.comp prQ) (hW.fun_sub hU) μ, pd_sub_eq hW hU,
    ContinuousLinearMap.comp_apply]

/-- A linear block of two fields which agree on an open set has agreeing partial derivatives. -/
theorem pd_block_eq {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W U : ST 3 → StateP m V S S'} {O : Set (ST 3)} (hO : IsOpen O) (hW : ContDiffOn ℝ 1 W O)
    (hU : ContDiff ℝ ∞ U) (Lm : StateP m V S S' →L[ℝ] F) (h0 : ∀ y ∈ O, Lm (W y) = Lm (U y)) :
    ∀ x ∈ O, ∀ γ, Lm (pd W γ x) = Lm (pd U γ x) := by
  intro x hx γ
  have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW one_ne_zero hx
  have hdU : DifferentiableAt ℝ U x := hU.differentiable (by simp) x
  have ev : (fun y => Lm (W y - U y)) =ᶠ[𝓝 x] 0 :=
    Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => by
      show Lm (W y - U y) = 0
      rw [map_sub, h0 y hy, sub_self]
  have h1 := pd_eq_zero_of_eventually ev γ
  rw [GenHarmonic.pd_clm Lm (hdW.fun_sub hdU) γ, pd_sub_eq hdW hdU, map_sub, sub_eq_zero] at h1
  exact h1

theorem stateF_fst_fst (z : Tuple m V S S') (x : ST 3) : (stateF SM z x).1.1 = z.g x :=
  GenConstraint.stateF_g SM z x

/-- The `p`-block: the shift-transported head row forces `p(W) = e_0(g)`. -/
theorem metric_p_block {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b : ℝ}
    (hW : ContDiffOn ℝ 1 W (openSlab a b)) (hg : ∀ x ∈ openSlab a b, (W x).1.1 = z.g x)
    (hMg : ∀ x ∈ openSlab a b, ∀ μ ν, (pd W 0 x).1.1 μ ν -
      ∑ j : Fin 3, (frameU (z.gi x)).β j * (pd W j.succ x).1.1 μ ν =
        (frameU (z.gi x)).N * (W x).1.2.1 μ ν) :
    ∀ x ∈ openSlab a b, (W x).1.2.1 = (stateF SM z x).1.2.1 := by
  have hpdg := pd_block_eq (isOpen_openSlab a b) hW (contDiff_stateF SM z) prG
    (fun y hy => by rw [prG_apply, prG_apply, hg y hy, stateF_fst_fst])
  intro x hx
  funext μ ν
  have h1 := hMg x hx μ ν
  have h2 := metric_head_row_actual SM z x μ ν
  have e : ∀ γ, (pd W γ x).1.1 = (pd (stateF SM z) γ x).1.1 := fun γ => hpdg x hx γ
  simp only [e] at h1
  have hN := (frameU (z.gi x)).N_pos
  exact mul_left_cancel₀ hN.ne' (by rw [← h1, ← h2])

/-- Once the `p`-blocks agree on the open slab, so do their derivatives. -/
theorem metric_pd_p_block {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b : ℝ}
    (hW : ContDiffOn ℝ 1 W (openSlab a b))
    (hp : ∀ x ∈ openSlab a b, (W x).1.2.1 = (stateF SM z x).1.2.1) :
    ∀ x ∈ openSlab a b, ∀ γ, (pd W γ x).1.2.1 = (pd (stateF SM z) γ x).1.2.1 :=
  pd_block_eq (isOpen_openSlab a b) hW (contDiff_stateF SM z) prP
    (fun y hy => by rw [prP_apply, prP_apply, hp y hy])

/-- The norm of a state difference supported in the `q`-block. -/
theorem norm_diff_q (v u : StateP m V S S') (hg : v.1.1 = u.1.1) (hp : v.1.2.1 = u.1.2.1) :
    ‖v - (u.1, v.2)‖ ≤ ‖qC (prQ (v - u))‖ := by
  rw [norm_qC]
  obtain ⟨⟨vg, vp, vq⟩, v2⟩ := v
  obtain ⟨⟨ug, up, uq⟩, u2⟩ := u
  simp only at hg hp
  subst hg hp
  simp [prQ_apply, Prod.norm_def]

/-- **Uniform Lipschitz bound of the `q`-forcing** along the segments joining `W` to the state with
the head and auxiliary metric blocks of `U = 𝒰(z)` and the matter blocks of `W`. -/
theorem forcing_lip_q (hS : SMSmooth SM) {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
    {a t₀ t₁ b : ℝ} (ha : a < t₀) (hb : t₁ < b) (hW : ContDiffOn ℝ 1 W (openSlab a b))
    (hWp : IsSPeriodic W) (hg : ∀ x ∈ openSlab a b, (W x).1.1 = z.g x) :
    ∃ L, ∀ x ∈ slab t₀ t₁, ‖(toP (Fsys SM (ofP (W x)))).1.2.2 -
        (toP (Fsys SM (ofP (stateF SM z x)))).1.2.2‖ ≤
      L * ‖W x - ((stateF SM z x).1, (W x).2)‖ := by
  set U := stateF SM z with hUdef
  have hU : ContDiff ℝ ∞ U := contDiff_stateF SM z
  have hUp : IsSPeriodic U := isSPeriodic_stateF SM z
  set Φ : StateP m V S S' → (Fin 3 → Fin 4 → Fin 4 → ℝ) :=
    fun v => (toP (Fsys SM (ofP v))).1.2.2 with hΦ
  set Ut : ST 3 → StateP m V S S' := fun x => ((U x).1, (W x).2) with hUt
  have hΦc : ContDiffOn ℝ 1 Φ (chartSet (m := m) (V := V) (S := S) (S' := S')) := fun v hv =>
    (((prQ (m := m) (V := V) (S := S) (S' := S')).contDiff.contDiffAt.comp v
      (contDiffAt_Fsys_state hS hv)).of_le (by norm_cast)).contDiffWithinAt
  have hUtc : ContinuousOn Ut (openSlab a b) :=
    (hU.continuous.fst.continuousOn).prodMk hW.continuousOn.snd
  have hUtp : IsSPeriodic Ut := fun k x => by simp only [hUt, hUp k x, hWp k x]
  have hseg : ∀ x ∈ openSlab a b, ∀ s ∈ Icc (0 : ℝ) 1,
      Ut x + s • (W x - Ut x) ∈ chartSet (m := m) (V := V) (S := S) (S' := S') := by
    intro x hx s _
    have hgx : (Ut x + s • (W x - Ut x)).1.1 = z.g x := by
      rw [Prod.fst_add, Prod.fst_add, Prod.smul_fst, Prod.smul_fst, Prod.fst_sub, Prod.fst_sub,
        hg x hx]
      have : (Ut x).1.1 = z.g x := stateF_fst_fst SM z x
      rw [this, sub_self, smul_zero, add_zero]
    exact ⟨by rw [hgx]; exact z.det_ne x, by rw [hgx]; exact z.lor x⟩
  obtain ⟨L, hL⟩ :=
    lip_slab (isOpen_chartSet) hΦc ha hb hUtc hW.continuousOn hUtp hWp hseg
  refine ⟨L, fun x hx => ?_⟩
  have h := hL x hx
  have hΦUt : Φ (Ut x) = Φ (U x) := Fsys_q_metric SM (Ut x) (U x) rfl
  rw [hΦUt] at h
  exact h

/-- The `q`-rows of `W` and of the actual-jet state `U = 𝒰(z)` differ, once the metric and `p`
blocks agree, by the shift transport of the `q`-defect. -/
theorem q_row_difference (z : Tuple m V S S') (Wx : StateP m V S S')
    (dW : Fin 4 → StateP m V S S') (x : ST 3) (hgx : Wx.1.1 = z.g x)
    (hpj : ∀ j : Fin 3, (dW j.succ).1.2.1 = (pd (stateF SM z) j.succ x).1.2.1)
    (hMq : (dW 0).1.2.2 + ∑ j : Fin 3, (princL SM Wx j (dW j.succ)).1.2.2 =
        (toP (Fsys SM (ofP Wx))).1.2.2) :
    prQ (dW 0 - pd (stateF SM z) 0 x) +
        ∑ j : Fin 3, shiftCoef z j.succ x • prQ (dW j.succ - pd (stateF SM z) j.succ x) =
      (toP (Fsys SM (ofP Wx))).1.2.2 - (toP (Fsys SM (ofP (stateF SM z x)))).1.2.2 := by
  rw [← hMq, ← writer_q_row SM z x]
  have hgW : ginvOf Wx.1.1 = z.gi x := by rw [hgx]; rfl
  have hgU : ginvOf (stateF SM z x).1.1 = z.gi x := by rw [stateF_fst_fst]; rfl
  funext a μ ν
  simp only [prQ_apply, Prod.fst_sub, Prod.snd_sub, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, princL_q, hgW, hgU, shiftCoef_eq_neg_beta]
  have hpj' : ∀ j : Fin 3, (dW j.succ).1.2.1 μ ν = (pd (stateF SM z) j.succ x).1.2.1 μ ν :=
    fun j => congrFun (congrFun (hpj j) μ) ν
  simp only [hpj']
  simp only [mul_sub, neg_mul, sub_neg_eq_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  ring

/-- **Propagation of the metric defining-jet identities** (shift-transported head row).  Let `W` be
a `C¹` spatially periodic state field on `(a, b) × 𝕋³` whose metric block is the metric of a
smooth tuple `z`, satisfying the shift-transported head row `∂_tg - βʲ∂_jg = Np` and the `q`-rows
of the symmetric system.  Then `p(W) = e_0(g)` on the slab, and if `q(W) = e_a(g)` on the slice
`t = t₀`, then `q(W) = e_a(g)` on `[t₀, t₁] × 𝕋³`. -/
theorem metric_defect_propagation (hS : SMSmooth SM) {W : ST 3 → StateP m V S S'}
    {z : Tuple m V S S'} {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hW : ContDiffOn ℝ 1 W (openSlab a b)) (hWp : IsSPeriodic W)
    (hg : ∀ x ∈ openSlab a b, (W x).1.1 = z.g x)
    (hMg : ∀ x ∈ openSlab a b, ∀ μ ν, (pd W 0 x).1.1 μ ν -
      ∑ j : Fin 3, (frameU (z.gi x)).β j * (pd W j.succ x).1.1 μ ν =
        (frameU (z.gi x)).N * (W x).1.2.1 μ ν)
    (hMq : ∀ x ∈ openSlab a b, (pd W 0 x).1.2.2 +
      ∑ j : Fin 3, (princL SM (W x) j (pd W j.succ x)).1.2.2 =
        (toP (Fsys SM (ofP (W x)))).1.2.2)
    (hq0 : ∀ y : Fin 3 → ℝ, (W (Fin.cons t₀ y)).1.2.2 = (stateF SM z (Fin.cons t₀ y)).1.2.2) :
    (∀ x ∈ openSlab a b, (W x).1.2.1 = (stateF SM z x).1.2.1) ∧
      ∀ x ∈ slab t₀ t₁, (W x).1.2.2 = (stateF SM z x).1.2.2 := by
  have hp := metric_p_block SM hW hg hMg
  refine ⟨hp, ?_⟩
  have hpdp := metric_pd_p_block SM hW hp
  obtain ⟨L, hL⟩ := forcing_lip_q SM hS ha hb hW hWp hg
  have heq : ∀ x ∈ slab t₀ t₁, ‖∑ μ, shiftCoef z μ x • pd (qDefect W (stateF SM z)) μ x‖ ≤
      max L 0 * ‖qDefect W (stateF SM z) x‖ := by
    intro x hx
    have hxO : x ∈ openSlab a b := slab_subset_openSlab ha hb hx
    have hdW : DifferentiableAt ℝ W x :=
      GenHarmonic.diffAt_of_contDiffOn (isOpen_openSlab a b) hW one_ne_zero hxO
    have hdU : DifferentiableAt ℝ (stateF SM z) x :=
      (contDiff_stateF SM z).differentiable (by simp) x
    have hrow := q_row_difference SM z (W x) (fun μ => pd W μ x) x (hg x hxO)
      (fun j => hpdp x hxO j.succ) (hMq x hxO)
    have hsum : ∑ μ, shiftCoef z μ x • pd (qDefect W (stateF SM z)) μ x =
        qC ((toP (Fsys SM (ofP (W x)))).1.2.2 -
          (toP (Fsys SM (ofP (stateF SM z x)))).1.2.2) := by
      rw [Fin.sum_univ_succ, ← hrow, map_add, map_sum]
      simp only [pd_qDefect hdW hdU, map_smul, shiftCoef_zero, one_smul]
    rw [hsum, norm_qC]
    have hd := norm_diff_q (W x) (stateF SM z x) (by rw [hg x hxO, stateF_fst_fst]) (hp x hxO)
    calc _ ≤ L * ‖W x - ((stateF SM z x).1, (W x).2)‖ := hL x hx
      _ ≤ max L 0 * ‖W x - ((stateF SM z x).1, (W x).2)‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max L 0 * ‖qDefect W (stateF SM z) x‖ :=
          mul_le_mul_of_nonneg_left hd (le_max_right _ _)
  have h0 : ∀ y : Fin 3 → ℝ, qDefect W (stateF SM z) (Fin.cons t₀ y) = 0 := by
    intro y
    unfold qDefect
    rw [map_sub, prQ_apply, prQ_apply, hq0 y, sub_self, map_zero]
  have hzero := GenGauss.transport_unique (N := Fin 3 × Fin 4 × Fin 4) (c := shiftCoef z) ha
    h01 hb (contDiffOn_qDefect hW ((contDiff_stateF SM z).of_le (by norm_cast)).contDiffOn)
    (isSPeriodic_qDefect hWp (isSPeriodic_stateF SM z))
    (fun μ => (contDiff_shiftCoef z μ).contDiffOn) (isSPeriodic_shiftCoef z) one_pos
    (fun x _ => (shiftCoef_zero z x).ge) (le_max_right L 0) heq h0
  intro x hx
  have h1 := qC_eq_zero (hzero x hx)
  rw [map_sub, prQ_apply, prQ_apply] at h1
  exact sub_eq_zero.1 h1

/-- Non-vacuity: the actual-jet state `𝒰(z)` of every smooth tuple satisfies all hypotheses of
`metric_defect_propagation` (with `W = 𝒰(z)`). -/
theorem metric_defect_hypotheses_stateF (z : Tuple m V S S') {a b : ℝ} :
    ContDiffOn ℝ 1 (stateF SM z) (openSlab a b) ∧ IsSPeriodic (stateF SM z) ∧
      (∀ x ∈ openSlab a b, (stateF SM z x).1.1 = z.g x) ∧
      (∀ x ∈ openSlab a b, ∀ μ ν, (pd (stateF SM z) 0 x).1.1 μ ν -
        ∑ j : Fin 3, (frameU (z.gi x)).β j * (pd (stateF SM z) j.succ x).1.1 μ ν =
          (frameU (z.gi x)).N * (stateF SM z x).1.2.1 μ ν) ∧
      (∀ x ∈ openSlab a b, (pd (stateF SM z) 0 x).1.2.2 +
        ∑ j : Fin 3, (princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x)).1.2.2 =
          (toP (Fsys SM (ofP (stateF SM z x)))).1.2.2) :=
  ⟨((contDiff_stateF SM z).of_le (by norm_cast)).contDiffOn, isSPeriodic_stateF SM z,
    fun x _ => stateF_fst_fst SM z x, fun x _ => metric_head_row_actual SM z x,
    fun x _ => writer_q_row SM z x⟩

end MetricDefect

end RenewalGeometry.GenDefJet
