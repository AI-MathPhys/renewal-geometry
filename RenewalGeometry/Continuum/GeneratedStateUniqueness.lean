/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedSpinorDefect

/-!
# Uniqueness against the actual-jet state of a physical tuple

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`), last step of the defining-jet identities: the remaining auxiliary
variables (the spinor jets `X_a`, `X̄_a`) are identified by uniqueness for the symmetric system.

* `pd_zero_of_halfslab` — a differentiable field vanishing on `[0, ε) × 𝕋³` has vanishing partial
  derivatives there (one-sided derivatives at `t = 0`).
* `errF_zero_of_phys` — the residual forcing `errF` of a tuple vanishes where the tuple is
  physical (including the initial slice).
* **`state_eq_of_rows`** — a `C¹` periodic field `W` solving the original symmetric system on a slab,
  with the metric block of the actual-jet state `𝒰(z)` of a tuple `z` whose residual forcing
  vanishes on `[t₀, t₁]`, and with `W = 𝒰(z)` at `t = t₀`, equals `𝒰(z)` on `[t₀, t₁] × 𝕋³`
  (symmetric-hyperbolic uniqueness in Euclidean coordinates of the block inner product, with the
  coefficients frozen along `z`).
-/

open Filter Topology Set
open scoped BigOperators ContDiff NNReal

noncomputable section

namespace RenewalGeometry.GenStateUnique

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
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

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-! ### Fields vanishing on a half-open slab -/

section Half

/-- A differentiable field vanishing on `[0, ε) × ℝ³` has vanishing partial derivatives there
(at `t = 0` the time derivative is the one-sided one). -/
theorem pd_zero_of_halfslab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    (hf : Differentiable ℝ f) {ε : ℝ} (h : ∀ y : ST 3, 0 ≤ y 0 → y 0 < ε → f y = 0) {x : ST 3}
    (hx0 : 0 ≤ x 0) (hxε : x 0 < ε) (μ : Fin 4) : pd f μ x = 0 := by
  have hg := ActualJetBridge.hasDerivAt_line0 (hf x) μ
  have ht : ∀ s : ℝ, (x + s • ev μ) 0 = x 0 + s * (ev μ : ST 3) 0 := fun s => by simp
  have hev : (ev μ : ST 3) 0 = 0 ∨ (ev μ : ST 3) 0 = 1 := by
    by_cases hμ : μ = 0
    · right; subst hμ; simp
    · left
      simp [Ne.symm hμ]
  have hg0 : HasDerivWithinAt (fun s : ℝ => f (x + s • ev μ)) 0 (Ici 0) 0 := by
    refine (hasDerivWithinAt_const (0 : ℝ) (Ici 0) (0 : E)).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Ico_mem_nhdsGE (show (0 : ℝ) < ε - x 0 by linarith)] with s hs
      apply h
      · rw [ht]
        rcases hev with e | e <;> rw [e] <;> simp only [mul_zero, mul_one, add_zero] <;>
          linarith [hs.1, hs.2]
      · rw [ht]
        rcases hev with e | e <;> rw [e] <;> simp only [mul_zero, mul_one, add_zero] <;>
          linarith [hs.1, hs.2]
    · simp [h x hx0 hxε]
  exact (uniqueDiffOn_Ici (0 : ℝ) 0 Set.self_mem_Ici).eq_deriv _ hg.hasDerivWithinAt hg0

/-- **The residual forcing vanishes where the tuple is physical** (on `[0, ε) × 𝕋³`, including the
initial slice). -/
theorem errF_zero_of_phys {z : Tuple m V S S'} {ε : ℝ}
    (hP : ∀ x : ST 3, 0 ≤ x 0 → x 0 < ε → bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0)
    {x : ST 3} (hx0 : 0 ≤ x 0) (hxε : x 0 < ε) : errF SM z x = 0 := by
  have hD : ∀ μ, pd (dirF SM z) μ x = 0 := fun μ =>
    pd_zero_of_halfslab ((contDiff_dirF SM z).differentiable (by simp))
      (fun y h0 h1 => (hP y h0 h1).2.1) hx0 hxε μ
  have hC : ∀ μ, pd (CF z) μ x = 0 := fun μ =>
    pd_zero_of_halfslab ((contDiff_CF z).differentiable (by simp))
      (fun y h0 h1 => (hP y h0 h1).2.2) hx0 hxε μ
  obtain ⟨hB, hDi, hCF⟩ := hP x hx0 hxε
  unfold errF
  rw [hB, hDi, hCF, hC 0]
  simp only [hD, hC, map_zero, add_zero, Finset.sum_const_zero]

end Half

/-! ### Uniqueness against the actual-jet state -/

section Unique

/-- The adapted frame along a tuple from its frame components. -/
theorem frameU_eq_mkFrame (z : Tuple m V S S') (x : ST 3) :
    frameU (z.gi x) = mkFrame (-Real.log (z.e x 0 0)) (fun j => -(z.e x 0 j.succ / z.e x 0 0))
      (fun a j => z.e x a.succ j.succ) := by
  symm
  apply mkFrame_eq
  · rw [e_eq_frameU, AdaptedFrame.fr_zero_zero, Real.log_inv, neg_neg]
  · funext j; rw [GenDefJet.frameU_beta]
  · funext a j; rw [e_eq_frameU, AdaptedFrame.fr_succ_succ]

/-- The principal matrices frozen along a tuple (`c 0 = 1`). -/
def cz (SM : SMData (MatLie m) V S S') (bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ)
    (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (z : Tuple m V S S') (μ : Fin 4)
    (x : ST 3) : Fin (dimS m V S S') → Fin (dimS m V S S') → ℝ :=
  Fin.cases (fun i k => if i = k then (1 : ℝ) else 0)
    (fun j i k => princEntry SM bG bV bS bS' κ (frameU (z.gi x)) j i k) μ

theorem contDiff_cz (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (z : Tuple m V S S')
    (μ : Fin 4) : ContDiff ℝ 1 (cz SM bG bV bS bS' κ z μ) := by
  induction μ using Fin.cases with
  | zero => exact contDiff_const
  | succ j =>
    have e : cz SM bG bV bS bS' κ z j.succ = fun x i k => princEntry SM bG bV bS bS' κ
        (mkFrame (-Real.log (z.e x 0 0)) (fun j => -(z.e x 0 j.succ / z.e x 0 0))
          (fun a j => z.e x a.succ j.succ)) j i k := by
      funext x i k
      simp only [cz, Fin.cases_succ, frameU_eq_mkFrame]
    rw [e]
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun k => ?_
    refine (contDiff_princEntry_mkFrame κ ?_ ?_ ?_ j i k).of_le (by norm_cast)
    · exact ((z.contDiff_e 0 0).log fun x => (GenDefJet.e00_pos z x).ne').neg
    · intro j'
      exact ((z.contDiff_e 0 j'.succ).div (z.contDiff_e 0 0)
        fun x => (GenDefJet.e00_pos z x).ne').neg
    · intro a' j'
      exact z.contDiff_e a'.succ j'.succ

theorem isSPeriodic_cz (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (z : Tuple m V S S')
    (μ : Fin 4) : IsSPeriodic (cz SM bG bV bS bS' κ z μ) := by
  intro k x
  induction μ using Fin.cases with
  | zero => simp only [cz, Fin.cases_zero]
  | succ j => simp only [cz, Fin.cases_succ, gi_per (z := z) k x]

theorem cz_zero (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (z : Tuple m V S S')
    (x : ST 3) (i k : Fin (dimS m V S S')) :
    cz SM bG bV bS bS' κ z 0 x i k = if i = k then (fun _ : ST 3 => (1 : ℝ)) x else 0 := by
  simp only [cz, Fin.cases_zero]

theorem cz_symm (hU : UnitaryForms SM bG bV bS bS')
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (z : Tuple m V S S') (μ : Fin 4)
    (x : ST 3) (i k : Fin (dimS m V S S')) :
    cz SM bG bV bS bS' κ z μ x i k = cz SM bG bV bS bS' κ z μ x k i := by
  induction μ using Fin.cases with
  | zero =>
    show (if i = k then (1 : ℝ) else 0) = if k = i then 1 else 0
    by_cases h : i = k
    · subst h; rfl
    · simp [h, Ne.symm h]
  | succ j => exact princEntry_symm hU κ _ j i k

set_option maxHeartbeats 2000000 in -- costly instance unification on states
/-- **Uniqueness against the actual-jet state of a tuple with vanishing residual forcing.** -/
theorem state_eq_of_rows (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    (hκ : ∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i)
    {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a t₀ t₁ b : ℝ}
    (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hW : ContDiffOn ℝ 1 W (openSlab a b)) (hWp : IsSPeriodic W)
    (hmet : ∀ y ∈ openSlab a b, (W y).1 = (stateF SM z y).1)
    (hrow : ∀ y ∈ openSlab a b, pd W 0 y + ∑ j : Fin 3, princL SM (W y) j (pd W j.succ y) =
      toP (Fsys SM (ofP (W y))))
    (herr : ∀ x ∈ slab t₀ t₁, errF SM z x = 0)
    (hinit : ∀ y : Fin 3 → ℝ, W (Fin.cons t₀ y) = stateF SM z (Fin.cons t₀ y)) :
    ∀ x ∈ slab t₀ t₁, W x = stateF SM z x := by
  have hO := isOpen_openSlab (d := 3) a b
  set U := stateF SM z with hUdef
  have hUs : ContDiff ℝ ∞ U := contDiff_stateF SM z
  set κc : StateP m V S S' →L[ℝ] (Fin (dimS m V S S') → ℝ) :=
    LinearMap.toContinuousLinearMap κ.toLinearMap with hκc
  set κs : (Fin (dimS m V S S') → ℝ) →L[ℝ] StateP m V S S' :=
    LinearMap.toContinuousLinearMap κ.symm.toLinearMap with hκs
  have hκc_apply : ∀ v, κc v = κ v := fun v => rfl
  have hκs_apply : ∀ v, κs v = κ.symm v := fun v => rfl
  set D : ST 3 → Fin (dimS m V S S') → ℝ := fun x => κc (W x - U x) with hD
  have hD1 : ContDiffOn ℝ 1 D (openSlab a b) :=
    κc.contDiff.comp_contDiffOn (hW.sub (hUs.of_le (by norm_cast)).contDiffOn)
  have hDp : IsSPeriodic D := fun k x => by
    simp only [hD, hWp k x]
    rw [show U (x + sshift k) = U x from isSPeriodic_stateF SM z k x]
  have hpdD : ∀ x ∈ openSlab a b, ∀ μ, pd D μ x = κc (pd W μ x - pd U μ x) := by
    intro x hx μ
    have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW one_ne_zero hx
    have hdU : DifferentiableAt ℝ U x := hUs.differentiable (by simp) x
    rw [show D = fun y => κc (W y - U y) from rfl, GenHarmonic.pd_clm κc (hdW.fun_sub hdU) μ,
      GenDefJet.pd_sub_eq hdW hdU]
  have hgU : ∀ x, frameU (ginvOf (U x).1.1) = frameU (z.gi x) := fun x => by
    rw [GenDefJet.stateF_fst_fst]; rfl
  -- the Lipschitz bound of the forcing along the slab
  set Φ : StateP m V S S' → StateP m V S S' := fun v => toP (Fsys SM (ofP v)) with hΦ
  have hΦc : ContDiffOn ℝ 1 Φ (chartSet (m := m) (V := V) (S := S) (S' := S')) := fun v hv =>
    ((contDiffAt_Fsys_state hS hv).of_le (by norm_cast)).contDiffWithinAt
  have hUc : ∀ x, MetChart (U x).1 := fun x =>
    ⟨by rw [GenDefJet.stateF_fst_fst]; exact z.det_ne x,
      by rw [GenDefJet.stateF_fst_fst]; exact z.lor x⟩
  have hseg : ∀ x ∈ openSlab a b, ∀ s ∈ Icc (0 : ℝ) 1,
      U x + s • (W x - U x) ∈ chartSet (m := m) (V := V) (S := S) (S' := S') := by
    intro x hx s _
    show MetChart (U x + s • (W x - U x)).1
    have : (U x + s • (W x - U x)).1 = (U x).1 := by
      simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, hmet x hx, sub_self, smul_zero,
        add_zero]
    rw [this]; exact hUc x
  obtain ⟨L, hL⟩ := GenDefJet.lip_slab isOpen_chartSet hΦc ha hb hUs.continuous.continuousOn
    hW.continuousOn (isSPeriodic_stateF SM z) hWp hseg
  -- the difference equation
  have hkey : ∀ x ∈ slab t₀ t₁, (fun i => ∑ μ, ∑ k, cz SM bG bV bS bS' κ z μ x i k * pd D μ x k) =
      κc (Φ (W x) - Φ (U x)) := by
    intro x hx
    have hxO : x ∈ openSlab a b := slab_subset_openSlab ha hb hx
    have hpL : ∀ j : Fin 3, ∀ w, princL SM (W x) j w = princL SM (U x) j w := by
      intro j w
      show toP (ActualJetSystem.princ (frameU (ginvOf (W x).1.1)) SM.D.Fr SM.Db.Fr j (ofP w)) =
        toP (ActualJetSystem.princ (frameU (ginvOf (U x).1.1)) SM.D.Fr SM.Db.Fr j (ofP w))
      rw [hmet x hxO]
    have hΦU : Φ (U x) = pd U 0 x + ∑ j : Fin 3, princL SM (U x) j (pd U j.succ x) := by
      rw [writer_pde_err SM z x, herr x hx, add_zero]
    have hvec : pd W 0 x - pd U 0 x +
        ∑ j : Fin 3, princL SM (U x) j (pd W j.succ x - pd U j.succ x) = Φ (W x) - Φ (U x) := by
      rw [hΦU, show Φ (W x) = toP (Fsys SM (ofP (W x))) from rfl, ← hrow x hxO]
      simp only [map_sub, Finset.sum_sub_distrib, hpL]
      abel
    rw [← hvec]
    funext i
    rw [Fin.sum_univ_succ]
    have e0 : ∑ k, cz SM bG bV bS bS' κ z 0 x i k * pd D 0 x k = pd D 0 x i := by
      simp [cz]
    have ej : ∀ j : Fin 3, ∑ k, cz SM bG bV bS bS' κ z j.succ x i k * pd D j.succ x k =
        κc (princL SM (U x) j (pd W j.succ x - pd U j.succ x)) i := by
      intro j
      show ∑ k, princEntry SM bG bV bS bS' κ (frameU (z.gi x)) j i k * pd D j.succ x k = _
      rw [sum_princEntry hU hκ, hpdD x hxO, hκc_apply, LinearEquiv.symm_apply_apply, ← hgU x]
      rfl
    rw [e0]
    simp only [ej]
    rw [hpdD x hxO, map_add, map_sum, Pi.add_apply, Finset.sum_apply]
  -- uniqueness
  set K : ℝ := ‖κc‖ * max L 0 * ‖κs‖ with hK
  have hK0 : 0 ≤ K := by positivity
  have heq : ∀ x ∈ slab t₀ t₁,
      ‖(fun i => ∑ μ, ∑ k, cz SM bG bV bS bS' κ z μ x i k * pd D μ x k)‖ ≤ K * ‖D x‖ := by
    intro x hx
    rw [hkey x hx]
    have hWU : W x - U x = κs (D x) := by
      rw [hκs_apply]
      exact (κ.symm_apply_apply _).symm
    calc ‖κc (Φ (W x) - Φ (U x))‖ ≤ ‖κc‖ * ‖Φ (W x) - Φ (U x)‖ := κc.le_opNorm _
      _ ≤ ‖κc‖ * (max L 0 * ‖W x - U x‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (hL x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      _ ≤ ‖κc‖ * (max L 0 * (‖κs‖ * ‖D x‖)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
            (norm_nonneg _)
          rw [hWU]; exact κs.le_opNorm _
      _ = K * ‖D x‖ := by rw [hK]; ring
  have hinitD : ∀ y : Fin 3 → ℝ, D (Fin.cons t₀ y) = 0 := fun y => by
    simp only [hD, hinit y, sub_self, map_zero]
  have hzero := GenHarmonic.sym_unique (W := D) (c := cz SM bG bV bS bS' κ z) (a0 := fun _ => 1)
    ha h01 hb hD1 hDp (fun μ => (contDiff_cz κ z μ).contDiffOn) (isSPeriodic_cz κ z)
    (cz_symm hU κ z) (cz_zero κ z) one_pos (fun x _ => le_refl 1) hK0 heq hinitD
  intro x hx
  have h := hzero x hx
  have h3 : κ (W x) - κ (U x) = 0 := by
    rw [← map_sub, ← hκc_apply]; exact h
  exact κ.injective (sub_eq_zero.1 h3)

end Unique


end RenewalGeometry.GenStateUnique
