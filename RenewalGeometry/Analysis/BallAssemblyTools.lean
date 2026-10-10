/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallUhlenbeckCore

/-!
# Tools for the assembly of Uhlenbeck's gauge on a ball
  (stage D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `matOfSmooth_eq_zero`, `sum_derM_embX_eq_zero` — Sobolev bookkeeping;
* `hasWeakPartial_congr_ae`, `pd_ae_eq_of_weak` — weak derivatives only see the ball, and the
  classical derivative of a smooth representative is the weak derivative;
* `EntCDO` — entrywise smoothness of matrix fields on a set, stable under products, adjoints,
  derivatives (on open sets) and gauge transformations (`EntCDO.gaugeConn`);
* `gaugeConn_mul_apply` — **composition of gauge transformations**
  `(U P)·A = U·(P·A)` for unitary `P`;
* `wCurvNorm_state_le` — the weak curvature norm of a Coulomb state `a = u·B_f` is bounded by
  `16 m² ‖F_{B_f}‖_{L²}` (gauge covariance of the curvature).
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.AssemblyTools

open SobolevOpen BallReg BallAlg SobAlg FinalTools UhlenbeckCore WeakCoulomb CriticalGauge

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

/-! ### Sobolev bookkeeping -/

theorem matOfSmooth_eq_zero {s : ℕ} [Fact (3 ≤ s)] {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) (h0 : ∀ x, F x = 0) :
    matOfSmooth (c := c) (r := r) s F hF = 0 := by
  refine ext_evM ?_
  filter_upwards [evM_matOfSmooth (c := c) (r := r) (s := s) hF,
    evM_zero (c := c) (r := r) (s := s) (m := m)] with x h1 h2
  rw [h1, h2, h0 x]

theorem sum_derM_embX_eq_zero (L : LieBasis m d) {a : Fin 4 → Fin d → SobAlg c r 4}
    (hcoul : coulF L (a, 0) = 0) : ∑ μ, derM μ (embX L (a μ)) = 0 := by
  have hcb : ∀ b, ∑ μ, derS μ (a μ b) = 0 := fun b => by
    have := congrFun hcoul b
    rwa [coulF_zero] at this
  refine Matrix.ext fun i j => ?_
  rw [Matrix.sum_apply]
  simp only [derM_embX, embX_apply, Matrix.zero_apply]
  ext
  · rw [Cx.sum_re, Cx.zero_re, Finset.sum_comm]
    simp only [← Finset.smul_sum, hcb, smul_zero, Finset.sum_const_zero]
  · rw [Cx.sum_im, Cx.zero_im, Finset.sum_comm]
    simp only [← Finset.smul_sum, hcb, smul_zero, Finset.sum_const_zero]

/-! ### Weak derivatives on the ball -/

theorem hasWeakPartial_congr_ae {Ω : Set (Fin 4 → ℝ)} {i : Fin 4} {f f' g : (Fin 4 → ℝ) → ℂ}
    (h : HasWeakPartial Ω i f g) (hf : f =ᵐ[volume.restrict Ω] f') : HasWeakPartial Ω i f' g := by
  intro φ hφ
  rw [integral_test_eq_setIntegral_complex (isTest_pd hφ i)]
  rw [← h φ hφ, integral_test_eq_setIntegral_complex (isTest_pd hφ i)]
  refine integral_congr_ae ?_
  filter_upwards [hf] with x hx
  rw [hx]

/-- **The classical derivative of a smooth representative is the weak derivative.** -/
theorem pd_ae_eq_of_weak {Ω : Set (Fin 4 → ℝ)} (hΩ : IsOpen Ω) {i : Fin 4}
    {F f g : (Fin 4 → ℝ) → ℂ} (hF : ContDiffOn ℝ ∞ F Ω) (hfF : f =ᵐ[volume.restrict Ω] F)
    (hw : HasWeakPartial Ω i f g) (hg : LocallyIntegrableOn g Ω) :
    pd F i =ᵐ[volume.restrict Ω] g := by
  have hcl : HasWeakPartial Ω i F (pd F i) := hasWeakPartial_of_contDiffOn hΩ (hF.of_le (by simp)) i
  have hw' : HasWeakPartial Ω i F g := hasWeakPartial_congr_ae hw hfF
  have hli : LocallyIntegrableOn (pd F i) Ω :=
    ((hF.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply
      continuousOn_const).locallyIntegrableOn hΩ.measurableSet
  have := hcl.ae_eq hΩ hw' hli hg
  rw [EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [this] with x hx hxΩ
  exact hx hxΩ

/-! ### Entrywise smoothness of matrix fields -/

/-- Entrywise `C^∞` on a set. -/
def EntCDO (F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ) (Ω : Set (Fin 4 → ℝ)) : Prop :=
  ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) Ω

theorem EntCDO.of_contDiff {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ a b, ContDiff ℝ ∞ (fun x => F x a b)) (Ω : Set (Fin 4 → ℝ)) : EntCDO F Ω :=
  fun a b => (hF a b).contDiffOn

theorem EntCDO.mul {F G : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {Ω : Set (Fin 4 → ℝ)}
    (hF : EntCDO F Ω) (hG : EntCDO G Ω) : EntCDO (fun x => F x * G x) Ω := fun a b => by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hF a k).mul (hG k b)

theorem EntCDO.sub {F G : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {Ω : Set (Fin 4 → ℝ)}
    (hF : EntCDO F Ω) (hG : EntCDO G Ω) : EntCDO (fun x => F x - G x) Ω := fun a b => by
  simp only [Matrix.sub_apply]
  exact (hF a b).sub (hG a b)

theorem EntCDO.star {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {Ω : Set (Fin 4 → ℝ)}
    (hF : EntCDO F Ω) : EntCDO (fun x => star (F x)) Ω := fun a b => by
  simp only [Matrix.star_apply]
  exact (Complex.conjCLE.contDiff.comp_contDiffOn (hF b a))

theorem EntCDO.pdM {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {Ω : Set (Fin 4 → ℝ)}
    (hΩ : IsOpen Ω) (hF : EntCDO F Ω) (μ : Fin 4) : EntCDO (pdM F μ) Ω := fun a b => by
  show ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => F y a b) x (Pi.single μ 1)) Ω
  exact ((hF a b).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const

theorem EntCDO.gaugeConn {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {A : MConn m}
    {Ω : Set (Fin 4 → ℝ)} (hΩ : IsOpen Ω) (hR : EntCDO R Ω) (hA : ∀ μ, EntCDO (A μ) Ω)
    (μ : Fin 4) : EntCDO (gaugeConn R A μ) Ω :=
  (((hR.mul (hA μ)).mul hR.star)).sub ((hR.pdM hΩ μ).mul hR.star)

theorem EntCDO.mDiffAt {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {Ω : Set (Fin 4 → ℝ)}
    (hΩ : IsOpen Ω) (hF : EntCDO F Ω) {x : Fin 4 → ℝ} (hx : x ∈ Ω) : MDiffAt F x := fun a b =>
  ((hF a b).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hx)

theorem EntCDO.continuousOn_pd {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    {Ω : Set (Fin 4 → ℝ)} (hΩ : IsOpen Ω) (hF : EntCDO F Ω) (a b : Fin m) (μ : Fin 4) :
    ContinuousOn (pd (fun x => F x a b) μ) Ω :=
  ((hF a b).continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const

/-! ### Composition of gauge transformations -/

/-- **Composition of gauge transformations**: for `P` unitary at `x`,
`((U P)·A)_μ(x) = (U·(P·A))_μ(x)`. -/
theorem gaugeConn_mul_apply {U P : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} (A : MConn m)
    {x : Fin 4 → ℝ} (hU : MDiffAt U x) (hP : MDiffAt P x) (hPu : P x * star (P x) = 1)
    (μ : Fin 4) :
    gaugeConn (fun y => U y * P y) A μ x = gaugeConn U (gaugeConn P A) μ x := by
  simp only [gaugeConn]
  rw [pdM_mul hU hP μ, star_mul]
  have e : pdM U μ x * P x * (star (P x) * star (U x)) = pdM U μ x * star (U x) := by
    rw [show pdM U μ x * P x * (star (P x) * star (U x)) =
      pdM U μ x * (P x * star (P x)) * star (U x) by noncomm_ring, hPu, mul_one]
  rw [add_mul, e]
  noncomm_ring

/-! ### The curvature bound for Coulomb states -/

theorem wCurvNorm_state_le (L : LieBasis m d) {u : MatSob c r 5 m} (hu : u * star u = 1)
    {Bf : MConn m} (hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j))
    {a : Fin 4 → Fin d → SobAlg c r 4}
    (hact : ∀ μ, actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ =
      embX L (a μ)) :
    wCurvNorm c r (fun ν i j x => evM (embX L (a ν)) x i j)
      (fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j) ≤
      16 * (m : ℝ≥0∞) ^ 2 * (∫⁻ x in euclBall c r, ‖curvVec Bf x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  set ρ := volume.restrict (euclBall c r)
  set E := (∫⁻ x in euclBall c r, ‖curvVec Bf x‖ₑ ^ 2) ^ (1 / 2 : ℝ)
  have hU : ∀ᵐ x ∂ρ, star (evM u x) * evM u x = 1 := by
    filter_upwards [evM_mul u (star u), evM_star u, evM_one (c := c) (r := r) (s := 5) (m := m)]
      with x h1 h2 h3
    have : evM u x * star (evM u x) = 1 := by rw [← h2, ← h1, hu, h3]
    exact mul_eq_one_comm.mp this
  have hent : ∀ μ ν i j, ∀ᵐ x ∂ρ, ‖wCurv (fun ν i j x => evM (embX L (a ν)) x i j)
      (fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j) μ ν i j x‖ ≤
      ‖curvVec Bf x‖ := by
    intro μ ν i j
    have hcov := curvMS_actM (s := 3) (mul_eq_one_comm.mp (mul_eq_one_comm.mp hu))
      (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ ν
    have heq : (fun κ => embX L (a κ)) =
        actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) :=
      funext fun κ => (hact κ).symm
    filter_upwards [wCurv_embX_ae L a μ ν i j, hU,
      evM_mul (rhoM (rhoM u) * curvMS (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ ν)
        (rhoM (rhoM (star u))),
      evM_mul (rhoM (rhoM u)) (curvMS (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ ν),
      evM_star u, evM_curvMS_matOfSmooth (c := c) (r := r) hB μ ν] with x h1 h2 h3 h4 h5 h6
    rw [h1, heq, hcov, h3, h4, evM_rhoM, evM_rhoM, evM_rhoM, evM_rhoM, h5, h6]
    refine (norm_conj_entry_le h2 i j).trans ?_
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    exact (le_of_eq rfl).trans (sum_slice_le (fun p => ‖curvVec Bf x p‖ ^ 2)
      (fun _ => sq_nonneg _) μ ν)
  have hE : eLpNorm (fun x => ‖curvVec Bf x‖) 2 ρ = E := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [E, ENNReal.toReal_ofNat, enorm_norm]
    congr 1
    · refine lintegral_congr fun x => ?_
      rw [← ENNReal.rpow_natCast]
      norm_num
  unfold wCurvNorm
  calc ∑ μ, ∑ ν, ∑ i, ∑ j, eLpNorm (wCurv (fun ν i j x => evM (embX L (a ν)) x i j)
        (fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j) μ ν i j) 2 ρ
      ≤ ∑ _μ : Fin 4, ∑ _ν : Fin 4, ∑ _i : Fin m, ∑ _j : Fin m,
          eLpNorm (fun x => ‖curvVec Bf x‖) 2 ρ := by
        refine Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ =>
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine eLpNorm_mono_ae ?_
        filter_upwards [hent μ ν i j] with x hx
        simpa using hx
    _ = 16 * (m : ℝ≥0∞) ^ 2 * E := by
        rw [hE]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end RenewalGeometry.BallAnalysis.AssemblyTools
