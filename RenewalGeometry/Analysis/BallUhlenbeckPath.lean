/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSmoothness

/-!
# The continuity path of Uhlenbeck's method on a ball: pre-gauged dilated connections
  (stage D3/D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `isWeakTangential_of_smooth` — a `C¹` vector field tangent to the sphere is weakly tangential
  (divergence theorem `divergence_ball`); `matOfSmooth_mem_tanM` — the corresponding Sobolev
  matrix connection lies in `tanM`;
* `gaugeConn_pregauge_mem` — the pre-gauged connection of a `𝔤`-valued connection is `𝔤`-valued
  (`exp_conj_mem`, `fderiv_exp_mul_mem`);
* `pathConn c r A t = R_t·A_t` with `A_t = dilateConn t c A`, `R_t = pregauge c r A_t`:
  `contDiff_pathConn` (**jointly smooth in `(t, x)`**), tangential on the sphere, `𝔤`-valued,
  `pathConn_zero` (trivial at `t = 0`), `pathConn_one` (gauge of `A` at `t = 1`),
  `curvEnergy_pathConn_le` (energy below that of `A` for `t ∈ (0,1]`).
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.UhlenbeckPath

open SobolevOpen BallReg BallAlg SobAlg CriticalGauge UhlenbeckGauge UhlenbeckPregauge

set_option linter.unusedSectionVars false

variable {m d : ℕ}

/-! ### Smooth tangential fields are weakly tangential -/

section Tangential

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- **A `C¹` field tangent to the sphere is weakly tangential.** -/
theorem isWeakTangential_of_smooth {X : Fin 4 → (Fin 4 → ℝ) → ℝ} (hX : ∀ ν, ContDiff ℝ 1 (X ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ ν, (y ν - c ν) * X ν y = 0) :
    IsWeakTangential c r X (fun x => ∑ ν, pd (X ν) ν x) := by
  intro φ hφ
  have hY : ∀ ν, ContDiff ℝ 1 (fun y => φ y * X ν y) := fun ν => hφ.mul (hX ν)
  have hdiv := divergence_ball c hr.out (fun ν y => φ y * X ν y) hY
  -- the boundary integrand vanishes
  have hbd : ∫ w, ∑ i, φ (c + r • w) * X i (c + r • w) * w i ∂(sphereMeasure 4) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_sphereMeasure 4] with w hw
    have hy : sqDist c (c + r • w) = r ^ 2 := by
      simp only [sqDist, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
      calc ∑ i, (r * w i) ^ 2 = r ^ 2 * ∑ i, w i ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = r ^ 2 := by rw [hw, mul_one]
    have h0 := hS _ hy
    have e : ∑ i, φ (c + r • w) * X i (c + r • w) * w i =
        φ (c + r • w) * r⁻¹ * ∑ i, ((c + r • w) i - c i) * X i (c + r • w) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
      field_simp [hr.out.ne']
    rw [e, h0, mul_zero]
    rfl
  rw [hbd, mul_zero] at hdiv
  -- expand the divergence
  have hexp : ∀ x, ∑ ν, pd (fun y => φ y * X ν y) ν x =
      ∑ ν, X ν x * pd φ ν x + (∑ ν, pd (X ν) ν x) * φ x := by
    intro x
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [pd_mul_real ((hφ.differentiable one_ne_zero) x) (((hX ν).differentiable one_ne_zero) x)]
    ring
  simp_rw [hexp] at hdiv
  have hi1 : ∀ ν, IntegrableOn (fun x => X ν x * pd φ ν x) (euclBall c r) := fun ν =>
    integrableOn_euclBall hr.out.le ((hX ν).continuous.mul (continuous_pd hφ ν))
  have hi2 : IntegrableOn (fun x => (∑ ν, pd (X ν) ν x) * φ x) (euclBall c r) :=
    integrableOn_euclBall hr.out.le ((continuous_finsetSum _ fun ν _ =>
      continuous_pd (hX ν) ν).mul hφ.continuous)
  rw [integral_add (integrable_finsetSum _ fun ν _ => hi1 ν) hi2,
    integral_finsetSum _ fun ν _ => hi1 ν] at hdiv
  linarith

/-- The Sobolev matrix connection of a smooth tangential matrix connection is tangential. -/
theorem matOfSmooth_mem_tanM {Bf : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) • Bf μ y = 0) :
    (fun μ => matOfSmooth (c := c) (r := r) 4 (Bf μ) (hB μ)) ∈ tanM (c := c) (r := r) m := by
  rw [mem_tanM]
  intro i j
  have hSre : ∀ y, sqDist c y = r ^ 2 → ∑ ν, (y ν - c ν) * (Bf ν y i j).re = 0 := by
    intro y hy
    have := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => (M i j).re) (hS y hy)
    simpa [Matrix.sum_apply, Matrix.smul_apply, Complex.re_sum] using this
  have hSim : ∀ y, sqDist c y = r ^ 2 → ∑ ν, (y ν - c ν) * (Bf ν y i j).im = 0 := by
    intro y hy
    have := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => (M i j).im) (hS y hy)
    simpa [Matrix.sum_apply, Matrix.smul_apply, Complex.im_sum] using this
  have key : ∀ (F : Fin 4 → (Fin 4 → ℝ) → ℝ) (hF : ∀ ν, ContDiff ℝ ∞ (F ν)),
      (∀ y, sqDist c y = r ^ 2 → ∑ ν, (y ν - c ν) * F ν y = 0) →
      (fun μ => ofSmooth (c := c) (r := r) (s := 4) (F μ) (hF μ)) ∈ tanSub (c := c) (r := r) := by
    intro F hF hFS
    rw [mem_tanSub]
    have h1 := isWeakTangential_of_smooth c r (fun ν => (hF ν).of_le (by simp)) hFS
    refine h1.congr_ae (fun ν => (fn_ofSmooth (hF ν)).symm) ?_
    filter_upwards [fn_divS (c := c) (r := r) (fun μ => ofSmooth (s := 4) (F μ) (hF μ)),
      ae_all_iff.mpr fun ν => (show fn (derS ν (ofSmooth (c := c) (r := r) (s := 4) (F ν) (hF ν)))
        =ᵐ[volume.restrict (euclBall c r)] pd (F ν) ν by
          rw [derS_ofSmooth]; exact fn_ofSmooth _)] with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun ν _ => (h2 ν).symm
  exact ⟨key _ (fun ν => contDiff_re_entry (hB ν) i j) hSre,
    key _ (fun ν => contDiff_im_entry (hB ν) i j) hSim⟩

end Tangential

/-! ### The pre-gauged connection is `𝔤`-valued -/

section LieValued

theorem pregaugeGen_mem (L : LieBasis m d) {c : Fin 4 → ℝ} {r : ℝ} {A : MConn m}
    (h𝔤 : ∀ μ y, A μ y ∈ L.lieAlg) (x : Fin 4 → ℝ) : pregaugeGen c r A x ∈ L.lieAlg :=
  L.lieAlg.smul_mem _ (L.lieAlg.sum_mem fun μ _ => L.lieAlg.smul_mem _ (h𝔤 μ x))

theorem pdM_eq_fderiv {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : Fin 4 → ℝ}
    (hF : DifferentiableAt ℝ F x) (μ : Fin 4) : pdM F μ x = fderiv ℝ F x (Pi.single μ 1) := by
  ext i j
  simp only [pdM, Matrix.of_apply, pd]
  have h := ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt
    (x := F x)).comp x hF.hasFDerivAt
  rw [show (fun y => F y i j) = (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℂ i j)) ∘ F from rfl, h.fderiv]
  rfl

/-- Derivatives of `𝔤`-valued smooth matrix functions are `𝔤`-valued. -/
theorem pdM_mem (L : LieBasis m d) {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ContDiff ℝ ∞ F) (hmem : ∀ y, F y ∈ L.lieAlg) (μ : Fin 4) (x : Fin 4 → ℝ) :
    pdM F μ x ∈ L.lieAlg := by
  set P : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    LinearMap.toContinuousLinearMap L.projL
  have hFP : F = P ∘ F := funext fun y => (L.projL_of_mem (hmem y)).symm
  have hd : DifferentiableAt ℝ F x := (hF.differentiable (by simp)) x
  have hcomp : fderiv ℝ (P ∘ F) x = P.comp (fderiv ℝ F x) :=
    (P.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  have e : pdM F μ x = P (fderiv ℝ F x (Pi.single μ 1)) := by
    rw [pdM_eq_fderiv hd]
    conv_lhs => rw [hFP]
    rw [hcomp]; rfl
  rw [e]
  exact L.projL_mem _

/-- **The pre-gauged connection of a `𝔤`-valued smooth unitary connection is `𝔤`-valued.** -/
theorem gaugeConn_pregauge_mem (L : LieBasis m d) {c : Fin 4 → ℝ} {r : ℝ} {A : MConn m}
    (hA : IsSmoothUnitaryConn A) (h𝔤 : ∀ μ y, A μ y ∈ L.lieAlg) (μ : Fin 4) (x : Fin 4 → ℝ) :
    gaugeConn (pregauge c r A) A μ x ∈ L.lieAlg := by
  set Ψ := pregaugeGen c r A
  have hΨ : ∀ y, Ψ y ∈ L.lieAlg := pregaugeGen_mem L h𝔤
  have hstar : star (pregauge c r A x) = exp (-Ψ x) := by
    rw [pregauge, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      ← Matrix.star_eq_conjTranspose, star_pregaugeGen hA]
  unfold gaugeConn
  rw [hstar]
  refine L.lieAlg.sub_mem ?_ ?_
  · exact L.exp_conj_mem (hΨ x) (h𝔤 μ x)
  · -- `∂R = Dexp(Ψ)[∂Ψ]`
    have hΨs : ∀ i j, ContDiff ℝ ∞ (fun y => Ψ y i j) := fun i j =>
      contDiff_entry_of_matrix (contDiff_pregaugeGen hA) i j
    have hd : pdM (pregauge c r A) μ x = fderiv ℝ exp (Ψ x) (pdM Ψ μ x) :=
      pdM_exp_comp hΨs μ x
    rw [hd]
    exact L.fderiv_exp_mul_mem (hΨ x) (pdM_mem L (contDiff_pregaugeGen hA) hΨ μ x)

end LieValued

/-! ### The continuity path -/

section Path

variable (c : Fin 4 → ℝ) (r : ℝ)

/-- **The continuity path** `t ↦ R_t·A_t`, `A_t = dilateConn t c A`, `R_t = pregauge c r A_t`. -/
def pathConn (A : MConn m) (t : ℝ) : MConn m :=
  gaugeConn (pregauge c r (dilateConn t c A)) (dilateConn t c A)

theorem dilateConn_one (A : MConn m) : dilateConn 1 c A = A := by
  funext μ y; simp [dilateConn]

theorem pathConn_zero (A : MConn m) : pathConn c r A 0 = fun _ _ => 0 :=
  pregauge_dilation_zero c r A

theorem pathConn_one (A : MConn m) :
    pathConn c r A 1 = gaugeConn (pregauge c r A) A := by
  simp [pathConn, dilateConn_one]

variable {c r}

theorem pathConn_tangential (hr : 0 < r) {A : MConn m} (hA : IsSmoothUnitaryConn A) (t : ℝ)
    {x : Fin 4 → ℝ} (hx : sqDist c x = r ^ 2) :
    ∑ μ, (x μ - c μ) • pathConn c r A t μ x = 0 :=
  pregauge_tangential hr (isSmoothUnitaryConn_dilateConn hA t c) hx

theorem dilateConn_mem (L : LieBasis m d) {A : MConn m} (h𝔤 : ∀ μ y, A μ y ∈ L.lieAlg) (t : ℝ)
    (μ : Fin 4) (y : Fin 4 → ℝ) : dilateConn t c A μ y ∈ L.lieAlg := by
  simp only [dilateConn]
  rw [show ((t : ℂ) • A μ (c + t • (y - c))) = t • A μ (c + t • (y - c)) from
    (Complex.coe_smul t _).symm]
  exact L.lieAlg.smul_mem _ (h𝔤 μ _)

theorem pathConn_mem (L : LieBasis m d) {A : MConn m} (hA : IsSmoothUnitaryConn A)
    (h𝔤 : ∀ μ y, A μ y ∈ L.lieAlg) (t : ℝ) (μ : Fin 4) (y : Fin 4 → ℝ) :
    pathConn c r A t μ y ∈ L.lieAlg :=
  gaugeConn_pregauge_mem L (isSmoothUnitaryConn_dilateConn hA t c) (dilateConn_mem L h𝔤 t) μ y

theorem curvEnergy_pathConn_le (hr : 0 < r) {A : MConn m} (hA : IsSmoothUnitaryConn A) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    curvEnergy (pathConn c r A t) (eBall c r) ≤ curvEnergy A (eBall c r) := by
  rcases ht0.eq_or_lt with h | h
  · subst h
    rw [pathConn_zero]
    have : curvEnergy (m := m) (fun _ _ => 0) (eBall c r) = 0 := by
      simp [curvEnergy, curvVec, curvatureW, entries, entryGrad, pd]
      left; rfl
    rw [this]; exact zero_le
  · exact (pregauge_dilation hr hA h ht1).2.2.2

/-! ### Joint smoothness -/

theorem contDiff_matrix_of_entries' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → Matrix (Fin m) (Fin m) ℂ} (h : ∀ a b, ContDiff ℝ ∞ (fun x => F x a b)) :
    ContDiff ℝ ∞ F := by
  have e : F = fun x => ∑ a, ∑ b, F x a b • Matrix.single a b (1 : ℂ) := by
    funext x
    conv_lhs => rw [Matrix.matrix_eq_sum_single (F x)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ => (h a b).smul contDiff_const

theorem contDiff_entry_of_matrix' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → Matrix (Fin m) (Fin m) ℂ} (h : ContDiff ℝ ∞ F) (a b : Fin m) :
    ContDiff ℝ ∞ (fun x => F x a b) :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp h

theorem pdM_param {R : ℝ × (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} (hR : ContDiff ℝ ∞ R)
    (t : ℝ) (μ : Fin 4) (x : Fin 4 → ℝ) :
    pdM (fun y => R (t, y)) μ x = fderiv ℝ R (t, x) (0, Pi.single μ 1) := by
  have h1 : HasFDerivAt (fun y : Fin 4 → ℝ => (t, y))
      ((0 : (Fin 4 → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin 4 → ℝ))) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h2 := ((hR.differentiable (by simp)) (t, x)).hasFDerivAt.comp x h1
  have h3 : HasFDerivAt (fun y => R (t, y)) ((fderiv ℝ R (t, x)).comp
      ((0 : (Fin 4 → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)))) x := h2
  rw [pdM_eq_fderiv h3.differentiableAt, h3.fderiv]
  simp

/-- **The continuity path is jointly smooth in `(t, x)`.** -/
theorem contDiff_pathConn {A : MConn m} (hA : IsSmoothUnitaryConn A) (μ : Fin 4) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => pathConn c r A p.1 μ p.2) := by
  have hAm : ∀ ν, ContDiff ℝ ∞ (A ν) := fun ν => contDiff_matrix_of_entries (hA.smooth ν)
  have haff : ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => c + p.1 • (p.2 - c)) :=
    contDiff_const.add (contDiff_fst.smul (contDiff_snd.sub contDiff_const))
  have hD : ∀ ν, ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => dilateConn p.1 c A ν p.2) := by
    intro ν
    simp only [dilateConn]
    exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul ((hAm ν).comp haff)
  have hΨ : ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => pregaugeGen c r (dilateConn p.1 c A) p.2) := by
    simp only [pregaugeGen, radComp, prof]
    refine (((contDiff_sqDist c).comp contDiff_snd).sub contDiff_const |>.div_const _).smul
      (ContDiff.sum fun ν _ => ?_)
    exact (((contDiff_apply ℝ ℝ ν).comp contDiff_snd).sub contDiff_const).smul (hD ν)
  have hR : ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => pregauge c r (dilateConn p.1 c A) p.2) :=
    contDiff_exp_matrix.comp hΨ
  have hdR : ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) =>
      pdM (pregauge c r (dilateConn p.1 c A)) μ p.2) := by
    have e : (fun p : ℝ × (Fin 4 → ℝ) => pdM (pregauge c r (dilateConn p.1 c A)) μ p.2) =
        fun p => fderiv ℝ (fun q : ℝ × (Fin 4 → ℝ) => pregauge c r (dilateConn q.1 c A) q.2) p
          (0, Pi.single μ 1) := by
      funext p
      exact pdM_param (R := fun q : ℝ × (Fin 4 → ℝ) => pregauge c r (dilateConn q.1 c A) q.2)
        hR p.1 μ p.2
    rw [e]
    exact (hR.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hstar : ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) =>
      star (pregauge c r (dilateConn p.1 c A) p.2)) :=
    (starL' ℝ : Matrix (Fin m) (Fin m) ℂ ≃L[ℝ] _).contDiff.comp hR
  simp only [pathConn, gaugeConn]
  exact ((hR.mul (hD μ)).mul hstar).sub (hdR.mul hstar)

theorem contDiff_pathConn_entry {A : MConn m} (hA : IsSmoothUnitaryConn A) (μ : Fin 4)
    (a b : Fin m) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => pathConn c r A p.1 μ p.2 a b) :=
  contDiff_entry_of_matrix' (contDiff_pathConn hA μ) a b

theorem contDiff_pathConn_slice {A : MConn m} (hA : IsSmoothUnitaryConn A) (t : ℝ) (μ : Fin 4)
    (a b : Fin m) : ContDiff ℝ ∞ (fun x => pathConn c r A t μ x a b) := by
  have h1 : ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => ((t, x) : ℝ × (Fin 4 → ℝ))) :=
    contDiff_const.prodMk contDiff_id
  have h2 := (contDiff_pathConn_entry (c := c) (r := r) hA μ a b).comp h1
  have e : (fun x => pathConn c r A t μ x a b) =
      (fun p : ℝ × (Fin 4 → ℝ) => pathConn c r A p.1 μ p.2 a b) ∘ fun x => (t, x) := by
    funext x; simp only [Function.comp_apply]
  rw [e]; exact h2

end Path

end RenewalGeometry.BallAnalysis.UhlenbeckPath
