/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.UhlenbeckGaugeTheorem
import RenewalGeometry.Analysis.UhlenbeckCurvatureCovariance
import RenewalGeometry.Analysis.BallDivergence

/-!
# A boundary-adapted pre-gauge for Uhlenbeck's continuity method on a ball
  (stage D0 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic gauge-theory infrastructure (no renewal notions) for `prop:critical-uhlenbeck` and
`thm:critical-quotient-defect` of the Einstein–Standard-Model action-closure manuscript.

Uhlenbeck's Coulomb gauge on a ball `B_r(c)` is the solution of the nonlinear Neumann problem
`d^*(u·A) = 0` in `B`, `(x - c)·(u·A) = 0` on `∂B`.  For a gauge `u = 1` on the sphere the boundary
condition reads `(x - c)·A = (x - c)·∇u`, i.e. it is **inhomogeneous** unless `A` is tangential.
The classical way to make it homogeneous is the radial (exponential) gauge, which requires the
smooth dependence of solutions of linear ODEs on parameters.  Here we use instead an explicit
**boundary-adapted pre-gauge**, which suffices because the boundary condition only involves the
first-order jet of the gauge on the sphere:

  `R = exp Ψ`,   `Ψ(x) = ((|x - c|² - r²) / (2r²)) · Σ_μ (x_μ - c_μ) A_μ(x)`.

* `pregaugeGen`, `pregauge` — the generator and the pre-gauge (no ODE);
* `contDiff_pregauge_entry` — smoothness (the exponential is analytic);
* `pregauge_unitary` — `R` is unitary (`Ψ` is skew-Hermitian), `pregauge_mem` — `R ∈ G` when
  `A` takes values in a real subspace `𝔤` with `exp 𝔤 ⊆ G`;
* `pregauge_eq_one_on_sphere` — `R = 1` on the sphere;
* `pregauge_tangential` (**main result**) — `Σ_μ (x_μ - c_μ) (R·A)_μ(x) = 0` on the sphere: the
  pre-gauged connection is tangential, so the Neumann condition for the Coulomb gauge of `R·A`
  is the homogeneous `∂_ν u = 0`;
* `pregauge_dilation` — along the dilation path `A_t = dilateConn t c A` (energy non-increasing,
  `A_0 = 0`), the pre-gauged connections `R_t·A_t` are tangential, start at `0` and have the same
  curvature energy as `A_t` (gauge invariance).
-/

open MeasureTheory Filter Topology Set Matrix NormedSpace
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.UhlenbeckPregauge

open SobolevOpen CriticalGauge BallAnalysis UhlenbeckGauge

set_option linter.unusedSectionVars false

variable {m : ℕ}

/-- The radial component `ι_{x-c}A = Σ_μ (x_μ - c_μ) A_μ(x)`. -/
def radComp (c : Fin 4 → ℝ) (A : MConn m) (x : Fin 4 → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ μ, (x μ - c μ) • A μ x

/-- The boundary profile `φ(x) = (|x - c|² - r²)/(2r²)`: zero on the sphere, with
`(x - c)·∇φ = 1` there. -/
def prof (c : Fin 4 → ℝ) (r : ℝ) (x : Fin 4 → ℝ) : ℝ := (sqDist c x - r ^ 2) / (2 * r ^ 2)

/-- The generator `Ψ = φ · ι_{x-c}A` of the pre-gauge. -/
def pregaugeGen (c : Fin 4 → ℝ) (r : ℝ) (A : MConn m) (x : Fin 4 → ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  prof c r x • radComp c A x

/-- **The boundary-adapted pre-gauge** `R = exp Ψ`. -/
def pregauge (c : Fin 4 → ℝ) (r : ℝ) (A : MConn m) (x : Fin 4 → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  exp (pregaugeGen c r A x)

theorem prof_eq_zero {c x : Fin 4 → ℝ} {r : ℝ} (hx : sqDist c x = r ^ 2) : prof c r x = 0 := by
  simp [prof, hx]

theorem pregaugeGen_eq_zero {c x : Fin 4 → ℝ} {r : ℝ} (A : MConn m) (hx : sqDist c x = r ^ 2) :
    pregaugeGen c r A x = 0 := by
  simp [pregaugeGen, prof_eq_zero hx]

theorem pregauge_eq_one_on_sphere {c x : Fin 4 → ℝ} {r : ℝ} (A : MConn m)
    (hx : sqDist c x = r ^ 2) : pregauge c r A x = 1 := by
  simp [pregauge, pregaugeGen_eq_zero A hx]

/-! ### Unitarity and structure group -/

theorem star_pregaugeGen {c : Fin 4 → ℝ} {r : ℝ} {A : MConn m} (hA : IsSmoothUnitaryConn A)
    (x : Fin 4 → ℝ) : star (pregaugeGen c r A x) = -pregaugeGen c r A x := by
  simp only [pregaugeGen, radComp, star_smul, star_sum, hA.skew, smul_neg, Finset.sum_neg_distrib,
    star_trivial]

/-- The pre-gauge is unitary. -/
theorem pregauge_unitary {c : Fin 4 → ℝ} {r : ℝ} {A : MConn m} (hA : IsSmoothUnitaryConn A)
    (x : Fin 4 → ℝ) : pregauge c r A x ∈ unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h1 : star (pregauge c r A x) = exp (-pregaugeGen c r A x) := by
    rw [pregauge, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      ← Matrix.star_eq_conjTranspose, star_pregaugeGen hA]
  rw [h1, pregauge, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))

/-- The pre-gauge takes values in the structure group when the connection takes values in a real
subspace `𝔤` with `exp 𝔤 ⊆ G`. -/
theorem pregauge_mem {c : Fin 4 → ℝ} {r : ℝ} {A : MConn m}
    (𝔤 : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ)) (h𝔤 : ∀ μ y, A μ y ∈ 𝔤)
    {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hexp : ∀ X ∈ 𝔤, exp X ∈ G) (x : Fin 4 → ℝ) :
    pregauge c r A x ∈ G := by
  refine hexp _ ?_
  exact 𝔤.smul_mem _ (𝔤.sum_mem fun μ _ => 𝔤.smul_mem _ (h𝔤 μ x))

/-! ### Smoothness -/

section Smooth

open scoped Matrix.Norms.Operator

theorem contDiff_matrix_of_entries {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ a b, ContDiff ℝ ∞ (fun x => F x a b)) : ContDiff ℝ ∞ F := by
  have e : F = fun x => ∑ a, ∑ b, F x a b • Matrix.single a b (1 : ℂ) := by
    funext x
    conv_lhs => rw [Matrix.matrix_eq_sum_single (F x)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ => (h a b).smul contDiff_const

theorem contDiff_entry_of_matrix {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (h : ContDiff ℝ ∞ F) (a b : Fin m) : ContDiff ℝ ∞ (fun x => F x a b) :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp h

theorem contDiff_exp_matrix : ContDiff ℝ ∞ (exp : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) :=
  contDiff_iff_contDiffAt.mpr fun X => (exp_analytic (𝕂 := ℝ) X).contDiffAt

theorem contDiff_pregaugeGen {c : Fin 4 → ℝ} {r : ℝ} {A : MConn m} (hA : IsSmoothUnitaryConn A) :
    ContDiff ℝ ∞ (pregaugeGen c r A) := by
  refine contDiff_matrix_of_entries fun a b => ?_
  have e : (fun x => pregaugeGen c r A x a b) =
      fun x => (prof c r x : ℂ) * ∑ μ, ((x μ - c μ : ℝ) : ℂ) * A μ x a b := by
    funext x
    simp only [pregaugeGen, radComp, Matrix.smul_apply, Matrix.sum_apply, Finset.smul_sum,
      Complex.real_smul, Finset.mul_sum]
  rw [e]
  have hp : ContDiff ℝ ∞ (fun x => (prof c r x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (((contDiff_sqDist c).sub contDiff_const).div_const _)
  refine hp.mul (ContDiff.sum fun μ _ => ?_)
  exact (Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ μ).sub contDiff_const)).mul
    (hA.smooth μ a b)

/-- **The pre-gauge is smooth.** -/
theorem contDiff_pregauge {c : Fin 4 → ℝ} {r : ℝ} {A : MConn m} (hA : IsSmoothUnitaryConn A) :
    ContDiff ℝ ∞ (pregauge c r A) :=
  contDiff_exp_matrix.comp (contDiff_pregaugeGen hA)

theorem contDiff_pregauge_entry {c : Fin 4 → ℝ} {r : ℝ} {A : MConn m}
    (hA : IsSmoothUnitaryConn A) (a b : Fin m) : ContDiff ℝ ∞ (fun x => pregauge c r A x a b) :=
  contDiff_entry_of_matrix (contDiff_pregauge hA) a b

/-- Derivative of the entries of the pre-gauge along `x - c` at a point of the sphere. -/
theorem hasDerivAt_pregauge_radial {c : Fin 4 → ℝ} {r : ℝ} (hr : 0 < r) {A : MConn m}
    (hA : IsSmoothUnitaryConn A) {x : Fin 4 → ℝ} (hx : sqDist c x = r ^ 2) (a b : Fin m) :
    HasDerivAt (fun s : ℝ => pregauge c r A (x + s • (x - c)) a b) (radComp c A x a b) 0 := by
  set v := x - c
  -- the profile along the ray
  have hprof : HasDerivAt (fun s : ℝ => prof c r (x + s • v)) 1 0 := by
    have e : (fun s : ℝ => prof c r (x + s • v)) =
        fun s => ((1 + s) ^ 2 * r ^ 2 - r ^ 2) / (2 * r ^ 2) := by
      funext s
      simp only [prof, sqDist]
      congr 1
      have : ∑ i, ((x + s • v) i - c i) ^ 2 = (1 + s) ^ 2 * ∑ i, (x i - c i) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [this]
      have hx' : ∑ i, (x i - c i) ^ 2 = r ^ 2 := hx
      rw [hx']
    rw [e]
    have h1 := ((((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2).mul_const (r ^ 2)).sub_const
      (r ^ 2) |>.div_const (2 * r ^ 2)
    refine h1.congr_deriv ?_
    simp only [id, add_zero, one_pow]
    field_simp
    norm_num
  have hrc : ContDiff ℝ ∞ (fun y => radComp c A y) := by
    refine contDiff_matrix_of_entries fun a b => ?_
    have e : (fun y => radComp c A y a b) = fun y => ∑ μ, ((y μ - c μ : ℝ) : ℂ) * A μ y a b := by
      funext y; simp [radComp, Matrix.sum_apply, Complex.real_smul]
    rw [e]
    exact ContDiff.sum fun μ _ => (Complex.ofRealCLM.contDiff.comp
      ((contDiff_apply ℝ ℝ μ).sub contDiff_const)).mul (hA.smooth μ a b)
  have hW : DifferentiableAt ℝ (fun s : ℝ => radComp c A (x + s • v)) 0 :=
    ((hrc.differentiable (by simp)) _).comp 0 (by fun_prop)
  have hprof0 : prof c r (x + (0 : ℝ) • v) = 0 := by
    simp only [zero_smul, add_zero]; exact prof_eq_zero hx
  have hg : HasDerivAt (fun s : ℝ => pregaugeGen c r A (x + s • v)) (radComp c A x) 0 := by
    have := hprof.smul hW.hasDerivAt
    refine this.congr_deriv ?_
    rw [hprof0, zero_smul, zero_add, one_smul, zero_smul, add_zero]
  have h0 : pregaugeGen c r A (x + (0 : ℝ) • v) = 0 := by
    simp only [zero_smul, add_zero]; exact pregaugeGen_eq_zero A hx
  have hexp : HasFDerivAt (exp : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ)
      (1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ)
      (pregaugeGen c r A (x + (0 : ℝ) • v)) := by
    rw [h0]; exact hasFDerivAt_exp_zero
  have hR : HasDerivAt (fun s : ℝ => pregauge c r A (x + s • v)) (radComp c A x) 0 := by
    exact hexp.comp_hasDerivAt (0 : ℝ) hg
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hR

end Smooth

/-- Directional derivatives of complex-valued functions as sums of partials. -/
theorem fderiv_apply_eq_sum_pd_C {f : (Fin 4 → ℝ) → ℂ} (x v : Fin 4 → ℝ) :
    fderiv ℝ f x v = ∑ μ, (v μ : ℂ) * pd f μ x := by
  conv_lhs => rw [show v = ∑ μ, v μ • Pi.single μ (1 : ℝ) by
    funext i; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, Complex.real_smul]
  rfl

/-- **The pre-gauged connection is tangential on the sphere**:
`Σ_μ (x_μ - c_μ) (R·A)_μ(x) = 0` for `|x - c| = r`. -/
theorem pregauge_tangential {c : Fin 4 → ℝ} {r : ℝ} (hr : 0 < r) {A : MConn m}
    (hA : IsSmoothUnitaryConn A) {x : Fin 4 → ℝ} (hx : sqDist c x = r ^ 2) :
    ∑ μ, (x μ - c μ) • gaugeConn (pregauge c r A) A μ x = 0 := by
  have hR1 : pregauge c r A x = 1 := pregauge_eq_one_on_sphere A hx
  have hpd : ∑ μ, (x μ - c μ) • pdM (pregauge c r A) μ x = radComp c A x := by
    ext a b
    have hdiff : DifferentiableAt ℝ (fun y => pregauge c r A y a b) x :=
      ((contDiff_pregauge_entry hA a b).differentiable (by simp)) x
    -- the derivative along the ray
    have h2 := hasDerivAt_pregauge_radial hr hA hx a b
    have h3 : HasDerivAt (fun s : ℝ => pregauge c r A (x + s • (x - c)) a b)
        (fderiv ℝ (fun y => pregauge c r A y a b) x (x - c)) 0 := by
      have hray : HasDerivAt (fun s : ℝ => x + s • (x - c)) (x - c) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).smul_const (x - c)).const_add x
        simpa using this
      have hd' : DifferentiableAt ℝ (fun y => pregauge c r A y a b) (x + (0 : ℝ) • (x - c)) := by
        simpa using hdiff
      have := hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hray
      rw [show x + (0 : ℝ) • (x - c) = x by simp] at this
      exact this
    have heq := h3.unique h2
    rw [fderiv_apply_eq_sum_pd_C] at heq
    simp only [Matrix.sum_apply, Matrix.smul_apply, pdM, Matrix.of_apply, Complex.real_smul]
    rw [← heq]
    simp only [Pi.sub_apply]
  simp only [gaugeConn, hR1, star_one, mul_one, one_mul, smul_sub, Finset.sum_sub_distrib]
  rw [hpd]
  simp [radComp]

/-! ### The pre-gauged dilation path -/

theorem pregauge_zero_conn (c : Fin 4 → ℝ) (r : ℝ) :
    gaugeConn (pregauge c r (fun _ _ => (0 : Matrix (Fin m) (Fin m) ℂ)))
      (fun _ _ => (0 : Matrix (Fin m) (Fin m) ℂ)) = fun _ _ => 0 := by
  have hR : pregauge c r (fun _ _ => (0 : Matrix (Fin m) (Fin m) ℂ)) = fun _ => 1 := by
    funext x; simp [pregauge, pregaugeGen, radComp]
  funext μ x
  rw [hR]
  simp only [gaugeConn, mul_zero, zero_mul, zero_sub, neg_eq_zero]
  ext a b
  simp [pdM, pd]

/-- **The pre-gauged continuity path** (stage D0): along the dilation path
`A_t = dilateConn t c A` (`0 < t ≤ 1`), the pre-gauged connections `b_t = R_t·A_t`
(`R_t = pregauge c r A_t`, smooth and unitary) are tangential on the sphere `|x - c| = r`, have
curvature energy on `B_r(c)` at most that of `A`, and `b_0 = 0`. -/
theorem pregauge_dilation {c : Fin 4 → ℝ} {r : ℝ} (hr : 0 < r) {A : MConn m}
    (hA : IsSmoothUnitaryConn A) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∀ y, pregauge c r (dilateConn t c A) y ∈ unitaryGroup (Fin m) ℂ) ∧
    (∀ a b, ContDiff ℝ ∞ (fun y => pregauge c r (dilateConn t c A) y a b)) ∧
    (∀ x, sqDist c x = r ^ 2 →
      ∑ μ, (x μ - c μ) • gaugeConn (pregauge c r (dilateConn t c A)) (dilateConn t c A) μ x = 0) ∧
    curvEnergy (gaugeConn (pregauge c r (dilateConn t c A)) (dilateConn t c A)) (eBall c r) ≤
      curvEnergy A (eBall c r) := by
  have hAt := UhlenbeckGauge.isSmoothUnitaryConn_dilateConn hA t c
  refine ⟨pregauge_unitary hAt, contDiff_pregauge_entry hAt, fun x hx => pregauge_tangential hr hAt hx,
    ?_⟩
  rw [CurvatureCovariance.curvEnergy_gaugeConn (isOpen_eBall c r) (fun y _ => pregauge_unitary hAt y)
    (fun a b => ((contDiff_pregauge_entry hAt a b).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).contDiffOn) hAt]
  exact UhlenbeckGauge.curvEnergy_dilateConn_le hA ht0 ht1 c r

/-- At `t = 0` the pre-gauged path starts at the trivial connection. -/
theorem pregauge_dilation_zero (c : Fin 4 → ℝ) (r : ℝ) (A : MConn m) :
    gaugeConn (pregauge c r (dilateConn 0 c A)) (dilateConn 0 c A) = fun _ _ => 0 := by
  rw [UhlenbeckGauge.dilateConn_zero]
  exact pregauge_zero_conn c r

/-- Non-vacuity: the pre-gauge of the zero connection is the identity. -/
example (c : Fin 4 → ℝ) (r : ℝ) (x : Fin 4 → ℝ) :
    pregauge (m := 2) c r (fun _ _ => 0) x = 1 := by
  simp [pregauge, pregaugeGen, radComp]

end RenewalGeometry.UhlenbeckPregauge
