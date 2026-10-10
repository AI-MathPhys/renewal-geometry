/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalGaugeEstimates

/-!
# Gauge covariance of the curvature: `F_{R·A} = R F_A R^*`
  (stage D support for Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

For a matrix-valued connection `A` and a gauge `R`, `C²` and unitary near a point `x`,
the gauge-transformed connection `R·A = R A R^* - (∂R) R^*` (`gaugeConn`) has curvature
`F_{R·A}(x) = R(x) F_A(x) R(x)^*` (`curvM_gaugeConn`).  Ingredients: the product rule for matrix
functions (`pdM_mul`), symmetry of second derivatives of `C²` functions (`pdM_pdM_symm`, Schwarz,
Mathlib's `ContDiffAt.isSymmSndFDerivAt`), and the derivative of unitarity
`(∂R)^* = -R^* (∂R) R^*` (`star_pdM_of_unitary`).

* `curvM`: the matrix curvature `∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]`; `curvatureW_eq_curvM`;
* `curvM_gaugeConn` (**gauge covariance**).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.CurvatureCovariance

open SobolevOpen CriticalGauge

set_option linter.unusedSectionVars false

variable {m : ℕ}

/-- The matrix curvature `F_{μν} = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]`. -/
def curvM (A : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ) (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  pdM (A ν) μ x - pdM (A μ) ν x + (A μ x * A ν x - A ν x * A μ x)

theorem curvatureW_eq_curvM (A : MConn m) (μ ν : Fin 4) (c e : Fin m) (x : Fin 4 → ℝ) :
    curvatureW (entries A) (entryGrad A) μ ν c e x = curvM A μ ν x c e := by
  simp only [curvatureW, curvM, entries, entryGrad, pdM, Matrix.add_apply, Matrix.sub_apply,
    Matrix.of_apply, Matrix.mul_apply, Finset.sum_sub_distrib]

theorem pdM_sub {R S : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : Fin 4 → ℝ}
    (hR : MDiffAt R x) (hS : MDiffAt S x) (μ : Fin 4) :
    pdM (fun y => R y - S y) μ x = pdM R μ x - pdM S μ x := by
  ext c e
  simp only [pdM, Matrix.of_apply, Matrix.sub_apply]
  exact pd_sub_complex (hR c e) (hS c e) μ

theorem MDiffAt.sub {R S : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : Fin 4 → ℝ}
    (hR : MDiffAt R x) (hS : MDiffAt S x) : MDiffAt (fun y => R y - S y) x := fun c e => by
  simp only [Matrix.sub_apply]; exact (hR c e).sub (hS c e)

/-- `C²` entries give differentiable first partials. -/
theorem mdiffAt_pdM {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : Fin 4 → ℝ}
    (hR : ∀ c e, ContDiffAt ℝ 2 (fun y => R y c e) x) (ν : Fin 4) : MDiffAt (pdM R ν) x := by
  intro c e
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fun y => R y c e)) x := (hR c e).fderiv_right (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ (fun y => R y c e)) x := h1.differentiableAt one_ne_zero
  simp only [pdM, Matrix.of_apply, pd]
  exact h2.clm_apply (differentiableAt_const _)

/-- **Symmetry of mixed partials** (Schwarz) for `C²` matrix functions. -/
theorem pdM_pdM_symm {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : Fin 4 → ℝ}
    (hR : ∀ c e, ContDiffAt ℝ 2 (fun y => R y c e) x) (μ ν : Fin 4) :
    pdM (pdM R ν) μ x = pdM (pdM R μ) ν x := by
  ext c e
  simp only [pdM, Matrix.of_apply]
  set f : (Fin 4 → ℝ) → ℂ := fun y => R y c e
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := (hR c e).fderiv_right (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) x := h1.differentiableAt one_ne_zero
  have hsymm := (hR c e).isSymmSndFDerivAt (by simp)
  have key : ∀ v w : Fin 4 → ℝ,
      fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    intro v w
    rw [fderiv_clm_apply h2 (differentiableAt_const v)]
    simp
  show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single ν 1)) x (Pi.single μ 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single μ 1)) x (Pi.single ν 1)
  rw [key, key]
  exact hsymm _ _

/-- **Derivative of unitarity**: if `R` is unitary near `x` and differentiable at `x`, then
`(∂_μ R)^* = -R^* (∂_μ R) R^*` at `x`. -/
theorem star_pdM_of_unitary {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : Fin 4 → ℝ}
    (hRu : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin m) ℂ) (hR : MDiffAt R x) (μ : Fin 4) :
    star (pdM R μ x) = -(star (R x) * pdM R μ x * star (R x)) := by
  have hev : (fun y => R y * star (R y)) =ᶠ[𝓝 x] fun _ => 1 :=
    hRu.mono fun y hy => Matrix.mem_unitaryGroup_iff.mp hy
  have h0 : pdM (fun y => R y * star (R y)) μ x = 0 := by
    ext c e
    simp only [pdM, Matrix.of_apply, Matrix.zero_apply, pd]
    have : (fun y => (R y * star (R y)) c e) =ᶠ[𝓝 x] fun _ => (1 : Matrix (Fin m) (Fin m) ℂ) c e :=
      hev.mono fun y hy => by
        change (R y * star (R y)) c e = (1 : Matrix (Fin m) (Fin m) ℂ) c e
        rw [show R y * star (R y) = 1 from hy]
    rw [this.fderiv_eq]; simp
  rw [pdM_mul hR hR.star, pdM_star hR] at h0
  have hsu : star (R x) * R x = 1 := Matrix.mem_unitaryGroup_iff'.mp hRu.self_of_nhds
  have h1 : star (R x) * (pdM R μ x * star (R x) + R x * star (pdM R μ x)) = 0 := by rw [h0, mul_zero]
  rw [mul_add, ← Matrix.mul_assoc (star (R x)) (R x), hsu, Matrix.one_mul] at h1
  rw [← Matrix.mul_assoc] at h1
  exact eq_neg_of_add_eq_zero_right h1

/-- **Gauge covariance of the curvature**: for `R` unitary near `x` with `C²` entries at `x` and
`A` differentiable at `x`, `F_{R·A}(x) = R(x) F_A(x) R(x)^*`. -/
theorem curvM_gaugeConn {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    {A : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : Fin 4 → ℝ}
    (hRu : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin m) ℂ)
    (hR2 : ∀ c e, ContDiffAt ℝ 2 (fun y => R y c e) x) (hA : ∀ μ, MDiffAt (A μ) x)
    (μ ν : Fin 4) :
    curvM (gaugeConn R A) μ ν x = R x * curvM A μ ν x * star (R x) := by
  have hR : MDiffAt R x := fun c e => (hR2 c e).differentiableAt (by norm_num)
  have hRs : MDiffAt (fun y => star (R y)) x := hR.star
  have hpR : ∀ κ, MDiffAt (pdM R κ) x := mdiffAt_pdM hR2
  -- derivatives of the two pieces of `R·A`
  have hd1 : ∀ κ l, pdM (fun y => R y * A κ y * star (R y)) l x =
      pdM R l x * A κ x * star (R x) + R x * pdM (A κ) l x * star (R x) +
        R x * A κ x * star (pdM R l x) := by
    intro κ l
    rw [pdM_mul (hR.mul (hA κ)) hRs, pdM_mul hR (hA κ), pdM_star hR]
    noncomm_ring
  have hd2 : ∀ κ l, pdM (fun y => pdM R κ y * star (R y)) l x =
      pdM (pdM R κ) l x * star (R x) + pdM R κ x * star (pdM R l x) := by
    intro κ l
    rw [pdM_mul (hpR κ) hRs, pdM_star hR]
  have hdB : ∀ κ l, pdM (gaugeConn R A κ) l x =
      pdM R l x * A κ x * star (R x) + R x * pdM (A κ) l x * star (R x) +
        R x * A κ x * star (pdM R l x) -
        (pdM (pdM R κ) l x * star (R x) + pdM R κ x * star (pdM R l x)) := by
    intro κ l
    have e : gaugeConn R A κ = fun y => R y * A κ y * star (R y) - pdM R κ y * star (R y) := rfl
    rw [e, pdM_sub ((hR.mul (hA κ)).mul hRs) ((hpR κ).mul hRs), hd1, hd2]
  simp only [curvM]
  rw [hdB, hdB, pdM_pdM_symm hR2 μ ν]
  have hsμ := star_pdM_of_unitary hRu hR μ
  have hsν := star_pdM_of_unitary hRu hR ν
  rw [hsμ, hsν]
  have hsu : star (R x) * R x = 1 := Matrix.mem_unitaryGroup_iff'.mp hRu.self_of_nhds
  have hsu' : ∀ Z : Matrix (Fin m) (Fin m) ℂ, star (R x) * (R x * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hsu, Matrix.one_mul]
  simp only [gaugeConn]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, Matrix.mul_assoc, hsu']
  noncomm_ring

/-! ### Invariance of the curvature energy -/

theorem sum_norm_sq_entries (X : Matrix (Fin m) (Fin m) ℂ) :
    ∑ c, ∑ e, ‖X c e‖ ^ 2 = (Matrix.trace (Xᴴ * X)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Unitary conjugation preserves the Frobenius norm.** -/
theorem sum_norm_sq_conj_unitary {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ unitaryGroup (Fin m) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    ∑ c, ∑ e, ‖(U * M * star U) c e‖ ^ 2 = ∑ c, ∑ e, ‖M c e‖ ^ 2 := by
  rw [sum_norm_sq_entries, sum_norm_sq_entries]
  have hsu : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have e1 : (U * M * star U)ᴴ * (U * M * star U) = U * (Mᴴ * M) * star U := by
    have hsu' : ∀ Z : Matrix (Fin m) (Fin m) ℂ, star U * (U * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, hsu, Matrix.one_mul]
    rw [← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star]
    simp only [Matrix.mul_assoc]
    rw [hsu']
    simp only [Matrix.star_eq_conjTranspose]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hsu, Matrix.one_mul]

theorem norm_sq_curvVec (A : MConn m) (x : Fin 4 → ℝ) :
    ‖curvVec A x‖ ^ 2 = ∑ μ, ∑ ν, ∑ c, ∑ e, ‖curvM A μ ν x c e‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  simp only [curvVec, PiLp.toLp_apply, curvatureW_eq_curvM, Fintype.sum_prod_type]

/-- **Pointwise invariance of `|F|` under `C²` unitary gauges.** -/
theorem norm_curvVec_gaugeConn {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {A : MConn m}
    {x : Fin 4 → ℝ} (hRu : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin m) ℂ)
    (hR2 : ∀ c e, ContDiffAt ℝ 2 (fun y => R y c e) x) (hA : ∀ μ, MDiffAt (A μ) x) :
    ‖curvVec (gaugeConn R A) x‖ = ‖curvVec A x‖ := by
  have h : ‖curvVec (gaugeConn R A) x‖ ^ 2 = ‖curvVec A x‖ ^ 2 := by
    rw [norm_sq_curvVec, norm_sq_curvVec]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [curvM_gaugeConn hRu hR2 hA μ ν]
    exact sum_norm_sq_conj_unitary hRu.self_of_nhds _
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **Gauge invariance of the curvature energy** on an open set where the gauge is `C²` and
unitary. -/
theorem curvEnergy_gaugeConn {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {A : MConn m}
    {S : Set (Fin 4 → ℝ)} (hS : IsOpen S) (hRu : ∀ y ∈ S, R y ∈ unitaryGroup (Fin m) ℂ)
    (hR2 : ∀ c e, ContDiffOn ℝ 2 (fun y => R y c e) S) (hA : IsSmoothUnitaryConn A) :
    curvEnergy (gaugeConn R A) S = curvEnergy A S := by
  unfold curvEnergy
  refine setLIntegral_congr_fun hS.measurableSet fun x hx => ?_
  have hev : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin m) ℂ :=
    Filter.mem_of_superset (hS.mem_nhds hx) fun y hy => hRu y hy
  have hR2' : ∀ c e, ContDiffAt ℝ 2 (fun y => R y c e) x := fun c e =>
    (hR2 c e).contDiffAt (hS.mem_nhds hx)
  have hAd : ∀ μ, MDiffAt (A μ) x := fun μ c e =>
    ((hA.smooth μ c e).differentiable (by simp)) x
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_curvVec_gaugeConn hev hR2' hAd]

end RenewalGeometry.CurvatureCovariance
