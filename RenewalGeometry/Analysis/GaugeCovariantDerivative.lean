/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.KatoInequalitySobolev

/-!
# Gauge covariance of covariant derivatives and unitary invariance of test sizes

Generic finite-dimensional fibre algebra (no renewal notions) for the invariance identity
`eq:equivariant-test-invariance` of `lem:equivariant-tests` (Einstein–Standard-Model
action-closure manuscript).

A gauge transformation of a rank-`m` Hermitian bundle (trivialised over `ℝ^ι`) is a
differentiable map `R : ℝ^ι → U(m)` (`Matrix.unitaryGroup`).  For a matrix-valued connection
`𝒜_μ(x)` and a section `η`:

* `covDerV 𝒜 η μ = ∂_μ η + 𝒜_μ η` (fundamental representation);
* `covDerAd 𝒜 a μ = ∂_μ a + [𝒜_μ, a]` (adjoint representation, `a` matrix-valued);
* `gaugeConn R 𝒜 = R 𝒜 R⁻¹ - (∂R) R⁻¹` (`R⁻¹ = R^*`), the gauge-transformed connection.

Main results:

* `pdV_mulVec`, `pdM_mul`: product rules for matrix–vector and matrix–matrix products;
* `pdM_unitary` (`∂R R^* + R ∂R^* = 0` for unitary-valued `R`);
* `covDerV_gauge` (**covariance, fundamental**): `∇^{R·𝒜}(R η) = R ∇^𝒜 η`;
* `covDerAd_gauge` (**covariance, adjoint**): `D_{R·𝒜}(R a R^*) = R (D_𝒜 a) R^*`;
* `covDerV_gauge_dual` (**covariance, dual**): for the dual connection `-𝒜ᵀ` and the dual
  action `η̄ ↦ η̄ R^*`, `(R̄ η̄)` with `R̄ = conj R`;
* `fibreNorm_mulVec_unitary`, `frobNorm_conj_unitary`: unitary invariance of the Hermitian
  fibre norm and of the Frobenius norm;
* `vecTestSize_gauge`, `adTestSize_gauge`: the sector test sizes
  `‖η‖_{L^∞} + Σ_μ ‖∇_μ η‖_{L²}` are **exactly gauge invariant**.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-! ### Scalar calculus for complex-valued functions -/

theorem pd_mul_complex {f g : (ι → ℝ) → ℂ} {x : ι → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : ι) :
    pd (fun y => f y * g y) μ x = pd f μ x * g x + f x * pd g μ x := by
  unfold pd
  rw [show (fun y => f y * g y) = f * g from rfl, (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pd_sum_complex {κ : Type*} {s : Finset κ} {F : κ → (ι → ℝ) → ℂ} {x : ι → ℝ}
    (h : ∀ k ∈ s, DifferentiableAt ℝ (F k) x) (μ : ι) :
    pd (fun y => ∑ k ∈ s, F k y) μ x = ∑ k ∈ s, pd (F k) μ x := by
  unfold pd
  have hs := HasFDerivAt.sum (u := s) fun k hk => (h k hk).hasFDerivAt
  rw [show (fun y => ∑ k ∈ s, F k y) = ∑ k ∈ s, F k from by funext y; simp [Finset.sum_apply],
    hs.fderiv]
  simp

theorem pd_sub_complex {f g : (ι → ℝ) → ℂ} {x : ι → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : ι) :
    pd (fun y => f y - g y) μ x = pd f μ x - pd g μ x := by
  unfold pd
  rw [show (fun y => f y - g y) = f - g from rfl, (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  rfl

theorem pd_conj_complex {f : (ι → ℝ) → ℂ} {x : ι → ℝ} (hf : DifferentiableAt ℝ f x) (μ : ι) :
    pd (fun y => conj (f y)) μ x = conj (pd f μ x) := by
  unfold pd
  have := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := f x)).comp x hf.hasFDerivAt
  rw [show (fun y => conj (f y)) = Complex.conjCLE.toContinuousLinearMap ∘ f from rfl,
    this.fderiv]
  rfl

theorem pd_const_complex (z : ℂ) (μ : ι) (x : ι → ℝ) : pd (fun _ : ι → ℝ => z) μ x = 0 := by
  simp [pd]

/-! ### Matrix and vector derivatives -/

/-- Entrywise partial derivative of a matrix-valued function. -/
def pdM (R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) (μ : ι) (x : ι → ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun c e => pd (fun y => R y c e) μ x

/-- Componentwise partial derivative of a vector-valued function. -/
def pdV (η : (ι → ℝ) → Fin m → ℂ) (μ : ι) (x : ι → ℝ) : Fin m → ℂ :=
  fun c => pd (fun y => η y c) μ x

/-- Entrywise differentiability of a matrix-valued function. -/
def MDiffAt (R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) (x : ι → ℝ) : Prop :=
  ∀ c e, DifferentiableAt ℝ (fun y => R y c e) x

/-- Componentwise differentiability of a vector-valued function. -/
def VDiffAt (η : (ι → ℝ) → Fin m → ℂ) (x : ι → ℝ) : Prop :=
  ∀ c, DifferentiableAt ℝ (fun y => η y c) x

theorem VDiffAt.mulVec {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ} {η : (ι → ℝ) → Fin m → ℂ}
    {x : ι → ℝ} (hR : MDiffAt R x) (hη : VDiffAt η x) : VDiffAt (fun y => R y *ᵥ η y) x := by
  intro c
  simp only [Matrix.mulVec, dotProduct]
  exact DifferentiableAt.fun_sum fun e _ => (hR c e).mul (hη e)

theorem MDiffAt.mul {R S : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : ι → ℝ} (hR : MDiffAt R x)
    (hS : MDiffAt S x) : MDiffAt (fun y => R y * S y) x := by
  intro c e
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (hR c k).mul (hS k e)

theorem MDiffAt.star {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : ι → ℝ} (hR : MDiffAt R x) :
    MDiffAt (fun y => star (R y)) x := by
  intro c e
  simp only [Matrix.star_apply]
  exact (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp x (hR e c)

/-- Product rule `∂(R η) = ∂R η + R ∂η`. -/
theorem pdV_mulVec {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ} {η : (ι → ℝ) → Fin m → ℂ}
    {x : ι → ℝ} (hR : MDiffAt R x) (hη : VDiffAt η x) (μ : ι) :
    pdV (fun y => R y *ᵥ η y) μ x = pdM R μ x *ᵥ η x + R x *ᵥ pdV η μ x := by
  funext c
  simp only [pdV, pdM, Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.of_apply]
  rw [pd_sum_complex (F := fun e y => R y c e * η y e) (fun e _ => (hR c e).mul (hη e)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pd_mul_complex (hR c e) (hη e)]

/-- Product rule `∂(R S) = ∂R S + R ∂S`. -/
theorem pdM_mul {R S : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : ι → ℝ} (hR : MDiffAt R x)
    (hS : MDiffAt S x) (μ : ι) :
    pdM (fun y => R y * S y) μ x = pdM R μ x * S x + R x * pdM S μ x := by
  ext c e
  simp only [pdM, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [pd_sum_complex (F := fun k y => R y c k * S y k e) (fun k _ => (hR c k).mul (hS k e)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pd_mul_complex (hR c k) (hS k e)]

theorem pdM_star {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : ι → ℝ} (hR : MDiffAt R x)
    (μ : ι) : pdM (fun y => star (R y)) μ x = star (pdM R μ x) := by
  ext c e
  simp only [pdM, Matrix.of_apply, Matrix.star_apply]
  exact pd_conj_complex (hR e c) μ

/-- For a unitary-valued `R`, `∂R R^* + R ∂(R^*) = 0`, i.e. `∂R R^* + R (∂R)^* = 0`. -/
theorem pdM_unitary {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) {x : ι → ℝ} (hR : MDiffAt R x) (μ : ι) :
    pdM R μ x * star (R x) + R x * star (pdM R μ x) = 0 := by
  have h1 : (fun y => R y * star (R y)) = fun _ => 1 := by
    funext y; exact Matrix.mem_unitaryGroup_iff.mp (hRu y)
  have h2 := pdM_mul hR hR.star μ
  rw [h1, pdM_star hR] at h2
  rw [← h2]
  ext c e
  simp [pdM, pd_const_complex]

/-! ### Covariant derivatives and the gauge action -/

/-- Covariant derivative in the fundamental representation: `∇_μ η = ∂_μ η + 𝒜_μ η`. -/
def covDerV (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) (η : (ι → ℝ) → Fin m → ℂ) (μ : ι)
    (x : ι → ℝ) : Fin m → ℂ :=
  pdV η μ x + 𝒜 μ x *ᵥ η x

/-- Covariant derivative in the adjoint representation: `D_μ a = ∂_μ a + [𝒜_μ, a]`. -/
def covDerAd (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    (a : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) (μ : ι) (x : ι → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  pdM a μ x + (𝒜 μ x * a x - a x * 𝒜 μ x)

/-- The gauge-transformed connection `R·𝒜 = R 𝒜 R^* - (∂R) R^*`. -/
def gaugeConn (R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ :=
  fun μ x => R x * 𝒜 μ x * star (R x) - pdM R μ x * star (R x)

/-- **Gauge covariance, fundamental representation**: `∇^{R·𝒜}_μ (R η) = R ∇^𝒜_μ η`. -/
theorem covDerV_gauge {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    {η : (ι → ℝ) → Fin m → ℂ} {x : ι → ℝ} (hR : MDiffAt R x) (hη : VDiffAt η x) (μ : ι) :
    covDerV (gaugeConn R 𝒜) (fun y => R y *ᵥ η y) μ x = R x *ᵥ covDerV 𝒜 η μ x := by
  have hu : star (R x) * R x = 1 := Matrix.mem_unitaryGroup_iff'.mp (hRu x)
  have e : (R x * 𝒜 μ x * star (R x) - pdM R μ x * star (R x)) * R x = R x * 𝒜 μ x - pdM R μ x := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc (pdM R μ x), hu, Matrix.mul_one,
      Matrix.mul_one]
  rw [covDerV, covDerV, gaugeConn, pdV_mulVec hR hη, Matrix.mulVec_mulVec, e, Matrix.sub_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

/-- **Gauge covariance, adjoint representation**: `D_{R·𝒜}(R a R^*) = R (D_𝒜 a) R^*`. -/
theorem covDerAd_gauge {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    {a : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : ι → ℝ} (hR : MDiffAt R x) (ha : MDiffAt a x)
    (μ : ι) :
    covDerAd (gaugeConn R 𝒜) (fun y => R y * a y * star (R y)) μ x =
      R x * covDerAd 𝒜 a μ x * star (R x) := by
  have hu : star (R x) * R x = 1 := Matrix.mem_unitaryGroup_iff'.mp (hRu x)
  have hz := pdM_unitary hRu hR μ
  have hd : pdM (fun y => R y * a y * star (R y)) μ x =
      pdM R μ x * a x * star (R x) + R x * pdM a μ x * star (R x) +
        R x * a x * star (pdM R μ x) := by
    rw [pdM_mul (hR.mul ha) hR.star, pdM_mul hR ha, pdM_star hR]
    noncomm_ring
  -- `R a ∂R^* = - R a R^* ∂R R^*`
  have hk : R x * a x * star (pdM R μ x) =
      -(R x * a x * star (R x) * (pdM R μ x * star (R x))) := by
    have : star (pdM R μ x) = -(star (R x) * (pdM R μ x * star (R x))) := by
      have h3 : R x * star (pdM R μ x) = -(pdM R μ x * star (R x)) := eq_neg_of_add_eq_zero_right hz
      calc star (pdM R μ x) = star (R x) * (R x * star (pdM R μ x)) := by
            rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
        _ = -(star (R x) * (pdM R μ x * star (R x))) := by rw [h3, Matrix.mul_neg]
    rw [this, Matrix.mul_neg]
    simp only [Matrix.mul_assoc]
  simp only [covDerAd, gaugeConn, hd, hk]
  have e1 : (R x * 𝒜 μ x * star (R x) - pdM R μ x * star (R x)) * (R x * a x * star (R x)) =
      R x * 𝒜 μ x * a x * star (R x) - pdM R μ x * a x * star (R x) := by
    simp only [Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (R x)) (R x), hu, Matrix.one_mul]
  have e2 : R x * a x * star (R x) * (R x * 𝒜 μ x * star (R x) - pdM R μ x * star (R x)) =
      R x * a x * 𝒜 μ x * star (R x) - R x * a x * star (R x) * (pdM R μ x * star (R x)) := by
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (R x)) (R x), hu, Matrix.one_mul]
  rw [e1, e2]
  noncomm_ring

/-! ### Unitary invariance of fibre norms -/

theorem sum_sq_norm_eq_re_dotProduct (v : Fin m → ℂ) :
    ∑ c, ‖v c‖ ^ 2 = (star v ⬝ᵥ v).re := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

/-- Unitary matrices preserve the Hermitian fibre norm. -/
theorem fibreNorm_mulVec_unitary {R : Matrix (Fin m) (Fin m) ℂ}
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℂ) (v : Fin m → ℂ) :
    fibreNorm (R *ᵥ v) = fibreNorm v := by
  have hu : star R * R = 1 := Matrix.mem_unitaryGroup_iff'.mp hR
  unfold fibreNorm
  rw [sum_sq_norm_eq_re_dotProduct, sum_sq_norm_eq_re_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [show Rᴴ = star R from rfl, hu, Matrix.one_mulVec]

/-- The Frobenius (Hilbert–Schmidt) norm `‖a‖_F = (Σ_{ce} |a_{ce}|²)^{1/2}`. -/
def frobNorm (a : Matrix (Fin m) (Fin m) ℂ) : ℝ := √(∑ c, ∑ e, ‖a c e‖ ^ 2)

theorem frobNorm_eq_sum_col (a : Matrix (Fin m) (Fin m) ℂ) :
    frobNorm a = √(∑ e, fibreNorm (fun c => a c e) ^ 2) := by
  unfold frobNorm fibreNorm
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem frobNorm_mul_unitary_left {R : Matrix (Fin m) (Fin m) ℂ}
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℂ) (a : Matrix (Fin m) (Fin m) ℂ) :
    frobNorm (R * a) = frobNorm a := by
  rw [frobNorm_eq_sum_col, frobNorm_eq_sum_col]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  have : (fun c => (R * a) c e) = R *ᵥ fun c => a c e := by
    funext c; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [this, fibreNorm_mulVec_unitary hR]

theorem frobNorm_star (a : Matrix (Fin m) (Fin m) ℂ) : frobNorm (star a) = frobNorm a := by
  unfold frobNorm
  rw [Finset.sum_comm]
  simp [Matrix.star_apply]

/-- Conjugation by a unitary matrix preserves the Frobenius norm. -/
theorem frobNorm_conj_unitary {R : Matrix (Fin m) (Fin m) ℂ}
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℂ) (a : Matrix (Fin m) (Fin m) ℂ) :
    frobNorm (R * a * star R) = frobNorm a := by
  rw [Matrix.mul_assoc, frobNorm_mul_unitary_left hR, ← frobNorm_star, Matrix.star_mul,
    star_star, frobNorm_mul_unitary_left hR, frobNorm_star]

/-! ### The dual representation -/

/-- The dual connection `-𝒜ᵀ` (acting on dual sections written as columns). -/
def dualConnM (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) :
    ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ :=
  fun μ x => -(𝒜 μ x)ᵀ

/-- The dual gauge matrix `R̄ = (R^*)ᵀ` (entrywise conjugate): `η̄ ↦ η̄ R^*` in column form. -/
def dualGauge (R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ :=
  fun y => (star (R y))ᵀ

theorem dualGauge_mem_unitary {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) (y : ι → ℝ) :
    dualGauge R y ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff.mp (hRu y)
  show (star (R y))ᵀ * star ((star (R y))ᵀ) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    ← Matrix.transpose_mul, ← Matrix.star_eq_conjTranspose, h, Matrix.transpose_one]

theorem MDiffAt.dualGauge {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : ι → ℝ}
    (hR : MDiffAt R x) : MDiffAt (dualGauge R) x := by
  intro c e
  exact hR.star e c

theorem pdM_dualGauge {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : ι → ℝ} (hR : MDiffAt R x)
    (μ : ι) : pdM (dualGauge R) μ x = (star (pdM R μ x))ᵀ := by
  ext c e
  have := congrArg (fun M => M e c) (pdM_star hR μ)
  simpa [pdM, dualGauge, Matrix.transpose_apply] using this

/-- **The dual gauge law**: `R̄·(-𝒜ᵀ) = -(R·𝒜)ᵀ`. -/
theorem gaugeConn_dual {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    {x : ι → ℝ} (hR : MDiffAt R x) (μ : ι) :
    gaugeConn (dualGauge R) (dualConnM 𝒜) μ x = dualConnM (gaugeConn R 𝒜) μ x := by
  have hz := pdM_unitary hRu hR μ
  have hz' : (R x * star (pdM R μ x))ᵀ = -(pdM R μ x * star (R x))ᵀ := by
    rw [← Matrix.transpose_neg]; congr 1; exact eq_neg_of_add_eq_zero_right hz
  simp only [gaugeConn, dualConnM, pdM_dualGauge hR, dualGauge]
  have e1 : star ((star (R x))ᵀ) = (R x)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [e1]
  have e2 : (star (pdM R μ x))ᵀ * (R x)ᵀ = (R x * star (pdM R μ x))ᵀ := by
    rw [Matrix.transpose_mul]
  have e3 : (star (R x))ᵀ * -(𝒜 μ x)ᵀ * (R x)ᵀ = -(R x * 𝒜 μ x * star (R x))ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc]
  rw [e2, e3, hz', Matrix.transpose_sub]
  abel

/-- **Gauge covariance, dual representation**: for the dual action `η̄ ↦ R̄ η̄` (`η̄ ↦ η̄ R^*`)
and the dual connection, `∇^{(R·𝒜)^∨}(R̄ η̄) = R̄ ∇^{𝒜^∨} η̄`. -/
theorem covDerV_gauge_dual {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    {η : (ι → ℝ) → Fin m → ℂ} {x : ι → ℝ} (hR : MDiffAt R x) (hη : VDiffAt η x) (μ : ι) :
    covDerV (dualConnM (gaugeConn R 𝒜)) (fun y => dualGauge R y *ᵥ η y) μ x =
      dualGauge R x *ᵥ covDerV (dualConnM 𝒜) η μ x := by
  rw [← covDerV_gauge (dualGauge_mem_unitary hRu) (dualConnM 𝒜) hR.dualGauge hη μ]
  simp only [covDerV, gaugeConn_dual hRu 𝒜 hR μ]

/-- A reference connection commuting with the gauge matrices passes through the gauge action:
`R·(Γ + 𝒜) = Γ + R·𝒜` when `R Γ = Γ R`. -/
theorem gaugeConn_add_commuting {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) (Γ 𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    (hΓ : ∀ μ y, R y * Γ μ y = Γ μ y * R y) (μ : ι) (x : ι → ℝ) :
    gaugeConn R (fun μ y => Γ μ y + 𝒜 μ y) μ x = Γ μ x + gaugeConn R 𝒜 μ x := by
  have hu : R x * star (R x) = 1 := Matrix.mem_unitaryGroup_iff.mp (hRu x)
  simp only [gaugeConn, Matrix.mul_add, Matrix.add_mul, hΓ μ x, Matrix.mul_assoc, hu,
    Matrix.mul_one]
  abel

/-! ### Gauge-invariant test sizes -/

/-- Test size of a section in the fundamental representation:
`‖η‖_{L^∞} + Σ_μ ‖∇_μ η‖_{L²}` (Hermitian fibre norm). -/
def vecTestSize (ρ : Measure (ι → ℝ)) (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    (η : (ι → ℝ) → Fin m → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun x => fibreNorm (η x)) ⊤ ρ + ∑ μ, eLpNorm (fun x => fibreNorm (covDerV 𝒜 η μ x)) 2 ρ

/-- Test size of an adjoint-valued test: `‖a‖_{L^∞} + Σ_μ ‖D_μ a‖_{L²}` (Frobenius norm). -/
def adTestSize (ρ : Measure (ι → ℝ)) (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    (a : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) : ℝ≥0∞ :=
  eLpNorm (fun x => frobNorm (a x)) ⊤ ρ + ∑ μ, eLpNorm (fun x => frobNorm (covDerAd 𝒜 a μ x)) 2 ρ

/-- **Exact gauge invariance of the fundamental test size.** -/
theorem vecTestSize_gauge (ρ : Measure (ι → ℝ)) {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) (hR : ∀ x, MDiffAt R x)
    (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) {η : (ι → ℝ) → Fin m → ℂ}
    (hη : ∀ x, VDiffAt η x) :
    vecTestSize ρ (gaugeConn R 𝒜) (fun y => R y *ᵥ η y) = vecTestSize ρ 𝒜 η := by
  unfold vecTestSize
  congr 1
  · congr 1; funext x; exact fibreNorm_mulVec_unitary (hRu x) _
  · refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1; funext x
    rw [covDerV_gauge hRu 𝒜 (hR x) (hη x) μ, fibreNorm_mulVec_unitary (hRu x)]

/-- **Exact gauge invariance of the dual test size.** -/
theorem vecTestSize_gauge_dual (ρ : Measure (ι → ℝ)) {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) (hR : ∀ x, MDiffAt R x)
    (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) {η : (ι → ℝ) → Fin m → ℂ}
    (hη : ∀ x, VDiffAt η x) :
    vecTestSize ρ (dualConnM (gaugeConn R 𝒜)) (fun y => dualGauge R y *ᵥ η y) =
      vecTestSize ρ (dualConnM 𝒜) η := by
  unfold vecTestSize
  congr 1
  · congr 1; funext x; exact fibreNorm_mulVec_unitary (dualGauge_mem_unitary hRu x) _
  · refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1; funext x
    rw [covDerV_gauge_dual hRu 𝒜 (hR x) (hη x) μ,
      fibreNorm_mulVec_unitary (dualGauge_mem_unitary hRu x)]

/-- **Exact gauge invariance of the adjoint test size.** -/
theorem adTestSize_gauge (ρ : Measure (ι → ℝ)) {R : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hRu : ∀ y, R y ∈ Matrix.unitaryGroup (Fin m) ℂ) (hR : ∀ x, MDiffAt R x)
    (𝒜 : ι → (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ) {a : (ι → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (ha : ∀ x, MDiffAt a x) :
    adTestSize ρ (gaugeConn R 𝒜) (fun y => R y * a y * star (R y)) = adTestSize ρ 𝒜 a := by
  unfold adTestSize
  congr 1
  · congr 1; funext x; exact frobNorm_conj_unitary (hRu x) _
  · refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1; funext x
    rw [covDerAd_gauge hRu 𝒜 (hR x) (ha x) μ, frobNorm_conj_unitary (hRu x)]

end RenewalGeometry.SobolevOpen
