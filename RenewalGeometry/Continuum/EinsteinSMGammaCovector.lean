/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMGravityFirstOrder

/-!
# The `ΓΓ` form of the first-order Einstein–Hilbert density and its coframe variation
  (infrastructure for `prop:homogeneous`, Einstein–Standard-Model action-closure manuscript)

Generic chart calculus for the gravitational jet density `gravPt` of
`EinsteinSMGravityFirstOrder.lean` (the first-order representative of the library's
second-order Einstein–Hilbert density `(Scal(g) - 2Λ)√|g|/(2κ)`):

* `hasDerivAt_metricInv_line`, `hasDerivAt_volFactor_line`: along a line `s ↦ e + s h` through a
  nondegenerate coframe, `d g^{-1} = -g^{-1} δg g^{-1}` and `d√|g| = ½ √|g| g^{μν} δg_{μν}`
  with `δg = hᵀηe + eᵀηh` (`metricVar`); Jacobi's formula is taken from Mathlib
  (`Matrix.det_one_add_smul`).
* `fderiv_volInvMetric_eq`: `D(√|g| g^{bd})(e)[h] = √|g| (½ g^{μν}δg_{μν} g^{bd} - (g^{-1}δg g^{-1})^{bd})`.
* `traceVar_eq_sum_christoffel`, `invVarInv_eq_christoffel`: the metric-compatibility identities
  `½ g^{μν}∂_c g_{μν} = Γ^a_{ac}` and `(g^{-1}∂_c g g^{-1})^{bd} = g^{be}Γ^d_{ce} + g^{de}Γ^b_{ce}`.
* `ehForm_eq_volQ`: **the `ΓΓ` form** — on the nondegenerate chart the first-order density is
  `ehForm e d d' = √|g| · Q(g^{-1}, Γ(e,d), Γ(e,d'))` with `Q` trilinear (`qForm`).
* `hasDerivAt_gravPt_line`: the derivative of `gravPt` along any line of jets through a
  nondegenerate jet, in closed form (product rule on `√|g| Q(g^{-1}, Γ, Γ)`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace GammaCov

/-! ### Line derivatives of the inverse metric and of the volume factor -/

/-- The metric variation `δg_{ρσ} = η_{ab}(h^a_ρ e^b_σ + e^a_ρ h^b_σ)` of `g = eᵀηe` along `h`. -/
def metricVar (e h : CoframeFibre) : Fin 4 → Fin 4 → ℝ :=
  fun ρ σ => ∑ a, ∑ b, minkowskiEta a b * (h a ρ * e b σ + e a ρ * h b σ)

theorem metricVar_symm (e h : CoframeFibre) (ρ σ : Fin 4) :
    metricVar e h ρ σ = metricVar e h σ ρ := by
  unfold metricVar
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : minkowskiEta b a = minkowskiEta a b := by
    simp only [minkowskiEta, Matrix.diagonal_apply]
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [this]; ring

theorem metricVar_eq_dMetricAlg (e : CoframeFibre) (d : CoframeJet) (c : Fin 4) :
    dMetricAlg e d c = metricVar e (d c) := rfl

theorem hasDerivAt_metricAt_line (e h : CoframeFibre) (s : ℝ) (μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => metricAt (e + s • h) μ ν) (metricVar (e + s • h) h μ ν) s := by
  simp only [metricAt_apply, metricVar]
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  have h1 : ∀ c κ, HasDerivAt (fun s : ℝ => (e + s • h) c κ) (h c κ) s := fun c κ => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id s).mul_const (h c κ)).const_add (e c κ)
  refine (((h1 a μ).mul (h1 b ν)).const_mul (minkowskiEta a b)).congr_deriv ?_
  ring

theorem metricInv_mul_metricAt {e : CoframeFibre} (he : e ∈ coframeGL) (μ σ : Fin 4) :
    ∑ ρ, metricInv e μ ρ * metricAt e ρ σ = if μ = σ then 1 else 0 := by
  have hne : IsUnit (metricAt e).det := by
    rw [det_metricAt]; exact (neg_ne_zero.mpr (pow_ne_zero 2 he)).isUnit
  have h := Matrix.nonsing_inv_mul (metricAt e) hne
  have := congrFun (congrFun h μ) σ
  simpa [Matrix.mul_apply, Matrix.one_apply, metricInv] using this

theorem metricAt_mul_metricInv {e : CoframeFibre} (he : e ∈ coframeGL) (μ σ : Fin 4) :
    ∑ ρ, metricAt e μ ρ * metricInv e ρ σ = if μ = σ then 1 else 0 := by
  have hne : IsUnit (metricAt e).det := by
    rw [det_metricAt]; exact (neg_ne_zero.mpr (pow_ne_zero 2 he)).isUnit
  have h := Matrix.mul_nonsing_inv (metricAt e) hne
  have := congrFun (congrFun h μ) σ
  simpa [Matrix.mul_apply, Matrix.one_apply, metricInv] using this

theorem metricAt_symm (e : CoframeFibre) (μ ν : Fin 4) : metricAt e μ ν = metricAt e ν μ := by
  rw [metricAt_apply, metricAt_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : minkowskiEta b a = minkowskiEta a b := by
    simp only [minkowskiEta, Matrix.diagonal_apply]
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [this]; ring

theorem metricInv_symm (e : CoframeFibre) (μ ν : Fin 4) : metricInv e μ ν = metricInv e ν μ := by
  have hs : Matrix.transpose (metricAt e) = metricAt e := Matrix.ext fun i j => metricAt_symm e j i
  have : Matrix.transpose (metricInv e) = metricInv e := by
    unfold metricInv; rw [Matrix.transpose_nonsing_inv, hs]
  exact (congrFun (congrFun this ν) μ)

theorem eventually_line_mem_GL {e : CoframeFibre} (he : e ∈ coframeGL) (h : CoframeFibre) :
    ∀ᶠ s in 𝓝 (0 : ℝ), e + s • h ∈ coframeGL := by
  have hc : Continuous fun s : ℝ => e + s • h := continuous_const.add (continuous_id.smul
    continuous_const)
  have := hc.continuousAt (x := 0) |>.preimage_mem_nhds (isOpen_coframeGL.mem_nhds
    (by simpa using he))
  exact this

/-- **Derivative of the inverse metric along a line**: `d/ds g^{-1}(e + s h)|₀ = -g^{-1}δg g^{-1}`. -/
theorem hasDerivAt_metricInv_line {e : CoframeFibre} (he : e ∈ coframeGL) (h : CoframeFibre)
    (μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => metricInv (e + s • h) μ ν)
      (-(∑ ρ, ∑ σ, metricInv e μ ρ * metricVar e h ρ σ * metricInv e σ ν)) 0 := by
  have hline : HasDerivAt (fun s : ℝ => e + s • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add e
  have hdI : ∀ μ ν, DifferentiableAt ℝ (fun s : ℝ => metricInv (e + s • h) μ ν) 0 := fun μ ν => by
    have h1 : DifferentiableAt ℝ (fun e : CoframeFibre => metricInv e μ ν) (e + (0 : ℝ) • h) := by
      simpa using ((contDiffAt_metricInv μ ν he (n := 1)).differentiableAt one_ne_zero)
    exact h1.comp (0 : ℝ) hline.differentiableAt
  set D : Fin 4 → Fin 4 → ℝ := fun μ ν => deriv (fun s : ℝ => metricInv (e + s • h) μ ν) 0
  have hG : ∀ ρ σ, HasDerivAt (fun s : ℝ => metricAt (e + s • h) ρ σ) (metricVar e h ρ σ) 0 :=
    fun ρ σ => by simpa using hasDerivAt_metricAt_line e h 0 ρ σ
  have key : ∀ μ σ, ∑ ρ, D μ ρ * metricAt e ρ σ = -∑ ρ, metricInv e μ ρ * metricVar e h ρ σ := by
    intro μ σ
    have hconst : (fun s : ℝ => ∑ ρ, metricInv (e + s • h) μ ρ * metricAt (e + s • h) ρ σ)
        =ᶠ[𝓝 0] fun _ => (if μ = σ then 1 else 0 : ℝ) := by
      filter_upwards [eventually_line_mem_GL he h] with s hs using metricInv_mul_metricAt hs μ σ
    have hsum : HasDerivAt (fun s : ℝ => ∑ ρ, metricInv (e + s • h) μ ρ * metricAt (e + s • h) ρ σ)
        (∑ ρ, (D μ ρ * metricAt e ρ σ + metricInv e μ ρ * metricVar e h ρ σ)) 0 := by
      refine HasDerivAt.fun_sum fun ρ _ => ?_
      have := (hdI μ ρ).hasDerivAt.mul (hG ρ σ)
      simp only [zero_smul, add_zero] at this
      exact this
    have h0 := hsum.unique ((hasDerivAt_const (0 : ℝ) (if μ = σ then (1 : ℝ) else 0)).congr_of_eventuallyEq
      hconst)
    rw [Finset.sum_add_distrib] at h0
    linarith
  have hD : ∀ μ ν, D μ ν = -(∑ ρ, ∑ σ, metricInv e μ ρ * metricVar e h ρ σ * metricInv e σ ν) := by
    intro μ ν
    calc D μ ν = ∑ σ, D μ σ * (if σ = ν then 1 else 0) := by simp
      _ = ∑ σ, D μ σ * ∑ ρ, metricAt e σ ρ * metricInv e ρ ν := by
          simp only [metricAt_mul_metricInv he]
      _ = ∑ ρ, (∑ σ, D μ σ * metricAt e σ ρ) * metricInv e ρ ν := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => by ring
      _ = _ := by
          simp only [key, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
          rw [Finset.sum_comm]
  have := (hdI μ ν).hasDerivAt
  rw [← hD μ ν]
  exact this


/-! ### Jacobi's formula and the volume factor -/

theorem hasDerivAt_det_line (A B : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsUnit A.det) :
    HasDerivAt (fun s : ℝ => (A + s • B).det) (A.det * (A⁻¹ * B).trace) 0 := by
  set M := A⁻¹ * B
  set p := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)).divX.divX
  have hfac : ∀ s : ℝ, (A + s • B).det = A.det * (1 + M.trace * s + p.eval s * s ^ 2) := by
    intro s
    have : A + s • B = A * (1 + s • M) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv A hA, Matrix.one_mul]
    rw [this, Matrix.det_mul, Matrix.det_one_add_smul]
  have hp : HasDerivAt (fun s : ℝ => p.eval s * s ^ 2) 0 0 := by
    have h1 := (Polynomial.hasDerivAt p 0).mul (hasDerivAt_pow 2 (0 : ℝ))
    have h2 : HasDerivAt (fun s : ℝ => p.eval s * s ^ 2) (Polynomial.eval 0
        (Polynomial.derivative p) * 0 ^ 2 + Polynomial.eval 0 p * (((2 : ℕ) : ℝ) * 0 ^ (2 - 1))) 0 :=
      h1
    exact h2.congr_deriv (by simp)
  have h := ((((hasDerivAt_id (0 : ℝ)).const_mul M.trace).const_add 1).add hp).const_mul A.det
  simp only [funext hfac]
  refine h.congr_deriv ?_
  simp

theorem minkowskiEta_mul_self : minkowskiEta * minkowskiEta = 1 := by
  rw [minkowskiEta, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem minkowskiEta_transpose : Matrix.transpose minkowskiEta = minkowskiEta := by
  rw [minkowskiEta, Matrix.diagonal_transpose]

theorem minkowskiEta_inv : minkowskiEta⁻¹ = minkowskiEta :=
  Matrix.inv_eq_left_inv minkowskiEta_mul_self

theorem metricVar_matrix (e h : CoframeFibre) :
    Matrix.of (metricVar e h) =
      Matrix.transpose (Matrix.of h) * minkowskiEta * Matrix.of e +
        Matrix.transpose (Matrix.of e) * minkowskiEta * Matrix.of h := by
  ext ρ σ
  simp only [metricVar, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_four]
  ring

/-- `½ g^{ρσ} δg_{ρσ} = tr(e⁻¹ h)`. -/
theorem sum_metricInv_mul_metricVar {e : CoframeFibre} (he : e ∈ coframeGL) (h : CoframeFibre) :
    ∑ ρ, ∑ σ, metricInv e ρ σ * metricVar e h ρ σ =
      2 * ((Matrix.of e)⁻¹ * Matrix.of h).trace := by
  set A := Matrix.of e
  set B := Matrix.of h
  set η := minkowskiEta
  have hA : IsUnit A.det := Ne.isUnit he
  have hAT : IsUnit (Matrix.transpose A).det := by rwa [Matrix.det_transpose]
  have hginv : metricInv e = A⁻¹ * η * (Matrix.transpose A)⁻¹ := by
    show (Matrix.transpose A * η * A)⁻¹ = _
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, minkowskiEta_inv, Matrix.mul_assoc]
  have hsum : ∑ ρ, ∑ σ, metricInv e ρ σ * metricVar e h ρ σ =
      (metricInv e * Matrix.transpose (Matrix.of (metricVar e h))).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  rw [hsum, metricVar_matrix, hginv, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, minkowskiEta_transpose, Matrix.mul_add, Matrix.trace_add]
  have h1 : (A⁻¹ * η * (Matrix.transpose A)⁻¹ * (Matrix.transpose B * (η * A))).trace =
      (A⁻¹ * B).trace := by
    rw [show A⁻¹ * η * (Matrix.transpose A)⁻¹ * (Matrix.transpose B * (η * A)) =
        (A⁻¹ * η * (Matrix.transpose A)⁻¹ * Matrix.transpose B * η) * A by
          simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv A hA, Matrix.one_mul,
      Matrix.trace_mul_comm (η * (Matrix.transpose A)⁻¹ * Matrix.transpose B) η]
    simp only [← Matrix.mul_assoc]
    rw [minkowskiEta_mul_self, Matrix.one_mul, ← Matrix.transpose_nonsing_inv,
      ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]
  have h2 : (A⁻¹ * η * (Matrix.transpose A)⁻¹ * (Matrix.transpose A * (η * B))).trace =
      (A⁻¹ * B).trace := by
    rw [show A⁻¹ * η * (Matrix.transpose A)⁻¹ * (Matrix.transpose A * (η * B)) =
        A⁻¹ * η * ((Matrix.transpose A)⁻¹ * Matrix.transpose A) * η * B by
          simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul _ hAT, Matrix.mul_one, Matrix.mul_assoc A⁻¹, minkowskiEta_mul_self,
      Matrix.mul_one]
  rw [h1, h2]; ring

theorem volFactor_eq_abs_det' (e : CoframeFibre) : volFactor e = |(Matrix.of e).det| :=
  volFactor_eq_abs_det e

/-- **Derivative of the volume factor along a line**:
`d/ds √|g|(e + s h)|₀ = ½ √|g| g^{ρσ} δg_{ρσ}`. -/
theorem hasDerivAt_volFactor_line {e : CoframeFibre} (he : e ∈ coframeGL) (h : CoframeFibre) :
    HasDerivAt (fun s : ℝ => volFactor (e + s • h))
      (volFactor e * ((1 / 2) * ∑ ρ, ∑ σ, metricInv e ρ σ * metricVar e h ρ σ)) 0 := by
  have hA : IsUnit (Matrix.of e).det := Ne.isUnit he
  have hdet := hasDerivAt_det_line (Matrix.of e) (Matrix.of h) hA
  have hfun : (fun s : ℝ => volFactor (e + s • h)) =
      fun s => |(Matrix.of e + s • Matrix.of h).det| := by
    funext s; rw [volFactor_eq_abs_det]; rfl
  have hne : (Matrix.of e).det ≠ 0 := he
  have habs := (hasDerivAt_abs (x := (Matrix.of e + (0 : ℝ) • Matrix.of h).det)
    (by simpa using hne)).comp (0 : ℝ) (by simpa using hdet)
  rw [hfun]
  refine habs.congr_deriv ?_
  rw [sum_metricInv_mul_metricVar he, volFactor_eq_abs_det]
  simp only [zero_smul, add_zero]
  have hs : (SignType.sign (Matrix.of e).det : ℝ) * (Matrix.of e).det = |(Matrix.of e).det| := by
    rcases lt_or_gt_of_ne he with hn | hp
    · simp [hn, abs_of_neg hn]
    · simp [hp, abs_of_pos hp]
  calc (SignType.sign (Matrix.of e).det : ℝ) * ((Matrix.of e).det * ((Matrix.of e)⁻¹ * Matrix.of h).trace)
      = ((SignType.sign (Matrix.of e).det : ℝ) * (Matrix.of e).det) *
          ((Matrix.of e)⁻¹ * Matrix.of h).trace := by ring
    _ = _ := by rw [hs]; ring

/-! ### The derivative of `√|g| g^{-1}` -/

theorem hasDerivAt_line_of_differentiableAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : CoframeFibre → F} {e : CoframeFibre} (hΦ : DifferentiableAt ℝ Φ e) (h : CoframeFibre) :
    HasDerivAt (fun s : ℝ => Φ (e + s • h)) (fderiv ℝ Φ e h) 0 := by
  have hline : HasDerivAt (fun s : ℝ => e + s • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add e
  have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ e) (e + (0 : ℝ) • h) := by simpa using hΦ.hasFDerivAt
  exact hΦ'.comp_hasDerivAt (0 : ℝ) hline

/-- **`D(√|g| g^{bd})(e)[h] = √|g| (½ g^{ρσ}δg_{ρσ} g^{bd} - (g^{-1}δg g^{-1})^{bd})`.** -/
theorem fderiv_volInvMetric_eq {e : CoframeFibre} (he : e ∈ coframeGL) (h : CoframeFibre)
    (b d : Fin 4) :
    fderiv ℝ (fun e => volInvMetric e b d) e h =
      volFactor e * ((1 / 2) * (∑ ρ, ∑ σ, metricInv e ρ σ * metricVar e h ρ σ) * metricInv e b d -
        ∑ ρ, ∑ σ, metricInv e b ρ * metricVar e h ρ σ * metricInv e σ d) := by
  have h1 := hasDerivAt_line_of_differentiableAt
    ((contDiffAt_volInvMetric he b d (n := 1)).differentiableAt one_ne_zero) h
  have h2 := (hasDerivAt_volFactor_line he h).mul (hasDerivAt_metricInv_line he h b d)
  have h2' : HasDerivAt (fun s : ℝ => volInvMetric (e + s • h) b d)
      (volFactor e * ((1 / 2) * ∑ ρ, ∑ σ, metricInv e ρ σ * metricVar e h ρ σ) *
          metricInv (e + (0 : ℝ) • h) b d +
        volFactor (e + (0 : ℝ) • h) *
          -(∑ ρ, ∑ σ, metricInv e b ρ * metricVar e h ρ σ * metricInv e σ d)) 0 := h2
  rw [h1.unique h2']
  simp only [zero_smul, add_zero]
  ring

/-! ### Metric compatibility of the Christoffel symbols -/

/-- `½ g^{ρσ}∂_c g_{ρσ} = Γ^a_{ac}` (for symmetric `g^{-1}` and `∂_c g`). -/
theorem traceVar_eq_sum_christoffel (G : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hG : ∀ i j, G i j = G j i) (hdg : ∀ c i j, dg c i j = dg c j i) (c : Fin 4) :
    (1 / 2) * ∑ ρ, ∑ σ, G ρ σ * dg c ρ σ = ∑ a, christoffel G dg a a c := by
  have hsw : ∑ a, ∑ e, G a e * dg e a c = ∑ a, ∑ e, G a e * dg a e c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [hG]
  have hexp : ∑ a, christoffel G dg a a c = (1 / 2) * (∑ a, ∑ e, G a e * dg a e c +
      ∑ a, ∑ e, G a e * dg c e a - ∑ a, ∑ e, G a e * dg e a c) := by
    simp only [christoffel, ← Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring
  rw [hexp, hsw]
  congr 1
  rw [add_sub_cancel_left]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
  rw [hdg c e a]

/-- `(g^{-1}∂_c g g^{-1})^{bd} = g^{be}Γ^d_{ce} + g^{de}Γ^b_{ce}` (for symmetric `g^{-1}`, `∂_c g`). -/
theorem invVarInv_eq_christoffel (G : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hG : ∀ i j, G i j = G j i) (hdg : ∀ c i j, dg c i j = dg c j i) (b d c : Fin 4) :
    ∑ ρ, ∑ σ, G b ρ * dg c ρ σ * G σ d =
      ∑ e, (G b e * christoffel G dg d c e + G d e * christoffel G dg b c e) := by
  have h1 : ∑ e, G b e * christoffel G dg d c e = ∑ e, ∑ f,
      (1 / 2) * (G b e * G d f * (dg c f e + dg e f c - dg f c e)) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [christoffel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => by ring
  have h2 : ∑ e, G d e * christoffel G dg b c e = ∑ e, ∑ f,
      (1 / 2) * (G b e * G d f * (dg c e f + dg f e c - dg e c f)) := by
    have : ∑ e, G d e * christoffel G dg b c e = ∑ f, ∑ e,
        (1 / 2) * (G b e * G d f * (dg c e f + dg f e c - dg e c f)) := by
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [christoffel, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => by ring
    rw [this, Finset.sum_comm]
  rw [Finset.sum_add_distrib, h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hdg e f c, hdg f e c, hdg c f e, hG f d]
  ring

/-! ### The `ΓΓ` form -/

/-- The trilinear `ΓΓ` form: `Q(G, Γ, Γ') = Σ_{b,d,a} [-(S_a G^{bd} - X^{bd}_a) Γ'^a_{db} +
(S_d G^{bd} - X^{bd}_d) Γ'^a_{ab} + G^{bd}(Γ^a_{ak}Γ'^k_{db} - Γ^a_{dk}Γ'^k_{ab})]`, with
`S_c = Γ^a_{ac}` and `X^{bd}_c = G^{be}Γ^d_{ce} + G^{de}Γ^b_{ce}`. -/
def qForm (G : Fin 4 → Fin 4 → ℝ) (Γ Γ' : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ b, ∑ dd, ∑ a,
    (-(((∑ c, Γ c c a) * G b dd - ∑ e, (G b e * Γ dd a e + G dd e * Γ b a e)) * Γ' a dd b) +
      ((∑ c, Γ c c dd) * G b dd - ∑ e, (G b e * Γ dd dd e + G dd e * Γ b dd e)) * Γ' a a b +
      G b dd * ((∑ k, Γ a a k * Γ' k dd b) - ∑ k, Γ a dd k * Γ' k a b))

theorem dMetricAlg_symm (e : CoframeFibre) (d : CoframeJet) (c i j : Fin 4) :
    dMetricAlg e d c i j = dMetricAlg e d c j i := by
  rw [metricVar_eq_dMetricAlg, metricVar_symm]

/-- **The `ΓΓ` form of the first-order Einstein–Hilbert density**: on the nondegenerate chart,
`ehForm e d d' = √|g| Q(g^{-1}, Γ(e,d), Γ(e,d'))`. -/
theorem ehForm_eq_volQ {e : CoframeFibre} (he : e ∈ coframeGL) (d d' : CoframeJet) :
    ehForm e d d' = volFactor e * qForm (fun i j => metricInv e i j) (christoffelJ e d)
      (christoffelJ e d') := by
  have hG : ∀ i j, metricInv e i j = metricInv e j i := metricInv_symm e
  have hdg := dMetricAlg_symm e d
  have hDV : ∀ b dd c, fderiv ℝ (fun e => volInvMetric e b dd) e (d c) =
      volFactor e * ((∑ a, christoffelJ e d a a c) * metricInv e b dd -
        ∑ f, (metricInv e b f * christoffelJ e d dd c f +
          metricInv e dd f * christoffelJ e d b c f)) := by
    intro b dd c
    rw [fderiv_volInvMetric_eq he]
    rw [← metricVar_eq_dMetricAlg e d c]
    rw [traceVar_eq_sum_christoffel (fun i j => metricInv e i j) (dMetricAlg e d) hG hdg c,
      invVarInv_eq_christoffel (fun i j => metricInv e i j) (dMetricAlg e d) hG hdg b dd c]
    rfl
  simp only [ehForm, hDV]
  simp only [qForm, volInvMetric, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun dd _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### Multilinear packaging -/

/-- Two-index real tensors. -/
abbrev T2 := Fin 4 → Fin 4 → ℝ
/-- Three-index real tensors. -/
abbrev T3 := Fin 4 → Fin 4 → Fin 4 → ℝ

theorem qForm_add₁ (G G' : T2) (Γ Γ' : T3) :
    qForm (G + G') Γ Γ' = qForm G Γ Γ' + qForm G' Γ Γ' := by
  unfold qForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun dd _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem qForm_add₂ (G : T2) (Γ₁ Γ₂ Γ' : T3) :
    qForm G (Γ₁ + Γ₂) Γ' = qForm G Γ₁ Γ' + qForm G Γ₂ Γ' := by
  unfold qForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun dd _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem qForm_add₃ (G : T2) (Γ Γ₁ Γ₂ : T3) :
    qForm G Γ (Γ₁ + Γ₂) = qForm G Γ Γ₁ + qForm G Γ Γ₂ := by
  unfold qForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun dd _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- `Q` as a continuous trilinear map. -/
def qTri :=
  addTrilinL (V₁ := T2) (V₂ := T3) (V₃ := T3) (W := ℝ) qForm qForm_add₁ qForm_add₂ qForm_add₃ (by unfold qForm; fun_prop)

theorem qTri_apply (G : T2) (Γ Γ' : T3) : qTri G Γ Γ' = qForm G Γ Γ' := rfl

theorem christoffel_add₁ (G G' : T2) (dg : T3) :
    christoffel (G + G') dg = christoffel G dg + christoffel G' dg := by
  funext c i j
  simp only [christoffel, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem christoffel_add₂ (G : T2) (dg dg' : T3) :
    christoffel G (dg + dg') = christoffel G dg + christoffel G dg' := by
  funext c i j
  simp only [christoffel, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by ring

/-- The Christoffel symbols as a continuous bilinear map `(g^{-1}, ∂g) ↦ Γ`. -/
def chBi :=
  addBilinL (V₁ := T2) (V₂ := T3) (W := T3) christoffel christoffel_add₁ christoffel_add₂ (by unfold christoffel; fun_prop)

theorem chBi_apply (G : T2) (dg : T3) : chBi G dg = christoffel G dg := rfl

theorem dMetricAlg_add₁ (e e' : CoframeFibre) (d : CoframeJet) :
    dMetricAlg (e + e') d = dMetricAlg e d + dMetricAlg e' d := by
  funext i μ ν
  simp only [dMetricAlg, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- `dMetricAlg` as a continuous bilinear map `(e, ∂e) ↦ ∂g`. -/
def dmBi :=
  addBilinL (V₁ := CoframeFibre) (V₂ := CoframeJet) (W := T3) dMetricAlg dMetricAlg_add₁ dMetricAlg_add (by unfold dMetricAlg; fun_prop)

theorem dmBi_apply (e : CoframeFibre) (d : CoframeJet) : dmBi e d = dMetricAlg e d := rfl

/-! ### The derivative of the gravitational jet density along a line -/

/-- The inverse metric as a two-index tensor. -/
def ginvT (e : CoframeFibre) : T2 := fun i j => metricInv e i j

/-- `G' = -g^{-1} δg g^{-1}`, the variation of the inverse metric along `M`. -/
def ginvVar (e M : CoframeFibre) : T2 :=
  fun μ ν => -(∑ ρ, ∑ σ, metricInv e μ ρ * metricVar e M ρ σ * metricInv e σ ν)

/-- `δ√|g| = ½√|g| g^{ρσ}δg_{ρσ}` along `M`. -/
def volVar (e M : CoframeFibre) : ℝ :=
  volFactor e * ((1 / 2) * ∑ ρ, ∑ σ, metricInv e ρ σ * metricVar e M ρ σ)

/-- `δΓ = Γ(δg^{-1}, ∂g) + Γ(g^{-1}, δ∂g)` along `(M, D)`, `δ∂g = ∂g(M, ∂e) + ∂g(e, D)`. -/
def christoffelVar (e : CoframeFibre) (de : CoframeJet) (M : CoframeFibre) (D : CoframeJet) : T3 :=
  christoffel (ginvVar e M) (dMetricAlg e de) +
    christoffel (ginvT e) (dMetricAlg M de + dMetricAlg e D)

/-- **The variation of the gravitational jet density** in closed form. -/
def gravVar {Ysec : Type} (θ : CoefficientBank Ysec) (e : CoframeFibre) (de : CoframeJet)
    (M : CoframeFibre) (D : CoframeJet) : ℝ :=
  (2 * θ.kappa)⁻¹ * (volVar e M * (qForm (ginvT e) (christoffelJ e de) (christoffelJ e de) -
      2 * θ.Lambda) +
    volFactor e * (qForm (ginvVar e M) (christoffelJ e de) (christoffelJ e de) +
      qForm (ginvT e) (christoffelVar e de M D) (christoffelJ e de) +
      qForm (ginvT e) (christoffelJ e de) (christoffelVar e de M D)))

theorem christoffelJ_eq (e : CoframeFibre) (de : CoframeJet) :
    christoffelJ e de = chBi (ginvT e) (dmBi e de) := rfl

section Line

variable {C : Type} [Fintype C] {Ysec : Type}

/-- **Line derivative of `gravPt`**: through a nondegenerate jet `J`, along any jet `W`,
`d/ds gravPt(J + sW)|₀ = gravVar(J.e, J.de, W.e, W.de)`. -/
theorem hasDerivAt_gravPt_line (θ : CoefficientBank Ysec) {J : RJet C} (hJ : J.e ∈ coframeGL)
    (W : RJet C) :
    HasDerivAt (fun s : ℝ => gravPt θ (J + s • W)) (gravVar θ J.e J.de W.e W.de) 0 := by
  generalize hE : J.e = e at hJ
  generalize hDe : J.de = de
  generalize hM : W.e = M
  generalize hD : W.de = D
  -- the line of jets stays nondegenerate
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), gravPt θ (J + s • W) =
      (2 * θ.kappa)⁻¹ * (volFactor (e + s • M) *
        qTri (ginvT (e + s • M)) (chBi (ginvT (e + s • M)) (dmBi (e + s • M) (de + s • D)))
          (chBi (ginvT (e + s • M)) (dmBi (e + s • M) (de + s • D))) -
        2 * θ.Lambda * volFactor (e + s • M)) := by
    filter_upwards [eventually_line_mem_GL hJ M] with s hs
    simp only [gravPt, RJet.add_e, RJet.smul_e, RJet.add_de, RJet.smul_de, hE, hDe, hM, hD, ginvT,
      ehFirstOrder_eq,
      ehForm_eq_volQ hs, qTri_apply, chBi_apply, dmBi_apply, christoffelJ]
    unfold ginvT
    ring
  -- derivatives of the pieces
  have hvol := hasDerivAt_volFactor_line hJ M
  have hG : HasDerivAt (fun s : ℝ => ginvT (e + s • M)) (ginvVar e M) 0 := by
    refine hasDerivAt_pi.mpr fun μ => hasDerivAt_pi.mpr fun ν => ?_
    exact hasDerivAt_metricInv_line hJ M μ ν
  have hdm : HasDerivAt (fun s : ℝ => dmBi (e + s • M) (de + s • D))
      (dmBi M de + dmBi e D) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => dmBi (e + s • M)) (dmBi M) 0 := by
      have : HasDerivAt (fun s : ℝ => e + s • M) M 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const M).const_add e
      exact dmBi.hasFDerivAt.comp_hasDerivAt (0 : ℝ) this
    have h2 : HasDerivAt (fun s : ℝ => de + s • D) D 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add de
    have := h1.clm_apply h2
    simpa [add_comm] using this
  have hch : HasDerivAt (fun s : ℝ => chBi (ginvT (e + s • M)) (dmBi (e + s • M) (de + s • D)))
      (christoffelVar e de M D) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => chBi (ginvT (e + s • M))) (chBi (ginvVar e M)) 0 := by
      exact chBi.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hG
    have := h1.clm_apply hdm
    simp only [zero_smul, add_zero] at this
    refine this.congr_deriv ?_
    simp only [christoffelVar, chBi_apply, dmBi_apply, map_add, christoffel_add₂]
  have hq : HasDerivAt (fun s : ℝ => qTri (ginvT (e + s • M))
      (chBi (ginvT (e + s • M)) (dmBi (e + s • M) (de + s • D)))
      (chBi (ginvT (e + s • M)) (dmBi (e + s • M) (de + s • D))))
      (qForm (ginvVar e M) (christoffelJ e de) (christoffelJ e de) +
        qForm (ginvT e) (christoffelVar e de M D) (christoffelJ e de) +
        qForm (ginvT e) (christoffelJ e de) (christoffelVar e de M D)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => qTri (ginvT (e + s • M))) (qTri (ginvVar e M)) 0 := by
      exact qTri.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hG
    have := (h1.clm_apply hch).clm_apply hch
    simp only [zero_smul, add_zero] at this
    refine this.congr_deriv ?_
    rfl
  have htot := ((hvol.mul hq).sub (hvol.const_mul (2 * θ.Lambda))).const_mul (2 * θ.kappa)⁻¹
  refine (htot.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [zero_smul, add_zero]
  show (2 * θ.kappa)⁻¹ * (volVar e M * qForm (ginvT e) (christoffelJ e de) (christoffelJ e de) +
      volFactor e * (qForm (ginvVar e M) (christoffelJ e de) (christoffelJ e de) +
        qForm (ginvT e) (christoffelVar e de M D) (christoffelJ e de) +
        qForm (ginvT e) (christoffelJ e de) (christoffelVar e de M D)) -
      2 * θ.Lambda * volVar e M) = gravVar θ e de M D
  unfold gravVar
  ring

/-- **The gravitational covector in `ΓΓ` form**: for a nondegenerate jet `J`,
`gravCov θ J T = gravVar(J.e, J.de, ė(k), ∂ė)` with `(ė, ∂ė)` the coframe part of `redVar J T`. -/
theorem gravCov_eq_gravVar (θ : CoefficientBank Ysec) {J : RJet C} (hJ : J.e ∈ coframeGL)
    (T : RJet C) :
    gravCov θ J T = gravVar θ J.e J.de (redVar J T).e (redVar J T).de := by
  rw [← fderiv_gravPt_redVar θ hJ T]
  have hd : DifferentiableAt ℝ (gravPt (C := C) θ) J :=
    ((contDiffOn_gravPt θ (n := 1)).contDiffAt (isOpen_jetGL.mem_nhds hJ)).differentiableAt
      one_ne_zero
  have hline : HasDerivAt (fun s : ℝ => J + s • redVar J T) (redVar J T) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (redVar J T)).const_add J
  have h2 : HasDerivAt (fun s : ℝ => gravPt θ (J + s • redVar J T))
      (fderiv ℝ (gravPt θ) J (redVar J T)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  exact h2.unique (hasDerivAt_gravPt_line θ hJ (redVar J T))

end Line

end GammaCov
end EinsteinSM
end RenewalGeometry
