/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMGammaCovector
import RenewalGeometry.Continuum.EinsteinSMHomogeneousSampling

/-!
# The Euler–Lagrange covectors at a flat FLRW–Higgs jet
  (`prop:homogeneous`, Einstein–Standard-Model action-closure manuscript)

At the jet of the homogeneous configuration of `eq:homogeneous-fields`
(coframe `e = diag(1, a, a, a)`, `∂₀e = ȧ diag(0,1,1,1)`, `A = 0`, `F = 0`,
`H = (φ/√2) h₀`, `K = ∂H = ((φ̇/√2) h₀, 0, 0, 0)`, zero spinors) the first-variation
covectors of the library's continuum action are computed in closed form:

* `qForm_flrw_left`, `qForm_flrw_right`, `qForm_flrw_metric`, `qForm_flrw`: the `ΓΓ` form at the
  FLRW Christoffel symbols;
* `gravCov_flrw`: the gravitational covector (second-order Einstein–Hilbert density, via its
  first-order `ΓΓ` representative) on an arbitrary test jet `(k, ∂k)`:
  `(1/4κ)[2(3aȧ² - Λa³)k₀₀ + 2(7a³ȧ² + Λa⁵)Σᵢkᵢᵢ + 4a⁴ȧ Σᵢ∂₀kᵢᵢ + a²ȧ Σᵢ(∂ᵢk₀ᵢ + ∂ᵢkᵢ₀)]`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace HomogeneousCov

open GammaCov Comparison

/-! ### The FLRW jet -/

/-- The FLRW coframe jet `∂_c e = δ_{c0} ȧ diag(0,1,1,1)`. -/
def flrwDe (ad : ℝ) : CoframeJet := fun c => (if c = 0 then ad else 0) • frameD

theorem frameDiag_apply (a : ℝ) (i j : Fin 4) :
    frameDiag a i j = if i = j then (if i = 0 then 1 else a) else 0 := rfl

theorem metricAt_frameDiag (a : ℝ) (i j : Fin 4) : metricAt (frameDiag a) i j = flrwG a i j := by
  rw [metricAt_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, minkowskiEta, frameDiag, flrwG, Matrix.diagonal_apply] <;> ring

theorem frameDiag_mem_GL {a : ℝ} (ha : a ≠ 0) : frameDiag a ∈ coframeGL := by
  show (Matrix.of (frameDiag a)).det ≠ 0
  rw [det_frameDiag]; exact pow_ne_zero 3 ha

theorem metricInv_frameDiag {a : ℝ} (ha : a ≠ 0) (i j : Fin 4) :
    metricInv (frameDiag a) i j = flrwGinv a i j := by
  have hG : metricAt (frameDiag a) = Matrix.diagonal fun i : Fin 4 => if i = 0 then -1 else a ^ 2 := by
    ext i j
    rw [metricAt_frameDiag]
    by_cases h : i = j
    · subst h; simp [flrwG]
    · simp [flrwG, h, Matrix.diagonal_apply]
  have hinv : metricInv (frameDiag a) =
      Matrix.diagonal fun i : Fin 4 => if i = 0 then -1 else (a ^ 2)⁻¹ := by
    unfold metricInv
    rw [hG]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i = 0
    · simp [h]
    · simp [h, ha]
  rw [hinv]
  by_cases h : i = j
  · subst h; simp [flrwGinv]
  · simp [flrwGinv, h, Matrix.diagonal_apply]

theorem volFactor_frameDiag {a : ℝ} (ha : 0 < a) : volFactor (frameDiag a) = a ^ 3 := by
  rw [volFactor_eq_abs_det, det_frameDiag, abs_of_pos (by positivity)]

theorem ginvT_frameDiag {a : ℝ} (ha : a ≠ 0) : ginvT (frameDiag a) = flrwGinv a := by
  funext i j; exact metricInv_frameDiag ha i j

theorem dMetricAlg_flrw (a ad : ℝ) : dMetricAlg (frameDiag a) (flrwDe ad) = flrwdg a ad := by
  funext c i j
  fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp [dMetricAlg, Fin.sum_univ_four, minkowskiEta, frameDiag, flrwDe, frameD, flrwdg,
      Matrix.diagonal_apply] <;> ring

theorem christoffelJ_flrw {a : ℝ} (ha : a ≠ 0) (ad : ℝ) :
    christoffelJ (frameDiag a) (flrwDe ad) = flrwGamma a ad := by
  unfold christoffelJ
  rw [dMetricAlg_flrw, show (fun i j => metricInv (frameDiag a) i j) = flrwGinv a from
    funext fun i => funext fun j => metricInv_frameDiag ha i j]
  exact flrw_christoffel ha ad

/-! ### The `ΓΓ` form at the FLRW Christoffel symbols -/

theorem qForm_flrw {a : ℝ} (ha : a ≠ 0) (ad : ℝ) :
    qForm (flrwGinv a) (flrwGamma a ad) (flrwGamma a ad) = -(6 * ad ^ 2 / a ^ 2) := by
  simp [qForm, Fin.sum_univ_four, flrwGinv, flrwGamma]
  field_simp
  ring

theorem qForm_flrw_right {a : ℝ} (ha : a ≠ 0) (ad : ℝ) (X : T3) :
    qForm (flrwGinv a) (flrwGamma a ad) X =
      -(3 * ad / a) * X 0 0 0 + ad / a ^ 3 * (X 0 1 1 + X 0 2 2 + X 0 3 3) -
        ad / a * (X 1 0 1 + X 2 0 2 + X 3 0 3) - 2 * ad / a * (X 1 1 0 + X 2 2 0 + X 3 3 0) := by
  simp [qForm, Fin.sum_univ_four, flrwGinv, flrwGamma]
  field_simp
  ring

theorem qForm_flrw_left {a : ℝ} (ha : a ≠ 0) (ad : ℝ) (X : T3) :
    qForm (flrwGinv a) X (flrwGamma a ad) =
      3 * ad / a * X 0 0 0 - 2 * ad / a ^ 3 * (X 0 1 1 + X 0 2 2 + X 0 3 3) +
        3 * ad / a * (X 1 0 1 + X 2 0 2 + X 3 0 3) - 3 * ad / a * (X 1 1 0 + X 2 2 0 + X 3 3 0) := by
  simp [qForm, Fin.sum_univ_four, flrwGinv, flrwGamma]
  field_simp
  ring

theorem qForm_flrw_metric {a : ℝ} (ha : a ≠ 0) (ad : ℝ) (Y : T2) :
    qForm Y (flrwGamma a ad) (flrwGamma a ad) =
      3 * ad ^ 2 / a ^ 2 * Y 0 0 - ad ^ 2 * (Y 1 1 + Y 2 2 + Y 3 3) := by
  simp [qForm, Fin.sum_univ_four, flrwGamma]
  field_simp
  ring

/-! ### The symmetric coframe lift and its derivative at the FLRW coframe -/

theorem metricLiftL_apply (e k : CoframeFibre) (A μ : Fin 4) :
    metricLiftL e k A μ = -(1 / 2) * ∑ α, ∑ β, e A α * metricAt e μ β * k α β := rfl

/-- `D_e ė(e)[d](k) = -½ (d g k + e δ_d g k)`. -/
theorem fderiv_metricLiftL_apply (e d k : CoframeFibre) (A μ : Fin 4) :
    fderiv ℝ metricLiftL e d k A μ =
      -(1 / 2) * ∑ α, ∑ β, (d A α * metricAt e μ β + e A α * metricVar e d μ β) * k α β := by
  have hd : DifferentiableAt ℝ metricLiftL e :=
    (contDiff_metricLiftL (n := 1)).differentiable one_ne_zero e
  have h1 := (hasDerivAt_line_of_differentiableAt hd d).clm_apply (hasDerivAt_const (0 : ℝ) k)
  simp only [map_zero, add_zero] at h1
  have h2 : HasDerivAt (fun s : ℝ => metricLiftL (e + s • d) k A μ)
      (fderiv ℝ metricLiftL e d k A μ) 0 :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp h1 A) μ
  have h3 : HasDerivAt (fun s : ℝ => metricLiftL (e + s • d) k A μ)
      (-(1 / 2) * ∑ α, ∑ β, (d A α * metricAt e μ β + e A α * metricVar e d μ β) * k α β) 0 := by
    simp only [metricLiftL_apply]
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ => ?_)
    have he : HasDerivAt (fun s : ℝ => (e + s • d) A α) (d A α) 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d A α)).const_add (e A α)
    have hg : HasDerivAt (fun s : ℝ => metricAt (e + s • d) μ β) (metricVar e d μ β) 0 := by
      simpa using hasDerivAt_metricAt_line e d 0 μ β
    refine ((he.mul hg).mul_const (k α β)).congr_deriv ?_
    simp
  exact h2.unique h3

/-- The symmetric coframe lift at `diag(1,a,a,a)`. -/
theorem metricLift_frameDiag (a : ℝ) (k : CoframeFibre) (A μ : Fin 4) :
    metricLiftL (frameDiag a) k A μ =
      -(1 / 2) * (frameDiag a A A * flrwG a μ μ * k A μ) := by
  rw [metricLiftL_apply]
  simp only [metricAt_frameDiag]
  fin_cases A <;> fin_cases μ <;> simp [Fin.sum_univ_four, frameDiag, flrwG]

/-- The metric variation at `diag(1,a,a,a)`: `δg_{ρσ} = c_σ N_{σρ} + c_ρ N_{ρσ}`, `c = (-1,a,a,a)`. -/
theorem metricVar_frameDiag (a : ℝ) (N : CoframeFibre) (ρ σ : Fin 4) :
    metricVar (frameDiag a) N ρ σ =
      (if σ = 0 then -1 else a) * N σ ρ + (if ρ = 0 then -1 else a) * N ρ σ := by
  fin_cases ρ <;> fin_cases σ <;>
    simp [metricVar, Fin.sum_univ_four, minkowskiEta, frameDiag, Matrix.diagonal_apply] <;> ring

theorem ginvVar_frameDiag {a : ℝ} (ha : a ≠ 0) (N : CoframeFibre) (μ ν : Fin 4) :
    ginvVar (frameDiag a) N μ ν =
      -(flrwGinv a μ μ * metricVar (frameDiag a) N μ ν * flrwGinv a ν ν) := by
  simp only [ginvVar, metricInv_frameDiag ha]
  congr 1
  fin_cases μ <;> fin_cases ν <;> simp [Fin.sum_univ_four, flrwGinv]

theorem fderiv_metricLift_flrw (a ad : ℝ) (k : CoframeFibre) (c A μ : Fin 4) :
    fderiv ℝ metricLiftL (frameDiag a) (flrwDe ad c) k A μ =
      if c = 0 then -(1 / 2) * ((frameD A A * ad * flrwG a μ μ +
        frameDiag a A A * flrwdg a ad 0 μ μ) * k A μ) else 0 := by
  rw [fderiv_metricLiftL_apply]
  by_cases hc : c = 0
  · subst hc
    simp only [metricAt_frameDiag, metricVar_frameDiag, if_true]
    fin_cases A <;> fin_cases μ <;>
      simp [Fin.sum_univ_four, frameDiag, flrwG, flrwDe, frameD, flrwdg] <;> first | ring1 | (ring_nf; simp) | (ring_nf; done) | simp
  · simp [flrwDe, hc, metricVar]

/-! ### The gravitational covector at the FLRW jet -/

/-- **The gravitational first-variation covector at the flat FLRW jet**, on an arbitrary test
jet `(k, ∂k)`. -/
theorem gravVar_flrw {Ysec : Type} (θ : CoefficientBank Ysec) {a : ℝ} (ha : 0 < a) (ad : ℝ)
    (k : CoframeFibre) (dk : CoframeJet) :
    gravVar θ (frameDiag a) (flrwDe ad) (metricLiftL (frameDiag a) k)
        (fun μ => fderiv ℝ metricLiftL (frameDiag a) (flrwDe ad μ) k +
          metricLiftL (frameDiag a) (dk μ)) =
      (4 * θ.kappa)⁻¹ * (2 * (3 * a * ad ^ 2 - θ.Lambda * a ^ 3) * k 0 0 +
        2 * (7 * a ^ 3 * ad ^ 2 + θ.Lambda * a ^ 5) * (k 1 1 + k 2 2 + k 3 3) +
        4 * a ^ 4 * ad * (dk 0 1 1 + dk 0 2 2 + dk 0 3 3) +
        a ^ 2 * ad * (dk 1 0 1 + dk 1 1 0 + dk 2 0 2 + dk 2 2 0 + dk 3 0 3 + dk 3 3 0)) := by
  have ha0 : a ≠ 0 := ha.ne'
  unfold gravVar
  rw [volFactor_frameDiag ha, christoffelJ_flrw ha0, ginvT_frameDiag ha0, qForm_flrw ha0,
    qForm_flrw_right ha0, qForm_flrw_left ha0, qForm_flrw_metric ha0]
  simp only [volVar, christoffelVar, ginvT_frameDiag ha0, dMetricAlg_flrw, Pi.add_apply,
    metricInv_frameDiag ha0, volFactor_frameDiag ha, ginvVar_frameDiag ha0, christoffel,
    dMetricAlg, metricVar_frameDiag, metricLift_frameDiag, fderiv_metricLift_flrw,
    Fin.sum_univ_four]
  simp [flrwGinv, flrwdg, flrwG, frameDiag, frameD, flrwDe, minkowskiEta, Matrix.diagonal_apply]
  field_simp
  ring

/-! ### The full gravitational covector at a homogeneous jet -/

section Covectors

variable {C : Type} [Fintype C] {Ysec : Type}

/-- **`gravCov` at the FLRW jet.** -/
theorem gravCov_flrw (θ : CoefficientBank Ysec) {a : ℝ} (ha : 0 < a) (ad : ℝ) {J : RJet C}
    (hJe : J.e = frameDiag a) (hJd : J.de = flrwDe ad) (T : RJet C) :
    gravCov θ J T =
      (4 * θ.kappa)⁻¹ * (2 * (3 * a * ad ^ 2 - θ.Lambda * a ^ 3) * T.e 0 0 +
        2 * (7 * a ^ 3 * ad ^ 2 + θ.Lambda * a ^ 5) * (T.e 1 1 + T.e 2 2 + T.e 3 3) +
        4 * a ^ 4 * ad * (T.de 0 1 1 + T.de 0 2 2 + T.de 0 3 3) +
        a ^ 2 * ad * (T.de 1 0 1 + T.de 1 1 0 + T.de 2 0 2 + T.de 2 2 0 + T.de 3 0 3 +
          T.de 3 3 0)) := by
  have hGL : J.e ∈ coframeGL := hJe ▸ frameDiag_mem_GL ha.ne'
  rw [gravCov_eq_gravVar θ hGL T]
  have h1 : (redVar J T).e = metricLiftL (frameDiag a) T.e := by
    simp [redVar, hJe]
  have h2 : (redVar J T).de = fun μ => fderiv ℝ metricLiftL (frameDiag a) (flrwDe ad μ) T.e +
      metricLiftL (frameDiag a) (T.de μ) := by
    simp [redVar, hJe, hJd]
  rw [h1, h2, hJe, hJd, gravVar_flrw θ ha ad T.e T.de]

/-! ### The Standard-Model covectors at a homogeneous Higgs jet -/

theorem hInnerReL_comm (u v : HiggsFibre) : hInnerReL u v = hInnerReL v u := by
  simp only [hInnerReL, mkBilinL_apply, hInner, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]
  ring

/-- `fderiv √|g| = δ√|g|` on the chart. -/
theorem fderiv_volFactor_eq {e : CoframeFibre} (he : e ∈ coframeGL) (M : CoframeFibre) :
    fderiv ℝ volFactor e M = volVar e M :=
  (hasDerivAt_line_of_differentiableAt
    ((contDiffAt_volFactor he (n := 1)).differentiableAt one_ne_zero) M).unique
    (hasDerivAt_volFactor_line he M)

/-- The metric derivative of the Higgs kinetic coefficient. -/
theorem fderiv_higgsCoeff_eq {e : CoframeFibre} (he : e ∈ coframeGL) (M : CoframeFibre)
    (K K' : Fin 4 → HiggsFibre) :
    fderiv ℝ higgsCoeff e M K K' =
      -(∑ μ, ∑ ν, ginvVar e M μ ν * hInnerReL (K μ) (K' ν)) * volFactor e -
        (∑ μ, ∑ ν, metricInv e μ ν * hInnerReL (K μ) (K' ν)) * volVar e M := by
  have hd : DifferentiableAt ℝ higgsCoeff e :=
    (contDiffAt_higgsCoeff he (n := 1)).differentiableAt one_ne_zero
  have h0 := hasDerivAt_line_of_differentiableAt
    (F := (Fin 4 → HiggsFibre) →L[ℝ] (Fin 4 → HiggsFibre) →L[ℝ] ℝ) hd M
  have h1 : HasDerivAt (fun s : ℝ => higgsCoeff (e + s • M) K K') (fderiv ℝ higgsCoeff e M K K') 0 := by
    have h := (h0.clm_apply (hasDerivAt_const (0 : ℝ) K)).clm_apply (hasDerivAt_const (0 : ℝ) K')
    refine h.congr_deriv ?_
    simp only [map_zero, add_zero, zero_add, ContinuousLinearMap.add_apply]
  have h2 : HasDerivAt (fun s : ℝ => higgsCoeff (e + s • M) K K')
      (-(∑ μ, ∑ ν, ginvVar e M μ ν * hInnerReL (K μ) (K' ν)) * volFactor e -
        (∑ μ, ∑ ν, metricInv e μ ν * hInnerReL (K μ) (K' ν)) * volVar e M) 0 := by
    simp only [higgsCoeff_apply]
    have hs : HasDerivAt (fun s : ℝ => ∑ μ, ∑ ν, metricInv (e + s • M) μ ν * hInnerReL (K μ) (K' ν))
        (∑ μ, ∑ ν, ginvVar e M μ ν * hInnerReL (K μ) (K' ν)) 0 :=
      HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ =>
        (hasDerivAt_metricInv_line he M μ ν).mul_const _
    have := hs.neg.mul (hasDerivAt_volFactor_line he M)
    refine this.congr_deriv ?_
    simp only [zero_smul, add_zero, volVar, Pi.neg_apply]
    ring
  exact h1.unique h2

/-- **The bosonic Standard-Model covector at a homogeneous FLRW–Higgs jet** (`A = 0`, `F = 0`,
`K = (K₀, 0, 0, 0)`). -/
theorem bosonCov_flrw (θ : CoefficientBank Ysec) {a : ℝ} (ha : 0 < a) {J : RJet C}
    (hJe : J.e = frameDiag a) (hJA : J.A = 0) (hJF : J.F = 0) (K₀ : HiggsFibre)
    (hJK : J.K = fun μ => if μ = 0 then K₀ else 0) (T : RJet C) :
    bosonCov θ J T =
      -(T.e 0 0) * a ^ 3 * hInnerReL K₀ K₀ +
        a ^ 3 * (T.e 0 0 - a ^ 2 * (T.e 1 1 + T.e 2 2 + T.e 3 3)) / 2 * hInnerReL K₀ K₀ +
        2 * a ^ 3 * hInnerReL K₀ (T.K 0 + higgsAct (T.A 0) J.H) -
        θ.lambdaH * (2 * (higgsQuad J.H - θ.vH ^ 2) * (2 * hInnerReL T.H J.H) * a ^ 3 +
          (higgsQuad J.H - θ.vH ^ 2) ^ 2 *
            (a ^ 3 * (T.e 0 0 - a ^ 2 * (T.e 1 1 + T.e 2 2 + T.e 3 3)) / 2)) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hGL : frameDiag a ∈ coframeGL := frameDiag_mem_GL ha0
  have hvv : volVar (frameDiag a) (metricLiftL (frameDiag a) T.e) =
      a ^ 3 * (T.e 0 0 - a ^ 2 * (T.e 1 1 + T.e 2 2 + T.e 3 3)) / 2 := by
    simp only [volVar, volFactor_frameDiag ha, metricInv_frameDiag ha0, metricVar_frameDiag,
      metricLift_frameDiag, Fin.sum_univ_four]
    simp [flrwGinv, flrwG, frameDiag]
    field_simp
    ring
  have hgv : ginvVar (frameDiag a) (metricLiftL (frameDiag a) T.e) 0 0 = T.e 0 0 := by
    rw [ginvVar_frameDiag ha0, metricVar_frameDiag, metricLift_frameDiag]
    simp [flrwGinv, flrwG, frameDiag]
    ring
  rw [bosonCov_apply]
  simp only [bosonDeriv, redVar, RJet.mk_e, RJet.mk_F, RJet.mk_K, RJet.mk_H, hJe, hJF, hJA, hJK,
    map_zero, ContinuousLinearMap.zero_apply, mul_zero, add_zero, Finset.sum_const_zero,
    zero_add, fderiv_volFactor_eq hGL, fderiv_higgsCoeff_eq hGL, hvv, higgsCoeff_apply,
    volFactor_frameDiag ha, metricInv_frameDiag ha0]
  simp only [Kdot, hJA, Pi.zero_apply]
  have hz : ∀ X : HiggsFibre, higgsAct 0 X = 0 := fun X => by
    funext i; simp [higgsAct]
  simp only [hz, add_zero]
  simp only [Fin.sum_univ_four, hgv]
  simp only [flrwGinv, map_add]
  simp
  rw [hInnerReL_comm (T.K 0) K₀, hInnerReL_comm (higgsAct (T.A 0) J.H) K₀,
    hInnerReL_comm J.H T.H]
  ring

/-- **The Dirac–Yukawa covector vanishes at zero spinor jets.** -/
theorem diracCov_zero (FC : FermionCarrier Ysec) (θ : CoefficientBank Ysec) {J : RJet FC.C}
    (hJ : J.e ∈ coframeGL) (h1 : J.Ψ = 0) (h2 : J.dΨ = 0) (h3 : J.Ψb = 0) (h4 : J.dΨb = 0)
    (T : RJet FC.C) : diracCov FC θ J T = 0 := by
  rw [← fderiv_diracPt_redVar FC θ hJ T, (hasFDerivAt_diracPt FC θ hJ).2]
  have hp : ((0 : SpinorFibre FC.C), (0 : SpinorFibre FC.C)) = 0 := rfl
  have hq : ((0 : Fin 4 → SpinorFibre FC.C), (0 : Fin 4 → SpinorFibre FC.C)) = 0 := rfl
  simp only [diracDeriv, h1, h2, h3, h4, hp, hq, map_zero, ContinuousLinearMap.zero_apply,
    add_zero]

end Covectors

end HomogeneousCov
end EinsteinSM
end RenewalGeometry
