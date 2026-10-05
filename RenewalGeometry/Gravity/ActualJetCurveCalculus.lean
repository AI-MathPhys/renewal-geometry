/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetSmoothness

/-!
# The jet formulas of the actual-jet system are the derivatives of their fields

Infrastructure for the bridge from smooth slab fields to `ActualJetSystem.ActualJet`
(`prop:coupled-bootstrap` of the Einstein–Standard-Model action-closure manuscript: "the state
`𝒰_h` is built from the actual derivatives and curvatures of `z_h`; no independent jet variables are
supplied").

The derivative jets of `FrameCurvature`, `HarmonicDefect`, `ActualJetWriter`, `ActualJetGauge` and
`ActualJetSpinor` (`dipg`, `ddipg`, `dginv`, `dchr`, `dcv1`, `FrameJet.dP`, `FrameJet.dGc`, `dpJ`,
`dqJ`, `dFm`, `dfrT`, `dDH`, `dfrV`, `dcUp`, `dωc`, `dXc`, `drc`, …) are defined by the product rule.
This file proves, for each of them, that along a differentiable curve of arguments the
corresponding formula has exactly that derivative (`HasDerivAt`), given the derivatives of the
arguments.  Applied to the lines `s ↦ x + s e_δ` through a point of space-time, these give the
coordinate derivatives of the fields built from smooth slab fields.

All statements are pure calculus on curves `ℝ → (jets)`; no renewal notions.
-/

open Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.JetCurve

open FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth
  ActualJetGauge SpinorProlongation TwistedHalfRicci

set_option linter.unusedSectionVars false

/-! ### Metric-sector formulas -/

section Metric

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `∂_δ g(X, Y) = dipg`. -/
theorem hasDerivAt_ipg {g : ℝ → n → n → ℝ} {X Y : ℝ → n → ℝ} {t : ℝ} {dg : n → n → n → ℝ}
    {dX dY : n → n → ℝ} (δ : n) (hg : ∀ μ ν, HasDerivAt (fun s => g s μ ν) (dg δ μ ν) t)
    (hX : ∀ μ, HasDerivAt (fun s => X s μ) (dX δ μ) t)
    (hY : ∀ ν, HasDerivAt (fun s => Y s ν) (dY δ ν) t) :
    HasDerivAt (fun s => ipg (g s) (X s) (Y s)) (dipg (g t) dg (X t) dX (Y t) dY δ) t := by
  unfold ipg dipg
  refine HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ => ?_
  exact (((hg μ ν).fun_mul (hX μ)).fun_mul (hY ν)).congr_deriv (by ring)

/-- `∂_δ (∂_γ g(X, Y)) = ddipg`. -/
theorem hasDerivAt_dipg {g : ℝ → n → n → ℝ} {dg : ℝ → n → n → n → ℝ} {X Y : ℝ → n → ℝ}
    {dX dY : ℝ → n → n → ℝ} {t : ℝ} {ddg : n → n → n → n → ℝ} {ddX ddY : n → n → n → ℝ}
    (δ γ : n) (hg : ∀ μ ν, HasDerivAt (fun s => g s μ ν) (dg t δ μ ν) t)
    (hdg : ∀ μ ν, HasDerivAt (fun s => dg s γ μ ν) (ddg δ γ μ ν) t)
    (hX : ∀ μ, HasDerivAt (fun s => X s μ) (dX t δ μ) t)
    (hdX : ∀ μ, HasDerivAt (fun s => dX s γ μ) (ddX δ γ μ) t)
    (hY : ∀ ν, HasDerivAt (fun s => Y s ν) (dY t δ ν) t)
    (hdY : ∀ ν, HasDerivAt (fun s => dY s γ ν) (ddY δ γ ν) t) :
    HasDerivAt (fun s => dipg (g s) (dg s) (X s) (dX s) (Y s) (dY s) γ)
      (ddipg (g t) (dg t) ddg (X t) (dX t) ddX (Y t) (dY t) ddY δ γ) t := by
  unfold dipg ddipg
  refine HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ => ?_
  have h1 := ((hdg μ ν).fun_mul (hX μ)).fun_mul (hY ν)
  have h2 := ((hg μ ν).fun_mul (hdX μ)).fun_mul (hY ν)
  have h3 := ((hg μ ν).fun_mul (hX μ)).fun_mul (hdY ν)
  exact ((h1.fun_add h2).fun_add h3).congr_deriv (by ring)

/-- The derivative of the inverse metric along a curve: `∂g⁻¹ = -g⁻¹ ∂g g⁻¹` (`dginv`). -/
theorem hasDerivAt_ginvOf {g : ℝ → Fin 4 → Fin 4 → ℝ} {t : ℝ} {dg : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (δ : Fin 4) (hg : ∀ μ ν, HasDerivAt (fun s => g s μ ν) (dg δ μ ν) t)
    (hdet : (Matrix.of (g t)).det ≠ 0) (l σ : Fin 4) :
    HasDerivAt (fun s => ginvOf (g s) l σ) (dginv (ginvOf (g t)) dg δ l σ) t := by
  have hgc : HasDerivAt g (fun μ ν => dg δ μ ν) t :=
    hasDerivAt_pi.2 fun μ => hasDerivAt_pi.2 fun ν => hg μ ν
  -- differentiability of the inverse along the curve
  have hdiff : ∀ i j, HasDerivAt (fun s => ginvOf (g s) i j)
      (fderiv ℝ (fun g => ginvOf g i j) (g t) (fun μ ν => dg δ μ ν)) t := fun i j =>
    (((ActualJetSmooth.contDiffAt_ginvOf' hdet i j).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt
      t hgc
  set D : Fin 4 → Fin 4 → ℝ := fun i j =>
    fderiv ℝ (fun g => ginvOf g i j) (g t) (fun μ ν => dg δ μ ν) with hD
  -- the identity `g g⁻¹ = 1` along the curve
  have hU : IsUnit (Matrix.of (g t)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hev : ∀ᶠ s in nhds t, (Matrix.of (g s)).det ≠ 0 := by
    have hc : ContinuousAt (fun s => (Matrix.of (g s)).det) t :=
      (Continuous.matrix_det (A := fun M : Fin 4 → Fin 4 → ℝ => Matrix.of M)
        continuous_id).continuousAt.comp hgc.continuousAt
    exact hc.eventually (isOpen_ne.mem_nhds hdet)
  have hmul : ∀ (M : Fin 4 → Fin 4 → ℝ), (Matrix.of M).det ≠ 0 → ∀ a c,
      ∑ b, M a b * ginvOf M b c = if a = c then 1 else 0 := by
    intro M hM a c
    have hUM : IsUnit (Matrix.of M).det := isUnit_iff_ne_zero.mpr hM
    have h := Matrix.mul_nonsing_inv (Matrix.of M) hUM
    have := congrFun (congrFun h a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [ginvOf] using this
  have hmul' : ∀ (M : Fin 4 → Fin 4 → ℝ), (Matrix.of M).det ≠ 0 → ∀ a c,
      ∑ b, ginvOf M a b * M b c = if a = c then 1 else 0 := by
    intro M hM a c
    have hUM : IsUnit (Matrix.of M).det := isUnit_iff_ne_zero.mpr hM
    have h := Matrix.nonsing_inv_mul (Matrix.of M) hUM
    have := congrFun (congrFun h a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [ginvOf] using this
  -- differentiate `Σ_b g_{ab} g^{bc} = δ_{ac}`
  have hzero : ∀ a c, ∑ b, (dg δ a b * ginvOf (g t) b c + g t a b * D b c) = 0 := by
    intro a c
    have h1 : HasDerivAt (fun s => ∑ b, g s a b * ginvOf (g s) b c)
        (∑ b, (dg δ a b * ginvOf (g t) b c + g t a b * D b c)) t :=
      HasDerivAt.fun_sum fun b _ => (hg a b).fun_mul (hdiff b c)
    have h2 : HasDerivAt (fun s => ∑ b, g s a b * ginvOf (g s) b c) 0 t := by
      refine (hasDerivAt_const t (if a = c then (1 : ℝ) else 0)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with s hs
      exact hmul (g s) hs a c
    exact h1.unique h2
  have hDeq : D l σ = dginv (ginvOf (g t)) dg δ l σ := by
    unfold dginv
    have e1 : D l σ = ∑ a, (if l = a then (1 : ℝ) else 0) * D a σ := by simp
    rw [e1]
    simp_rw [← hmul' (g t) hdet l]
    have e2 : ∑ a, (∑ b, ginvOf (g t) l b * g t b a) * D a σ =
        ∑ b, ginvOf (g t) l b * ∑ a, g t b a * D a σ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
    rw [e2]
    have e3 : ∀ b, ∑ a, g t b a * D a σ = -∑ a, dg δ b a * ginvOf (g t) a σ := by
      intro b
      have := hzero b σ
      rw [Finset.sum_add_distrib] at this
      linarith
    simp_rw [e3]
    simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [← hDeq]
  exact hdiff l σ

/-- The frame components `frU(g⁻¹)` along a curve: the derivative is the frame jet. -/
theorem hasDerivAt_frU {gi : ℝ → IMet} {t : ℝ} {dgi : Fin 4 → IMet} (δ : Fin 4)
    (hgi : ∀ l σ, HasDerivAt (fun s => gi s l σ) (dgi δ l σ) t) (h : IsLorChart (gi t))
    (A μ : Fin 4) :
    HasDerivAt (fun s => frU (gi s) A μ) (ActualJetFrame.frameJet (gi t) dgi δ A μ) t := by
  have hc : HasDerivAt gi (dgi δ) t :=
    hasDerivAt_pi.2 fun l => hasDerivAt_pi.2 fun σ => hgi l σ
  exact hasDerivAt_frU_comp hc h A μ

/-- The Christoffel symbols along a curve: `dchr`. -/
theorem hasDerivAt_chr {gi : ℝ → n → n → ℝ} {dg : ℝ → n → n → n → ℝ} {t : ℝ}
    {ddg : n → n → n → n → ℝ} (δ : n)
    (hgi : ∀ l σ, HasDerivAt (fun s => gi s l σ) (dginv (gi t) (dg t) δ l σ) t)
    (hdg : ∀ α μ ν, HasDerivAt (fun s => dg s α μ ν) (ddg δ α μ ν) t) (l μ ν : n) :
    HasDerivAt (fun s => chr (gi s) (dg s) l μ ν) (dchr (gi t) (dg t) ddg δ l μ ν) t := by
  unfold chr dchr dchr1 dchr2
  have h : HasDerivAt (fun s => ∑ σ, gi s l σ * (dg s μ σ ν + dg s ν σ μ - dg s σ μ ν))
      (∑ σ, (dginv (gi t) (dg t) δ l σ * (dg t μ σ ν + dg t ν σ μ - dg t σ μ ν) +
        gi t l σ * (ddg δ μ σ ν + ddg δ ν σ μ - ddg δ σ μ ν))) t :=
    HasDerivAt.fun_sum fun σ _ => (hgi l σ).fun_mul (((hdg μ σ ν).fun_add (hdg ν σ μ)).fun_sub (hdg σ μ ν))
  refine (h.const_mul (1 / 2 : ℝ)).congr_deriv ?_
  rw [Finset.sum_add_distrib]
  ring

/-- `∇_γV^μ` along a curve: `dcv1`. -/
theorem hasDerivAt_cv1 {Γ : ℝ → n → n → n → ℝ} {V : ℝ → n → ℝ} {dV : ℝ → n → n → ℝ} {t : ℝ}
    {dΓ : n → n → n → n → ℝ} {ddV : n → n → n → ℝ} (δ : n)
    (hΓ : ∀ l μ ν, HasDerivAt (fun s => Γ s l μ ν) (dΓ δ l μ ν) t)
    (hV : ∀ μ, HasDerivAt (fun s => V s μ) (dV t δ μ) t)
    (hdV : ∀ γ μ, HasDerivAt (fun s => dV s γ μ) (ddV δ γ μ) t) (γ μ : n) :
    HasDerivAt (fun s => cv1 (Γ s) (V s) (dV s) γ μ)
      (dcv1 (Γ t) dΓ (V t) (dV t) ddV δ γ μ) t := by
  unfold cv1 dcv1
  exact (hdV γ μ).fun_add (HasDerivAt.fun_sum fun σ _ => (hΓ μ γ σ).fun_mul (hV σ))

/-- `C^l = g^{αβ}Γ^l_{αβ}` along a curve: `dcUp`. -/
theorem hasDerivAt_cUp {gi : ℝ → n → n → ℝ} {Γ : ℝ → n → n → n → ℝ} {t : ℝ}
    {dgi : n → n → n → ℝ} {dΓ : n → n → n → n → ℝ} (δ : n)
    (hgi : ∀ a b, HasDerivAt (fun s => gi s a b) (dgi δ a b) t)
    (hΓ : ∀ l a b, HasDerivAt (fun s => Γ s l a b) (dΓ δ l a b) t) (l : n) :
    HasDerivAt (fun s => cUp (gi s) (Γ s) l) (dcUp (gi t) dgi (Γ t) dΓ δ l) t := by
  unfold cUp dcUp
  exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => (hgi a b).fun_mul (hΓ l a b)

end Metric


/-! ### Bilinear and linear maps along curves -/

section Linear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A bilinear map of finite-dimensional spaces along curves (product rule). -/
theorem hasDerivAt_bilin (B : E →ₗ[ℝ] F →ₗ[ℝ] G) {f : ℝ → E} {g : ℝ → F} {f' : E} {g' : F}
    {t : ℝ} (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => B (f s) (g s)) (B f' (g t) + B (f t) g') t := by
  let B' : E →L[ℝ] F →L[ℝ] G :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] G) ≃ₗ[ℝ] (F →L[ℝ] G)).toLinearMap ∘ₗ B)
  have h1 : HasDerivAt (fun s => B' (f s)) (B' f') t := B'.hasFDerivAt.comp_hasDerivAt t hf
  have h2 := h1.clm_apply hg
  exact h2

/-- A linear map out of a finite-dimensional space along a curve. -/
theorem hasDerivAt_lin (T : E →ₗ[ℝ] G) {f : ℝ → E} {f' : E} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => T (f s)) (T f') t :=
  (LinearMap.toContinuousLinearMap T).hasFDerivAt.comp_hasDerivAt t hf

end Linear

/-! ### Gauge and Higgs formulas -/

section Gauge

variable {m : ℕ}

/-- The Lie bracket of `gl(m)` as a bilinear map. -/
def lieB (m : ℕ) : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] MatLie m :=
  LinearMap.mk₂ ℝ (fun a b : MatLie m => ⁅a, b⁆) add_lie smul_lie lie_add lie_smul

theorem hasDerivAt_lie {f g : ℝ → MatLie m} {f' g' : MatLie m} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => ⁅f s, g s⁆) (⁅f', g t⁆ + ⁅f t, g'⁆) t :=
  hasDerivAt_bilin (lieB m) hf hg

/-- The field strength along a curve: `dFm`. -/
theorem hasDerivAt_Fm {A : ℝ → Fin 4 → MatLie m} {dA : ℝ → Fin 4 → Fin 4 → MatLie m} {t : ℝ}
    {ddA : Fin 4 → Fin 4 → Fin 4 → MatLie m} (δ : Fin 4)
    (hA : ∀ μ, HasDerivAt (fun s => A s μ) (dA t δ μ) t)
    (hdA : ∀ μ ν, HasDerivAt (fun s => dA s μ ν) (ddA δ μ ν) t) (μ ν : Fin 4) :
    HasDerivAt (fun s => ActualJetGauge.Fm (A s) (dA s) μ ν)
      (ActualJetGauge.dFm (A t) (dA t) ddA δ μ ν) t := by
  unfold ActualJetGauge.Fm ActualJetGauge.dFm fieldStrength
  exact (((hdA μ ν).sub (hdA ν μ)).add (hasDerivAt_lie (hA μ) (hA ν))).congr_deriv (by abel)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]

/-- The Lie module action as a bilinear map. -/
def lieMod (m : ℕ) (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V] :
    MatLie m →ₗ[ℝ] V →ₗ[ℝ] V :=
  LinearMap.mk₂ ℝ (fun (a : MatLie m) (v : V) => ⁅a, v⁆) add_lie smul_lie lie_add lie_smul

theorem hasDerivAt_lieMod {f : ℝ → MatLie m} {g : ℝ → V} {f' : MatLie m} {g' : V} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => ⁅f s, g s⁆) (⁅f', g t⁆ + ⁅f t, g'⁆) t :=
  hasDerivAt_bilin (lieMod m V) hf hg

/-- The covariant Higgs derivative along a curve: `dDH`. -/
theorem hasDerivAt_DH {A : ℝ → Fin 4 → MatLie m} {dA : ℝ → Fin 4 → Fin 4 → MatLie m}
    {H : ℝ → V} {dH : ℝ → Fin 4 → V} {t : ℝ} {ddH : Fin 4 → Fin 4 → V} (δ : Fin 4)
    (hA : ∀ μ, HasDerivAt (fun s => A s μ) (dA t δ μ) t) (hH : HasDerivAt H (dH t δ) t)
    (hdH : ∀ μ, HasDerivAt (fun s => dH s μ) (ddH δ μ) t) (μ : Fin 4) :
    HasDerivAt (fun s => ActualJetGauge.DH (A s) (H s) (dH s) μ)
      (ActualJetGauge.dDH (A t) (dA t) (H t) (dH t) ddH δ μ) t := by
  unfold ActualJetGauge.DH ActualJetGauge.dDH
  exact ((hdH μ).add (hasDerivAt_lieMod (hA μ) hH)).congr_deriv (by abel)

end Gauge

/-! ### Frame contractions -/

section Frame

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- Frame components of a tensor along a curve: `dfrT`. -/
theorem hasDerivAt_frT {fr : ℝ → Fin 4 → Fin 4 → ℝ} {T : ℝ → Fin 4 → Fin 4 → M} {t : ℝ}
    {de : Fin 4 → Fin 4 → Fin 4 → ℝ} {dT : Fin 4 → Fin 4 → Fin 4 → M} (δ : Fin 4)
    (hfr : ∀ A μ, HasDerivAt (fun s => fr s A μ) (de δ A μ) t)
    (hT : ∀ μ ν, HasDerivAt (fun s => T s μ ν) (dT δ μ ν) t) (b c : Fin 4) :
    HasDerivAt (fun s => ∑ μ, ∑ ν, (fr s b μ * fr s c ν) • T s μ ν)
      (∑ μ, ∑ ν, ((de δ b μ * fr t c ν + fr t b μ * de δ c ν) • T t μ ν +
        (fr t b μ * fr t c ν) • dT δ μ ν)) t := by
  refine HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ => ?_
  exact (((hfr b μ).fun_mul (hfr c ν)).fun_smul (hT μ ν)).congr_deriv (by
    rw [add_comm])

/-- Frame components of a covector along a curve. -/
theorem hasDerivAt_frV {fr : ℝ → Fin 4 → Fin 4 → ℝ} {X : ℝ → Fin 4 → M} {t : ℝ}
    {de : Fin 4 → Fin 4 → Fin 4 → ℝ} {dX : Fin 4 → Fin 4 → M} (δ : Fin 4)
    (hfr : ∀ A μ, HasDerivAt (fun s => fr s A μ) (de δ A μ) t)
    (hX : ∀ μ, HasDerivAt (fun s => X s μ) (dX δ μ) t) (B : Fin 4) :
    HasDerivAt (fun s => ∑ μ, fr s B μ • X s μ)
      (∑ μ, (de δ B μ • X t μ + fr t B μ • dX δ μ)) t :=
  HasDerivAt.fun_sum fun μ _ => ((hfr B μ).fun_smul (hX μ)).congr_deriv (by rw [add_comm])

/-- The dual vector along a curve (linear). -/
theorem hasDerivAt_dualVec {S : ℝ → Fin 3 → Fin 3 → M} {t : ℝ} {dS : Fin 3 → Fin 3 → M}
    (hS : ∀ b c, HasDerivAt (fun s => S s b c) (dS b c) t) (a : Fin 3) :
    HasDerivAt (fun s => ActualJetGauge.dualVec (S s) a) (ActualJetGauge.dualVec dS a) t := by
  unfold ActualJetGauge.dualVec
  exact (HasDerivAt.fun_sum fun b _ => HasDerivAt.fun_sum fun c _ =>
    (hS b c).const_smul (eps3 a b c)).const_smul _

end Frame

/-! ### The spinor formulas -/

section Spinor

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

/-- `spinPart Fr W` acting on a vector, along curves (bilinear in `(W, v)`). -/
theorem hasDerivAt_spinPart_apply (Fr : CliffordFrame (Fin 4) (Module.End ℝ S))
    {W : ℝ → Fin 4 → Fin 4 → ℝ} {v : ℝ → S} {W' : Fin 4 → Fin 4 → ℝ} {v' : S} {t : ℝ}
    (hW : ∀ c d, HasDerivAt (fun s => W s c d) (W' c d) t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => spinPart Fr (W s) • v s)
      (spinPart Fr W' • v t + spinPart Fr (W t) • v') t := by
  have hexp : ∀ (W₀ : Fin 4 → Fin 4 → ℝ) (v₀ : S), spinPart Fr W₀ • v₀ =
      (1 / 4 : ℝ) • ∑ c, ∑ d, (Fr.ε c * Fr.ε d * W₀ c d) • ((Fr.c c * Fr.c d) v₀) := by
    intro W₀ v₀
    unfold spinPart
    simp only [Module.End.smul_def, LinearMap.smul_apply, LinearMap.sum_apply,
      Finset.sum_apply]
  simp_rw [hexp]
  have hT : ∀ c d, HasDerivAt (fun s => (Fr.c c * Fr.c d) (v s)) ((Fr.c c * Fr.c d) v') t :=
    fun c d => hasDerivAt_lin (Fr.c c * Fr.c d) hv
  have h := (HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
    ((((hasDerivAt_const t (Fr.ε c * Fr.ε d)).fun_mul (hW c d))).fun_smul (hT c d))).const_smul
      (1 / 4 : ℝ)
  refine h.congr_deriv ?_
  simp only [zero_mul, zero_add, smul_add, Finset.sum_add_distrib, map_smul]
  rw [add_comm]

end Spinor
end RenewalGeometry.JetCurve
