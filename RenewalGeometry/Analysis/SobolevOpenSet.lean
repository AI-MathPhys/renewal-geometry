/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Sobolev space `W^{1,2}(Ω)` on open subsets of `ℝ^d` via weak derivatives

Generic infrastructure (no renewal notions) for the local Sobolev steps of the
Einstein–Standard-Model action-closure manuscript (`prop:orlicz`, `prop:sobolev-bosonic`,
`prop:covariant-higgs-endpoint`, `cor:stress-topology`).

The ambient space is `ℝ^ι = ι → ℝ` for a finite index type `ι`, with Lebesgue measure `volume`
(the product measure).  We use `ι → ℝ` rather than `EuclideanSpace ℝ ι` because (i) its Lebesgue
measure is literally the product measure, which is what Mathlib's torus integration formula
`UnitAddTorus.integral_preimage` uses, so the periodisation bridge to `𝕋^ι = UnitAddTorus ι`
needs no change of measure, and (ii) Mathlib's integration by parts
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`), the Gagliardo–Nirenberg–Sobolev
inequality (`eLpNorm_le_eLpNorm_fderiv_of_eq`) and the mollifier calculus all apply to any
finite-dimensional normed space with an additive Haar measure.  The sup norm on `ι → ℝ` only
enters through equivalent constants.

* `pd φ i x = Dφ(x) e_i`: the classical partial derivative.
* `IsTest Ω φ`: `φ ∈ C_c^∞(Ω, ℝ)` (smooth, compact support, `tsupport φ ⊆ Ω`).
* `HasWeakPartial Ω i u g`: `g` is the **weak `i`-th partial derivative** of `u : ℝ^ι → ℂ` on
  `Ω`, i.e. `∫ ∂_iφ · u = -∫ φ · g` for every real test function `φ ∈ C_c^∞(Ω)`.
* `MemW12 Ω u g`: `u ∈ L²(Ω)`, weak partials `g i ∈ L²(Ω)` — the Sobolev space
  `W^{1,2}(Ω) = H¹(Ω)`, with the weak gradient carried as data (it is unique a.e.,
  `HasWeakPartial.ae_eq`).
* `w12Norm Ω u g = ‖u‖_{L²(Ω)} + Σ_i ‖g i‖_{L²(Ω)}` (equivalent to the Hilbert norm).

Main results of this file:

* `HasWeakPartial.complex_test`: the defining identity extends to complex-valued test functions;
* `hasWeakPartial_of_contDiff`: a `C¹` function has its classical partials as weak partials
  (non-vacuity);
* `HasWeakPartial.ae_eq`: uniqueness of weak derivatives;
* `HasWeakPartial.mul_test` (**cutoff product rule**): for `χ ∈ C_c^∞(Ω)` and a weak partial
  `g` of `u` on `Ω`, the product `χ u` (extended by zero) has weak partial `χ g + ∂_iχ u` on all
  of `ℝ^ι`; `MemW12.mul_test` is the `W^{1,2}` version with the norm bound.

Continued in `SobolevTorusBridge.lean` (periodisation and the Fourier rule),
`SobolevLocalRellich.lean` (Rellich, compact support and interior), `SobolevCriticalEmbedding.lean`
(`H¹_c ↪ L^{2d/(d-2)}`), `SobolevBoxExtension.lean` (reflection extension for boxes) and
`SobolevBoxCompactness.lean` (Rellich and Sobolev on boxes, `prop:orlicz`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The classical partial derivative `∂_i φ(x) = Dφ(x) e_i` on `ℝ^ι`. -/
def pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : (ι → ℝ) → F) (i : ι)
    (x : ι → ℝ) : F :=
  fderiv ℝ φ x (Pi.single i 1)

/-- `φ ∈ C_c^∞(Ω, ℝ)`: a real test function on the set `Ω`. -/
structure IsTest (Ω : Set (ι → ℝ)) (φ : (ι → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ
  subset : tsupport φ ⊆ Ω

/-- `g` is the **weak `i`-th partial derivative** of `u` on `Ω`:
`∫ ∂_iφ · u = -∫ φ · g` for every `φ ∈ C_c^∞(Ω, ℝ)`.  The integrals are over `ℝ^ι`; since the
integrands vanish off `tsupport φ ⊆ Ω`, the values of `u, g` off `Ω` are irrelevant. -/
def HasWeakPartial (Ω : Set (ι → ℝ)) (i : ι) (u g : (ι → ℝ) → ℂ) : Prop :=
  ∀ φ : (ι → ℝ) → ℝ, IsTest Ω φ →
    ∫ x, ((pd φ i x : ℝ) : ℂ) * u x = -∫ x, ((φ x : ℝ) : ℂ) * g x

/-- **The Sobolev space `W^{1,2}(Ω) = H¹(Ω)`**: `u ∈ L²(Ω)` with weak partial derivatives
`g i ∈ L²(Ω)` for all `i`. -/
structure MemW12 (Ω : Set (ι → ℝ)) (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ) : Prop where
  memLp : MemLp u 2 (volume.restrict Ω)
  memLp_grad : ∀ i, MemLp (g i) 2 (volume.restrict Ω)
  weak : ∀ i, HasWeakPartial Ω i u (g i)

/-- The `W^{1,2}(Ω)` norm `‖u‖_{L²(Ω)} + Σ_i ‖∂_i u‖_{L²(Ω)}` (equivalent to the Hilbert norm
`(‖u‖² + Σ‖∂_iu‖²)^{1/2}`). -/
def w12Norm (Ω : Set (ι → ℝ)) (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ) : ℝ≥0∞ :=
  eLpNorm u 2 (volume.restrict Ω) + ∑ i, eLpNorm (g i) 2 (volume.restrict Ω)

/-! ### Elementary facts on test functions -/

theorem IsTest.continuous {Ω : Set (ι → ℝ)} {φ : (ι → ℝ) → ℝ} (h : IsTest Ω φ) :
    Continuous φ := h.smooth.continuous

theorem contDiff_pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : (ι → ℝ) → F}
    (h : ContDiff ℝ ∞ φ) (i : ι) : ContDiff ℝ ∞ (pd φ i) := by
  unfold pd
  exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem continuous_pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : (ι → ℝ) → F}
    (h : ContDiff ℝ 1 φ) (i : ι) : Continuous (pd φ i) := by
  unfold pd
  exact (h.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem hasCompactSupport_pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : (ι → ℝ) → F} (h : HasCompactSupport φ) (i : ι) : HasCompactSupport (pd φ i) :=
  h.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)

theorem tsupport_pd_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : (ι → ℝ) → F) (i : ι) : tsupport (pd φ i) ⊆ tsupport φ := by
  unfold pd
  exact (tsupport_fderiv_apply_subset ℝ (Pi.single i 1))

theorem IsTest.mono {Ω Ω' : Set (ι → ℝ)} {φ : (ι → ℝ) → ℝ} (h : IsTest Ω φ) (hΩ : Ω ⊆ Ω') :
    IsTest Ω' φ := ⟨h.smooth, h.compact, h.subset.trans hΩ⟩

/-- A continuous compactly supported function with support in `Ω`, times a function locally
integrable on `Ω`, is integrable. -/
theorem integrable_mul_of_locallyIntegrableOn {Ω : Set (ι → ℝ)} {u : (ι → ℝ) → ℂ}
    (hu : LocallyIntegrableOn u Ω) {ψ : (ι → ℝ) → ℂ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) :
    Integrable (fun x => ψ x * u x) := by
  have h1 : IntegrableOn u (tsupport ψ) := hu.integrableOn_compact_subset hs hc
  have h2 : IntegrableOn (fun x => ψ x * u x) (tsupport ψ) :=
    h1.continuousOn_mul hψ.continuousOn hc
  refine h2.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- `L²(Ω)` functions are locally integrable on an open `Ω`. -/
theorem locallyIntegrableOn_of_memLp {Ω : Set (ι → ℝ)} {u : (ι → ℝ) → ℂ}
    (hu : MemLp u 2 (volume.restrict Ω)) : LocallyIntegrableOn u Ω :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable (by norm_num))


/-! ### Complex test functions -/

theorem pd_re {φ : (ι → ℝ) → ℂ} (hφ : ContDiff ℝ 1 φ) (i : ι) (x : ι → ℝ) :
    pd (fun y => (φ y).re) i x = (pd φ i x).re := by
  unfold pd
  have hd : HasFDerivAt φ (fderiv ℝ φ x) x :=
    ((hφ.differentiable one_ne_zero) x).hasFDerivAt
  have := (Complex.reCLM.hasFDerivAt (x := φ x)).comp x hd
  rw [show (fun y => (φ y).re) = Complex.reCLM ∘ φ from rfl, this.fderiv]
  rfl

theorem pd_im {φ : (ι → ℝ) → ℂ} (hφ : ContDiff ℝ 1 φ) (i : ι) (x : ι → ℝ) :
    pd (fun y => (φ y).im) i x = (pd φ i x).im := by
  unfold pd
  have hd : HasFDerivAt φ (fderiv ℝ φ x) x :=
    ((hφ.differentiable one_ne_zero) x).hasFDerivAt
  have := (Complex.imCLM.hasFDerivAt (x := φ x)).comp x hd
  rw [show (fun y => (φ y).im) = Complex.imCLM ∘ φ from rfl, this.fderiv]
  rfl

theorem isTest_re {Ω : Set (ι → ℝ)} {φ : (ι → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) : IsTest Ω (fun y => (φ y).re) :=
  ⟨Complex.reCLM.contDiff.comp hφ, hc.comp_left Complex.zero_re,
    (tsupport_comp_subset Complex.zero_re φ).trans hs⟩

theorem isTest_im {Ω : Set (ι → ℝ)} {φ : (ι → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) : IsTest Ω (fun y => (φ y).im) :=
  ⟨Complex.imCLM.contDiff.comp hφ, hc.comp_left Complex.zero_im,
    (tsupport_comp_subset Complex.zero_im φ).trans hs⟩

/-- The weak-derivative identity holds for **complex-valued** test functions `φ ∈ C_c^∞(Ω, ℂ)`
(split `φ = Re φ + i Im φ`). -/
theorem HasWeakPartial.complex_test {Ω : Set (ι → ℝ)} {i : ι} {u g : (ι → ℝ) → ℂ}
    (h : HasWeakPartial Ω i u g) (hu : LocallyIntegrableOn u Ω) (hg : LocallyIntegrableOn g Ω)
    {φ : (ι → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, pd φ i x * u x = -∫ x, φ x * g x := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hr := h _ (isTest_re hφ hc hs)
  have hi := h _ (isTest_im hφ hc hs)
  simp only [pd_re hφ1, pd_im hφ1] at hr hi
  have htr : ∀ ψ : (ι → ℝ) → ℂ, Continuous ψ → (∀ x, x ∉ tsupport φ → ψ x = 0) →
      ∀ w : (ι → ℝ) → ℂ, LocallyIntegrableOn w Ω → Integrable (fun x => ψ x * w x) := by
    intro ψ hψ h0 w hw
    have hsub : tsupport ψ ⊆ tsupport φ := by
      refine closure_minimal (fun x hx => ?_) (isClosed_tsupport φ)
      by_contra hn; exact hx (h0 x hn)
    exact integrable_mul_of_locallyIntegrableOn hw hψ (hc.mono' ((subset_tsupport ψ).trans hsub)) (hsub.trans hs)
  have hpdc : Continuous (pd φ i) := continuous_pd hφ1 i
  have hpd0 : ∀ x, x ∉ tsupport φ → pd φ i x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_pd_subset φ i h))
  have hφ0 : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have i1 := htr (fun x => (((pd φ i x).re : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hpdc))
    (fun x hx => by simp [hpd0 x hx]) u hu
  have i2 := htr (fun x => (((pd φ i x).im : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hpdc))
    (fun x hx => by simp [hpd0 x hx]) u hu
  have i3 := htr (fun x => (((φ x).re : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hφ.continuous))
    (fun x hx => by simp [hφ0 x hx]) g hg
  have i4 := htr (fun x => (((φ x).im : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hφ.continuous))
    (fun x hx => by simp [hφ0 x hx]) g hg
  have e1 : (fun x => pd φ i x * u x) = fun x =>
      (((pd φ i x).re : ℝ) : ℂ) * u x + Complex.I * ((((pd φ i x).im : ℝ) : ℂ) * u x) := by
    funext x
    conv_lhs => rw [← Complex.re_add_im (pd φ i x)]
    ring
  have e2 : (fun x => φ x * g x) = fun x =>
      (((φ x).re : ℝ) : ℂ) * g x + Complex.I * ((((φ x).im : ℝ) : ℂ) * g x) := by
    funext x
    conv_lhs => rw [← Complex.re_add_im (φ x)]
    ring
  rw [e1, e2, integral_add i1 (i2.const_mul _), integral_add i3 (i4.const_mul _),
    integral_const_mul, integral_const_mul, hr, hi]
  ring

/-! ### Classical derivatives are weak derivatives (non-vacuity) -/

theorem pd_ofReal {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (i : ι) (x : ι → ℝ) :
    pd (fun y => ((φ y : ℝ) : ℂ)) i x = ((pd φ i x : ℝ) : ℂ) := by
  unfold pd
  have hd : HasFDerivAt φ (fderiv ℝ φ x) x := ((hφ.differentiable one_ne_zero) x).hasFDerivAt
  have := (Complex.ofRealCLM.hasFDerivAt (x := φ x)).comp x hd
  rw [show (fun y => ((φ y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, this.fderiv]
  rfl

/-- **Non-vacuity**: a `C¹` function `u` has its classical partial derivative `∂_i u` as weak
partial derivative on every set `Ω`. -/
theorem hasWeakPartial_of_contDiff (Ω : Set (ι → ℝ)) {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ 1 u)
    (i : ι) : HasWeakPartial Ω i u (pd u i) := by
  intro φ hφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  set ψ : (ι → ℝ) → ℂ := fun y => ((φ y : ℝ) : ℂ) with hψ
  have hψ1 : ContDiff ℝ 1 ψ := Complex.ofRealCLM.contDiff.comp hφ1
  have hψc : HasCompactSupport ψ := hφ.compact.comp_left Complex.ofReal_zero
  have hpdψ : ∀ x, fderiv ℝ ψ x (Pi.single i 1) = ((pd φ i x : ℝ) : ℂ) := pd_ofReal hφ1 i
  have hint : ∀ w : (ι → ℝ) → ℂ, Continuous w → Integrable (fun x => ψ x * w x) := by
    intro w hw
    exact (hψ1.continuous.mul hw).integrable_of_hasCompactSupport (hψc.mul_right)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := ψ) (g := u)
    (v := Pi.single i 1) ?_ ?_ (hint u hu.continuous)
    (fun x _ => hψ1.differentiable one_ne_zero x) (fun x _ => hu.differentiable one_ne_zero x)
  · simp only [hpdψ] at h
    rw [← neg_neg (∫ x, ((pd φ i x : ℝ) : ℂ) * u x), ← h]
    rfl
  · simp only [hpdψ]
    have hc : HasCompactSupport fun x => ((pd φ i x : ℝ) : ℂ) :=
      (hasCompactSupport_pd hφ.compact i).comp_left Complex.ofReal_zero
    exact ((Complex.continuous_ofReal.comp (continuous_pd hφ1 i)).mul hu.continuous)
      |>.integrable_of_hasCompactSupport hc.mul_right
  · exact hint _ (continuous_pd hu i)

/-! ### Uniqueness of weak derivatives -/

/-- **Uniqueness of weak derivatives**: two weak `i`-th partials of `u` on an open `Ω` agree
almost everywhere on `Ω`. -/
theorem HasWeakPartial.ae_eq {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) {i : ι} {u g g' : (ι → ℝ) → ℂ}
    (h : HasWeakPartial Ω i u g) (h' : HasWeakPartial Ω i u g')
    (hg : LocallyIntegrableOn g Ω) (hg' : LocallyIntegrableOn g' Ω) :
    ∀ᵐ x, x ∈ Ω → g x = g' x := by
  have hsub : LocallyIntegrableOn (fun x => g x - g' x) Ω := hg.sub hg'
  have := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hsub ?_
  · filter_upwards [this] with x hx hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  intro φ hφs hφc hφΩ
  have ht : IsTest Ω φ := ⟨hφs, hφc, hφΩ⟩
  have e1 := h φ ht
  have e2 := h' φ ht
  have i1 : Integrable fun x => ((φ x : ℝ) : ℂ) * g x :=
    integrable_mul_of_locallyIntegrableOn hg (Complex.continuous_ofReal.comp hφs.continuous)
      (hφc.comp_left Complex.ofReal_zero)
      ((tsupport_comp_subset Complex.ofReal_zero φ).trans hφΩ)
  have i2 : Integrable fun x => ((φ x : ℝ) : ℂ) * g' x :=
    integrable_mul_of_locallyIntegrableOn hg' (Complex.continuous_ofReal.comp hφs.continuous)
      (hφc.comp_left Complex.ofReal_zero)
      ((tsupport_comp_subset Complex.ofReal_zero φ).trans hφΩ)
  have : ∫ x, ((φ x : ℝ) : ℂ) * g x = ∫ x, ((φ x : ℝ) : ℂ) * g' x := by
    have := e1.symm.trans e2
    exact neg_inj.mp this
  simp only [Complex.real_smul]
  simp_rw [mul_sub]
  rw [integral_sub i1 i2, this, sub_self]

/-! ### The cutoff product rule -/

theorem pd_mul {χ φ : (ι → ℝ) → ℝ} (hχ : ContDiff ℝ 1 χ) (hφ : ContDiff ℝ 1 φ) (i : ι)
    (x : ι → ℝ) : pd (fun y => χ y * φ y) i x = pd χ i x * φ x + χ x * pd φ i x := by
  unfold pd
  rw [show (fun y => χ y * φ y) = χ * φ from rfl, (((hχ.differentiable one_ne_zero) x).hasFDerivAt.mul
    ((hφ.differentiable one_ne_zero) x).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem IsTest.mul_smooth {Ω : Set (ι → ℝ)} {χ φ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ)
    (hφ : ContDiff ℝ ∞ φ) : IsTest Ω (fun y => χ y * φ y) :=
  ⟨hχ.smooth.mul hφ, hχ.compact.mul_right, (tsupport_mul_subset_left).trans hχ.subset⟩

/-- Integrability of `ψ · w` for a continuous `ψ` supported in the support of a test function on
`Ω` and `w` locally integrable on `Ω`. -/
theorem IsTest.integrable_mul {Ω : Set (ι → ℝ)} {χ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ)
    {ψ : (ι → ℝ) → ℝ} (hψ : Continuous ψ) (hψs : tsupport ψ ⊆ tsupport χ) {w : (ι → ℝ) → ℂ}
    (hw : LocallyIntegrableOn w Ω) : Integrable fun x => ((ψ x : ℝ) : ℂ) * w x := by
  have hs : tsupport (fun x => ((ψ x : ℝ) : ℂ)) ⊆ tsupport χ :=
    (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψs
  exact integrable_mul_of_locallyIntegrableOn hw (Complex.continuous_ofReal.comp hψ)
    (hχ.compact.mono' ((subset_tsupport _).trans hs)) (hs.trans hχ.subset)

/-- **Cutoff product rule.**  If `g` is the weak `i`-th partial of `u` on `Ω` and
`χ ∈ C_c^∞(Ω)`, then `χ u` (which vanishes off `tsupport χ`) has the weak `i`-th partial
`χ g + ∂_iχ · u` on the **whole space** `ℝ^ι`. -/
theorem HasWeakPartial.mul_test {Ω : Set (ι → ℝ)} {i : ι} {u g : (ι → ℝ) → ℂ}
    (h : HasWeakPartial Ω i u g) (hu : LocallyIntegrableOn u Ω) (hg : LocallyIntegrableOn g Ω)
    {χ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ) :
    HasWeakPartial univ i (fun x => ((χ x : ℝ) : ℂ) * u x)
      (fun x => ((χ x : ℝ) : ℂ) * g x + ((pd χ i x : ℝ) : ℂ) * u x) := by
  intro φ hφ
  have hχ1 : ContDiff ℝ 1 χ := hχ.smooth.of_le (by simp)
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have key := h _ (hχ.mul_smooth hφ.smooth)
  simp only [pd_mul hχ1 hφ1] at key
  have sχ : ∀ ψ : (ι → ℝ) → ℝ, Continuous ψ → (∀ x, χ x = 0 → ψ x = 0) →
      tsupport ψ ⊆ tsupport χ := by
    intro ψ _ h0
    refine closure_mono fun x hx => ?_
    intro hχx; exact hx (h0 x hχx)
  have hpdχ0 : ∀ x, x ∉ tsupport χ → pd χ i x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h' => hx (tsupport_pd_subset χ i h'))
  have tA : tsupport (fun x => pd χ i x * φ x) ⊆ tsupport χ :=
    (tsupport_mul_subset_left).trans (tsupport_pd_subset χ i)
  have iA := hχ.integrable_mul (ψ := fun x => pd χ i x * φ x)
    ((continuous_pd hχ1 i).mul hφ1.continuous) tA hu
  have iB := hχ.integrable_mul (ψ := fun x => χ x * pd φ i x)
    (hχ1.continuous.mul (continuous_pd hφ1 i)) tsupport_mul_subset_left hu
  have iC := hχ.integrable_mul (ψ := fun x => χ x * φ x)
    (hχ1.continuous.mul hφ1.continuous) tsupport_mul_subset_left hg
  have iD := hχ.integrable_mul (ψ := fun x => φ x * pd χ i x)
    (hφ1.continuous.mul (continuous_pd hχ1 i))
    ((tsupport_mul_subset_right).trans (tsupport_pd_subset χ i)) hu
  have e1 : (fun x => ((pd φ i x : ℝ) : ℂ) * (((χ x : ℝ) : ℂ) * u x)) =
      fun x => ((pd χ i x * φ x + χ x * pd φ i x : ℝ) : ℂ) * u x -
        ((pd χ i x * φ x : ℝ) : ℂ) * u x := by
    funext x; push_cast; ring
  have e2 : (fun x => ((φ x : ℝ) : ℂ) * (((χ x : ℝ) : ℂ) * g x + ((pd χ i x : ℝ) : ℂ) * u x)) =
      fun x => ((χ x * φ x : ℝ) : ℂ) * g x + ((φ x * pd χ i x : ℝ) : ℂ) * u x := by
    funext x; push_cast; ring
  have e3 : (fun x => ((pd χ i x * φ x + χ x * pd φ i x : ℝ) : ℂ) * u x) =
      fun x => ((pd χ i x * φ x : ℝ) : ℂ) * u x + ((χ x * pd φ i x : ℝ) : ℂ) * u x := by
    funext x; push_cast; ring
  have e4 : (fun x => ((φ x * pd χ i x : ℝ) : ℂ) * u x) =
      fun x => ((pd χ i x * φ x : ℝ) : ℂ) * u x := by
    funext x; push_cast; ring
  have iS : Integrable fun x => ((pd χ i x * φ x + χ x * pd φ i x : ℝ) : ℂ) * u x := by
    rw [e3]; exact iA.add iB
  show ∫ x, ((pd φ i x : ℝ) : ℂ) * (((χ x : ℝ) : ℂ) * u x) =
    -∫ x, ((φ x : ℝ) : ℂ) * (((χ x : ℝ) : ℂ) * g x + ((pd χ i x : ℝ) : ℂ) * u x)
  rw [e1, integral_sub iS iA, key, e2, integral_add iC iD, e4]
  ring

/-- A bounded continuous real multiplier `ψ` vanishing off a measurable `Ω` maps `L²(Ω)` into
`L²(ℝ^ι)`, with `‖ψ w‖_{L²(ℝ^ι)} ≤ K ‖w‖_{L²(Ω)}`. -/
theorem memLp_mul_of_vanish {Ω : Set (ι → ℝ)} (hΩ : MeasurableSet Ω) {ψ : (ι → ℝ) → ℝ}
    (hψ : Continuous ψ) (h0 : ∀ x, x ∉ Ω → ψ x = 0) {K : ℝ≥0} (hK : ∀ x, ‖ψ x‖ ≤ K)
    {w : (ι → ℝ) → ℂ} (hw : MemLp w 2 (volume.restrict Ω)) :
    MemLp (fun x => ((ψ x : ℝ) : ℂ) * w x) 2 volume ∧
      eLpNorm (fun x => ((ψ x : ℝ) : ℂ) * w x) 2 volume ≤ K * eLpNorm w 2 (volume.restrict Ω) := by
  have hind : (fun x => ((ψ x : ℝ) : ℂ) * w x) = Ω.indicator (fun x => ((ψ x : ℝ) : ℂ) * w x) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · simp [hx, h0 x hx]
  have hbd : ∀ x, ‖((ψ x : ℝ) : ℂ) * w x‖ ≤ (K : ℝ) * ‖w x‖ := by
    intro x
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _)
  have hmeas : AEStronglyMeasurable (fun x => ((ψ x : ℝ) : ℂ) * w x) (volume.restrict Ω) :=
    (Complex.continuous_ofReal.comp hψ).aestronglyMeasurable.mul hw.1
  have hmem : MemLp (fun x => ((ψ x : ℝ) : ℂ) * w x) 2 (volume.restrict Ω) :=
    hw.of_le_mul hmeas (Eventually.of_forall hbd)
  refine ⟨?_, ?_⟩
  · rw [hind, memLp_indicator_iff_restrict hΩ]; exact hmem
  · rw [hind, eLpNorm_indicator_eq_eLpNorm_restrict hΩ]
    refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2).trans
      (le_of_eq rfl)
    have := hbd x
    rw [← NNReal.coe_le_coe]
    simpa using this

/-- **`W^{1,2}` cutoff.**  For `u ∈ W^{1,2}(Ω)` (`Ω` open) and `χ ∈ C_c^∞(Ω)` with
`|χ| ≤ M`, `|∂_iχ| ≤ M'`, the product `χ u` lies in `W^{1,2}(ℝ^ι)` with weak gradient
`χ ∂_i u + ∂_iχ u`, and `‖χ u‖_{W^{1,2}(ℝ^ι)} ≤ (M + d M') ‖u‖_{W^{1,2}(Ω)}`. -/
theorem MemW12.mul_test {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) {u : (ι → ℝ) → ℂ}
    {g : ι → (ι → ℝ) → ℂ} (hu : MemW12 Ω u g) {χ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ)
    {M M' : ℝ≥0} (hM : ∀ x, ‖χ x‖ ≤ M) (hM' : ∀ i x, ‖pd χ i x‖ ≤ M') :
    MemW12 univ (fun x => ((χ x : ℝ) : ℂ) * u x)
        (fun i x => ((χ x : ℝ) : ℂ) * g i x + ((pd χ i x : ℝ) : ℂ) * u x) ∧
      w12Norm univ (fun x => ((χ x : ℝ) : ℂ) * u x)
        (fun i x => ((χ x : ℝ) : ℂ) * g i x + ((pd χ i x : ℝ) : ℂ) * u x) ≤
        ((M : ℝ≥0∞) + Fintype.card ι * M') * w12Norm Ω u g := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.smooth.of_le (by simp)
  have h0 : ∀ x, x ∉ Ω → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hχ.subset h))
  have h0' : ∀ i x, x ∉ Ω → pd χ i x = 0 := fun i x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hχ.subset (tsupport_pd_subset χ i h)))
  obtain ⟨m1, n1⟩ := memLp_mul_of_vanish hΩ.measurableSet hχ1.continuous h0 hM hu.memLp
  have m2 := fun i => memLp_mul_of_vanish hΩ.measurableSet hχ1.continuous h0 hM (hu.memLp_grad i)
  have m3 := fun i => memLp_mul_of_vanish hΩ.measurableSet (continuous_pd hχ1 i) (h0' i)
    (hM' i) hu.memLp
  have hloc := locallyIntegrableOn_of_memLp hu.memLp
  have hlocg := fun i => locallyIntegrableOn_of_memLp (hu.memLp_grad i)
  refine ⟨⟨by rw [Measure.restrict_univ]; exact m1, fun i => ?_, fun i => ?_⟩, ?_⟩
  · rw [Measure.restrict_univ]; exact (m2 i).1.add (m3 i).1
  · exact (hu.weak i).mul_test hloc (hlocg i) hχ
  · unfold w12Norm
    rw [Measure.restrict_univ]
    have hgi : ∀ i, eLpNorm (fun x => ((χ x : ℝ) : ℂ) * g i x + ((pd χ i x : ℝ) : ℂ) * u x) 2
        volume ≤ M * eLpNorm (g i) 2 (volume.restrict Ω) +
          M' * eLpNorm u 2 (volume.restrict Ω) := by
      intro i
      refine (eLpNorm_add_le (m2 i).1.1 (m3 i).1.1 (by norm_num)).trans ?_
      exact add_le_add (m2 i).2 (m3 i).2
    calc eLpNorm (fun x => ((χ x : ℝ) : ℂ) * u x) 2 volume +
          ∑ i, eLpNorm (fun x => ((χ x : ℝ) : ℂ) * g i x + ((pd χ i x : ℝ) : ℂ) * u x) 2 volume
        ≤ M * eLpNorm u 2 (volume.restrict Ω) + ∑ i, ((M : ℝ≥0∞) *
            eLpNorm (g i) 2 (volume.restrict Ω) + M' * eLpNorm u 2 (volume.restrict Ω)) :=
          add_le_add n1 (Finset.sum_le_sum fun i _ => hgi i)
      _ = (M + Fintype.card ι * M') * eLpNorm u 2 (volume.restrict Ω) +
            M * ∑ i, eLpNorm (g i) 2 (volume.restrict Ω) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum]
          ring
      _ ≤ (M + Fintype.card ι * M') * eLpNorm u 2 (volume.restrict Ω) +
            (M + Fintype.card ι * M') * ∑ i, eLpNorm (g i) 2 (volume.restrict Ω) := by
          gcongr
          exact le_self_add
      _ = ((M : ℝ≥0∞) + Fintype.card ι * M') * (eLpNorm u 2 (volume.restrict Ω) +
            ∑ i, eLpNorm (g i) 2 (volume.restrict Ω)) := by ring

end RenewalGeometry.SobolevOpen
