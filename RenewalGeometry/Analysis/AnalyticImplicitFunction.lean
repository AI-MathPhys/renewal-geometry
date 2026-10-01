/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The analytic implicit function theorem

Mathlib provides the strict-derivative implicit function theorem
(`ImplicitFunctionData.implicitFunction`, `HasStrictFDerivAt.implicitFunctionOfProdDomain`),
its `C^n` refinement (`ContDiffAt.contDiffAt_implicitFunction`), and the analyticity of the
inverse of an analytic open partial homeomorphism with invertible derivative
(`OpenPartialHomeomorph.analyticAt_symm'`).  This file combines them into the **analytic**
implicit function theorem.

* `ImplicitFunctionData.analyticAt_implicitFunction_uncurry`: in the general (two-function)
  form, if `leftFun` and `rightFun` are analytic at the base point, the implicit function
  `(y, z) ↦ φ.implicitFunction y z` is analytic at the image of the base point.
* `HasStrictFDerivAt.analyticAt_implicitFunctionOfProdDomain`: for `f : E₁ × E₂ → F`
  analytic at `u` with invertible partial derivative in the second variable, the implicit
  function `ψ` with `f (x, ψ x) = f u` is analytic at `u.1`.
* `analytic_implicit_function`: a self-contained existence-and-uniqueness statement: there is
  a germ `ψ`, analytic at `u.1`, with `ψ u.1 = u.2`, `f (x, ψ x) = f u` near `u.1`, such that
  near `u` the level set `{f = f u}` is exactly the graph of `ψ`, and with strict derivative
  `-(∂₂f)⁻¹ ∘ ∂₁f` at `u.1`.

These are the analytic implicit-function inputs of `lem:supp-exact-two-row-elimination` and
`lem:supp-exact-normal-coordinates` (emergent-spacetime manuscript).
-/

open Filter
open scoped Topology

namespace RenewalGeometry

namespace AnalyticImplicit

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- **Analytic implicit function theorem, general form.**  If the two functions of an
`ImplicitFunctionData` are analytic at the base point, then the (uncurried) implicit function
is analytic at the image of the base point. -/
theorem implicitFunctionData_analyticAt_uncurry (φ : ImplicitFunctionData 𝕜 E F G)
    (hl : AnalyticAt 𝕜 φ.leftFun φ.pt) (hr : AnalyticAt 𝕜 φ.rightFun φ.pt) :
    AnalyticAt 𝕜 φ.implicitFunction.uncurry (φ.prodFun φ.pt) := by
  rw [ImplicitFunctionData.implicitFunction_def, Function.uncurry_curry]
  set R := φ.hasStrictFDerivAt.toOpenPartialHomeomorph φ.prodFun
  have h0 : φ.pt ∈ R.source := φ.hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
  have hcoe : (R : E → F × G) = φ.prodFun := rfl
  have han : AnalyticAt 𝕜 R φ.pt := by
    rw [hcoe]
    exact hl.prod hr
  have hd : fderiv 𝕜 R φ.pt = ((φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
      φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker : E ≃L[𝕜] F × G) : E →L[𝕜] F × G) := by
    rw [hcoe]
    exact φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have := R.analyticAt_symm' h0 han hd
  simpa [hcoe] using this

end General

section ProdDomain

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Analytic implicit function theorem, product-domain form.**  If `f : E₁ × E₂ → F` is
analytic at `u` (with strict derivative `f'u` there) and the partial derivative in the second
variable is invertible, the implicit function `ψ` (with `f (x, ψ x) = f u`) is analytic at
`u.1`. -/
theorem analyticAt_implicitFunctionOfProdDomain {f : E₁ × E₂ → F} {u : E₁ × E₂}
    {f'u : E₁ × E₂ →L[𝕜] F} (dfu : HasStrictFDerivAt f f'u u)
    (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) (hf : AnalyticAt 𝕜 f u) :
    AnalyticAt 𝕜 (dfu.implicitFunctionOfProdDomain if₂u) u.1 := by
  set φ := dfu.implicitFunctionDataOfProdDomain if₂u
  have hφ : AnalyticAt 𝕜 φ.implicitFunction.uncurry (φ.prodFun φ.pt) :=
    implicitFunctionData_analyticAt_uncurry φ hf analyticAt_fst
  have hpt : φ.prodFun φ.pt = (f u, u.1) := rfl
  rw [hpt] at hφ
  have hin : AnalyticAt 𝕜 (fun x : E₁ => (f u, x)) u.1 :=
    analyticAt_const.prod analyticAt_id
  have hcomp := hφ.comp_of_eq hin rfl
  have : dfu.implicitFunctionOfProdDomain if₂u =
      Prod.snd ∘ (φ.implicitFunction.uncurry ∘ fun x : E₁ => (f u, x)) := by
    funext x
    rfl
  rw [this]
  exact analyticAt_snd.comp hcomp

/-- **Analytic implicit function theorem** (existence, uniqueness, analyticity, derivative).
Let `f : E₁ × E₂ → F` be analytic at `u` with invertible partial derivative
`∂₂f(u) = fderiv f u ∘ inr`.  Then there is `ψ : E₁ → E₂`, analytic at `u.1`, with
`ψ u.1 = u.2`, `f (x, ψ x) = f u` for `x` near `u.1`, such that near `u` the level set
`{v | f v = f u}` is exactly the graph of `ψ`, and `ψ` has strict derivative
`-(∂₂f(u))⁻¹ ∘ ∂₁f(u)` at `u.1`. -/
theorem analytic_implicit_function {f : E₁ × E₂ → F} {u : E₁ × E₂} (hf : AnalyticAt 𝕜 f u)
    (hinv : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∃ ψ : E₁ → E₂, ψ u.1 = u.2 ∧ AnalyticAt 𝕜 ψ u.1 ∧
      (∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u) ∧
      (∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2) ∧
      HasStrictFDerivAt ψ (-(fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).inverse ∘L
        (fderiv 𝕜 f u ∘L .inl 𝕜 E₁ E₂)) u.1 := by
  have dfu : HasStrictFDerivAt f (fderiv 𝕜 f u) u := hf.hasStrictFDerivAt
  refine ⟨dfu.implicitFunctionOfProdDomain hinv, ?_, ?_, ?_, ?_, ?_⟩
  · exact eq_of_tendsto_nhds (dfu.tendsto_implicitFunctionOfProdDomain hinv)
  · exact analyticAt_implicitFunctionOfProdDomain dfu hinv hf
  · exact dfu.eventually_apply_implicitFunctionOfProdDomain hinv
  · exact dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  · exact dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv

end ProdDomain


section Divisible

/-! ### Divisible partial derivatives of an implicit function

If the implicit equation `f (y, n) = 0` has an analytically *divisible* partial derivative in a
direction `ι` of the parameter space, `∂_ι f = c • F` with `F` analytic, then every analytic
solution germ `n = ψ(y)` has the same divisibility, `∂_ι ψ = c • G` with `G` analytic
(`implicit_fderiv_comp_eq_smul`).  This is the bookkeeping of derivative orders
(`D_q n = O(a)`, `D_p n = O(a²)`) in `lem:supp-exact-normal-coordinates`. -/

variable {Y N R V : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Divisibility transfers to the implicit function.**  Let `f : Y × N → R` be analytic at
`0` with invertible partial derivative `∂_n f(0) = C`, and let `ψ` be an analytic solution germ
(`ψ 0 = 0`, `f (y, ψ y) = 0` near `0`).  If, in a parameter direction `ι : V →L Y`, the partial
derivative of `f` factors as `∂_ι f(x) = c(x.1) • F(x)` near `0` with `F` analytic, then
`∂_ι ψ(y) = c(y) • G(y)` near `0` with `G` analytic at `0`; explicitly
`G(y) = -(∂_n f(y, ψ y))⁻¹ F(y, ψ y)`. -/
theorem implicit_fderiv_comp_eq_smul (f : Y × N → R) (hf : AnalyticAt ℝ f 0) (ψ : Y → N)
    (hψ : AnalyticAt ℝ ψ 0) (hψ0 : ψ 0 = 0) (hsol : ∀ᶠ y in 𝓝 (0 : Y), f (y, ψ y) = 0)
    (C : N ≃L[ℝ] R) (hC : fderiv ℝ f 0 ∘L ContinuousLinearMap.inr ℝ Y N = (C : N →L[ℝ] R))
    (ι : V →L[ℝ] Y) (c : Y → ℝ) (F : Y × N → (V →L[ℝ] R)) (hF : AnalyticAt ℝ F 0)
    (hdiv : ∀ᶠ x in 𝓝 (0 : Y × N),
      fderiv ℝ f x ∘L (ContinuousLinearMap.inl ℝ Y N ∘L ι) = c x.1 • F x) :
    ∃ G : Y → (V →L[ℝ] N), AnalyticAt ℝ G 0 ∧
      ∀ᶠ y in 𝓝 (0 : Y), fderiv ℝ ψ y ∘L ι = c y • G y := by
  set X : Y → Y × N := fun y => (y, ψ y) with hXdef
  have hX : AnalyticAt ℝ X 0 := analyticAt_id.prod hψ
  have hX0 : X 0 = 0 := by simp [hXdef, hψ0]
  -- the normalized normal derivative `M(x) = C⁻¹ ∘ ∂_n f(x)`
  let Φ : ((Y × N) →L[ℝ] R) →L[ℝ] (N →L[ℝ] N) :=
    (ContinuousLinearMap.compL ℝ N R N (C.symm : R →L[ℝ] N)).comp
      ((ContinuousLinearMap.compL ℝ N (Y × N) R).flip (ContinuousLinearMap.inr ℝ Y N))
  have hΦ : ∀ L, Φ L = (C.symm : R →L[ℝ] N) ∘L (L ∘L ContinuousLinearMap.inr ℝ Y N) :=
    fun L => rfl
  set M : Y × N → (N →L[ℝ] N) := fun x => Φ (fderiv ℝ f x) with hMdef
  have hM : AnalyticAt ℝ M 0 := (Φ.analyticAt _).comp hf.fderiv
  have hM0 : M 0 = 1 := by
    simp only [hMdef, hΦ, hC]
    ext v
    simp
  have hMX : AnalyticAt ℝ (M ∘ X) 0 := hM.comp_of_eq hX hX0
  have hMX0 : (M ∘ X) 0 = ((1 : (N →L[ℝ] N)ˣ) : N →L[ℝ] N) := by
    simp [hX0, hM0]
  -- invertibility near `0`
  have hunit : ∀ᶠ y in 𝓝 (0 : Y), IsUnit (M (X y)) := by
    have hopen : {L : N →L[ℝ] N | IsUnit L} ∈ 𝓝 ((M ∘ X) 0) := by
      rw [hMX0]
      exact Units.isOpen.mem_nhds (Units.isUnit 1)
    exact hMX.continuousAt.preimage_mem_nhds hopen
  -- the factor `G`
  let B := ContinuousLinearMap.compL ℝ V N N
  let Ψ : (V →L[ℝ] R) →L[ℝ] (V →L[ℝ] N) :=
    ContinuousLinearMap.compL ℝ V R N (C.symm : R →L[ℝ] N)
  set G : Y → (V →L[ℝ] N) := fun y => -(B (Ring.inverse (M (X y))) (Ψ (F (X y)))) with hGdef
  have hInv : AnalyticAt ℝ (fun y => Ring.inverse (M (X y))) 0 :=
    (analyticAt_inverse (𝕜 := ℝ) (1 : (N →L[ℝ] N)ˣ)).comp_of_eq hMX hMX0
  have hΨF : AnalyticAt ℝ (fun y => Ψ (F (X y))) 0 :=
    (Ψ.analyticAt _).comp (hF.comp_of_eq hX hX0)
  have hG : AnalyticAt ℝ G 0 := by
    have hpair := hInv.prod hΨF
    have := (B.analyticAt_bilinear _).comp hpair
    exact this.neg
  refine ⟨G, hG, ?_⟩
  -- the differentiated implicit equation
  have hsol' : ∀ᶠ y in 𝓝 (0 : Y), ∀ᶠ z in 𝓝 y, f (z, ψ z) = 0 := hsol.eventually_nhds
  have hfan : ∀ᶠ y in 𝓝 (0 : Y), AnalyticAt ℝ f (X y) := by
    have := hf.eventually_analyticAt
    rw [← hX0] at this
    exact hX.continuousAt.eventually this
  have hψan : ∀ᶠ y in 𝓝 (0 : Y), AnalyticAt ℝ ψ y := hψ.eventually_analyticAt
  have hdivX : ∀ᶠ y in 𝓝 (0 : Y),
      fderiv ℝ f (X y) ∘L (ContinuousLinearMap.inl ℝ Y N ∘L ι) = c y • F (X y) := by
    rw [← hX0] at hdiv
    exact hX.continuousAt.eventually hdiv
  filter_upwards [hsol', hfan, hψan, hdivX, hunit] with y hy hfy hψy hdy huy
  set T := fderiv ℝ ψ y ∘L ι
  set Df := fderiv ℝ f (X y)
  have hchain : HasFDerivAt (fun z => f (z, ψ z))
      (Df ∘L ((ContinuousLinearMap.id ℝ Y).prod (fderiv ℝ ψ y))) y := by
    have h1 : HasFDerivAt (fun z => (z, ψ z))
        ((ContinuousLinearMap.id ℝ Y).prod (fderiv ℝ ψ y)) y :=
      (hasFDerivAt_id y).prodMk hψy.differentiableAt.hasFDerivAt
    exact hfy.differentiableAt.hasFDerivAt.comp y h1
  have hzero : Df ∘L ((ContinuousLinearMap.id ℝ Y).prod (fderiv ℝ ψ y)) = 0 := by
    have h0 : HasFDerivAt (fun z => f (z, ψ z)) (0 : Y →L[ℝ] R) y :=
      (hasFDerivAt_const (0 : R) y).congr_of_eventuallyEq (hy.mono fun z hz => hz)
    exact hchain.unique h0
  have hsplit : Df ∘L (ContinuousLinearMap.inl ℝ Y N ∘L ι) +
      (Df ∘L ContinuousLinearMap.inr ℝ Y N) ∘L T = 0 := by
    ext v
    have := congrArg (fun L => L (ι v)) hzero
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at this
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.zero_apply, T]
    rw [← map_add]
    simpa using this
  have hMT : M (X y) ∘L T = -(c y • Ψ (F (X y))) := by
    have : (Df ∘L ContinuousLinearMap.inr ℝ Y N) ∘L T = -(c y • F (X y)) := by
      rw [← hdy]; exact eq_neg_of_add_eq_zero_right hsplit
    simp only [hMdef, hΦ]
    rw [ContinuousLinearMap.comp_assoc, this]
    ext v
    simp [Ψ]
  have hinvM : Ring.inverse (M (X y)) * M (X y) = 1 := Ring.inverse_mul_cancel _ huy
  calc T = (Ring.inverse (M (X y)) * M (X y)) ∘L T := by rw [hinvM]; rfl
    _ = Ring.inverse (M (X y)) ∘L (M (X y) ∘L T) := rfl
    _ = c y • G y := by
      rw [hMT]
      ext v
      simp [hGdef, B]

/-- If `F y = c(y)^k • G y` near `0` with `G` analytic and `ι` a direction along which the
amplitude functional `c` vanishes (`c ∘ ι = 0`), then the `ι`-partial derivative of `F` is
bounded by `K |c y|^k` near `0`. -/
theorem norm_fderiv_comp_pow_smul_le {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']
    [CompleteSpace W'] (c : Y →L[ℝ] ℝ) (ι : V →L[ℝ] Y) (hι : c ∘L ι = 0) (k : ℕ)
    (G : Y → W') (hG : AnalyticAt ℝ G 0) (F : Y → W')
    (hF : ∀ᶠ y in 𝓝 (0 : Y), F y = c y ^ k • G y) :
    ∃ K, ∀ᶠ y in 𝓝 (0 : Y), ‖fderiv ℝ F y ∘L ι‖ ≤ K * |c y| ^ k := by
  have hcont : ContinuousAt (fun y => fderiv ℝ G y) 0 := hG.fderiv.continuousAt
  have hbd : ∀ᶠ y in 𝓝 (0 : Y), ‖fderiv ℝ G y‖ ≤ ‖fderiv ℝ G 0‖ + 1 := by
    have := hcont.eventually (Metric.ball_mem_nhds (fderiv ℝ G 0) one_pos)
    filter_upwards [this] with y hy
    have := norm_sub_norm_le (fderiv ℝ G y) (fderiv ℝ G 0)
    rw [dist_eq_norm] at hy
    linarith
  refine ⟨(‖fderiv ℝ G 0‖ + 1) * ‖ι‖, ?_⟩
  have hGan : ∀ᶠ y in 𝓝 (0 : Y), AnalyticAt ℝ G y := hG.eventually_analyticAt
  have hF' : ∀ᶠ y in 𝓝 (0 : Y), F =ᶠ[𝓝 y] fun z => c z ^ k • G z := by
    filter_upwards [hF.eventually_nhds] with y hy
    exact hy
  filter_upwards [hF', hGan, hbd] with y hy hGy hby
  rw [hy.fderiv_eq]
  have hd : HasFDerivAt (fun z => c z ^ k • G z)
      (c y ^ k • fderiv ℝ G y + ((k • c y ^ (k - 1)) • c).smulRight (G y)) y :=
    ((c.hasFDerivAt (x := y)).pow k).smul hGy.differentiableAt.hasFDerivAt
  rw [hd.fderiv]
  have hcv : ∀ v, c (ι v) = 0 := fun v => by
    have := congrArg (fun L => L v) hι
    simpa using this
  have hcomp : ∀ (a b : ℝ) (L : Y →L[ℝ] W'),
      (a • L + (b • c).smulRight (G y)) ∘L ι = a • (L ∘L ι) := by
    intro a b L
    ext v
    simp [hcv]
  rw [hcomp, norm_smul, Real.norm_eq_abs, abs_pow]
  calc |c y| ^ k * ‖fderiv ℝ G y ∘L ι‖ ≤ |c y| ^ k * (‖fderiv ℝ G y‖ * ‖ι‖) := by
        gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ |c y| ^ k * ((‖fderiv ℝ G 0‖ + 1) * ‖ι‖) := by gcongr
    _ = (‖fderiv ℝ G 0‖ + 1) * ‖ι‖ * |c y| ^ k := by ring

end Divisible

end AnalyticImplicit

end RenewalGeometry
