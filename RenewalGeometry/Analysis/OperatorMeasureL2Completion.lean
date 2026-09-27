/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.OperatorTailMeasureIntegralCalculus
/-!
# The Hilbert space `L²(μ; H)` of a positive operator-valued measure

Infrastructure for `con:supp-Naimark-tail` and `thm:supp-Naimark-realization` of
`papers/predictive_spectral_geometry`.  For a positive semidefinite-valued vector measure
`μ : 𝔅(X) → B(H)` (`PosOperatorMeasure X H`, `H` finite) with finite variation we build

* the pre-Hilbert space `PreL2 μ` of bounded measurable `H`-valued functions with the
  semi-inner product `⟨f, g⟩_μ = ∫ ⟨f(x), dμ(x) g(x)⟩` (`PreL2.form`), which for simple functions
  `∑ 1_{E_j} ξ_j`, `∑ 1_{F_k} η_k` is `∑_{j,k} ⟨ξ_j, μ(E_j ∩ F_k) η_k⟩` (`con:supp-Naimark-tail`);
  positivity is proved for simple functions by `SimpleFunc.induction` and for bounded measurable
  functions by dominated convergence;
* the Hilbert space `L2 μ := Completion (SeparationQuotient (PreL2 μ))` — the quotient by the
  null space, completed — with the dense embedding `L2.mk μ : PreL2 μ →L[ℂ] L2 μ`;
* the bounded multiplication operators `L2.mul μ g` by bounded measurable scalar functions `g`,
  obtained by extension from `PreL2 μ` (`‖g f‖_μ ≤ sup|g| ‖f‖_μ` from positivity applied to
  `√(sup|g|² - |g|²) f`), with `mul (g₁ g₂) = mul g₁ ∘ mul g₂`, `mul 1 = 1` and
  `(mul g)† = mul (conj g)`;
* the projection-valued measure `L2.proj μ E = mul (1_E)`: orthogonal projections,
  multiplicative, `proj univ = 1`, finitely additive, and strongly σ-additive
  (`L2.hasSum_proj`);
* the embedding `L2.embed μ ξ = [1 ξ]` of `EuclideanSpace ℂ H` (`V_μ`), whose adjoint is `B_μ`,
  with `⟨V ξ, proj E (V η)⟩ = ⟨ξ, μ(E) η⟩` (`L2.inner_embed_proj_embed`) and the density of
  `span {proj E (V ξ)}` (`L2.topologicalClosure_span_proj_embed`, `eq:supp-Naimark-minimal`).
-/

open MeasureTheory Filter Topology Set
open scoped ComplexOrder ENNReal Matrix InnerProductSpace

namespace RenewalGeometry
namespace OperatorMeasureL2

variable {X : Type*} [MeasurableSpace X] {H : Type*} [Fintype H] [DecidableEq H]

/-- A positive operator-valued measure on `X`: a countably additive `B(H)`-valued set function
with positive semidefinite values. -/
structure PosOperatorMeasure (X : Type*) [MeasurableSpace X] (H : Type*) [Fintype H]
    [DecidableEq H] where
  /-- The underlying vector measure with values in `H → H → ℂ`. -/
  toVectorMeasure : VectorMeasure X (H → H → ℂ)
  /-- Positivity of the values. -/
  posSemidef : ∀ s : Set X, MeasurableSet s → (Matrix.of (toVectorMeasure s)).PosSemidef

namespace PosOperatorMeasure

variable (μ : PosOperatorMeasure X H)

theorem posSemidef_apply (s : Set X) : (Matrix.of (μ.toVectorMeasure s)).PosSemidef := by
  by_cases hs : MeasurableSet s
  · exact μ.posSemidef s hs
  · rw [VectorMeasure.not_measurable _ hs]
    exact Matrix.PosSemidef.zero

theorem isHermitian_apply (s : Set X) (i j : H) :
    star (μ.toVectorMeasure s j i) = μ.toVectorMeasure s i j := by
  have h := (μ.posSemidef_apply s).1.apply i j
  simpa [Matrix.of_apply] using h

end PosOperatorMeasure

/-- A positive tail measure on `ℝ` is a positive operator-valued measure. -/
def _root_.RenewalGeometry.OperatorTailMeasure.PositiveTailMeasure.toPosOperatorMeasure
    (μ : OperatorTailMeasure.PositiveTailMeasure H) : PosOperatorMeasure ℝ H :=
  ⟨μ.toVectorMeasure, μ.posSemidef⟩

/-! ## The trace pairing -/

/-- The coordinate functional `M ↦ M i j` on `H → H → ℂ`. -/
noncomputable def entryCLM (i j : H) : (H → H → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : H => H → ℂ) i)

@[simp]
theorem entryCLM_apply (i j : H) (M : H → H → ℂ) : entryCLM i j M = M i j := rfl

/-- The real bilinear pairing `(A, M) ↦ ∑_{i,j} A i j * M i j` on `H → H → ℂ`. -/
noncomputable def pairCLM : (H → H → ℂ) →L[ℝ] (H → H → ℂ) →L[ℝ] ℂ :=
  ∑ i : H, ∑ j : H, (ContinuousLinearMap.mul ℝ ℂ).bilinearComp (entryCLM i j) (entryCLM i j)

theorem pairCLM_apply (A M : H → H → ℂ) : pairCLM A M = ∑ i, ∑ j, A i j * M i j := by
  simp [pairCLM, ContinuousLinearMap.sum_apply]

/-- The sesquilinear integrand `x ↦ (i, j) ↦ conj (f x i) * g x j`. -/
def innerIntegrand (f g : X → H → ℂ) : X → H → H → ℂ := fun x i j => star (f x i) * g x j

theorem innerIntegrand_apply (f g : X → H → ℂ) (x : X) (i j : H) :
    innerIntegrand f g x i j = star (f x i) * g x j := rfl

theorem measurable_innerIntegrand {f g : X → H → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (innerIntegrand f g) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact Measurable.mul (continuous_star.measurable.comp ((measurable_pi_apply i).comp hf))
    ((measurable_pi_apply j).comp hg)

theorem norm_innerIntegrand_le (f g : X → H → ℂ) (x : X) :
    ‖innerIntegrand f g x‖ ≤ ‖f x‖ * ‖g x‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  rw [innerIntegrand_apply, norm_mul, norm_star]
  exact mul_le_mul (norm_le_pi_norm (f x) i) (norm_le_pi_norm (g x) j) (norm_nonneg _)
    (norm_nonneg _)

/-- The bounded measurable `H`-valued functions on `X`, as a `ℂ`-submodule of `X → H → ℂ`. -/
def bddMeasurable (X : Type*) [MeasurableSpace X] (H : Type*) [Fintype H] :
    Submodule ℂ (X → H → ℂ) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C}
  add_mem' := by
    rintro f g ⟨hf, C, hC⟩ ⟨hg, D, hD⟩
    refine ⟨hf.add hg, C + D, fun x => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))
  zero_mem' := ⟨measurable_const, 0, fun x => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, C, hC⟩
    refine ⟨hf.const_smul c, ‖c‖ * C, fun x => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

theorem mem_bddMeasurable {f : X → H → ℂ} :
    f ∈ bddMeasurable X H ↔ Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := Iff.rfl

/-- The constant function `x ↦ ξ` is bounded measurable. -/
theorem const_mem_bddMeasurable (ξ : H → ℂ) : (fun _ : X => ξ) ∈ bddMeasurable X H :=
  ⟨measurable_const, ‖ξ‖, fun _ => le_rfl⟩

/-- Multiplication by a bounded measurable scalar function preserves bounded measurability. -/
theorem smul_mem_bddMeasurable {g : X → ℂ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C)
    {f : X → H → ℂ} (hf : f ∈ bddMeasurable X H) : (fun x => g x • f x) ∈ bddMeasurable X H := by
  obtain ⟨hfm, D, hD⟩ := hf
  refine ⟨hg.smul hfm, C * D, fun x => ?_⟩
  rw [norm_smul]
  exact mul_le_mul (hgC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hgC x))

/-- Simple functions are bounded measurable. -/
theorem simpleFunc_mem_bddMeasurable (φ : SimpleFunc X (H → ℂ)) : ⇑φ ∈ bddMeasurable X H := by
  refine ⟨φ.measurable, ?_⟩
  obtain ⟨C, hC⟩ := φ.exists_forall_norm_le
  exact ⟨C, hC⟩

namespace PosOperatorMeasure

/-! ## The semi-inner product -/

variable (μ : PosOperatorMeasure X H) [IsFiniteMeasure μ.toVectorMeasure.variation]

/-- The semi-inner product `⟨f, g⟩_μ = ∫ ⟨f(x), dμ(x) g(x)⟩` on bounded measurable functions. -/
noncomputable def form (f g : X → H → ℂ) : ℂ :=
  VectorMeasure.integral μ.toVectorMeasure (innerIntegrand f g) pairCLM

theorem integrable_innerIntegrand {f g : X → H → ℂ} (hf : f ∈ bddMeasurable X H)
    (hg : g ∈ bddMeasurable X H) :
    Integrable (innerIntegrand f g) μ.toVectorMeasure.variation := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  refine Integrable.mono' (integrable_const (C * D))
    (measurable_innerIntegrand hfm hgm).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  exact (norm_innerIntegrand_le f g x).trans
    (mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))

theorem innerIntegrand_add_left (f g h : X → H → ℂ) :
    innerIntegrand (f + g) h = innerIntegrand f h + innerIntegrand g h := by
  funext x i j
  simp [innerIntegrand_apply, add_mul]

theorem innerIntegrand_smul_left (c : ℂ) (f g : X → H → ℂ) :
    innerIntegrand (c • f) g = fun x => star c • innerIntegrand f g x := by
  funext x i j
  simp [innerIntegrand_apply, mul_assoc]

theorem innerIntegrand_conjTranspose (f g : X → H → ℂ) (x : X) :
    OperatorTailMeasure.conjTransposeCLM (innerIntegrand f g x) = innerIntegrand g f x := by
  funext i j
  simp [innerIntegrand_apply, mul_comm]

theorem form_add_left {f g h : X → H → ℂ} (hf : f ∈ bddMeasurable X H) (hg : g ∈ bddMeasurable X H)
    (hh : h ∈ bddMeasurable X H) : μ.form (f + g) h = μ.form f h + μ.form g h := by
  unfold form
  rw [innerIntegrand_add_left]
  exact VectorMeasure.integral_add (μ.integrable_innerIntegrand hf hh)
    (μ.integrable_innerIntegrand hg hh)

/-- Complex constants come out of the pairing integral. -/
theorem integral_pairCLM_const_smul (c : ℂ) {A : X → H → H → ℂ}
    (hA : Integrable A μ.toVectorMeasure.variation) :
    VectorMeasure.integral μ.toVectorMeasure (fun x => c • A x) pairCLM =
      c * VectorMeasure.integral μ.toVectorMeasure A pairCLM := by
  have h1 : (fun x => c • A x) =
      fun x => (ContinuousLinearMap.lsmul ℝ ℂ c : (H → H → ℂ) →L[ℝ] (H → H → ℂ)) (A x) := by
    funext x
    simp
  rw [h1, VectorMeasure.integral_continuousLinearMap_comp hA]
  have h2 := VectorMeasure.continuousLinearMap_apply_integral (μ := μ.toVectorMeasure)
    (B := (pairCLM : (H → H → ℂ) →L[ℝ] (H → H → ℂ) →L[ℝ] ℂ))
    (C := (ContinuousLinearMap.lsmul ℝ ℂ c : ℂ →L[ℝ] ℂ)) hA
  rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul] at h2
  rw [h2]
  congr 1
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun M => ?_
  simp [pairCLM_apply, Finset.mul_sum, mul_assoc]

theorem form_smul_left (c : ℂ) {f g : X → H → ℂ} (hf : f ∈ bddMeasurable X H)
    (hg : g ∈ bddMeasurable X H) : μ.form (c • f) g = star c * μ.form f g := by
  unfold form
  rw [innerIntegrand_smul_left]
  exact μ.integral_pairCLM_const_smul _ (μ.integrable_innerIntegrand hf hg)

/-- The conjugate of a pairing integral against a Hermitian-valued measure is the pairing integral
of the conjugate transpose. -/
theorem star_integral_pairCLM {A : X → H → H → ℂ} (hA : Integrable A μ.toVectorMeasure.variation) :
    star (VectorMeasure.integral μ.toVectorMeasure A pairCLM) =
      VectorMeasure.integral μ.toVectorMeasure
        (fun x => OperatorTailMeasure.conjTransposeCLM (A x)) pairCLM := by
  have h1 : star (VectorMeasure.integral μ.toVectorMeasure A pairCLM) =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) (VectorMeasure.integral μ.toVectorMeasure A pairCLM) := rfl
  rw [h1, VectorMeasure.continuousLinearMap_apply_integral hA,
    VectorMeasure.integral_continuousLinearMap_comp hA]
  set B₁ : (H → H → ℂ) →L[ℝ] (H → H → ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.compL ℝ (H → H → ℂ) ℂ ℂ (Complex.conjCLE : ℂ →L[ℝ] ℂ)) ∘L pairCLM
  set B₂ : (H → H → ℂ) →L[ℝ] (H → H → ℂ) →L[ℝ] ℂ :=
    pairCLM ∘L OperatorTailMeasure.conjTransposeCLM
  have hT : μ.toVectorMeasure.transpose B₁ = μ.toVectorMeasure.transpose B₂ := by
    refine VectorMeasure.ext fun s hs => ?_
    change B₁.flip (μ.toVectorMeasure s) = B₂.flip (μ.toVectorMeasure s)
    refine ContinuousLinearMap.ext fun A => ?_
    change star (pairCLM A (μ.toVectorMeasure s)) =
      pairCLM (OperatorTailMeasure.conjTransposeCLM A) (μ.toVectorMeasure s)
    simp only [pairCLM_apply, star_sum, star_mul', OperatorTailMeasure.conjTransposeCLM_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [μ.isHermitian_apply s i j]
  rw [VectorMeasure.integral_eq_setToFun, VectorMeasure.integral_eq_setToFun]
  exact setToFun_congr_left' _ _ (fun s _ _ => by rw [hT]) A

theorem form_conj_symm {f g : X → H → ℂ} (hf : f ∈ bddMeasurable X H) (hg : g ∈ bddMeasurable X H) :
    star (μ.form g f) = μ.form f g := by
  unfold form
  rw [μ.star_integral_pairCLM (μ.integrable_innerIntegrand hg hf)]
  congr 1
  funext x
  exact innerIntegrand_conjTranspose g f x

/-! ## Positivity -/

/-- The form on an indicator function `1_s ξ` is the quadratic form `⟨ξ, μ(s) ξ⟩`. -/
theorem form_indicator_const {s : Set X} (hs : MeasurableSet s) (ξ η : H → ℂ) :
    μ.form (s.indicator fun _ => ξ) (s.indicator fun _ => η) =
      OperatorTailMeasure.sesqForm ξ η (Matrix.of (μ.toVectorMeasure s)) := by
  unfold form
  have h : innerIntegrand (s.indicator fun _ => ξ) (s.indicator fun _ => η) =
      s.indicator fun _ => (fun i j => star (ξ i) * η j) := by
    funext x i j
    by_cases hx : x ∈ s <;> simp [innerIntegrand_apply, Set.indicator, hx]
  rw [h, VectorMeasure.integral_indicator_const _ hs, pairCLM_apply]
  simp only [OperatorTailMeasure.sesqForm, dotProduct, Matrix.mulVec, Matrix.of_apply,
    Finset.mul_sum, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Positivity of the form on simple functions. -/
theorem re_form_self_nonneg_simpleFunc (φ : SimpleFunc X (H → ℂ)) :
    0 ≤ (μ.form φ φ).re ∧ (μ.form φ φ).im = 0 := by
  refine SimpleFunc.induction (motive := fun φ : SimpleFunc X (H → ℂ) =>
    0 ≤ (μ.form φ φ).re ∧ (μ.form φ φ).im = 0) ?_ ?_ φ
  · intro c s hs
    have hcoe : ⇑(SimpleFunc.piecewise s hs (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
        s.indicator fun _ => c := by
      funext x
      by_cases hx : x ∈ s <;> simp [SimpleFunc.piecewise_apply, Set.indicator_apply, hx]
    rw [hcoe, μ.form_indicator_const hs]
    exact ⟨OperatorTailMeasure.posSemidef_re_quadForm_nonneg (μ.posSemidef s hs) c,
      OperatorTailMeasure.posSemidef_im_quadForm_eq_zero (μ.posSemidef s hs) c⟩
  · intro φ ψ hdisj hφ hψ
    have hcross : ∀ (a b : SimpleFunc X (H → ℂ)), Disjoint (Function.support a)
        (Function.support b) → μ.form a b = 0 := by
      intro a b hab
      unfold form
      have : innerIntegrand a b = 0 := by
        funext x i j
        by_cases hx : a x = 0
        · simp [innerIntegrand_apply, hx]
        · have hb : b x = 0 := by
            by_contra hb
            exact Set.disjoint_left.mp hab hx hb
          simp [innerIntegrand_apply, hb]
      rw [this]
      exact VectorMeasure.integral_zero
    have hmφ := simpleFunc_mem_bddMeasurable φ
    have hmψ := simpleFunc_mem_bddMeasurable ψ
    rw [SimpleFunc.coe_add, μ.form_add_left hmφ hmψ ((bddMeasurable X H).add_mem hmφ hmψ)]
    have h1 : μ.form φ (φ + ψ) = μ.form φ φ := by
      rw [← μ.form_conj_symm hmφ ((bddMeasurable X H).add_mem hmφ hmψ), μ.form_add_left hmφ hmψ hmφ,
        hcross ψ φ hdisj.symm, add_zero, μ.form_conj_symm hmφ hmφ]
    have h2 : μ.form ψ (φ + ψ) = μ.form ψ ψ := by
      rw [← μ.form_conj_symm hmψ ((bddMeasurable X H).add_mem hmφ hmψ), μ.form_add_left hmφ hmψ hmψ,
        hcross φ ψ hdisj, zero_add, μ.form_conj_symm hmψ hmψ]
    rw [h1, h2, Complex.add_re, Complex.add_im, hφ.2, hψ.2]
    exact ⟨add_nonneg hφ.1 hψ.1, by simp⟩

/-- Simple approximations of a bounded measurable function. -/
theorem exists_simpleFunc_tendsto {f : X → H → ℂ} (hf : f ∈ bddMeasurable X H) :
    ∃ φ : ℕ → SimpleFunc X (H → ℂ), (∀ n x, ‖φ n x‖ ≤ 2 * ‖f x‖) ∧
      ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (f x)) := by
  obtain ⟨hfm, -⟩ := hf
  refine ⟨fun n => SimpleFunc.approxOn f hfm univ 0 (mem_univ _) n, fun n x => ?_, fun x => ?_⟩
  · have := SimpleFunc.norm_approxOn_zero_le hfm (mem_univ (0 : H → ℂ)) x n
    linarith
  · exact SimpleFunc.tendsto_approxOn hfm (mem_univ _) (by simp)

/-- Dominated convergence for the form along pointwise bounded convergence. -/
theorem tendsto_form_of_tendsto {f g : ℕ → X → H → ℂ} {f₀ g₀ : X → H → ℂ}
    (hf : ∀ n, f n ∈ bddMeasurable X H) (hg : ∀ n, g n ∈ bddMeasurable X H)
    (hf₀ : f₀ ∈ bddMeasurable X H) (hg₀ : g₀ ∈ bddMeasurable X H)
    {C : ℝ} (hfC : ∀ n x, ‖f n x‖ ≤ C) (hgC : ∀ n x, ‖g n x‖ ≤ C)
    (hft : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hgt : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (g₀ x))) :
    Tendsto (fun n => μ.form (f n) (g n)) atTop (𝓝 (μ.form f₀ g₀)) := by
  unfold form
  refine VectorMeasure.tendsto_integral_filter_of_norm_le_const
    (Eventually.of_forall fun n => (measurable_innerIntegrand (hf n).1 (hg n).1).aestronglyMeasurable)
    ⟨C * C, Eventually.of_forall fun n => ae_of_all _ fun x => ?_⟩ (ae_of_all _ fun x => ?_)
  · exact (norm_innerIntegrand_le _ _ x).trans
      (mul_le_mul (hfC n x) (hgC n x) (norm_nonneg _) ((norm_nonneg _).trans (hfC n x)))
  · have hc : Continuous fun p : (H → ℂ) × (H → ℂ) => (fun i j => star (p.1 i) * p.2 j : H → H → ℂ) :=
      continuous_pi fun i => continuous_pi fun j =>
        (((continuous_apply i).comp continuous_fst).star).mul ((continuous_apply j).comp continuous_snd)
    exact (hc.tendsto (f₀ x, g₀ x)).comp ((hft x).prodMk_nhds (hgt x))

/-- **Positivity of the form** on bounded measurable functions. -/
theorem re_form_self_nonneg {f : X → H → ℂ} (hf : f ∈ bddMeasurable X H) :
    0 ≤ (μ.form f f).re := by
  obtain ⟨φ, hφb, hφt⟩ := exists_simpleFunc_tendsto hf
  obtain ⟨C, hC⟩ := hf.2
  have hφC : ∀ n x, ‖φ n x‖ ≤ 2 * C := fun n x => (hφb n x).trans (by linarith [hC x])
  have ht := μ.tendsto_form_of_tendsto (fun n => simpleFunc_mem_bddMeasurable (φ n))
    (fun n => simpleFunc_mem_bddMeasurable (φ n)) hf hf hφC hφC hφt hφt
  exact ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp ht)
    fun n => (μ.re_form_self_nonneg_simpleFunc (φ n)).1

/-! ## The pre-Hilbert space and its completion -/

end PosOperatorMeasure

/-- The pre-Hilbert space of `con:supp-Naimark-tail`: bounded measurable `H`-valued functions
with the semi-inner product `⟨f, g⟩_μ`. -/
def PreL2 (μ : PosOperatorMeasure X H) : Type _ := ↥(bddMeasurable X H)

namespace PreL2

variable (μ : PosOperatorMeasure X H)

instance : AddCommGroup (PreL2 μ) := inferInstanceAs (AddCommGroup ↥(bddMeasurable X H))
instance : Module ℂ (PreL2 μ) := inferInstanceAs (Module ℂ ↥(bddMeasurable X H))

variable {μ} in
/-- The underlying function. -/
def toFun (f : PreL2 μ) : X → H → ℂ := (f : ↥(bddMeasurable X H)).1

variable {μ} in
theorem mem (f : PreL2 μ) : f.toFun ∈ bddMeasurable X H := (f : ↥(bddMeasurable X H)).2

/-- Build an element from a bounded measurable function. -/
def ofFun (f : X → H → ℂ) (hf : f ∈ bddMeasurable X H) : PreL2 μ :=
  (⟨f, hf⟩ : ↥(bddMeasurable X H))

@[simp] theorem toFun_ofFun (f : X → H → ℂ) (hf : f ∈ bddMeasurable X H) :
    (ofFun μ f hf).toFun = f := rfl

variable {μ} in
@[simp] theorem toFun_add (f g : PreL2 μ) : (f + g).toFun = f.toFun + g.toFun := rfl
variable {μ} in
@[simp] theorem toFun_smul (c : ℂ) (f : PreL2 μ) : (c • f).toFun = c • f.toFun := rfl
variable {μ} in
@[simp] theorem toFun_sub (f g : PreL2 μ) : (f - g).toFun = f.toFun - g.toFun := rfl
variable {μ} in
@[simp] theorem toFun_neg (f : PreL2 μ) : (-f).toFun = -f.toFun := rfl
@[simp] theorem toFun_zero : (0 : PreL2 μ).toFun = 0 := rfl

variable {μ} in
theorem ext {f g : PreL2 μ} (h : f.toFun = g.toFun) : f = g := Subtype.ext h

variable [IsFiniteMeasure μ.toVectorMeasure.variation]

noncomputable instance : PreInnerProductSpace.Core ℂ (PreL2 μ) where
  inner f g := μ.form f.toFun g.toFun
  conj_inner_symm f g := μ.form_conj_symm f.mem g.mem
  re_inner_nonneg f := μ.re_form_self_nonneg f.mem
  add_left f g h := μ.form_add_left f.mem g.mem h.mem
  smul_left f g r := μ.form_smul_left r f.mem g.mem

noncomputable instance instSeminormedAddCommGroup : SeminormedAddCommGroup (PreL2 μ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ) (F := PreL2 μ)

noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (PreL2 μ) :=
  InnerProductSpace.ofCore (𝕜 := ℂ) (F := PreL2 μ) inferInstance

theorem inner_def (f g : PreL2 μ) : ⟪f, g⟫_ℂ = μ.form f.toFun g.toFun := rfl

theorem norm_eq (f : PreL2 μ) : ‖f‖ = Real.sqrt (μ.form f.toFun f.toFun).re := rfl

end PreL2

/-- **The Hilbert space `K_μ = L²(μ; H)`** of `con:supp-Naimark-tail`: the pre-Hilbert space of
bounded measurable functions, quotiented by its null space and completed. -/
abbrev L2 (μ : PosOperatorMeasure X H) [IsFiniteMeasure μ.toVectorMeasure.variation] : Type _ :=
  UniformSpace.Completion (SeparationQuotient (PreL2 μ))

namespace L2

variable (μ : PosOperatorMeasure X H) [IsFiniteMeasure μ.toVectorMeasure.variation]

/-- The canonical map `f ↦ [f]` from the pre-Hilbert space to `L²(μ; H)`. -/
noncomputable def mk : PreL2 μ →L[ℂ] L2 μ :=
  (UniformSpace.Completion.toComplL : SeparationQuotient (PreL2 μ) →L[ℂ] L2 μ) ∘L
    SeparationQuotient.mkCLM ℂ (PreL2 μ)

theorem mk_apply (f : PreL2 μ) :
    mk μ f = ((SeparationQuotient.mk f : SeparationQuotient (PreL2 μ)) : L2 μ) := rfl

theorem inner_mk_mk (f g : PreL2 μ) : ⟪mk μ f, mk μ g⟫_ℂ = μ.form f.toFun g.toFun := by
  rw [mk_apply, mk_apply, UniformSpace.Completion.inner_coe, SeparationQuotient.inner_mk_mk]
  rfl

theorem norm_mk (f : PreL2 μ) : ‖mk μ f‖ = Real.sqrt (μ.form f.toFun f.toFun).re := by
  rw [mk_apply, UniformSpace.Completion.norm_coe, SeparationQuotient.norm_mk]
  rfl

theorem coe_mk : ⇑(mk μ) = ((↑) : SeparationQuotient (PreL2 μ) → L2 μ) ∘ SeparationQuotient.mk :=
  rfl

theorem denseRange_mk : DenseRange (mk μ) := by
  rw [coe_mk]
  exact UniformSpace.Completion.denseRange_coe.comp SeparationQuotient.surjective_mk.denseRange
    (UniformSpace.Completion.continuous_coe _)

theorem isUniformInducing_mk : IsUniformInducing (mk μ) := by
  rw [coe_mk]
  exact (UniformSpace.Completion.isUniformInducing_coe _).comp SeparationQuotient.isUniformInducing_mk

/-- Two continuous linear maps out of `L2 μ` agreeing on the image of `mk` are equal. -/
theorem ext_of_mk {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {A B : L2 μ →L[ℂ] F}
    (h : ∀ f, A (mk μ f) = B (mk μ f)) : A = B := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine (denseRange_mk μ).induction_on x (isClosed_eq A.continuous B.continuous) fun f => ?_
  exact h f

end L2

/-! ### Bounded scalar multipliers -/

/-- A bounded measurable scalar function on `X`, with an explicit bound. -/
structure BddScalar (X : Type*) [MeasurableSpace X] where
  /-- The function. -/
  toFun : X → ℂ
  /-- Measurability. -/
  measurable : Measurable toFun
  /-- A bound. -/
  bound : ℝ
  /-- Nonnegativity of the bound. -/
  bound_nonneg : 0 ≤ bound
  /-- The bound. -/
  norm_le : ∀ x, ‖toFun x‖ ≤ bound

namespace BddScalar


/-- Pointwise product. -/
def mul (g₁ g₂ : BddScalar X) : BddScalar X where
  toFun x := g₁.toFun x * g₂.toFun x
  measurable := g₁.measurable.mul g₂.measurable
  bound := g₁.bound * g₂.bound
  bound_nonneg := mul_nonneg g₁.bound_nonneg g₂.bound_nonneg
  norm_le x := by
    rw [norm_mul]
    exact mul_le_mul (g₁.norm_le x) (g₂.norm_le x) (norm_nonneg _) g₁.bound_nonneg

/-- Pointwise sum. -/
def add (g₁ g₂ : BddScalar X) : BddScalar X where
  toFun x := g₁.toFun x + g₂.toFun x
  measurable := g₁.measurable.add g₂.measurable
  bound := g₁.bound + g₂.bound
  bound_nonneg := add_nonneg g₁.bound_nonneg g₂.bound_nonneg
  norm_le x := (norm_add_le _ _).trans (add_le_add (g₁.norm_le x) (g₂.norm_le x))

/-- Pointwise conjugate. -/
def conj (g : BddScalar X) : BddScalar X where
  toFun x := star (g.toFun x)
  measurable := continuous_star.measurable.comp g.measurable
  bound := g.bound
  bound_nonneg := g.bound_nonneg
  norm_le x := by
    rw [norm_star]
    exact g.norm_le x

/-- The constant function `1`. -/
def one : BddScalar X where
  toFun _ := 1
  measurable := measurable_const
  bound := 1
  bound_nonneg := zero_le_one
  norm_le _ := by simp

/-- The indicator function of a measurable set. -/
noncomputable def indicator (s : Set X) (hs : MeasurableSet s) : BddScalar X where
  toFun := s.indicator fun _ => 1
  measurable := measurable_const.indicator hs
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := by
    by_cases hx : x ∈ s <;> simp [Set.indicator_apply, hx]

@[simp] theorem mul_toFun (g₁ g₂ : BddScalar X) (x : X) :
    (g₁.mul g₂).toFun x = g₁.toFun x * g₂.toFun x := rfl
@[simp] theorem add_toFun (g₁ g₂ : BddScalar X) (x : X) :
    (g₁.add g₂).toFun x = g₁.toFun x + g₂.toFun x := rfl
@[simp] theorem conj_toFun (g : BddScalar X) (x : X) :
    g.conj.toFun x = star (g.toFun x) := rfl
@[simp] theorem one_toFun (x : X) : (one : BddScalar X).toFun x = 1 := rfl
@[simp] theorem indicator_toFun (s : Set X) (hs : MeasurableSet s) (x : X) :
    (indicator s hs).toFun x = s.indicator (fun _ => (1 : ℂ)) x := rfl

end BddScalar

namespace L2

variable (μ : PosOperatorMeasure X H) [IsFiniteMeasure μ.toVectorMeasure.variation]

/-- Multiplication by `g` on the pre-Hilbert space. -/
noncomputable def mulPre (g : BddScalar X) : PreL2 μ →ₗ[ℂ] PreL2 μ where
  toFun f := PreL2.ofFun μ (fun x => g.toFun x • f.toFun x)
    (smul_mem_bddMeasurable g.measurable g.norm_le f.mem)
  map_add' f h := by
    refine PreL2.ext ?_
    funext x
    simp [smul_add]
  map_smul' c f := by
    refine PreL2.ext ?_
    funext x
    change g.toFun x • (c • f.toFun x) = c • (g.toFun x • f.toFun x)
    exact smul_comm _ _ _

@[simp] theorem mulPre_toFun (g : BddScalar X) (f : PreL2 μ) (x : X) :
    (mulPre μ g f).toFun x = g.toFun x • f.toFun x := rfl

/-- The multiplier bound `‖g f‖_μ ≤ sup|g| ‖f‖_μ`, from positivity of the form applied to
`√(sup|g|² - |g|²) f`. -/
theorem norm_mulPre_le (g : BddScalar X) (f : PreL2 μ) : ‖mulPre μ g f‖ ≤ g.bound * ‖f‖ := by
  set C := g.bound with hC
  set k : X → ℂ := fun x => ((Real.sqrt (C ^ 2 - ‖g.toFun x‖ ^ 2) : ℝ) : ℂ) with hk
  have hkm : Measurable k := Complex.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp (measurable_const.sub (g.measurable.norm.pow_const 2)))
  have hkb : ∀ x, ‖k x‖ ≤ C := fun x => by
    rw [hk]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (C ^ 2 - ‖g.toFun x‖ ^ 2) ≤ Real.sqrt (C ^ 2) :=
          Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖g.toFun x‖])
      _ = C := Real.sqrt_sq g.bound_nonneg
  have hgC : ∀ x, ‖g.toFun x‖ ^ 2 ≤ C ^ 2 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (g.norm_le x) 2
  set kf : X → H → ℂ := fun x => k x • f.toFun x with hkf
  have hkf_mem : kf ∈ bddMeasurable X H := smul_mem_bddMeasurable hkm hkb f.mem
  have hgf_mem : (fun x => g.toFun x • f.toFun x) ∈ bddMeasurable X H :=
    smul_mem_bddMeasurable g.measurable g.norm_le f.mem
  have h1 : innerIntegrand kf kf =
      (C ^ 2) • innerIntegrand f.toFun f.toFun - innerIntegrand (fun x => g.toFun x • f.toFun x)
        (fun x => g.toFun x • f.toFun x) := by
    funext x i j
    simp only [innerIntegrand_apply, hkf, hk, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, star_mul',
      Complex.star_def, Complex.conj_ofReal]
    have hst : (starRingEnd ℂ) (g.toFun x) * g.toFun x = ((‖g.toFun x‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
    have hsq : ((Real.sqrt (C ^ 2 - ‖g.toFun x‖ ^ 2) : ℝ) : ℂ) *
        ((Real.sqrt (C ^ 2 - ‖g.toFun x‖ ^ 2) : ℝ) : ℂ) = ((C ^ 2 - ‖g.toFun x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith [hgC x])]
    rw [Complex.real_smul]
    push_cast at hsq hst ⊢
    linear_combination ((starRingEnd ℂ) (f.toFun x i) * f.toFun x j) * hsq +
      ((starRingEnd ℂ) (f.toFun x i) * f.toFun x j) * hst
  have hint := μ.integrable_innerIntegrand f.mem f.mem
  have hint' := μ.integrable_innerIntegrand hgf_mem hgf_mem
  have hpos := μ.re_form_self_nonneg hkf_mem
  unfold PosOperatorMeasure.form at hpos
  rw [h1] at hpos
  rw [VectorMeasure.integral_sub (hint.smul _) hint', VectorMeasure.integral_smul,
    Complex.sub_re, Complex.real_smul, Complex.re_ofReal_mul] at hpos
  set a := (VectorMeasure.integral μ.toVectorMeasure (innerIntegrand f.toFun f.toFun) pairCLM).re
    with ha
  set b := (VectorMeasure.integral μ.toVectorMeasure (innerIntegrand
    (fun x => g.toFun x • f.toFun x) (fun x => g.toFun x • f.toFun x)) pairCLM).re with hb
  have hle : b ≤ C ^ 2 * a := by linarith
  have hmul : (mulPre μ g f).toFun = fun x => g.toFun x • f.toFun x := rfl
  rw [PreL2.norm_eq, PreL2.norm_eq, hmul]
  unfold PosOperatorMeasure.form
  rw [← hb, ← ha]
  calc Real.sqrt b ≤ Real.sqrt (C ^ 2 * a) := Real.sqrt_le_sqrt hle
    _ = C * Real.sqrt a := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq g.bound_nonneg]

/-- Multiplication by `g` as a continuous linear map on the pre-Hilbert space. -/
noncomputable def mulPreCLM (g : BddScalar X) : PreL2 μ →L[ℂ] PreL2 μ :=
  (mulPre μ g).mkContinuous g.bound (norm_mulPre_le μ g)

/-- **The bounded multiplication operator** `f ↦ g f` on `L²(μ; H)`. -/
noncomputable def mul (g : BddScalar X) : L2 μ →L[ℂ] L2 μ :=
  ((mk μ) ∘L mulPreCLM μ g).extend (mk μ)

theorem mul_mk (g : BddScalar X) (f : PreL2 μ) : mul μ g (mk μ f) = mk μ (mulPre μ g f) :=
  ContinuousLinearMap.extend_eq _ (denseRange_mk μ) (isUniformInducing_mk μ) f

/-- The multiplication operator depends only on the function. -/
theorem mul_congr {g g' : BddScalar X} (h : g.toFun = g'.toFun) : mul μ g = mul μ g' := by
  refine ext_of_mk μ fun f => ?_
  rw [mul_mk, mul_mk]
  congr 1
  refine PreL2.ext ?_
  funext x
  simp [h]

theorem mul_mul (g₁ g₂ : BddScalar X) : mul μ (g₁.mul g₂) = mul μ g₁ ∘L mul μ g₂ := by
  refine ext_of_mk μ fun f => ?_
  rw [ContinuousLinearMap.comp_apply, mul_mk, mul_mk, mul_mk]
  congr 1
  refine PreL2.ext ?_
  funext x
  simp [mul_smul]

theorem mul_one : mul μ BddScalar.one = ContinuousLinearMap.id ℂ (L2 μ) := by
  refine ext_of_mk μ fun f => ?_
  rw [mul_mk, ContinuousLinearMap.id_apply]
  congr 1
  refine PreL2.ext ?_
  funext x
  simp

theorem mul_add (g₁ g₂ : BddScalar X) : mul μ (g₁.add g₂) = mul μ g₁ + mul μ g₂ := by
  refine ext_of_mk μ fun f => ?_
  rw [ContinuousLinearMap.add_apply, mul_mk, mul_mk, mul_mk, ← map_add]
  congr 1
  refine PreL2.ext ?_
  funext x
  simp [add_smul]

/-- The adjoint of multiplication by `g` is multiplication by `conj g`. -/
theorem adjoint_mul (g : BddScalar X) :
    ContinuousLinearMap.adjoint (mul μ g) = mul μ g.conj := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  refine (denseRange_mk μ).induction_on₂
    (p := fun x y => ⟪mul μ g.conj x, y⟫_ℂ = ⟪x, mul μ g y⟫_ℂ) ?_ ?_ x y
  · exact isClosed_eq (((mul μ g.conj).continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner ((mul μ g).continuous.comp continuous_snd))
  · intro f h
    rw [mul_mk, mul_mk, inner_mk_mk, inner_mk_mk]
    unfold PosOperatorMeasure.form
    congr 1
    funext x i j
    simp [innerIntegrand_apply, mul_assoc, mul_left_comm]

/-- If `g` is supported in a measurable set `s` on which `μ` vanishes, then `mul μ g = 0`. -/
theorem mul_eq_zero_of_forall_subset {g : BddScalar X} {s : Set X} (hs : MeasurableSet s)
    (hg : ∀ x, x ∉ s → g.toFun x = 0)
    (hμ : ∀ t : Set X, MeasurableSet t → t ⊆ s → μ.toVectorMeasure t = 0) :
    mul μ g = 0 := by
  refine ext_of_mk μ fun f => ?_
  rw [mul_mk, ContinuousLinearMap.zero_apply, ← norm_eq_zero, norm_mk]
  have hres : μ.toVectorMeasure.restrict s = 0 := by
    refine VectorMeasure.ext fun t ht => ?_
    rw [VectorMeasure.restrict_apply _ hs ht, VectorMeasure.zero_apply]
    exact hμ _ (ht.inter hs) inter_subset_right
  have hind : innerIntegrand (mulPre μ g f).toFun (mulPre μ g f).toFun =
      s.indicator (innerIntegrand (mulPre μ g f).toFun (mulPre μ g f).toFun) := by
    funext x i j
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, innerIntegrand_apply, hg x hx]
  unfold PosOperatorMeasure.form
  rw [hind, VectorMeasure.integral_indicator hs, hres, VectorMeasure.integral_zero_vectorMeasure]
  simp

/-! ### The projection-valued measure `E ↦ multiplication by 1_E` -/

/-- **The projection-valued measure** `P_μ(E) = ` multiplication by `1_E`
(`con:supp-Naimark-tail`). -/
noncomputable def proj (s : Set X) (hs : MeasurableSet s) : L2 μ →L[ℂ] L2 μ :=
  mul μ (BddScalar.indicator s hs)

theorem proj_inter (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    proj μ (s ∩ t) (hs.inter ht) = proj μ s hs ∘L proj μ t ht := by
  unfold proj
  rw [← mul_mul]
  refine mul_congr μ ?_
  funext x
  by_cases hx : x ∈ s <;> by_cases hx' : x ∈ t <;> simp [Set.indicator_apply, hx, hx']

theorem proj_univ : proj μ univ MeasurableSet.univ = ContinuousLinearMap.id ℂ (L2 μ) := by
  unfold proj
  rw [← mul_one]
  refine mul_congr μ ?_
  funext x
  simp

theorem proj_union_of_disjoint {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) : proj μ (s ∪ t) (hs.union ht) = proj μ s hs + proj μ t ht := by
  unfold proj
  rw [← mul_add]
  refine mul_congr μ ?_
  funext x
  by_cases hx : x ∈ s
  · have hx' : x ∉ t := Set.disjoint_left.mp hst hx
    simp [Set.indicator_apply, hx, hx']
  · by_cases hx' : x ∈ t <;> simp [Set.indicator_apply, hx, hx']

theorem isSelfAdjoint_proj (s : Set X) (hs : MeasurableSet s) : IsSelfAdjoint (proj μ s hs) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
  unfold proj
  rw [adjoint_mul]
  refine mul_congr μ ?_
  funext x
  by_cases hx : x ∈ s <;> simp [Set.indicator_apply, hx]

theorem isIdempotentElem_proj (s : Set X) (hs : MeasurableSet s) :
    IsIdempotentElem (proj μ s hs) := by
  have h := proj_inter μ s s hs hs
  simp only [Set.inter_self] at h
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, ← h]

theorem proj_eq_zero_of_forall_subset {s : Set X} (hs : MeasurableSet s)
    (hμ : ∀ t : Set X, MeasurableSet t → t ⊆ s → μ.toVectorMeasure t = 0) : proj μ s hs = 0 :=
  mul_eq_zero_of_forall_subset μ hs (fun x hx => by simp [Set.indicator_of_notMem hx]) hμ

/-- The indicator `1_s f` of a bounded measurable function. -/
theorem indicator_mem_bddMeasurable {s : Set X} (hs : MeasurableSet s) (f : PreL2 μ) :
    s.indicator f.toFun ∈ bddMeasurable X H := by
  obtain ⟨hfm, C, hC⟩ := f.mem
  refine ⟨hfm.indicator hs, C, fun x => ?_⟩
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx, hC x]
  · simp [Set.indicator_of_notMem hx, (norm_nonneg _).trans (hC x)]

theorem proj_mk (s : Set X) (hs : MeasurableSet s) (f : PreL2 μ) :
    proj μ s hs (mk μ f) = mk μ (PreL2.ofFun μ (s.indicator f.toFun)
      (indicator_mem_bddMeasurable μ hs f)) := by
  unfold proj
  rw [mul_mk]
  congr 1
  refine PreL2.ext ?_
  funext x
  by_cases hx : x ∈ s <;> simp [Set.indicator_apply, hx]

/-! ### Norm bounds -/

theorem norm_mk_eq (f : PreL2 μ) : ‖mk μ f‖ = ‖f‖ := by
  rw [norm_mk, PreL2.norm_eq]

theorem norm_mul_apply_le (g : BddScalar X) (x : L2 μ) : ‖mul μ g x‖ ≤ g.bound * ‖x‖ := by
  refine (denseRange_mk μ).induction_on x
    (isClosed_le (mul μ g).continuous.norm (continuous_const.mul continuous_norm)) fun f => ?_
  rw [mul_mk, norm_mk_eq, norm_mk_eq]
  exact norm_mulPre_le μ g f

theorem norm_mul_le (g : BddScalar X) : ‖mul μ g‖ ≤ g.bound :=
  ContinuousLinearMap.opNorm_le_bound _ g.bound_nonneg (norm_mul_apply_le μ g)

theorem norm_proj_le (s : Set X) (hs : MeasurableSet s) : ‖proj μ s hs‖ ≤ 1 :=
  norm_mul_le μ _

/-- `⟨x, P(s) x⟩ = ⟨P(s) x, P(s) x⟩` for the orthogonal projections `P(s)`. -/
theorem inner_proj_self (s : Set X) (hs : MeasurableSet s) (x : L2 μ) :
    ⟪x, proj μ s hs x⟫_ℂ = ⟪proj μ s hs x, proj μ s hs x⟫_ℂ := by
  have hidem := isIdempotentElem_proj μ s hs
  have hsa := isSelfAdjoint_proj μ s hs
  conv_lhs => rw [← hidem.eq]
  rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left]
  have hadj : ContinuousLinearMap.adjoint (proj μ s hs) = proj μ s hs := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hsa.star_eq
  rw [hadj]

/-! ### Strong convergence from a dense subset -/

/-- A uniformly bounded sequence of operators converging pointwise on a dense subset converges
pointwise everywhere. -/
theorem tendsto_apply_of_denseRange {E F D : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {e : D → E} (he : DenseRange e)
    {T : ℕ → E →L[ℂ] F} {T₀ : E →L[ℂ] F} {C : ℝ} (hT : ∀ n, ‖T n‖ ≤ C) (hT₀ : ‖T₀‖ ≤ C)
    (h : ∀ d, Tendsto (fun n => T n (e d)) atTop (𝓝 (T₀ (e d)))) (x : E) :
    Tendsto (fun n => T n x) atTop (𝓝 (T₀ x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hC : 0 ≤ C := (norm_nonneg _).trans hT₀
  set δ := ε / (3 * (C + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδC : (C + 1) * δ = ε / 3 := by
    rw [hδ]
    field_simp
  obtain ⟨d, hd⟩ := Metric.denseRange_iff.mp he x δ hδpos
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h d) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound : ∀ S : E →L[ℂ] F, ‖S‖ ≤ C → dist (S x) (S (e d)) ≤ C * δ := fun S hS => by
    rw [dist_eq_norm, ← map_sub]
    calc ‖S (x - e d)‖ ≤ ‖S‖ * ‖x - e d‖ := S.le_opNorm _
      _ ≤ C * δ := by
          rw [dist_eq_norm] at hd
          exact mul_le_mul hS hd.le (norm_nonneg _) hC
  have h1 := hbound (T n) (hT n)
  have h2 := hbound T₀ hT₀
  have h3 := hN n hn
  have h4 : C * δ ≤ ε / 3 := by nlinarith
  calc dist (T n x) (T₀ x) ≤ dist (T n x) (T n (e d)) + dist (T n (e d)) (T₀ (e d)) +
        dist (T₀ (e d)) (T₀ x) := dist_triangle4 _ _ _ _
    _ < ε := by
        rw [dist_comm (T₀ (e d))]
        linarith

/-! ### Strong σ-additivity of the projection-valued measure -/

theorem form_zero_left (g : X → H → ℂ) : μ.form 0 g = 0 := by
  unfold PosOperatorMeasure.form
  have : innerIntegrand (0 : X → H → ℂ) g = 0 := by
    funext x i j
    simp [innerIntegrand_apply]
  rw [this]
  exact VectorMeasure.integral_zero

/-- Continuity from below of `P_μ` on the image of `mk`. -/
theorem tendsto_proj_mk_of_monotone {F : ℕ → Set X} (hF : ∀ n, MeasurableSet (F n))
    (hmono : Monotone F) (f : PreL2 μ) :
    Tendsto (fun n => proj μ (F n) (hF n) (mk μ f)) atTop
      (𝓝 (proj μ (⋃ n, F n) (MeasurableSet.iUnion hF) (mk μ f))) := by
  set U := ⋃ n, F n with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion hF
  -- the difference is `[1_{U \ F n} f]`
  have hdiff : ∀ n, proj μ (F n) (hF n) (mk μ f) - proj μ U hUm (mk μ f) =
      -(mk μ (PreL2.ofFun μ ((U \ F n).indicator f.toFun)
        (indicator_mem_bddMeasurable μ (hUm.diff (hF n)) f))) := by
    intro n
    rw [proj_mk, proj_mk, ← map_sub, ← map_neg]
    congr 1
    refine PreL2.ext ?_
    funext x
    simp only [PreL2.toFun_sub, PreL2.toFun_ofFun, Pi.sub_apply, PreL2.toFun_neg, Pi.neg_apply]
    by_cases hx : x ∈ F n
    · have hxU : x ∈ U := Set.mem_iUnion.mpr ⟨n, hx⟩
      simp [Set.indicator_apply, hx, hxU]
    · by_cases hxU : x ∈ U
      · simp [Set.indicator_apply, hx, hxU]
      · simp [Set.indicator_apply, hx, hxU]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖proj μ (F n) (hF n) (mk μ f) - proj μ U hUm (mk μ f)‖ =
      Real.sqrt (μ.form ((U \ F n).indicator f.toFun) ((U \ F n).indicator f.toFun)).re := by
    intro n
    rw [hdiff n, norm_neg, norm_mk, PreL2.toFun_ofFun]
  refine (tendsto_congr hnorm).mpr ?_
  -- the forms tend to zero by dominated convergence
  obtain ⟨C, hC⟩ := f.mem.2
  have hpt : ∀ x, Tendsto (fun n => (U \ F n).indicator f.toFun x) atTop (𝓝 ((0 : X → H → ℂ) x)) := by
    intro x
    by_cases hxU : x ∈ U
    · obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hxU
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      have : x ∉ U \ F n := fun h => h.2 (hmono hn hm)
      simp [Set.indicator_of_notMem this]
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      have : x ∉ U \ F n := fun h => hxU h.1
      simp [Set.indicator_of_notMem this]
  have hbd : ∀ n x, ‖(U \ F n).indicator f.toFun x‖ ≤ C := fun n x => by
    by_cases hx : x ∈ U \ F n
    · simp [Set.indicator_of_mem hx, hC x]
    · simp [Set.indicator_of_notMem hx, (norm_nonneg _).trans (hC x)]
  have hform := μ.tendsto_form_of_tendsto (f := fun n => (U \ F n).indicator f.toFun)
    (g := fun n => (U \ F n).indicator f.toFun) (f₀ := 0) (g₀ := 0)
    (fun n => indicator_mem_bddMeasurable μ (hUm.diff (hF n)) f)
    (fun n => indicator_mem_bddMeasurable μ (hUm.diff (hF n)) f) (Submodule.zero_mem _)
    (Submodule.zero_mem _) hbd hbd hpt hpt
  rw [form_zero_left] at hform
  have := ((Real.continuous_sqrt.comp Complex.continuous_re).tendsto 0).comp hform
  simp only [Function.comp_def, Complex.zero_re, Real.sqrt_zero] at this
  exact this

/-- Continuity from below of the projection-valued measure `P_μ` (strong topology). -/
theorem tendsto_proj_of_monotone {F : ℕ → Set X} (hF : ∀ n, MeasurableSet (F n))
    (hmono : Monotone F) (x : L2 μ) :
    Tendsto (fun n => proj μ (F n) (hF n) x) atTop
      (𝓝 (proj μ (⋃ n, F n) (MeasurableSet.iUnion hF) x)) :=
  tendsto_apply_of_denseRange (denseRange_mk μ) (fun n => norm_proj_le μ _ _) (norm_proj_le μ _ _)
    (fun f => tendsto_proj_mk_of_monotone μ hF hmono f) x

/-- Finite additivity over a finite set of pairwise disjoint sets. -/
theorem proj_biUnion_finset {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise fun m n => Disjoint (E m) (E n)) (t : Finset ℕ) :
    proj μ (⋃ n ∈ t, E n) (t.measurableSet_biUnion fun n _ => hE n) =
      ∑ n ∈ t, proj μ (E n) (hE n) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Finset.sum_empty]
    exact proj_eq_zero_of_forall_subset μ MeasurableSet.empty fun s _ hs => by
      rw [Set.subset_empty_iff.mp hs, VectorMeasure.empty]
  | insert a s has ih =>
    have hU : (⋃ n ∈ insert a s, E n) = E a ∪ ⋃ n ∈ s, E n := by
      ext x
      simp
    have hd : Disjoint (E a) (⋃ n ∈ s, E n) := by
      rw [Set.disjoint_iUnion₂_right]
      intro n hn
      exact hdisj (fun h => has (h ▸ hn))
    rw [Finset.sum_insert has, ← ih, ← proj_union_of_disjoint μ (hE a)
      (s.measurableSet_biUnion fun n _ => hE n) hd]
    congr 1

/-- Pythagoras for a finite family of pairwise disjoint sets. -/
theorem norm_sq_sum_proj {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise fun m n => Disjoint (E m) (E n)) (t : Finset ℕ) (x : L2 μ) :
    ‖∑ n ∈ t, proj μ (E n) (hE n) x‖ ^ 2 = ∑ n ∈ t, ‖proj μ (E n) (hE n) x‖ ^ 2 := by
  have hsum : ∑ n ∈ t, proj μ (E n) (hE n) x =
      proj μ (⋃ n ∈ t, E n) (t.measurableSet_biUnion fun n _ => hE n) x := by
    rw [proj_biUnion_finset μ hE hdisj t, ContinuousLinearMap.sum_apply]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hsum, ← inner_proj_self, proj_biUnion_finset μ hE hdisj t,
    ContinuousLinearMap.sum_apply, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_proj_self]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (proj μ (E n) (hE n) x)

/-- The squared norms `‖P(E n) x‖²` are summable, with sum at most `‖x‖²`. -/
theorem summable_norm_sq_proj {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise fun m n => Disjoint (E m) (E n)) (x : L2 μ) :
    Summable fun n => ‖proj μ (E n) (hE n) x‖ ^ 2 := by
  refine summable_of_sum_range_le (c := ‖x‖ ^ 2) (fun n => sq_nonneg _) fun N => ?_
  rw [← norm_sq_sum_proj μ hE hdisj, ← ContinuousLinearMap.sum_apply,
    ← proj_biUnion_finset μ hE hdisj]
  have := (norm_proj_le μ (⋃ n ∈ Finset.range N, E n)
    ((Finset.range N).measurableSet_biUnion fun n _ => hE n))
  calc ‖proj μ (⋃ n ∈ Finset.range N, E n) _ x‖ ^ 2
      ≤ (‖proj μ (⋃ n ∈ Finset.range N, E n) _‖ * ‖x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
    _ ≤ (1 * ‖x‖) ^ 2 := by gcongr
    _ = ‖x‖ ^ 2 := by rw [one_mul]

/-- **Strong σ-additivity of the projection-valued measure**: for pairwise disjoint measurable
sets, `∑ₙ P_μ(E n) x = P_μ(⋃ₙ E n) x`. -/
theorem hasSum_proj {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise fun m n => Disjoint (E m) (E n)) (x : L2 μ) :
    HasSum (fun n => proj μ (E n) (hE n) x) (proj μ (⋃ n, E n) (MeasurableSet.iUnion hE) x) := by
  -- summability from the vanishing of tails of the squared norms
  have hsq := summable_norm_sq_proj μ hE hdisj x
  have hsumm : Summable fun n => proj μ (E n) (hE n) x := by
    rw [summable_iff_vanishing_norm]
    intro ε hε
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsq (ε ^ 2) (by positivity)
    refine ⟨s, fun t ht => ?_⟩
    have h := hs t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun n _ => sq_nonneg _),
      ← norm_sq_sum_proj μ hE hdisj] at h
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h
  -- identify the sum through the partial sums
  have hpartial : Tendsto (fun N => ∑ n ∈ Finset.range N, proj μ (E n) (hE n) x) atTop
      (𝓝 (proj μ (⋃ n, E n) (MeasurableSet.iUnion hE) x)) := by
    have hmono : Monotone fun N => ⋃ n ∈ Finset.range N, E n := by
      intro N M hNM
      exact Set.biUnion_subset_biUnion_left (Finset.range_subset_range.mpr hNM)
    have hU : (⋃ N, ⋃ n ∈ Finset.range N, E n) = ⋃ n, E n := by
      ext y
      simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
      exact ⟨fun ⟨_, n, _, h⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨n + 1, n, Nat.lt_succ_self n, h⟩⟩
    have := tendsto_proj_of_monotone μ (F := fun N => ⋃ n ∈ Finset.range N, E n)
      (fun N => (Finset.range N).measurableSet_biUnion fun n _ => hE n) hmono x
    simp_rw [proj_biUnion_finset μ hE hdisj, ContinuousLinearMap.sum_apply] at this
    simp only [hU] at this
    exact this
  have hlim := hsumm.hasSum.tendsto_sum_nat
  have heq := tendsto_nhds_unique hlim hpartial
  rw [← heq]
  exact hsumm.hasSum

/-! ### The embedding `V_μ` of `H` -/

/-- **The embedding `V_μ ξ = [1 ξ]`** of `H` into `L²(μ; H)` (`con:supp-Naimark-tail`). -/
noncomputable def embed : EuclideanSpace ℂ H →L[ℂ] L2 μ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => mk μ (PreL2.ofFun μ (fun _ => WithLp.ofLp ξ) (const_mem_bddMeasurable _))
      map_add' := fun ξ η => by
        rw [← map_add]
        exact congrArg (mk μ) (PreL2.ext (funext fun x => by simp))
      map_smul' := fun c ξ => by
        rw [RingHom.id_apply, ← map_smul]
        exact congrArg (mk μ) (PreL2.ext (funext fun x => by simp)) }

theorem embed_apply (ξ : EuclideanSpace ℂ H) :
    embed μ ξ = mk μ (PreL2.ofFun μ (fun _ => WithLp.ofLp ξ) (const_mem_bddMeasurable _)) := rfl

/-- **Compression identity** `⟨V ξ, P(s) V η⟩ = ⟨ξ, μ(s) η⟩`, i.e. `μ(s) = B P(s) B^*`
(`thm:supp-Naimark-realization`). -/
theorem inner_embed_proj_embed (s : Set X) (hs : MeasurableSet s) (ξ η : EuclideanSpace ℂ H) :
    ⟪embed μ ξ, proj μ s hs (embed μ η)⟫_ℂ =
      ⟪ξ, Matrix.toEuclideanLin (Matrix.of (μ.toVectorMeasure s)) η⟫_ℂ := by
  rw [embed_apply, embed_apply, proj_mk, inner_mk_mk]
  have h : μ.form (fun _ : X => WithLp.ofLp ξ) (s.indicator fun _ => WithLp.ofLp η) =
      μ.form (s.indicator fun _ => WithLp.ofLp ξ) (s.indicator fun _ => WithLp.ofLp η) := by
    unfold PosOperatorMeasure.form
    congr 1
    funext x i j
    by_cases hx : x ∈ s <;> simp [innerIntegrand_apply, Set.indicator_apply, hx]
  simp only [PreL2.toFun_ofFun]
  rw [h, μ.form_indicator_const hs, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanLin_apply, OperatorTailMeasure.sesqForm, dotProduct_comm]

/-! ### Minimality `eq:supp-Naimark-minimal` -/

/-- The span of the spectral source vectors `P(s) V ξ`. -/
noncomputable def sourceSpan : Submodule ℂ (L2 μ) :=
  Submodule.span ℂ {y : L2 μ | ∃ (s : Set X) (hs : MeasurableSet s) (ξ : EuclideanSpace ℂ H),
    y = proj μ s hs (embed μ ξ)}

theorem mk_simpleFunc_mem_sourceSpan (φ : SimpleFunc X (H → ℂ)) :
    mk μ (PreL2.ofFun μ φ (simpleFunc_mem_bddMeasurable φ)) ∈ sourceSpan μ := by
  refine SimpleFunc.induction (motive := fun φ : SimpleFunc X (H → ℂ) =>
    mk μ (PreL2.ofFun μ φ (simpleFunc_mem_bddMeasurable φ)) ∈ sourceSpan μ) ?_ ?_ φ
  · intro c s hs
    refine Submodule.subset_span ⟨s, hs, WithLp.toLp 2 c, ?_⟩
    rw [embed_apply, proj_mk]
    refine congrArg (mk μ) (PreL2.ext (funext fun x => ?_))
    by_cases hx : x ∈ s <;> simp [SimpleFunc.piecewise_apply, Set.indicator_apply, hx]
  · intro φ ψ _ hφ hψ
    have : PreL2.ofFun μ (⇑(φ + ψ)) (simpleFunc_mem_bddMeasurable (φ + ψ)) =
        PreL2.ofFun μ φ (simpleFunc_mem_bddMeasurable φ) +
          PreL2.ofFun μ ψ (simpleFunc_mem_bddMeasurable ψ) := by
      refine PreL2.ext ?_
      funext x
      simp
    rw [this, map_add]
    exact (sourceSpan μ).add_mem hφ hψ

theorem mk_mem_closure_sourceSpan (f : PreL2 μ) :
    mk μ f ∈ closure (sourceSpan μ : Set (L2 μ)) := by
  obtain ⟨φ, hφb, hφt⟩ := PosOperatorMeasure.exists_simpleFunc_tendsto f.mem
  obtain ⟨C, hC⟩ := f.mem.2
  have hφC : ∀ n x, ‖φ n x‖ ≤ 2 * C := fun n x => (hφb n x).trans (by linarith [hC x])
  refine mem_closure_of_tendsto (b := atTop) (f := fun n => mk μ (PreL2.ofFun μ (φ n)
    (simpleFunc_mem_bddMeasurable (φ n)))) ?_ (Eventually.of_forall fun n =>
    mk_simpleFunc_mem_sourceSpan μ (φ n))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [← map_sub, norm_mk]
  have hmem : ∀ n, (PreL2.ofFun μ (φ n) (simpleFunc_mem_bddMeasurable (φ n)) - f).toFun ∈
      bddMeasurable X H := fun n => (PreL2.ofFun μ (φ n) _ - f).mem
  have hpt : ∀ x, Tendsto (fun n => (PreL2.ofFun μ (φ n) (simpleFunc_mem_bddMeasurable (φ n)) -
      f).toFun x) atTop (𝓝 ((0 : X → H → ℂ) x)) := by
    intro x
    simp only [PreL2.toFun_sub, PreL2.toFun_ofFun, Pi.sub_apply, Pi.zero_apply]
    have := (hφt x).sub_const (f.toFun x)
    simpa using this
  have hbd : ∀ n x, ‖(PreL2.ofFun μ (φ n) (simpleFunc_mem_bddMeasurable (φ n)) - f).toFun x‖ ≤
      3 * C := fun n x => by
    simp only [PreL2.toFun_sub, PreL2.toFun_ofFun, Pi.sub_apply]
    calc ‖φ n x - f.toFun x‖ ≤ ‖φ n x‖ + ‖f.toFun x‖ := norm_sub_le _ _
      _ ≤ 2 * C + C := add_le_add (hφC n x) (hC x)
      _ = 3 * C := by ring
  have hform := μ.tendsto_form_of_tendsto hmem hmem (Submodule.zero_mem _) (Submodule.zero_mem _)
    hbd hbd hpt hpt
  rw [form_zero_left] at hform
  have := ((Real.continuous_sqrt.comp Complex.continuous_re).tendsto 0).comp hform
  simp only [Function.comp_def, Complex.zero_re, Real.sqrt_zero] at this
  exact this

/-- **`eq:supp-Naimark-minimal`**: the spectral source vectors `P_μ(E) V_μ ξ` span a dense
subspace of `L²(μ; H)`. -/
theorem topologicalClosure_sourceSpan : (sourceSpan μ).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  have h1 : closure (Set.range (mk μ)) ⊆ closure (sourceSpan μ : Set (L2 μ)) :=
    closure_minimal (Set.range_subset_iff.mpr fun f => mk_mem_closure_sourceSpan μ f)
      isClosed_closure
  exact h1 ((denseRange_mk μ).closure_range ▸ Set.mem_univ x)

end L2

end OperatorMeasureL2
end RenewalGeometry
