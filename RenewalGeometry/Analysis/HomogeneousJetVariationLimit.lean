/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LpProductContinuity
import RenewalGeometry.Continuum.NativeYangMillsIdentification

/-!
# First variations of degree-two homogeneous jet densities under strong `L²` jet convergence

Generic infrastructure (no renewal notions) for the first-jet consistency of literal lattice
actions (`prop:native-gravity-firstjet` of the Einstein–SM action-closure manuscript).

Setting: a finite measure space `(X, μ)`, finite-dimensional real normed spaces `V` (values),
`Q` (first differences) and `T` (test jets), and a density `Γ : ℝ × (V × Q) → ℝ` of a mesh
parameter `ρ` and a jet `(v, q)` which is **homogeneous of degree two under the lattice
rescaling** `(ρ, v, q) ↦ (ρK, v, q/K)`:
`Γ(ρ, v, q) = K² Γ(ρK, v, K⁻¹q)` for `K > 0`.
This is the exact scaling of a literal logarithmic plaquette density (`lem:native-scaling`).

* `jetDeriv Γ ρ w = D_w Γ(ρ, ·)(w)`: the partial derivative in the jet variable.
* `jetDeriv_scale`: the homogeneity transported to the jet derivative,
  `D_wΓ(ρ, v, q)[v̇, q̇] = K² D_wΓ(ρK, v, q/K)[v̇, q̇/K]`.
* `TendstoInMeasure.prodMk`, `tendstoInMeasure_of_lipschitz`, `normalize`: small calculus of
  convergence in measure.
* `lpTendsto_homogeneous_variation` (**the variation limit**): suppose `Γ` is `C¹` at every point
  of a compact set `Kc` which contains all normalised jets
  `(ρ_k (1 + ‖q_k‖), v_k, q_k/(1 + ‖q_k‖))`, the mesh `ρ_k → 0`, the values `v_k → v` in measure
  and the differences `q_k → q` strongly in `L²`.  Let the variation directions be given by
  linear maps of a test jet `t ∈ T`, `v̇ = L_k t` and `q̇ = (B_k + A_k q_k) t`, with `L_k, B_k, A_k`
  uniformly bounded and converging in measure (the derivative of a lifted test contains one
  factor of the first difference of the field).  Then the covector fields
  `t ↦ D_wΓ(ρ_k, v_k, q_k)[L_k t, (B_k + A_k q_k) t]` converge **strongly in `L¹`** to the
  corresponding covector at `ρ = 0` and the limit jet.  No pointwise bound on the differences
  and no second differences are used: the homogeneity converts the degree-two growth into
  bounded coefficients (converging in measure) times `L¹`-convergent products of the strongly
  convergent first differences (`lem:products`).
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal

namespace RenewalGeometry.HomogeneousJetVariation

open LpProductContinuity

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-! ### Convergence in measure: pairs, Lipschitz maps, normalisation -/

section InMeasure

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Convergence in measure of the two components gives convergence in measure of the pair. -/
theorem TendstoInMeasure.prodMk {f : ℕ → X → E} {f₀ : X → E} {g : ℕ → X → F} {g₀ : X → F}
    (hf : TendstoInMeasure μ f atTop f₀) (hg : TendstoInMeasure μ g atTop g₀) :
    TendstoInMeasure μ (fun k x => (f k x, g k x)) atTop (fun x => (f₀ x, g₀ x)) := by
  rw [tendstoInMeasure_iff_dist] at hf hg ⊢
  intro ε hε
  have h := (hf ε hε).add (hg ε hε)
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    fun k => ?_
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro x hx
  simp only [Set.mem_ofPred_eq, Prod.dist_eq] at hx
  rcases le_max_iff.1 hx with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

/-- Lipschitz maps preserve convergence in measure. -/
theorem tendstoInMeasure_of_lipschitz {Φ : E → F} {L : ℝ} (hL : 0 < L)
    (hΦ : ∀ a b, dist (Φ a) (Φ b) ≤ L * dist a b) {f : ℕ → X → E} {f₀ : X → E}
    (hf : TendstoInMeasure μ f atTop f₀) :
    TendstoInMeasure μ (fun k x => Φ (f k x)) atTop (fun x => Φ (f₀ x)) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf (ε / L) (by positivity))
    (fun k => zero_le) fun k => measure_mono fun x hx => ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [div_le_iff₀ hL]
  have := hΦ (f k x) (f₀ x)
  nlinarith

variable [NormedSpace ℝ E]

/-- The normalisation `q ↦ q / (1 + ‖q‖)` into the closed unit ball. -/
def normalize (q : E) : E := (1 + ‖q‖)⁻¹ • q

theorem one_add_norm_pos (q : E) : 0 < 1 + ‖q‖ := by positivity

theorem norm_normalize_le (q : E) : ‖normalize q‖ ≤ 1 := by
  unfold normalize
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (one_add_norm_pos q).le)]
  rw [inv_mul_le_iff₀ (one_add_norm_pos q)]
  linarith

/-- The normalisation is `2`-Lipschitz. -/
theorem dist_normalize_le (a b : E) : dist (normalize a) (normalize b) ≤ 2 * dist a b := by
  rw [dist_eq_norm, dist_eq_norm]
  unfold normalize
  have ha := one_add_norm_pos a
  have hb := one_add_norm_pos b
  have e : (1 + ‖a‖)⁻¹ • a - (1 + ‖b‖)⁻¹ • b =
      ((1 + ‖a‖)⁻¹ * (1 + ‖b‖)⁻¹) • ((1 + ‖b‖) • (a - b) + (‖b‖ - ‖a‖) • b) := by
    rw [smul_add, smul_smul, smul_smul, smul_sub]
    have h1 : (1 + ‖a‖)⁻¹ * (1 + ‖b‖)⁻¹ * (1 + ‖b‖) = (1 + ‖a‖)⁻¹ := by
      field_simp
    have h2 : (1 + ‖a‖)⁻¹ * (1 + ‖b‖)⁻¹ * (‖b‖ - ‖a‖) = (1 + ‖a‖)⁻¹ - (1 + ‖b‖)⁻¹ := by
      field_simp; ring
    rw [h1, h2, sub_smul]
    abel
  rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hn : ‖(1 + ‖b‖) • (a - b) + (‖b‖ - ‖a‖) • b‖ ≤ (1 + 2 * ‖b‖) * ‖a - b‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hb.le, Real.norm_eq_abs]
    have h3 : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
      rw [abs_sub_comm]; exact abs_norm_sub_norm_le a b
    nlinarith [norm_nonneg b, norm_nonneg (a - b)]
  calc (1 + ‖a‖)⁻¹ * (1 + ‖b‖)⁻¹ * ‖(1 + ‖b‖) • (a - b) + (‖b‖ - ‖a‖) • b‖
      ≤ (1 + ‖a‖)⁻¹ * (1 + ‖b‖)⁻¹ * ((1 + 2 * ‖b‖) * ‖a - b‖) := by gcongr
    _ ≤ 2 * ‖a - b‖ := by
        rw [← mul_assoc]
        have h4 : (1 + ‖a‖)⁻¹ * (1 + ‖b‖)⁻¹ * (1 + 2 * ‖b‖) ≤ 2 := by
          rw [mul_assoc, ← div_eq_inv_mul, ← div_eq_inv_mul, div_le_iff₀ ha]
          rw [div_le_iff₀ hb]
          nlinarith [norm_nonneg a, norm_nonneg b, mul_nonneg (norm_nonneg a) (norm_nonneg b)]
        exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)

end InMeasure

/-! ### Measurability of compositions with functions continuous on a closed set -/

section Measurability

/-- If `ζ` is a.e. strongly measurable with values a.e. in a closed set `s` and `g` is continuous
on `s`, then `g ∘ ζ` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_comp_continuousOn {Z W : Type*} [TopologicalSpace Z]
    [PseudoMetrizableSpace Z] [SecondCountableTopology Z] [TopologicalSpace W]
    [PseudoMetrizableSpace W] {g : Z → W} {s : Set Z} (hs : IsClosed s) (hg : ContinuousOn g s)
    {ζ : X → Z} (hζ : AEStronglyMeasurable ζ μ) (hmem : ∀ᵐ x ∂μ, ζ x ∈ s) :
    AEStronglyMeasurable (fun x => g (ζ x)) μ := by
  borelize Z
  have hζ' : AEMeasurable ζ μ := hζ.aemeasurable
  have h1 : ∀ᵐ z ∂(μ.map ζ), z ∈ s := (ae_map_iff hζ' hs.measurableSet).2 hmem
  have h2 : AEStronglyMeasurable g (μ.map ζ) := by
    rw [← Measure.restrict_eq_self_of_ae_mem h1]
    exact hg.aestronglyMeasurable hs.measurableSet
  exact h2.comp_aemeasurable hζ'

/-- A limit in measure of functions with values in a closed set takes values in the set a.e. -/
theorem ae_mem_of_tendstoInMeasure {Z : Type*} [MetricSpace Z] {s : Set Z} (hs : IsClosed s)
    {f : ℕ → X → Z} {f₀ : X → Z} (hf : TendstoInMeasure μ f atTop f₀)
    (hmem : ∀ k, ∀ᵐ x ∂μ, f k x ∈ s) : ∀ᵐ x ∂μ, f₀ x ∈ s := by
  obtain ⟨ns, -, hns⟩ := hf.exists_seq_tendsto_ae
  filter_upwards [hns, ae_all_iff.2 fun k => hmem (ns k)] with x hx hxs
  exact hs.mem_of_tendsto hx (Eventually.of_forall hxs)

end Measurability

/-! ### The jet derivative and its homogeneity -/

section Jet

variable {V Q T : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- The partial derivative `D_w Γ(ρ, ·)(w)` in the jet variable `w = (v, q)`. -/
def jetDeriv (Γ : ℝ × (V × Q) → ℝ) (ρ : ℝ) (w : V × Q) : V × Q →L[ℝ] ℝ :=
  fderiv ℝ (fun w' => Γ (ρ, w')) w

/-- The jet rescaling `(v, q) ↦ (v, K⁻¹ q)`. -/
def rescale (K : ℝ) : V × Q →L[ℝ] V × Q :=
  (ContinuousLinearMap.fst ℝ V Q).prod (K⁻¹ • ContinuousLinearMap.snd ℝ V Q)

@[simp] theorem rescale_apply (K : ℝ) (w : V × Q) : rescale K w = (w.1, K⁻¹ • w.2) := rfl

/-- At a point of differentiability the jet derivative is the restriction of the full derivative. -/
theorem jetDeriv_eq {Γ : ℝ × (V × Q) → ℝ} {z : ℝ × (V × Q)} (hz : DifferentiableAt ℝ Γ z) :
    jetDeriv Γ z.1 z.2 = (fderiv ℝ Γ z).comp (ContinuousLinearMap.inr ℝ ℝ (V × Q)) := by
  have h := hz.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  exact h.fderiv

/-- **Homogeneity of the jet derivative.**  If `Γ(ρ, v, q) = K² Γ(ρK, v, K⁻¹q)` for all jets, then
`D_wΓ(ρ, w) = K² D_wΓ(ρK, rescale_K w) ∘ rescale_K`. -/
theorem jetDeriv_scale {Γ : ℝ × (V × Q) → ℝ} {ρ K : ℝ}
    (hom : ∀ v q, Γ (ρ, (v, q)) = K ^ 2 * Γ (ρ * K, (v, K⁻¹ • q))) (w : V × Q)
    (hd : DifferentiableAt ℝ (fun w' => Γ (ρ * K, w')) (rescale K w)) :
    jetDeriv Γ ρ w = K ^ 2 • (jetDeriv Γ (ρ * K) (rescale K w)).comp (rescale K) := by
  unfold jetDeriv
  have hf : (fun w' : V × Q => Γ (ρ, w')) = fun w' => K ^ 2 * Γ (ρ * K, rescale K w') := by
    funext w'
    exact hom w'.1 w'.2
  rw [hf]
  have h := ((hd.hasFDerivAt.comp w ((rescale K).hasFDerivAt (x := w))).const_mul (K ^ 2))
  exact h.fderiv

theorem differentiableAt_slice {Γ : ℝ × (V × Q) → ℝ} {z : ℝ × (V × Q)}
    (hz : DifferentiableAt ℝ Γ z) : DifferentiableAt ℝ (fun w' => Γ (z.1, w')) z.2 :=
  hz.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2).differentiableAt

/-- The jet derivative is continuous on a set of points at which `Γ` is `C¹`. -/
theorem continuousOn_jetDeriv {Γ : ℝ × (V × Q) → ℝ} {Kc : Set (ℝ × (V × Q))}
    (hC1 : ∀ z ∈ Kc, ContDiffAt ℝ 1 Γ z) :
    ContinuousOn (fun z : ℝ × (V × Q) => jetDeriv Γ z.1 z.2) Kc := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  have h1 := hC1 z hz
  have hfd : ContinuousAt (fderiv ℝ Γ) z :=
    (h1.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hev : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ Γ z' :=
    (h1.eventually (by simp)).mono fun z' hz' => hz'.differentiableAt one_ne_zero
  have heq : (fun z' : ℝ × (V × Q) => jetDeriv Γ z'.1 z'.2) =ᶠ[𝓝 z]
      fun z' => (fderiv ℝ Γ z').comp (ContinuousLinearMap.inr ℝ ℝ (V × Q)) :=
    hev.mono fun z' hz' => jetDeriv_eq hz'
  refine ContinuousAt.congr ?_ heq.symm
  exact (ContinuousLinearMap.compL ℝ (V × Q) (ℝ × (V × Q)) ℝ |>.flip
    (ContinuousLinearMap.inr ℝ ℝ (V × Q))).continuous.continuousAt.comp hfd

end Jet

/-! ### The variation limit -/

section Main

variable {V Q T : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]

/-- The normalised jet `(ρ (1 + ‖q‖), v, q/(1 + ‖q‖))`. -/
def normJet (ρ : ℝ) (v : V) (q : Q) : ℝ × (V × Q) := (ρ * (1 + ‖q‖), (v, normalize q))

/-- The variation covector `t ↦ D_wΓ(ρ, v, q)[L t, (B + A q) t]`. -/
def varCov (Γ : ℝ × (V × Q) → ℝ) (ρ : ℝ) (v : V) (q : Q) (L : T →L[ℝ] V) (B : T →L[ℝ] Q)
    (A : Q →L[ℝ] T →L[ℝ] Q) : T →L[ℝ] ℝ :=
  (jetDeriv Γ ρ (v, q)).comp (L.prod (B + A q))

/-- **Pointwise decomposition of the variation covector** by the homogeneity, with
`K = 1 + ‖q‖` and `D = D_wΓ` at the normalised jet:
`K² D(L ·, 0) + K D(0, B ·) + D(0, A (K q) ·)`. -/
theorem varCov_eq {Γ : ℝ × (V × Q) → ℝ}
    (hom : ∀ ρ K v q, 0 < K → Γ (ρ, (v, q)) = K ^ 2 * Γ (ρ * K, (v, K⁻¹ • q)))
    (ρ : ℝ) (v : V) (q : Q) (L : T →L[ℝ] V) (B : T →L[ℝ] Q) (A : Q →L[ℝ] T →L[ℝ] Q)
    (hd : DifferentiableAt ℝ Γ (normJet ρ v q)) :
    varCov Γ ρ v q L B A =
      (1 + ‖q‖) ^ 2 • ((jetDeriv Γ (normJet ρ v q).1 (normJet ρ v q).2).comp
          ((ContinuousLinearMap.inl ℝ V Q).comp L)) +
        (1 + ‖q‖) • ((jetDeriv Γ (normJet ρ v q).1 (normJet ρ v q).2).comp
          ((ContinuousLinearMap.inr ℝ V Q).comp B)) +
        (jetDeriv Γ (normJet ρ v q).1 (normJet ρ v q).2).comp
          ((ContinuousLinearMap.inr ℝ V Q).comp (A ((1 + ‖q‖) • q))) := by
  set K := 1 + ‖q‖ with hK
  have hK0 : 0 < K := one_add_norm_pos q
  have hsc := jetDeriv_scale (Γ := Γ) (ρ := ρ) (K := K) (fun v q => hom ρ K v q hK0) (v, q)
    (differentiableAt_slice hd)
  set D := jetDeriv Γ (normJet ρ v q).1 (normJet ρ v q).2 with hD
  have hD' : jetDeriv Γ (ρ * K) (rescale K (v, q)) = D := rfl
  rw [hD'] at hsc
  ext t
  simp only [varCov, hsc, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.prod_apply, rescale_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    smul_eq_mul, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  have h : (L t, K⁻¹ • (B t + (A q) t)) =
      (L t, 0) + K⁻¹ • ((0 : V), B t) + K⁻¹ • ((0 : V), (A q) t) := by
    ext <;> simp [smul_add]
  rw [h, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  field_simp

variable [IsFiniteMeasure μ]

local instance fact_one_le_two_hj : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_one_hj : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩

/-- Convergence of continuous images of bounded pairs converging in measure. -/
theorem tendstoInMeasure_pair_comp {E₁ E₂ W : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : E₁ × E₂ → W)
    (hΦ : Continuous Φ) {M C : ℝ} {f : ℕ → X → E₁} {f₀ : X → E₁} {g : ℕ → X → E₂} {g₀ : X → E₂}
    (hfm : ∀ k, AEStronglyMeasurable (f k) μ) (hgm : ∀ k, AEStronglyMeasurable (g k) μ)
    (hf : TendstoInMeasure μ f atTop f₀) (hg : TendstoInMeasure μ g atTop g₀)
    (hfM : ∀ k x, ‖f k x‖ ≤ M) (hf₀M : ∀ᵐ x ∂μ, ‖f₀ x‖ ≤ M) (hgC : ∀ k x, ‖g k x‖ ≤ C) :
    (∀ k, AEStronglyMeasurable (fun x => Φ (f k x, g k x)) μ) ∧
      (∃ M', ∀ k x, ‖Φ (f k x, g k x)‖ ≤ M') ∧
      TendstoInMeasure μ (fun k x => Φ (f k x, g k x)) atTop (fun x => Φ (f₀ x, g₀ x)) := by
  have hg₀C : ∀ᵐ x ∂μ, ‖g₀ x‖ ≤ C :=
    ae_norm_le_of_tendstoInMeasure hg fun k => Eventually.of_forall (hgC k)
  set S : Set (E₁ × E₂) := Metric.closedBall 0 M ×ˢ Metric.closedBall 0 C
  have hS : IsCompact S := (isCompact_closedBall 0 M).prod (isCompact_closedBall 0 C)
  have hmemS : ∀ k x, (f k x, g k x) ∈ S := fun k x =>
    ⟨mem_closedBall_zero_iff.2 (hfM k x), mem_closedBall_zero_iff.2 (hgC k x)⟩
  obtain ⟨M', hM'⟩ := (hS.image_of_continuousOn hΦ.continuousOn).isBounded.exists_norm_le
  refine ⟨fun k => hΦ.comp_aestronglyMeasurable ((hfm k).prodMk (hgm k)),
    ⟨M', fun k x => hM' _ ⟨_, hmemS k x, rfl⟩⟩, ?_⟩
  refine tendstoInMeasure_comp_of_continuousOn hS hΦ.continuousOn
    (fun k => Eventually.of_forall (hmemS k)) ?_ (TendstoInMeasure.prodMk hf hg)
  filter_upwards [hf₀M, hg₀C] with x h1 h2
  exact ⟨mem_closedBall_zero_iff.2 h1, mem_closedBall_zero_iff.2 h2⟩

set_option maxHeartbeats 2000000 in
/-- **The variation limit for degree-two homogeneous jet densities.**  See the module
docstring. -/
theorem lpTendsto_homogeneous_variation {Γ : ℝ × (V × Q) → ℝ}
    (hom : ∀ ρ K v q, 0 < K → Γ (ρ, (v, q)) = K ^ 2 * Γ (ρ * K, (v, K⁻¹ • q)))
    {Kc : Set (ℝ × (V × Q))} (hKc : IsCompact Kc) (hC1 : ∀ z ∈ Kc, ContDiffAt ℝ 1 Γ z)
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0))
    {v : ℕ → X → V} {v₀ : X → V} (hvm : ∀ k, AEStronglyMeasurable (v k) μ)
    (hv : TendstoInMeasure μ v atTop v₀)
    {q : ℕ → X → Q} {q₀ : X → Q} (hq : LpTendsto μ 2 q q₀)
    (hmem : ∀ k x, normJet (ρ k) (v k x) (q k x) ∈ Kc) {C : ℝ}
    {L : ℕ → X → T →L[ℝ] V} {L₀ : X → T →L[ℝ] V} (hLm : ∀ k, AEStronglyMeasurable (L k) μ)
    (hL : TendstoInMeasure μ L atTop L₀) (hLC : ∀ k x, ‖L k x‖ ≤ C)
    {B : ℕ → X → T →L[ℝ] Q} {B₀ : X → T →L[ℝ] Q} (hBm : ∀ k, AEStronglyMeasurable (B k) μ)
    (hB : TendstoInMeasure μ B atTop B₀) (hBC : ∀ k x, ‖B k x‖ ≤ C)
    {A : ℕ → X → Q →L[ℝ] T →L[ℝ] Q} {A₀ : X → Q →L[ℝ] T →L[ℝ] Q}
    (hAm : ∀ k, AEStronglyMeasurable (A k) μ) (hA : TendstoInMeasure μ A atTop A₀)
    (hAC : ∀ k x, ‖A k x‖ ≤ C) :
    LpTendsto μ 1 (fun k x => varCov Γ (ρ k) (v k x) (q k x) (L k x) (B k x) (A k x))
      (fun x => varCov Γ 0 (v₀ x) (q₀ x) (L₀ x) (B₀ x) (A₀ x)) := by
  set D : ℝ × (V × Q) → V × Q →L[ℝ] ℝ := fun z => jetDeriv Γ z.1 z.2 with hDdef
  have hDc : ContinuousOn D Kc := continuousOn_jetDeriv hC1
  obtain ⟨M, hM⟩ := (hKc.image_of_continuousOn hDc).isBounded.exists_norm_le
  have hDM : ∀ z ∈ Kc, ‖D z‖ ≤ M := fun z hz => hM _ ⟨z, hz, rfl⟩
  have hqm : TendstoInMeasure μ q atTop q₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (hq.memLp k).1) hq.memLp_lim.1
      hq.tendsto
  -- the scalar `K = 1 + ‖q‖`
  have hK : LpTendsto μ 2 (fun k x => 1 + ‖q k x‖) (fun x => 1 + ‖q₀ x‖) := by
    have h := (LpTendsto.const (u := fun _ : X => (1 : ℝ)) (memLp_const (1 : ℝ))).add hq.norm
    exact h.congr (fun k => Eventually.of_forall fun x => rfl) (Eventually.of_forall fun x => rfl)
  -- `ρ K → 0`
  have hρK : LpTendsto μ 2 (fun k x => ρ k * (1 + ‖q k x‖)) (fun _ => (0 : ℝ)) := by
    refine ⟨fun k => (hK.memLp k).const_mul (ρ k), memLp_const 0, ?_⟩
    have hb : ∀ k, eLpNorm ((fun x => ρ k * (1 + ‖q k x‖)) - fun _ => (0 : ℝ)) 2 μ ≤
        ‖ρ k‖ₑ * eLpNorm ((fun x => 1 + ‖q k x‖) - fun x => 1 + ‖q₀ x‖) 2 μ +
          ‖ρ k‖ₑ * eLpNorm (fun x => 1 + ‖q₀ x‖) 2 μ := by
      intro k
      have e : ((fun x => ρ k * (1 + ‖q k x‖)) - fun _ => (0 : ℝ)) =
          ρ k • ((fun x => 1 + ‖q k x‖) - fun x => 1 + ‖q₀ x‖) +
            ρ k • (fun x => 1 + ‖q₀ x‖) := by
        funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      refine (eLpNorm_add_le (((hK.memLp k).1.sub hK.memLp_lim.1).const_smul _)
        (hK.memLp_lim.1.const_smul _) (by norm_num)).trans ?_
      rw [eLpNorm_const_smul, eLpNorm_const_smul]
    have hρe : Tendsto (fun k => ‖ρ k‖ₑ) atTop (𝓝 0) := by
      have := (continuous_enorm.tendsto (0 : ℝ)).comp hρ
      rw [enorm_zero] at this
      exact this
    have h1 : Tendsto (fun k => ‖ρ k‖ₑ * eLpNorm ((fun x => 1 + ‖q k x‖) -
        fun x => 1 + ‖q₀ x‖) 2 μ) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul hρe (Or.inr ENNReal.zero_ne_top) hK.tendsto
        (Or.inr ENNReal.zero_ne_top)
      simpa using this
    have h2 : Tendsto (fun k => ‖ρ k‖ₑ * eLpNorm (fun x => 1 + ‖q₀ x‖) 2 μ) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const hρe (Or.inr hK.memLp_lim.2.ne)
      simpa using this
    have h12 := h1.add h2
    rw [add_zero] at h12
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12 (fun k => zero_le) hb
  have hρKm : TendstoInMeasure μ (fun k x => ρ k * (1 + ‖q k x‖)) atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun k => (hρK.memLp k).1)
      hρK.memLp_lim.1 hρK.tendsto
  have hnorm : TendstoInMeasure μ (fun k x => normalize (q k x)) atTop
      (fun x => normalize (q₀ x)) :=
    tendstoInMeasure_of_lipschitz two_pos dist_normalize_le hqm
  have hζ : TendstoInMeasure μ (fun k x => normJet (ρ k) (v k x) (q k x)) atTop
      (fun x => ((0 : ℝ), (v₀ x, normalize (q₀ x)))) :=
    TendstoInMeasure.prodMk hρKm (TendstoInMeasure.prodMk hv hnorm)
  have hζ0 : ∀ᵐ x ∂μ, ((0 : ℝ), (v₀ x, normalize (q₀ x))) ∈ Kc :=
    ae_mem_of_tendstoInMeasure hKc.isClosed hζ fun k => Eventually.of_forall (hmem k)
  have hcontN : Continuous (normalize : Q → Q) := by
    unfold normalize
    exact ((continuous_const.add continuous_norm).inv₀ fun q => (one_add_norm_pos q).ne').smul
      continuous_id
  have hζm : ∀ k, AEStronglyMeasurable (fun x => normJet (ρ k) (v k x) (q k x)) μ := fun k =>
    ((hK.memLp k).1.const_mul (ρ k)).prodMk ((hvm k).prodMk
      (hcontN.comp_aestronglyMeasurable (hq.memLp k).1))
  have hDζm : ∀ k, AEStronglyMeasurable (fun x => D (normJet (ρ k) (v k x) (q k x))) μ :=
    fun k => aestronglyMeasurable_comp_continuousOn hKc.isClosed hDc (hζm k)
      (Eventually.of_forall (hmem k))
  have hDζ : TendstoInMeasure μ (fun k x => D (normJet (ρ k) (v k x) (q k x))) atTop
      (fun x => D ((0 : ℝ), (v₀ x, normalize (q₀ x)))) :=
    tendstoInMeasure_comp_of_continuousOn hKc hDc (fun k => Eventually.of_forall (hmem k)) hζ0 hζ
  have hDζM : ∀ k x, ‖D (normJet (ρ k) (v k x) (q k x))‖ ≤ M := fun k x => hDM _ (hmem k x)
  have hDζ0M : ∀ᵐ x ∂μ, ‖D ((0 : ℝ), (v₀ x, normalize (q₀ x)))‖ ≤ M := by
    filter_upwards [hζ0] with x hx using hDM _ hx
  -- the three coefficient fields
  set Φ1 : (V × Q →L[ℝ] ℝ) × (T →L[ℝ] V) → ℝ →L[ℝ] (T →L[ℝ] ℝ) := fun p =>
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (p.1.comp ((ContinuousLinearMap.inl ℝ V Q).comp p.2)) with hΦ1
  set Φ2 : (V × Q →L[ℝ] ℝ) × (T →L[ℝ] Q) → ℝ →L[ℝ] (T →L[ℝ] ℝ) := fun p =>
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (p.1.comp ((ContinuousLinearMap.inr ℝ V Q).comp p.2)) with hΦ2
  set Φ3 : (V × Q →L[ℝ] ℝ) × (Q →L[ℝ] T →L[ℝ] Q) → Q →L[ℝ] (T →L[ℝ] ℝ) := fun p =>
    (ContinuousLinearMap.compL ℝ T (V × Q) ℝ p.1).comp
      ((ContinuousLinearMap.compL ℝ T Q (V × Q) (ContinuousLinearMap.inr ℝ V Q)).comp p.2)
    with hΦ3
  have hsr : Continuous fun G : T →L[ℝ] ℝ =>
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) G :=
    (ContinuousLinearMap.smulRightL ℝ ℝ (T →L[ℝ] ℝ)
      (ContinuousLinearMap.id ℝ ℝ)).continuous
  have hΦ1c : Continuous Φ1 := by
    have hc := (ContinuousLinearMap.compL ℝ T (V × Q) ℝ).continuous₂
    have h1 : Continuous fun p : (V × Q →L[ℝ] ℝ) × (T →L[ℝ] V) =>
        p.1.comp ((ContinuousLinearMap.inl ℝ V Q).comp p.2) :=
      hc.comp (continuous_fst.prodMk
        ((ContinuousLinearMap.compL ℝ T V (V × Q) (ContinuousLinearMap.inl ℝ V Q)).continuous.comp
          continuous_snd))
    exact hsr.comp h1
  have hΦ2c : Continuous Φ2 := by
    have hc := (ContinuousLinearMap.compL ℝ T (V × Q) ℝ).continuous₂
    have h1 : Continuous fun p : (V × Q →L[ℝ] ℝ) × (T →L[ℝ] Q) =>
        p.1.comp ((ContinuousLinearMap.inr ℝ V Q).comp p.2) :=
      hc.comp (continuous_fst.prodMk
        ((ContinuousLinearMap.compL ℝ T Q (V × Q) (ContinuousLinearMap.inr ℝ V Q)).continuous.comp
          continuous_snd))
    exact hsr.comp h1
  have hΦ3c : Continuous Φ3 := by
    have hc := (ContinuousLinearMap.compL ℝ Q (T →L[ℝ] (V × Q)) (T →L[ℝ] ℝ)).continuous₂
    have hc1 := (ContinuousLinearMap.compL ℝ T (V × Q) ℝ).continuous
    have hc2 := (ContinuousLinearMap.compL ℝ Q (T →L[ℝ] Q) (T →L[ℝ] (V × Q))
      (ContinuousLinearMap.compL ℝ T Q (V × Q) (ContinuousLinearMap.inr ℝ V Q))).continuous
    exact hc.comp ((hc1.comp continuous_fst).prodMk (hc2.comp continuous_snd))
  obtain ⟨hβ1m, ⟨M1, hβ1M⟩, hβ1⟩ := tendstoInMeasure_pair_comp Φ1 hΦ1c hDζm hLm hDζ hL hDζM
    hDζ0M hLC
  obtain ⟨hβ2m, ⟨M2, hβ2M⟩, hβ2⟩ := tendstoInMeasure_pair_comp Φ2 hΦ2c hDζm hBm hDζ hB hDζM
    hDζ0M hBC
  obtain ⟨hβ3m, ⟨M3, hβ3M⟩, hβ3⟩ := tendstoInMeasure_pair_comp Φ3 hΦ3c hDζm hAm hDζ hA hDζM
    hDζ0M hAC
  -- the three terms
  have hK2 := LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℝ) hK hK
  have hKq := LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.lsmul ℝ ℝ) hK hq
  have t1 := LpTendsto.coeff (p := 1) ENNReal.one_ne_top hβ1m hβ1
    (fun k => Eventually.of_forall (hβ1M k)) hK2
  have t2 := (LpTendsto.coeff (p := 2) (by norm_num) hβ2m hβ2
    (fun k => Eventually.of_forall (hβ2M k)) hK).mono one_ne_zero (by norm_num)
  have t3 := LpTendsto.coeff (p := 1) ENNReal.one_ne_top hβ3m hβ3
    (fun k => Eventually.of_forall (hβ3M k)) hKq
  have hsum := (t1.add t2).add t3
  refine hsum.congr (fun k => Eventually.of_forall fun x => ?_) ?_
  · have hd : DifferentiableAt ℝ Γ (normJet (ρ k) (v k x) (q k x)) :=
      (hC1 _ (hmem k x)).differentiableAt one_ne_zero
    show _ = varCov Γ (ρ k) (v k x) (q k x) (L k x) (B k x) (A k x)
    rw [varCov_eq hom _ _ _ _ _ _ hd]
    ext t
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply, hΦ1, hΦ2, hΦ3, hDdef,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.smul_apply, sq]
  · have e : ∀ x, normJet 0 (v₀ x) (q₀ x) = ((0 : ℝ), (v₀ x, normalize (q₀ x))) := by
      intro x; simp [normJet]
    filter_upwards [hζ0] with x hx
    have hd : DifferentiableAt ℝ Γ (normJet 0 (v₀ x) (q₀ x)) := by
      rw [e]
      exact (hC1 _ hx).differentiableAt one_ne_zero
    show _ = varCov Γ 0 (v₀ x) (q₀ x) (L₀ x) (B₀ x) (A₀ x)
    rw [varCov_eq hom _ _ _ _ _ _ hd]
    ext t
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply, hΦ1, hΦ2, hΦ3, hDdef, e,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.smul_apply, sq]

end Main

end

end RenewalGeometry.HomogeneousJetVariation
