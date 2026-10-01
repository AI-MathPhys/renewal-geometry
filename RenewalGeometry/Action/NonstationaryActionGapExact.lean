/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Action.PhysicalTestStationarityExact

/-!
# Action-gap control for nonstationary marginals
  (`prop:supp-nonstationary-action-gap`, `eq:supp-nonstationary-gap`,
  `eq:supp-nonstationary-test`; emergent-spacetime manuscript)

On the convex chart of `thm:supp-action-stationarity` (Fisher potential `Ψ` with
`m I ⪯ ∇²Ψ ⪯ M I`, common action `𝒜` with `-λG ⪯ D²𝒜 ⪯ LG`, proximal minimizer `y*_θ`,
gap `Δ_Ψ(θ,y)`; all rendered through gradients as in
`AcceptedBregmanStationarityExact.lean`), let `π` be *any* coupling on `E × E` with
source marginal `α = π ∘ fst⁻¹` and target marginal `β = π ∘ snd⁻¹`.  No invariant law is
assumed.  With `Δ̄_π = E_π Δ_Ψ` and the action drop `d_𝒜 = E_α 𝒜 - E_β 𝒜`
(`actionDrop`):

* `integral_bregmanD_le_coupling` — `E_π D_Ψ(y,θ) ≤ η (Δ̄_π + d_𝒜)`
  (`eq:supp-nonstationary-gap`, first bound);
* `integral_sq_le_coupling` — `E_π ‖y-θ‖² ≤ (2η/m)(Δ̄_π + d_𝒜)`;
* `integral_stationarity_form_le_coupling` — for any stationarity form
  `0 ≤ 𝔖 ≤ m⁻¹‖∇𝒜‖²`, `E_α 𝔖 ≤ (C₁' + C₂) Δ̄_π + C₂ d_𝒜` with the (sharper) proximal
  constant `C₁' = 4Λ_Φ/m` and `C₂ = 4M²(1+ηℓ)²/(m²η)`, and
  `integral_stationarity_form_le_coupling_paper` — the same with the displayed constant
  `C₁ = 4Λ_Φ²/(mμ_Φ)` (`eq:supp-nonstationary-gap`, second bound; `C₁' ≤ C₁` because
  `μ_Φ ≤ Λ_Φ`), and with `d_𝒜` enlarged to its positive part;
* `physical_test_nonstationary` — `eq:supp-nonstationary-test`: for a represented
  physical test lift `v` with budget `⟪v, G v⟫ ≤ B(k)²` on the positive chart Gram
  `G ⪰ m I`, `E_α |D𝒜[v(k)]|² ≤ B(k)² [(C₁ + C₂) Δ̄_π + C₂ (d_𝒜)₊]`;
* `actionDrop_eq_zero_of_marginals_eq` — equal marginals give `d_𝒜 = 0`, recovering the
  stationary estimates.

The pointwise layer (`action_bregman_le_gap`, `bregman_floor`, `grad_action_sq_le_gap`,
`inner_sq_le_of_gram_budget`) is the one of the stationary theorem; only the integration
against the coupling is new, and it retains the action difference instead of cancelling
it through stationarity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace

namespace RenewalGeometry
namespace BregmanStationarity

variable {E : Type} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ψ 𝒜 : E → ℝ} {gΨ g𝒜 : E → E}
  {η m M L lam : ℝ} {ystar : E → E}
variable {π : Measure (E × E)}

/-- The action drop `d_𝒜 = E_α 𝒜 - E_β 𝒜` between the source and target marginals of a
coupling `π`. -/
noncomputable def actionDrop (π : Measure (E × E)) (𝒜 : E → ℝ) : ℝ :=
  ∫ θ, 𝒜 θ ∂(π.map Prod.fst) - ∫ y, 𝒜 y ∂(π.map Prod.snd)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- Equal source and target marginals give a vanishing action drop. -/
theorem actionDrop_eq_zero_of_marginals_eq (π : Measure (E × E)) (𝒜 : E → ℝ)
    (h : π.map Prod.fst = π.map Prod.snd) : actionDrop π 𝒜 = 0 := by
  unfold actionDrop
  rw [h, sub_self]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
/-- The action drop as a single integral against the coupling. -/
theorem actionDrop_eq_integral (π : Measure (E × E)) (𝒜 : E → ℝ) (h𝒜c : Continuous 𝒜)
    (hi𝒜α : Integrable 𝒜 (π.map Prod.fst)) (hi𝒜β : Integrable 𝒜 (π.map Prod.snd)) :
    actionDrop π 𝒜 = ∫ p, (𝒜 p.1 - 𝒜 p.2) ∂π := by
  unfold actionDrop
  rw [integral_map measurable_fst.aemeasurable h𝒜c.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable h𝒜c.aestronglyMeasurable]
  have h1 : Integrable (fun p : E × E => 𝒜 p.1) π :=
    (integrable_map_measure h𝒜c.aestronglyMeasurable measurable_fst.aemeasurable).mp hi𝒜α
  have h2 : Integrable (fun p : E × E => 𝒜 p.2) π :=
    (integrable_map_measure h𝒜c.aestronglyMeasurable measurable_snd.aemeasurable).mp hi𝒜β
  rw [integral_sub h1 h2]

/-- Integrability of the Bregman integrand against an arbitrary coupling. -/
theorem integrable_bregmanD_coupling
    (hη : 0 < η)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ) ≤ prox Ψ 𝒜 gΨ η θ z)
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ) (hm : 0 < m)
    (hΨlo : ∀ a b : E, m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜c : Continuous 𝒜)
    (hi𝒜α : Integrable 𝒜 (π.map Prod.fst)) (hi𝒜β : Integrable 𝒜 (π.map Prod.snd))
    (higap : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2) π) :
    Integrable (fun p : E × E => bregmanD Ψ gΨ p.2 p.1) π := by
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr
    fun x => (hΨg x).differentiableAt.continuousAt
  have hDc : Continuous (fun p : E × E => bregmanD Ψ gΨ p.2 p.1) := by
    unfold bregmanD
    refine Continuous.sub (Continuous.sub ?_ ?_) ?_
    · exact hΨc.comp continuous_snd
    · exact hΨc.comp continuous_fst
    · exact Continuous.inner (hΨgc.comp continuous_fst) (continuous_snd.sub continuous_fst)
  have h1 : Integrable (fun p : E × E => 𝒜 p.1) π :=
    (integrable_map_measure h𝒜c.aestronglyMeasurable measurable_fst.aemeasurable).mp hi𝒜α
  have h2 : Integrable (fun p : E × E => 𝒜 p.2) π :=
    (integrable_map_measure h𝒜c.aestronglyMeasurable measurable_snd.aemeasurable).mp hi𝒜β
  have hb : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1 - 𝒜 p.2) π :=
    (higap.add h1).sub h2
  refine Integrable.mono' (hb.const_mul η) hDc.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun p => ?_
  have hpt := action_bregman_le_gap hmin p.1 p.2
  have hnn := bregmanD_nonneg hΨg hΨgc hm hΨlo p.1 p.2
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have h3 : η⁻¹ * bregmanD Ψ gΨ p.2 p.1 ≤ gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1 - 𝒜 p.2 := by
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hη.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hη), one_mul] at h4
  linarith

/-- **`eq:supp-nonstationary-gap`, first bound**: against any coupling `π` with source
`α` and target `β`, `E_π D_Ψ(y,θ) ≤ η (Δ̄_π + d_𝒜)`, the action difference being retained
instead of cancelled by stationarity. -/
theorem integral_bregmanD_le_coupling
    (hη : 0 < η)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ) ≤ prox Ψ 𝒜 gΨ η θ z)
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ) (hm : 0 < m)
    (hΨlo : ∀ a b : E, m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜c : Continuous 𝒜)
    (hi𝒜α : Integrable 𝒜 (π.map Prod.fst)) (hi𝒜β : Integrable 𝒜 (π.map Prod.snd))
    (higap : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2) π) :
    ∫ p, bregmanD Ψ gΨ p.2 p.1 ∂π
      ≤ η * (∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π + actionDrop π 𝒜) := by
  have h1 : Integrable (fun p : E × E => 𝒜 p.1) π :=
    (integrable_map_measure h𝒜c.aestronglyMeasurable measurable_fst.aemeasurable).mp hi𝒜α
  have h2 : Integrable (fun p : E × E => 𝒜 p.2) π :=
    (integrable_map_measure h𝒜c.aestronglyMeasurable measurable_snd.aemeasurable).mp hi𝒜β
  have hiD := integrable_bregmanD_coupling hη hmin hΨg hΨgc hm hΨlo h𝒜c hi𝒜α hi𝒜β higap
  have hpt : ∀ p : E × E,
      η⁻¹ * bregmanD Ψ gΨ p.2 p.1 ≤ gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1 - 𝒜 p.2 := by
    intro p
    have := action_bregman_le_gap hmin p.1 p.2
    linarith
  have hfg : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1) π :=
    higap.add h1
  have hb : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2 + 𝒜 p.1 - 𝒜 p.2) π :=
    hfg.sub h2
  have hint := integral_mono (hiD.const_mul η⁻¹) hb hpt
  rw [integral_sub hfg h2, integral_add higap h1, integral_const_mul] at hint
  have hdrop : actionDrop π 𝒜 = ∫ p, 𝒜 p.1 ∂π - ∫ p, 𝒜 p.2 ∂π := by
    unfold actionDrop
    rw [integral_map measurable_fst.aemeasurable h𝒜c.aestronglyMeasurable,
      integral_map measurable_snd.aemeasurable h𝒜c.aestronglyMeasurable]
  rw [hdrop]
  have h3 : η⁻¹ * ∫ p, bregmanD Ψ gΨ p.2 p.1 ∂π
      ≤ ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π + (∫ p, 𝒜 p.1 ∂π - ∫ p, 𝒜 p.2 ∂π) := by
    linarith
  calc ∫ p, bregmanD Ψ gΨ p.2 p.1 ∂π
      = η * (η⁻¹ * ∫ p, bregmanD Ψ gΨ p.2 p.1 ∂π) := by field_simp
    _ ≤ η * (∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π + (∫ p, 𝒜 p.1 ∂π - ∫ p, 𝒜 p.2 ∂π)) :=
        mul_le_mul_of_nonneg_left h3 hη.le

/-- Integrability of the squared displacement against the coupling. -/
theorem integrable_sq_coupling
    (hη : 0 < η)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ) ≤ prox Ψ 𝒜 gΨ η θ z)
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ) (hm : 0 < m)
    (hΨlo : ∀ a b : E, m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜c : Continuous 𝒜)
    (hi𝒜α : Integrable 𝒜 (π.map Prod.fst)) (hi𝒜β : Integrable 𝒜 (π.map Prod.snd))
    (higap : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2) π) :
    Integrable (fun p : E × E => ‖p.2 - p.1‖ ^ 2) π := by
  have hiD := integrable_bregmanD_coupling hη hmin hΨg hΨgc hm hΨlo h𝒜c hi𝒜α hi𝒜β higap
  refine Integrable.mono' (hiD.const_mul (2 / m)) ?_ ?_
  · exact (Continuous.pow ((continuous_snd.sub continuous_fst).norm) 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := bregman_floor Ψ gΨ hΨg hΨgc m hΨlo p.1 (p.2 - p.1)
    rw [show p.1 + (p.2 - p.1) = p.2 from by abel] at h
    have h2 : m / 2 * ‖p.2 - p.1‖ ^ 2 ≤ bregmanD Ψ gΨ p.2 p.1 := h
    calc ‖p.2 - p.1‖ ^ 2 = 2 / m * (m / 2 * ‖p.2 - p.1‖ ^ 2) := by field_simp
      _ ≤ 2 / m * bregmanD Ψ gΨ p.2 p.1 := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The displacement bound against the coupling:
`E_π ‖y-θ‖² ≤ (2η/m)(Δ̄_π + d_𝒜)`. -/
theorem integral_sq_le_coupling
    (hη : 0 < η)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ) ≤ prox Ψ 𝒜 gΨ η θ z)
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ) (hm : 0 < m)
    (hΨlo : ∀ a b : E, m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜c : Continuous 𝒜)
    (hi𝒜α : Integrable 𝒜 (π.map Prod.fst)) (hi𝒜β : Integrable 𝒜 (π.map Prod.snd))
    (higap : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2) π) :
    ∫ p, ‖p.2 - p.1‖ ^ 2 ∂π
      ≤ 2 * η / m * (∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π + actionDrop π 𝒜) := by
  have hiD := integrable_bregmanD_coupling hη hmin hΨg hΨgc hm hΨlo h𝒜c hi𝒜α hi𝒜β higap
  have hisq := integrable_sq_coupling hη hmin hΨg hΨgc hm hΨlo h𝒜c hi𝒜α hi𝒜β higap
  have hpt : ∀ p : E × E, ‖p.2 - p.1‖ ^ 2 ≤ 2 / m * bregmanD Ψ gΨ p.2 p.1 := by
    intro p
    have h := bregman_floor Ψ gΨ hΨg hΨgc m hΨlo p.1 (p.2 - p.1)
    rw [show p.1 + (p.2 - p.1) = p.2 from by abel] at h
    calc ‖p.2 - p.1‖ ^ 2 = 2 / m * (m / 2 * ‖p.2 - p.1‖ ^ 2) := by field_simp
      _ ≤ 2 / m * bregmanD Ψ gΨ p.2 p.1 := mul_le_mul_of_nonneg_left h (by positivity)
  have hint := integral_mono hisq (hiD.const_mul (2 / m)) hpt
  rw [integral_const_mul] at hint
  have hD := integral_bregmanD_le_coupling hη hmin hΨg hΨgc hm hΨlo h𝒜c hi𝒜α hi𝒜β higap
  calc ∫ p, ‖p.2 - p.1‖ ^ 2 ∂π
      ≤ 2 / m * ∫ p, bregmanD Ψ gΨ p.2 p.1 ∂π := hint
    _ ≤ 2 / m * (η * (∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π + actionDrop π 𝒜)) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = 2 * η / m * (∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π + actionDrop π 𝒜) := by ring

/-- Integrability of the squared action gradient at the source against the coupling. -/
theorem integrable_grad_action_sq_coupling
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hm : 0 < m) (hM : 0 < M) (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hΨlo : ∀ a b : E, m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hΨup : ∀ a b : E, ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫ ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜lip : ∀ a b : E, ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ) ≤ prox Ψ 𝒜 gΨ η θ z)
    (hi𝒜α : Integrable 𝒜 (π.map Prod.fst)) (hi𝒜β : Integrable 𝒜 (π.map Prod.snd))
    (higap : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2) π) :
    Integrable (fun p : E × E => ‖g𝒜 p.1‖ ^ 2) π := by
  have h𝒜c : Continuous 𝒜 := continuous_iff_continuousAt.mpr
    fun x => (h𝒜g x).differentiableAt.continuousAt
  have hΨlo0 : ∀ a b : E, 0 ≤ ⟪gΨ a - gΨ b, a - b⟫ := fun a b =>
    le_trans (by positivity) (hΨlo a b)
  have hisq := integrable_sq_coupling hη hmin hΨg hΨgc hm hΨlo h𝒜c hi𝒜α hi𝒜β higap
  have hsum : Integrable (fun p : E × E =>
      2 * η ^ 2 * ((η⁻¹ + L) * M) * gap Ψ 𝒜 gΨ η ystar p.1 p.2
      + (1 + η * max lam L) ^ 2 * M ^ 2 * ‖p.2 - p.1‖ ^ 2) π :=
    (higap.const_mul _).add (hisq.const_mul _)
  refine Integrable.mono' (hsum.const_mul (2 * η⁻¹ ^ 2)) ?_ ?_
  · exact (((h𝒜gc.comp continuous_fst).norm).pow 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact grad_action_sq_le_gap hΨg hΨgc h𝒜g h𝒜gc hη hM hL hlam hΨup hΨlo0 hΨlip h𝒜up
      h𝒜lip hmin p

/-- **`eq:supp-nonstationary-gap`, second bound** (sharp proximal constant): for any
stationarity form `0 ≤ 𝔖 ≤ m⁻¹‖∇𝒜‖²` on the source marginal `α`,
`E_α 𝔖 ≤ (4Λ_Φ/m + C₂) Δ̄_π + C₂ d_𝒜`, `Λ_Φ = (η⁻¹+L)M`, `C₂ = 4M²(1+ηℓ)²/(m²η)`. -/
theorem integral_stationarity_form_le_coupling
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hm : 0 < m) (hM : 0 < M) (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hΨlo : ∀ a b : E, m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hΨup : ∀ a b : E, ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫ ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜lip : ∀ a b : E, ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ) ≤ prox Ψ 𝒜 gΨ η θ z)
    (hi𝒜α : Integrable 𝒜 (π.map Prod.fst)) (hi𝒜β : Integrable 𝒜 (π.map Prod.snd))
    (higap : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2) π)
    (S : E → ℝ) (hS0 : ∀ θ, 0 ≤ S θ) (hSle : ∀ θ, S θ ≤ m⁻¹ * ‖g𝒜 θ‖ ^ 2)
    (hSm : AEStronglyMeasurable S (π.map Prod.fst)) :
    ∫ θ, S θ ∂(π.map Prod.fst)
      ≤ (4 * ((η⁻¹ + L) * M) / m + 4 * M ^ 2 * (1 + η * max lam L) ^ 2 / (m ^ 2 * η))
          * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π
        + 4 * M ^ 2 * (1 + η * max lam L) ^ 2 / (m ^ 2 * η) * actionDrop π 𝒜 := by
  have h𝒜c : Continuous 𝒜 := continuous_iff_continuousAt.mpr
    fun x => (h𝒜g x).differentiableAt.continuousAt
  have hΨlo0 : ∀ a b : E, 0 ≤ ⟪gΨ a - gΨ b, a - b⟫ := fun a b =>
    le_trans (by positivity) (hΨlo a b)
  have hig𝒜π := integrable_grad_action_sq_coupling hΨg hΨgc h𝒜g h𝒜gc hη hm hM hL hlam hΨlo
    hΨup hΨlip h𝒜up h𝒜lip hmin hi𝒜α hi𝒜β higap
  have hg2m : AEStronglyMeasurable (fun θ => ‖g𝒜 θ‖ ^ 2) (π.map Prod.fst) :=
    (((h𝒜gc.norm).pow 2).aestronglyMeasurable)
  have hig𝒜α : Integrable (fun θ => ‖g𝒜 θ‖ ^ 2) (π.map Prod.fst) :=
    (integrable_map_measure hg2m measurable_fst.aemeasurable).mpr hig𝒜π
  have hiS : Integrable S (π.map Prod.fst) := by
    refine Integrable.mono' (hig𝒜α.const_mul m⁻¹) hSm ?_
    refine Filter.Eventually.of_forall fun θ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 θ)]
    exact hSle θ
  have hstep1 := integral_mono hiS (hig𝒜α.const_mul m⁻¹) hSle
  rw [integral_const_mul] at hstep1
  have hstep2 : ∫ θ, ‖g𝒜 θ‖ ^ 2 ∂(π.map Prod.fst) = ∫ p, ‖g𝒜 p.1‖ ^ 2 ∂π :=
    integral_map measurable_fst.aemeasurable hg2m
  have h1 : Integrable (fun p : E × E =>
      2 * η ^ 2 * ((η⁻¹ + L) * M) * gap Ψ 𝒜 gΨ η ystar p.1 p.2) π :=
    higap.const_mul _
  have hisq := integrable_sq_coupling hη hmin hΨg hΨgc hm hΨlo h𝒜c hi𝒜α hi𝒜β higap
  have h2 : Integrable (fun p : E × E =>
      (1 + η * max lam L) ^ 2 * M ^ 2 * ‖p.2 - p.1‖ ^ 2) π :=
    hisq.const_mul _
  have hsum : Integrable (fun p : E × E =>
      2 * η ^ 2 * ((η⁻¹ + L) * M) * gap Ψ 𝒜 gΨ η ystar p.1 p.2
      + (1 + η * max lam L) ^ 2 * M ^ 2 * ‖p.2 - p.1‖ ^ 2) π := h1.add h2
  have hstep3 := integral_mono hig𝒜π (hsum.const_mul (2 * η⁻¹ ^ 2))
    (fun p => grad_action_sq_le_gap hΨg hΨgc h𝒜g h𝒜gc hη hM hL hlam hΨup hΨlo0 hΨlip h𝒜up
      h𝒜lip hmin p)
  rw [integral_const_mul, integral_add h1 h2, integral_const_mul, integral_const_mul] at hstep3
  have hstep4 := integral_sq_le_coupling hη hmin hΨg hΨgc hm hΨlo h𝒜c hi𝒜α hi𝒜β higap
  set Δ := ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π with hΔ
  set d := actionDrop π 𝒜 with hd
  have hins : ∫ p, ‖g𝒜 p.1‖ ^ 2 ∂π
      ≤ 2 * η⁻¹ ^ 2 * (2 * η ^ 2 * ((η⁻¹ + L) * M) * Δ
          + (1 + η * max lam L) ^ 2 * M ^ 2 * (2 * η / m * (Δ + d))) := by
    have hmono := mul_le_mul_of_nonneg_left hstep4
      (by positivity : (0:ℝ) ≤ (1 + η * max lam L) ^ 2 * M ^ 2)
    have h5 : (0:ℝ) ≤ 2 * η⁻¹ ^ 2 := by positivity
    nlinarith [hstep3, hmono]
  have hchain : ∫ θ, S θ ∂(π.map Prod.fst)
      ≤ m⁻¹ * (2 * η⁻¹ ^ 2 * (2 * η ^ 2 * ((η⁻¹ + L) * M) * Δ
          + (1 + η * max lam L) ^ 2 * M ^ 2 * (2 * η / m * (Δ + d)))) := by
    calc ∫ θ, S θ ∂(π.map Prod.fst)
        ≤ m⁻¹ * ∫ θ, ‖g𝒜 θ‖ ^ 2 ∂(π.map Prod.fst) := hstep1
      _ = m⁻¹ * ∫ p, ‖g𝒜 p.1‖ ^ 2 ∂π := by rw [hstep2]
      _ ≤ _ := mul_le_mul_of_nonneg_left hins (by positivity)
  have hconst : m⁻¹ * (2 * η⁻¹ ^ 2 * (2 * η ^ 2 * ((η⁻¹ + L) * M) * Δ
          + (1 + η * max lam L) ^ 2 * M ^ 2 * (2 * η / m * (Δ + d))))
      = (4 * ((η⁻¹ + L) * M) / m + 4 * M ^ 2 * (1 + η * max lam L) ^ 2 / (m ^ 2 * η)) * Δ
        + 4 * M ^ 2 * (1 + η * max lam L) ^ 2 / (m ^ 2 * η) * d := by
    field_simp
    ring
  linarith [hchain, hconst]

/-- The sharp proximal constant `4Λ_Φ/m` is dominated by the displayed constant
`C₁ = 4Λ_Φ²/(mμ_Φ)`, since `μ_Φ = (η⁻¹-λ)m ≤ (η⁻¹+L)M = Λ_Φ` when `m ≤ M`. -/
theorem proximal_constant_le_paper (hη : 0 < η) (hm : 0 < m) (hM : 0 < M) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam) (hmM : m ≤ M) (hμ : 0 < (η⁻¹ - lam) * m) :
    4 * ((η⁻¹ + L) * M) / m ≤ 4 * ((η⁻¹ + L) * M) ^ 2 / (m * ((η⁻¹ - lam) * m)) := by
  have hΛ : 0 < (η⁻¹ + L) * M := by positivity
  have hμΛ : (η⁻¹ - lam) * m ≤ (η⁻¹ + L) * M := by
    have h1 : (η⁻¹ - lam) * m ≤ η⁻¹ * m := by nlinarith
    have h2 : η⁻¹ * m ≤ η⁻¹ * M := by
      exact mul_le_mul_of_nonneg_left hmM (by positivity)
    have h3 : η⁻¹ * M ≤ (η⁻¹ + L) * M := by nlinarith
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : 0 ≤ 4 * ((η⁻¹ + L) * M) * m := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hμΛ h4]

/-- **`eq:supp-nonstationary-gap`, second bound, displayed constants**:
`E_α 𝔖 ≤ (C₁ + C₂) Δ̄_π + C₂ (d_𝒜)₊` with `C₁ = 4Λ_Φ²/(mμ_Φ)`, `C₂ = 4M²(1+ηℓ)²/(m²η)`,
`μ_Φ = (η⁻¹-λ)m > 0` (the interiority/convexity constant of
`eq:supp-action-constants`); the action drop is enlarged to its positive part. -/
theorem integral_stationarity_form_le_coupling_paper
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hm : 0 < m) (hM : 0 < M) (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hmM : m ≤ M) (hμ : 0 < (η⁻¹ - lam) * m)
    (hΨlo : ∀ a b : E, m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hΨup : ∀ a b : E, ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫ ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜lip : ∀ a b : E, ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ) ≤ prox Ψ 𝒜 gΨ η θ z)
    (hi𝒜α : Integrable 𝒜 (π.map Prod.fst)) (hi𝒜β : Integrable 𝒜 (π.map Prod.snd))
    (higap : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2) π)
    (S : E → ℝ) (hS0 : ∀ θ, 0 ≤ S θ) (hSle : ∀ θ, S θ ≤ m⁻¹ * ‖g𝒜 θ‖ ^ 2)
    (hSm : AEStronglyMeasurable S (π.map Prod.fst)) :
    ∫ θ, S θ ∂(π.map Prod.fst)
      ≤ (4 * ((η⁻¹ + L) * M) ^ 2 / (m * ((η⁻¹ - lam) * m))
            + 4 * M ^ 2 * (1 + η * max lam L) ^ 2 / (m ^ 2 * η))
          * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π
        + 4 * M ^ 2 * (1 + η * max lam L) ^ 2 / (m ^ 2 * η) * max (actionDrop π 𝒜) 0 := by
  have hbase := integral_stationarity_form_le_coupling hΨg hΨgc h𝒜g h𝒜gc hη hm hM hL hlam
    hΨlo hΨup hΨlip h𝒜up h𝒜lip hmin hi𝒜α hi𝒜β higap S hS0 hSle hSm
  have hΔ : 0 ≤ ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π :=
    integral_nonneg fun p => gap_nonneg hmin p.1 p.2
  have hC1 := proximal_constant_le_paper hη hm hM hL hlam hmM hμ
  have hC2 : 0 ≤ 4 * M ^ 2 * (1 + η * max lam L) ^ 2 / (m ^ 2 * η) := by positivity
  have hpos : actionDrop π 𝒜 ≤ max (actionDrop π 𝒜) 0 := le_max_left _ _
  nlinarith [mul_le_mul_of_nonneg_right hC1 hΔ, mul_le_mul_of_nonneg_left hpos hC2]

/-- **`eq:supp-nonstationary-test`**: for a represented physical test lift `v` with
budget `⟪v θ, G θ (v θ)⟫ ≤ b = B(k)²` on the positive chart Gram `G ⪰ m I`, the mean
square of the represented first variation `D𝒜[v(k)] = ⟪∇𝒜 θ, v θ⟫` under the source
marginal is bounded by `B(k)² [(C₁ + C₂) Δ̄_π + C₂ (d_𝒜)₊]`.  No invariant law is
required. -/
theorem physical_test_nonstationary
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hm : 0 < m) (hM : 0 < M) (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hmM : m ≤ M) (hμ : 0 < (η⁻¹ - lam) * m)
    (hΨlo : ∀ a b : E, m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hΨup : ∀ a b : E, ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫ ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜lip : ∀ a b : E, ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ) ≤ prox Ψ 𝒜 gΨ η θ z)
    (hi𝒜α : Integrable 𝒜 (π.map Prod.fst)) (hi𝒜β : Integrable 𝒜 (π.map Prod.snd))
    (higap : Integrable (fun p : E × E => gap Ψ 𝒜 gΨ η ystar p.1 p.2) π)
    -- the positive chart Gram `G_X(θ) ⪰ m I`
    (G : E → E →L[ℝ] E) (hG : ∀ θ x, m * ‖x‖ ^ 2 ≤ ⟪x, G θ x⟫)
    -- the represented test lift and its budget `B(k)² = b`
    (v : E → E) (hv : AEStronglyMeasurable (fun θ => ⟪g𝒜 θ, v θ⟫) (π.map Prod.fst))
    {b : ℝ} (hb : 0 < b) (hbudget : ∀ θ, ⟪v θ, G θ (v θ)⟫ ≤ b) :
    ∫ θ, ⟪g𝒜 θ, v θ⟫ ^ 2 ∂(π.map Prod.fst)
      ≤ b * ((4 * ((η⁻¹ + L) * M) ^ 2 / (m * ((η⁻¹ - lam) * m))
            + 4 * M ^ 2 * (1 + η * max lam L) ^ 2 / (m ^ 2 * η))
          * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2 ∂π
        + 4 * M ^ 2 * (1 + η * max lam L) ^ 2 / (m ^ 2 * η) * max (actionDrop π 𝒜) 0) := by
  set S : E → ℝ := fun θ => b⁻¹ * ⟪g𝒜 θ, v θ⟫ ^ 2 with hS
  have hS0 : ∀ θ, 0 ≤ S θ := fun θ => by
    simp only [hS]; positivity
  have hSle : ∀ θ, S θ ≤ m⁻¹ * ‖g𝒜 θ‖ ^ 2 := by
    intro θ
    simp only [hS]
    have h := inner_sq_le_of_gram_budget hm (G θ) (hG θ) (g𝒜 θ) (v θ) (hbudget θ)
    calc b⁻¹ * ⟪g𝒜 θ, v θ⟫ ^ 2 ≤ b⁻¹ * (m⁻¹ * ‖g𝒜 θ‖ ^ 2 * b) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hb.le)
      _ = m⁻¹ * ‖g𝒜 θ‖ ^ 2 := by field_simp
  have hSm : AEStronglyMeasurable S (π.map Prod.fst) :=
    ((hv.aemeasurable.pow_const 2).const_mul b⁻¹).aestronglyMeasurable
  have hbase := integral_stationarity_form_le_coupling_paper hΨg hΨgc h𝒜g h𝒜gc hη hm hM hL
    hlam hmM hμ hΨlo hΨup hΨlip h𝒜up h𝒜lip hmin hi𝒜α hi𝒜β higap S hS0 hSle hSm
  have hint : ∫ θ, ⟪g𝒜 θ, v θ⟫ ^ 2 ∂(π.map Prod.fst) = b * ∫ θ, S θ ∂(π.map Prod.fst) := by
    rw [← integral_const_mul]
    congr 1
    funext θ
    simp only [hS]
    field_simp
  rw [hint]
  exact mul_le_mul_of_nonneg_left hbase hb.le

end BregmanStationarity
end RenewalGeometry
