/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMVariationLipschitz

/-!
# First-variation Lipschitz estimates: uniform coefficient-term bounds, bosonic and Dirac sectors
  (`prop:variation-continuity`, Einstein–Standard-Model action-closure manuscript)

Continuation of `EinsteinSMVariationLipschitz.lean` (gravitational sector).

## Uniform coefficient terms

`coeff1_lip`, `coeff2_lip`, `coeff3_lip`: for a `C¹` coefficient map `Ψ` on the chart `coframeGL`
(linear, bilinear, trilinear in the packets) and a compact chart set `Ke`, there is one constant `K`
such that for all coframe fields with values a.e. in `Ke` and all packets bounded by `B`,
`‖Ψ(e₁)(X₁,…) - Ψ(e₂)(X₂,…)‖_{L¹} ≤ K·D` whenever `D` dominates `‖e₁-e₂‖_∞` and the packet
differences (`L¹` for linear, `L²×L²` for bilinear, `L²×L⁴×L⁴` for trilinear terms), and
`‖Ψ(e₂)(X₂,…)‖_{L¹} ≤ K`.

`bil_const_22`, `bil_const_44`: constant bilinear maps, Hölder `(2,2) → 1` and `(4,4) → 2`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace VarLip

/-! ### `L^p` comparison on finite measure spaces -/

section Compare

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem rpow_le_max_one {a : ℝ≥0∞} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : a ^ t ≤ max 1 a := by
  rcases le_total a 1 with ha | ha
  · exact (ENNReal.rpow_le_one ha h0).trans (le_max_left _ _)
  · calc a ^ t ≤ a ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le ha h1
      _ = a := ENNReal.rpow_one a
      _ ≤ _ := le_max_right _ _

/-- `‖f‖_p ≤ max(1, μ(X)) ‖f‖_q` for `p ≤ q` with `0 ≤ 1/p - 1/q ≤ 1`. -/
theorem eLpNorm_le_cmax [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] {f : X → E}
    (hf : AEStronglyMeasurable f μ) {p q : ℝ≥0∞} (hpq : p ≤ q)
    (h0 : 0 ≤ 1 / p.toReal - 1 / q.toReal) (h1 : 1 / p.toReal - 1 / q.toReal ≤ 1) :
    eLpNorm f p μ ≤ max 1 (μ univ) * eLpNorm f q μ := by
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf).trans ?_
  rw [mul_comm]
  gcongr
  exact rpow_le_max_one h0 h1

theorem eLpNorm_le_cmax_12 [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] {f : X → E}
    (hf : AEStronglyMeasurable f μ) : eLpNorm f 1 μ ≤ max 1 (μ univ) * eLpNorm f 2 μ :=
  eLpNorm_le_cmax hf (by norm_num) (by norm_num) (by norm_num)

theorem eLpNorm_le_cmax_24 [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] {f : X → E}
    (hf : AEStronglyMeasurable f μ) : eLpNorm f 2 μ ≤ max 1 (μ univ) * eLpNorm f 4 μ :=
  eLpNorm_le_cmax hf (by norm_num) (by norm_num) (by norm_num)

theorem eLpNorm_le_cmax_14 [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] {f : X → E}
    (hf : AEStronglyMeasurable f μ) : eLpNorm f 1 μ ≤ max 1 (μ univ) * eLpNorm f 4 μ :=
  eLpNorm_le_cmax hf (by norm_num) (by norm_num) (by norm_num)

theorem eLpNorm_le_cmax_2top [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] {f : X → E}
    (hf : AEStronglyMeasurable f μ) : eLpNorm f 2 μ ≤ max 1 (μ univ) * eLpNorm f ⊤ μ :=
  eLpNorm_le_cmax hf le_top (by norm_num) (by norm_num)

theorem eLpNorm_const_le_cmax [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] (c : E) :
    eLpNorm (fun _ : X => c) 2 μ ≤ max 1 (μ univ) * ENNReal.ofReal ‖c‖ :=
  (eLpNorm_le_cmax_2top aestronglyMeasurable_const).trans
    (by gcongr; exact eLpNorm_top_le_of_ae (Eventually.of_forall fun _ => le_rfl))

theorem one_le_cmax : (1 : ℝ≥0∞) ≤ max 1 (μ univ) := le_max_left _ _

theorem cmax_ne_top [IsFiniteMeasure μ] : max 1 (μ univ) ≠ ⊤ :=
  max_ne_top ENNReal.one_ne_top (measure_ne_top _ _)

end Compare

/-! ### Uniform coefficient terms -/

section UniformCoeff

variable {V W U Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

theorem aesm_coeff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F] {Ψ : CoframeFibre → F} (hΨ : ContinuousOn Ψ coframeGL)
    {Ke : Set CoframeFibre} (hsub : Ke ⊆ coframeGL) {μ : Measure E4} {e : E4 → CoframeFibre}
    (he : AEStronglyMeasurable e μ) (hK : ∀ᵐ x ∂μ, e x ∈ Ke) :
    AEStronglyMeasurable (fun x => Ψ (e x)) μ := by
  borelize F
  exact aestronglyMeasurable_comp_of_continuousOn isOpen_coframeGL hΨ he.aemeasurable
    (hK.mono fun _ hx => hsub hx)

/-- **Uniform linear coefficient terms** (packets in `L¹`). -/
theorem coeff1_lip [SecondCountableTopology (V →L[ℝ] Z)] {Ψ : CoframeFibre → V →L[ℝ] Z}
    (hΨ : ContDiffOn ℝ 1 Ψ coframeGL) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hsub : Ke ⊆ coframeGL) {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (μ : Measure E4) (e₁ e₂ : E4 → CoframeFibre) (X₁ X₂ : E4 → V)
      (D : ℝ≥0∞), AEStronglyMeasurable e₁ μ → AEStronglyMeasurable e₂ μ →
      (∀ᵐ x ∂μ, e₁ x ∈ Ke) → (∀ᵐ x ∂μ, e₂ x ∈ Ke) →
      AEStronglyMeasurable X₁ μ → AEStronglyMeasurable X₂ μ →
      eLpNorm X₁ 1 μ ≤ B → eLpNorm X₂ 1 μ ≤ B →
      eLpNorm (fun x => e₁ x - e₂ x) ⊤ μ ≤ D → eLpNorm (fun x => X₁ x - X₂ x) 1 μ ≤ D →
      eLpNorm (fun x => Ψ (e₁ x) (X₁ x) - Ψ (e₂ x) (X₂ x)) 1 μ ≤ K * D ∧
        eLpNorm (fun x => Ψ (e₂ x) (X₂ x)) 1 μ ≤ K := by
  obtain ⟨L, M, hL, hM, hb, hl⟩ := exists_lipschitz_bound hΨ hKe hsub
  refine ⟨ENNReal.ofReal L * B + ENNReal.ofReal M * 1 + ENNReal.ofReal M * B, by finiteness, ?_⟩
  intro μ e₁ e₂ X₁ X₂ D he₁ he₂ hK₁ hK₂ hX₁ hX₂ hb₁ hb₂ hDe hDX
  have cf := coeff_field hL hb hl hK₁ hK₂
  have m₁ : AEStronglyMeasurable (fun x => Ψ (e₁ x)) μ := aesm_coeff hΨ.continuousOn hsub he₁ hK₁
  have m₂ : AEStronglyMeasurable (fun x => Ψ (e₂ x)) μ := aesm_coeff hΨ.continuousOn hsub he₂ hK₂
  have hΔ : eLpNorm (fun x => Ψ (e₁ x) - Ψ (e₂ x)) ⊤ μ ≤ ENNReal.ofReal L * D :=
    cf.1.trans (by gcongr)
  have hDX' : eLpNorm (fun x => X₁ x - X₂ x) 1 μ ≤ 1 * D := by rwa [one_mul]
  constructor
  · refine (term1_bound (Φ₁ := fun x => Ψ (e₁ x)) (Φ₂ := fun x => Ψ (e₂ x)) m₁ m₂ hX₁ hX₂ hΔ
      cf.2 hb₁ hDX').trans ?_
    gcongr ?_ * _
    exact le_self_add
  · refine (eLpNorm_apply1_le (Φ := fun x => Ψ (e₂ x)) m₂ hX₂ 1).trans ?_
    calc eLpNorm (fun x => Ψ (e₂ x)) ⊤ μ * eLpNorm X₂ 1 μ ≤ ENNReal.ofReal M * B := by
          gcongr; exact cf.2
      _ ≤ _ := le_add_self

/-- **Uniform bilinear coefficient terms** (packets in `L² × L²`). -/
theorem coeff2_lip [SecondCountableTopology (V →L[ℝ] W →L[ℝ] Z)]
    {Ψ : CoframeFibre → V →L[ℝ] W →L[ℝ] Z}
    (hΨ : ContDiffOn ℝ 1 Ψ coframeGL) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hsub : Ke ⊆ coframeGL) {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (μ : Measure E4) (e₁ e₂ : E4 → CoframeFibre) (X₁ X₂ : E4 → V)
      (Y₁ Y₂ : E4 → W) (D : ℝ≥0∞), AEStronglyMeasurable e₁ μ → AEStronglyMeasurable e₂ μ →
      (∀ᵐ x ∂μ, e₁ x ∈ Ke) → (∀ᵐ x ∂μ, e₂ x ∈ Ke) →
      AEStronglyMeasurable X₁ μ → AEStronglyMeasurable X₂ μ →
      AEStronglyMeasurable Y₁ μ → AEStronglyMeasurable Y₂ μ →
      eLpNorm X₁ 2 μ ≤ B → eLpNorm X₂ 2 μ ≤ B → eLpNorm Y₁ 2 μ ≤ B → eLpNorm Y₂ 2 μ ≤ B →
      eLpNorm (fun x => e₁ x - e₂ x) ⊤ μ ≤ D → eLpNorm (fun x => X₁ x - X₂ x) 2 μ ≤ D →
      eLpNorm (fun x => Y₁ x - Y₂ x) 2 μ ≤ D →
      eLpNorm (fun x => Ψ (e₁ x) (X₁ x) (Y₁ x) - Ψ (e₂ x) (X₂ x) (Y₂ x)) 1 μ ≤ K * D ∧
        eLpNorm (fun x => Ψ (e₂ x) (X₂ x) (Y₂ x)) 1 μ ≤ K := by
  obtain ⟨L, M, hL, hM, hb, hl⟩ := exists_lipschitz_bound hΨ hKe hsub
  refine ⟨ENNReal.ofReal L * (B * B) + ENNReal.ofReal M * (1 * B) + ENNReal.ofReal M * (B * 1) +
    ENNReal.ofReal M * (B * B), by finiteness, ?_⟩
  intro μ e₁ e₂ X₁ X₂ Y₁ Y₂ D he₁ he₂ hK₁ hK₂ hX₁ hX₂ hY₁ hY₂ hbX₁ hbX₂ hbY₁ hbY₂ hDe hDX hDY
  have cf := coeff_field hL hb hl hK₁ hK₂
  have m₁ : AEStronglyMeasurable (fun x => Ψ (e₁ x)) μ := aesm_coeff hΨ.continuousOn hsub he₁ hK₁
  have m₂ : AEStronglyMeasurable (fun x => Ψ (e₂ x)) μ := aesm_coeff hΨ.continuousOn hsub he₂ hK₂
  have hΔ : eLpNorm (fun x => Ψ (e₁ x) - Ψ (e₂ x)) ⊤ μ ≤ ENNReal.ofReal L * D :=
    cf.1.trans (by gcongr)
  have hDX' : eLpNorm (fun x => X₁ x - X₂ x) 2 μ ≤ 1 * D := by rwa [one_mul]
  have hDY' : eLpNorm (fun x => Y₁ x - Y₂ x) 2 μ ≤ 1 * D := by rwa [one_mul]
  constructor
  · refine (term2_bound (Φ₁ := fun x => Ψ (e₁ x)) (Φ₂ := fun x => Ψ (e₂ x)) m₁ m₂ hX₁ hX₂ hY₁ hY₂
      hΔ cf.2 hbX₁ hbX₂ hbY₁ hDX' hDY').trans ?_
    gcongr ?_ * _
    exact le_self_add
  · refine (eLpNorm_apply2_le (Φ := fun x => Ψ (e₂ x)) m₂ hX₂ hY₂).trans ?_
    calc eLpNorm (fun x => Ψ (e₂ x)) ⊤ μ * (eLpNorm X₂ 2 μ * eLpNorm Y₂ 2 μ) ≤
          ENNReal.ofReal M * (B * B) := by gcongr; exact cf.2
      _ ≤ _ := le_add_self

/-- **Uniform trilinear coefficient terms** (packets in `L² × L⁴ × L⁴`). -/
theorem coeff3_lip [SecondCountableTopology (V →L[ℝ] W →L[ℝ] U →L[ℝ] Z)]
    {Ψ : CoframeFibre → V →L[ℝ] W →L[ℝ] U →L[ℝ] Z}
    (hΨ : ContDiffOn ℝ 1 Ψ coframeGL) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hsub : Ke ⊆ coframeGL) {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (μ : Measure E4) (e₁ e₂ : E4 → CoframeFibre) (X₁ X₂ : E4 → V)
      (Y₁ Y₂ : E4 → W) (W₁ W₂ : E4 → U) (D : ℝ≥0∞),
      AEStronglyMeasurable e₁ μ → AEStronglyMeasurable e₂ μ →
      (∀ᵐ x ∂μ, e₁ x ∈ Ke) → (∀ᵐ x ∂μ, e₂ x ∈ Ke) →
      AEStronglyMeasurable X₁ μ → AEStronglyMeasurable X₂ μ →
      AEStronglyMeasurable Y₁ μ → AEStronglyMeasurable Y₂ μ →
      AEStronglyMeasurable W₁ μ → AEStronglyMeasurable W₂ μ →
      eLpNorm X₁ 2 μ ≤ B → eLpNorm X₂ 2 μ ≤ B → eLpNorm Y₁ 4 μ ≤ B → eLpNorm Y₂ 4 μ ≤ B →
      eLpNorm W₁ 4 μ ≤ B → eLpNorm W₂ 4 μ ≤ B →
      eLpNorm (fun x => e₁ x - e₂ x) ⊤ μ ≤ D → eLpNorm (fun x => X₁ x - X₂ x) 2 μ ≤ D →
      eLpNorm (fun x => Y₁ x - Y₂ x) 4 μ ≤ D → eLpNorm (fun x => W₁ x - W₂ x) 4 μ ≤ D →
      eLpNorm (fun x => Ψ (e₁ x) (X₁ x) (Y₁ x) (W₁ x) - Ψ (e₂ x) (X₂ x) (Y₂ x) (W₂ x)) 1 μ ≤
          K * D ∧
        eLpNorm (fun x => Ψ (e₂ x) (X₂ x) (Y₂ x) (W₂ x)) 1 μ ≤ K := by
  obtain ⟨L, M, hL, hM, hb, hl⟩ := exists_lipschitz_bound hΨ hKe hsub
  refine ⟨ENNReal.ofReal L * (B * (B * B)) + ENNReal.ofReal M * (1 * (B * B)) +
    ENNReal.ofReal M * (B * (1 * B)) + ENNReal.ofReal M * (B * (B * 1)) +
    ENNReal.ofReal M * (B * (B * B)), by finiteness, ?_⟩
  intro μ e₁ e₂ X₁ X₂ Y₁ Y₂ W₁ W₂ D he₁ he₂ hK₁ hK₂ hX₁ hX₂ hY₁ hY₂ hW₁ hW₂ hbX₁ hbX₂ hbY₁ hbY₂
    hbW₁ hbW₂ hDe hDX hDY hDW
  have cf := coeff_field hL hb hl hK₁ hK₂
  have m₁ : AEStronglyMeasurable (fun x => Ψ (e₁ x)) μ := aesm_coeff hΨ.continuousOn hsub he₁ hK₁
  have m₂ : AEStronglyMeasurable (fun x => Ψ (e₂ x)) μ := aesm_coeff hΨ.continuousOn hsub he₂ hK₂
  have hΔ : eLpNorm (fun x => Ψ (e₁ x) - Ψ (e₂ x)) ⊤ μ ≤ ENNReal.ofReal L * D :=
    cf.1.trans (by gcongr)
  have hDX' : eLpNorm (fun x => X₁ x - X₂ x) 2 μ ≤ 1 * D := by rwa [one_mul]
  have hDY' : eLpNorm (fun x => Y₁ x - Y₂ x) 4 μ ≤ 1 * D := by rwa [one_mul]
  have hDW' : eLpNorm (fun x => W₁ x - W₂ x) 4 μ ≤ 1 * D := by rwa [one_mul]
  constructor
  · refine (term3_bound (Φ₁ := fun x => Ψ (e₁ x)) (Φ₂ := fun x => Ψ (e₂ x)) m₁ m₂ hX₁ hX₂ hY₁ hY₂
      hW₁ hW₂ hΔ cf.2 hbX₁ hbX₂ hbY₁ hbY₂ hbW₁ hDX' hDY' hDW').trans ?_
    gcongr ?_ * _
    exact le_self_add
  · refine (eLpNorm_apply3_le (Φ := fun x => Ψ (e₂ x)) m₂ hX₂ hY₂ hW₂).trans ?_
    calc eLpNorm (fun x => Ψ (e₂ x)) ⊤ μ * (eLpNorm X₂ 2 μ * (eLpNorm Y₂ 4 μ * eLpNorm W₂ 4 μ)) ≤
          ENNReal.ofReal M * (B * (B * B)) := by gcongr; exact cf.2
      _ ≤ _ := le_add_self

end UniformCoeff

/-! ### Constant bilinear maps -/

section ConstBil

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem eLpNorm_const_clm_le (b : V →L[ℝ] W →L[ℝ] Z) :
    eLpNorm (fun _ : X => b) ⊤ μ ≤ ENNReal.ofReal ‖b‖ :=
  eLpNorm_top_le_of_ae (Eventually.of_forall fun _ => le_rfl)

/-- Constant bilinear maps, Hölder `(2, 2) → 1`. -/
theorem bil_const_22 (b : V →L[ℝ] W →L[ℝ] Z) {X₁ X₂ : X → V} {Y₁ Y₂ : X → W}
    (hX₁ : AEStronglyMeasurable X₁ μ) (hX₂ : AEStronglyMeasurable X₂ μ)
    (hY₁ : AEStronglyMeasurable Y₁ μ) (hY₂ : AEStronglyMeasurable Y₂ μ)
    {D BX BY : ℝ≥0∞} (hX₂b : eLpNorm X₂ 2 μ ≤ BX) (hY₁b : eLpNorm Y₁ 2 μ ≤ BY)
    (hdX : eLpNorm (fun x => X₁ x - X₂ x) 2 μ ≤ D)
    (hdY : eLpNorm (fun x => Y₁ x - Y₂ x) 2 μ ≤ D) :
    eLpNorm (fun x => b (X₁ x) (Y₁ x) - b (X₂ x) (Y₂ x)) 1 μ ≤
      ENNReal.ofReal ‖b‖ * (BY + BX) * D := by
  have h := eLpNorm_term2 (Φ₁ := fun _ : X => b) (Φ₂ := fun _ : X => b) (μ := μ)
    aestronglyMeasurable_const aestronglyMeasurable_const hX₁ hX₂ hY₁ hY₂
  have h0 : eLpNorm (fun _ : X => b - b) ⊤ μ = 0 := by
    simp only [sub_self]; exact eLpNorm_zero'
  rw [h0, zero_mul, zero_add] at h
  refine h.trans ?_
  have hb := eLpNorm_const_clm_le (μ := μ) b
  calc eLpNorm (fun _ : X => b) ⊤ μ * (eLpNorm (fun x => X₁ x - X₂ x) 2 μ * eLpNorm Y₁ 2 μ) +
        eLpNorm (fun _ : X => b) ⊤ μ * (eLpNorm X₂ 2 μ * eLpNorm (fun x => Y₁ x - Y₂ x) 2 μ)
      ≤ ENNReal.ofReal ‖b‖ * (D * BY) + ENNReal.ofReal ‖b‖ * (BX * D) := by gcongr
    _ = _ := by ring

/-- Bound for a constant bilinear map, Hölder `(2, 2) → 1`. -/
theorem bil_const_22_bound (b : V →L[ℝ] W →L[ℝ] Z) {X₂ : X → V} {Y₂ : X → W}
    (hX₂ : AEStronglyMeasurable X₂ μ) (hY₂ : AEStronglyMeasurable Y₂ μ) {BX BY : ℝ≥0∞}
    (hX₂b : eLpNorm X₂ 2 μ ≤ BX) (hY₂b : eLpNorm Y₂ 2 μ ≤ BY) :
    eLpNorm (fun x => b (X₂ x) (Y₂ x)) 1 μ ≤ ENNReal.ofReal ‖b‖ * (BX * BY) :=
  (eLpNorm_apply2_le (Φ := fun _ : X => b) aestronglyMeasurable_const hX₂ hY₂).trans
    (by gcongr; exact eLpNorm_const_clm_le b)

theorem eLpNorm_const_mul_le (c : ℝ) {f : X → ℝ} :
    eLpNorm (fun x => c * f x) 2 μ ≤ ENNReal.ofReal |c| * eLpNorm f 2 μ := by
  have := eLpNorm_const_smul c f 2 μ
  rw [Real.enorm_eq_ofReal_abs] at this
  exact this.le

/-- Constant bilinear maps, Hölder `(4, 4) → 2`. -/
theorem bil_const_44 (b : V →L[ℝ] W →L[ℝ] Z) {X₁ X₂ : X → V} {Y₁ Y₂ : X → W}
    (hX₁ : AEStronglyMeasurable X₁ μ) (hX₂ : AEStronglyMeasurable X₂ μ)
    (hY₁ : AEStronglyMeasurable Y₁ μ) (hY₂ : AEStronglyMeasurable Y₂ μ)
    {D BX BY : ℝ≥0∞} (hX₂b : eLpNorm X₂ 4 μ ≤ BX) (hY₁b : eLpNorm Y₁ 4 μ ≤ BY)
    (hdX : eLpNorm (fun x => X₁ x - X₂ x) 4 μ ≤ D)
    (hdY : eLpNorm (fun x => Y₁ x - Y₂ x) 4 μ ≤ D) :
    eLpNorm (fun x => b (X₁ x) (Y₁ x) - b (X₂ x) (Y₂ x)) 2 μ ≤
      ENNReal.ofReal ‖b‖ * (BY + BX) * D := by
  have hdXm : AEStronglyMeasurable (fun x => X₁ x - X₂ x) μ := hX₁.sub hX₂
  have hdYm : AEStronglyMeasurable (fun x => Y₁ x - Y₂ x) μ := hY₁.sub hY₂
  have hpt : ∀ x, ‖b (X₁ x) (Y₁ x) - b (X₂ x) (Y₂ x)‖ ≤
      ‖b‖ * (‖X₁ x - X₂ x‖ * ‖Y₁ x‖) + ‖b‖ * (‖X₂ x‖ * ‖Y₁ x - Y₂ x‖) := by
    intro x
    have e : b (X₁ x) (Y₁ x) - b (X₂ x) (Y₂ x) =
        b (X₁ x - X₂ x) (Y₁ x) + b (X₂ x) (Y₁ x - Y₂ x) := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [← mul_assoc]; exact b.le_opNorm₂ _ _
    · rw [← mul_assoc]; exact b.le_opNorm₂ _ _
  have m1 : AEStronglyMeasurable (fun x => ‖X₁ x - X₂ x‖ * ‖Y₁ x‖) μ := hdXm.norm.mul hY₁.norm
  have m2 : AEStronglyMeasurable (fun x => ‖X₂ x‖ * ‖Y₁ x - Y₂ x‖) μ := hX₂.norm.mul hdYm.norm
  have b1 : eLpNorm (fun x => ‖X₁ x - X₂ x‖ * ‖Y₁ x‖) 2 μ ≤ D * BY := by
    refine (eLpNorm_mul_four_four hdXm.norm hY₁.norm).trans ?_
    rw [eLpNorm_norm, eLpNorm_norm]; gcongr
  have b2 : eLpNorm (fun x => ‖X₂ x‖ * ‖Y₁ x - Y₂ x‖) 2 μ ≤ BX * D := by
    refine (eLpNorm_mul_four_four hX₂.norm hdYm.norm).trans ?_
    rw [eLpNorm_norm, eLpNorm_norm]; gcongr
  calc eLpNorm (fun x => b (X₁ x) (Y₁ x) - b (X₂ x) (Y₂ x)) 2 μ
      ≤ eLpNorm (fun x => ‖b‖ * (‖X₁ x - X₂ x‖ * ‖Y₁ x‖) + ‖b‖ * (‖X₂ x‖ * ‖Y₁ x - Y₂ x‖)) 2 μ :=
        eLpNorm_mono_real hpt
    _ ≤ eLpNorm (fun x => ‖b‖ * (‖X₁ x - X₂ x‖ * ‖Y₁ x‖)) 2 μ +
          eLpNorm (fun x => ‖b‖ * (‖X₂ x‖ * ‖Y₁ x - Y₂ x‖)) 2 μ :=
        eLpNorm_add_le (m1.const_mul _) (m2.const_mul _) (by norm_num)
    _ ≤ ENNReal.ofReal |‖b‖| * eLpNorm (fun x => ‖X₁ x - X₂ x‖ * ‖Y₁ x‖) 2 μ +
          ENNReal.ofReal |‖b‖| * eLpNorm (fun x => ‖X₂ x‖ * ‖Y₁ x - Y₂ x‖) 2 μ :=
        add_le_add (eLpNorm_const_mul_le _) (eLpNorm_const_mul_le _)
    _ ≤ ENNReal.ofReal ‖b‖ * (D * BY) + ENNReal.ofReal ‖b‖ * (BX * D) := by
        rw [abs_of_nonneg (norm_nonneg b)]; gcongr
    _ = _ := by ring

/-- Bound for a constant bilinear map, Hölder `(4, 4) → 2`. -/
theorem bil_const_44_bound (b : V →L[ℝ] W →L[ℝ] Z) {X₂ : X → V} {Y₂ : X → W}
    (hX₂ : AEStronglyMeasurable X₂ μ) (hY₂ : AEStronglyMeasurable Y₂ μ) {BX BY : ℝ≥0∞}
    (hX₂b : eLpNorm X₂ 4 μ ≤ BX) (hY₂b : eLpNorm Y₂ 4 μ ≤ BY) :
    eLpNorm (fun x => b (X₂ x) (Y₂ x)) 2 μ ≤ ENNReal.ofReal ‖b‖ * (BX * BY) := by
  have m : AEStronglyMeasurable (fun x => ‖X₂ x‖ * ‖Y₂ x‖) μ := hX₂.norm.mul hY₂.norm
  calc eLpNorm (fun x => b (X₂ x) (Y₂ x)) 2 μ ≤ eLpNorm (fun x => ‖b‖ * (‖X₂ x‖ * ‖Y₂ x‖)) 2 μ :=
        eLpNorm_mono_real fun x => by rw [← mul_assoc]; exact b.le_opNorm₂ _ _
    _ ≤ ENNReal.ofReal |‖b‖| * eLpNorm (fun x => ‖X₂ x‖ * ‖Y₂ x‖) 2 μ := eLpNorm_const_mul_le _
    _ ≤ ENNReal.ofReal ‖b‖ * (BX * BY) := by
        rw [abs_of_nonneg (norm_nonneg b)]
        gcongr
        refine (eLpNorm_mul_four_four hX₂.norm hY₂.norm).trans ?_
        rw [eLpNorm_norm, eLpNorm_norm]; gcongr

end ConstBil

/-! ### Sums of term differences -/

section Sums

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem eLpNorm_sum3_sub {f₁ f₂ g₁ g₂ h₁ h₂ : X → Z}
    (hf₁ : AEStronglyMeasurable f₁ μ) (hf₂ : AEStronglyMeasurable f₂ μ)
    (hg₁ : AEStronglyMeasurable g₁ μ) (hg₂ : AEStronglyMeasurable g₂ μ)
    (hh₁ : AEStronglyMeasurable h₁ μ) (hh₂ : AEStronglyMeasurable h₂ μ) :
    eLpNorm (fun x => (f₁ x + g₁ x + h₁ x) - (f₂ x + g₂ x + h₂ x)) 1 μ ≤
      eLpNorm (fun x => f₁ x - f₂ x) 1 μ + eLpNorm (fun x => g₁ x - g₂ x) 1 μ +
        eLpNorm (fun x => h₁ x - h₂ x) 1 μ := by
  have e : (fun x => (f₁ x + g₁ x + h₁ x) - (f₂ x + g₂ x + h₂ x)) =
      (fun x => f₁ x - f₂ x) + (fun x => g₁ x - g₂ x) + (fun x => h₁ x - h₂ x) := by
    funext x; simp only [Pi.add_apply]; abel
  rw [e]
  exact (eLpNorm_add_le ((hf₁.sub hf₂).add (hg₁.sub hg₂)) (hh₁.sub hh₂) le_rfl).trans
    (add_le_add (eLpNorm_add_le (hf₁.sub hf₂) (hg₁.sub hg₂) le_rfl) le_rfl)

theorem eLpNorm_sum3_le {f g h : X → Z}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) :
    eLpNorm (fun x => f x + g x + h x) 1 μ ≤ eLpNorm f 1 μ + eLpNorm g 1 μ + eLpNorm h 1 μ := by
  exact (eLpNorm_add_le (hf.add hg) hh le_rfl).trans
    (add_le_add (eLpNorm_add_le hf hg le_rfl) le_rfl)

theorem eLpNorm_sum4_sub {f₁ f₂ g₁ g₂ h₁ h₂ k₁ k₂ : X → Z}
    (hf₁ : AEStronglyMeasurable f₁ μ) (hf₂ : AEStronglyMeasurable f₂ μ)
    (hg₁ : AEStronglyMeasurable g₁ μ) (hg₂ : AEStronglyMeasurable g₂ μ)
    (hh₁ : AEStronglyMeasurable h₁ μ) (hh₂ : AEStronglyMeasurable h₂ μ)
    (hk₁ : AEStronglyMeasurable k₁ μ) (hk₂ : AEStronglyMeasurable k₂ μ) :
    eLpNorm (fun x => (f₁ x + g₁ x + h₁ x + k₁ x) - (f₂ x + g₂ x + h₂ x + k₂ x)) 1 μ ≤
      eLpNorm (fun x => f₁ x - f₂ x) 1 μ + eLpNorm (fun x => g₁ x - g₂ x) 1 μ +
        eLpNorm (fun x => h₁ x - h₂ x) 1 μ + eLpNorm (fun x => k₁ x - k₂ x) 1 μ := by
  have e : (fun x => (f₁ x + g₁ x + h₁ x + k₁ x) - (f₂ x + g₂ x + h₂ x + k₂ x)) =
      fun x => ((f₁ x - f₂ x) + (g₁ x - g₂ x) + (h₁ x - h₂ x)) + (k₁ x - k₂ x) := by
    funext x; abel
  rw [e]
  exact (eLpNorm_add_le (((hf₁.sub hf₂).add (hg₁.sub hg₂)).add (hh₁.sub hh₂)) (hk₁.sub hk₂)
    le_rfl).trans
    (add_le_add (eLpNorm_sum3_le (hf₁.sub hf₂) (hg₁.sub hg₂) (hh₁.sub hh₂)) le_rfl)

theorem eLpNorm_sum4_le {f g h k : X → Z}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) (hk : AEStronglyMeasurable k μ) :
    eLpNorm (fun x => f x + g x + h x + k x) 1 μ ≤
      eLpNorm f 1 μ + eLpNorm g 1 μ + eLpNorm h 1 μ + eLpNorm k 1 μ := by
  exact (eLpNorm_add_le ((hf.add hg).add hh) hk le_rfl).trans
    (add_le_add (eLpNorm_sum3_le hf hg hh) le_rfl)

theorem eLpNorm_sum2_sub {f₁ f₂ g₁ g₂ : X → Z}
    (hf₁ : AEStronglyMeasurable f₁ μ) (hf₂ : AEStronglyMeasurable f₂ μ)
    (hg₁ : AEStronglyMeasurable g₁ μ) (hg₂ : AEStronglyMeasurable g₂ μ) :
    eLpNorm (fun x => (f₁ x + g₁ x) - (f₂ x + g₂ x)) 1 μ ≤
      eLpNorm (fun x => f₁ x - f₂ x) 1 μ + eLpNorm (fun x => g₁ x - g₂ x) 1 μ := by
  have e : (fun x => (f₁ x + g₁ x) - (f₂ x + g₂ x)) =
      (fun x => f₁ x - f₂ x) + (fun x => g₁ x - g₂ x) := by
    funext x; simp only [Pi.add_apply]; abel
  rw [e]
  exact eLpNorm_add_le (hf₁.sub hf₂) (hg₁.sub hg₂) le_rfl

theorem eLpNorm_finsum_sub {ι : Type*} (s : Finset ι) {f₁ f₂ : ι → X → Z}
    (hf₁ : ∀ i, AEStronglyMeasurable (f₁ i) μ) (hf₂ : ∀ i, AEStronglyMeasurable (f₂ i) μ) :
    eLpNorm (fun x => ∑ i ∈ s, f₁ i x - ∑ i ∈ s, f₂ i x) 1 μ ≤
      ∑ i ∈ s, eLpNorm (fun x => f₁ i x - f₂ i x) 1 μ := by
  have e : (fun x => ∑ i ∈ s, f₁ i x - ∑ i ∈ s, f₂ i x) =
      ∑ i ∈ s, fun x => f₁ i x - f₂ i x := by
    funext x; simp [Finset.sum_apply, Finset.sum_sub_distrib]
  rw [e]
  exact eLpNorm_sum_le (fun i _ => (hf₁ i).sub (hf₂ i)) le_rfl

end Sums

/-! ### Packet bounds of a bounded jet field -/

section JetPackets

variable {T : ℝ} {C : Type} [Fintype C] {Q : ChartBox T} {Ke : Set CoframeFibre} {B : ℝ≥0∞}
  {R R₁ R₂ : E4 → RJet C}

/-- The comparison constant `max(1, |Q|)` of the chart. -/
def cQ (Q : ChartBox T) : ℝ≥0∞ := max 1 (Q.μ univ)

theorem one_le_cQ (Q : ChartBox T) : 1 ≤ cQ Q := le_max_left _ _

theorem cQ_ne_top (Q : ChartBox T) : cQ Q ≠ ⊤ := cmax_ne_top

theorem le_cQ_mul (Q : ChartBox T) (a : ℝ≥0∞) : a ≤ cQ Q * a :=
  le_mul_of_one_le_left' (one_le_cQ Q)

theorem JetBound.bF2 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).F) 2 Q.μ ≤ cQ Q * B :=
  h.F.trans (le_cQ_mul Q B)
theorem JetBound.bF1 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).F) 1 Q.μ ≤ cQ Q * B :=
  (eLpNorm_le_cmax_12 h.m_F).trans (by unfold cQ; gcongr; exact h.F)
theorem JetBound.bA2 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).A) 2 Q.μ ≤ cQ Q * B :=
  (eLpNorm_le_cmax_24 h.m_A).trans (by unfold cQ; gcongr; exact h.A)
theorem JetBound.bA4 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).A) 4 Q.μ ≤ cQ Q * B :=
  h.A.trans (le_cQ_mul Q B)
theorem JetBound.bK2 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).K) 2 Q.μ ≤ cQ Q * B :=
  h.K.trans (le_cQ_mul Q B)
theorem JetBound.bK1 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).K) 1 Q.μ ≤ cQ Q * B :=
  (eLpNorm_le_cmax_12 h.m_K).trans (by unfold cQ; gcongr; exact h.K)
theorem JetBound.bH2 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).H) 2 Q.μ ≤ cQ Q * B :=
  (eLpNorm_le_cmax_24 h.m_H).trans (by unfold cQ; gcongr; exact h.H)
theorem JetBound.bH4 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).H) 4 Q.μ ≤ cQ Q * B :=
  h.H.trans (le_cQ_mul Q B)
theorem JetBound.bde2 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).de) 2 Q.μ ≤ cQ Q * B :=
  h.de.trans (le_cQ_mul Q B)
theorem JetBound.bΨ2 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).Ψ) 2 Q.μ ≤ cQ Q * B :=
  (eLpNorm_le_cmax_24 h.m_Ψ).trans (by unfold cQ; gcongr; exact h.Ψ)
theorem JetBound.bΨ4 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).Ψ) 4 Q.μ ≤ cQ Q * B :=
  h.Ψ.trans (le_cQ_mul Q B)
theorem JetBound.bΨb2 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).Ψb) 2 Q.μ ≤ cQ Q * B :=
  (eLpNorm_le_cmax_24 h.m_Ψb).trans (by unfold cQ; gcongr; exact h.Ψb)
theorem JetBound.bΨb4 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).Ψb) 4 Q.μ ≤ cQ Q * B :=
  h.Ψb.trans (le_cQ_mul Q B)
theorem JetBound.bdΨ2 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).dΨ) 2 Q.μ ≤ cQ Q * B :=
  h.dΨ.trans (le_cQ_mul Q B)
theorem JetBound.bdΨb2 (h : JetBound Q Ke B R) : eLpNorm (fun x => (R x).dΨb) 2 Q.μ ≤ cQ Q * B :=
  h.dΨb.trans (le_cQ_mul Q B)

theorem dist_e (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).e - (R₂ x).e) ⊤ Q.μ ≤ cQ Q * D :=
  (le_jetDist_e.trans hD).trans (le_cQ_mul Q D)
theorem dist_de2 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).de - (R₂ x).de) 2 Q.μ ≤ cQ Q * D :=
  (le_jetDist_de.trans hD).trans (le_cQ_mul Q D)
theorem dist_F2 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).F - (R₂ x).F) 2 Q.μ ≤ cQ Q * D :=
  (le_jetDist_F.trans hD).trans (le_cQ_mul Q D)
theorem dist_F1 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).F - (R₂ x).F) 1 Q.μ ≤ cQ Q * D :=
  (eLpNorm_le_cmax_12 (h₁.m_F.sub h₂.m_F)).trans (by unfold cQ; gcongr; exact le_jetDist_F.trans hD)
theorem dist_A2 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).A - (R₂ x).A) 2 Q.μ ≤ cQ Q * D :=
  (eLpNorm_le_cmax_24 (h₁.m_A.sub h₂.m_A)).trans (by unfold cQ; gcongr; exact le_jetDist_A.trans hD)
theorem dist_K2 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).K - (R₂ x).K) 2 Q.μ ≤ cQ Q * D :=
  (le_jetDist_K.trans hD).trans (le_cQ_mul Q D)
theorem dist_K1 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).K - (R₂ x).K) 1 Q.μ ≤ cQ Q * D :=
  (eLpNorm_le_cmax_12 (h₁.m_K.sub h₂.m_K)).trans (by unfold cQ; gcongr; exact le_jetDist_K.trans hD)
theorem dist_H2 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).H - (R₂ x).H) 2 Q.μ ≤ cQ Q * D :=
  (eLpNorm_le_cmax_24 (h₁.m_H.sub h₂.m_H)).trans (by unfold cQ; gcongr; exact le_jetDist_H.trans hD)
theorem dist_H4 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).H - (R₂ x).H) 4 Q.μ ≤ cQ Q * D :=
  (le_jetDist_H.trans hD).trans (le_cQ_mul Q D)
theorem dist_Ψ2 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).Ψ - (R₂ x).Ψ) 2 Q.μ ≤ cQ Q * D :=
  (eLpNorm_le_cmax_24 (h₁.m_Ψ.sub h₂.m_Ψ)).trans (by unfold cQ; gcongr; exact le_jetDist_Ψ.trans hD)
theorem dist_Ψ4 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).Ψ - (R₂ x).Ψ) 4 Q.μ ≤ cQ Q * D :=
  (le_jetDist_Ψ.trans hD).trans (le_cQ_mul Q D)
theorem dist_Ψb2 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).Ψb - (R₂ x).Ψb) 2 Q.μ ≤ cQ Q * D :=
  (eLpNorm_le_cmax_24 (h₁.m_Ψb.sub h₂.m_Ψb)).trans (by unfold cQ; gcongr; exact le_jetDist_Ψb.trans hD)
theorem dist_Ψb4 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).Ψb - (R₂ x).Ψb) 4 Q.μ ≤ cQ Q * D :=
  (le_jetDist_Ψb.trans hD).trans (le_cQ_mul Q D)
theorem dist_dΨ2 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).dΨ - (R₂ x).dΨ) 2 Q.μ ≤ cQ Q * D :=
  (le_jetDist_dΨ.trans hD).trans (le_cQ_mul Q D)
theorem dist_dΨb2 (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => (R₁ x).dΨb - (R₂ x).dΨb) 2 Q.μ ≤ cQ Q * D :=
  (le_jetDist_dΨb.trans hD).trans (le_cQ_mul Q D)

end JetPackets

/-! ### The bosonic sector: Yang–Mills and Higgs-kinetic pieces -/

section BosonPieces

variable {T : ℝ} {C : Type} [Fintype C] {Ysec : Type} [Fintype Ysec]

/-- The Yang–Mills piece of factor `j` of the bosonic covector. -/
def ymJet (j : Fin 3) (R : RJet C) : RJet C →L[ℝ] ℝ :=
  ymMetCoeff j R.e R.F R.F + ymDaCoeff j R.e R.F + ymACoeff j R.e R.A R.F

/-- The Higgs-kinetic piece of the bosonic covector. -/
def hgJet (R : RJet C) : RJet C →L[ℝ] ℝ :=
  higgsMetCoeff R.e R.K R.K + higgsDCoeff R.e R.K + higgsHCoeff R.e R.H R.K +
    higgsACoeff R.e R.A R.K

/-- The Higgs potential factor `|H|² - v²`. -/
def potA (θ : CoefficientBank Ysec) (R : RJet C) : ℝ := higgsQuad R.H - θ.vH ^ 2

/-- The potential piece of the bosonic covector (without `λ_H`). -/
def potJet (θ : CoefficientBank Ysec) (R : RJet C) : RJet C →L[ℝ] ℝ :=
  potHCoeff R.e (potA θ R • R.H) + potVCoeff R.e (potA θ R ^ 2)

theorem bosonCov_eq_pieces (θ : CoefficientBank Ysec) (R : RJet C) :
    bosonCov θ R = (∑ j, gaugeScalars θ j • ymJet j R) + hgJet R + θ.lambdaH • potJet θ R :=
  rfl

theorem le_mul_cQ (Q : ChartBox T) (a : ℝ≥0∞) : a ≤ a * cQ Q :=
  le_mul_of_one_le_right' (one_le_cQ Q)

set_option maxHeartbeats 4000000 in
/-- **Yang–Mills piece**: uniform Lipschitz bound on bounded jet fields. -/
theorem ym_piece (Q : ChartBox T) (j : Fin 3) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hsub : Ke ⊆ coframeGL) {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (R₁ R₂ : E4 → RJet C) (D : ℝ≥0∞), JetBound Q Ke B R₁ →
      JetBound Q Ke B R₂ → jetDist Q R₁ R₂ ≤ D →
      eLpNorm (fun x => ymJet j (R₁ x) - ymJet j (R₂ x)) 1 Q.μ ≤ K * D ∧
        eLpNorm (fun x => ymJet j (R₂ x)) 1 Q.μ ≤ K := by
  have hB' : cQ Q * B ≠ ⊤ := ENNReal.mul_ne_top (cQ_ne_top Q) hB
  obtain ⟨K1, hK1, h1⟩ :=
    coeff2_lip (CovSmooth.contDiffOn_ymMetCoeff (C := C) (n := 1) j) hKe hsub hB'
  obtain ⟨K2, hK2, h2⟩ :=
    coeff1_lip (CovSmooth.contDiffOn_ymDaCoeff (C := C) (n := 1) j) hKe hsub hB'
  obtain ⟨K3, hK3, h3⟩ :=
    coeff2_lip (CovSmooth.contDiffOn_ymACoeff (C := C) (n := 1) j) hKe hsub hB'
  refine ⟨(K1 + K2 + K3) * cQ Q,
    ENNReal.mul_ne_top (by finiteness) (cQ_ne_top Q), ?_⟩
  intro R₁ R₂ D h₁ h₂ hD
  have t1 := h1 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => (R₁ x).F)
    (fun x => (R₂ x).F) (fun x => (R₁ x).F) (fun x => (R₂ x).F) (cQ Q * D) h₁.m_e h₂.m_e
    h₁.chart h₂.chart h₁.m_F h₂.m_F h₁.m_F h₂.m_F h₁.bF2 h₂.bF2 h₁.bF2 h₂.bF2
    (dist_e h₁ h₂ hD) (dist_F2 h₁ h₂ hD) (dist_F2 h₁ h₂ hD)
  have t2 := h2 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => (R₁ x).F)
    (fun x => (R₂ x).F) (cQ Q * D) h₁.m_e h₂.m_e h₁.chart h₂.chart h₁.m_F h₂.m_F h₁.bF1 h₂.bF1
    (dist_e h₁ h₂ hD) (dist_F1 h₁ h₂ hD)
  have t3 := h3 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => (R₁ x).A)
    (fun x => (R₂ x).A) (fun x => (R₁ x).F) (fun x => (R₂ x).F) (cQ Q * D) h₁.m_e h₂.m_e
    h₁.chart h₂.chart h₁.m_A h₂.m_A h₁.m_F h₂.m_F h₁.bA2 h₂.bA2 h₁.bF2 h₂.bF2
    (dist_e h₁ h₂ hD) (dist_A2 h₁ h₂ hD) (dist_F2 h₁ h₂ hD)
  have c1 := (CovSmooth.contDiffOn_ymMetCoeff (C := C) (n := 1) j).continuousOn
  have c2 := (CovSmooth.contDiffOn_ymDaCoeff (C := C) (n := 1) j).continuousOn
  have c3 := (CovSmooth.contDiffOn_ymACoeff (C := C) (n := 1) j).continuousOn
  have m11 := aesm_apply (aesm_apply (aesm_coeff c1 hsub h₁.m_e h₁.chart) h₁.m_F) h₁.m_F
  have m12 := aesm_apply (aesm_apply (aesm_coeff c1 hsub h₂.m_e h₂.chart) h₂.m_F) h₂.m_F
  have m21 := aesm_apply (aesm_coeff c2 hsub h₁.m_e h₁.chart) h₁.m_F
  have m22 := aesm_apply (aesm_coeff c2 hsub h₂.m_e h₂.chart) h₂.m_F
  have m31 := aesm_apply (aesm_apply (aesm_coeff c3 hsub h₁.m_e h₁.chart) h₁.m_A) h₁.m_F
  have m32 := aesm_apply (aesm_apply (aesm_coeff c3 hsub h₂.m_e h₂.chart) h₂.m_A) h₂.m_F
  constructor
  · calc eLpNorm (fun x => ymJet j (R₁ x) - ymJet j (R₂ x)) 1 Q.μ
        ≤ eLpNorm (fun x => ymMetCoeff j (R₁ x).e (R₁ x).F (R₁ x).F -
              ymMetCoeff j (R₂ x).e (R₂ x).F (R₂ x).F) 1 Q.μ +
            eLpNorm (fun x => ymDaCoeff j (R₁ x).e (R₁ x).F -
              ymDaCoeff j (R₂ x).e (R₂ x).F) 1 Q.μ +
            eLpNorm (fun x => ymACoeff j (R₁ x).e (R₁ x).A (R₁ x).F -
              ymACoeff j (R₂ x).e (R₂ x).A (R₂ x).F) 1 Q.μ :=
          eLpNorm_sum3_sub m11 m12 m21 m22 m31 m32
      _ ≤ K1 * (cQ Q * D) + K2 * (cQ Q * D) + K3 * (cQ Q * D) :=
          add_le_add (add_le_add t1.1 t2.1) t3.1
      _ = (K1 + K2 + K3) * cQ Q * D := by ring
  · calc eLpNorm (fun x => ymJet j (R₂ x)) 1 Q.μ
        ≤ eLpNorm (fun x => ymMetCoeff (C := C) j (R₂ x).e (R₂ x).F (R₂ x).F) 1 Q.μ +
            eLpNorm (fun x => ymDaCoeff (C := C) j (R₂ x).e (R₂ x).F) 1 Q.μ +
            eLpNorm (fun x => ymACoeff (C := C) j (R₂ x).e (R₂ x).A (R₂ x).F) 1 Q.μ :=
          eLpNorm_sum3_le m12 m22 m32
      _ ≤ K1 + K2 + K3 := add_le_add (add_le_add t1.2 t2.2) t3.2
      _ ≤ _ := le_mul_cQ Q _

set_option maxHeartbeats 4000000 in
/-- **Higgs-kinetic piece**: uniform Lipschitz bound on bounded jet fields. -/
theorem hg_piece (Q : ChartBox T) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hsub : Ke ⊆ coframeGL) {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (R₁ R₂ : E4 → RJet C) (D : ℝ≥0∞), JetBound Q Ke B R₁ →
      JetBound Q Ke B R₂ → jetDist Q R₁ R₂ ≤ D →
      eLpNorm (fun x => hgJet (R₁ x) - hgJet (R₂ x)) 1 Q.μ ≤ K * D ∧
        eLpNorm (fun x => hgJet (R₂ x)) 1 Q.μ ≤ K := by
  have hB' : cQ Q * B ≠ ⊤ := ENNReal.mul_ne_top (cQ_ne_top Q) hB
  obtain ⟨K1, hK1, h1⟩ :=
    coeff2_lip (CovSmooth.contDiffOn_higgsMetCoeff (C := C) (n := 1)) hKe hsub hB'
  obtain ⟨K2, hK2, h2⟩ :=
    coeff1_lip (CovSmooth.contDiffOn_higgsDCoeff (C := C) (n := 1)) hKe hsub hB'
  obtain ⟨K3, hK3, h3⟩ :=
    coeff2_lip (CovSmooth.contDiffOn_higgsHCoeff (C := C) (n := 1)) hKe hsub hB'
  obtain ⟨K4, hK4, h4⟩ :=
    coeff2_lip (CovSmooth.contDiffOn_higgsACoeff (C := C) (n := 1)) hKe hsub hB'
  refine ⟨(K1 + K2 + K3 + K4) * cQ Q,
    ENNReal.mul_ne_top (by finiteness) (cQ_ne_top Q), ?_⟩
  intro R₁ R₂ D h₁ h₂ hD
  have t1 := h1 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => (R₁ x).K)
    (fun x => (R₂ x).K) (fun x => (R₁ x).K) (fun x => (R₂ x).K) (cQ Q * D) h₁.m_e h₂.m_e
    h₁.chart h₂.chart h₁.m_K h₂.m_K h₁.m_K h₂.m_K h₁.bK2 h₂.bK2 h₁.bK2 h₂.bK2
    (dist_e h₁ h₂ hD) (dist_K2 h₁ h₂ hD) (dist_K2 h₁ h₂ hD)
  have t2 := h2 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => (R₁ x).K)
    (fun x => (R₂ x).K) (cQ Q * D) h₁.m_e h₂.m_e h₁.chart h₂.chart h₁.m_K h₂.m_K h₁.bK1 h₂.bK1
    (dist_e h₁ h₂ hD) (dist_K1 h₁ h₂ hD)
  have t3 := h3 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => (R₁ x).H)
    (fun x => (R₂ x).H) (fun x => (R₁ x).K) (fun x => (R₂ x).K) (cQ Q * D) h₁.m_e h₂.m_e
    h₁.chart h₂.chart h₁.m_H h₂.m_H h₁.m_K h₂.m_K h₁.bH2 h₂.bH2 h₁.bK2 h₂.bK2
    (dist_e h₁ h₂ hD) (dist_H2 h₁ h₂ hD) (dist_K2 h₁ h₂ hD)
  have t4 := h4 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => (R₁ x).A)
    (fun x => (R₂ x).A) (fun x => (R₁ x).K) (fun x => (R₂ x).K) (cQ Q * D) h₁.m_e h₂.m_e
    h₁.chart h₂.chart h₁.m_A h₂.m_A h₁.m_K h₂.m_K h₁.bA2 h₂.bA2 h₁.bK2 h₂.bK2
    (dist_e h₁ h₂ hD) (dist_A2 h₁ h₂ hD) (dist_K2 h₁ h₂ hD)
  have c1 := (CovSmooth.contDiffOn_higgsMetCoeff (C := C) (n := 1)).continuousOn
  have c2 := (CovSmooth.contDiffOn_higgsDCoeff (C := C) (n := 1)).continuousOn
  have c3 := (CovSmooth.contDiffOn_higgsHCoeff (C := C) (n := 1)).continuousOn
  have c4 := (CovSmooth.contDiffOn_higgsACoeff (C := C) (n := 1)).continuousOn
  have m11 := aesm_apply (aesm_apply (aesm_coeff c1 hsub h₁.m_e h₁.chart) h₁.m_K) h₁.m_K
  have m12 := aesm_apply (aesm_apply (aesm_coeff c1 hsub h₂.m_e h₂.chart) h₂.m_K) h₂.m_K
  have m21 := aesm_apply (aesm_coeff c2 hsub h₁.m_e h₁.chart) h₁.m_K
  have m22 := aesm_apply (aesm_coeff c2 hsub h₂.m_e h₂.chart) h₂.m_K
  have m31 := aesm_apply (aesm_apply (aesm_coeff c3 hsub h₁.m_e h₁.chart) h₁.m_H) h₁.m_K
  have m32 := aesm_apply (aesm_apply (aesm_coeff c3 hsub h₂.m_e h₂.chart) h₂.m_H) h₂.m_K
  have m41 := aesm_apply (aesm_apply (aesm_coeff c4 hsub h₁.m_e h₁.chart) h₁.m_A) h₁.m_K
  have m42 := aesm_apply (aesm_apply (aesm_coeff c4 hsub h₂.m_e h₂.chart) h₂.m_A) h₂.m_K
  constructor
  · calc eLpNorm (fun x => hgJet (R₁ x) - hgJet (R₂ x)) 1 Q.μ
        ≤ eLpNorm (fun x => higgsMetCoeff (R₁ x).e (R₁ x).K (R₁ x).K -
              higgsMetCoeff (R₂ x).e (R₂ x).K (R₂ x).K) 1 Q.μ +
            eLpNorm (fun x => higgsDCoeff (R₁ x).e (R₁ x).K -
              higgsDCoeff (R₂ x).e (R₂ x).K) 1 Q.μ +
            eLpNorm (fun x => higgsHCoeff (R₁ x).e (R₁ x).H (R₁ x).K -
              higgsHCoeff (R₂ x).e (R₂ x).H (R₂ x).K) 1 Q.μ +
            eLpNorm (fun x => higgsACoeff (R₁ x).e (R₁ x).A (R₁ x).K -
              higgsACoeff (R₂ x).e (R₂ x).A (R₂ x).K) 1 Q.μ :=
          eLpNorm_sum4_sub m11 m12 m21 m22 m31 m32 m41 m42
      _ ≤ K1 * (cQ Q * D) + K2 * (cQ Q * D) + K3 * (cQ Q * D) + K4 * (cQ Q * D) :=
          add_le_add (add_le_add (add_le_add t1.1 t2.1) t3.1) t4.1
      _ = (K1 + K2 + K3 + K4) * cQ Q * D := by ring
  · calc eLpNorm (fun x => hgJet (R₂ x)) 1 Q.μ
        ≤ eLpNorm (fun x => higgsMetCoeff (C := C) (R₂ x).e (R₂ x).K (R₂ x).K) 1 Q.μ +
            eLpNorm (fun x => higgsDCoeff (C := C) (R₂ x).e (R₂ x).K) 1 Q.μ +
            eLpNorm (fun x => higgsHCoeff (C := C) (R₂ x).e (R₂ x).H (R₂ x).K) 1 Q.μ +
            eLpNorm (fun x => higgsACoeff (C := C) (R₂ x).e (R₂ x).A (R₂ x).K) 1 Q.μ :=
          eLpNorm_sum4_le m12 m22 m32 m42
      _ ≤ K1 + K2 + K3 + K4 := add_le_add (add_le_add (add_le_add t1.2 t2.2) t3.2) t4.2
      _ ≤ _ := le_mul_cQ Q _

end BosonPieces

/-! ### The bosonic sector: the Higgs potential piece -/

section PotPiece

variable {T : ℝ} {C : Type} [Fintype C] {Ysec : Type} [Fintype Ysec]

theorem potJet_eq (θ : CoefficientBank Ysec) (R : RJet C) :
    potJet θ R = potHCoeff R.e (ContinuousLinearMap.lsmul ℝ ℝ (potA θ R) R.H) +
      potVCoeff R.e (ContinuousLinearMap.mul ℝ ℝ (potA θ R) (potA θ R)) := by
  simp only [potJet, ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply', sq]

theorem abs_sq_sub_sq_le {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |a ^ 2 - b ^ 2| ≤ 2 * M * |a - b| := by
  rw [show a ^ 2 - b ^ 2 = (a + b) * (a - b) by ring, abs_mul]
  gcongr
  calc |a + b| ≤ |a| + |b| := abs_add_le a b
    _ ≤ 2 * M := by linarith

theorem vH_sq_le (θ₁ θ₂ : CoefficientBank Ysec) {Mb : ℝ} (hMb : 0 ≤ Mb) (h₁ : |θ₁.vH| ≤ Mb)
    (h₂ : |θ₂.vH| ≤ Mb) :
    ENNReal.ofReal |θ₁.vH ^ 2 - θ₂.vH ^ 2| ≤ ENNReal.ofReal (2 * Mb) * bankDist θ₁ θ₂ := by
  refine (ENNReal.ofReal_le_ofReal (abs_sq_sub_sq_le h₁ h₂)).trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr
  exact vH_le θ₁ θ₂

/-- `L²` bound of the potential factor `|H|² - v²`. -/
theorem potA_bound {Q : ChartBox T} {Ke : Set CoframeFibre} {B : ℝ≥0∞} {R : E4 → RJet C}
    (h : JetBound Q Ke B R) (θ : CoefficientBank Ysec) {Mb : ℝ} (hv : |θ.vH| ≤ Mb) :
    eLpNorm (fun x => potA θ (R x)) 2 Q.μ ≤
      ENNReal.ofReal ‖hInnerReL‖ * (cQ Q * B * (cQ Q * B)) + cQ Q * ENNReal.ofReal (Mb ^ 2) := by
  have mq : AEStronglyMeasurable (fun x => hInnerReL (R x).H (R x).H) Q.μ :=
    aesm_apply (aesm_apply (Φ := fun _ => hInnerReL) aestronglyMeasurable_const h.m_H) h.m_H
  have e : (fun x => potA θ (R x)) = fun x => hInnerReL (R x).H (R x).H - θ.vH ^ 2 := rfl
  rw [e]
  refine (eLpNorm_sub_le mq aestronglyMeasurable_const (by norm_num)).trans (add_le_add ?_ ?_)
  · exact bil_const_44_bound hInnerReL h.m_H h.m_H h.bH4 h.bH4
  · refine (eLpNorm_const_le_cmax _).trans ?_
    unfold cQ
    gcongr
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hv 2

/-- Lipschitz bound of the potential factor `|H|² - v²` in `L²`. -/
theorem potA_dist {Q : ChartBox T} {Ke : Set CoframeFibre} {B : ℝ≥0∞} {R₁ R₂ : E4 → RJet C}
    (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) (θ₁ θ₂ : CoefficientBank Ysec)
    {Mb : ℝ} (hMb : 0 ≤ Mb) (hv₁ : |θ₁.vH| ≤ Mb) (hv₂ : |θ₂.vH| ≤ Mb) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) (hDθ : bankDist θ₁ θ₂ ≤ D) :
    eLpNorm (fun x => potA θ₁ (R₁ x) - potA θ₂ (R₂ x)) 2 Q.μ ≤
      (ENNReal.ofReal ‖hInnerReL‖ * (cQ Q * B + cQ Q * B) * cQ Q +
        cQ Q * ENNReal.ofReal (2 * Mb)) * D := by
  have mq₁ : AEStronglyMeasurable (fun x => hInnerReL (R₁ x).H (R₁ x).H) Q.μ :=
    aesm_apply (aesm_apply (Φ := fun _ => hInnerReL) aestronglyMeasurable_const h₁.m_H) h₁.m_H
  have mq₂ : AEStronglyMeasurable (fun x => hInnerReL (R₂ x).H (R₂ x).H) Q.μ :=
    aesm_apply (aesm_apply (Φ := fun _ => hInnerReL) aestronglyMeasurable_const h₂.m_H) h₂.m_H
  have e : (fun x => potA θ₁ (R₁ x) - potA θ₂ (R₂ x)) = fun x =>
      (hInnerReL (R₁ x).H (R₁ x).H - hInnerReL (R₂ x).H (R₂ x).H) - (θ₁.vH ^ 2 - θ₂.vH ^ 2) := by
    funext x; simp only [potA, higgsQuad]; ring
  rw [e]
  have hq := bil_const_44 hInnerReL h₁.m_H h₂.m_H h₁.m_H h₂.m_H h₂.bH4 h₁.bH4
    (dist_H4 h₁ h₂ hD) (dist_H4 h₁ h₂ hD)
  refine (eLpNorm_sub_le (mq₁.sub mq₂) aestronglyMeasurable_const (by norm_num)).trans ?_
  calc _ ≤ ENNReal.ofReal ‖hInnerReL‖ * (cQ Q * B + cQ Q * B) * (cQ Q * D) +
        cQ Q * ENNReal.ofReal ‖θ₁.vH ^ 2 - θ₂.vH ^ 2‖ :=
        add_le_add hq (eLpNorm_const_le_cmax _)
    _ ≤ ENNReal.ofReal ‖hInnerReL‖ * (cQ Q * B + cQ Q * B) * (cQ Q * D) +
        cQ Q * (ENNReal.ofReal (2 * Mb) * D) := by
        gcongr
        rw [Real.norm_eq_abs]
        exact (vH_sq_le θ₁ θ₂ hMb hv₁ hv₂).trans (by gcongr)
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **Higgs-potential piece**: uniform Lipschitz bound on bounded jet fields and banks with
`|v_H| ≤ M_b`. -/
theorem pot_piece (Q : ChartBox T) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hsub : Ke ⊆ coframeGL) {B : ℝ≥0∞} (hB : B ≠ ⊤) {Mb : ℝ} (hMb : 0 ≤ Mb) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (R₁ R₂ : E4 → RJet C) (θ₁ θ₂ : CoefficientBank Ysec) (D : ℝ≥0∞),
      JetBound Q Ke B R₁ → JetBound Q Ke B R₂ → |θ₁.vH| ≤ Mb → |θ₂.vH| ≤ Mb →
      jetDist Q R₁ R₂ ≤ D → bankDist θ₁ θ₂ ≤ D →
      eLpNorm (fun x => potJet θ₁ (R₁ x) - potJet θ₂ (R₂ x)) 1 Q.μ ≤ K * D ∧
        eLpNorm (fun x => potJet θ₂ (R₂ x)) 1 Q.μ ≤ K := by
  obtain ⟨cB, hcB⟩ : ∃ r : ℝ≥0∞, r = cQ Q * B := ⟨_, rfl⟩
  have hcBt : cB ≠ ⊤ := by rw [hcB]; exact ENNReal.mul_ne_top (cQ_ne_top Q) hB
  obtain ⟨Ba, hBa⟩ : ∃ r : ℝ≥0∞,
      r = ENNReal.ofReal ‖hInnerReL‖ * (cQ Q * B * (cQ Q * B)) + cQ Q * ENNReal.ofReal (Mb ^ 2) :=
    ⟨_, rfl⟩
  have hBat : Ba ≠ ⊤ := by
    rw [hBa]
    have := cQ_ne_top Q
    finiteness
  obtain ⟨ka, hka⟩ : ∃ r : ℝ≥0∞, r = ENNReal.ofReal ‖hInnerReL‖ * (cQ Q * B + cQ Q * B) * cQ Q +
      cQ Q * ENNReal.ofReal (2 * Mb) := ⟨_, rfl⟩
  have hkat : ka ≠ ⊤ := by
    rw [hka]
    have := cQ_ne_top Q
    finiteness
  obtain ⟨Kd, hKd⟩ : ∃ r : ℝ≥0∞, r = cQ Q + ka := ⟨_, rfl⟩
  have hKdt : Kd ≠ ⊤ := by rw [hKd]; exact ENNReal.add_ne_top.mpr ⟨cQ_ne_top Q, hkat⟩
  obtain ⟨BP, hBP⟩ : ∃ r : ℝ≥0∞, r = ENNReal.ofReal ‖ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)‖ *
      (Ba * cB) + ENNReal.ofReal ‖ContinuousLinearMap.mul ℝ ℝ‖ * (Ba * Ba) := ⟨_, rfl⟩
  have hBPt : BP ≠ ⊤ := by rw [hBP]; finiteness
  obtain ⟨Kp, hKp⟩ : ∃ r : ℝ≥0∞, r = cQ Q +
      ENNReal.ofReal ‖ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)‖ * (cB + Ba) * Kd +
      ENNReal.ofReal ‖ContinuousLinearMap.mul ℝ ℝ‖ * (Ba + Ba) * Kd := ⟨_, rfl⟩
  have hKpt : Kp ≠ ⊤ := by
    rw [hKp]
    have := cQ_ne_top Q
    finiteness
  obtain ⟨K5, hK5, h5⟩ :=
    coeff1_lip (CovSmooth.contDiffOn_potHCoeff (C := C) (n := 1)) hKe hsub hBPt
  obtain ⟨K6, hK6, h6⟩ :=
    coeff1_lip (CovSmooth.contDiffOn_potVCoeff (C := C) (n := 1)) hKe hsub hBPt
  refine ⟨(K5 + K6) * Kp + (K5 + K6), by finiteness, ?_⟩
  intro R₁ R₂ θ₁ θ₂ D h₁ h₂ hv₁ hv₂ hD hDθ
  -- the potential factor
  have ma₁ : AEStronglyMeasurable (fun x => potA θ₁ (R₁ x)) Q.μ :=
    (aesm_apply (aesm_apply (Φ := fun _ => hInnerReL) aestronglyMeasurable_const h₁.m_H)
      h₁.m_H).sub aestronglyMeasurable_const
  have ma₂ : AEStronglyMeasurable (fun x => potA θ₂ (R₂ x)) Q.μ :=
    (aesm_apply (aesm_apply (Φ := fun _ => hInnerReL) aestronglyMeasurable_const h₂.m_H)
      h₂.m_H).sub aestronglyMeasurable_const
  have ba₁ : eLpNorm (fun x => potA θ₁ (R₁ x)) 2 Q.μ ≤ Ba := by
    rw [hBa]; exact potA_bound h₁ θ₁ hv₁
  have ba₂ : eLpNorm (fun x => potA θ₂ (R₂ x)) 2 Q.μ ≤ Ba := by
    rw [hBa]; exact potA_bound h₂ θ₂ hv₂
  have da : eLpNorm (fun x => potA θ₁ (R₁ x) - potA θ₂ (R₂ x)) 2 Q.μ ≤ Kd * D := by
    refine (potA_dist h₁ h₂ θ₁ θ₂ hMb hv₁ hv₂ hD hDθ).trans ?_
    rw [← hka, hKd]
    gcongr
    exact le_add_self
  have dH : eLpNorm (fun x => (R₁ x).H - (R₂ x).H) 2 Q.μ ≤ Kd * D := by
    refine (dist_H2 h₁ h₂ hD).trans ?_
    rw [hKd]
    gcongr
    exact le_self_add
  have bH₁ : eLpNorm (fun x => (R₁ x).H) 2 Q.μ ≤ cB := by rw [hcB]; exact h₁.bH2
  have bH₂ : eLpNorm (fun x => (R₂ x).H) 2 Q.μ ≤ cB := by rw [hcB]; exact h₂.bH2
  -- the cubic and quartic fields
  have dP := bil_const_22 (ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)) ma₁ ma₂ h₁.m_H h₂.m_H
    ba₂ bH₁ da dH
  have dS := bil_const_22 (ContinuousLinearMap.mul ℝ ℝ) ma₁ ma₂ ma₁ ma₂ ba₂ ba₁ da da
  have bP₁ := bil_const_22_bound (ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)) ma₁ h₁.m_H
    ba₁ bH₁
  have bP₂ := bil_const_22_bound (ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)) ma₂ h₂.m_H
    ba₂ bH₂
  have bS₁ := bil_const_22_bound (ContinuousLinearMap.mul ℝ ℝ) ma₁ ma₁ ba₁ ba₁
  have bS₂ := bil_const_22_bound (ContinuousLinearMap.mul ℝ ℝ) ma₂ ma₂ ba₂ ba₂
  have mP₁ := aesm_apply (aesm_apply
    (Φ := fun _ => ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)) aestronglyMeasurable_const ma₁)
    h₁.m_H
  have mP₂ := aesm_apply (aesm_apply
    (Φ := fun _ => ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)) aestronglyMeasurable_const ma₂)
    h₂.m_H
  have mS₁ := aesm_apply (aesm_apply
    (Φ := fun _ => ContinuousLinearMap.mul ℝ ℝ) aestronglyMeasurable_const ma₁) ma₁
  have mS₂ := aesm_apply (aesm_apply
    (Φ := fun _ => ContinuousLinearMap.mul ℝ ℝ) aestronglyMeasurable_const ma₂) ma₂
  have bP₁' : eLpNorm (fun x => ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)
      (potA θ₁ (R₁ x)) (R₁ x).H) 1 Q.μ ≤ BP := bP₁.trans (by rw [hBP]; exact le_self_add)
  have bP₂' : eLpNorm (fun x => ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)
      (potA θ₂ (R₂ x)) (R₂ x).H) 1 Q.μ ≤ BP := bP₂.trans (by rw [hBP]; exact le_self_add)
  have bS₁' : eLpNorm (fun x => ContinuousLinearMap.mul ℝ ℝ
      (potA θ₁ (R₁ x)) (potA θ₁ (R₁ x))) 1 Q.μ ≤ BP := bS₁.trans (by rw [hBP]; exact le_add_self)
  have bS₂' : eLpNorm (fun x => ContinuousLinearMap.mul ℝ ℝ
      (potA θ₂ (R₂ x)) (potA θ₂ (R₂ x))) 1 Q.μ ≤ BP := bS₂.trans (by rw [hBP]; exact le_add_self)
  have dP' : eLpNorm (fun x => ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)
      (potA θ₁ (R₁ x)) (R₁ x).H - ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)
      (potA θ₂ (R₂ x)) (R₂ x).H) 1 Q.μ ≤ Kp * D := by
    refine dP.trans ?_
    calc ENNReal.ofReal ‖ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)‖ * (cB + Ba) * (Kd * D)
        = (ENNReal.ofReal ‖ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)‖ * (cB + Ba) * Kd) * D :=
          by ring
      _ ≤ Kp * D := by
          gcongr ?_ * _
          rw [hKp]
          exact le_add_self.trans le_self_add
  have dS' : eLpNorm (fun x => ContinuousLinearMap.mul ℝ ℝ (potA θ₁ (R₁ x)) (potA θ₁ (R₁ x)) -
      ContinuousLinearMap.mul ℝ ℝ (potA θ₂ (R₂ x)) (potA θ₂ (R₂ x))) 1 Q.μ ≤ Kp * D := by
    refine dS.trans ?_
    calc ENNReal.ofReal ‖ContinuousLinearMap.mul ℝ ℝ‖ * (Ba + Ba) * (Kd * D)
        = (ENNReal.ofReal ‖ContinuousLinearMap.mul ℝ ℝ‖ * (Ba + Ba) * Kd) * D := by ring
      _ ≤ Kp * D := by
          gcongr ?_ * _
          rw [hKp]
          exact le_add_self
  have de : eLpNorm (fun x => (R₁ x).e - (R₂ x).e) ⊤ Q.μ ≤ Kp * D := by
    refine (dist_e h₁ h₂ hD).trans ?_
    rw [hKp]
    gcongr
    calc cQ Q ≤ cQ Q + ENNReal.ofReal ‖ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)‖ *
          (cB + Ba) * Kd := le_self_add
      _ ≤ _ := le_self_add
  have t5 := h5 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e)
    (fun x => ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre) (potA θ₁ (R₁ x)) (R₁ x).H)
    (fun x => ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre) (potA θ₂ (R₂ x)) (R₂ x).H)
    (Kp * D) h₁.m_e h₂.m_e h₁.chart h₂.chart mP₁ mP₂ bP₁' bP₂' de dP'
  have t6 := h6 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e)
    (fun x => ContinuousLinearMap.mul ℝ ℝ (potA θ₁ (R₁ x)) (potA θ₁ (R₁ x)))
    (fun x => ContinuousLinearMap.mul ℝ ℝ (potA θ₂ (R₂ x)) (potA θ₂ (R₂ x)))
    (Kp * D) h₁.m_e h₂.m_e h₁.chart h₂.chart mS₁ mS₂ bS₁' bS₂' de dS'
  have c5 := (CovSmooth.contDiffOn_potHCoeff (C := C) (n := 1)).continuousOn
  have c6 := (CovSmooth.contDiffOn_potVCoeff (C := C) (n := 1)).continuousOn
  have m51 := aesm_apply (aesm_coeff c5 hsub h₁.m_e h₁.chart) mP₁
  have m52 := aesm_apply (aesm_coeff c5 hsub h₂.m_e h₂.chart) mP₂
  have m61 := aesm_apply (aesm_coeff c6 hsub h₁.m_e h₁.chart) mS₁
  have m62 := aesm_apply (aesm_coeff c6 hsub h₂.m_e h₂.chart) mS₂
  simp only [potJet_eq]
  constructor
  · calc _ ≤ _ := eLpNorm_sum2_sub m51 m52 m61 m62
      _ ≤ K5 * (Kp * D) + K6 * (Kp * D) := add_le_add t5.1 t6.1
      _ = (K5 + K6) * Kp * D := by ring
      _ ≤ _ := by gcongr; exact le_self_add
  · calc _ ≤ _ := eLpNorm_add_le m52 m62 le_rfl
      _ ≤ K5 + K6 := add_le_add t5.2 t6.2
      _ ≤ _ := le_add_self

end PotPiece

/-! ### Bank bounds and the gauge couplings -/

section BankBoundsSec

variable {Ysec : Type} [Fintype Ysec]

/-- **Uniform bank bounds on a bank set `P`** (`eq:strong-parameters`): `κ, g_j ≥ c > 0` and all
couplings bounded by `M_b`.  Derived from compactness of `P` (`IsCompactBankSet`) in
`EinsteinSMVariationContinuity.lean`. -/
structure BankBounds (P : Set (CoefficientBank Ysec)) (c Mb : ℝ) : Prop where
  pos : 0 < c
  nonneg : 0 ≤ Mb
  kappa : ∀ θ ∈ P, c ≤ θ.kappa
  g1 : ∀ θ ∈ P, c ≤ θ.g1 ∧ θ.g1 ≤ Mb
  g2 : ∀ θ ∈ P, c ≤ θ.g2 ∧ θ.g2 ≤ Mb
  g3 : ∀ θ ∈ P, c ≤ θ.g3 ∧ θ.g3 ≤ Mb
  Lambda : ∀ θ ∈ P, |θ.Lambda| ≤ Mb
  lambdaH : ∀ θ ∈ P, |θ.lambdaH| ≤ Mb
  vH : ∀ θ ∈ P, |θ.vH| ≤ Mb

/-- The gauge coupling of factor `j` (`g₃, g₂, g₁`). -/
def gCoup (θ : CoefficientBank Ysec) (j : Fin 3) : ℝ := ![θ.g3, θ.g2, θ.g1] j

theorem gaugeScalars_eq (θ : CoefficientBank Ysec) (j : Fin 3) :
    gaugeScalars θ j = ((gCoup θ j) ^ 2)⁻¹ := by
  fin_cases j <;> rfl

theorem gCoup_le (θ₁ θ₂ : CoefficientBank Ysec) (j : Fin 3) :
    ENNReal.ofReal |gCoup θ₁ j - gCoup θ₂ j| ≤ bankDist θ₁ θ₂ := by
  fin_cases j
  · exact g3_le θ₁ θ₂
  · exact g2_le θ₁ θ₂
  · exact g1_le θ₁ θ₂

theorem BankBounds.coup {P : Set (CoefficientBank Ysec)} {c Mb : ℝ} (h : BankBounds P c Mb)
    {θ : CoefficientBank Ysec} (hθ : θ ∈ P) (j : Fin 3) : c ≤ gCoup θ j ∧ gCoup θ j ≤ Mb := by
  fin_cases j
  · exact h.g3 θ hθ
  · exact h.g2 θ hθ
  · exact h.g1 θ hθ

theorem BankBounds.gs_abs_le {P : Set (CoefficientBank Ysec)} {c Mb : ℝ} (h : BankBounds P c Mb)
    {θ : CoefficientBank Ysec} (hθ : θ ∈ P) (j : Fin 3) : |gaugeScalars θ j| ≤ (c ^ 2)⁻¹ := by
  obtain ⟨h1, -⟩ := h.coup hθ j
  have hc := h.pos
  rw [gaugeScalars_eq, abs_of_pos (by have : 0 < gCoup θ j := hc.trans_le h1; positivity)]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le h1 2)

theorem BankBounds.gs_sub_le {P : Set (CoefficientBank Ysec)} {c Mb : ℝ} (h : BankBounds P c Mb)
    {θ₁ θ₂ : CoefficientBank Ysec} (hθ₁ : θ₁ ∈ P) (hθ₂ : θ₂ ∈ P) (j : Fin 3) :
    ENNReal.ofReal |gaugeScalars θ₁ j - gaugeScalars θ₂ j| ≤
      ENNReal.ofReal (((c ^ 2) ^ 2)⁻¹ * (2 * Mb)) * bankDist θ₁ θ₂ := by
  obtain ⟨a1, a2⟩ := h.coup hθ₁ j
  obtain ⟨b1, b2⟩ := h.coup hθ₂ j
  have hc := h.pos
  have ha : |gCoup θ₁ j| ≤ Mb := by rw [abs_of_pos (hc.trans_le a1)]; exact a2
  have hb : |gCoup θ₂ j| ≤ Mb := by rw [abs_of_pos (hc.trans_le b1)]; exact b2
  have h1 := abs_inv_sub_le (by positivity : 0 < c ^ 2) (pow_le_pow_left₀ hc.le a1 2)
    (pow_le_pow_left₀ hc.le b1 2)
  have h2 := abs_sq_sub_sq_le ha hb
  rw [gaugeScalars_eq, gaugeScalars_eq]
  have hM : 0 ≤ Mb := h.nonneg
  calc ENNReal.ofReal |((gCoup θ₁ j) ^ 2)⁻¹ - ((gCoup θ₂ j) ^ 2)⁻¹|
      ≤ ENNReal.ofReal ((((c ^ 2) ^ 2)⁻¹ * (2 * Mb)) * |gCoup θ₁ j - gCoup θ₂ j|) := by
        refine ENNReal.ofReal_le_ofReal (h1.trans ?_)
        rw [mul_assoc]
        gcongr
    _ = ENNReal.ofReal (((c ^ 2) ^ 2)⁻¹ * (2 * Mb)) *
          ENNReal.ofReal |gCoup θ₁ j - gCoup θ₂ j| := ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := by gcongr; exact gCoup_le θ₁ θ₂ j

end BankBoundsSec

/-! ### Measurability of the bosonic pieces -/

section BosonMeas

variable {T : ℝ} {C : Type} [Fintype C] {Ysec : Type} [Fintype Ysec] {Q : ChartBox T}
  {Ke : Set CoframeFibre} {B : ℝ≥0∞} {R : E4 → RJet C}

theorem JetBound.aesm_ymJet (h : JetBound Q Ke B R) (hsub : Ke ⊆ coframeGL) (j : Fin 3) :
    AEStronglyMeasurable (fun x => ymJet j (R x)) Q.μ := by
  have c1 := (CovSmooth.contDiffOn_ymMetCoeff (C := C) (n := 1) j).continuousOn
  have c2 := (CovSmooth.contDiffOn_ymDaCoeff (C := C) (n := 1) j).continuousOn
  have c3 := (CovSmooth.contDiffOn_ymACoeff (C := C) (n := 1) j).continuousOn
  exact ((aesm_apply (aesm_apply (aesm_coeff c1 hsub h.m_e h.chart) h.m_F) h.m_F).add
    (aesm_apply (aesm_coeff c2 hsub h.m_e h.chart) h.m_F)).add
    (aesm_apply (aesm_apply (aesm_coeff c3 hsub h.m_e h.chart) h.m_A) h.m_F)

theorem JetBound.aesm_hgJet (h : JetBound Q Ke B R) (hsub : Ke ⊆ coframeGL) :
    AEStronglyMeasurable (fun x => hgJet (R x)) Q.μ := by
  have c1 := (CovSmooth.contDiffOn_higgsMetCoeff (C := C) (n := 1)).continuousOn
  have c2 := (CovSmooth.contDiffOn_higgsDCoeff (C := C) (n := 1)).continuousOn
  have c3 := (CovSmooth.contDiffOn_higgsHCoeff (C := C) (n := 1)).continuousOn
  have c4 := (CovSmooth.contDiffOn_higgsACoeff (C := C) (n := 1)).continuousOn
  exact (((aesm_apply (aesm_apply (aesm_coeff c1 hsub h.m_e h.chart) h.m_K) h.m_K).add
    (aesm_apply (aesm_coeff c2 hsub h.m_e h.chart) h.m_K)).add
    (aesm_apply (aesm_apply (aesm_coeff c3 hsub h.m_e h.chart) h.m_H) h.m_K)).add
    (aesm_apply (aesm_apply (aesm_coeff c4 hsub h.m_e h.chart) h.m_A) h.m_K)

theorem JetBound.aesm_potJet (h : JetBound Q Ke B R) (hsub : Ke ⊆ coframeGL)
    (θ : CoefficientBank Ysec) :
    AEStronglyMeasurable (fun x => potJet θ (R x)) Q.μ := by
  have c5 := (CovSmooth.contDiffOn_potHCoeff (C := C) (n := 1)).continuousOn
  have c6 := (CovSmooth.contDiffOn_potVCoeff (C := C) (n := 1)).continuousOn
  have ma : AEStronglyMeasurable (fun x => potA θ (R x)) Q.μ :=
    (aesm_apply (aesm_apply (Φ := fun _ => hInnerReL) aestronglyMeasurable_const h.m_H)
      h.m_H).sub aestronglyMeasurable_const
  have mP := aesm_apply (aesm_apply
    (Φ := fun _ => ContinuousLinearMap.lsmul ℝ ℝ (E := HiggsFibre)) aestronglyMeasurable_const ma)
    h.m_H
  have mS := aesm_apply (aesm_apply
    (Φ := fun _ => ContinuousLinearMap.mul ℝ ℝ) aestronglyMeasurable_const ma) ma
  simp only [potJet_eq]
  exact (aesm_apply (aesm_coeff c5 hsub h.m_e h.chart) mP).add
    (aesm_apply (aesm_coeff c6 hsub h.m_e h.chart) mS)

end BosonMeas

/-! ### The bosonic sector -/

section BosonSector

variable {T : ℝ} {C : Type} [Fintype C] {Ysec : Type} [Fintype Ysec]

set_option maxHeartbeats 4000000 in
/-- **`prop:variation-continuity`, bosonic (Yang–Mills + Higgs) sector, jet form**: on uniformly
bounded strong-packet jet fields and banks in `P` with uniform bank bounds,
`‖bosonCov_{θ₁}(R₁) - bosonCov_{θ₂}(R₂)‖_{L¹(Q)} ≤ C (d(R₁,R₂) + |θ₁-θ₂|)`. -/
theorem boson_lipschitz (Q : ChartBox T) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hsub : Ke ⊆ coframeGL) {P : Set (CoefficientBank Ysec)} {c Mb : ℝ}
    (hP : BankBounds P c Mb) {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ∃ Cb : ℝ≥0∞, Cb ≠ ⊤ ∧ ∀ (R₁ R₂ : E4 → RJet C) (θ₁ θ₂ : CoefficientBank Ysec),
      θ₁ ∈ P → θ₂ ∈ P → JetBound Q Ke B R₁ → JetBound Q Ke B R₂ →
        eLpNorm (fun x => bosonCov θ₁ (R₁ x) - bosonCov θ₂ (R₂ x)) 1 Q.μ ≤
          Cb * (jetDist Q R₁ R₂ + bankDist θ₁ θ₂) := by
  choose Ky hKy hy using fun j : Fin 3 => ym_piece (C := C) Q j hKe hsub hB
  obtain ⟨Kh, hKh, hh⟩ := hg_piece (C := C) Q hKe hsub hB
  obtain ⟨Kp, hKp, hp⟩ := pot_piece (C := C) (Ysec := Ysec) Q hKe hsub hB hP.nonneg
  obtain ⟨Lg, hLg⟩ : ∃ r : ℝ≥0∞, r = ENNReal.ofReal (((c ^ 2) ^ 2)⁻¹ * (2 * Mb)) := ⟨_, rfl⟩
  refine ⟨(∑ j, (ENNReal.ofReal ((c ^ 2)⁻¹) * Ky j + Lg * Ky j)) + Kh +
    (ENNReal.ofReal Mb * Kp + 1 * Kp), ?_, ?_⟩
  · refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun j _ => ?_,
      hKh⟩, by finiteness⟩
    have := hKy j
    rw [hLg]
    finiteness
  intro R₁ R₂ θ₁ θ₂ hθ₁ hθ₂ h₁ h₂
  obtain ⟨D, hD⟩ : ∃ d, d = jetDist Q R₁ R₂ + bankDist θ₁ θ₂ := ⟨_, rfl⟩
  have hDj : jetDist Q R₁ R₂ ≤ D := by rw [hD]; exact le_self_add
  have hDθ : bankDist θ₁ θ₂ ≤ D := by rw [hD]; exact le_add_self
  -- Yang–Mills
  have TY : ∀ j : Fin 3, eLpNorm (fun x => gaugeScalars θ₁ j • ymJet j (R₁ x) -
      gaugeScalars θ₂ j • ymJet j (R₂ x)) 1 Q.μ ≤
      (ENNReal.ofReal ((c ^ 2)⁻¹) * Ky j + Lg * Ky j) * D := fun j =>
    scaled_combine (h₁.aesm_ymJet hsub j) (h₂.aesm_ymJet hsub j) (hP.gs_abs_le hθ₁ j)
      (hy j R₁ R₂ D h₁ h₂ hDj).1 (hy j R₁ R₂ D h₁ h₂ hDj).2
      ((hP.gs_sub_le hθ₁ hθ₂ j).trans (by rw [← hLg]; gcongr))
  have mY₁ : ∀ j : Fin 3, AEStronglyMeasurable
      (fun x => gaugeScalars θ₁ j • ymJet j (R₁ x)) Q.μ := fun j =>
    (h₁.aesm_ymJet hsub j).const_smul (gaugeScalars θ₁ j)
  have mY₂ : ∀ j : Fin 3, AEStronglyMeasurable
      (fun x => gaugeScalars θ₂ j • ymJet j (R₂ x)) Q.μ := fun j =>
    (h₂.aesm_ymJet hsub j).const_smul (gaugeScalars θ₂ j)
  have SY : eLpNorm (fun x => ∑ j, gaugeScalars θ₁ j • ymJet j (R₁ x) -
      ∑ j, gaugeScalars θ₂ j • ymJet j (R₂ x)) 1 Q.μ ≤
      (∑ j, (ENNReal.ofReal ((c ^ 2)⁻¹) * Ky j + Lg * Ky j)) * D := by
    refine (eLpNorm_finsum_sub Finset.univ
      (f₁ := fun j x => gaugeScalars θ₁ j • ymJet j (R₁ x))
      (f₂ := fun j x => gaugeScalars θ₂ j • ymJet j (R₂ x)) mY₁ mY₂).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => TY j
  -- Higgs kinetic
  have TH := (hh R₁ R₂ D h₁ h₂ hDj).1
  -- potential
  have TP : eLpNorm (fun x => θ₁.lambdaH • potJet θ₁ (R₁ x) - θ₂.lambdaH • potJet θ₂ (R₂ x)) 1
      Q.μ ≤ (ENNReal.ofReal Mb * Kp + 1 * Kp) * D :=
    scaled_combine (h₁.aesm_potJet hsub θ₁) (h₂.aesm_potJet hsub θ₂) (hP.lambdaH θ₁ hθ₁)
      (hp R₁ R₂ θ₁ θ₂ D h₁ h₂ (hP.vH θ₁ hθ₁) (hP.vH θ₂ hθ₂) hDj hDθ).1
      (hp R₁ R₂ θ₁ θ₂ D h₁ h₂ (hP.vH θ₁ hθ₁) (hP.vH θ₂ hθ₂) hDj hDθ).2
      ((lambdaH_le θ₁ θ₂).trans (by rw [one_mul]; exact hDθ))
  have mS₁ : AEStronglyMeasurable (fun x => ∑ j, gaugeScalars θ₁ j • ymJet j (R₁ x)) Q.μ :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => mY₁ j
  have mS₂ : AEStronglyMeasurable (fun x => ∑ j, gaugeScalars θ₂ j • ymJet j (R₂ x)) Q.μ :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => mY₂ j
  have e : (fun x => bosonCov θ₁ (R₁ x) - bosonCov θ₂ (R₂ x)) = fun x =>
      ((∑ j, gaugeScalars θ₁ j • ymJet j (R₁ x)) + hgJet (R₁ x) +
        θ₁.lambdaH • potJet θ₁ (R₁ x)) -
      ((∑ j, gaugeScalars θ₂ j • ymJet j (R₂ x)) + hgJet (R₂ x) +
        θ₂.lambdaH • potJet θ₂ (R₂ x)) := rfl
  rw [e, ← hD]
  calc _ ≤ _ := eLpNorm_sum3_sub mS₁ mS₂ (h₁.aesm_hgJet hsub) (h₂.aesm_hgJet hsub)
        ((h₁.aesm_potJet hsub θ₁).const_smul θ₁.lambdaH)
        ((h₂.aesm_potJet hsub θ₂).const_smul θ₂.lambdaH)
    _ ≤ (∑ j, (ENNReal.ofReal ((c ^ 2)⁻¹) * Ky j + Lg * Ky j)) * D + Kh * D +
          (ENNReal.ofReal Mb * Kp + 1 * Kp) * D := add_le_add (add_le_add SY TH) TP
    _ = _ := by ring

end BosonSector

end VarLip
end EinsteinSM
end RenewalGeometry
