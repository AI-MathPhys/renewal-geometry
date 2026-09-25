/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sharp differentiated action-current certificate
  (`prop:main-action-current`, `eq:main-sharp-current-transfer`,
  `eq:main-action-source-budget`, `eq:main-current-incidence`;
  emergent-spacetime manuscript)

Finite-dimensional real inner-product spaces `E` (action-gradient covectors
`𝔞`) and `F` (curvature-energy space).  Positive Grams are supplied through
their square roots (`GramSqrt`): a self-adjoint continuous linear
automorphism `R = G^{1/2}` with `R ∘ R = G`; this is the manuscript's
`G_X^{1/2}`, `H_X^{1/2}`.  The Gram norm is `‖x‖²_H = ⟪x, H x⟫ = ‖H^{1/2} x‖²`
(`gramNormSq`, `gramNormSq_eq`), and the action dual norm is
`‖𝔞‖²_{G⁻¹} = ⟪𝔞, G⁻¹ 𝔞⟫ = ‖G^{-1/2} 𝔞‖²` (`dualNormSq`, `dualNormSq_eq`,
with `G⁻¹ = G^{-1/2} ∘ G^{-1/2}` the inverse of `G`, `gramInv_apply_gram`).

* `sharp_current_transfer` (`eq:main-sharp-current-transfer`): with
  `Γ = ‖H^{1/2} 𝖳 G^{1/2}‖²_op` one has `‖𝖳 𝔞‖²_H ≤ Γ ‖𝔞‖²_{G⁻¹}` for all
  `𝔞`, and `Γ` is the least such (nonnegative) constant.
* `source_gramNormSq_le` (`eq:supp-curvature-source-budget`): for
  `f = 𝖳 𝔞 + r` and a pointwise certificate `‖𝔞‖²_{G⁻¹} ≤ C Δ`,
  `‖f‖²_H ≤ 2 (Γ C Δ + ‖r‖²_H)`.
* `action_source_budget` (`eq:main-action-source-budget`): time
  Cauchy–Schwarz on `[0, T_*]` gives
  `∫_0^{T_*} ‖f‖_H ≤ √(2 T_* ∫_0^{T_*} (Γ C Δ + ‖r‖²_H))`
  (`sq_integral_le_measure_mul_integral_sq` is the elementary
  `(∫ g)² ≤ |μ| ∫ g²`).
* `discrete_source_budget`: the discrete counterpart
  `𝒟_X ≤ 2 Σ_j s_j (Γ_j C_j Δ_j + ‖r_j‖²_{H_j})` for
  `ε_j / s_j = 𝖳_j 𝔞_j + r_j`.

Scoped hypotheses disclosed: square roots of the Grams are supplied as data
(they exist uniquely for positive definite Grams); for the time box the
`H`-norm of the source is square integrable on `[0, T_*]` and the right-hand
integrand is integrable there (the manuscript's finite budgets).
-/

open scoped InnerProductSpace BigOperators
open MeasureTheory

namespace RenewalGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A self-adjoint invertible square root `R = G^{1/2}` of a Gram operator
`G` (`R ∘ R = G`). -/
structure GramSqrt (G : E →L[ℝ] E) where
  /-- the square root `G^{1/2}` -/
  sqrt : E ≃L[ℝ] E
  selfAdjoint : ∀ x y, ⟪sqrt x, y⟫_ℝ = ⟪x, sqrt y⟫_ℝ
  mul_self : ∀ x, sqrt (sqrt x) = G x

/-- Gram-weighted squared norm `‖x‖²_H = ⟪x, H x⟫`. -/
def gramNormSq (H : F →L[ℝ] F) (x : F) : ℝ := ⟪x, H x⟫_ℝ

/-- Gram-weighted norm `‖x‖_H`. -/
noncomputable def gramNorm (H : F →L[ℝ] F) (x : F) : ℝ := Real.sqrt (gramNormSq H x)

/-- The inverse Gram `G⁻¹ = G^{-1/2} ∘ G^{-1/2}`. -/
def GramSqrt.gramInv {G : E →L[ℝ] E} (R : GramSqrt G) (x : E) : E :=
  R.sqrt.symm (R.sqrt.symm x)

/-- `G⁻¹` is the inverse of `G`. -/
theorem GramSqrt.gramInv_apply_gram {G : E →L[ℝ] E} (R : GramSqrt G) (x : E) :
    R.gramInv (G x) = x := by
  unfold GramSqrt.gramInv
  rw [← R.mul_self, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- Action dual squared norm `‖𝔞‖²_{G⁻¹} = ⟪𝔞, G⁻¹ 𝔞⟫`. -/
def dualNormSq {G : E →L[ℝ] E} (R : GramSqrt G) (a : E) : ℝ := ⟪a, R.gramInv a⟫_ℝ

theorem GramSqrt.symm_selfAdjoint {G : E →L[ℝ] E} (R : GramSqrt G) (x y : E) :
    ⟪R.sqrt.symm x, y⟫_ℝ = ⟪x, R.sqrt.symm y⟫_ℝ := by
  conv_lhs => rw [← R.sqrt.apply_symm_apply y]
  rw [← R.selfAdjoint, R.sqrt.apply_symm_apply]

/-- `‖x‖²_H = ‖H^{1/2} x‖²`. -/
theorem gramNormSq_eq {H : F →L[ℝ] F} (S : GramSqrt H) (x : F) :
    gramNormSq H x = ‖S.sqrt x‖ ^ 2 := by
  rw [gramNormSq, ← S.mul_self, ← S.selfAdjoint, real_inner_self_eq_norm_sq]

theorem gramNormSq_nonneg {H : F →L[ℝ] F} (S : GramSqrt H) (x : F) :
    0 ≤ gramNormSq H x := by
  rw [gramNormSq_eq S]; positivity

/-- `‖𝔞‖²_{G⁻¹} = ‖G^{-1/2} 𝔞‖²`. -/
theorem dualNormSq_eq {G : E →L[ℝ] E} (R : GramSqrt G) (a : E) :
    dualNormSq R a = ‖R.sqrt.symm a‖ ^ 2 := by
  rw [dualNormSq, GramSqrt.gramInv, ← R.symm_selfAdjoint, real_inner_self_eq_norm_sq]

/-- The Gram-normalized transfer `H^{1/2} 𝖳 G^{1/2}`. -/
def normalizedTransfer {G : E →L[ℝ] E} {H : F →L[ℝ] F} (R : GramSqrt G) (S : GramSqrt H)
    (T : E →L[ℝ] F) : E →L[ℝ] F :=
  (S.sqrt : F →L[ℝ] F) ∘L T ∘L (R.sqrt : E →L[ℝ] E)

/-- The amplification constant `Γ = ‖H^{1/2} 𝖳 G^{1/2}‖²_op`. -/
noncomputable def amplification {G : E →L[ℝ] E} {H : F →L[ℝ] F} (R : GramSqrt G)
    (S : GramSqrt H) (T : E →L[ℝ] F) : ℝ :=
  ‖normalizedTransfer R S T‖ ^ 2

theorem normalizedTransfer_apply {G : E →L[ℝ] E} {H : F →L[ℝ] F} (R : GramSqrt G)
    (S : GramSqrt H) (T : E →L[ℝ] F) (v : E) :
    normalizedTransfer R S T v = S.sqrt (T (R.sqrt v)) := rfl

/-- `eq:main-sharp-current-transfer`: `‖𝖳 𝔞‖²_H ≤ Γ ‖𝔞‖²_{G⁻¹}` with
`Γ = ‖H^{1/2} 𝖳 G^{1/2}‖²_op`, and `Γ` is the least nonnegative constant
with this property. -/
theorem sharp_current_transfer {G : E →L[ℝ] E} {H : F →L[ℝ] F} (R : GramSqrt G)
    (S : GramSqrt H) (T : E →L[ℝ] F) :
    (∀ a : E, gramNormSq H (T a) ≤ amplification R S T * dualNormSq R a) ∧
    ∀ Γ' : ℝ, 0 ≤ Γ' → (∀ a : E, gramNormSq H (T a) ≤ Γ' * dualNormSq R a) →
      amplification R S T ≤ Γ' := by
  constructor
  · intro a
    rw [gramNormSq_eq S, dualNormSq_eq R, amplification]
    have h := (normalizedTransfer R S T).le_opNorm (R.sqrt.symm a)
    rw [normalizedTransfer_apply, R.sqrt.apply_symm_apply] at h
    have h0 : 0 ≤ ‖S.sqrt (T a)‖ := norm_nonneg _
    calc ‖S.sqrt (T a)‖ ^ 2 ≤ (‖normalizedTransfer R S T‖ * ‖R.sqrt.symm a‖) ^ 2 :=
          pow_le_pow_left₀ h0 h 2
      _ = _ := by ring
  · intro Γ' hΓ' hbound
    rw [amplification]
    have hop : ‖normalizedTransfer R S T‖ ≤ Real.sqrt Γ' := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
      have h := hbound (R.sqrt v)
      rw [gramNormSq_eq S, dualNormSq_eq R, R.sqrt.symm_apply_apply] at h
      rw [normalizedTransfer_apply]
      have h1 : ‖S.sqrt (T (R.sqrt v))‖ ^ 2 ≤ (Real.sqrt Γ' * ‖v‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hΓ']
        exact h
      exact pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num) |>.mp h1
    calc ‖normalizedTransfer R S T‖ ^ 2 ≤ Real.sqrt Γ' ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hop 2
      _ = Γ' := Real.sq_sqrt hΓ'

/-- `eq:supp-curvature-source-budget`: for `f = 𝖳 𝔞 + r` with the pointwise
certificate `‖𝔞‖²_{G⁻¹} ≤ C Δ`, `‖f‖²_H ≤ 2 (Γ C Δ + ‖r‖²_H)`. -/
theorem source_gramNormSq_le {G : E →L[ℝ] E} {H : F →L[ℝ] F} (R : GramSqrt G)
    (S : GramSqrt H) (T : E →L[ℝ] F) {a : E} {r f : F} {C Δ : ℝ}
    (hf : f = T a + r) (hcert : dualNormSq R a ≤ C * Δ) :
    gramNormSq H f ≤ 2 * (amplification R S T * (C * Δ) + gramNormSq H r) := by
  have hΓ := (sharp_current_transfer R S T).1 a
  have hΓ0 : 0 ≤ amplification R S T := by unfold amplification; positivity
  rw [gramNormSq_eq S, hf, map_add]
  rw [gramNormSq_eq S] at hΓ ⊢
  have h1 : ‖S.sqrt (T a) + S.sqrt r‖ ^ 2 ≤ (‖S.sqrt (T a)‖ + ‖S.sqrt r‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  have h2 : (‖S.sqrt (T a)‖ + ‖S.sqrt r‖) ^ 2 ≤
      2 * ‖S.sqrt (T a)‖ ^ 2 + 2 * ‖S.sqrt r‖ ^ 2 := by
    nlinarith [sq_nonneg (‖S.sqrt (T a)‖ - ‖S.sqrt r‖)]
  have h3 := mul_le_mul_of_nonneg_left hcert hΓ0
  linarith

/-- Elementary time Cauchy–Schwarz on a finite measure:
`(∫ g)² ≤ μ(univ) ∫ g²`. -/
theorem sq_integral_le_measure_mul_integral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {g : α → ℝ} (hg : Integrable g μ)
    (hg2 : Integrable (fun t => g t ^ 2) μ) :
    (∫ t, g t ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ t, g t ^ 2 ∂μ := by
  set V : ℝ := μ.real Set.univ with hV
  set m : ℝ := ∫ t, g t ∂μ with hm
  rcases (measureReal_nonneg (μ := μ) (s := Set.univ)).lt_or_eq with hVpos | hV0
  · -- expand `0 ≤ ∫ (g - m/V)²`
    set c : ℝ := m / V with hc
    have hnn : 0 ≤ ∫ t, (g t - c) ^ 2 ∂μ := integral_nonneg fun t => sq_nonneg _
    have h1 : Integrable (fun t => 2 * c * g t) μ := hg.const_mul _
    have h2 : Integrable (fun t => g t ^ 2 - 2 * c * g t) μ := hg2.sub h1
    have hexp : ∫ t, (g t - c) ^ 2 ∂μ = (∫ t, g t ^ 2 ∂μ) - 2 * c * m + V * c ^ 2 := by
      calc ∫ t, (g t - c) ^ 2 ∂μ = ∫ t, ((g t ^ 2 - 2 * c * g t) + c ^ 2) ∂μ := by
            congr 1; funext t; ring
        _ = ∫ t, (g t ^ 2 - 2 * c * g t) ∂μ + ∫ _, c ^ 2 ∂μ :=
            integral_add h2 (integrable_const _)
        _ = (∫ t, g t ^ 2 ∂μ - ∫ t, 2 * c * g t ∂μ) + V * c ^ 2 := by
            rw [integral_sub hg2 h1, integral_const, smul_eq_mul]
        _ = _ := by rw [integral_const_mul]
    rw [hexp] at hnn
    have hVne : V ≠ 0 := hVpos.ne'
    have hkey : ∫ t, g t ^ 2 ∂μ - m ^ 2 / V ≥ 0 := by
      have : (∫ t, g t ^ 2 ∂μ) - 2 * c * m + V * c ^ 2 = ∫ t, g t ^ 2 ∂μ - m ^ 2 / V := by
        rw [hc]; field_simp; ring
      linarith
    have : m ^ 2 / V ≤ ∫ t, g t ^ 2 ∂μ := by linarith
    rwa [div_le_iff₀ hVpos, mul_comm] at this
  · -- zero total mass: the measure is zero
    have hμ : μ = 0 := by
      have h0 : (μ Set.univ).toReal = 0 := by rw [← measureReal_def]; exact hV0.symm
      have h := ENNReal.toReal_eq_zero_iff (μ Set.univ) |>.mp h0
      rcases h with h | h
      · exact Measure.measure_univ_eq_zero.mp h
      · exact absurd h (measure_ne_top μ _)
    rw [hm, hμ]
    simp

/-- `eq:main-action-source-budget`: on `[0, T_*]`, if `f = 𝖳 𝔞 + r` with the
pointwise certificate `‖𝔞‖²_{G⁻¹} ≤ C Δ`, then
`∫_0^{T_*} ‖f‖_H ≤ √(2 T_* ∫_0^{T_*} (Γ C Δ + ‖r‖²_H))`. -/
theorem action_source_budget {G : E →L[ℝ] E} {H : F →L[ℝ] F} (R : GramSqrt G)
    (S : GramSqrt H) (T : E →L[ℝ] F) {T₀ : ℝ} (hT₀ : 0 ≤ T₀)
    (a : ℝ → E) (f r : ℝ → F) (C Δ : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc 0 T₀, f t = T (a t) + r t)
    (hcert : ∀ t ∈ Set.Icc 0 T₀, dualNormSq R (a t) ≤ C t * Δ t)
    (hint : MemLp (fun t => gramNorm H (f t)) 2 (volume.restrict (Set.Icc 0 T₀)))
    (hrhs : Integrable (fun t => amplification R S T * (C t * Δ t) + gramNormSq H (r t))
      (volume.restrict (Set.Icc 0 T₀))) :
    ∫ t in Set.Icc 0 T₀, gramNorm H (f t) ≤
      Real.sqrt (2 * T₀ * ∫ t in Set.Icc 0 T₀,
        (amplification R S T * (C t * Δ t) + gramNormSq H (r t))) := by
  set μ := volume.restrict (Set.Icc 0 T₀) with hμ
  have hfin : IsFiniteMeasure μ := by
    rw [hμ]; infer_instance
  have hμuniv : μ.real Set.univ = T₀ := by
    rw [hμ, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), sub_zero]
  have hg : Integrable (fun t => gramNorm H (f t)) μ := hint.integrable (by norm_num)
  have hg2 : Integrable (fun t => gramNorm H (f t) ^ 2) μ := by
    rw [memLp_two_iff_integrable_sq hint.1] at hint
    exact hint
  have hsq_eq : ∀ t, gramNorm H (f t) ^ 2 = gramNormSq H (f t) := fun t =>
    Real.sq_sqrt (gramNormSq_nonneg S _)
  -- pointwise bound on `[0, T₀]`
  have hpt : ∀ t ∈ Set.Icc 0 T₀, gramNorm H (f t) ^ 2 ≤
      2 * (amplification R S T * (C t * Δ t) + gramNormSq H (r t)) := by
    intro t ht
    rw [hsq_eq]
    exact source_gramNormSq_le R S T (hf t ht) (hcert t ht)
  have hmono : ∫ t, gramNorm H (f t) ^ 2 ∂μ ≤
      ∫ t, 2 * (amplification R S T * (C t * Δ t) + gramNormSq H (r t)) ∂μ := by
    refine integral_mono_ae hg2 (hrhs.const_mul 2) ?_
    exact (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  have hcs := sq_integral_le_measure_mul_integral_sq μ hg hg2
  rw [hμuniv] at hcs
  have h0 : 0 ≤ ∫ t, gramNorm H (f t) ∂μ :=
    integral_nonneg fun t => Real.sqrt_nonneg _
  have hI : (∫ t, gramNorm H (f t) ∂μ) ^ 2 ≤
      2 * T₀ * ∫ t, (amplification R S T * (C t * Δ t) + gramNormSq H (r t)) ∂μ := by
    calc (∫ t, gramNorm H (f t) ∂μ) ^ 2 ≤ T₀ * ∫ t, gramNorm H (f t) ^ 2 ∂μ := hcs
      _ ≤ T₀ * (2 * ∫ t, (amplification R S T * (C t * Δ t) + gramNormSq H (r t)) ∂μ) :=
          mul_le_mul_of_nonneg_left hmono hT₀
      _ = _ := by ring
  have hrhs0 : 0 ≤ 2 * T₀ * ∫ t, (amplification R S T * (C t * Δ t) + gramNormSq H (r t)) ∂μ :=
    le_trans (sq_nonneg _) hI
  exact (Real.le_sqrt h0 hrhs0).mpr hI

theorem gramNormSq_smul (H : F →L[ℝ] F) (c : ℝ) (x : F) :
    gramNormSq H (c • x) = c ^ 2 * gramNormSq H x := by
  rw [gramNormSq, gramNormSq, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Discrete counterpart: for `ε_j / s_j = 𝖳_j 𝔞_j + r_j` with pointwise
certificates `‖𝔞_j‖²_{G_j⁻¹} ≤ C_j Δ_j`,
`𝒟_X = Σ_j ‖ε_j‖²_{H_j} / s_j ≤ 2 Σ_j s_j (Γ_j C_j Δ_j + ‖r_j‖²_{H_j})`. -/
theorem discrete_source_budget (M : ℕ) (G : ℕ → E →L[ℝ] E) (H : ℕ → F →L[ℝ] F)
    (R : ∀ j, GramSqrt (G j)) (S : ∀ j, GramSqrt (H j)) (T : ℕ → E →L[ℝ] F)
    (s C Δ : ℕ → ℝ) (a : ℕ → E) (ε r : ℕ → F) (hs : ∀ j < M, 0 < s j)
    (hε : ∀ j < M, ε j = s j • (T j (a j) + r j))
    (hcert : ∀ j < M, dualNormSq (R j) (a j) ≤ C j * Δ j) :
    ∑ j ∈ Finset.range M, gramNormSq (H j) (ε j) / s j ≤
      2 * ∑ j ∈ Finset.range M, s j *
        (amplification (R j) (S j) (T j) * (C j * Δ j) + gramNormSq (H j) (r j)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjM := Finset.mem_range.mp hj
  have hsj := hs j hjM
  rw [hε j hjM, gramNormSq_smul]
  have h := source_gramNormSq_le (R j) (S j) (T j) (rfl : T j (a j) + r j = T j (a j) + r j)
    (hcert j hjM)
  rw [div_le_iff₀ hsj]
  have := mul_le_mul_of_nonneg_left h (sq_nonneg (s j))
  nlinarith [this, hsj]

end RenewalGeometry
