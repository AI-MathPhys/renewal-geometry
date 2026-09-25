/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ActionCurrentCertificateExact

/-!
# Exact amplification of the differentiated action current
  (`prop:supp-sharp-current-transfer`, `eq:supp-curvature-source-budget`;
  emergent-spacetime manuscript, supplement)

The main-text certificate `prop:main-action-current` is proved in
`RenewalGeometry/Action/ActionCurrentCertificateExact.lean`
(`sharp_current_transfer`: `Γ = ‖H^{1/2} 𝖳 G^{1/2}‖²_op` is the least
constant in `‖𝖳 𝔞‖²_H ≤ Γ ‖𝔞‖²_{G⁻¹}`; `source_gramNormSq_le`:
`eq:supp-curvature-source-budget`; `action_source_budget` and
`discrete_source_budget`: the time and discrete budgets).  The supplement
proposition adds the two clauses of its proof:

* **attainment / finite witness**: on a finite-dimensional (nontrivial)
  action-covector space a unit maximizing right singular vector exists, i.e.
  there is `𝔞` with `‖𝔞‖²_{G⁻¹} = 1` and `‖𝖳 𝔞‖²_H = Γ`
  (`sharp_current_transfer_attained`, from the compactness of the unit sphere:
  `exists_unit_norm_apply_eq_opNorm`); hence every `Γ' < Γ` is beaten by a
  unit-dual-norm covector (`exists_large_amplification_witness`), the
  "finite witness to large source amplification";
* **expectation clause**: with a deterministic supported upper bound
  `Γ_X(ω) ≤ Γ̄` and an action-gradient bound holding only in expectation,
  `𝔼 ‖𝔞‖²_{G⁻¹} ≤ C Δ`, one still has
  `𝔼 ‖f‖²_H ≤ 2 Γ̄ C Δ + 2 𝔼 ‖r^{src}‖²_H`
  (`expected_source_gramNormSq_le`; the manuscript's remark that without a
  deterministic bound one must retain `𝔼[Γ_X ‖𝔞_X‖²]` is reflected in the
  proof, which bounds the product pointwise before averaging).

`supplement_sharp_current_transfer` collects the least-constant statement,
its attainment, and the pointwise budget `eq:supp-curvature-source-budget`.

Scoped hypotheses disclosed: the Gram square roots are supplied as data
(`GramSqrt`), the covector space is finite-dimensional and nontrivial for the
attainment clause, and in the expectation clause the dual norm of `𝔞` and
the `H`-norm of `r^{src}` are integrable (the manuscript's finite budgets).
-/

open scoped InnerProductSpace
open MeasureTheory

namespace RenewalGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- On a finite-dimensional nontrivial domain the operator norm is attained on
the unit sphere: there is `v` with `‖v‖ = 1` and `‖A v‖ = ‖A‖`. -/
theorem exists_unit_norm_apply_eq_opNorm [FiniteDimensional ℝ E] [Nontrivial E]
    (A : E →L[ℝ] F) : ∃ v : E, ‖v‖ = 1 ∧ ‖A v‖ = ‖A‖ := by
  have hS : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
    exact ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
  obtain ⟨v, hv, hmax⟩ := hS.exists_isMaxOn hne A.continuous.norm.continuousOn
  have hv1 : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
  refine ⟨v, hv1, le_antisymm ?_ ?_⟩
  · have := A.le_opNorm v
    rwa [hv1, mul_one] at this
  · exact ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun x hx =>
      hmax (mem_sphere_zero_iff_norm.mpr hx)

/-- Attainment of the sharp transfer constant: a unit maximizing right singular
vector `v` of `H^{1/2} 𝖳 G^{1/2}` gives `𝔞 = G^{1/2} v` with
`‖𝔞‖²_{G⁻¹} = 1` and `‖𝖳 𝔞‖²_H = Γ` (`prop:supp-sharp-current-transfer`). -/
theorem sharp_current_transfer_attained [FiniteDimensional ℝ E] [Nontrivial E]
    {G : E →L[ℝ] E} {H : F →L[ℝ] F} (R : GramSqrt G) (S : GramSqrt H) (T : E →L[ℝ] F) :
    ∃ a : E, dualNormSq R a = 1 ∧ gramNormSq H (T a) = amplification R S T := by
  obtain ⟨v, hv1, hv⟩ := exists_unit_norm_apply_eq_opNorm (normalizedTransfer R S T)
  refine ⟨R.sqrt v, ?_, ?_⟩
  · rw [dualNormSq_eq R, R.sqrt.symm_apply_apply, hv1]
    norm_num
  · rw [gramNormSq_eq S, amplification, ← hv, normalizedTransfer_apply]

/-- Finite witness to large source amplification: every `Γ' < Γ` is exceeded
by the amplification of some covector of unit action dual norm. -/
theorem exists_large_amplification_witness [FiniteDimensional ℝ E] [Nontrivial E]
    {G : E →L[ℝ] E} {H : F →L[ℝ] F} (R : GramSqrt G) (S : GramSqrt H) (T : E →L[ℝ] F)
    {Γ' : ℝ} (hΓ' : Γ' < amplification R S T) :
    ∃ a : E, dualNormSq R a = 1 ∧ Γ' < gramNormSq H (T a) := by
  obtain ⟨a, ha, hTa⟩ := sharp_current_transfer_attained R S T
  exact ⟨a, ha, by rw [hTa]; exact hΓ'⟩

/-- `prop:supp-sharp-current-transfer`: the least constant in
`‖𝖳 𝔞‖²_H ≤ Γ ‖𝔞‖²_{G⁻¹}` is `Γ = ‖H^{1/2} 𝖳 G^{1/2}‖²_op`
(`eq:main-sharp-current-transfer`), it is attained by a covector of unit dual
norm, and a pointwise certificate `‖𝔞‖²_{G⁻¹} ≤ C Δ` for the incidence
`f = 𝖳 𝔞 + r^{src}` gives `eq:supp-curvature-source-budget`
`‖f‖²_H ≤ 2 Γ C Δ + 2 ‖r^{src}‖²_H`. -/
theorem supplement_sharp_current_transfer [FiniteDimensional ℝ E] [Nontrivial E]
    {G : E →L[ℝ] E} {H : F →L[ℝ] F} (R : GramSqrt G) (S : GramSqrt H) (T : E →L[ℝ] F) :
    (∀ a : E, gramNormSq H (T a) ≤ amplification R S T * dualNormSq R a) ∧
    (∀ Γ' : ℝ, 0 ≤ Γ' → (∀ a : E, gramNormSq H (T a) ≤ Γ' * dualNormSq R a) →
      amplification R S T ≤ Γ') ∧
    (∃ a : E, dualNormSq R a = 1 ∧ gramNormSq H (T a) = amplification R S T) ∧
    ∀ (a : E) (r f : F) (C Δ : ℝ), f = T a + r → dualNormSq R a ≤ C * Δ →
      gramNormSq H f ≤ 2 * amplification R S T * (C * Δ) + 2 * gramNormSq H r := by
  obtain ⟨h1, h2⟩ := sharp_current_transfer R S T
  refine ⟨h1, h2, sharp_current_transfer_attained R S T, ?_⟩
  intro a r f C Δ hf hcert
  have := source_gramNormSq_le R S T hf hcert
  linarith

/-- Expectation clause of `prop:supp-sharp-current-transfer`: with a
deterministic supported upper bound `Γ_X(ω) ≤ Γ̄` on the (possibly random)
transfer and Grams, an action-gradient bound holding only in expectation,
`𝔼 ‖𝔞‖²_{G⁻¹} ≤ C Δ`, gives `𝔼 ‖f‖²_H ≤ 2 Γ̄ C Δ + 2 𝔼 ‖r^{src}‖²_H` for
the incidence `f = 𝖳 𝔞 + r^{src}`. -/
theorem expected_source_gramNormSq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Ω → E →L[ℝ] E) (H : Ω → F →L[ℝ] F) (R : ∀ ω, GramSqrt (G ω))
    (S : ∀ ω, GramSqrt (H ω)) (T : Ω → E →L[ℝ] F) (a : Ω → E) (r f : Ω → F)
    {Γbar C Δ : ℝ} (hΓ0 : 0 ≤ Γbar)
    (hΓ : ∀ ω, amplification (R ω) (S ω) (T ω) ≤ Γbar)
    (hf : ∀ ω, f ω = T ω (a ω) + r ω)
    (hdual : Integrable (fun ω => dualNormSq (R ω) (a ω)) μ)
    (hr : Integrable (fun ω => gramNormSq (H ω) (r ω)) μ)
    (hcert : ∫ ω, dualNormSq (R ω) (a ω) ∂μ ≤ C * Δ) :
    ∫ ω, gramNormSq (H ω) (f ω) ∂μ ≤
      2 * Γbar * (C * Δ) + 2 * ∫ ω, gramNormSq (H ω) (r ω) ∂μ := by
  -- pointwise bound with the deterministic amplification bound
  have hpt : ∀ ω, gramNormSq (H ω) (f ω) ≤
      2 * Γbar * dualNormSq (R ω) (a ω) + 2 * gramNormSq (H ω) (r ω) := by
    intro ω
    have h := source_gramNormSq_le (R ω) (S ω) (T ω) (hf ω)
      (le_of_eq (mul_one (dualNormSq (R ω) (a ω))).symm)
    have hd0 : 0 ≤ dualNormSq (R ω) (a ω) := by rw [dualNormSq_eq]; positivity
    have := mul_le_mul_of_nonneg_right (hΓ ω) hd0
    linarith
  have hg : Integrable (fun ω => 2 * Γbar * dualNormSq (R ω) (a ω) +
      2 * gramNormSq (H ω) (r ω)) μ :=
    (hdual.const_mul _).add (hr.const_mul _)
  have hmono := integral_mono_of_nonneg (μ := μ)
    (f := fun ω => gramNormSq (H ω) (f ω))
    (Filter.Eventually.of_forall fun ω => gramNormSq_nonneg (S ω) _) hg
    (Filter.Eventually.of_forall hpt)
  rw [integral_add (hdual.const_mul _) (hr.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have h2 : 2 * Γbar * ∫ ω, dualNormSq (R ω) (a ω) ∂μ ≤ 2 * Γbar * (C * Δ) :=
    mul_le_mul_of_nonneg_left hcert (by positivity)
  linarith

end RenewalGeometry
