/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Source-core semigroup intertwining

Exact encoding of `thm:source-core-semigroup` for bounded generators: `A` on
the source space `X`, `N` on the target space `H`, the source isometry
`V : X → H`, and the defect `R = N V - V A`.

* `duhamel` : `e^{tN} V - V e^{tA} = ∫₀ᵗ e^{(t-s)N} R e^{sA} ds` (Duhamel's
  formula, via the fundamental theorem of calculus for the operator-valued
  curve `s ↦ e^{(t-s)N} V e^{sA}`);
* `intertwine_iff` : `N V = V A` ⇔ `e^{tN} V = V e^{tA}` for all `t ≥ 0`
  (forward direction by Duhamel, converse by differentiating at `t = 0`);
* `resolvent_defect` : `(z-N)⁻¹ V - V (z-A)⁻¹ = (z-N)⁻¹ R (z-A)⁻¹` for any
  common resolvent point (with explicit two-sided inverses);
* `semigroup_defect_bound` : with `‖e^{tN}‖ ≤ M_N e^{ω_N t}` and
  `‖e^{tA}‖ ≤ M_A e^{ω_A t}`,
  `‖e^{tN} V - V e^{tA}‖ ≤ M_N M_A ‖R‖ Φ_t(ω_N, ω_A)`,
  `Φ_t = ∫₀ᵗ e^{ω_N (t-s) + ω_A s} ds`.

Scope: generators are bounded (the graph-norm domain `D(A)_A` of the record
is then `X` itself); the identification `‖R‖² = Δ_leak + Δ_comp` is
`thm:source-core-Pythagoras`, so the bound is stated with `‖R‖`.
-/

open NormedSpace Set intervalIntegral

namespace NCG
namespace SourceCoreSemigroup

variable {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- The intertwining defect `R = N V - V A`. -/
def defect (A : X →L[ℝ] X) (N : H →L[ℝ] H) (V : X →L[ℝ] H) : X →L[ℝ] H :=
  N.comp V - V.comp A

omit [CompleteSpace X] in
theorem hasDerivAt_exp_left (N : H →L[ℝ] H) (t s : ℝ) :
    HasDerivAt (fun s => exp ((t - s) • N)) ((-1 : ℝ) • (exp ((t - s) • N) * N)) s := by
  have hh : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub t
  have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) N (t - s)).scomp s hh
  simpa [Function.comp_def] using h1

omit [CompleteSpace X] in
theorem hasDerivAt_exp_comp_left (N : H →L[ℝ] H) (V : X →L[ℝ] H) (t s : ℝ) :
    HasDerivAt (fun s => (exp ((t - s) • N)).comp V)
      (-((exp ((t - s) • N)).comp (N.comp V))) s := by
  have h1 := hasDerivAt_exp_left N t s
  have h2 := h1.clm_comp (hasDerivAt_const s V)
  refine h2.congr_deriv ?_
  simp only [ContinuousLinearMap.comp_zero, add_zero, neg_one_smul,
    ContinuousLinearMap.neg_comp, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

/-- The Duhamel curve `g(s) = e^{(t-s)N} V e^{sA}` and its derivative. -/
theorem hasDerivAt_duhamelCurve (A : X →L[ℝ] X) (N : H →L[ℝ] H) (V : X →L[ℝ] H) (t s : ℝ) :
    HasDerivAt (fun s => ((exp ((t - s) • N)).comp V).comp (exp (s • A)))
      (-(((exp ((t - s) • N)).comp (defect A N V)).comp (exp (s • A)))) s := by
  have h1 := hasDerivAt_exp_comp_left N V t s
  have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s
  have h := h1.clm_comp h2
  refine h.congr_deriv ?_
  unfold defect
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
  abel

theorem continuous_duhamelIntegrand (A : X →L[ℝ] X) (N : H →L[ℝ] H) (V : X →L[ℝ] H) (t : ℝ) :
    Continuous fun s => ((exp ((t - s) • N)).comp (defect A N V)).comp (exp (s • A)) := by
  have h1 : Continuous fun s : ℝ => exp ((t - s) • N) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_exp_left N t s).continuousAt
  have h2 : Continuous fun s : ℝ => exp (s • A) :=
    continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s).continuousAt
  exact (h1.clm_comp continuous_const).clm_comp h2

/-- **Duhamel's formula**: `e^{tN} V - V e^{tA} = ∫₀ᵗ e^{(t-s)N} R e^{sA} ds`. -/
theorem duhamel (A : X →L[ℝ] X) (N : H →L[ℝ] H) (V : X →L[ℝ] H) (t : ℝ) :
    (exp (t • N)).comp V - V.comp (exp (t • A))
      = ∫ s in (0 : ℝ)..t, ((exp ((t - s) • N)).comp (defect A N V)).comp (exp (s • A)) := by
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun s => ((exp ((t - s) • N)).comp V).comp (exp (s • A)))
        (-(((exp ((t - s) • N)).comp (defect A N V)).comp (exp (s • A)))) s :=
    fun s _ => hasDerivAt_duhamelCurve A N V t s
  have hint := integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_duhamelIntegrand A N V t).neg.intervalIntegrable 0 t)
  rw [integral_neg] at hint
  have h0 : ((exp ((t - 0) • N)).comp V).comp (exp ((0 : ℝ) • A)) = (exp (t • N)).comp V := by
    simp [ContinuousLinearMap.one_def]
  have ht : ((exp ((t - t) • N)).comp V).comp (exp (t • A)) = V.comp (exp (t • A)) := by
    simp [ContinuousLinearMap.one_def]
  rw [h0, ht] at hint
  have := congrArg Neg.neg hint
  rw [neg_neg] at this
  rw [this]
  abel

/-- **Intertwining ⇔ semigroup intertwining.** -/
theorem intertwine_iff (A : X →L[ℝ] X) (N : H →L[ℝ] H) (V : X →L[ℝ] H) :
    N.comp V = V.comp A ↔ ∀ t : ℝ, 0 ≤ t → (exp (t • N)).comp V = V.comp (exp (t • A)) := by
  constructor
  · intro h t _
    have hR : defect A N V = 0 := by unfold defect; rw [h, sub_self]
    have := duhamel A N V t
    rw [hR] at this
    simp only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp,
      integral_zero] at this
    exact sub_eq_zero.mp this
  · intro h
    -- differentiate `e^{tN} V - V e^{tA} = 0` at `t = 0`
    have hd : HasDerivAt (fun t : ℝ => (exp (t • N)).comp V - V.comp (exp (t • A)))
        (N.comp V - V.comp A) 0 := by
      have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) N 0).clm_comp (hasDerivAt_const (0 : ℝ) V)
      have h2 := (hasDerivAt_const (0 : ℝ) V).clm_comp (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A 0)
      refine (h1.sub h2).congr_deriv ?_
      simp
    -- the function vanishes on `[0, ∞)`, so the right derivative at `0` vanishes
    have hzero : ∀ t : ℝ, 0 ≤ t → (exp (t • N)).comp V - V.comp (exp (t • A)) = 0 :=
      fun t ht => sub_eq_zero.mpr (h t ht)
    have hright : HasDerivWithinAt (fun t : ℝ => (exp (t • N)).comp V - V.comp (exp (t • A)))
        (N.comp V - V.comp A) (Ici 0) 0 := hd.hasDerivWithinAt
    have hconst : HasDerivWithinAt (fun t : ℝ => (exp (t • N)).comp V - V.comp (exp (t • A)))
        0 (Ici 0) 0 := by
      refine (hasDerivWithinAt_const (0 : ℝ) (Ici 0) (0 : X →L[ℝ] H)).congr ?_ ?_
      · intro t ht; exact hzero t ht
      · exact hzero 0 le_rfl
    have := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hright hconst
    exact sub_eq_zero.mp this

omit [CompleteSpace X] [CompleteSpace H] in
/-- **Resolvent defect identity**: for resolvents `RN = (z - N)⁻¹`,
`RA = (z - A)⁻¹` (left inverse on the target side, right inverse on the
source side), `RN V - V RA = RN R RA`. -/
theorem resolvent_defect (A : X →L[ℝ] X) (N : H →L[ℝ] H) (V : X →L[ℝ] H) (z : ℝ)
    (RN : H →L[ℝ] H) (RA : X →L[ℝ] X)
    (hN : RN.comp (z • (1 : H →L[ℝ] H) - N) = 1)
    (hA' : (z • (1 : X →L[ℝ] X) - A).comp RA = 1) :
    RN.comp V - V.comp RA = (RN.comp (defect A N V)).comp RA := by
  -- `V = V (z - A) RA` and `V = RN (z - N) V`
  have e1 : V.comp RA = (RN.comp ((z • (1 : H →L[ℝ] H) - N).comp V)).comp RA := by
    rw [← ContinuousLinearMap.comp_assoc, hN, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
  have e2 : RN.comp V = (RN.comp (V.comp (z • (1 : X →L[ℝ] X) - A))).comp RA := by
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hA',
      ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  rw [e1, e2]
  unfold defect
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc]
  abel

/-- **Semigroup defect bound**: with `‖e^{sN}‖ ≤ M_N e^{ω_N s}` and
`‖e^{sA}‖ ≤ M_A e^{ω_A s}` for `s ∈ [0,t]`,
`‖e^{tN} V - V e^{tA}‖ ≤ M_N M_A ‖R‖ ∫₀ᵗ e^{ω_N (t-s) + ω_A s} ds`. -/
theorem semigroup_defect_bound (A : X →L[ℝ] X) (N : H →L[ℝ] H) (V : X →L[ℝ] H)
    (MN MA ωN ωA : ℝ) (hMN : 0 ≤ MN) {t : ℝ} (ht : 0 ≤ t)
    (hN : ∀ s, 0 ≤ s → s ≤ t → ‖exp (s • N)‖ ≤ MN * Real.exp (ωN * s))
    (hA : ∀ s, 0 ≤ s → s ≤ t → ‖exp (s • A)‖ ≤ MA * Real.exp (ωA * s)) :
    ‖(exp (t • N)).comp V - V.comp (exp (t • A))‖
      ≤ MN * MA * ‖defect A N V‖ * ∫ s in (0 : ℝ)..t, Real.exp (ωN * (t - s) + ωA * s) := by
  rw [duhamel]
  have hbound : ∀ s ∈ Set.Ioc (0 : ℝ) t,
      ‖((exp ((t - s) • N)).comp (defect A N V)).comp (exp (s • A))‖
        ≤ MN * MA * ‖defect A N V‖ * Real.exp (ωN * (t - s) + ωA * s) := by
    intro s hs
    obtain ⟨hs0, hst⟩ := hs
    have h1 := hN (t - s) (by linarith) (by linarith)
    have h2 := hA s hs0.le hst
    calc ‖((exp ((t - s) • N)).comp (defect A N V)).comp (exp (s • A))‖
        ≤ ‖(exp ((t - s) • N)).comp (defect A N V)‖ * ‖exp (s • A)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖exp ((t - s) • N)‖ * ‖defect A N V‖ * ‖exp (s • A)‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (MN * Real.exp (ωN * (t - s))) * ‖defect A N V‖ * (MA * Real.exp (ωA * s)) :=
          mul_le_mul (mul_le_mul h1 le_rfl (norm_nonneg _) (mul_nonneg hMN (Real.exp_pos _).le))
            h2 (norm_nonneg _)
            (mul_nonneg (mul_nonneg hMN (Real.exp_pos _).le) (norm_nonneg _))
      _ = MN * MA * ‖defect A N V‖ * Real.exp (ωN * (t - s) + ωA * s) := by
          rw [Real.exp_add]; ring
  have hg : IntervalIntegrable
      (fun s : ℝ => MN * MA * ‖defect A N V‖ * Real.exp (ωN * (t - s) + ωA * s))
      MeasureTheory.volume 0 t :=
    (by fun_prop : Continuous fun s : ℝ =>
      MN * MA * ‖defect A N V‖ * Real.exp (ωN * (t - s) + ωA * s)).intervalIntegrable 0 t
  calc ‖∫ s in (0 : ℝ)..t, ((exp ((t - s) • N)).comp (defect A N V)).comp (exp (s • A))‖
      ≤ ∫ s in (0 : ℝ)..t, MN * MA * ‖defect A N V‖ * Real.exp (ωN * (t - s) + ωA * s) :=
        norm_integral_le_of_norm_le ht (Filter.Eventually.of_forall hbound) hg
    _ = MN * MA * ‖defect A N V‖ * ∫ s in (0 : ℝ)..t, Real.exp (ωN * (t - s) + ωA * s) := by
        rw [integral_const_mul]

end SourceCoreSemigroup
end NCG
