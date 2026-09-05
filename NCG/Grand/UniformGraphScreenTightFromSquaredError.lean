/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GraphScreenMassEscape
import NCG.Grand.GraphScreenTailFromSquaredError

/-!
# Uniform graph-screen tightness from squared tail estimates

A squared graph-tail estimate with a scalar majorant tending to zero supplies the manuscript's
monotone eventual tightness predicate directly. The estimate may depend on both the varying stage
and its admissible vector; uniform domination by the scalar majorant removes all cutoff dependence.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {Hn : ℕ → Type u}
variable {G : Type v} [NormedAddCommGroup G]

/-- A uniform squared-error estimate with a majorant tending to zero implies monotone eventual
graph-screen tightness. -/
theorem uniformGraphScreenTight_of_squaredErrorBound_tendsto_zero
    (graph : ∀ n, Hn n → G) (tail : ℕ → G → G)
    (admissible : ∀ n, Hn n → Prop) (bound : ℕ → ℝ)
    (hbound : Tendsto bound atTop (𝓝 0))
    (herror : ∀ R n u, admissible n u →
      ‖tail R (graph n u)‖ ^ 2 ≤ bound R) :
    UniformGraphScreenTight graph tail admissible := by
  intro ε hε
  have hevent : ∀ᶠ R in atTop, bound R < ε ^ 2 :=
    hbound.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hevent
  refine ⟨R₀, fun S hS ↦ Filter.Eventually.of_forall fun n u hu ↦ ?_⟩
  have hsquare : ‖tail S (graph n u)‖ ^ 2 < ε ^ 2 :=
    (herror S n u hu).trans_lt (hR₀ S hS)
  nlinarith [norm_nonneg (tail S (graph n u))]

/-- The standard inverse-radius squared graph-tail estimate implies monotone eventual graph-screen
tightness. -/
theorem uniformGraphScreenTight_of_inverseRadiusSquaredError
    (graph : ∀ n, Hn n → G) (tail : ℕ → G → G)
    (admissible : ∀ n, Hn n → Prop) (E : ℝ)
    (herror : ∀ R n u, admissible n u →
      ‖tail R (graph n u)‖ ^ 2 ≤ E / (R + 1)) :
    UniformGraphScreenTight graph tail admissible := by
  apply uniformGraphScreenTight_of_squaredErrorBound_tendsto_zero
    graph tail admissible (fun R ↦ E / (R + 1))
  · simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  · exact herror

/-- A positive-order polynomial squared graph-tail estimate implies monotone eventual
graph-screen tightness. -/
theorem uniformGraphScreenTight_of_polynomialSquaredError
    (graph : ∀ n, Hn n → G) (tail : ℕ → G → G)
    (admissible : ∀ n, Hn n → Prop) (C c s : ℝ)
    (_hc : 0 < c) (hs : 0 < s)
    (herror : ∀ R n u, admissible n u →
      ‖tail R (graph n u)‖ ^ 2 ≤
        C / (c * (1 + (R : ℝ)) ^ s)) :
    UniformGraphScreenTight graph tail admissible := by
  apply uniformGraphScreenTight_of_squaredErrorBound_tendsto_zero
    graph tail admissible
      (fun R ↦ C / (c * (1 + (R : ℝ)) ^ s))
  · have hbase : Tendsto (fun R : ℕ ↦ 1 + (R : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 tendsto_natCast_atTop_atTop
    have hdecay : Tendsto (fun R : ℕ ↦ (1 + (R : ℝ)) ^ (-s))
        atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hs).comp hbase
    have hscaled : Tendsto
        (fun R : ℕ ↦ (C / c) * (1 + (R : ℝ)) ^ (-s))
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hdecay
    apply hscaled.congr'
    filter_upwards with R
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv,
      ← Real.rpow_neg (by positivity : 0 ≤ 1 + (R : ℝ))]
    ring
  · exact herror

end NCG.VaryingHilbert
