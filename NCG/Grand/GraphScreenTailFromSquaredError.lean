/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Graph-screen tails from squared-error estimates

A uniform squared-error bound whose scalar majorant tends to zero implies the
epsilon-form compact-screen tail used by the varying-Hilbert graph compilers.
The inverse-radius estimate produced by Lyapunov and Hodge arguments is exposed
as a direct corollary.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u

variable {K : Type*} [NontriviallyNormedField K]
variable {G : Type u} [NormedAddCommGroup G] [NormedSpace K G]

/-- A uniform squared screen-error estimate with a vanishing scalar majorant
implies uniform epsilon-tail exhaustion. -/
theorem graphScreenTail_of_squaredErrorBound_tendsto_zero
    (screen : ℕ → G →L[K] G) (S : Set G) (bound : ℕ → ℝ)
    (hbound : Tendsto bound atTop (nhds 0))
    (herror : ∀ R y, y ∈ S → ‖y - screen R y‖ ^ 2 ≤ bound R) :
    ∀ ε > 0, ∃ R, ∀ y ∈ S, ‖y - screen R y‖ < ε := by
  intro ε hε
  have hevent : ∀ᶠ R in atTop, bound R < ε ^ 2 :=
    hbound.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hevent
  refine ⟨R₀, fun y hy ↦ ?_⟩
  have hsquare : ‖y - screen R₀ y‖ ^ 2 < ε ^ 2 :=
    (herror R₀ y hy).trans_lt (hR₀ R₀ le_rfl)
  nlinarith [norm_nonneg (y - screen R₀ y)]

/-- The standard inverse-radius squared-error estimate automatically supplies
the graph-screen epsilon tail. -/
theorem graphScreenTail_of_inverseRadiusSquaredError
    (screen : ℕ → G →L[K] G) (S : Set G) (E : ℝ)
    (herror : ∀ R y, y ∈ S → ‖y - screen R y‖ ^ 2 ≤ E / (R + 1)) :
    ∀ ε > 0, ∃ R, ∀ y ∈ S, ‖y - screen R y‖ < ε := by
  exact graphScreenTail_of_squaredErrorBound_tendsto_zero
    screen S (fun R ↦ E / (R + 1))
      (by
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds.mul
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))) herror

/-- A positive-order polynomial Sobolev tail of the form produced by the
shorted-Hodge estimate supplies the graph-screen epsilon tail. -/
theorem graphScreenTail_of_polynomialSquaredError
    (screen : ℕ → G →L[K] G) (S : Set G) (C c s : ℝ)
    (_hc : 0 < c) (hs : 0 < s)
    (herror : ∀ R y, y ∈ S →
      ‖y - screen R y‖ ^ 2 ≤
        C / (c * (1 + (R : ℝ)) ^ s)) :
    ∀ ε > 0, ∃ R, ∀ y ∈ S, ‖y - screen R y‖ < ε := by
  apply graphScreenTail_of_squaredErrorBound_tendsto_zero
    screen S (fun R ↦ C / (c * (1 + (R : ℝ)) ^ s))
  · have hbase : Tendsto (fun R : ℕ ↦ 1 + (R : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 tendsto_natCast_atTop_atTop
    have hdecay : Tendsto (fun R : ℕ ↦ (1 + (R : ℝ)) ^ (-s))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hs).comp hbase
    have hscaled : Tendsto
        (fun R : ℕ ↦ (C / c) * (1 + (R : ℝ)) ^ (-s))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hdecay
    apply hscaled.congr'
    filter_upwards with R
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv,
      ← Real.rpow_neg (by positivity : 0 ≤ 1 + (R : ℝ))]
    ring
  · exact herror

end NCG.VaryingHilbert
