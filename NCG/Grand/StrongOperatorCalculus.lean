/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Calculus for locally bounded strong-operator families

A strong-operator family need not be continuous in operator norm.  The lemmas
below provide the correct replacement needed for semigroup product paths:
local uniform operator bounds allow moving vectors to pass through a strong
operator limit, and give a product rule from a derivative on one fixed vector.
-/

open Filter
open scoped Topology

noncomputable section

namespace NCG

universe u v w

variable {I : Type u}
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {H : Type w} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A locally uniformly bounded family of operators can be evaluated on a
moving convergent vector under strong convergence at the limiting vector. -/
theorem tendsto_clm_apply_of_eventually_opNorm_bounded
    {l : Filter I} (A : I → X →L[ℝ] H) (A₀ : X →L[ℝ] H)
    (x : I → X) (x₀ : X)
    (hx : Tendsto x l (𝓝 x₀))
    (hAx₀ : Tendsto (fun i ↦ A i x₀) l (𝓝 (A₀ x₀)))
    (hbound : ∃ C : ℝ, ∀ᶠ i in l, ‖A i‖ ≤ C) :
    Tendsto (fun i ↦ A i (x i)) l (𝓝 (A₀ x₀)) := by
  rcases hbound with ⟨C, hC⟩
  have hdiff : Tendsto (fun i ↦ x i - x₀) l (𝓝 0) := by
    simpa using hx.sub_const x₀
  have hsmall : Tendsto (fun i ↦ A i (x i - x₀)) l (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hC] with i hi
      calc
        ‖A i (x i - x₀)‖ ≤ ‖A i‖ * ‖x i - x₀‖ :=
          (A i).le_opNorm _
        _ ≤ C * ‖x i - x₀‖ :=
          mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    · simpa using tendsto_const_nhds.mul hdiff.norm
  have hsum := hsmall.add hAx₀
  simpa only [zero_add] using hsum.congr' (by
    filter_upwards with i
    rw [map_sub]
    abel)

/-- Continuous-at version of the locally bounded strong-operator application
limit. -/
theorem ContinuousAt.clm_apply_of_strong
    (A : ℝ → X →L[ℝ] H) (v : ℝ → X) {s : ℝ}
    (hv : ContinuousAt v s)
    (hstrong : ContinuousAt (fun r ↦ A r (v s)) s)
    (hbound : ∃ C : ℝ, ∀ᶠ r in 𝓝 s, ‖A r‖ ≤ C) :
    ContinuousAt (fun r ↦ A r (v r)) s := by
  exact tendsto_clm_apply_of_eventually_opNorm_bounded
    A (A s) v (v s) hv hstrong hbound

/-- Within-set version of strong-operator application continuity. -/
theorem ContinuousWithinAt.clm_apply_of_strong
    (A : ℝ → X →L[ℝ] H) (v : ℝ → X) (u : Set ℝ) {s : ℝ}
    (hv : ContinuousWithinAt v u s)
    (hstrong : ContinuousWithinAt (fun r ↦ A r (v s)) u s)
    (hbound : ∃ C : ℝ, ∀ᶠ r in 𝓝[u] s, ‖A r‖ ≤ C) :
    ContinuousWithinAt (fun r ↦ A r (v r)) u s := by
  exact tendsto_clm_apply_of_eventually_opNorm_bounded
    A (A s) v (v s) hv hstrong hbound

/-- Strong-operator product rule.  It requires only:

* a derivative of the moving vector;
* a derivative of the operator orbit on the fixed base vector;
* strong continuity on the vector derivative; and
* a local operator-norm bound.

No operator-norm differentiability of `A` is assumed. -/
theorem hasDerivAt_clm_apply_of_strong
    (A : ℝ → X →L[ℝ] H) (v : ℝ → X)
    {s : ℝ} {v' : X} {Av' : H}
    (hv : HasDerivAt v v' s)
    (hfixed : HasDerivAt (fun r ↦ A r (v s)) Av' s)
    (hstrong : ContinuousAt (fun r ↦ A r v') s)
    (hbound : ∃ C : ℝ, ∀ᶠ r in 𝓝 s, ‖A r‖ ≤ C) :
    HasDerivAt (fun r ↦ A r (v r)) (A s v' + Av') s := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hbound' : ∃ C : ℝ, ∀ᶠ r in 𝓝[≠] s, ‖A r‖ ≤ C := by
    rcases hbound with ⟨C, hC⟩
    exact ⟨C, hC.filter_mono inf_le_left⟩
  have hmove := tendsto_clm_apply_of_eventually_opNorm_bounded
    (l := 𝓝[≠] s) A (A s) (slope v s) v'
    hv.tendsto_slope (hstrong.tendsto.mono_left inf_le_left) hbound'
  have hsum := hmove.add hfixed.tendsto_slope
  apply hsum.congr'
  filter_upwards with r
  simp only [slope_def_module, map_sub, map_smul]
  module

end NCG
