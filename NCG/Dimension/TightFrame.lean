/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The minimal isotropic access frame

**Lemma `lem:minimal-frame`** (minimal isotropic access frame): an
antipodal equal-weight direction system on `S^{d−1}` with isotropic
second moment is built from `k` antipodal pairs forming a **tight
frame**, and a tight frame for a `d`-dimensional space needs at least
`d` vectors — so the minimal cardinality is `N_min(d) = 2d`, attained by
the cross-polytope frame `{±e₁, …, ±e_d}`.

This file proves the load-bearing lower bound
(`NCG.tight_frame_card_lower_bound`): a family `u : Fin k → V` with
`∑ ⟪uₐ, x⟫ uₐ = c·x` for some `c ≠ 0` spans `V`, hence
`dim V ≤ k`.  The cross-polytope realisation `M = (1/d)·I` is
`NCG.crossPolytope_second_moment` (`NCG/Dimension/AccessSelection.lean`);
the uniqueness-up-to-orthogonal-frame refinement at `k = d` is not
formalised. -/

namespace NCG

open Module RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **Lemma `lem:minimal-frame`, lower bound**: a tight frame
(`∑ₐ ⟪uₐ, x⟫ uₐ = c·x` with `c ≠ 0`) for a `d`-dimensional real inner
product space has at least `d` vectors — hence an isotropic antipodal
system on `S^{d−1}` has at least `2d` directions. -/
theorem tight_frame_card_lower_bound {k : ℕ} (u : Fin k → V) {c : ℝ}
    (hc : c ≠ 0)
    (hframe : ∀ x : V, ∑ a, ⟪u a, x⟫ • u a = c • x) :
    finrank ℝ V ≤ k := by
  have hspan : Submodule.span ℝ (Set.range u) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x = c⁻¹ • ∑ a, ⟪u a, x⟫ • u a := by
      rw [hframe x, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a)))
  have h1 : finrank ℝ V
      = finrank ℝ (Submodule.span ℝ (Set.range u)) := by
    rw [hspan, finrank_top]
  rw [h1]
  exact (finrank_range_le_card u).trans_eq (Fintype.card_fin k)

end NCG
