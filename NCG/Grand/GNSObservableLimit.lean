/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Bounded observable convergence on the GNS direct limit
  (`thm:GNS-observable-limit`, Gran-Tensor manuscript)

* `limit_observable_unique`: uniqueness — two bounded operators
  agreeing on a dense subspace are equal
  (`ContinuousLinearMap.ext_on`);
* `limit_observable_norm`: the norm bound `‖O∞‖ ≤ C` transfers
  from the dense domain (the proved dense-bound criterion);
* `polynomial_relation_persists`: if a `*`-polynomial relation
  `p(O∞)ξ = 0` holds on a dense subspace then `p(O∞) = 0` — the
  limit observables inherit every finitely-verified word
  relation;
* `nonscalar_of_centered_norm`: if the centered vector norm has
  a positive lower bound, the observable is not a scalar —
  `‖(O - c)Ω‖ ≥ ε > 0` for every scalar `c` forces `O ≠ c·1`.

Rendering disclosed: the existence of the limit operator from
uniformly bounded Cauchy families on the dense GNS core (the
Banach–Steinhaus/completeness construction on the direct limit)
is the manuscript's functional-analysis step; uniqueness, the
norm transfer, relation persistence, and the non-scalarity
witness are proved here.
-/

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Uniqueness: bounded operators agreeing on a dense set are
equal. -/
theorem limit_observable_unique (S T : E →L[ℂ] E)
    (D : Set E) (hdense : Dense D)
    (hagree : ∀ x ∈ D, S x = T x) : S = T := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hx : x ∈ closure D := hdense x
  have hclosed : IsClosed {y : E | S y = T y} :=
    isClosed_eq S.continuous T.continuous
  exact hclosed.closure_subset_iff.mpr hagree hx

/-- Norm transfer from the dense domain: `‖O∞‖ ≤ C` once the
bound holds on a dense set. -/
theorem limit_observable_norm (T : E →L[ℂ] E) (C : ℝ)
    (hC : 0 ≤ C) (D : Set E) (hdense : Dense D)
    (hbd : ∀ x ∈ D, ‖T x‖ ≤ C * ‖x‖) : ‖T‖ ≤ C := by
  refine T.opNorm_le_bound hC fun x => ?_
  have hx : x ∈ closure D := hdense x
  have hclosed : IsClosed {y : E | ‖T y‖ ≤ C * ‖y‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact hclosed.closure_subset_iff.mpr hbd hx

/-- Word-relation persistence: a bounded operator vanishing on a
dense subspace vanishes — every finitely-verified polynomial
relation among limit observables holds exactly. -/
theorem polynomial_relation_persists (P : E →L[ℂ] E)
    (D : Set E) (hdense : Dense D)
    (hzero : ∀ x ∈ D, P x = 0) : P = 0 := by
  refine limit_observable_unique P 0 D hdense fun x hx => ?_
  simp [hzero x hx]

/-- Non-scalarity witness: a uniform positive centered norm at
the vacuum excludes every scalar value. -/
theorem nonscalar_of_centered_norm (T : E →L[ℂ] E) (Ω : E)
    (ε : ℝ) (hε : 0 < ε)
    (hlow : ∀ c : ℂ, ε ≤ ‖T Ω - c • Ω‖) :
    ∀ c : ℂ, T ≠ c • ContinuousLinearMap.id ℂ E := by
  intro c hTc
  have h := hlow c
  rw [hTc] at h
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    sub_self, norm_zero] at h
  linarith

end NCG
